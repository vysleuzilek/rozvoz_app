import 'dart:async';
import 'dart:convert';
import 'dart:math';

import 'package:cloud_firestore/cloud_firestore.dart' as fs;
import 'package:firebase_auth/firebase_auth.dart' as fa;
import 'package:firebase_core/firebase_core.dart' as fc;
import 'package:flutter/material.dart';
import 'package:flutter_map/flutter_map.dart';
import 'package:geolocator/geolocator.dart';
import 'package:latlong2/latlong.dart';
import 'package:shared_preferences/shared_preferences.dart';

import 'firebase_config.dart';

// ===================== SDÍLENÍ POLOHY S RESTAURACÍ =====================
// Všechno je volitelné: dokud řidič sdílení v Nastavení nezapne, appka
// Firebase vůbec nespouští a funguje přesně jako dřív. Veškerá chyba v
// sdílení se jen potichu zahodí, nikdy nesmí shodit navigaci.

const LatLng _liveDefaultCenter = LatLng(50.1560, 15.4600);

class LiveShare {
  LiveShare._();

  static const _prefsKey = 'rozvozka_liveshare_v1';

  static bool get configured => kFirebaseConfigured;
  static String? initError;

  // ---------- nastavení uložené v zařízení ----------
  static bool _prefsLoaded = false;
  static bool _enabled = false;
  static String _name = '';

  static bool get enabledSync => _enabled;
  static String get nameSync => _name;
  static String get _displayName => _name.isNotEmpty ? _name : 'Řidič';

  static Future<void> ensurePrefs() async {
    if (_prefsLoaded) return;
    try {
      final prefs = await SharedPreferences.getInstance();
      final raw = prefs.getString(_prefsKey);
      if (raw != null && raw.isNotEmpty) {
        final m = json.decode(raw) as Map<String, dynamic>;
        _enabled = m['enabled'] == true;
        _name = (m['name'] as String?) ?? '';
      }
    } catch (_) {}
    _prefsLoaded = true;
  }

  static Future<void> _savePrefs() async {
    final prefs = await SharedPreferences.getInstance();
    await prefs.setString(
        _prefsKey, json.encode({'enabled': _enabled, 'name': _name}));
  }

  static Future<void> setEnabled(bool value) async {
    await ensurePrefs();
    _enabled = value;
    await _savePrefs();
    if (!value) await _writeStopped();
  }

  static Future<void> setName(String name) async {
    await ensurePrefs();
    _name = name.trim();
    await _savePrefs();
  }

  // ---------- spuštění Firebase (až když je potřeba) ----------
  static Future<bool>? _initFuture;

  static Future<bool> ensureInit() {
    return _initFuture ??= _doInit();
  }

  static Future<bool> _doInit() async {
    if (!configured) {
      initError =
          'Firebase ještě není nastavený (chybí hodnoty v lib/firebase_config.dart).';
      return false;
    }
    try {
      if (fc.Firebase.apps.isEmpty) {
        await fc.Firebase.initializeApp(options: kFirebaseOptions)
            .timeout(const Duration(seconds: 15));
      }
      initError = null;
      return true;
    } catch (e) {
      initError = 'Firebase se nepodařilo spustit: $e';
      _initFuture = null; // příště to zkusíme znovu
      return false;
    }
  }

  // ---------- přihlášení ----------
  static Future<fa.User?> currentUser() async {
    if (!await ensureInit()) return null;
    try {
      final auth = fa.FirebaseAuth.instance;
      final existing = auth.currentUser;
      if (existing != null) return existing;
      return await auth
          .authStateChanges()
          .first
          .timeout(const Duration(seconds: 6), onTimeout: () => null);
    } catch (_) {
      return null;
    }
  }

  /// Vrátí null při úspěchu, jinak text chyby.
  static Future<String?> signIn(String email, String password) async {
    if (!await ensureInit()) return initError;
    try {
      await fa.FirebaseAuth.instance
          .signInWithEmailAndPassword(email: email.trim(), password: password);
      return null;
    } on fa.FirebaseAuthException catch (e) {
      switch (e.code) {
        case 'invalid-credential':
        case 'wrong-password':
        case 'user-not-found':
        case 'invalid-email':
          return 'Špatný e-mail nebo heslo.';
        case 'network-request-failed':
          return 'Bez připojení k internetu.';
        case 'too-many-requests':
          return 'Moc pokusů, zkus to za chvíli.';
        default:
          return 'Přihlášení se nepovedlo (${e.code}).';
      }
    } catch (e) {
      return 'Přihlášení se nepovedlo: $e';
    }
  }

  /// Odhlášení řidiče (před odhlášením vypne sdílení).
  static Future<void> signOut() async {
    await ensurePrefs();
    if (_enabled) await _writeStopped();
    await signOutOnly();
  }

  /// Odhlášení bez zápisu do databáze (pro účet restaurace).
  static Future<void> signOutOnly() async {
    try {
      if (await ensureInit()) await fa.FirebaseAuth.instance.signOut();
    } catch (_) {}
  }

  // ---------- zápis polohy řidiče ----------
  static DateTime? _lastPush;
  static LatLng? _lastPushPos;
  static DateTime? _lastRoutePush;
  static String _status = 'idle';
  static bool _pushing = false;

  static Future<fs.DocumentReference<Map<String, dynamic>>?> _myDoc() async {
    if (!await ensureInit()) return null;
    final user = fa.FirebaseAuth.instance.currentUser ?? await currentUser();
    if (user == null) return null;
    return fs.FirebaseFirestore.instance.collection('drivers').doc(user.uid);
  }

  static List<double> _flatten(List<LatLng> pts) {
    final step = max(1, (pts.length / 150).ceil());
    final out = <double>[];
    for (var i = 0; i < pts.length; i += step) {
      out.add(pts[i].latitude);
      out.add(pts[i].longitude);
    }
    if ((pts.length - 1) % step != 0) {
      out.add(pts.last.latitude);
      out.add(pts.last.longitude);
    }
    return out;
  }

  /// Volá se z navigace při každé nové poloze. Sama hlídá, jak často se píše.
  static Future<void> pushPosition({
    required LatLng pos,
    double? heading,
    double? speedKmh,
    required String address,
    required double destLat,
    required double destLon,
    double? distanceKm,
    int? etaMin,
    List<LatLng>? route,
  }) async {
    try {
      await ensurePrefs();
      if (!_enabled || !configured) return;
      if (_pushing) return;
      final now = DateTime.now();
      final routeDue = route != null &&
          route.length >= 2 &&
          (_lastRoutePush == null ||
              now.difference(_lastRoutePush!) > const Duration(seconds: 30));
      final statusChange = _status != 'driving';
      if (!statusChange && !routeDue && _lastPush != null) {
        final since = now.difference(_lastPush!);
        if (since < const Duration(seconds: 5)) return;
        final moved = _lastPushPos == null
            ? 999.0
            : Geolocator.distanceBetween(_lastPushPos!.latitude,
                _lastPushPos!.longitude, pos.latitude, pos.longitude);
        if (moved < 8 && since < const Duration(seconds: 20)) return;
      }
      _pushing = true;
      try {
        final doc = await _myDoc();
        if (doc == null) return;
        final data = <String, dynamic>{
          'name': _displayName,
          'sharing': true,
          'status': 'driving',
          'lat': pos.latitude,
          'lon': pos.longitude,
          'heading': heading,
          'speedKmh': speedKmh ?? 0,
          'address': address,
          'destLat': destLat,
          'destLon': destLon,
          'distanceKm': distanceKm,
          'etaMin': etaMin,
          'etaAtMs': etaMin == null
              ? null
              : now.add(Duration(minutes: etaMin)).millisecondsSinceEpoch,
          'updatedAtMs': now.millisecondsSinceEpoch,
        };
        if (routeDue) {
          data['route'] = _flatten(route!);
        }
        await doc.set(data, fs.SetOptions(merge: true));
        if (routeDue) _lastRoutePush = now;
        _status = 'driving';
        _lastPush = now;
        _lastPushPos = pos;
      } finally {
        _pushing = false;
      }
    } catch (_) {}
  }

  /// Řidič kliknul na Doručeno.
  static Future<void> markDelivered() async {
    if (_status != 'driving') return; // nic jsme nesdíleli
    _status = 'delivered';
    _lastRoutePush = null;
    _lastPush = null;
    try {
      final doc = await _myDoc();
      if (doc == null) return;
      final now = DateTime.now().millisecondsSinceEpoch;
      await doc.set({
        'sharing': true,
        'status': 'delivered',
        'deliveredAtMs': now,
        'updatedAtMs': now,
        'route': <double>[],
        'etaMin': null,
        'etaAtMs': null,
        'distanceKm': null,
      }, fs.SetOptions(merge: true));
    } catch (_) {}
  }

  /// Obrazovka navigace se zavřela. Když nebylo doručeno, vrátí stav na "volný".
  static Future<void> leaveDelivery() async {
    if (_status != 'driving') return;
    _status = 'idle';
    _lastRoutePush = null;
    _lastPush = null;
    try {
      final doc = await _myDoc();
      if (doc == null) return;
      await doc.set({
        'status': 'idle',
        'route': <double>[],
        'etaMin': null,
        'etaAtMs': null,
        'distanceKm': null,
        'updatedAtMs': DateTime.now().millisecondsSinceEpoch,
      }, fs.SetOptions(merge: true));
    } catch (_) {}
  }

  static Future<void> _writeStopped() async {
    try {
      final doc = await _myDoc();
      if (doc == null) return;
      await doc.set({
        'name': _displayName,
        'sharing': false,
        'status': 'idle',
        'route': <double>[],
        'etaMin': null,
        'etaAtMs': null,
        'distanceKm': null,
        'updatedAtMs': DateTime.now().millisecondsSinceEpoch,
      }, fs.SetOptions(merge: true));
      _status = 'idle';
    } catch (_) {}
  }
}

// ===================== PŘIHLAŠOVACÍ FORMULÁŘ =====================
class _LoginForm extends StatefulWidget {
  final VoidCallback onLoggedIn;
  const _LoginForm({required this.onLoggedIn});

  @override
  State<_LoginForm> createState() => _LoginFormState();
}

class _LoginFormState extends State<_LoginForm> {
  final _email = TextEditingController();
  final _pass = TextEditingController();
  bool _busy = false;
  String? _err;

  @override
  void dispose() {
    _email.dispose();
    _pass.dispose();
    super.dispose();
  }

  Future<void> _go() async {
    setState(() {
      _busy = true;
      _err = null;
    });
    final err = await LiveShare.signIn(_email.text, _pass.text);
    if (!mounted) return;
    setState(() {
      _busy = false;
      _err = err;
    });
    if (err == null) widget.onLoggedIn();
  }

  @override
  Widget build(BuildContext context) {
    return Column(
      mainAxisSize: MainAxisSize.min,
      crossAxisAlignment: CrossAxisAlignment.stretch,
      children: [
        TextField(
          controller: _email,
          keyboardType: TextInputType.emailAddress,
          autocorrect: false,
          decoration: const InputDecoration(
            labelText: 'E-mail',
            border: OutlineInputBorder(),
          ),
        ),
        const SizedBox(height: 12),
        TextField(
          controller: _pass,
          obscureText: true,
          onSubmitted: (_) => _go(),
          decoration: const InputDecoration(
            labelText: 'Heslo',
            border: OutlineInputBorder(),
          ),
        ),
        if (_err != null)
          Padding(
            padding: const EdgeInsets.only(top: 10),
            child: Text(_err!,
                style: TextStyle(color: Theme.of(context).colorScheme.error)),
          ),
        const SizedBox(height: 12),
        ElevatedButton(
          onPressed: _busy ? null : _go,
          child: _busy
              ? const SizedBox(
                  width: 18,
                  height: 18,
                  child: CircularProgressIndicator(strokeWidth: 2),
                )
              : const Text('Přihlásit'),
        ),
      ],
    );
  }
}

// ===================== SEKCE V NASTAVENÍ (pro řidiče) =====================
class LiveShareSettingsSection extends StatefulWidget {
  const LiveShareSettingsSection({super.key});

  @override
  State<LiveShareSettingsSection> createState() =>
      _LiveShareSettingsSectionState();
}

class _LiveShareSettingsSectionState extends State<LiveShareSettingsSection> {
  bool _loading = true;
  fa.User? _user;
  bool _enabled = false;
  final _nameCtrl = TextEditingController();

  @override
  void initState() {
    super.initState();
    _load();
  }

  @override
  void dispose() {
    _nameCtrl.dispose();
    super.dispose();
  }

  Future<void> _load() async {
    await LiveShare.ensurePrefs();
    final u = LiveShare.configured ? await LiveShare.currentUser() : null;
    if (!mounted) return;
    setState(() {
      _user = u;
      _enabled = LiveShare.enabledSync;
      _nameCtrl.text = LiveShare.nameSync;
      _loading = false;
    });
  }

  Future<void> _logout() async {
    await LiveShare.signOut();
    if (!mounted) return;
    setState(() => _user = null);
  }

  @override
  Widget build(BuildContext context) {
    final children = <Widget>[
      const SizedBox(height: 8),
      const Divider(),
      const Padding(
        padding: EdgeInsets.symmetric(vertical: 8),
        child: Text(
          'Sdílení polohy s restaurací',
          style: TextStyle(fontWeight: FontWeight.bold, fontSize: 16),
        ),
      ),
      const Text(
        'Restaurace uvidí na mapě, kde jsi, kam jedeš a za jak dlouho tam '
        'budeš. Poloha se posílá jen při navigaci k zákazníkovi, když je '
        'sdílení zapnuté a appka je otevřená na obrazovce.',
        style: TextStyle(color: Colors.grey),
      ),
      const SizedBox(height: 12),
    ];

    if (!LiveShare.configured) {
      children.add(const Text(
        'Firebase ještě není nastavený. Vyplň hodnoty v souboru '
        'lib/firebase_config.dart.',
      ));
    } else if (_loading) {
      children.add(const LinearProgressIndicator());
    } else if (_user == null) {
      children.add(_LoginForm(onLoggedIn: _load));
    } else {
      children.addAll([
        Text('Přihlášen jako ${_user!.email ?? ''}'),
        const SizedBox(height: 12),
        TextField(
          controller: _nameCtrl,
          onChanged: (v) => LiveShare.setName(v),
          decoration: const InputDecoration(
            labelText: 'Jméno, které uvidí restaurace',
            border: OutlineInputBorder(),
          ),
        ),
        SwitchListTile(
          contentPadding: EdgeInsets.zero,
          title: const Text('Sdílet polohu'),
          subtitle: const Text('Po směně vypni.'),
          value: _enabled,
          onChanged: (v) async {
            setState(() => _enabled = v);
            await LiveShare.setEnabled(v);
          },
        ),
        Align(
          alignment: Alignment.centerLeft,
          child: TextButton(
            onPressed: _logout,
            child: const Text('Odhlásit'),
          ),
        ),
      ]);
    }

    return Column(
      crossAxisAlignment: CrossAxisAlignment.start,
      children: children,
    );
  }
}

// ===================== POHLED PRO RESTAURACI =====================
String _liveAgo(DateTime? t, DateTime now) {
  if (t == null) return 'neznámo';
  final m = now.difference(t).inMinutes;
  if (m < 1) return 'právě teď';
  if (m < 60) return 'před $m min';
  return 'před ${m ~/ 60} h';
}

String _liveHhmm(DateTime t) =>
    '${t.hour.toString().padLeft(2, '0')}:${t.minute.toString().padLeft(2, '0')}';

class _Driver {
  final String id;
  final String name;
  final bool sharing;
  final String status;
  final LatLng? pos;
  final double? heading;
  final double speedKmh;
  final String? address;
  final LatLng? dest;
  final double? distanceKm;
  final DateTime? etaAt;
  final List<LatLng> route;
  final DateTime? updatedAt;
  final DateTime? deliveredAt;

  _Driver({
    required this.id,
    required this.name,
    required this.sharing,
    required this.status,
    required this.pos,
    required this.heading,
    required this.speedKmh,
    required this.address,
    required this.dest,
    required this.distanceKm,
    required this.etaAt,
    required this.route,
    required this.updatedAt,
    required this.deliveredAt,
  });

  static DateTime? _ms(dynamic v) =>
      v is num ? DateTime.fromMillisecondsSinceEpoch(v.toInt()) : null;

  factory _Driver.fromMap(String id, Map<String, dynamic> d) {
    final lat = (d['lat'] as num?)?.toDouble();
    final lon = (d['lon'] as num?)?.toDouble();
    final dLat = (d['destLat'] as num?)?.toDouble();
    final dLon = (d['destLon'] as num?)?.toDouble();
    final route = <LatLng>[];
    final raw = d['route'];
    if (raw is List) {
      for (var i = 0; i + 1 < raw.length; i += 2) {
        final a = raw[i];
        final b = raw[i + 1];
        if (a is num && b is num) {
          route.add(LatLng(a.toDouble(), b.toDouble()));
        }
      }
    }
    final name = (d['name'] as String?) ?? '';
    return _Driver(
      id: id,
      name: name.isEmpty ? 'Řidič' : name,
      sharing: d['sharing'] == true,
      status: (d['status'] as String?) ?? 'idle',
      pos: (lat != null && lon != null) ? LatLng(lat, lon) : null,
      heading: (d['heading'] as num?)?.toDouble(),
      speedKmh: (d['speedKmh'] as num?)?.toDouble() ?? 0,
      address: d['address'] as String?,
      dest: (dLat != null && dLon != null) ? LatLng(dLat, dLon) : null,
      distanceKm: (d['distanceKm'] as num?)?.toDouble(),
      etaAt: _ms(d['etaAtMs']),
      route: route,
      updatedAt: _ms(d['updatedAtMs']),
      deliveredAt: _ms(d['deliveredAtMs']),
    );
  }

  bool isFresh(DateTime now) {
    if (!sharing || updatedAt == null) return false;
    final limit = status == 'driving'
        ? const Duration(minutes: 3)
        : const Duration(minutes: 90);
    return now.difference(updatedAt!) < limit;
  }

  bool isDriving(DateTime now) => isFresh(now) && status == 'driving';

  String headline(DateTime now) {
    if (!sharing) return 'Nesdílí polohu';
    if (!isFresh(now)) return 'Offline · naposledy ${_liveAgo(updatedAt, now)}';
    switch (status) {
      case 'driving':
        return 'Jede k zákazníkovi';
      case 'delivered':
        return 'Doručeno ${_liveAgo(deliveredAt ?? updatedAt, now)}, vrací se';
      default:
        return 'Online, momentálně nikam nejede';
    }
  }
}

class RestaurantScreen extends StatefulWidget {
  const RestaurantScreen({super.key});

  @override
  State<RestaurantScreen> createState() => _RestaurantScreenState();
}

class _RestaurantScreenState extends State<RestaurantScreen> {
  final MapController _map = MapController();
  bool _mapReady = false;
  bool _loading = true;
  fa.User? _user;
  String? _selectedId;
  bool _follow = true;
  LatLng? _lastCentered;
  Timer? _tick;

  @override
  void initState() {
    super.initState();
    _tick = Timer.periodic(const Duration(seconds: 15), (_) {
      if (mounted) setState(() {});
    });
    _load();
  }

  @override
  void dispose() {
    _tick?.cancel();
    super.dispose();
  }

  Future<void> _load() async {
    final u = LiveShare.configured ? await LiveShare.currentUser() : null;
    if (!mounted) return;
    setState(() {
      _user = u;
      _loading = false;
    });
  }

  Future<void> _logout() async {
    await LiveShare.signOutOnly();
    if (!mounted) return;
    setState(() => _user = null);
  }

  @override
  Widget build(BuildContext context) {
    return Scaffold(
      appBar: AppBar(
        title: const Text('Rozvoz – kde jsou řidiči'),
        actions: [
          if (_user != null)
            IconButton(
              icon: const Icon(Icons.logout),
              tooltip: 'Odhlásit',
              onPressed: _logout,
            ),
        ],
      ),
      body: _body(),
    );
  }

  Widget _body() {
    if (!LiveShare.configured) {
      return const Center(
        child: Padding(
          padding: EdgeInsets.all(24),
          child: Text(
              'Firebase ještě není nastavený (lib/firebase_config.dart).'),
        ),
      );
    }
    if (_loading) return const Center(child: CircularProgressIndicator());
    if (_user == null) {
      return Center(
        child: ConstrainedBox(
          constraints: const BoxConstraints(maxWidth: 380),
          child: Padding(
            padding: const EdgeInsets.all(24),
            child: Column(
              mainAxisSize: MainAxisSize.min,
              children: [
                const Text('Přihlášení pro restauraci',
                    style:
                        TextStyle(fontSize: 18, fontWeight: FontWeight.bold)),
                const SizedBox(height: 16),
                _LoginForm(onLoggedIn: _load),
              ],
            ),
          ),
        ),
      );
    }
    return StreamBuilder<fs.QuerySnapshot<Map<String, dynamic>>>(
      stream: fs.FirebaseFirestore.instance.collection('drivers').snapshots(),
      builder: (context, snap) {
        if (snap.hasError) {
          return Center(
              child: Text('Nepodařilo se načíst data: ${snap.error}'));
        }
        if (!snap.hasData) {
          return const Center(child: CircularProgressIndicator());
        }
        final drivers = snap.data!.docs
            .map((d) => _Driver.fromMap(d.id, d.data()))
            .toList()
          ..sort((a, b) => a.name.compareTo(b.name));
        if (drivers.isEmpty) {
          return const Center(child: Text('Zatím žádný řidič nesdílel polohu.'));
        }
        return _buildLive(drivers);
      },
    );
  }

  Widget _buildLive(List<_Driver> drivers) {
    final now = DateTime.now();
    final selected = drivers.firstWhere(
      (d) => d.id == _selectedId,
      orElse: () => drivers.firstWhere(
        (d) => d.isFresh(now),
        orElse: () => drivers.first,
      ),
    );

    final sp = selected.pos;
    if (_follow && _mapReady && sp != null && sp != _lastCentered) {
      _lastCentered = sp;
      WidgetsBinding.instance.addPostFrameCallback((_) {
        if (mounted && _mapReady) _map.move(sp, _map.camera.zoom);
      });
    }

    final driving = selected.isDriving(now);
    final etaAt = selected.etaAt;
    final etaMin = etaAt == null
        ? null
        : max(0, etaAt.difference(now).inMinutes + 1);

    final markers = <Marker>[];
    if (driving && selected.dest != null) {
      markers.add(Marker(
        point: selected.dest!,
        width: 44,
        height: 44,
        child: Container(
          decoration: BoxDecoration(
            color: const Color(0xFFB3261E),
            shape: BoxShape.circle,
            border: Border.all(color: Colors.white, width: 3),
            boxShadow: const [
              BoxShadow(
                  color: Colors.black45, blurRadius: 6, offset: Offset(0, 2)),
            ],
          ),
          alignment: Alignment.center,
          child: const Icon(Icons.flag, color: Colors.white, size: 22),
        ),
      ));
    }
    for (final d in drivers) {
      if (d.pos == null) continue;
      final isSel = d.id == selected.id;
      final fresh = d.isFresh(now);
      markers.add(Marker(
        point: d.pos!,
        width: 70,
        height: 62,
        child: Column(
          mainAxisSize: MainAxisSize.min,
          children: [
            Container(
              padding: const EdgeInsets.symmetric(horizontal: 5, vertical: 1),
              decoration: BoxDecoration(
                color: Colors.white,
                borderRadius: BorderRadius.circular(8),
                boxShadow: const [
                  BoxShadow(color: Colors.black26, blurRadius: 3),
                ],
              ),
              child: Text(d.name,
                  style: const TextStyle(
                      fontSize: 10, fontWeight: FontWeight.w700),
                  overflow: TextOverflow.ellipsis),
            ),
            Transform.rotate(
              angle: (d.heading ?? 0) * pi / 180,
              child: Icon(
                Icons.navigation,
                size: isSel ? 38 : 30,
                color: !fresh
                    ? Colors.grey
                    : (isSel ? const Color(0xFF2F7FF0) : Colors.orange),
                shadows: const [Shadow(color: Colors.black45, blurRadius: 5)],
              ),
            ),
          ],
        ),
      ));
    }

    return Column(
      children: [
        Material(
          elevation: 2,
          color: Theme.of(context).colorScheme.surface,
          child: Padding(
            padding: const EdgeInsets.fromLTRB(14, 10, 14, 12),
            child: Column(
              crossAxisAlignment: CrossAxisAlignment.start,
              children: [
                if (drivers.length > 1)
                  Padding(
                    padding: const EdgeInsets.only(bottom: 8),
                    child: Wrap(
                      spacing: 8,
                      runSpacing: 4,
                      children: [
                        for (final d in drivers)
                          ChoiceChip(
                            label: Text(d.name),
                            selected: d.id == selected.id,
                            onSelected: (_) => setState(() {
                              _selectedId = d.id;
                              _follow = true;
                              _lastCentered = null;
                            }),
                          ),
                      ],
                    ),
                  ),
                Text(selected.name,
                    style: const TextStyle(
                        fontSize: 18, fontWeight: FontWeight.w800)),
                const SizedBox(height: 2),
                Text(selected.headline(now),
                    style: TextStyle(
                        fontWeight: FontWeight.w600,
                        color: driving
                            ? Colors.green.shade700
                            : Colors.grey.shade700)),
                if (driving && (selected.address ?? '').isNotEmpty)
                  Padding(
                    padding: const EdgeInsets.only(top: 4),
                    child: Text('Adresa: ${selected.address}'),
                  ),
                if (driving && etaAt != null)
                  Padding(
                    padding: const EdgeInsets.only(top: 2),
                    child: Text(
                      'Příjezd k zákazníkovi: ${_liveHhmm(etaAt)}'
                      ' (za $etaMin min)'
                      '${selected.distanceKm != null ? " · ${selected.distanceKm!.toStringAsFixed(1)} km" : ""}',
                      style: const TextStyle(fontWeight: FontWeight.w600),
                    ),
                  ),
                if (driving)
                  Padding(
                    padding: const EdgeInsets.only(top: 2),
                    child: Text(
                        'Rychlost: ${selected.speedKmh.round()} km/h · '
                        'aktualizováno ${_liveAgo(selected.updatedAt, now)}',
                        style: TextStyle(
                            fontSize: 12, color: Colors.grey.shade600)),
                  ),
              ],
            ),
          ),
        ),
        Expanded(
          child: Stack(
            children: [
              FlutterMap(
                mapController: _map,
                options: MapOptions(
                  initialCenter: selected.pos ?? _liveDefaultCenter,
                  initialZoom: 14,
                  onMapReady: () {
                    WidgetsBinding.instance.addPostFrameCallback((_) {
                      if (mounted) setState(() => _mapReady = true);
                    });
                  },
                  onPositionChanged: (pos, hasGesture) {
                    if (hasGesture && _follow) {
                      setState(() => _follow = false);
                    }
                  },
                ),
                children: [
                  TileLayer(
                    urlTemplate:
                        'https://tile.openstreetmap.org/{z}/{x}/{y}.png',
                    userAgentPackageName: 'com.example.rozvozka',
                  ),
                  if (driving && selected.route.length >= 2)
                    PolylineLayer(polylines: [
                      Polyline(
                        points: selected.route,
                        strokeWidth: 6,
                        color: const Color(0xFF2F7FF0),
                      ),
                    ]),
                  MarkerLayer(markers: markers),
                ],
              ),
              Positioned(
                right: 12,
                bottom: 12,
                child: FloatingActionButton(
                  heroTag: 'restaurantFollow',
                  backgroundColor: _follow ? Colors.orange : Colors.white,
                  onPressed: () => setState(() {
                    _follow = true;
                    _lastCentered = null;
                  }),
                  child: Icon(Icons.my_location,
                      color: _follow ? Colors.white : Colors.black87),
                ),
              ),
            ],
          ),
        ),
      ],
    );
  }
}
