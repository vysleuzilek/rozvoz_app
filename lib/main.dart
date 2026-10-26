import 'package:flutter/material.dart';
import 'package:flutter/services.dart';
import 'package:flutter_map/flutter_map.dart';
import 'package:latlong2/latlong.dart';
import 'package:geolocator/geolocator.dart';
import 'package:url_launcher/url_launcher.dart';
import 'package:http/http.dart' as http;
import 'package:shared_preferences/shared_preferences.dart';
import 'package:pdf/pdf.dart';
import 'package:pdf/widgets.dart' as pw;
import 'package:printing/printing.dart';
import 'dart:convert';
import 'dart:async';
import 'dart:math';
import 'dart:js_interop';
import 'package:web/web.dart' as web;

// Appka je určená pro okolí Chlumce nad Cidlinou -- vše mimo tento rádius
// appka odmítne, ať tě nenavede daleko od domovské oblasti.
const LatLng _chlumecCenter = LatLng(50.1560, 15.4600);
const double _maxDistanceKm = 20.0;

class _BBox {
  final double latMin, latMax, lonMin, lonMax;
  _BBox(this.latMin, this.latMax, this.lonMin, this.lonMax);
}

_BBox _boundingBoxKm(LatLng center, double radiusKm) {
  final latDelta = radiusKm / 111.32;
  final lonDelta = radiusKm / (111.32 * cos(center.latitude * pi / 180));
  return _BBox(
    center.latitude - latDelta,
    center.latitude + latDelta,
    center.longitude - lonDelta,
    center.longitude + lonDelta,
  );
}

// ---- Pomocné funkce pro turn-by-turn banner (podobně jako v navigacích) ----
String _maneuverText(Map<String, dynamic> step) {
  final maneuver = step['maneuver'] as Map<String, dynamic>? ?? {};
  final type = maneuver['type'] as String? ?? '';
  final modifier = maneuver['modifier'] as String?;
  final name = step['name'] as String?;
  final street = (name != null && name.trim().isNotEmpty) ? ' na $name' : '';

  if (type == 'arrive') {
    if (modifier == 'left') return 'Cíl bude po levé straně';
    if (modifier == 'right') return 'Cíl bude po pravé straně';
    return 'Cíl je před vámi';
  }
  if (type == 'depart') return 'Vyrazte a pokračujte rovně$street';
  if (type == 'roundabout' || type == 'rotary' || type == 'roundabout turn') {
    return 'Na kruhovém objezdu pokračujte$street';
  }
  switch (modifier) {
    case 'left':
      return 'Odbočte vlevo$street';
    case 'sharp left':
      return 'Ostře odbočte vlevo$street';
    case 'slight left':
      return 'Mírně vlevo$street';
    case 'right':
      return 'Odbočte vpravo$street';
    case 'sharp right':
      return 'Ostře odbočte vpravo$street';
    case 'slight right':
      return 'Mírně vpravo$street';
    case 'uturn':
      return 'Otočte se$street';
    default:
      return 'Pokračujte rovně$street';
  }
}

IconData _maneuverIcon(Map<String, dynamic> step) {
  final maneuver = step['maneuver'] as Map<String, dynamic>? ?? {};
  final type = maneuver['type'] as String? ?? '';
  final modifier = maneuver['modifier'] as String?;
  if (type == 'arrive') return Icons.flag;
  if (type == 'roundabout' || type == 'rotary') return Icons.roundabout_left;
  switch (modifier) {
    case 'left':
      return Icons.turn_left;
    case 'sharp left':
      return Icons.turn_sharp_left;
    case 'slight left':
      return Icons.turn_slight_left;
    case 'right':
      return Icons.turn_right;
    case 'sharp right':
      return Icons.turn_sharp_right;
    case 'slight right':
      return Icons.turn_slight_right;
    case 'uturn':
      return Icons.u_turn_left;
    default:
      return Icons.straight;
  }
}

String _formatDistance(num meters) {
  if (meters < 1000) {
    final rounded = (meters / 10).round() * 10;
    return '$rounded m';
  }
  return '${(meters / 1000).toStringAsFixed(1)} km';
}

// ---- Lokální dopočet polohy na trase (mezi přepočty z OSRM) ----
// Trasu z OSRM přepočítáváme jen občas (kvůli zatížení veřejného serveru),
// ale appka mezitím sama, bez internetu, dopočítá, kde přesně na trase
// jsme - ať modrá čára "nekouká za nás" a vzdálenost k odbočení je aktuální
// i mezi jednotlivými přepočty.
class _RouteProjection {
  final int segmentIndex;
  final LatLng point;
  final double distanceAlongRoute;
  _RouteProjection(this.segmentIndex, this.point, this.distanceAlongRoute);
}

double _projectFactor(LatLng p, LatLng a, LatLng b) {
  final apx = p.longitude - a.longitude;
  final apy = p.latitude - a.latitude;
  final abx = b.longitude - a.longitude;
  final aby = b.latitude - a.latitude;
  final ab2 = abx * abx + aby * aby;
  if (ab2 == 0) return 0;
  final t = (apx * abx + apy * aby) / ab2;
  return t.clamp(0.0, 1.0);
}

_RouteProjection? _projectOntoRoute(LatLng position, List<LatLng> route) {
  if (route.length < 2) return null;
  double bestDist = double.infinity;
  int bestSeg = 0;
  LatLng bestPoint = route[0];
  double bestCumulative = 0;
  double cumulative = 0;
  for (int i = 0; i < route.length - 1; i++) {
    final a = route[i];
    final b = route[i + 1];
    final segLen = Geolocator.distanceBetween(
        a.latitude, a.longitude, b.latitude, b.longitude);
    final t = _projectFactor(position, a, b);
    final projLat = a.latitude + (b.latitude - a.latitude) * t;
    final projLon = a.longitude + (b.longitude - a.longitude) * t;
    final dist = Geolocator.distanceBetween(
        position.latitude, position.longitude, projLat, projLon);
    if (dist < bestDist) {
      bestDist = dist;
      bestSeg = i;
      bestPoint = LatLng(projLat, projLon);
      bestCumulative = cumulative + segLen * t;
    }
    cumulative += segLen;
  }
  return _RouteProjection(bestSeg, bestPoint, bestCumulative);
}

// ---- Formátovač telefonu: automaticky vkládá mezery po 3 číslicích ----
class _PhoneNumberFormatter extends TextInputFormatter {
  @override
  TextEditingValue formatEditUpdate(
      TextEditingValue oldValue, TextEditingValue newValue) {
    String digits = newValue.text.replaceAll(RegExp(r'[^\d+]'), '');
    String prefix = '';
    if (digits.startsWith('+')) {
      prefix = '+';
      digits = digits.substring(1);
    }
    final buffer = StringBuffer();
    for (int i = 0; i < digits.length; i++) {
      if (i != 0 && i % 3 == 0) buffer.write(' ');
      buffer.write(digits[i]);
    }
    final formatted = prefix + buffer.toString();
    return TextEditingValue(
      text: formatted,
      selection: TextSelection.collapsed(offset: formatted.length),
    );
  }
}

// ---- Sdílené geokódování v okruhu kolem Chlumce nad Cidlinou ----
// Okolní vesnice (Klamoš, Olešnice, Převýšov...) NEJSOU "Chlumec" - patří
// pod jeho úřad, ale adresně jsou samostatné obce. Proto se název Chlumce
// nepřilepuje násilně ke každému dotazu (to dřív vedlo k tomu, že appka
// hledala nesmysl typu "Olešnice, Chlumec nad Cidlinou" a skončila třeba
// na dálnici) - zkouší se postupně čistá adresa, pak okres, a Chlumec
// natvrdo až jako poslední možnost pro ulice přímo ve městě.
class GeocodeResult {
  final double lat;
  final double lon;
  final double distanceKm;
  final bool isPrecise; // true = nalezeno na úrovni čísla popisného/domu
  GeocodeResult(this.lat, this.lon, this.distanceKm, {this.isPrecise = true});
}

Future<List> _nominatimSearch(String query) async {
  final box = _boundingBoxKm(_chlumecCenter, 25);
  final geoUrl = Uri.parse(
      'https://nominatim.openstreetmap.org/search'
      '?format=json&limit=5&countrycodes=cz&addressdetails=1'
      '&viewbox=${box.lonMin},${box.latMax},${box.lonMax},${box.latMin}'
      '&bounded=1'
      '&q=${Uri.encodeComponent(query)}');
  final res = await http.get(geoUrl, headers: {'Accept-Language': 'cs'});
  if (res.statusCode != 200) {
    throw Exception('Geokódování selhalo (${res.statusCode})');
  }
  return json.decode(res.body) as List;
}

// Podle vrácených dat pozná, jestli se adresa našla přesně (na úrovni čísla
// popisného/domu), nebo jen zhruba (např. jen střed obce/vesnice) - malé
// vesnice často v OpenStreetMap nemají zmapovaná jednotlivá čísla.
bool _isPreciseMatch(Map r) {
  final type = r['type'] as String?;
  if (type == 'house' || type == 'building') return true;
  final address = r['address'] as Map?;
  if (address != null && address['house_number'] != null) return true;
  return false;
}

// Z vrácených výsledků vybere ten geograficky nejblíž Chlumci - ne jen
// první v pořadí, jak ho seřadil Nominatim.
GeocodeResult? _closestCandidate(List results) {
  GeocodeResult? best;
  for (final r in results) {
    final lat = double.tryParse(r['lat'].toString());
    final lon = double.tryParse(r['lon'].toString());
    if (lat == null || lon == null) continue;
    final dist = Geolocator.distanceBetween(
          _chlumecCenter.latitude,
          _chlumecCenter.longitude,
          lat,
          lon,
        ) /
        1000;
    if (best == null || dist < best.distanceKm) {
      best = GeocodeResult(lat, lon, dist, isPrecise: _isPreciseMatch(r));
    }
  }
  return best;
}

Future<GeocodeResult?> _geocodeInChlumec(String address) async {
  // 1) čistá adresa v okruhu - správně najde i samostatné vesnice
  List results = await _nominatimSearch(address);
  GeocodeResult? best = _closestCandidate(results);
  if (best != null) return best;

  // 2) fallback s okresem, pro nejasnější dotazy
  results = await _nominatimSearch('$address, okres Hradec Králové');
  best = _closestCandidate(results);
  if (best != null) return best;

  // 3) poslední pokus: výslovně přidat Chlumec - pro ulice přímo ve městě,
  // které se nepodařilo najít jinak
  results = await _nominatimSearch('$address, Chlumec nad Cidlinou');
  return _closestCandidate(results);
}

// Zeptá se, jestli chce uživatel pokračovat s adresou, kterou appka nenašla
// přesně na úrovni čísla popisného (typicky malé vesnice bez zmapovaných
// jednotlivých čísel v OpenStreetMap) - appka pak navede jen do okolí.
Future<bool> _confirmImpreciseAddress(BuildContext context) async {
  final confirmed = await showDialog<bool>(
    context: context,
    builder: (ctx) => AlertDialog(
      title: const Text('Adresa nalezena jen přibližně'),
      content: const Text(
          'Appka nenašla přesné číslo popisné/orientační - navede tě jen '
          'do okolí (např. střed obce), ne přímo k domu. Chceš i tak '
          'pokračovat?'),
      actions: [
        TextButton(
          onPressed: () => Navigator.pop(ctx, false),
          child: const Text('Zrušit, upravím adresu'),
        ),
        FilledButton(
          onPressed: () => Navigator.pop(ctx, true),
          child: const Text('Pokračovat'),
        ),
      ],
    ),
  );
  return confirmed ?? false;
}

// ===================== DATOVÝ MODEL OBJEDNÁVKY =====================
class DeliveryOrder {
  final String id;
  final String address;
  final String phone;
  final double amount;
  final bool prePaid; // true = už zaplaceno, false = platba/dobírka při předání
  final double deliveryFee; // doprava - vybírá se u platby na místě
  final double tip; // dýško - přišlo s online platbou
  final double cashCardTip; // dýško z hotovosti/karty (jen když je zapnuté v nastavení)
  bool bossDelivered; // true = tuhle objednávku vezl šéf sám
  final bool paidByCard; // true = platba na místě proběhla kartou (ne hotově)
  final double lat;
  final double lon;
  final DateTime createdAt;
  bool done;
  DateTime? completedAt;

  DeliveryOrder({
    required this.id,
    required this.address,
    required this.phone,
    required this.amount,
    required this.prePaid,
    this.deliveryFee = 0,
    this.tip = 0,
    this.cashCardTip = 0,
    this.bossDelivered = false,
    this.paidByCard = false,
    required this.lat,
    required this.lon,
    required this.createdAt,
    this.done = false,
    this.completedAt,
  });

  Map<String, dynamic> toJson() => {
        'id': id,
        'address': address,
        'phone': phone,
        'amount': amount,
        'prePaid': prePaid,
        'deliveryFee': deliveryFee,
        'tip': tip,
        'cashCardTip': cashCardTip,
        'bossDelivered': bossDelivered,
        'paidByCard': paidByCard,
        'lat': lat,
        'lon': lon,
        'createdAt': createdAt.toIso8601String(),
        'done': done,
        'completedAt': completedAt?.toIso8601String(),
      };

  factory DeliveryOrder.fromJson(Map<String, dynamic> j) => DeliveryOrder(
        id: j['id'],
        address: j['address'],
        phone: j['phone'],
        amount: (j['amount'] as num).toDouble(),
        prePaid: j['prePaid'] as bool,
        deliveryFee: (j['deliveryFee'] as num?)?.toDouble() ?? 0,
        tip: (j['tip'] as num?)?.toDouble() ?? 0,
        cashCardTip: (j['cashCardTip'] as num?)?.toDouble() ?? 0,
        bossDelivered: j['bossDelivered'] as bool? ?? false,
        paidByCard: j['paidByCard'] as bool? ?? false,
        lat: (j['lat'] as num).toDouble(),
        lon: (j['lon'] as num).toDouble(),
        createdAt: DateTime.parse(j['createdAt']),
        done: j['done'] as bool? ?? false,
        completedAt: j['completedAt'] != null
            ? DateTime.parse(j['completedAt'])
            : null,
      );

  DeliveryOrder copyWith({
    String? address,
    String? phone,
    double? amount,
    bool? prePaid,
    double? deliveryFee,
    double? tip,
    double? cashCardTip,
    bool? paidByCard,
    double? lat,
    double? lon,
  }) {
    return DeliveryOrder(
      id: id,
      address: address ?? this.address,
      phone: phone ?? this.phone,
      amount: amount ?? this.amount,
      prePaid: prePaid ?? this.prePaid,
      deliveryFee: deliveryFee ?? this.deliveryFee,
      tip: tip ?? this.tip,
      cashCardTip: cashCardTip ?? this.cashCardTip,
      paidByCard: paidByCard ?? this.paidByCard,
      lat: lat ?? this.lat,
      lon: lon ?? this.lon,
      createdAt: createdAt,
      done: done,
      completedAt: completedAt,
      bossDelivered: bossDelivered,
    );
  }
}

// ===================== ULOŽENÁ MÍSTA (adresář pro rychlé zadávání) =====================
class SavedPlace {
  final String id;
  final String address;
  final String label; // vlastní název, např. "Kand" (může být prázdný)
  final String phone; // poslední použité číslo na téhle adrese
  final double lat;
  final double lon;
  final DateTime lastUsedAt;

  SavedPlace({
    required this.id,
    required this.address,
    required this.label,
    required this.phone,
    required this.lat,
    required this.lon,
    required this.lastUsedAt,
  });

  Map<String, dynamic> toJson() => {
        'id': id,
        'address': address,
        'label': label,
        'phone': phone,
        'lat': lat,
        'lon': lon,
        'lastUsedAt': lastUsedAt.toIso8601String(),
      };

  factory SavedPlace.fromJson(Map<String, dynamic> j) => SavedPlace(
        id: j['id'],
        address: j['address'],
        label: j['label'] as String? ?? '',
        phone: j['phone'] as String? ?? '',
        lat: (j['lat'] as num).toDouble(),
        lon: (j['lon'] as num).toDouble(),
        lastUsedAt: DateTime.parse(j['lastUsedAt']),
      );

  SavedPlace copyWith({String? label, String? phone, DateTime? lastUsedAt}) {
    return SavedPlace(
      id: id,
      address: address,
      label: label ?? this.label,
      phone: phone ?? this.phone,
      lat: lat,
      lon: lon,
      lastUsedAt: lastUsedAt ?? this.lastUsedAt,
    );
  }
}

class SavedPlacesStore {
  static const _key = 'rozvozka_saved_places_v1';

  static Future<List<SavedPlace>> load() async {
    final prefs = await SharedPreferences.getInstance();
    final raw = prefs.getString(_key);
    if (raw == null || raw.isEmpty) return [];
    try {
      final List list = json.decode(raw);
      return list.map((e) => SavedPlace.fromJson(e)).toList();
    } catch (_) {
      return [];
    }
  }

  static Future<void> save(List<SavedPlace> places) async {
    final prefs = await SharedPreferences.getInstance();
    final raw = json.encode(places.map((p) => p.toJson()).toList());
    await prefs.setString(_key, raw);
  }

  // Uloží/aktualizuje místo podle adresy (case-insensitive). Telefon se vždy
  // přepíše na nově zadaný (ať se aktualizuje, když si tam objedná někdo
  // jiný). Vrátí novou celou aktualizovanou historii.
  static List<SavedPlace> upsert(
    List<SavedPlace> current, {
    required String address,
    required String label,
    required String phone,
    required double lat,
    required double lon,
  }) {
    final normalized = address.trim().toLowerCase();
    final idx =
        current.indexWhere((p) => p.address.trim().toLowerCase() == normalized);
    final updatedList = [...current];
    if (idx != -1) {
      updatedList[idx] = updatedList[idx].copyWith(
        label: label.isNotEmpty ? label : updatedList[idx].label,
        phone: phone.isNotEmpty ? phone : updatedList[idx].phone,
        lastUsedAt: DateTime.now(),
      );
    } else {
      updatedList.insert(
        0,
        SavedPlace(
          id: DateTime.now().microsecondsSinceEpoch.toString(),
          address: address,
          label: label,
          phone: phone,
          lat: lat,
          lon: lon,
          lastUsedAt: DateTime.now(),
        ),
      );
    }
    return updatedList;
  }
}

// ===================== NASTAVENÍ APPKY =====================
class AppSettingsStore {
  static const _key = 'rozvozka_settings_v1';

  static Future<Map<String, dynamic>> load() async {
    final prefs = await SharedPreferences.getInstance();
    final raw = prefs.getString(_key);
    if (raw == null || raw.isEmpty) return {};
    try {
      return json.decode(raw) as Map<String, dynamic>;
    } catch (_) {
      return {};
    }
  }

  static Future<void> save(Map<String, dynamic> settings) async {
    final prefs = await SharedPreferences.getInstance();
    await prefs.setString(_key, json.encode(settings));
  }
}

// ===================== TRVALÉ ÚLOŽIŠTĚ OBJEDNÁVEK =====================
// Ukládá do prohlížeče (shared_preferences), takže fronta přežije zavření appky.
class OrdersStore {
  static const _key = 'rozvozka_orders_v1';

  static Future<List<DeliveryOrder>> load() async {
    final prefs = await SharedPreferences.getInstance();
    final raw = prefs.getString(_key);
    if (raw == null || raw.isEmpty) return [];
    try {
      final List list = json.decode(raw);
      return list.map((e) => DeliveryOrder.fromJson(e)).toList();
    } catch (_) {
      return [];
    }
  }

  static Future<void> save(List<DeliveryOrder> orders) async {
    final prefs = await SharedPreferences.getInstance();
    final raw = json.encode(orders.map((o) => o.toJson()).toList());
    await prefs.setString(_key, raw);
  }
}

// ===================== ÚLOŽIŠTĚ VYÚČTOVÁNÍ SMĚNY =====================
// Ukládá ručně zadané položky (karty, stravenky...) vázané na dnešní datum -
// další den se automaticky nepoužijí (nová směna, nové vyúčtování).
class ShiftSettlementStore {
  static const _key = 'rozvozka_shift_settlement_v1';

  static String _todayKey() {
    final now = DateTime.now();
    return '${now.year}-${now.month}-${now.day}';
  }

  static Future<Map<String, dynamic>?> load() async {
    final prefs = await SharedPreferences.getInstance();
    final raw = prefs.getString(_key);
    if (raw == null || raw.isEmpty) return null;
    try {
      final data = json.decode(raw) as Map<String, dynamic>;
      if (data['date'] != _todayKey()) return null; // z jiného dne, ignorovat
      return data;
    } catch (_) {
      return null;
    }
  }

  static Future<void> save(Map<String, String> values) async {
    final prefs = await SharedPreferences.getInstance();
    final data = {...values, 'date': _todayKey()};
    await prefs.setString(_key, json.encode(data));
  }
}

// ===================== FORMULÁŘ ÚPRAVY OBJEDNÁVKY =====================
// Použije se jak pro nevyřízené, tak pro vyřízené objednávky (bottom sheet).
class _EditOrderSheet extends StatefulWidget {
  final DeliveryOrder order;
  const _EditOrderSheet({required this.order});

  @override
  State<_EditOrderSheet> createState() => _EditOrderSheetState();
}

class _EditOrderSheetState extends State<_EditOrderSheet> {
  late final TextEditingController _addressController;
  late final TextEditingController _phoneController;
  late final TextEditingController _amountController;
  late final TextEditingController _deliveryFeeController;
  late final TextEditingController _tipController;
  late bool _prePaid;
  bool _saving = false;
  String? _errorMessage;

  @override
  void initState() {
    super.initState();
    final o = widget.order;
    _addressController = TextEditingController(text: o.address);
    _phoneController = TextEditingController(text: o.phone);
    _amountController = TextEditingController(text: o.amount.toStringAsFixed(0));
    _deliveryFeeController = TextEditingController(
        text: o.deliveryFee > 0 ? o.deliveryFee.toStringAsFixed(0) : '');
    _tipController =
        TextEditingController(text: o.tip > 0 ? o.tip.toStringAsFixed(0) : '');
    _prePaid = o.prePaid;
  }

  @override
  void dispose() {
    _addressController.dispose();
    _phoneController.dispose();
    _amountController.dispose();
    _deliveryFeeController.dispose();
    _tipController.dispose();
    super.dispose();
  }

  Future<void> _save() async {
    final address = _addressController.text.trim();
    final phone = _phoneController.text.trim();
    final amount =
        double.tryParse(_amountController.text.trim().replaceAll(',', '.')) ?? 0;
    final deliveryFee = double.tryParse(
            _deliveryFeeController.text.trim().replaceAll(',', '.')) ??
        0;
    final tip =
        double.tryParse(_tipController.text.trim().replaceAll(',', '.')) ?? 0;

    if (address.isEmpty || phone.isEmpty) {
      setState(() => _errorMessage = 'Vyplň adresu i telefon.');
      return;
    }

    setState(() {
      _saving = true;
      _errorMessage = null;
    });

    double lat = widget.order.lat;
    double lon = widget.order.lon;

    // adresa se změnila -> musíme znovu dohledat souřadnice
    if (address != widget.order.address) {
      try {
        final result = await _geocodeInChlumec(address);
        if (result == null) {
          setState(() {
            _errorMessage =
                'Novou adresu se nepodařilo najít do 20 km od Chlumce.';
            _saving = false;
          });
          return;
        }
        if (result.distanceKm > _maxDistanceKm) {
          setState(() {
            _errorMessage =
                'Nová adresa je ${result.distanceKm.toStringAsFixed(1)} km od Chlumce — mimo rozsah.';
            _saving = false;
          });
          return;
        }
        if (!result.isPrecise) {
          final ok = await _confirmImpreciseAddress(context);
          if (!ok) {
            setState(() => _saving = false);
            return;
          }
        }
        lat = result.lat;
        lon = result.lon;
      } catch (e) {
        setState(() {
          _errorMessage = 'Chyba: $e';
          _saving = false;
        });
        return;
      }
    }

    final updated = widget.order.copyWith(
      address: address,
      phone: phone,
      amount: amount,
      prePaid: _prePaid,
      deliveryFee: _prePaid ? 0 : deliveryFee,
      tip: _prePaid ? tip : 0,
      lat: lat,
      lon: lon,
    );

    if (mounted) Navigator.pop(context, updated);
  }

  Future<void> _confirmDelete() async {
    final confirmed = await showDialog<bool>(
      context: context,
      builder: (ctx) => AlertDialog(
        title: const Text('Smazat objednávku?'),
        content: Text(
            'Opravdu smazat objednávku "${widget.order.address}"? Tuto akci nelze vrátit zpět.'),
        actions: [
          TextButton(
            onPressed: () => Navigator.pop(ctx, false),
            child: const Text('Zrušit'),
          ),
          FilledButton(
            style: FilledButton.styleFrom(backgroundColor: Colors.red),
            onPressed: () => Navigator.pop(ctx, true),
            child: const Text('Smazat'),
          ),
        ],
      ),
    );
    if (confirmed == true && mounted) {
      Navigator.pop(context, 'DELETE');
    }
  }

  @override
  Widget build(BuildContext context) {
    return Padding(
      padding: EdgeInsets.only(
        left: 16,
        right: 16,
        top: 16,
        bottom: MediaQuery.of(context).viewInsets.bottom + 16,
      ),
      child: SingleChildScrollView(
        child: Column(
          crossAxisAlignment: CrossAxisAlignment.stretch,
          children: [
            Row(
              children: [
                const Expanded(
                  child: Text('Upravit objednávku',
                      style: TextStyle(
                          fontWeight: FontWeight.bold, fontSize: 16)),
                ),
                if (widget.order.done)
                  const Icon(Icons.info_outline, size: 18, color: Colors.grey),
              ],
            ),
            if (widget.order.done)
              const Padding(
                padding: EdgeInsets.only(top: 4),
                child: Text(
                  'Objednávka je už doručená - úprava se promítne i do statistik.',
                  style: TextStyle(fontSize: 12, color: Colors.grey),
                ),
              ),
            const SizedBox(height: 12),
            TextField(
              controller: _addressController,
              decoration: const InputDecoration(
                  labelText: 'Adresa', border: OutlineInputBorder()),
            ),
            const SizedBox(height: 10),
            TextField(
              controller: _phoneController,
              keyboardType: TextInputType.phone,
              inputFormatters: [_PhoneNumberFormatter()],
              decoration: const InputDecoration(
                  labelText: 'Telefon', border: OutlineInputBorder()),
            ),
            const SizedBox(height: 10),
            TextField(
              controller: _amountController,
              keyboardType: const TextInputType.numberWithOptions(decimal: true),
              decoration: const InputDecoration(
                  labelText: 'Cena objednávky (Kč)',
                  border: OutlineInputBorder()),
            ),
            const SizedBox(height: 10),
            SegmentedButton<bool>(
              segments: const [
                ButtonSegment(value: false, label: Text('Platba při předání')),
                ButtonSegment(value: true, label: Text('Už zaplaceno online')),
              ],
              selected: {_prePaid},
              onSelectionChanged: (s) => setState(() => _prePaid = s.first),
            ),
            const SizedBox(height: 10),
            if (_prePaid)
              TextField(
                controller: _tipController,
                keyboardType:
                    const TextInputType.numberWithOptions(decimal: true),
                decoration: const InputDecoration(
                    labelText: 'Dýško (Kč)', border: OutlineInputBorder()),
              )
            else
              TextField(
                controller: _deliveryFeeController,
                keyboardType:
                    const TextInputType.numberWithOptions(decimal: true),
                decoration: const InputDecoration(
                    labelText: 'Doprava (Kč)', border: OutlineInputBorder()),
              ),
            if (_errorMessage != null)
              Padding(
                padding: const EdgeInsets.only(top: 8),
                child: Text(_errorMessage!,
                    style:
                        TextStyle(color: Theme.of(context).colorScheme.error)),
              ),
            const SizedBox(height: 14),
            Row(
              children: [
                Expanded(
                  child: OutlinedButton(
                    onPressed: () => Navigator.pop(context),
                    child: const Text('Zrušit'),
                  ),
                ),
                const SizedBox(width: 10),
                Expanded(
                  child: FilledButton(
                    onPressed: _saving ? null : _save,
                    child: _saving
                        ? const SizedBox(
                            width: 16,
                            height: 16,
                            child: CircularProgressIndicator(strokeWidth: 2))
                        : const Text('Uložit'),
                  ),
                ),
              ],
            ),
            const SizedBox(height: 10),
            TextButton.icon(
              onPressed: _saving ? null : _confirmDelete,
              icon: const Icon(Icons.delete_outline, color: Colors.red),
              label: const Text('Smazat objednávku',
                  style: TextStyle(color: Colors.red)),
            ),
          ],
        ),
      ),
    );
  }
}

void main() {
  WidgetsFlutterBinding.ensureInitialized();
  runApp(const RozvozkaApp());
}

class RozvozkaApp extends StatelessWidget {
  const RozvozkaApp({super.key});

  @override
  Widget build(BuildContext context) {
    return MaterialApp(
      debugShowCheckedModeBanner: false,
      title: 'Rozvozka',
      theme: ThemeData(
        useMaterial3: true,
        colorSchemeSeed: Colors.orange,
      ),
      home: const OrdersScreen(),
    );
  }
}

// ===================== DOMOVSKÁ OBRAZOVKA: FRONTA OBJEDNÁVEK =====================
class OrdersScreen extends StatefulWidget {
  const OrdersScreen({super.key});

  @override
  State<OrdersScreen> createState() => _OrdersScreenState();
}

class _OrdersScreenState extends State<OrdersScreen> {
  List<DeliveryOrder> _orders = [];
  bool _loading = true;
  bool _saving = false;
  String? _errorMessage;

  final _addressController = TextEditingController();
  final _phoneController = TextEditingController();
  final _amountController = TextEditingController();
  final _deliveryFeeController = TextEditingController();
  final _tipController = TextEditingController();
  final _placeLabelController = TextEditingController();
  bool _prePaid = false;

  // Uložená místa (adresář) pro rychlé opětovné zadávání a hledání podle jména.
  List<SavedPlace> _savedPlaces = [];
  List<SavedPlace> _addressSuggestions = [];
  SavedPlace? _selectedSavedPlace;
  double? _lastTipHint; // kolik dali dýška minule na tomhle telefonním čísle

  bool? _trackCashCardTips; // null = ještě se appka nezeptala

  @override
  void initState() {
    super.initState();
    _loadOrders();
    _loadSavedPlaces();
    _loadSettings();
    _addressController.addListener(_onAddressChanged);
    _phoneController.addListener(_onPhoneChanged);
  }

  @override
  void dispose() {
    _addressController.removeListener(_onAddressChanged);
    _phoneController.removeListener(_onPhoneChanged);
    _addressController.dispose();
    _phoneController.dispose();
    _amountController.dispose();
    _deliveryFeeController.dispose();
    _tipController.dispose();
    _placeLabelController.dispose();
    super.dispose();
  }

  // Najde poslední doručenou objednávku na tomhle telefonním čísle - číslo
  // patří konkrétnímu člověku, na rozdíl od adresy, kde může objednávat
  // víc různých lidí (byty, více nájemníků atd.).
  DeliveryOrder? _lastOrderForPhone(String phone) {
    final normalized = phone.replaceAll(' ', '');
    if (normalized.isEmpty) return null;
    final matches = _orders
        .where((o) =>
            o.done &&
            o.completedAt != null &&
            o.phone.replaceAll(' ', '') == normalized)
        .toList()
      ..sort((a, b) => b.completedAt!.compareTo(a.completedAt!));
    return matches.isEmpty ? null : matches.first;
  }

  // Vrátí dýško z poslední objednávky na daném čísle, pokud ho appka umí
  // zjistit (online dýško vždy, dýško z hotovosti/karty jen když je
  // zapnuté v nastavení).
  double? _lastTipForPhone(String phone) {
    final o = _lastOrderForPhone(phone);
    if (o == null) return null;
    if (o.prePaid) return o.tip;
    if (_trackCashCardTips == true) return o.cashCardTip;
    return null;
  }

  void _onPhoneChanged() {
    setState(() {
      _lastTipHint = _lastTipForPhone(_phoneController.text);
    });
  }

  void _onAddressChanged() {
    final q = _addressController.text.trim().toLowerCase();
    setState(() {
      _selectedSavedPlace = null;
      if (q.isEmpty) {
        _addressSuggestions = [];
      } else {
        _addressSuggestions = _savedPlaces
            .where((p) =>
                p.address.toLowerCase().contains(q) ||
                (p.label.isNotEmpty && p.label.toLowerCase().contains(q)))
            .take(5)
            .toList();
      }
    });
  }

  Future<void> _loadSavedPlaces() async {
    final places = await SavedPlacesStore.load();
    setState(() => _savedPlaces = places);
  }

  Future<void> _loadSettings() async {
    final settings = await AppSettingsStore.load();
    setState(() {
      _trackCashCardTips = settings['trackCashCardTips'] as bool?;
    });
    if (_trackCashCardTips == null) {
      // appka se ještě nikdy nezeptala -> zeptej se teď
      WidgetsBinding.instance.addPostFrameCallback((_) => _askTipSetting());
    }
  }

  Future<void> _askTipSetting() async {
    if (!mounted) return;
    final answer = await showDialog<bool>(
      context: context,
      barrierDismissible: false,
      builder: (ctx) => AlertDialog(
        title: const Text('Počítat dýška i z hotovosti/karty?'),
        content: const Text(
            'Chcete si počítat dýška i při platbě hotově a kartou? Appka se '
            'vás při dokončení objednávky zeptá, kolik jste reálně vybral/a, '
            'a rozdíl oproti ceně objednávky bude dýško ve statistikách. '
            'Tuhle volbu můžete kdykoliv později změnit v nastavení.'),
        actions: [
          TextButton(
            onPressed: () => Navigator.pop(ctx, false),
            child: const Text('Nechci'),
          ),
          FilledButton(
            onPressed: () => Navigator.pop(ctx, true),
            child: const Text('Ano, chci'),
          ),
        ],
      ),
    );
    final value = answer ?? false;
    setState(() => _trackCashCardTips = value);
    await AppSettingsStore.save({'trackCashCardTips': value});
  }

  Future<void> _loadOrders() async {
    try {
      final orders = await OrdersStore.load();
      setState(() {
        _orders = orders;
        _loading = false;
      });
    } catch (e) {
      setState(() {
        _orders = [];
        _loading = false;
        _errorMessage = 'Nepodařilo se načíst uložená data: $e';
      });
    }
  }

  Future<void> _addOrder() async {
    final address = _addressController.text.trim();
    final phone = _phoneController.text.trim();
    final amountText = _amountController.text.trim().replaceAll(',', '.');
    final amount = double.tryParse(amountText) ?? 0;
    final deliveryFeeText =
        _deliveryFeeController.text.trim().replaceAll(',', '.');
    final deliveryFee = double.tryParse(deliveryFeeText) ?? 0;
    final tipText = _tipController.text.trim().replaceAll(',', '.');
    final tip = double.tryParse(tipText) ?? 0;
    final placeLabel = _placeLabelController.text.trim();

    if (address.isEmpty || phone.isEmpty) {
      setState(() => _errorMessage = 'Vyplň adresu i telefon.');
      return;
    }

    setState(() {
      _saving = true;
      _errorMessage = null;
    });

    try {
      double lat;
      double lon;

      // Pokud uživatel vybral uložené místo a adresu od té doby nezměnil,
      // použijeme rovnou uložené souřadnice - žádný síťový dotaz navíc.
      if (_selectedSavedPlace != null &&
          _selectedSavedPlace!.address == address) {
        lat = _selectedSavedPlace!.lat;
        lon = _selectedSavedPlace!.lon;
      } else {
        final result = await _geocodeInChlumec(address);
        if (result == null) {
          setState(() {
            _errorMessage =
                'Adresu se nepodařilo najít do 20 km od Chlumce nad Cidlinou.';
            _saving = false;
          });
          return;
        }
        if (result.distanceKm > _maxDistanceKm) {
          setState(() {
            _errorMessage =
                'Adresa je ${result.distanceKm.toStringAsFixed(1)} km od Chlumce — mimo rozsah 20 km.';
            _saving = false;
          });
          return;
        }
        if (!result.isPrecise) {
          final ok = await _confirmImpreciseAddress(context);
          if (!ok) {
            setState(() => _saving = false);
            return;
          }
        }
        lat = result.lat;
        lon = result.lon;
      }

      final order = DeliveryOrder(
        id: DateTime.now().microsecondsSinceEpoch.toString(),
        address: address,
        phone: phone,
        amount: amount,
        prePaid: _prePaid,
        deliveryFee: _prePaid ? 0 : deliveryFee,
        tip: _prePaid ? tip : 0,
        lat: lat,
        lon: lon,
        createdAt: DateTime.now(),
      );

      final updatedOrders = [order, ..._orders]; // nejnovější nahoře
      await OrdersStore.save(updatedOrders);

      final updatedPlaces = SavedPlacesStore.upsert(
        _savedPlaces,
        address: address,
        label: placeLabel,
        phone: phone,
        lat: lat,
        lon: lon,
      );
      await SavedPlacesStore.save(updatedPlaces);

      setState(() {
        _orders = updatedOrders;
        _savedPlaces = updatedPlaces;
        _saving = false;
        _addressController.clear();
        _phoneController.clear();
        _amountController.clear();
        _deliveryFeeController.clear();
        _tipController.clear();
        _placeLabelController.clear();
        _prePaid = false;
        _selectedSavedPlace = null;
        _addressSuggestions = [];
      });
    } catch (e) {
      setState(() {
        _errorMessage = 'Chyba: $e';
        _saving = false;
      });
    }
  }

  Future<void> _openDelivery(DeliveryOrder order) async {
    await Navigator.push(
      context,
      MaterialPageRoute(
        builder: (_) => DeliveryScreen(
          order: order,
          trackCashCardTips: _trackCashCardTips ?? false,
        ),
      ),
    );
    _loadOrders(); // po návratu (např. po označení "Doručeno") znovu načteme
  }

  Future<void> _editOrder(DeliveryOrder order) async {
    final result = await showModalBottomSheet<Object?>(
      context: context,
      isScrollControlled: true,
      builder: (_) => _EditOrderSheet(order: order),
    );
    if (result == 'DELETE') {
      final newList = _orders.where((o) => o.id != order.id).toList();
      await OrdersStore.save(newList);
      setState(() => _orders = newList);
    } else if (result is DeliveryOrder) {
      final idx = _orders.indexWhere((o) => o.id == order.id);
      if (idx != -1) {
        final newList = [..._orders];
        newList[idx] = result;
        await OrdersStore.save(newList);
        setState(() => _orders = newList);
      }
    }
  }

  Future<void> _toggleBossDelivered(DeliveryOrder order) async {
    final idx = _orders.indexWhere((o) => o.id == order.id);
    if (idx == -1) return;
    final newList = [..._orders];
    newList[idx].bossDelivered = !newList[idx].bossDelivered;
    await OrdersStore.save(newList);
    setState(() => _orders = newList);
  }

  Future<void> _togglePaidByCard(DeliveryOrder order) async {
    final idx = _orders.indexWhere((o) => o.id == order.id);
    if (idx == -1) return;
    final newList = [..._orders];
    newList[idx] = newList[idx].copyWith(paidByCard: !newList[idx].paidByCard);
    await OrdersStore.save(newList);
    setState(() => _orders = newList);
  }

  List<DeliveryOrder> get _pending =>
      _orders.where((o) => !o.done).toList();

  List<DeliveryOrder> get _completedToday {
    final now = DateTime.now();
    return _orders
        .where((o) =>
            o.done &&
            o.completedAt != null &&
            o.completedAt!.year == now.year &&
            o.completedAt!.month == now.month &&
            o.completedAt!.day == now.day)
        .toList()
      ..sort((a, b) => b.completedAt!.compareTo(a.completedAt!));
  }

  String _orderSubtitle(DeliveryOrder o) {
    if (o.prePaid) {
      final tipPart =
          o.tip > 0 ? ' + ${o.tip.toStringAsFixed(0)} Kč dýško' : '';
      return '${o.phone} · ${o.amount.toStringAsFixed(0)} Kč online$tipPart';
    } else {
      final total = o.amount + o.deliveryFee;
      final feePart = o.deliveryFee > 0
          ? ' (z toho doprava ${o.deliveryFee.toStringAsFixed(0)} Kč)'
          : '';
      return '${o.phone} · vybrat ${total.toStringAsFixed(0)} Kč$feePart';
    }
  }

  @override
  Widget build(BuildContext context) {
    return Scaffold(
      appBar: AppBar(
        leading: IconButton(
          icon: const Text('💰', style: TextStyle(fontSize: 22)),
          tooltip: 'Vyúčtování směny',
          onPressed: () async {
            await Navigator.push(
              context,
              MaterialPageRoute(builder: (_) => const ShiftSettlementScreen()),
            );
          },
        ),
        title: const Text('Rozvozka'),
        actions: [
          IconButton(
            icon: const Icon(Icons.settings_outlined),
            tooltip: 'Nastavení',
            onPressed: () async {
              final changed = await Navigator.push<bool>(
                context,
                MaterialPageRoute(
                  builder: (_) => SettingsScreen(
                    trackCashCardTips: _trackCashCardTips ?? false,
                  ),
                ),
              );
              if (changed == true) _loadSettings();
            },
          ),
          IconButton(
            icon: const Icon(Icons.bar_chart),
            tooltip: 'Statistiky',
            onPressed: () async {
              await Navigator.push(
                context,
                MaterialPageRoute(builder: (_) => const StatsScreen()),
              );
            },
          ),
        ],
      ),
      body: _loading
          ? const Center(child: CircularProgressIndicator())
          : ListView(
              padding: const EdgeInsets.all(12),
              children: [
                Card(
                  child: Padding(
                    padding: const EdgeInsets.all(14),
                    child: Column(
                      crossAxisAlignment: CrossAxisAlignment.stretch,
                      children: [
                        const Text('Nová objednávka',
                            style: TextStyle(
                                fontWeight: FontWeight.bold, fontSize: 16)),
                        const SizedBox(height: 10),
                        TextField(
                          controller: _addressController,
                          decoration: InputDecoration(
                            labelText: 'Adresa',
                            helperText: 'Napiš adresu nebo název místa '
                                '(např. dřívější firmu)',
                            prefixIcon: const Icon(Icons.location_on_outlined),
                            border: const OutlineInputBorder(),
                            suffixIcon: _addressController.text.isNotEmpty
                                ? IconButton(
                                    icon: const Icon(Icons.clear),
                                    onPressed: () {
                                      _addressController.clear();
                                    },
                                  )
                                : null,
                          ),
                        ),
                        if (_addressSuggestions.isNotEmpty)
                          Container(
                            margin: const EdgeInsets.only(top: 4),
                            decoration: BoxDecoration(
                              color: Colors.white,
                              border: Border.all(color: Colors.grey.shade300),
                              borderRadius: BorderRadius.circular(8),
                            ),
                            child: Column(
                              mainAxisSize: MainAxisSize.min,
                              children: _addressSuggestions
                                  .map((p) => ListTile(
                                        dense: true,
                                        leading: const Icon(Icons.history, size: 18),
                                        title: Text(
                                            p.label.isNotEmpty ? p.label : p.address,
                                            style: const TextStyle(fontSize: 14)),
                                        subtitle: Text(
                                          [
                                            if (p.label.isNotEmpty) p.address,
                                            if (p.phone.isNotEmpty) p.phone,
                                          ].join(' · '),
                                          style: const TextStyle(fontSize: 11),
                                        ),
                                        onTap: () {
                                          setState(() {
                                            _addressController.text = p.address;
                                            _selectedSavedPlace = p;
                                            _addressSuggestions = [];
                                            if (p.phone.isNotEmpty) {
                                              _phoneController.text = p.phone;
                                            }
                                            _lastTipHint =
                                                _lastTipForPhone(_phoneController.text);
                                          });
                                        },
                                      ))
                                  .toList(),
                            ),
                          ),
                        const SizedBox(height: 10),
                        TextField(
                          controller: _placeLabelController,
                          decoration: const InputDecoration(
                            labelText: 'Název místa (nepovinné)',
                            helperText: 'Např. název firmy - příště podle něj najdeš adresu',
                            prefixIcon: Icon(Icons.label_outline),
                            border: OutlineInputBorder(),
                          ),
                        ),
                        const SizedBox(height: 10),
                        TextField(
                          controller: _phoneController,
                          keyboardType: TextInputType.phone,
                          inputFormatters: [_PhoneNumberFormatter()],
                          decoration: const InputDecoration(
                            labelText: 'Telefon zákazníka',
                            prefixIcon: Icon(Icons.phone_outlined),
                            border: OutlineInputBorder(),
                          ),
                        ),
                        if (_lastTipHint != null)
                          Container(
                            margin: const EdgeInsets.only(top: 6),
                            padding: const EdgeInsets.symmetric(
                                horizontal: 10, vertical: 7),
                            decoration: BoxDecoration(
                              color: Colors.blueGrey.shade50,
                              borderRadius: BorderRadius.circular(8),
                            ),
                            child: Row(
                              children: [
                                Icon(Icons.info_outline,
                                    size: 16, color: Colors.blueGrey.shade700),
                                const SizedBox(width: 8),
                                Text(
                                  'Naposledy dýško: ${_lastTipHint!.toStringAsFixed(0)} Kč',
                                  style: TextStyle(
                                    fontSize: 12,
                                    fontWeight: FontWeight.w600,
                                    color: Colors.blueGrey.shade900,
                                  ),
                                ),
                              ],
                            ),
                          ),
                        const SizedBox(height: 10),
                        TextField(
                          controller: _amountController,
                          keyboardType: const TextInputType.numberWithOptions(
                              decimal: true),
                          decoration: const InputDecoration(
                            labelText: 'Cena objednávky (Kč)',
                            prefixIcon: Icon(Icons.payments_outlined),
                            border: OutlineInputBorder(),
                          ),
                        ),
                        const SizedBox(height: 10),
                        SegmentedButton<bool>(
                          segments: const [
                            ButtonSegment(
                                value: false, label: Text('Platba při předání')),
                            ButtonSegment(
                                value: true, label: Text('Už zaplaceno online')),
                          ],
                          selected: {_prePaid},
                          onSelectionChanged: (s) =>
                              setState(() => _prePaid = s.first),
                        ),
                        const SizedBox(height: 10),
                        if (_prePaid)
                          TextField(
                            controller: _tipController,
                            keyboardType:
                                const TextInputType.numberWithOptions(
                                    decimal: true),
                            decoration: const InputDecoration(
                              labelText: 'Dýško (Kč)',
                              helperText: 'Dýško, které přišlo s online platbou',
                              prefixIcon:
                                  Icon(Icons.volunteer_activism_outlined),
                              border: OutlineInputBorder(),
                            ),
                          )
                        else
                          TextField(
                            controller: _deliveryFeeController,
                            keyboardType:
                                const TextInputType.numberWithOptions(
                                    decimal: true),
                            decoration: const InputDecoration(
                              labelText: 'Doprava (Kč)',
                              helperText: 'Kolik navíc vybrat za dopravu',
                              prefixIcon: Icon(Icons.local_shipping_outlined),
                              border: OutlineInputBorder(),
                            ),
                          ),
                        if (_errorMessage != null)
                          Padding(
                            padding: const EdgeInsets.only(top: 8),
                            child: Text(
                              _errorMessage!,
                              style: TextStyle(
                                  color: Theme.of(context).colorScheme.error),
                            ),
                          ),
                        const SizedBox(height: 12),
                        FilledButton.icon(
                          onPressed: _saving ? null : _addOrder,
                          icon: _saving
                              ? const SizedBox(
                                  width: 16,
                                  height: 16,
                                  child: CircularProgressIndicator(
                                      strokeWidth: 2))
                              : const Icon(Icons.add),
                          label: const Text('Přidat objednávku'),
                        ),
                      ],
                    ),
                  ),
                ),
                const SizedBox(height: 18),
                Text('Nevyřízené objednávky (${_pending.length})',
                    style: const TextStyle(
                        fontWeight: FontWeight.bold, fontSize: 16)),
                const SizedBox(height: 8),
                if (_pending.isEmpty)
                  const Padding(
                    padding: EdgeInsets.symmetric(vertical: 24),
                    child: Center(
                      child: Text('Zatím žádné čekající objednávky.',
                          style: TextStyle(color: Colors.grey)),
                    ),
                  ),
                ..._pending.map((o) => Card(
                      child: ListTile(
                        leading: CircleAvatar(
                          backgroundColor: o.prePaid
                              ? Colors.green.shade100
                              : Colors.orange.shade100,
                          child: Icon(
                            o.prePaid ? Icons.check : Icons.payments,
                            color:
                                o.prePaid ? Colors.green : Colors.orange,
                            size: 20,
                          ),
                        ),
                        title: Text(o.address,
                            maxLines: 1, overflow: TextOverflow.ellipsis),
                        subtitle: Text(_orderSubtitle(o)),
                        trailing: Row(
                          mainAxisSize: MainAxisSize.min,
                          children: [
                            IconButton(
                              icon: const Icon(Icons.edit_outlined, size: 20),
                              tooltip: 'Upravit',
                              onPressed: () => _editOrder(o),
                            ),
                            const Icon(Icons.chevron_right),
                          ],
                        ),
                        onTap: () => _openDelivery(o),
                      ),
                    )),
                const SizedBox(height: 18),
                Card(
                  clipBehavior: Clip.antiAlias,
                  child: ExpansionTile(
                    leading: const Icon(Icons.history),
                    title: Text('Vyřízené objednávky dnes (${_completedToday.length})',
                        style: const TextStyle(fontWeight: FontWeight.bold)),
                    children: [
                      if (_completedToday.isEmpty)
                        const Padding(
                          padding: EdgeInsets.all(16),
                          child: Text('Dnes zatím žádná hotová objednávka.',
                              style: TextStyle(color: Colors.grey)),
                        ),
                      ..._completedToday.map((o) => Padding(
                            padding: const EdgeInsets.symmetric(
                                horizontal: 16, vertical: 8),
                            child: Column(
                              crossAxisAlignment: CrossAxisAlignment.start,
                              children: [
                                Row(
                                  children: [
                                    Expanded(
                                      child: Text(o.address,
                                          style: const TextStyle(
                                              fontWeight: FontWeight.w600)),
                                    ),
                                    IconButton(
                                      icon: const Icon(Icons.edit_outlined, size: 18),
                                      tooltip: 'Upravit',
                                      padding: EdgeInsets.zero,
                                      constraints: const BoxConstraints(),
                                      visualDensity: VisualDensity.compact,
                                      onPressed: () => _editOrder(o),
                                    ),
                                    const SizedBox(width: 8),
                                    Text(
                                      TimeOfDay.fromDateTime(o.completedAt!)
                                          .format(context),
                                      style: const TextStyle(
                                          color: Colors.grey, fontSize: 12),
                                    ),
                                  ],
                                ),
                                const SizedBox(height: 2),
                                Wrap(
                                  spacing: 6,
                                  runSpacing: 4,
                                  children: [
                                    Chip(
                                      visualDensity: VisualDensity.compact,
                                      label: Text(
                                          'Cena ${o.amount.toStringAsFixed(0)} Kč'),
                                    ),
                                    if (!o.prePaid && o.deliveryFee > 0)
                                      Chip(
                                        visualDensity: VisualDensity.compact,
                                        label: Text(
                                            'Doprava ${o.deliveryFee.toStringAsFixed(0)} Kč'),
                                      ),
                                    if (o.prePaid && o.tip > 0)
                                      Chip(
                                        visualDensity: VisualDensity.compact,
                                        label: Text(
                                            'Dýško ${o.tip.toStringAsFixed(0)} Kč'),
                                      ),
                                    Chip(
                                      visualDensity: VisualDensity.compact,
                                      backgroundColor: o.prePaid
                                          ? Colors.green.shade50
                                          : Colors.orange.shade50,
                                      label: Text(
                                          o.prePaid ? 'online' : 'na místě'),
                                    ),
                                    ActionChip(
                                      visualDensity: VisualDensity.compact,
                                      avatar: Icon(
                                        o.bossDelivered
                                            ? Icons.check_circle
                                            : Icons.person_outline,
                                        size: 16,
                                        color: o.bossDelivered
                                            ? Colors.white
                                            : Colors.grey.shade700,
                                      ),
                                      backgroundColor: o.bossDelivered
                                          ? Colors.blueGrey.shade400
                                          : null,
                                      label: Text(
                                        'Jel šéf',
                                        style: TextStyle(
                                          color: o.bossDelivered
                                              ? Colors.white
                                              : null,
                                        ),
                                      ),
                                      onPressed: () => _toggleBossDelivered(o),
                                    ),
                                    if ((_trackCashCardTips ?? false) && !o.prePaid)
                                      ActionChip(
                                        visualDensity: VisualDensity.compact,
                                        avatar: Icon(
                                          o.paidByCard
                                              ? Icons.credit_card
                                              : Icons.payments_outlined,
                                          size: 16,
                                          color: o.paidByCard
                                              ? Colors.white
                                              : Colors.grey.shade700,
                                        ),
                                        backgroundColor: o.paidByCard
                                            ? Colors.indigo.shade400
                                            : null,
                                        label: Text(
                                          o.paidByCard ? 'Kartou' : 'Hotově',
                                          style: TextStyle(
                                            color: o.paidByCard
                                                ? Colors.white
                                                : null,
                                          ),
                                        ),
                                        onPressed: () => _togglePaidByCard(o),
                                      ),
                                  ],
                                ),
                              ],
                            ),
                          )),
                      const SizedBox(height: 8),
                    ],
                  ),
                ),
              ],
            ),
    );
  }
}

// ===================== OBRAZOVKA DORUČENÍ (mapa pro 1 objednávku) =====================
class DeliveryScreen extends StatefulWidget {
  final DeliveryOrder order;
  final bool trackCashCardTips;
  const DeliveryScreen(
      {super.key, required this.order, this.trackCashCardTips = false});

  @override
  State<DeliveryScreen> createState() => _DeliveryScreenState();
}

class _DeliveryScreenState extends State<DeliveryScreen>
    with SingleTickerProviderStateMixin {
  final MapController _mapController = MapController();
  LatLng _myLocation = _chlumecCenter;
  List<LatLng> _routePoints = [];
  List<LatLng> _displayRoutePoints = []; // trasa "ořezaná" podle aktuální polohy
  List<Map<String, dynamic>> _routeSteps = [];
  List<double> _stepCumulative = []; // kumulativní vzdálenost na konci každého kroku
  Map<String, dynamic>? _liveUpcomingStep;
  double? _liveDistanceToManeuver;
  double? _heading;
  StreamSubscription<Position>? _positionStream;
  DateTime? _lastRouteCalc;
  bool _followMe = true;
  double? _distanceKm;
  int? _durationMin;
  double? _speedKmh;
  String? _statusMessage;

  // --- Plynulá animace kamery (aby appka místo skoků "jela" jako navigace) ---
  late final AnimationController _camAnim;
  LatLng _camFrom = _chlumecCenter;
  LatLng _camTo = _chlumecCenter;
  double _camRotFrom = 0;
  double _camRotTo = 0;
  double _camZoom = 16;

  @override
  void initState() {
    super.initState();
    _camAnim = AnimationController(
      vsync: this,
      duration: const Duration(milliseconds: 450),
    )..addListener(_onCameraTick);
    _init();
  }

  @override
  void dispose() {
    _camAnim.dispose();
    _positionStream?.cancel();
    super.dispose();
  }

  void _onCameraTick() {
    final t = Curves.easeOut.transform(_camAnim.value);
    final lat = _camFrom.latitude + (_camTo.latitude - _camFrom.latitude) * t;
    final lon =
        _camFrom.longitude + (_camTo.longitude - _camFrom.longitude) * t;
    final rot = _camRotFrom + _shortestAngleDiff(_camRotFrom, _camRotTo) * t;
    _mapController.moveAndRotate(LatLng(lat, lon), _camZoom, rot);
  }

  // Otočení "kratší cestou" (např. z 350° na 10° = +20°, ne -340°),
  // ať se mapa netočí zbytečně skoro celým kruhem.
  double _shortestAngleDiff(double from, double to) {
    var diff = (to - from) % 360;
    if (diff > 180) diff -= 360;
    if (diff < -180) diff += 360;
    return diff;
  }

  void _animateCameraTo(LatLng target, double rotationDeg, {double? zoom}) {
    final cam = _mapController.camera;
    _camFrom = cam.center;
    _camTo = target;
    _camRotFrom = cam.rotation;
    _camRotTo = rotationDeg;
    _camZoom = zoom ?? cam.zoom;
    _camAnim.forward(from: 0);
  }

  // Čím blíž jsme k cíli, tím víc appka přiblíží mapu - ať je na poslední
  // metry vidět, kde přesně je barák, ne jen obecná oblast.
  double _zoomForDistance(double meters) {
    if (meters < 200) return 18;
    if (meters < 1000) return 16;
    return 15;
  }

  // Mezi jednotlivými přepočty trasy z OSRM appka lokálně dopočítá, kde na
  // trase přesně jsme - ořeže zobrazenou modrou čáru za náma a přepočítá
  // vzdálenost k dalšímu odbočení, aniž by musela čekat na síťový dotaz.
  void _updateLiveRouteProgress() {
    if (_routePoints.length < 2) return;
    final proj = _projectOntoRoute(_myLocation, _routePoints);
    if (proj == null) return;

    _displayRoutePoints = [
      proj.point,
      ..._routePoints.sublist(proj.segmentIndex + 1),
    ];

    if (_stepCumulative.isNotEmpty) {
      int idx = _stepCumulative.indexWhere((c) => c > proj.distanceAlongRoute);
      if (idx == -1) idx = _stepCumulative.length - 1;
      final upcomingIdx =
          (idx + 1 < _routeSteps.length) ? idx + 1 : idx;
      _liveUpcomingStep = _routeSteps[upcomingIdx];
      final remaining = _stepCumulative[idx] - proj.distanceAlongRoute;
      _liveDistanceToManeuver = remaining < 0 ? 0 : remaining;
    }
  }

  Future<void> _init() async {
    try {
      final pos = await Geolocator.getCurrentPosition(
        desiredAccuracy: LocationAccuracy.high,
        timeLimit: const Duration(seconds: 8),
      );
      setState(() => _myLocation = LatLng(pos.latitude, pos.longitude));
      _mapController.move(_myLocation, 16);
      _camZoom = 16;
    } catch (e) {
      setState(() => _statusMessage =
          'Nepodařilo se získat polohu ($e). Trasa se zobrazí od Chlumce.');
    }
    await _computeRoute();

    _positionStream = Geolocator.getPositionStream(
      locationSettings: const LocationSettings(
        accuracy: LocationAccuracy.high,
        distanceFilter: 5,
      ),
    ).listen((pos) {
      setState(() {
        _myLocation = LatLng(pos.latitude, pos.longitude);
        // heading bereme jen když se opravdu hýbeme, jinak GPS kompas
        // zbytečně cuká
        if (pos.speed > 1.0 && pos.heading >= 0) {
          _heading = pos.heading;
        }
        _speedKmh = pos.speed > 0 ? pos.speed * 3.6 : 0;
        _updateLiveRouteProgress();
      });
      if (_followMe) {
        final distToDest = Geolocator.distanceBetween(
          _myLocation.latitude,
          _myLocation.longitude,
          widget.order.lat,
          widget.order.lon,
        );
        _animateCameraTo(
          _myLocation,
          _heading != null ? -_heading! : 0,
          zoom: _zoomForDistance(distToDest),
        );
      }
      // trasu z internetu přepočítáváme jen občas (ne při každém 5m posunu),
      // ať nezahltíme veřejný OSRM server - mezitím appka polohu na trase
      // dopočítává sama lokálně (viz _updateLiveRouteProgress výše)
      final now = DateTime.now();
      if (_lastRouteCalc == null ||
          now.difference(_lastRouteCalc!) > const Duration(seconds: 10)) {
        _lastRouteCalc = now;
        _computeRoute(silent: true);
      }
    });
  }

  Future<void> _computeRoute({bool silent = false}) async {
    try {
      final routeUrl = Uri.parse(
          'https://router.project-osrm.org/route/v1/driving/'
          '${_myLocation.longitude},${_myLocation.latitude};${widget.order.lon},${widget.order.lat}'
          '?overview=full&geometries=geojson&steps=true');
      final res = await http.get(routeUrl);
      if (res.statusCode == 200) {
        final data = json.decode(res.body);
        if (data['routes'] != null && data['routes'].isNotEmpty) {
          final route = data['routes'][0];
          final List coords = route['geometry']['coordinates'];
          final List legs = route['legs'] as List? ?? [];
          final List steps =
              legs.isNotEmpty ? (legs[0]['steps'] as List? ?? []) : [];
          final stepsList = steps.cast<Map<String, dynamic>>();
          final cumList = <double>[];
          double cum = 0;
          for (final step in stepsList) {
            cum += (step['distance'] as num?)?.toDouble() ?? 0;
            cumList.add(cum);
          }
          setState(() {
            _routePoints =
                coords.map<LatLng>((c) => LatLng(c[1], c[0])).toList();
            _routeSteps = stepsList;
            _stepCumulative = cumList;
            _distanceKm = (route['distance'] as num) / 1000;
            _durationMin = ((route['duration'] as num) / 60).round();
            _statusMessage = null;
            _updateLiveRouteProgress();
          });
          if (_followMe == false) _fitBounds();
        }
      }
    } catch (e) {
      if (!silent) {
        setState(() => _statusMessage = 'Trasu se nepodařilo spočítat.');
      }
    }
  }

  void _fitBounds() {
    if (_routePoints.isEmpty) return;
    final bounds = LatLngBounds.fromPoints(_routePoints);
    _mapController.fitCamera(
      CameraFit.bounds(bounds: bounds, padding: const EdgeInsets.all(48)),
    );
  }

  Future<void> _callCustomer() async {
    final uri = Uri.parse('tel:${widget.order.phone.replaceAll(' ', '')}');
    if (await canLaunchUrl(uri)) {
      await launchUrl(uri);
    }
  }

  Future<void> _markDone() async {
    double cashCardTip = 0;
    bool paidByCard = false;

    if (widget.trackCashCardTips && !widget.order.prePaid) {
      final expected = widget.order.amount + widget.order.deliveryFee;
      final controller =
          TextEditingController(text: expected.toStringAsFixed(0));
      bool localPaidByCard = false;
      final collected = await showDialog<double>(
        context: context,
        builder: (ctx) => StatefulBuilder(
          builder: (ctx, setDialogState) => AlertDialog(
            title: const Text('Kolik jste reálně vybral/a?'),
            content: Column(
              mainAxisSize: MainAxisSize.min,
              crossAxisAlignment: CrossAxisAlignment.start,
              children: [
                Text('Mělo se vybrat: ${expected.toStringAsFixed(0)} Kč'),
                const SizedBox(height: 12),
                TextField(
                  controller: controller,
                  autofocus: true,
                  keyboardType:
                      const TextInputType.numberWithOptions(decimal: true),
                  decoration: const InputDecoration(
                    labelText: 'Kolik vybráno (Kč)',
                    border: OutlineInputBorder(),
                  ),
                ),
                const SizedBox(height: 12),
                SegmentedButton<bool>(
                  segments: const [
                    ButtonSegment(value: false, label: Text('Hotově')),
                    ButtonSegment(value: true, label: Text('Kartou')),
                  ],
                  selected: {localPaidByCard},
                  onSelectionChanged: (s) =>
                      setDialogState(() => localPaidByCard = s.first),
                ),
              ],
            ),
            actions: [
              TextButton(
                onPressed: () => Navigator.pop(ctx, null),
                child: const Text('Zrušit'),
              ),
              FilledButton(
                onPressed: () {
                  final v = double.tryParse(
                      controller.text.trim().replaceAll(',', '.'));
                  paidByCard = localPaidByCard;
                  Navigator.pop(ctx, v ?? expected);
                },
                child: const Text('Potvrdit'),
              ),
            ],
          ),
        ),
      );
      if (collected == null) return; // uživatel zrušil, nedokončujeme
      cashCardTip = collected - expected;
    }

    final orders = await OrdersStore.load();
    final idx = orders.indexWhere((o) => o.id == widget.order.id);
    if (idx != -1) {
      final updated = orders[idx]
          .copyWith(cashCardTip: cashCardTip, paidByCard: paidByCard);
      updated.done = true;
      updated.completedAt = DateTime.now();
      orders[idx] = updated;
      await OrdersStore.save(orders);
    }
    if (mounted) Navigator.pop(context);
  }

  @override
  Widget build(BuildContext context) {
    final o = widget.order;
    return Scaffold(
      appBar: AppBar(
        title: Text(o.address, overflow: TextOverflow.ellipsis),
      ),
      body: Column(
        children: [
          // Kompaktní info řádek (telefon + co vybrat) - jeden řádek, ať mapě
          // zbyde co nejvíc místa
          Padding(
            padding: const EdgeInsets.fromLTRB(14, 8, 14, 8),
            child: Row(
              children: [
                Icon(Icons.phone, size: 15, color: Colors.grey.shade600),
                const SizedBox(width: 4),
                Text(o.phone, style: const TextStyle(fontSize: 13)),
                const SizedBox(width: 12),
                Expanded(
                  child: Text(
                    o.prePaid
                        ? 'Online: ${o.amount.toStringAsFixed(0)} Kč'
                            '${o.tip > 0 ? " · dýško ${o.tip.toStringAsFixed(0)}" : ""}'
                        : 'Vybrat: ${(o.amount + o.deliveryFee).toStringAsFixed(0)} Kč',
                    style: TextStyle(
                      color: o.prePaid ? Colors.green.shade700 : Colors.orange.shade800,
                      fontWeight: FontWeight.w700,
                      fontSize: 13,
                    ),
                    textAlign: TextAlign.right,
                    overflow: TextOverflow.ellipsis,
                  ),
                ),
              ],
            ),
          ),
          if (_statusMessage != null)
            Padding(
              padding: const EdgeInsets.only(left: 14, right: 14, bottom: 6),
              child: Text(_statusMessage!,
                  style: TextStyle(color: Theme.of(context).colorScheme.error, fontSize: 12)),
            ),
          Expanded(
            child: Stack(
              children: [
                FlutterMap(
                  mapController: _mapController,
                  options: MapOptions(
                    initialCenter: _myLocation,
                    initialZoom: 14,
                    onPositionChanged: (pos, hasGesture) {
                      if (hasGesture && _followMe) {
                        setState(() => _followMe = false);
                      }
                    },
                  ),
                  children: [
                    TileLayer(
                      urlTemplate:
                          'https://tile.openstreetmap.org/{z}/{x}/{y}.png',
                      userAgentPackageName: 'com.example.rozvozka',
                    ),
                    if (_routePoints.isNotEmpty)
                      PolylineLayer(polylines: [
                        Polyline(
                            points: _displayRoutePoints.isNotEmpty
                                ? _displayRoutePoints
                                : _routePoints,
                            strokeWidth: 6,
                            color: const Color(0xFF2F7FF0)),
                      ]),
                    MarkerLayer(markers: [
                      Marker(
                        point: LatLng(o.lat, o.lon),
                        width: 44,
                        height: 44,
                        child: Container(
                          decoration: BoxDecoration(
                            color: const Color(0xFFB3261E),
                            shape: BoxShape.circle,
                            border: Border.all(color: Colors.white, width: 3),
                            boxShadow: const [
                              BoxShadow(
                                  color: Colors.black45,
                                  blurRadius: 6,
                                  offset: Offset(0, 2)),
                            ],
                          ),
                          alignment: Alignment.center,
                          child: const Icon(Icons.flag,
                              color: Colors.white, size: 22),
                        ),
                      ),
                      // Šipku na mapě (vázanou na GPS souřadnice) ukazujeme jen
                      // když appka nesleduje - jinak je šipka fixní uprostřed
                      // obrazovky (viz níže) a hýbe se mapa pod ní.
                      if (!_followMe)
                        Marker(
                          point: _myLocation,
                          width: 40,
                          height: 40,
                          child: Transform.rotate(
                            angle: (_heading ?? 0) * pi / 180,
                            child: const Icon(
                              Icons.navigation,
                              color: Color(0xFF2F7FF0),
                              size: 36,
                              shadows: [
                                Shadow(color: Colors.black45, blurRadius: 6),
                              ],
                            ),
                          ),
                        ),
                    ]),
                  ],
                ),
                // Fixní šipka uprostřed obrazovky (jen v režimu sledování) -
                // appka se "sune" pod ní, ne naopak.
                if (_followMe)
                  const IgnorePointer(
                    child: Center(
                      child: Icon(
                        Icons.navigation,
                        color: Color(0xFF2F7FF0),
                        size: 40,
                        shadows: [
                          Shadow(color: Colors.black45, blurRadius: 6),
                        ],
                      ),
                    ),
                  ),
                // Celoplošný zelený banner s pokyny nahoře (styl Mapy.cz)
                if (_routeSteps.isNotEmpty)
                  Positioned(
                    top: 0,
                    left: 0,
                    right: 0,
                    child: _InstructionBanner(
                      distanceMeters: _liveDistanceToManeuver ??
                          ((_routeSteps[0]['distance'] as num?)
                                  ?.toDouble() ??
                              0),
                      step: _liveUpcomingStep ??
                          (_routeSteps.length >= 2
                              ? _routeSteps[1]
                              : _routeSteps[0]),
                    ),
                  ),
                // Kolečko s aktuální rychlostí (vlevo dole nad mapou)
                Positioned(
                  left: 14,
                  bottom: 14,
                  child: Container(
                    width: 58,
                    height: 58,
                    decoration: const BoxDecoration(
                      color: Colors.white,
                      shape: BoxShape.circle,
                      boxShadow: [
                        BoxShadow(color: Colors.black26, blurRadius: 6, offset: Offset(0, 2)),
                      ],
                    ),
                    alignment: Alignment.center,
                    child: Column(
                      mainAxisSize: MainAxisSize.min,
                      children: [
                        Text('${(_speedKmh ?? 0).round()}',
                            style: const TextStyle(
                                fontSize: 20, fontWeight: FontWeight.w800, height: 1.0)),
                        Text('km/h',
                            style: TextStyle(fontSize: 9, color: Colors.grey.shade600)),
                      ],
                    ),
                  ),
                ),
                Positioned(
                  right: 12,
                  bottom: 12,
                  child: FloatingActionButton(
                    heroTag: 'followBtn',
                    backgroundColor: _followMe ? Colors.orange : Colors.white,
                    onPressed: () {
                      setState(() => _followMe = true);
                      _animateCameraTo(
                          _myLocation, _heading != null ? -_heading! : 0);
                    },
                    child: Icon(Icons.my_location,
                        color: _followMe ? Colors.white : Colors.black87),
                  ),
                ),
              ],
            ),
          ),
          // Bílá spodní lišta ve stylu navigace (příjezd / min / km) + tlačítka
          Container(
            decoration: const BoxDecoration(
              color: Colors.white,
              boxShadow: [
                BoxShadow(color: Colors.black12, blurRadius: 10, offset: Offset(0, -2)),
              ],
            ),
            child: SafeArea(
              top: false,
              child: Column(
                children: [
                  const SizedBox(height: 8),
                  Container(
                    width: 40,
                    height: 4,
                    decoration: BoxDecoration(
                      color: Colors.grey.shade300,
                      borderRadius: BorderRadius.circular(2),
                    ),
                  ),
                  const SizedBox(height: 12),
                  if (_distanceKm != null && _durationMin != null)
                    Padding(
                      padding: const EdgeInsets.symmetric(horizontal: 24),
                      child: Row(
                        mainAxisAlignment: MainAxisAlignment.spaceBetween,
                        children: [
                          Column(
                            crossAxisAlignment: CrossAxisAlignment.start,
                            children: [
                              Text(_formatEta(_durationMin!),
                                  style: const TextStyle(
                                      fontSize: 24, fontWeight: FontWeight.w800)),
                              const Text('příjezd',
                                  style: TextStyle(color: Colors.grey, fontSize: 12)),
                            ],
                          ),
                          Column(
                            children: [
                              Text('$_durationMin',
                                  style: const TextStyle(
                                      fontSize: 22, fontWeight: FontWeight.w700)),
                              const Text('min',
                                  style: TextStyle(color: Colors.grey, fontSize: 12)),
                            ],
                          ),
                          Column(
                            children: [
                              Text(_distanceKm!.toStringAsFixed(1),
                                  style: const TextStyle(
                                      fontSize: 22, fontWeight: FontWeight.w700)),
                              const Text('km',
                                  style: TextStyle(color: Colors.grey, fontSize: 12)),
                            ],
                          ),
                        ],
                      ),
                    ),
                  const SizedBox(height: 14),
                  Padding(
                    padding: const EdgeInsets.fromLTRB(16, 0, 16, 12),
                    child: Row(
                      children: [
                        Expanded(
                          child: OutlinedButton.icon(
                            onPressed: _callCustomer,
                            icon: const Icon(Icons.call, color: Colors.green),
                            label: const Text('Zavolat'),
                          ),
                        ),
                        const SizedBox(width: 10),
                        Expanded(
                          child: FilledButton.icon(
                            onPressed: _markDone,
                            icon: const Icon(Icons.check),
                            label: const Text('Doručeno'),
                          ),
                        ),
                      ],
                    ),
                  ),
                ],
              ),
            ),
          ),
        ],
      ),
    );
  }

  String _formatEta(int minutesFromNow) {
    final eta = DateTime.now().add(Duration(minutes: minutesFromNow));
    return '${eta.hour.toString().padLeft(2, '0')}:${eta.minute.toString().padLeft(2, '0')}';
  }
}

// Celoplošný zelený banner s pokyny (ikona + velké číslo vzdálenosti + text),
// stylizovaný podle klasických navigačních appek (Mapy.cz apod.).
class _InstructionBanner extends StatelessWidget {
  final double distanceMeters;
  final Map<String, dynamic> step;
  const _InstructionBanner({required this.distanceMeters, required this.step});

  @override
  Widget build(BuildContext context) {
    return Container(
      width: double.infinity,
      padding: const EdgeInsets.fromLTRB(18, 14, 18, 16),
      decoration: BoxDecoration(
        color: Theme.of(context).colorScheme.primary,
        boxShadow: const [
          BoxShadow(color: Colors.black26, blurRadius: 8, offset: Offset(0, 3)),
        ],
      ),
      child: Row(
        crossAxisAlignment: CrossAxisAlignment.center,
        children: [
          Icon(_maneuverIcon(step), color: Colors.white, size: 46),
          const SizedBox(width: 16),
          Expanded(
            child: Column(
              crossAxisAlignment: CrossAxisAlignment.start,
              children: [
                Text(_formatDistance(distanceMeters),
                    style: const TextStyle(
                        color: Colors.white,
                        fontSize: 32,
                        fontWeight: FontWeight.w800,
                        height: 1.05)),
                const SizedBox(height: 2),
                Text(_maneuverText(step),
                    style: const TextStyle(
                        color: Colors.white,
                        fontSize: 15,
                        fontWeight: FontWeight.w500),
                    maxLines: 1,
                    overflow: TextOverflow.ellipsis),
              ],
            ),
          ),
        ],
      ),
    );
  }
}

// ===================== STATISTIKY =====================
class StatsScreen extends StatefulWidget {
  const StatsScreen({super.key});

  @override
  State<StatsScreen> createState() => _StatsScreenState();
}

class _StatsScreenState extends State<StatsScreen> {
  List<DeliveryOrder> _orders = [];
  bool _loading = true;
  bool _trackCashCardTips = false;
  bool _exportingPdf = false;

  @override
  void initState() {
    super.initState();
    _load();
  }

  Future<void> _load() async {
    final orders = await OrdersStore.load();
    final settings = await AppSettingsStore.load();
    setState(() {
      _orders = orders;
      _trackCashCardTips = settings['trackCashCardTips'] as bool? ?? false;
      _loading = false;
    });
  }

  bool _isToday(DateTime d) {
    final now = DateTime.now();
    return d.year == now.year && d.month == now.month && d.day == now.day;
  }

  String _fmtDay(DateTime d) => '${d.day}. ${d.month}. ${d.year}';

  // Sestaví PDF přesně ve stylu papírového rozpisu, co appka nahrazuje -
  // číslovaný seznam objednávek + vyhodnocení dne dole, stejný systém
  // sčítání/odečítání jako ve Vyúčtování směny.
  Future<void> _exportPdf() async {
    setState(() => _exportingPdf = true);
    try {
      final now = DateTime.now();
      final doneOrders =
          _orders.where((o) => o.done && o.completedAt != null).toList();
      final todayOrders = doneOrders
          .where((o) => _isToday(o.completedAt!))
          .toList()
        ..sort((a, b) => a.completedAt!.compareTo(b.completedAt!));

      final revenue = todayOrders.fold<double>(0, (s, o) => s + o.amount);
      final online = todayOrders
          .where((o) => o.prePaid)
          .fold<double>(0, (s, o) => s + o.amount);
      final onlineTips = todayOrders
          .where((o) => o.prePaid)
          .fold<double>(0, (s, o) => s + o.tip);
      final delivery = todayOrders
          .where((o) => !o.prePaid && !o.bossDelivered)
          .fold<double>(0, (s, o) => s + o.deliveryFee);
      final bossAmount = todayOrders
          .where((o) => o.bossDelivered)
          .fold<double>(0, (s, o) => s + o.amount);
      final cardAmount = todayOrders
          .where((o) => !o.prePaid && o.paidByCard)
          .fold<double>(
              0, (s, o) => s + o.amount + o.deliveryFee + o.cashCardTip);

      final saved = await ShiftSettlementStore.load();
      final stravenky = double.tryParse(
              ((saved?['stravenky'] ?? '') as String).replaceAll(',', '.')) ??
          0;
      final platby = double.tryParse(
              ((saved?['platby'] ?? '') as String).replaceAll(',', '.')) ??
          0;

      final result = revenue -
          cardAmount -
          online -
          onlineTips -
          stravenky -
          platby -
          bossAmount +
          delivery;

      final regularFont = await PdfGoogleFonts.notoSansRegular();
      final boldFont = await PdfGoogleFonts.notoSansBold();
      final doc = pw.Document(
        theme: pw.ThemeData.withFont(
          base: regularFont,
          bold: boldFont,
        ),
      );
      doc.addPage(
        pw.MultiPage(
          build: (context) => [
            pw.Text('Vyúčtování směny',
                style:
                    pw.TextStyle(fontSize: 20, fontWeight: pw.FontWeight.bold)),
            pw.Text(_fmtDay(now),
                style: const pw.TextStyle(fontSize: 12, color: PdfColors.grey700)),
            pw.SizedBox(height: 14),
            pw.Table(
              border: pw.TableBorder.all(color: PdfColors.grey400, width: 0.5),
              columnWidths: const {
                0: pw.FlexColumnWidth(0.6),
                1: pw.FlexColumnWidth(2.6),
                2: pw.FlexColumnWidth(1.2),
                3: pw.FlexColumnWidth(1.2),
                4: pw.FlexColumnWidth(1.4),
              },
              children: [
                pw.TableRow(
                  decoration: const pw.BoxDecoration(color: PdfColors.grey300),
                  children: [
                    _pdfCell('Č.', bold: true),
                    _pdfCell('Adresa', bold: true),
                    _pdfCell('Částka (Kč)', bold: true),
                    _pdfCell('Doprava (Kč)', bold: true),
                    _pdfCell('Dýško online (Kč)', bold: true),
                  ],
                ),
                for (int i = 0; i < todayOrders.length; i++)
                  _pdfOrderRow(i + 1, todayOrders[i]),
              ],
            ),
            pw.SizedBox(height: 8),
            pw.Row(children: [
              _pdfLegendDot(PdfColor.fromInt(0xFFC8F7C5)),
              pw.SizedBox(width: 4),
              pw.Text('zaplaceno online', style: const pw.TextStyle(fontSize: 9)),
              pw.SizedBox(width: 14),
              _pdfLegendDot(PdfColor.fromInt(0xFF64B5F6)),
              pw.SizedBox(width: 4),
              pw.Text('jel šéf', style: const pw.TextStyle(fontSize: 9)),
            ]),
            pw.SizedBox(height: 20),
            pw.Divider(),
            pw.SizedBox(height: 8),
            pw.Text('Vyhodnocení dne',
                style:
                    pw.TextStyle(fontSize: 14, fontWeight: pw.FontWeight.bold)),
            pw.SizedBox(height: 8),
            _pdfSummaryRow('Tržba', revenue),
            _pdfSummaryRow('Karty', cardAmount),
            _pdfSummaryRow('Online platby', online),
            _pdfSummaryRow('Dýška z online', onlineTips),
            _pdfSummaryRow('Stravenky', stravenky),
            _pdfSummaryRow('Platby/výdaje', platby),
            _pdfSummaryRow('Jel šéf (bez dopravy)', bossAmount),
            _pdfSummaryRow('Doprava', delivery),
            pw.SizedBox(height: 6),
            pw.Divider(),
            pw.SizedBox(height: 4),
            pw.Row(
              mainAxisAlignment: pw.MainAxisAlignment.spaceBetween,
              children: [
                pw.Text('Dát šéfovi',
                    style: pw.TextStyle(
                        fontSize: 14, fontWeight: pw.FontWeight.bold)),
                pw.Text('${result.toStringAsFixed(0)} Kč',
                    style: pw.TextStyle(
                        fontSize: 16, fontWeight: pw.FontWeight.bold)),
              ],
            ),
          ],
        ),
      );

      final filename =
          'smena_${now.year}-${now.month.toString().padLeft(2, '0')}-${now.day.toString().padLeft(2, '0')}.pdf';
      await Printing.layoutPdf(
        name: filename,
        onLayout: (PdfPageFormat format) async => doc.save(),
      );
    } catch (e) {
      if (mounted) {
        ScaffoldMessenger.of(context).showSnackBar(
          SnackBar(content: Text('Export PDF selhal: $e')),
        );
      }
    } finally {
      if (mounted) setState(() => _exportingPdf = false);
    }
  }

  pw.TableRow _pdfOrderRow(int index, DeliveryOrder o) {
    PdfColor? bg;
    if (o.bossDelivered) {
      bg = PdfColor.fromInt(0xFF64B5F6); // tmavší modrá, ale černý text čitelný
    } else if (o.prePaid) {
      bg = PdfColor.fromInt(0xFFC8F7C5); // světle zelená
    }
    return pw.TableRow(
      decoration: bg != null ? pw.BoxDecoration(color: bg) : null,
      children: [
        _pdfCell('$index'),
        _pdfCell(o.address),
        _pdfCell(o.amount.toStringAsFixed(0)),
        _pdfCell(!o.bossDelivered && o.deliveryFee > 0
            ? o.deliveryFee.toStringAsFixed(0)
            : ''),
        _pdfCell(
            o.prePaid && o.tip > 0 ? o.tip.toStringAsFixed(0) : ''),
      ],
    );
  }

  pw.Widget _pdfCell(String text, {bool bold = false}) {
    return pw.Padding(
      padding: const pw.EdgeInsets.all(4),
      child: pw.Text(
        text,
        style: pw.TextStyle(
          fontSize: 9,
          fontWeight: bold ? pw.FontWeight.bold : pw.FontWeight.normal,
          color: PdfColors.black,
        ),
      ),
    );
  }

  pw.Widget _pdfSummaryRow(String label, double value) {
    return pw.Padding(
      padding: const pw.EdgeInsets.symmetric(vertical: 2),
      child: pw.Row(
        mainAxisAlignment: pw.MainAxisAlignment.spaceBetween,
        children: [
          pw.Text(label, style: const pw.TextStyle(fontSize: 11)),
          pw.Text('${value.toStringAsFixed(0)} Kč',
              style: pw.TextStyle(fontSize: 11, fontWeight: pw.FontWeight.bold)),
        ],
      ),
    );
  }

  pw.Widget _pdfLegendDot(PdfColor color) {
    return pw.Container(
      width: 10,
      height: 10,
      decoration:
          pw.BoxDecoration(color: color, borderRadius: pw.BorderRadius.circular(2)),
    );
  }

  @override
  Widget build(BuildContext context) {
    final doneOrders =
        _orders.where((o) => o.done && o.completedAt != null).toList();
    final todayOrders =
        doneOrders.where((o) => _isToday(o.completedAt!)).toList();
    final todayPending = _orders
        .where((o) => !o.done && _isToday(o.createdAt))
        .toList();

    final todayCount = todayOrders.length;
    final todayRevenue =
        todayOrders.fold<double>(0, (sum, o) => sum + o.amount);
    final todayOnline = todayOrders
        .where((o) => o.prePaid)
        .fold<double>(0, (sum, o) => sum + o.amount);
    final todayOnlineCount = todayOrders.where((o) => o.prePaid).length;
    final todayTips = todayOrders
        .where((o) => o.prePaid)
        .fold<double>(0, (sum, o) => sum + o.tip);
    // doprava z objednávek, které vezl šéf, se do "mojí" dopravy nepočítá
    final todayDelivery = todayOrders
        .where((o) => !o.prePaid && !o.bossDelivered)
        .fold<double>(0, (sum, o) => sum + o.deliveryFee);
    final todayCashCardTips = todayOrders
        .where((o) => !o.prePaid)
        .fold<double>(0, (sum, o) => sum + o.cashCardTip);

    final todayPendingCount = todayPending.length;
    final todayPendingRevenue =
        todayPending.fold<double>(0, (sum, o) => sum + o.amount);
    final todayAllCount = todayCount + todayPendingCount;
    final todayAllRevenue = todayRevenue + todayPendingRevenue;

    final totalCount = doneOrders.length;
    final totalRevenue =
        doneOrders.fold<double>(0, (sum, o) => sum + o.amount);
    final totalOnline = doneOrders
        .where((o) => o.prePaid)
        .fold<double>(0, (sum, o) => sum + o.amount);
    final totalOnlineCount = doneOrders.where((o) => o.prePaid).length;
    final totalTips = doneOrders
        .where((o) => o.prePaid)
        .fold<double>(0, (sum, o) => sum + o.tip);
    final totalDelivery = doneOrders
        .where((o) => !o.prePaid && !o.bossDelivered)
        .fold<double>(0, (sum, o) => sum + o.deliveryFee);
    final totalCashCardTips = doneOrders
        .where((o) => !o.prePaid)
        .fold<double>(0, (sum, o) => sum + o.cashCardTip);

    // --- Osobní rekordy: nejlepší den podle tržby a podle počtu objednávek ---
    final byDay = <DateTime, List<DeliveryOrder>>{};
    for (final o in doneOrders) {
      final d = o.completedAt!;
      final key = DateTime(d.year, d.month, d.day);
      byDay.putIfAbsent(key, () => []).add(o);
    }
    DateTime? bestRevenueDay;
    double bestRevenueAmount = 0;
    DateTime? bestCountDay;
    int bestCountAmount = 0;
    DateTime? bestDayTipsDay;
    double bestDayTipsAmount = 0;
    DateTime? bestDayDeliveryDay;
    double bestDayDeliveryAmount = 0;
    byDay.forEach((day, dayOrders) {
      final revenue = dayOrders.fold<double>(0, (s, o) => s + o.amount);
      final count = dayOrders.length;
      final dayTips = dayOrders.fold<double>(
          0, (s, o) => s + (o.prePaid ? o.tip : o.cashCardTip));
      final dayDelivery = dayOrders
          .where((o) => !o.prePaid && !o.bossDelivered)
          .fold<double>(0, (s, o) => s + o.deliveryFee);
      if (revenue > bestRevenueAmount) {
        bestRevenueAmount = revenue;
        bestRevenueDay = day;
      }
      if (count > bestCountAmount) {
        bestCountAmount = count;
        bestCountDay = day;
      }
      if (dayTips > bestDayTipsAmount) {
        bestDayTipsAmount = dayTips;
        bestDayTipsDay = day;
      }
      if (dayDelivery > bestDayDeliveryAmount) {
        bestDayDeliveryAmount = dayDelivery;
        bestDayDeliveryDay = day;
      }
    });

    // nejlepší dýško z jedné konkrétní objednávky (ne za celý den)
    DateTime? bestSingleTipDay;
    double bestSingleTipAmount = 0;
    for (final o in doneOrders) {
      final orderTip = o.prePaid ? o.tip : o.cashCardTip;
      if (orderTip > bestSingleTipAmount) {
        bestSingleTipAmount = orderTip;
        final d = o.completedAt!;
        bestSingleTipDay = DateTime(d.year, d.month, d.day);
      }
    }

    final isTodayBestRevenue =
        bestRevenueDay != null && _isToday(bestRevenueDay!);
    final isTodayBestCount = bestCountDay != null && _isToday(bestCountDay!);
    final isTodayBestSingleTip =
        bestSingleTipDay != null && _isToday(bestSingleTipDay!);
    final isTodayBestDayTips =
        bestDayTipsDay != null && _isToday(bestDayTipsDay!);
    final isTodayBestDayDelivery =
        bestDayDeliveryDay != null && _isToday(bestDayDeliveryDay!);

    return Scaffold(
      appBar: AppBar(
        title: const Text('Statistiky'),
        actions: [
          IconButton(
            icon: _exportingPdf
                ? const SizedBox(
                    width: 20,
                    height: 20,
                    child: CircularProgressIndicator(strokeWidth: 2),
                  )
                : const Icon(Icons.picture_as_pdf_outlined),
            tooltip: 'Export do PDF',
            onPressed: _exportingPdf ? null : _exportPdf,
          ),
        ],
      ),
      body: _loading
          ? const Center(child: CircularProgressIndicator())
          : ListView(
              padding: const EdgeInsets.all(16),
              children: [
                const Text('Dnes',
                    style:
                        TextStyle(fontWeight: FontWeight.bold, fontSize: 18)),
                const SizedBox(height: 8),
                _statCard('Doručené objednávky', '$todayCount'),
                _statCard('Celková tržba', '${todayRevenue.toStringAsFixed(0)} Kč'),
                _statCard('Online platby', '${todayOnline.toStringAsFixed(0)} Kč'),
                _statCard('Dýšky z online plateb',
                    '${todayTips.toStringAsFixed(0)} Kč'),
                _statCard('Doprava', '${todayDelivery.toStringAsFixed(0)} Kč'),
                _statCard('Počet online objednávek', '$todayOnlineCount'),
                if (_trackCashCardTips)
                  _statCard('Dýška z hotovosti/karet',
                      '${todayCashCardTips.toStringAsFixed(0)} Kč'),
                _statCard('Celkem dnes (s nevyřízenými)',
                    '$todayAllCount obj. · ${todayAllRevenue.toStringAsFixed(0)} Kč'),
                const SizedBox(height: 20),
                Card(
                  color: Colors.amber.shade50,
                  child: Padding(
                    padding: const EdgeInsets.all(14),
                    child: Column(
                      crossAxisAlignment: CrossAxisAlignment.start,
                      children: [
                        Row(
                          children: const [
                            Text('🏆', style: TextStyle(fontSize: 20)),
                            SizedBox(width: 8),
                            Text('Osobní rekordy',
                                style: TextStyle(
                                    fontWeight: FontWeight.bold, fontSize: 16)),
                          ],
                        ),
                        const SizedBox(height: 10),
                        if (bestRevenueDay == null)
                          const Text(
                            'Zatím žádný záznam - doruč první objednávku!',
                            style: TextStyle(color: Colors.grey),
                          )
                        else ...[
                          _recordRow(
                            'Nejlepší den (tržba)',
                            '${_fmtDay(bestRevenueDay!)} · '
                                '${bestRevenueAmount.toStringAsFixed(0)} Kč',
                            isNew: isTodayBestRevenue,
                          ),
                          const SizedBox(height: 8),
                          _recordRow(
                            'Nejvíc objednávek za den',
                            '${_fmtDay(bestCountDay!)} · $bestCountAmount objednávek',
                            isNew: isTodayBestCount,
                          ),
                          if (bestSingleTipDay != null) ...[
                            const SizedBox(height: 8),
                            _recordRow(
                              'Největší dýško z jednoho rozvozu',
                              '${_fmtDay(bestSingleTipDay!)} · '
                                  '${bestSingleTipAmount.toStringAsFixed(0)} Kč',
                              isNew: isTodayBestSingleTip,
                            ),
                          ],
                          if (bestDayTipsDay != null) ...[
                            const SizedBox(height: 8),
                            _recordRow(
                              'Největší dýško za den',
                              '${_fmtDay(bestDayTipsDay!)} · '
                                  '${bestDayTipsAmount.toStringAsFixed(0)} Kč',
                              isNew: isTodayBestDayTips,
                            ),
                          ],
                          if (bestDayDeliveryDay != null) ...[
                            const SizedBox(height: 8),
                            _recordRow(
                              'Největší doprava za den',
                              '${_fmtDay(bestDayDeliveryDay!)} · '
                                  '${bestDayDeliveryAmount.toStringAsFixed(0)} Kč',
                              isNew: isTodayBestDayDelivery,
                            ),
                          ],
                        ],
                      ],
                    ),
                  ),
                ),
                const SizedBox(height: 20),
                Card(
                  clipBehavior: Clip.antiAlias,
                  child: ExpansionTile(
                    leading: const Icon(Icons.calendar_month_outlined),
                    title: const Text('Od začátku',
                        style: TextStyle(fontWeight: FontWeight.bold)),
                    children: [
                      Padding(
                        padding: const EdgeInsets.fromLTRB(12, 0, 12, 12),
                        child: Column(
                          children: [
                            _statCard('Doručené objednávky', '$totalCount'),
                            _statCard('Celková tržba',
                                '${totalRevenue.toStringAsFixed(0)} Kč'),
                            _statCard('Online platby',
                                '${totalOnline.toStringAsFixed(0)} Kč'),
                            _statCard('Dýšky z online plateb',
                                '${totalTips.toStringAsFixed(0)} Kč'),
                            _statCard('Doprava',
                                '${totalDelivery.toStringAsFixed(0)} Kč'),
                            _statCard(
                                'Počet online objednávek', '$totalOnlineCount'),
                            if (_trackCashCardTips)
                              _statCard('Dýška z hotovosti/karet',
                                  '${totalCashCardTips.toStringAsFixed(0)} Kč'),
                          ],
                        ),
                      ),
                    ],
                  ),
                ),
              ],
            ),
    );
  }

  Widget _statCard(String label, String value) {
    return Card(
      child: ListTile(
        title: Text(label),
        trailing: Text(value,
            style: const TextStyle(fontWeight: FontWeight.bold, fontSize: 18)),
      ),
    );
  }

  Widget _recordRow(String label, String value, {bool isNew = false}) {
    return Row(
      mainAxisAlignment: MainAxisAlignment.spaceBetween,
      children: [
        Expanded(
          child: Text(label, style: const TextStyle(fontSize: 13)),
        ),
        Row(
          mainAxisSize: MainAxisSize.min,
          children: [
            if (isNew)
              const Padding(
                padding: EdgeInsets.only(right: 6),
                child: Text('🎉', style: TextStyle(fontSize: 14)),
              ),
            Text(value,
                style: const TextStyle(fontWeight: FontWeight.bold, fontSize: 13)),
          ],
        ),
      ],
    );
  }
}

// ===================== NASTAVENÍ =====================
class SettingsScreen extends StatefulWidget {
  final bool trackCashCardTips;
  const SettingsScreen({super.key, required this.trackCashCardTips});

  @override
  State<SettingsScreen> createState() => _SettingsScreenState();
}

class _SettingsScreenState extends State<SettingsScreen> {
  late bool _trackCashCardTips;

  @override
  void initState() {
    super.initState();
    _trackCashCardTips = widget.trackCashCardTips;
  }

  Future<void> _save(bool value) async {
    setState(() => _trackCashCardTips = value);
    final settings = await AppSettingsStore.load();
    settings['trackCashCardTips'] = value;
    await AppSettingsStore.save(settings);
  }

  @override
  Widget build(BuildContext context) {
    return Scaffold(
      appBar: AppBar(
        title: const Text('Nastavení'),
        leading: IconButton(
          icon: const Icon(Icons.arrow_back),
          onPressed: () => Navigator.pop(context, true),
        ),
      ),
      body: ListView(
        padding: const EdgeInsets.all(16),
        children: [
          SwitchListTile(
            title: const Text('Počítat dýška i z hotovosti/karty'),
            subtitle: const Text(
                'Appka se při dokončení objednávky s platbou na místě '
                'zeptá, kolik jste reálně vybral/a. Rozdíl oproti ceně '
                'objednávky se počítá jako dýško ve statistikách.'),
            value: _trackCashCardTips,
            onChanged: _save,
          ),
          const _BackupSection(),
        ],
      ),
    );
  }
}

// ===================== ZÁLOHA DAT (export / import) =====================
// Záloha bere všechny klíče rozvozka_* z paměti prohlížeče, takže do ní
// automaticky spadnou i budoucí data.

class RozvozkaBackup {
  static const _prefix = 'rozvozka_';
  static const _format = 'rozvozka-backup';
  static const _ordersKey = 'rozvozka_orders_v1';

  /// Všechna data appky z paměti prohlížeče: klíč -> uložený text.
  static Future<Map<String, String>> collect() async {
    final prefs = await SharedPreferences.getInstance();
    final data = <String, String>{};
    for (final k in prefs.getKeys()) {
      if (!k.startsWith(_prefix)) continue;
      final v = prefs.get(k);
      if (v is String) data[k] = v;
    }
    return data;
  }

  static String encode(Map<String, String> data) {
    return json.encode({
      'format': _format,
      'version': 1,
      'exportedAt': DateTime.now().toIso8601String(),
      'data': data,
    });
  }

  /// Přečte text zálohy. Vrátí null, když to není záloha Rozvozky.
  static Map<String, String>? parse(String text) {
    try {
      final m = json.decode(text);
      if (m is! Map || m['format'] != _format) return null;
      final d = m['data'];
      if (d is! Map) return null;
      final out = <String, String>{};
      d.forEach((k, v) {
        if (k is String && k.startsWith(_prefix) && v is String) out[k] = v;
      });
      return out.isEmpty ? null : out;
    } catch (_) {
      return null;
    }
  }

  static int countOrders(Map<String, String> data) {
    try {
      final raw = data[_ordersKey];
      if (raw == null || raw.isEmpty) return 0;
      return (json.decode(raw) as List).length;
    } catch (_) {
      return 0;
    }
  }

  /// Zapíše data ze zálohy do paměti prohlížeče (přepíše stejné klíče).
  static Future<void> restore(Map<String, String> data) async {
    final prefs = await SharedPreferences.getInstance();
    for (final e in data.entries) {
      await prefs.setString(e.key, e.value);
    }
  }

  /// Stáhne text jako soubor.
  static void downloadText(String filename, String text) {
    final blob = web.Blob(
      [text.toJS].toJS,
      web.BlobPropertyBag(type: 'application/json'),
    );
    final url = web.URL.createObjectURL(blob);
    final a = web.document.createElement('a') as web.HTMLAnchorElement;
    a.href = url;
    a.download = filename;
    web.document.body!.appendChild(a);
    a.click();
    a.remove();
    Timer(const Duration(seconds: 10), () => web.URL.revokeObjectURL(url));
  }

  /// Otevře výběr souboru a vrátí jeho text. Když uživatel výběr zruší,
  /// future se nedokončí (nic se neděje, jen se nic nenačte).
  static Future<String?> pickTextFile() {
    final completer = Completer<String?>();
    final input = web.document.createElement('input') as web.HTMLInputElement;
    input.type = 'file';
    input.accept = '.json,application/json';
    input.onchange = ((web.Event _) {
      final file = input.files?.item(0);
      if (file == null) {
        completer.complete(null);
        return;
      }
      file.text().toDart.then((t) {
        if (!completer.isCompleted) completer.complete(t.toDart);
      }).catchError((_) {
        if (!completer.isCompleted) completer.complete(null);
      });
    }).toJS;
    input.click();
    return completer.future;
  }
}

class _BackupSection extends StatefulWidget {
  const _BackupSection();

  @override
  State<_BackupSection> createState() => _BackupSectionState();
}

class _BackupSectionState extends State<_BackupSection> {
  String? _msg;

  String _two(int n) => n.toString().padLeft(2, '0');

  Future<void> _export() async {
    final data = await RozvozkaBackup.collect();
    final d = DateTime.now();
    final name =
        'rozvozka-zaloha-${d.year}-${_two(d.month)}-${_two(d.day)}.json';
    RozvozkaBackup.downloadText(name, RozvozkaBackup.encode(data));
    if (!mounted) return;
    setState(() => _msg =
        'Záloha se stáhla jako $name (${RozvozkaBackup.countOrders(data)} objednávek). '
        'Na iPhonu se otevře náhled - dej Sdílet a Uložit do Souborů.');
  }

  Future<void> _import() async {
    final text = await RozvozkaBackup.pickTextFile();
    if (text == null || !mounted) return;
    final backup = RozvozkaBackup.parse(text);
    if (backup == null) {
      setState(() => _msg =
          'Tenhle soubor není záloha Rozvozky, nic se nezměnilo.');
      return;
    }
    final current = await RozvozkaBackup.collect();
    final inBackup = RozvozkaBackup.countOrders(backup);
    final inApp = RozvozkaBackup.countOrders(current);
    if (!mounted) return;
    final ok = await showDialog<bool>(
      context: context,
      builder: (ctx) => AlertDialog(
        title: const Text('Obnovit data ze zálohy?'),
        content: Text(
          'Záloha obsahuje $inBackup objednávek.\n'
          'V appce je teď $inApp objednávek.\n\n'
          'Import přepíše současná data daty ze zálohy.'
          '${inApp > inBackup ? '\n\nPozor: v appce je teď víc dat než v záloze, o rozdíl přijdeš. Radši si nejdřív udělej export.' : ''}',
        ),
        actions: [
          TextButton(
            onPressed: () => Navigator.pop(ctx, false),
            child: const Text('Zrušit'),
          ),
          ElevatedButton(
            onPressed: () => Navigator.pop(ctx, true),
            child: const Text('Obnovit'),
          ),
        ],
      ),
    );
    if (ok != true) return;
    await RozvozkaBackup.restore(backup);
    // Znovu načíst appku, ať všechny obrazovky načtou čerstvá data.
    web.window.location.reload();
  }

  @override
  Widget build(BuildContext context) {
    return Column(
      crossAxisAlignment: CrossAxisAlignment.start,
      children: [
        const SizedBox(height: 8),
        const Divider(),
        const Padding(
          padding: EdgeInsets.symmetric(vertical: 8),
          child: Text(
            'Záloha dat',
            style: TextStyle(fontWeight: FontWeight.bold, fontSize: 16),
          ),
        ),
        const Text(
          'Všechna data appky (objednávky, uložená místa, nastavení) jsou jen '
          'v paměti prohlížeče na tomhle zařízení. Exportuj si je jako zálohu, '
          'nebo je odsud naimportuj do nové adresy appky či nového telefonu.',
          style: TextStyle(color: Colors.grey),
        ),
        const SizedBox(height: 12),
        Wrap(
          spacing: 12,
          runSpacing: 8,
          children: [
            ElevatedButton.icon(
              onPressed: _export,
              icon: const Icon(Icons.download),
              label: const Text('Exportovat data'),
            ),
            OutlinedButton.icon(
              onPressed: _import,
              icon: const Icon(Icons.upload),
              label: const Text('Importovat data'),
            ),
          ],
        ),
        if (_msg != null)
          Padding(
            padding: const EdgeInsets.only(top: 12),
            child: Text(_msg!),
          ),
      ],
    );
  }
}

// ===================== VYÚČTOVÁNÍ SMĚNY =====================
// Automaticky doplní, co appka ví (tržba, online platby, dýška, doprava),
// zbytek (karty, stravenky, výdaje, šéfovy jízdy) doplní řidič ručně a appka
// rovnou spočítá, kolik peněz odevzdat.
class ShiftSettlementScreen extends StatefulWidget {
  const ShiftSettlementScreen({super.key});

  @override
  State<ShiftSettlementScreen> createState() => _ShiftSettlementScreenState();
}

class _ShiftSettlementScreenState extends State<ShiftSettlementScreen> {
  bool _loading = true;
  bool _trackCashCardTips = false;
  double _todayRevenue = 0;
  double _todayOnline = 0;
  double _todayTips = 0;
  double _todayDelivery = 0;
  double _todayCashCardTips = 0;
  double _todayBossAmount = 0;
  double _todayCardAmount = 0;

  final _stravenkyController = TextEditingController();
  final _platbyController = TextEditingController();
  final _hodinyController = TextEditingController();
  final _sazbaController = TextEditingController(text: '140');

  @override
  void initState() {
    super.initState();
    _load();
    for (final c in [
      _stravenkyController,
      _platbyController,
      _hodinyController,
      _sazbaController,
    ]) {
      c.addListener(() => setState(() {}));
    }
  }

  @override
  void dispose() {
    _stravenkyController.dispose();
    _platbyController.dispose();
    _hodinyController.dispose();
    _sazbaController.dispose();
    super.dispose();
  }

  bool _isToday(DateTime d) {
    final now = DateTime.now();
    return d.year == now.year && d.month == now.month && d.day == now.day;
  }

  Future<void> _load() async {
    final orders = await OrdersStore.load();
    final settings = await AppSettingsStore.load();
    final todayOrders = orders
        .where((o) => o.done && o.completedAt != null && _isToday(o.completedAt!))
        .toList();

    final revenue = todayOrders.fold<double>(0, (s, o) => s + o.amount);
    final online =
        todayOrders.where((o) => o.prePaid).fold<double>(0, (s, o) => s + o.amount);
    final tips =
        todayOrders.where((o) => o.prePaid).fold<double>(0, (s, o) => s + o.tip);
    // doprava z objednávek, které vezl šéf, se do mojí dopravy nepočítá
    final delivery = todayOrders
        .where((o) => !o.prePaid && !o.bossDelivered)
        .fold<double>(0, (s, o) => s + o.deliveryFee);
    final cashCardTips = todayOrders
        .where((o) => !o.prePaid)
        .fold<double>(0, (s, o) => s + o.cashCardTip);
    // co vezl šéf - jen cena objednávky, bez dopravy (tu si nechává on na benzín)
    final bossAmount = todayOrders
        .where((o) => o.bossDelivered)
        .fold<double>(0, (s, o) => s + o.amount);
    // kolik se dnes reálně vybralo kartou (skutečně vybraná částka, ne jen
    // cena objednávky) - appka to teď ví sama z volby při "Doručeno"
    final cardAmount = todayOrders
        .where((o) => !o.prePaid && o.paidByCard)
        .fold<double>(
            0, (s, o) => s + o.amount + o.deliveryFee + o.cashCardTip);

    final saved = await ShiftSettlementStore.load();

    setState(() {
      _trackCashCardTips = settings['trackCashCardTips'] as bool? ?? false;
      _todayRevenue = revenue;
      _todayOnline = online;
      _todayTips = tips;
      _todayDelivery = delivery;
      _todayCashCardTips = cashCardTips;
      _todayBossAmount = bossAmount;
      _todayCardAmount = cardAmount;
      if (saved != null) {
        _stravenkyController.text = (saved['stravenky'] ?? '') as String;
        _platbyController.text = (saved['platby'] ?? '') as String;
        _hodinyController.text = (saved['hodiny'] ?? '') as String;
        _sazbaController.text =
            (saved['sazba'] as String?)?.isNotEmpty == true
                ? saved['sazba'] as String
                : '140';
      }
      _loading = false;
    });
  }

  double _num(TextEditingController c) =>
      double.tryParse(c.text.trim().replaceAll(',', '.')) ?? 0;

  Future<void> _persist() async {
    await ShiftSettlementStore.save({
      'stravenky': _stravenkyController.text.trim(),
      'platby': _platbyController.text.trim(),
      'hodiny': _hodinyController.text.trim(),
      'sazba': _sazbaController.text.trim(),
    });
  }

  @override
  Widget build(BuildContext context) {
    final stravenky = _num(_stravenkyController);
    final platby = _num(_platbyController);

    final result = _todayRevenue -
        _todayCardAmount -
        _todayOnline -
        _todayTips -
        stravenky -
        platby -
        _todayBossAmount +
        _todayDelivery;

    final hodiny = _num(_hodinyController);
    final sazba = _num(_sazbaController);
    final mzda = hodiny * sazba;
    final dyskaCelkem = _todayTips + _todayCashCardTips;
    final vyplataCelkem = mzda + dyskaCelkem;
    final hodinovkaSDyskama = hodiny > 0 ? vyplataCelkem / hodiny : 0.0;

    return Scaffold(
      appBar: AppBar(title: const Text('Vyúčtování směny')),
      body: _loading
          ? const Center(child: CircularProgressIndicator())
          : ListView(
              padding: const EdgeInsets.all(16),
              children: [
                const Text('Z appky (automaticky, dnešní směna)',
                    style: TextStyle(fontWeight: FontWeight.bold, fontSize: 15)),
                const SizedBox(height: 8),
                Card(
                  child: Padding(
                    padding: const EdgeInsets.symmetric(
                        horizontal: 16, vertical: 8),
                    child: Column(
                      children: [
                        _readOnlyRow('Tržba', _todayRevenue),
                        _readOnlyRow('Online objednávky', _todayOnline),
                        _readOnlyRow('Dýška z online objednávek', _todayTips),
                        _readOnlyRow('Doprava', _todayDelivery),
                        _readOnlyRow(
                            'Jel šéf (bez dopravy)', _todayBossAmount),
                        if (_trackCashCardTips)
                          _readOnlyRow('Karty', _todayCardAmount),
                      ],
                    ),
                  ),
                ),
                const SizedBox(height: 20),
                const Text('Doplň ručně',
                    style: TextStyle(fontWeight: FontWeight.bold, fontSize: 15)),
                const SizedBox(height: 8),
                _inputField('Stravenky (Kč)', _stravenkyController),
                const SizedBox(height: 10),
                _inputField('Platby / výdaje (Kč)', _platbyController),
                const SizedBox(height: 24),
                Container(
                  width: double.infinity,
                  padding: const EdgeInsets.all(18),
                  decoration: BoxDecoration(
                    color: Theme.of(context).colorScheme.primaryContainer,
                    borderRadius: BorderRadius.circular(14),
                  ),
                  child: Column(
                    children: [
                      const Text('Dát šéfovi', style: TextStyle(fontSize: 14)),
                      const SizedBox(height: 4),
                      Text('${result.toStringAsFixed(0)} Kč',
                          style: const TextStyle(
                              fontSize: 34, fontWeight: FontWeight.w800)),
                    ],
                  ),
                ),
                const SizedBox(height: 8),
                const Text(
                  'Vzorec: tržba − karty − online − dýška z online − stravenky '
                  '− platby − co jel šéf + doprava',
                  style: TextStyle(fontSize: 11, color: Colors.grey),
                  textAlign: TextAlign.center,
                ),
                if (_trackCashCardTips) ...[
                  const SizedBox(height: 28),
                  const Divider(),
                  const SizedBox(height: 8),
                  const Text('Výplata',
                      style:
                          TextStyle(fontWeight: FontWeight.bold, fontSize: 15)),
                  const SizedBox(height: 8),
                  Row(
                    children: [
                      Expanded(
                        child:
                            _inputField('Odpracované hodiny', _hodinyController),
                      ),
                      const SizedBox(width: 10),
                      Expanded(
                        child: _inputField('Kč / hodina', _sazbaController),
                      ),
                    ],
                  ),
                  const SizedBox(height: 16),
                  Card(
                    child: Padding(
                      padding: const EdgeInsets.symmetric(
                          horizontal: 16, vertical: 8),
                      child: Column(
                        children: [
                          _readOnlyRow('Mzda (hodiny × sazba)', mzda),
                          _readOnlyRow(
                              'Dýška (online + hotovost/karta)', dyskaCelkem),
                          const Divider(),
                          _readOnlyRow('Celkem k výplatě', vyplataCelkem,
                              bold: true),
                          if (hodiny > 0)
                            Padding(
                              padding: const EdgeInsets.only(top: 6),
                              child: Row(
                                mainAxisAlignment:
                                    MainAxisAlignment.spaceBetween,
                                children: [
                                  const Text('Efektivní hodinovka (s dýšky)'),
                                  Text(
                                      '${hodinovkaSDyskama.toStringAsFixed(0)} Kč/h',
                                      style: const TextStyle(
                                          fontWeight: FontWeight.w700)),
                                ],
                              ),
                            ),
                        ],
                      ),
                    ),
                  ),
                ],
              ],
            ),
    );
  }

  Widget _readOnlyRow(String label, double value, {bool bold = false}) {
    return Padding(
      padding: const EdgeInsets.symmetric(vertical: 6),
      child: Row(
        mainAxisAlignment: MainAxisAlignment.spaceBetween,
        children: [
          Text(label,
              style: TextStyle(
                  fontWeight: bold ? FontWeight.bold : FontWeight.normal)),
          Text('${value.toStringAsFixed(0)} Kč',
              style: TextStyle(
                  fontWeight: FontWeight.w700,
                  fontSize: bold ? 17 : 14)),
        ],
      ),
    );
  }

  Widget _inputField(String label, TextEditingController controller,
      {String? helper}) {
    return TextField(
      controller: controller,
      keyboardType: const TextInputType.numberWithOptions(decimal: true),
      decoration: InputDecoration(
        labelText: label,
        helperText: helper,
        border: const OutlineInputBorder(),
      ),
      onChanged: (_) => _persist(),
    );
  }
}
