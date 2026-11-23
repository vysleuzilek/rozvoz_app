import 'package:flutter/material.dart';
import 'package:flutter/services.dart';
import 'package:flutter_localizations/flutter_localizations.dart';
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
  final String label; // jak to pojmenovala mapa (pro kontrolu, kam appka vede)
  GeocodeResult(this.lat, this.lon, this.distanceKm,
      {this.isPrecise = true, this.label = ''});
}

Future<List> _nominatimSearch(String query) async {
  final box = _boundingBoxKm(_chlumecCenter, 25);
  final geoUrl = Uri.parse(
      'https://nominatim.openstreetmap.org/search'
      '?format=json&limit=10&countrycodes=cz&addressdetails=1'
      '&viewbox=${box.lonMin},${box.latMax},${box.lonMax},${box.latMin}'
      '&bounded=1'
      '&q=${Uri.encodeComponent(query)}');
  final res = await http
      .get(geoUrl, headers: {'Accept-Language': 'cs'})
      .timeout(const Duration(seconds: 15));
  if (res.statusCode != 200) {
    throw Exception('Geokódování selhalo (${res.statusCode})');
  }
  return json.decode(res.body) as List;
}

// Čísla z konce zadané adresy: "nepolisy 281" -> {281}, "Palackého 123/45" ->
// {123, 45}, "Zámecká 12a" -> {12}.
Set<String> _queryNumbers(String query) {
  final m = RegExp(r'(\d+(?:\s*/\s*\d+)?)\s*[a-zA-Z]?\s*$')
      .firstMatch(query.trim());
  if (m == null) return <String>{};
  return RegExp(r'\d+')
      .allMatches(m.group(1)!)
      .map((x) => x.group(0)!)
      .toSet();
}

Set<String> _numbersIn(String text) {
  return RegExp(r'\d+').allMatches(text).map((x) => x.group(0)!).toSet();
}

// Je výsledek opravdu ten dům, který jsme hledali? (na úrovni domu A zároveň
// sedí číslo, které řidič napsal)
bool _isPreciseMatch(Map r, Set<String> queryNums) {
  final type = r['type']?.toString();
  final address = r['address'] as Map?;
  final hn = address?['house_number']?.toString();
  final isHouse = type == 'house' || type == 'building' || hn != null;
  if (!isHouse) return false;
  if (queryNums.isEmpty || hn == null) return true;
  final resultNums = _numbersIn(hn);
  return queryNums.any((n) => resultNums.contains(n));
}

// Bodování výsledků z Nominatimu. Dřív appka vybírala prostě ten výsledek, co
// byl nejblíž Chlumci - a tak se stávalo, že místo domu "Nepolisy 281"
// vybrala nějaký bod ve stejné vesnici (třeba firmu), který byl o kus blíž.
// Teď vyhrává: dům se správným číslem > dům s jiným číslem > střed obce / ulice
// > ostatní body (firmy, objekty). Při shodě rozhoduje vzdálenost od Chlumce.
double _candidateScore(Map r, Set<String> queryNums) {
  final type = r['type']?.toString();
  final cls = (r['class'] ?? r['category'])?.toString();
  final address = r['address'] as Map?;
  final hn = address?['house_number']?.toString();
  final isHouse = type == 'house' || type == 'building' || hn != null;
  double score = 0;
  if (isHouse) score += 100;
  if (queryNums.isNotEmpty && hn != null) {
    final resultNums = _numbersIn(hn);
    if (queryNums.any((n) => resultNums.contains(n))) {
      score += 200;
    } else {
      score -= 150;
    }
  }
  if (!isHouse) {
    if (cls == 'place') {
      score += 40;
    } else if (cls == 'highway') {
      score += 30;
    }
  }
  return score;
}

GeocodeResult? _bestCandidate(List results, String query) {
  final queryNums = _queryNumbers(query);
  GeocodeResult? best;
  double bestScore = -1e9;
  for (final r in results) {
    if (r is! Map) continue;
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
    final score = _candidateScore(r, queryNums);
    if (best == null ||
        score > bestScore ||
        (score == bestScore && dist < best.distanceKm)) {
      best = GeocodeResult(
        lat,
        lon,
        dist,
        isPrecise: _isPreciseMatch(r, queryNums),
        label: (r['display_name'] ?? '').toString(),
      );
      bestScore = score;
    }
  }
  return best;
}

Future<GeocodeResult?> _geocodeInChlumec(String address) async {
  // Zkouší se postupně: 1) čistá adresa v okruhu (správně najde i samostatné
  // vesnice), 2) s okresem, 3) výslovně s Chlumcem (ulice přímo ve městě).
  // Jakmile se najde přesný dům se správným číslem, hledání končí; jinak se
  // zkusí další varianta a nakonec se použije první přibližný nález.
  final queries = <String>[
    address,
    '$address, okres Hradec Králové',
    '$address, Chlumec nad Cidlinou',
  ];
  GeocodeResult? approximate;
  for (final q in queries) {
    final results = await _nominatimSearch(q);
    final candidate = _bestCandidate(results, address);
    if (candidate == null) continue;
    if (candidate.isPrecise) return candidate;
    approximate ??= candidate;
  }
  return approximate;
}

// Zeptá se, jestli chce uživatel pokračovat s adresou, kterou appka nenašla
// přesně na úrovni čísla popisného (typicky malé vesnice bez zmapovaných
// jednotlivých čísel v OpenStreetMap) - appka pak navede jen do okolí.
Future<bool> _confirmImpreciseAddress(BuildContext context,
    {String? found}) async {
  final confirmed = await showDialog<bool>(
    context: context,
    builder: (ctx) => AlertDialog(
      title: const Text('Adresa nalezena jen přibližně'),
      content: Text(
          'Appka nenašla přesné číslo popisné/orientační - navede tě jen '
          'do okolí (např. střed obce), ne přímo k domu.'
          '${found != null && found.isNotEmpty ? '\n\nNalezeno: $found' : ''}'
          '\n\nChceš i tak pokračovat?'),
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
  final double handTip; // dýško na ruku - hotově navíc, mimo terminál / online platbu
  bool bossDelivered; // true = tuhle objednávku vezl šéf sám
  final bool paidByCard; // true = platba na místě proběhla kartou (ne hotově)
  final double lat;
  final double lon;
  final DateTime createdAt;
  bool done;
  DateTime? completedAt;

  // --- Údaje pro počítání kilometrů (vyplní appka při navigaci) ---
  // 0 = neznámé (starší objednávka, appka to odhadne podle časů),
  // 1 = jízda začala na základně (restauraci),
  // 2 = navazuje na předchozí objednávku (jel jsem rovnou od ní, ne přes základnu)
  final int tripMode;
  final String? chainPrev; // id objednávky, na kterou navazuje (jen tripMode 2)
  final double? startLat; // kde jsem byl, když jsem spustil navigaci
  final double? startLon;
  final DateTime? startedAt; // kdy jsem spustil navigaci

  DeliveryOrder({
    required this.id,
    required this.address,
    required this.phone,
    required this.amount,
    required this.prePaid,
    this.deliveryFee = 0,
    this.tip = 0,
    this.cashCardTip = 0,
    this.handTip = 0,
    this.bossDelivered = false,
    this.paidByCard = false,
    required this.lat,
    required this.lon,
    required this.createdAt,
    this.done = false,
    this.completedAt,
    this.tripMode = 0,
    this.chainPrev,
    this.startLat,
    this.startLon,
    this.startedAt,
  });

  // Všechno dýško z téhle objednávky: online nebo z terminálu/hotovosti
  // + dýško na ruku.
  double get totalTip => (prePaid ? tip : cashCardTip) + handTip;

  Map<String, dynamic> toJson() => {
        'id': id,
        'address': address,
        'phone': phone,
        'amount': amount,
        'prePaid': prePaid,
        'deliveryFee': deliveryFee,
        'tip': tip,
        'cashCardTip': cashCardTip,
        'handTip': handTip,
        'bossDelivered': bossDelivered,
        'paidByCard': paidByCard,
        'lat': lat,
        'lon': lon,
        'createdAt': createdAt.toIso8601String(),
        'done': done,
        'completedAt': completedAt?.toIso8601String(),
        'tripMode': tripMode,
        'chainPrev': chainPrev,
        'startLat': startLat,
        'startLon': startLon,
        'startedAt': startedAt?.toIso8601String(),
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
        handTip: (j['handTip'] as num?)?.toDouble() ?? 0,
        bossDelivered: j['bossDelivered'] as bool? ?? false,
        paidByCard: j['paidByCard'] as bool? ?? false,
        lat: (j['lat'] as num).toDouble(),
        lon: (j['lon'] as num).toDouble(),
        createdAt: DateTime.parse(j['createdAt']),
        done: j['done'] as bool? ?? false,
        completedAt: j['completedAt'] != null
            ? DateTime.parse(j['completedAt'])
            : null,
        tripMode: (j['tripMode'] as num?)?.toInt() ?? 0,
        chainPrev: j['chainPrev'] as String?,
        startLat: (j['startLat'] as num?)?.toDouble(),
        startLon: (j['startLon'] as num?)?.toDouble(),
        startedAt: j['startedAt'] != null
            ? DateTime.parse(j['startedAt'])
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
    double? handTip,
    bool? paidByCard,
    double? lat,
    double? lon,
    int? tripMode,
    String? chainPrev,
    double? startLat,
    double? startLon,
    DateTime? startedAt,
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
      handTip: handTip ?? this.handTip,
      paidByCard: paidByCard ?? this.paidByCard,
      lat: lat ?? this.lat,
      lon: lon ?? this.lon,
      createdAt: createdAt,
      done: done,
      completedAt: completedAt,
      bossDelivered: bossDelivered,
      tripMode: tripMode ?? this.tripMode,
      chainPrev: chainPrev ?? this.chainPrev,
      startLat: startLat ?? this.startLat,
      startLon: startLon ?? this.startLon,
      startedAt: startedAt ?? this.startedAt,
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
  // true = poloha byla nalezena přesně na úrovni domu se správným číslem.
  // Jen takovým polohám appka příště věří bez nového hledání; ostatní
  // (a všechny starší uložené) se při dalším použití znovu dohledají.
  final bool verified;

  SavedPlace({
    required this.id,
    required this.address,
    required this.label,
    required this.phone,
    required this.lat,
    required this.lon,
    required this.lastUsedAt,
    this.verified = false,
  });

  Map<String, dynamic> toJson() => {
        'id': id,
        'address': address,
        'label': label,
        'phone': phone,
        'lat': lat,
        'lon': lon,
        'lastUsedAt': lastUsedAt.toIso8601String(),
        'verified': verified,
      };

  factory SavedPlace.fromJson(Map<String, dynamic> j) => SavedPlace(
        id: j['id'],
        address: j['address'],
        label: j['label'] as String? ?? '',
        phone: j['phone'] as String? ?? '',
        lat: (j['lat'] as num).toDouble(),
        lon: (j['lon'] as num).toDouble(),
        lastUsedAt: DateTime.parse(j['lastUsedAt']),
        verified: j['verified'] as bool? ?? false,
      );

  SavedPlace copyWith({
    String? label,
    String? phone,
    DateTime? lastUsedAt,
    double? lat,
    double? lon,
    bool? verified,
  }) {
    return SavedPlace(
      id: id,
      address: address,
      label: label ?? this.label,
      phone: phone ?? this.phone,
      lat: lat ?? this.lat,
      lon: lon ?? this.lon,
      lastUsedAt: lastUsedAt ?? this.lastUsedAt,
      verified: verified ?? this.verified,
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
  // jiný). Souřadnice se přepíšou, když je nový nález přesný, nebo když to
  // staré místo ještě nebylo ověřené - tím se špatně uložené polohy samy
  // opraví. Vrátí novou celou aktualizovanou historii.
  static List<SavedPlace> upsert(
    List<SavedPlace> current, {
    required String address,
    required String label,
    required String phone,
    required double lat,
    required double lon,
    bool verified = false,
  }) {
    final normalized = address.trim().toLowerCase();
    final idx =
        current.indexWhere((p) => p.address.trim().toLowerCase() == normalized);
    final updatedList = [...current];
    if (idx != -1) {
      final old = updatedList[idx];
      final replaceCoords = verified || !old.verified;
      updatedList[idx] = old.copyWith(
        label: label.isNotEmpty ? label : old.label,
        phone: phone.isNotEmpty ? phone : old.phone,
        lastUsedAt: DateTime.now(),
        lat: replaceCoords ? lat : old.lat,
        lon: replaceCoords ? lon : old.lon,
        verified: replaceCoords ? verified : old.verified,
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
          verified: verified,
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
  late final TextEditingController _handTipController;
  late bool _prePaid;
  bool _regeocode = false; // vynutit nové vyhledání polohy i při stejné adrese
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
    _handTipController = TextEditingController(
        text: o.handTip > 0 ? o.handTip.toStringAsFixed(0) : '');
    _prePaid = o.prePaid;
  }

  @override
  void dispose() {
    _addressController.dispose();
    _phoneController.dispose();
    _amountController.dispose();
    _deliveryFeeController.dispose();
    _tipController.dispose();
    _handTipController.dispose();
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
    final handTip = double.tryParse(
            _handTipController.text.trim().replaceAll(',', '.')) ??
        0;

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

    // adresa se změnila (nebo chci polohu vyhledat znovu) -> dohledat souřadnice
    if (address != widget.order.address || _regeocode) {
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
          final ok =
              await _confirmImpreciseAddress(context, found: result.label);
          if (!ok) {
            setState(() => _saving = false);
            return;
          }
        }
        lat = result.lat;
        lon = result.lon;
        // opravená poloha se uloží i do uložených míst, ať se při příští
        // objednávce na tuhle adresu nepoužije stará špatná
        final places = await SavedPlacesStore.load();
        await SavedPlacesStore.save(SavedPlacesStore.upsert(
          places,
          address: address,
          label: '',
          phone: phone,
          lat: lat,
          lon: lon,
          verified: result.isPrecise,
        ));
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
      handTip: widget.order.done ? handTip : widget.order.handTip,
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
            CheckboxListTile(
              dense: true,
              contentPadding: EdgeInsets.zero,
              controlAffinity: ListTileControlAffinity.leading,
              value: _regeocode,
              onChanged: (v) => setState(() => _regeocode = v ?? false),
              title: const Text('Znovu vyhledat polohu na mapě',
                  style: TextStyle(fontSize: 13)),
              subtitle: const Text('Zaškrtni, když tě appka vede na špatné místo',
                  style: TextStyle(fontSize: 11)),
            ),
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
            if (widget.order.done) ...[
              const SizedBox(height: 10),
              TextField(
                controller: _handTipController,
                keyboardType:
                    const TextInputType.numberWithOptions(decimal: true),
                decoration: const InputDecoration(
                  labelText: 'Dýško na ruku (Kč)',
                  border: OutlineInputBorder(),
                ),
              ),
            ],
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

// ===================== VZHLED (světlý / tmavý režim) =====================
// Zvolený režim se ukládá do nastavení. Sem se později dá celý nový vzhled
// appky - barvy a styly se berou odtud, ne z jednotlivých obrazovek.
final ValueNotifier<ThemeMode> appThemeMode =
    ValueNotifier<ThemeMode>(ThemeMode.light);

ThemeMode _themeModeFromString(String? s) {
  switch (s) {
    case 'dark':
      return ThemeMode.dark;
    case 'system':
      return ThemeMode.system;
    default:
      return ThemeMode.light;
  }
}

String _themeModeToString(ThemeMode m) {
  switch (m) {
    case ThemeMode.dark:
      return 'dark';
    case ThemeMode.system:
      return 'system';
    case ThemeMode.light:
      return 'light';
  }
}

// ---- Barevné palety (zvolená se ukládá do nastavení, jako světlý/tmavý režim) ----
enum AppPalette { orange, indigo, warm }

final ValueNotifier<AppPalette> appPalette =
    ValueNotifier<AppPalette>(AppPalette.orange);

AppPalette _paletteFromString(String? s) {
  switch (s) {
    case 'indigo':
      return AppPalette.indigo;
    case 'warm':
      return AppPalette.warm;
    default:
      return AppPalette.orange;
  }
}

String _paletteToString(AppPalette p) {
  switch (p) {
    case AppPalette.indigo:
      return 'indigo';
    case AppPalette.warm:
      return 'warm';
    case AppPalette.orange:
      return 'orange';
  }
}

String _paletteName(AppPalette p) {
  switch (p) {
    case AppPalette.indigo:
      return 'Indigo';
    case AppPalette.warm:
      return 'Béžová';
    case AppPalette.orange:
      return 'Oranžová';
  }
}

class _Tokens {
  final Color bg;
  final Color card;
  final Color text;
  final Color muted;
  final Color acc;
  final Color onAcc;
  final Color soft;
  final Color chipText;
  final Color border;
  final Color inp;
  final Color route;
  const _Tokens({
    required this.bg,
    required this.card,
    required this.text,
    required this.muted,
    required this.acc,
    required this.onAcc,
    required this.soft,
    required this.chipText,
    required this.border,
    required this.inp,
    required this.route,
  });
}

const _Tokens _orangeLight = _Tokens(
  bg: Color(0xFFF5F4F1), card: Color(0xFFFFFFFF), text: Color(0xFF1C1B19),
  muted: Color(0xFF6B665F), acc: Color(0xFFFB923C), onAcc: Color(0xFF1C1B19),
  soft: Color(0xFFFDEBDD), chipText: Color(0xFF7C2D12), border: Color(0xFFE7E3DC),
  inp: Color(0xFFF5F4F1), route: Color(0xFFFB923C),
);
const _Tokens _orangeDark = _Tokens(
  bg: Color(0xFF121110), card: Color(0xFF1D1B19), text: Color(0xFFF3F0EB),
  muted: Color(0xFFA39D94), acc: Color(0xFFFB923C), onAcc: Color(0xFF1C1B19),
  soft: Color(0xFF3A2416), chipText: Color(0xFFFDBA74), border: Color(0xFF2D2A26),
  inp: Color(0xFF121110), route: Color(0xFFFB923C),
);
const _Tokens _indigoLight = _Tokens(
  bg: Color(0xFFF3F4FA), card: Color(0xFFFFFFFF), text: Color(0xFF161A2B),
  muted: Color(0xFF5B6178), acc: Color(0xFF4338CA), onAcc: Color(0xFFFFFFFF),
  soft: Color(0xFFEEF0FF), chipText: Color(0xFF312E81), border: Color(0xFFE3E6F0),
  inp: Color(0xFFF3F4FA), route: Color(0xFF4338CA),
);
const _Tokens _indigoDark = _Tokens(
  bg: Color(0xFF0E1420), card: Color(0xFF161C2C), text: Color(0xFFE8ECF7),
  muted: Color(0xFF9AA3BD), acc: Color(0xFF818CF8), onAcc: Color(0xFF0E1420),
  soft: Color(0xFF25295A), chipText: Color(0xFFC7CBFF), border: Color(0xFF27304A),
  inp: Color(0xFF0E1420), route: Color(0xFF818CF8),
);
const _Tokens _warmLight = _Tokens(
  bg: Color(0xFFF7F3EC), card: Color(0xFFFFFFFF), text: Color(0xFF1F1A14),
  muted: Color(0xFF6D6458), acc: Color(0xFFFB923C), onAcc: Color(0xFF1F1A14),
  soft: Color(0xFFFBE7D6), chipText: Color(0xFF7C2D12), border: Color(0xFFE9E1D4),
  inp: Color(0xFFF7F3EC), route: Color(0xFF4338CA),
);
const _Tokens _warmDark = _Tokens(
  bg: Color(0xFF14110E), card: Color(0xFF201B16), text: Color(0xFFF5EFE6),
  muted: Color(0xFFAEA496), acc: Color(0xFFFB923C), onAcc: Color(0xFF1F1A14),
  soft: Color(0xFF3B2616), chipText: Color(0xFFFDBA74), border: Color(0xFF322B24),
  inp: Color(0xFF14110E), route: Color(0xFF818CF8),
);

class AppTheme {
  static _Tokens _tokens(AppPalette p, Brightness b) {
    final dark = b == Brightness.dark;
    switch (p) {
      case AppPalette.indigo:
        return dark ? _indigoDark : _indigoLight;
      case AppPalette.warm:
        return dark ? _warmDark : _warmLight;
      case AppPalette.orange:
        return dark ? _orangeDark : _orangeLight;
    }
  }

  // Barva trasy na mapě podle zvolené palety.
  static Color routeColor(Brightness b) =>
      _tokens(appPalette.value, b).route;

  // Náhled barvy palety (kolečka v Nastavení).
  static Color swatch(AppPalette p, Brightness b) => _tokens(p, b).acc;

  static ThemeData light(AppPalette p) => _build(p, Brightness.light);
  static ThemeData dark(AppPalette p) => _build(p, Brightness.dark);

  static ThemeData _build(AppPalette p, Brightness b) {
    final k = _tokens(p, b);
    final dark = b == Brightness.dark;
    final cs = ColorScheme(
      brightness: b,
      primary: k.acc,
      onPrimary: k.onAcc,
      primaryContainer: k.soft,
      onPrimaryContainer: k.chipText,
      secondary: k.acc,
      onSecondary: k.onAcc,
      secondaryContainer: k.soft,
      onSecondaryContainer: k.chipText,
      tertiary: k.acc,
      onTertiary: k.onAcc,
      tertiaryContainer: k.soft,
      onTertiaryContainer: k.chipText,
      error: dark ? const Color(0xFFF2B8B5) : const Color(0xFFB3261E),
      onError: dark ? const Color(0xFF601410) : const Color(0xFFFFFFFF),
      surface: k.card,
      onSurface: k.text,
      onSurfaceVariant: k.muted,
      outline: k.muted,
      outlineVariant: k.border,
      surfaceContainerLowest: k.card,
      surfaceContainerLow: k.card,
      surfaceContainer: k.card,
      surfaceContainerHigh: k.card,
      surfaceContainerHighest: k.inp,
      inverseSurface: k.text,
      onInverseSurface: k.bg,
      inversePrimary: k.acc,
      surfaceTint: Colors.transparent,
    );
    final r14 = RoundedRectangleBorder(borderRadius: BorderRadius.circular(14));
    OutlineInputBorder ob(Color c, [double w = 1]) => OutlineInputBorder(
          borderRadius: BorderRadius.circular(14),
          borderSide: BorderSide(color: c, width: w),
        );
    return ThemeData(
      useMaterial3: true,
      brightness: b,
      colorScheme: cs,
      scaffoldBackgroundColor: k.bg,
      appBarTheme: AppBarThemeData(
        backgroundColor: k.bg,
        foregroundColor: k.text,
        elevation: 0,
        scrolledUnderElevation: 0,
        surfaceTintColor: Colors.transparent,
        centerTitle: false,
        titleTextStyle: TextStyle(
          color: k.text,
          fontSize: 26,
          fontWeight: FontWeight.w800,
          letterSpacing: -0.5,
        ),
      ),
      cardTheme: CardThemeData(
        color: k.card,
        elevation: 0,
        surfaceTintColor: Colors.transparent,
        margin: const EdgeInsets.symmetric(vertical: 4),
        shape: RoundedRectangleBorder(
          borderRadius: BorderRadius.circular(20),
          side: BorderSide(color: k.border),
        ),
      ),
      inputDecorationTheme: InputDecorationThemeData(
        filled: true,
        fillColor: k.inp,
        border: ob(k.border),
        enabledBorder: ob(k.border),
        focusedBorder: ob(k.acc, 2),
        errorBorder: ob(cs.error),
        focusedErrorBorder: ob(cs.error, 2),
      ),
      filledButtonTheme: FilledButtonThemeData(
        style: FilledButton.styleFrom(
          minimumSize: const Size(0, 48),
          shape: r14,
          textStyle: const TextStyle(fontSize: 16, fontWeight: FontWeight.w700),
        ),
      ),
      elevatedButtonTheme: ElevatedButtonThemeData(
        style: ElevatedButton.styleFrom(
          minimumSize: const Size(0, 48),
          shape: r14,
          textStyle: const TextStyle(fontSize: 16, fontWeight: FontWeight.w700),
        ),
      ),
      outlinedButtonTheme: OutlinedButtonThemeData(
        style: OutlinedButton.styleFrom(
          minimumSize: const Size(0, 48),
          shape: r14,
          side: BorderSide(color: k.border),
          textStyle: const TextStyle(fontSize: 15, fontWeight: FontWeight.w700),
        ),
      ),
      textButtonTheme: TextButtonThemeData(
        style: TextButton.styleFrom(
          shape: r14,
          textStyle: const TextStyle(fontWeight: FontWeight.w700),
        ),
      ),
      chipTheme: ChipThemeData(
        backgroundColor: k.soft,
        side: BorderSide.none,
        shape: const StadiumBorder(),
        labelStyle: TextStyle(
            color: k.chipText, fontWeight: FontWeight.w700, fontSize: 12),
      ),
      dialogTheme: DialogThemeData(
        backgroundColor: k.card,
        surfaceTintColor: Colors.transparent,
        shape: RoundedRectangleBorder(borderRadius: BorderRadius.circular(28)),
      ),
      bottomSheetTheme: BottomSheetThemeData(
        backgroundColor: k.bg,
        surfaceTintColor: Colors.transparent,
        shape: const RoundedRectangleBorder(
          borderRadius: BorderRadius.vertical(top: Radius.circular(28)),
        ),
      ),
      popupMenuTheme: PopupMenuThemeData(
        color: k.card,
        surfaceTintColor: Colors.transparent,
        shape: r14,
      ),
      snackBarTheme: SnackBarThemeData(
        behavior: SnackBarBehavior.floating,
        backgroundColor: k.text,
        contentTextStyle: TextStyle(color: k.bg),
        shape: r14,
      ),
      dividerTheme: DividerThemeData(color: k.border, space: 1, thickness: 1),
      expansionTileTheme: const ExpansionTileThemeData(
        shape: Border(),
        collapsedShape: Border(),
      ),
      switchTheme: SwitchThemeData(
        thumbColor: WidgetStateProperty.resolveWith((s) =>
            s.contains(WidgetState.selected) ? k.onAcc : k.card),
        trackColor: WidgetStateProperty.resolveWith((s) =>
            s.contains(WidgetState.selected) ? k.acc : k.border),
        trackOutlineColor: WidgetStateProperty.all(Colors.transparent),
      ),
    );
  }
}

Future<void> main() async {
  WidgetsFlutterBinding.ensureInitialized();
  try {
    final settings = await AppSettingsStore.load();
    appThemeMode.value = _themeModeFromString(settings['themeMode'] as String?);
    appPalette.value = _paletteFromString(settings['palette'] as String?);
  } catch (_) {}
  runApp(const RozvozkaApp());
}

class RozvozkaApp extends StatelessWidget {
  const RozvozkaApp({super.key});

  @override
  Widget build(BuildContext context) {
    return ValueListenableBuilder<AppPalette>(
      valueListenable: appPalette,
      builder: (context, palette, _) => ValueListenableBuilder<ThemeMode>(
        valueListenable: appThemeMode,
        builder: (context, mode, _) => MaterialApp(
          debugShowCheckedModeBanner: false,
          title: 'Rozvozka',
          theme: AppTheme.light(palette),
          darkTheme: AppTheme.dark(palette),
          themeMode: mode,
          locale: const Locale('cs'),
          supportedLocales: const [Locale('cs'), Locale('en')],
          localizationsDelegates: const [
            GlobalMaterialLocalizations.delegate,
            GlobalWidgetsLocalizations.delegate,
            GlobalCupertinoLocalizations.delegate,
          ],
          home: const OrdersScreen(),
        ),
      ),
    );
  }
}

// ---- Pomocné věci pro telefonní čísla a dýška v seznamu objednávek ----
String _normAddr(String a) =>
    a.trim().toLowerCase().replaceAll(RegExp(r'\s+'), ' ');

// Porovnává se posledních 9 číslic, ať nevadí předvolba +420 ani mezery.
String _normPhone(String p) {
  final d = p.replaceAll(RegExp(r'[^0-9]'), '');
  return d.length > 9 ? d.substring(d.length - 9) : d;
}

String _fmtShortDate(DateTime d) => '${d.day}. ${d.month}.';

// 3840 -> "3 840" (pevná mezera, ať se číslo nezalomí)
String _fmtThousands(num v) {
  final s = v.round().abs().toString();
  final b = StringBuffer(v < 0 ? '-' : '');
  for (int i = 0; i < s.length; i++) {
    if (i > 0 && (s.length - i) % 3 == 0) b.write('\u00A0');
    b.write(s[i]);
  }
  return b.toString();
}

class _PhoneUse {
  String phone;
  int count;
  DateTime lastUsed;
  _PhoneUse(this.phone, this.count, this.lastUsed);
}

class _TipEntry {
  final DateTime when;
  final double amount;
  const _TipEntry(this.when, this.amount);
}

class _TipSummary {
  final int orders; // kolik doručených objednávek z toho čísla je
  final int known; // u kolika z nich appka dýško umí zjistit
  final List<_TipEntry> entries; // jen objednávky s dýškem, nejnovější první
  final double total;
  const _TipSummary(this.orders, this.known, this.entries, this.total);
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
  String? _autoPhone; // telefon, který appka sama doplnila podle adresy
  bool _tipsExpanded = false;

  bool? _trackCashCardTips; // null = ještě se appka nezeptala
  bool _askHandTip = true; // ptát se při Doručeno na dýško na ruku

  // Najeté km dnes pro pruh nahoře (z uložených tras, nic se tu nestahuje).
  double? _kmToday;
  bool _kmTodayEstimated = false;

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

  // Všechna čísla, ze kterých se kdy objednávalo na tuhle adresu, od nejnovějšího.
  // U adres, kde se čísla střídají, si tak vybereš ze seznamu.
  List<_PhoneUse> _phonesForAddress(String address) {
    final key = _normAddr(address);
    if (key.isEmpty) return [];
    final byNumber = <String, _PhoneUse>{};
    for (final o in _orders) {
      if (_normAddr(o.address) != key) continue;
      final n = _normPhone(o.phone);
      if (n.isEmpty) continue;
      final when = o.completedAt ?? o.createdAt;
      final existing = byNumber[n];
      if (existing == null) {
        byNumber[n] = _PhoneUse(o.phone, 1, when);
      } else {
        existing.count++;
        if (when.isAfter(existing.lastUsed)) {
          existing.lastUsed = when;
          existing.phone = o.phone;
        }
      }
    }
    for (final sp in _savedPlaces) {
      if (_normAddr(sp.address) != key) continue;
      final n = _normPhone(sp.phone);
      if (n.isEmpty || byNumber.containsKey(n)) continue;
      byNumber[n] = _PhoneUse(sp.phone, 0, sp.lastUsedAt);
    }
    final list = byNumber.values.toList()
      ..sort((a, b) => b.lastUsed.compareTo(a.lastUsed));
    return list;
  }

  // Dýška z tohohle telefonního čísla - číslo patří konkrétnímu člověku, na
  // rozdíl od adresy, kde může objednávat víc různých lidí (byty apod.).
  _TipSummary? _tipSummaryForPhone(String phone) {
    final n = _normPhone(phone);
    if (n.length < 9) return null;
    final matches = _orders
        .where((o) =>
            o.done && o.completedAt != null && _normPhone(o.phone) == n)
        .toList()
      ..sort((a, b) => b.completedAt!.compareTo(a.completedAt!));
    if (matches.isEmpty) return null;
    final entries = <_TipEntry>[];
    double total = 0;
    int known = 0;
    for (final o in matches) {
      // dýško z hotovosti/karty appka zná jen když je zapnuté sledování
      final tipKnown =
          o.prePaid || (_trackCashCardTips == true) || o.handTip > 0;
      if (tipKnown) known++;
      final t = o.totalTip;
      if (t > 0) {
        entries.add(_TipEntry(o.completedAt!, t));
        total += t;
      }
    }
    return _TipSummary(matches.length, known, entries, total);
  }

  void _onPhoneChanged() {
    setState(() {
      _tipsExpanded = false;
    });
  }

  void _onAddressChanged() {
    final q = _addressController.text.trim().toLowerCase();
    setState(() {
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
      // Když je adresa už známá, appka sama doplní poslední číslo, které na ni
      // objednávalo. Doplněné číslo zase zmizí, když adresu dopíšeš na jinou
      // (a mezitím jsi do telefonu nic nepsal sám).
      final known = _phonesForAddress(_addressController.text);
      if (known.isNotEmpty) {
        if (_phoneController.text.isEmpty ||
            _phoneController.text == _autoPhone) {
          _phoneController.text = known.first.phone;
          _autoPhone = known.first.phone;
        }
      } else if (_autoPhone != null) {
        if (_phoneController.text == _autoPhone) _phoneController.clear();
        _autoPhone = null;
      }
    });
  }

  Widget _buildTipHistory(BuildContext context, _TipSummary s) {
    final cs = Theme.of(context).colorScheme;
    final shown = _tipsExpanded ? s.entries : s.entries.take(8).toList();
    final String headline;
    if (s.entries.isEmpty) {
      headline = 'Z tohohle čísla zatím žádné dýško (${s.orders} objednávek)';
    } else {
      final n = s.entries.length;
      final word = n == 1 ? 'objednávka' : (n >= 2 && n <= 4 ? 'objednávky' : 'objednávek');
      headline = '$n $word s dýškem, celkem ${s.total.toStringAsFixed(0)},-';
    }
    return Container(
      margin: const EdgeInsets.only(top: 6),
      padding: const EdgeInsets.symmetric(horizontal: 10, vertical: 7),
      decoration: BoxDecoration(
        color: cs.secondaryContainer,
        borderRadius: BorderRadius.circular(8),
      ),
      child: Column(
        crossAxisAlignment: CrossAxisAlignment.start,
        children: [
          Row(
            crossAxisAlignment: CrossAxisAlignment.start,
            children: [
              Icon(Icons.volunteer_activism_outlined,
                  size: 16, color: cs.onSecondaryContainer),
              const SizedBox(width: 8),
              Expanded(
                child: Text(
                  headline,
                  style: TextStyle(
                    fontSize: 12,
                    fontWeight: FontWeight.w600,
                    color: cs.onSecondaryContainer,
                  ),
                ),
              ),
            ],
          ),
          if (shown.isNotEmpty)
            Padding(
              padding: const EdgeInsets.only(top: 6),
              child: Wrap(
                spacing: 6,
                runSpacing: 4,
                children: [
                  for (final e in shown)
                    Container(
                      padding:
                          const EdgeInsets.symmetric(horizontal: 8, vertical: 3),
                      decoration: BoxDecoration(
                        color: cs.surface,
                        borderRadius: BorderRadius.circular(12),
                      ),
                      child: Text(
                        '${e.amount.toStringAsFixed(0)},- · ${_fmtShortDate(e.when)}',
                        style: const TextStyle(
                            fontSize: 12, fontWeight: FontWeight.w600),
                      ),
                    ),
                ],
              ),
            ),
          if (s.entries.length > 8)
            Align(
              alignment: Alignment.centerLeft,
              child: TextButton(
                onPressed: () => setState(() => _tipsExpanded = !_tipsExpanded),
                child: Text(_tipsExpanded
                    ? 'Skrýt'
                    : 'Zobrazit všechna (${s.entries.length})'),
              ),
            ),
        ],
      ),
    );
  }

  Future<void> _loadSavedPlaces() async {
    final places = await SavedPlacesStore.load();
    setState(() => _savedPlaces = places);
  }

  Future<void> _loadSettings() async {
    final settings = await AppSettingsStore.load();
    setState(() {
      _trackCashCardTips = settings['trackCashCardTips'] as bool?;
      _askHandTip = settings['askHandTip'] as bool? ?? true;
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
    final settings = await AppSettingsStore.load();
    settings['trackCashCardTips'] = value;
    await AppSettingsStore.save(settings);
  }

  Future<void> _loadOrders() async {
    try {
      final orders = await OrdersStore.load();
      setState(() {
        _orders = orders;
        _loading = false;
      });
      unawaited(_computeKmToday());
    } catch (e) {
      setState(() {
        _orders = [];
        _loading = false;
        _errorMessage = 'Nepodařilo se načíst uložená data: $e';
      });
    }
  }

  Future<void> _computeKmToday() async {
    try {
      final settings = await AppSettingsStore.load();
      final cache = await KmService.loadCache();
      final report =
          KmService.compute(_orders, _baseFromSettings(settings), cache);
      double sum = 0;
      bool est = false;
      for (final o in _completedToday) {
        final k = report.kmByOrder[o.id];
        if (k != null) {
          sum += k;
          if (report.estimated.contains(o.id)) est = true;
        }
      }
      if (!mounted) return;
      setState(() {
        _kmToday = sum;
        _kmTodayEstimated = est;
      });
    } catch (_) {}
  }

  // Malé obdélníkové tlačítko v horní liště (stejný styl jako v návrhu).
  Widget _barButton(IconData icon, String tooltip, VoidCallback onPressed) {
    final cs = Theme.of(context).colorScheme;
    return Padding(
      padding: const EdgeInsets.only(left: 6),
      child: IconButton(
        icon: Icon(icon, size: 20),
        tooltip: tooltip,
        onPressed: onPressed,
        style: IconButton.styleFrom(
          backgroundColor: cs.surface,
          foregroundColor: cs.onSurface,
          side: BorderSide(color: cs.outlineVariant),
          fixedSize: const Size(44, 44),
          shape:
              RoundedRectangleBorder(borderRadius: BorderRadius.circular(14)),
        ),
      ),
    );
  }

  // Pruh "dnes": doručeno / tržba / km.
  Widget _todayStrip(ColorScheme cs) {
    final done = _completedToday;
    final revenue = done.fold<double>(0, (s, o) => s + o.amount);
    final kmText = _kmToday == null
        ? '–'
        : '${_kmTodayEstimated ? '~' : ''}${_kmToday!.toStringAsFixed(0)}';
    Widget cell(String value, String label, {bool accent = false}) {
      return Expanded(
        child: Column(
          children: [
            Text(value,
                style: TextStyle(
                    fontSize: 26,
                    fontWeight: FontWeight.w800,
                    color: accent ? cs.primary : cs.onSurface)),
            Text(label,
                style: TextStyle(fontSize: 12, color: cs.onSurfaceVariant)),
          ],
        ),
      );
    }

    return Card(
      child: Padding(
        padding: const EdgeInsets.symmetric(vertical: 16, horizontal: 8),
        child: IntrinsicHeight(
          child: Row(
            children: [
              cell('${done.length}', 'doručeno'),
              VerticalDivider(width: 1, color: cs.outlineVariant),
              cell(_fmtThousands(revenue), 'Kč tržba', accent: true),
              VerticalDivider(width: 1, color: cs.outlineVariant),
              cell(kmText, 'km dnes'),
            ],
          ),
        ),
      ),
    );
  }

  Widget _sectionLabel(String text) {
    final cs = Theme.of(context).colorScheme;
    return Padding(
      padding: const EdgeInsets.fromLTRB(2, 18, 2, 8),
      child: Text(
        text.toUpperCase(),
        style: TextStyle(
            fontSize: 12,
            fontWeight: FontWeight.w700,
            letterSpacing: 0.7,
            color: cs.onSurfaceVariant),
      ),
    );
  }

  Widget _miniChip(String text) {
    final cs = Theme.of(context).colorScheme;
    return Container(
      padding: const EdgeInsets.symmetric(horizontal: 10, vertical: 4),
      decoration: BoxDecoration(
        color: cs.secondaryContainer,
        borderRadius: BorderRadius.circular(999),
      ),
      child: Text(text,
          style: TextStyle(
              fontSize: 12,
              fontWeight: FontWeight.w700,
              color: cs.onSecondaryContainer)),
    );
  }

  // Karta čekající objednávky: adresa, telefon, čipy, částka, navigace.
  Widget _orderCard(DeliveryOrder o) {
    final cs = Theme.of(context).colorScheme;
    final total = o.prePaid ? o.amount : o.amount + o.deliveryFee;
    return Card(
      child: InkWell(
        borderRadius: BorderRadius.circular(20),
        onTap: () => _openDelivery(o),
        child: Padding(
          padding: const EdgeInsets.fromLTRB(16, 14, 12, 14),
          child: Row(
            crossAxisAlignment: CrossAxisAlignment.start,
            children: [
              Expanded(
                child: Column(
                  crossAxisAlignment: CrossAxisAlignment.start,
                  children: [
                    Text(o.address,
                        maxLines: 2,
                        overflow: TextOverflow.ellipsis,
                        style: const TextStyle(
                            fontSize: 17, fontWeight: FontWeight.w700)),
                    const SizedBox(height: 4),
                    Text(o.phone,
                        style: TextStyle(
                            fontSize: 14, color: cs.onSurfaceVariant)),
                    const SizedBox(height: 8),
                    Wrap(
                      spacing: 6,
                      runSpacing: 4,
                      children: [
                        _miniChip(o.prePaid ? 'Online' : 'Při předání'),
                        if (o.prePaid && o.tip > 0)
                          _miniChip('Dýško ${o.tip.toStringAsFixed(0)} Kč'),
                        if (!o.prePaid && o.deliveryFee > 0)
                          _miniChip(
                              'Doprava ${o.deliveryFee.toStringAsFixed(0)} Kč'),
                      ],
                    ),
                  ],
                ),
              ),
              const SizedBox(width: 8),
              Column(
                crossAxisAlignment: CrossAxisAlignment.end,
                children: [
                  Text('${total.toStringAsFixed(0)} Kč',
                      style: const TextStyle(
                          fontSize: 18, fontWeight: FontWeight.w800)),
                  const SizedBox(height: 6),
                  Row(
                    mainAxisSize: MainAxisSize.min,
                    children: [
                      IconButton(
                        icon: const Icon(Icons.edit_outlined, size: 20),
                        tooltip: 'Upravit',
                        onPressed: () => _editOrder(o),
                      ),
                      IconButton.filled(
                        icon: const Icon(Icons.navigation_outlined, size: 20),
                        tooltip: 'Navigovat',
                        onPressed: () => _openDelivery(o),
                        style: IconButton.styleFrom(
                          fixedSize: const Size(44, 44),
                          shape: RoundedRectangleBorder(
                              borderRadius: BorderRadius.circular(14)),
                        ),
                      ),
                    ],
                  ),
                ],
              ),
            ],
          ),
        ),
      ),
    );
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
      bool verified = false;

      // Uložené místo s ověřenou (přesně nalezenou) polohou použijeme rovnou -
      // žádný síťový dotaz navíc. Neověřené (a všechny starší) se dohledají
      // znovu, a tak se špatně uložené polohy samy opraví.
      final wanted = _normAddr(address);
      SavedPlace? trusted;
      for (final sp in _savedPlaces) {
        if (sp.verified && _normAddr(sp.address) == wanted) {
          trusted = sp;
          break;
        }
      }
      if (trusted != null) {
        lat = trusted.lat;
        lon = trusted.lon;
        verified = true;
      } else {
        GeocodeResult? result;
        bool offlineFallback = false;
        try {
          result = await _geocodeInChlumec(address);
        } catch (e) {
          // bez internetu: použij starší uloženou polohu, když nějaká je
          for (final sp in _savedPlaces) {
            if (_normAddr(sp.address) == wanted) {
              result = GeocodeResult(sp.lat, sp.lon, 0, isPrecise: true);
              offlineFallback = true;
              break;
            }
          }
          if (result == null) rethrow;
        }
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
                'Adresa je ${result!.distanceKm.toStringAsFixed(1)} km od Chlumce — mimo rozsah 20 km.';
            _saving = false;
          });
          return;
        }
        if (!result.isPrecise) {
          final ok =
              await _confirmImpreciseAddress(context, found: result.label);
          if (!ok) {
            setState(() => _saving = false);
            return;
          }
        }
        lat = result.lat;
        lon = result.lon;
        verified = result.isPrecise && !offlineFallback;
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
        verified: verified,
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
        _autoPhone = null;
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
          askHandTip: _askHandTip,
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
    // úprava mohla opravit uloženou polohu místa -> načíst znovu
    await _loadSavedPlaces();
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

  @override
  Widget build(BuildContext context) {
    final cs = Theme.of(context).colorScheme;
    final knownPhones = _phonesForAddress(_addressController.text);
    final tipSummary = _tipSummaryForPhone(_phoneController.text);
    return Scaffold(
      appBar: AppBar(
        automaticallyImplyLeading: false,
        leadingWidth: 62,
        leading: Align(
          alignment: Alignment.centerLeft,
          child: _barButton(Icons.receipt_long_outlined, 'Vyúčtování směny',
              () async {
            await Navigator.push(
              context,
              MaterialPageRoute(builder: (_) => const ShiftSettlementScreen()),
            );
          }),
        ),
        actions: [
          _barButton(Icons.settings_outlined, 'Nastavení', () async {
            final changed = await Navigator.push<bool>(
              context,
              MaterialPageRoute(
                builder: (_) => SettingsScreen(
                  trackCashCardTips: _trackCashCardTips ?? false,
                ),
              ),
            );
            if (changed == true) _loadSettings();
          }),
          _barButton(Icons.bar_chart, 'Statistiky', () async {
            await Navigator.push(
              context,
              MaterialPageRoute(builder: (_) => const StatsScreen()),
            );
            _loadOrders();
          }),
          const SizedBox(width: 12),
        ],
      ),
      body: _loading
          ? const Center(child: CircularProgressIndicator())
          : ListView(
              padding: const EdgeInsets.fromLTRB(16, 4, 16, 24),
              children: [
                _todayStrip(cs),
                _sectionLabel('Nová objednávka'),
                Card(
                  child: Padding(
                    padding: const EdgeInsets.all(14),
                    child: Column(
                      crossAxisAlignment: CrossAxisAlignment.stretch,
                      children: [
                        TextField(
                          controller: _addressController,
                          decoration: InputDecoration(
                            labelText: 'Adresa',
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
                              color: cs.surfaceContainerHighest,
                              border: Border.all(color: cs.outlineVariant),
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
                                            _addressSuggestions = [];
                                            // nejnovější číslo z téhle adresy
                                            final known =
                                                _phonesForAddress(p.address);
                                            final phone = known.isNotEmpty
                                                ? known.first.phone
                                                : p.phone;
                                            if (phone.isNotEmpty) {
                                              _phoneController.text = phone;
                                              _autoPhone = phone;
                                            }
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
                            prefixIcon: Icon(Icons.label_outline),
                            border: OutlineInputBorder(),
                          ),
                        ),
                        const SizedBox(height: 10),
                        TextField(
                          controller: _phoneController,
                          keyboardType: TextInputType.phone,
                          inputFormatters: [_PhoneNumberFormatter()],
                          decoration: InputDecoration(
                            labelText: 'Telefon zákazníka',
                            prefixIcon: const Icon(Icons.phone_outlined),
                            border: const OutlineInputBorder(),
                            suffixIcon: knownPhones.isEmpty
                                ? null
                                : PopupMenuButton<String>(
                                    icon: const Icon(Icons.arrow_drop_down),
                                    tooltip: 'Čísla z téhle adresy',
                                    onSelected: (v) {
                                      setState(() {
                                        _phoneController.text = v;
                                        _autoPhone = null;
                                      });
                                    },
                                    itemBuilder: (ctx) => [
                                      for (final u in knownPhones)
                                        PopupMenuItem<String>(
                                          value: u.phone,
                                          child: Text(
                                            u.count > 0
                                                ? '${u.phone}  ·  ${u.count}×  ·  ${_fmtShortDate(u.lastUsed)}'
                                                : u.phone,
                                          ),
                                        ),
                                    ],
                                  ),
                          ),
                        ),
                        if (tipSummary != null)
                          _buildTipHistory(context, tipSummary),
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
                _sectionLabel('Čeká na doručení · ${_pending.length}'),
                if (_pending.isEmpty)
                  const Padding(
                    padding: EdgeInsets.symmetric(vertical: 24),
                    child: Center(
                      child: Text('Zatím žádné čekající objednávky.',
                          style: TextStyle(color: Colors.grey)),
                    ),
                  ),
                ..._pending.map(_orderCard),
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
                                    if (o.handTip > 0)
                                      Chip(
                                        visualDensity: VisualDensity.compact,
                                        label: Text(
                                            'Na ruku ${o.handTip.toStringAsFixed(0)} Kč'),
                                      ),
                                    Chip(
                                      visualDensity: VisualDensity.compact,
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
                                            ? cs.onPrimary
                                            : cs.onSurfaceVariant,
                                      ),
                                      backgroundColor: o.bossDelivered
                                          ? cs.primary
                                          : null,
                                      label: Text(
                                        'Jel šéf',
                                        style: TextStyle(
                                          color: o.bossDelivered
                                              ? cs.onPrimary
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
                                              ? cs.onPrimary
                                              : cs.onSurfaceVariant,
                                        ),
                                        backgroundColor: o.paidByCard
                                            ? cs.primary
                                            : null,
                                        label: Text(
                                          o.paidByCard ? 'Kartou' : 'Hotově',
                                          style: TextStyle(
                                            color: o.paidByCard
                                                ? cs.onPrimary
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

// ===================== KILOMETRY =====================
// Kolik km jsem s rozvozem ujel. Počítá se jízda po silnici (stejný server
// jako navigace) a PO JÍZDÁCH, ne po objednávkách:
//   základna -> zákazník -> (další zákazník) -> zpět na základnu.
// Když vezeš dvě objednávky najednou (Nepolisy a pak Zábědov), počítá se
// Nepolisy -> Zábědov a zpátky na základnu jedeš až ze Zábědova.
// Jízda "navazuje", když jsi navigaci k další objednávce spustil u předchozího
// zákazníka, a ne u základny. U starších objednávek (před touhle funkcí) to
// appka odhadne podle časů doručení - takové jsou ve statistikách označené ~.

LatLng _baseFromSettings(Map<String, dynamic> s) {
  final lat = (s['baseLat'] as num?)?.toDouble();
  final lon = (s['baseLon'] as num?)?.toDouble();
  if (lat == null || lon == null) return _chlumecCenter;
  return LatLng(lat, lon);
}

bool _sameDay(DateTime a, DateTime b) =>
    a.year == b.year && a.month == b.month && a.day == b.day;

class _RouteReq {
  final String key;
  final LatLng from;
  final LatLng to;
  final String orderId;
  _RouteReq(this.key, this.from, this.to, this.orderId);
}

class _TripInfo {
  final int mode; // 0 = nevím, 1 = jízda ze základny, 2 = navazuje
  final String? prevId;
  const _TripInfo(this.mode, this.prevId);
}

class KmReport {
  final Map<String, double> kmByOrder; // id objednávky -> km (jen co jsem vezl já)
  final Set<String> estimated; // objednávky, kde je číslo jen odhad
  final List<_RouteReq> missing; // trasy, které ještě nemáme z mapy
  KmReport(this.kmByOrder, this.estimated, this.missing);
}

class KmService {
  static const _cacheKey = 'rozvozka_routekm_v1';
  static const double _roadFactor = 1.3; // odhad: silnice je ~1,3x vzdušná čára
  static Future<void> _lock = Future<void>.value();

  static String keyFor(LatLng a, LatLng b) =>
      '${a.latitude.toStringAsFixed(4)},${a.longitude.toStringAsFixed(4)}>'
      '${b.latitude.toStringAsFixed(4)},${b.longitude.toStringAsFixed(4)}';

  static double _haversineKm(LatLng a, LatLng b) =>
      Geolocator.distanceBetween(
          a.latitude, a.longitude, b.latitude, b.longitude) /
      1000;

  static Future<Map<String, double>> loadCache() async {
    final prefs = await SharedPreferences.getInstance();
    final raw = prefs.getString(_cacheKey);
    if (raw == null || raw.isEmpty) return {};
    try {
      final m = json.decode(raw) as Map<String, dynamic>;
      return m.map((k, v) => MapEntry(k, (v as num).toDouble()));
    } catch (_) {
      return {};
    }
  }

  // Zápisy do cache se řadí za sebe, ať si souběžné dotazy nepřepíšou data.
  static Future<void> _saveCacheEntry(String key, double km) async {
    final previous = _lock;
    final done = Completer<void>();
    _lock = done.future;
    try {
      await previous;
      final cache = await loadCache();
      cache[key] = km;
      final prefs = await SharedPreferences.getInstance();
      await prefs.setString(_cacheKey, json.encode(cache));
    } finally {
      done.complete();
    }
  }

  // Silniční vzdálenost z OSRM (stejný server, který používá navigace).
  static Future<double?> fetchRoadKm(LatLng a, LatLng b) async {
    try {
      final url = Uri.parse(
          'https://router.project-osrm.org/route/v1/driving/'
          '${a.longitude},${a.latitude};${b.longitude},${b.latitude}'
          '?overview=false');
      final res = await http.get(url).timeout(const Duration(seconds: 10));
      if (res.statusCode != 200) return null;
      final data = json.decode(res.body);
      final routes = data['routes'];
      if (routes is List && routes.isNotEmpty) {
        final d = routes[0]['distance'];
        if (d is num) return d.toDouble() / 1000;
      }
    } catch (_) {}
    return null;
  }

  // Dopočítá chybějící trasy jednu po druhé (veřejný server nezatěžujeme víc
  // než cca 1 dotaz za vteřinu). Vrátí počet úspěšně doplněných tras.
  static Future<int> fillMissing(
    List<_RouteReq> missing, {
    bool Function()? shouldStop,
    void Function(int done, int total)? onProgress,
  }) async {
    final seen = <String>{};
    final todo = <_RouteReq>[];
    for (final r in missing) {
      if (seen.add(r.key)) todo.add(r);
    }
    int ok = 0;
    int fails = 0;
    int processed = 0;
    for (final r in todo) {
      if (shouldStop != null && shouldStop()) break;
      final km = await fetchRoadKm(r.from, r.to);
      if (km != null) {
        await _saveCacheEntry(r.key, km);
        ok++;
        fails = 0;
      } else {
        fails++;
        if (fails >= 3) break; // nejspíš nejsme online, nemá smysl pokračovat
      }
      processed++;
      if (onProgress != null) onProgress(processed, todo.length);
      await Future<void>.delayed(const Duration(milliseconds: 1100));
    }
    return ok;
  }

  // Po doručení: na pozadí dopočítá trasy právě dokončené objednávky.
  static Future<void> warmUp(String orderId) async {
    try {
      final orders = await OrdersStore.load();
      final settings = await AppSettingsStore.load();
      final cache = await loadCache();
      final report = compute(orders, _baseFromSettings(settings), cache);
      final mine = report.missing.where((r) => r.orderId == orderId).toList();
      if (mine.isEmpty) return;
      await fillMissing(mine);
    } catch (_) {}
  }

  // Při doručení: navazuje tahle objednávka na předchozí, nebo jsem jel ze základny?
  static _TripInfo classifyTrip({
    required List<DeliveryOrder> orders,
    required String orderId,
    required DateTime startedAt,
    required LatLng? startPos,
    required LatLng base,
  }) {
    DeliveryOrder? prev;
    for (final o in orders) {
      if (o.id == orderId || !o.done || o.completedAt == null) continue;
      if (o.bossDelivered) continue;
      if (o.completedAt!.isAfter(startedAt.add(const Duration(minutes: 2)))) {
        continue;
      }
      if (startedAt.difference(o.completedAt!) > const Duration(minutes: 40)) {
        continue;
      }
      if (prev == null || o.completedAt!.isAfter(prev.completedAt!)) prev = o;
    }
    if (prev == null) return const _TripInfo(1, null);
    if (startPos == null) return const _TripInfo(0, null);
    final dPrev = _haversineKm(startPos, LatLng(prev.lat, prev.lon));
    final dBase = _haversineKm(startPos, base);
    if (dPrev <= dBase) return _TripInfo(2, prev.id);
    return const _TripInfo(1, null);
  }

  // Starší objednávky (bez údajů z navigace): navazuje B na A? Porovná, jestli
  // čas mezi doručeními sedí spíš na "jel jsem rovnou" nebo "vrátil jsem se".
  static bool _looksChained(DeliveryOrder prev, DeliveryOrder o, LatLng base) {
    final gapMin =
        o.completedAt!.difference(prev.completedAt!).inSeconds / 60.0;
    if (gapMin > 60) return false;
    final a = LatLng(prev.lat, prev.lon);
    final b = LatLng(o.lat, o.lon);
    final dAB = _haversineKm(a, b) * _roadFactor;
    final dA0 = _haversineKm(a, base) * _roadFactor;
    final d0B = _haversineKm(base, b) * _roadFactor;
    const speed = 40.0; // km/h, průměr po městě a okolí
    final expectedChain = dAB / speed * 60 + 4; // jízda + předání
    final expectedReturn = (dA0 + d0B) / speed * 60 + 8; // návrat + naložení + jízda
    return (gapMin - expectedChain).abs() < (gapMin - expectedReturn).abs();
  }

  // Spočítá km za každou objednávku, kterou jsem vezl já (ne šéf).
  static KmReport compute(
      List<DeliveryOrder> orders, LatLng base, Map<String, double> cache) {
    final ds = orders
        .where((o) => o.done && o.completedAt != null && !o.bossDelivered)
        .toList()
      ..sort((a, b) => a.completedAt!.compareTo(b.completedAt!));
    final byId = <String, DeliveryOrder>{for (final o in ds) o.id: o};
    final kmByOrder = <String, double>{};
    final estimated = <String>{};
    final missing = <_RouteReq>[];

    // 1) na kterou objednávku která navazuje
    final prevOf = <String, DeliveryOrder?>{};
    final hasSuccessor = <String>{};
    for (int i = 0; i < ds.length; i++) {
      final o = ds[i];
      DeliveryOrder? prev;
      if (o.tripMode == 2) {
        prev = o.chainPrev == null ? null : byId[o.chainPrev!];
      } else if (o.tripMode == 0) {
        estimated.add(o.id); // hádá se podle časů
        if (i > 0 && _sameDay(ds[i - 1].completedAt!, o.completedAt!)) {
          if (_looksChained(ds[i - 1], o, base)) prev = ds[i - 1];
        }
      }
      prevOf[o.id] = prev;
      if (prev != null) hasSuccessor.add(prev.id);
    }

    // 2) vzdálenosti úseků
    double leg(LatLng a, LatLng b, String orderId) {
      if (_haversineKm(a, b) < 0.03) return 0;
      final key = keyFor(a, b);
      final cached = cache[key];
      if (cached != null) return cached;
      missing.add(_RouteReq(key, a, b, orderId));
      estimated.add(orderId);
      return _haversineKm(a, b) * _roadFactor;
    }

    for (final o in ds) {
      final dest = LatLng(o.lat, o.lon);
      final prev = prevOf[o.id];
      double km = prev != null
          ? leg(LatLng(prev.lat, prev.lon), dest, o.id)
          : leg(base, dest, o.id);
      // poslední objednávka jízdy: ještě cesta zpátky na základnu
      if (!hasSuccessor.contains(o.id)) {
        km += leg(dest, base, o.id);
      }
      kmByOrder[o.id] = km;
    }
    return KmReport(kmByOrder, estimated, missing);
  }
}

String _fmtKm(double km) => '${km.toStringAsFixed(1).replaceAll('.', ',')} km';

class _DoneDialogResult {
  final double collected;
  final bool paidByCard;
  final double handTip;
  const _DoneDialogResult(this.collected, this.paidByCard, this.handTip);
}

// Filtr, který z map světlé OpenStreetMap udělá tmavou (invertuje barvy
// a zpětně otočí odstíny, ať zůstane zelená zelená a voda modrá).
const ColorFilter _darkMapFilter = ColorFilter.matrix(<double>[
  0.574, -1.430, -0.144, 0, 255,
  -0.426, -0.430, -0.144, 0, 255,
  -0.426, -1.430, 0.856, 0, 255,
  0, 0, 0, 1, 0,
]);

// ===================== OBRAZOVKA DORUČENÍ (mapa pro 1 objednávku) =====================
class DeliveryScreen extends StatefulWidget {
  final DeliveryOrder order;
  final bool trackCashCardTips;
  final bool askHandTip;
  const DeliveryScreen(
      {super.key,
      required this.order,
      this.trackCashCardTips = false,
      this.askHandTip = true});

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
  LatLng? _startPos; // kde jsem byl, když jsem spustil navigaci (pro km)
  DateTime? _startedAt; // kdy jsem navigaci spustil

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
    _startedAt = DateTime.now();
    try {
      final pos = await Geolocator.getCurrentPosition(
        desiredAccuracy: LocationAccuracy.high,
        timeLimit: const Duration(seconds: 8),
      );
      setState(() => _myLocation = LatLng(pos.latitude, pos.longitude));
      _startPos = LatLng(pos.latitude, pos.longitude);
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

  // Dialog při "Doručeno": kolik jsem reálně vybral (když se sledují dýška
  // z hotovosti/karty) a dýško na ruku (hotově navíc, mimo terminál).
  Future<_DoneDialogResult?> _askDoneDetails({
    required bool needsCollect,
    required double expected,
  }) {
    final collectedController =
        TextEditingController(text: expected.toStringAsFixed(0));
    final handTipController = TextEditingController();
    bool localPaidByCard = false;
    return showDialog<_DoneDialogResult>(
      context: context,
      builder: (ctx) => StatefulBuilder(
        builder: (ctx, setDialogState) => AlertDialog(
          title: Text(needsCollect ? 'Kolik jste reálně vybral/a?' : 'Doručeno'),
          content: SingleChildScrollView(
            child: Column(
              mainAxisSize: MainAxisSize.min,
              crossAxisAlignment: CrossAxisAlignment.start,
              children: [
                if (needsCollect) ...[
                  Text('Mělo se vybrat: ${expected.toStringAsFixed(0)} Kč'),
                  const SizedBox(height: 12),
                  TextField(
                    controller: collectedController,
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
                  const SizedBox(height: 16),
                ],
                TextField(
                  controller: handTipController,
                  keyboardType:
                      const TextInputType.numberWithOptions(decimal: true),
                  decoration: InputDecoration(
                    labelText: 'Dýško na ruku (Kč)',
                    helperText: needsCollect
                        ? 'Hotově navíc, mimo částku na terminálu'
                        : 'Nepovinné - když ti dali dýško na místě',
                    border: const OutlineInputBorder(),
                  ),
                ),
                const SizedBox(height: 8),
                Wrap(
                  spacing: 8,
                  children: [
                    for (final v in const [10, 20, 50, 100])
                      ActionChip(
                        label: Text('$v'),
                        onPressed: () => setDialogState(
                            () => handTipController.text = '$v'),
                      ),
                  ],
                ),
              ],
            ),
          ),
          actions: [
            TextButton(
              onPressed: () => Navigator.pop(ctx),
              child: const Text('Zrušit'),
            ),
            FilledButton(
              onPressed: () {
                final collected = double.tryParse(
                        collectedController.text.trim().replaceAll(',', '.')) ??
                    expected;
                final tip = double.tryParse(
                        handTipController.text.trim().replaceAll(',', '.')) ??
                    0;
                Navigator.pop(
                    ctx, _DoneDialogResult(collected, localPaidByCard, tip));
              },
              child: const Text('Potvrdit'),
            ),
          ],
        ),
      ),
    );
  }

  Future<void> _markDone() async {
    double cashCardTip = 0;
    double handTip = 0;
    bool paidByCard = false;
    final needsCollect = widget.trackCashCardTips && !widget.order.prePaid;

    if (needsCollect || widget.askHandTip) {
      final expected = widget.order.amount + widget.order.deliveryFee;
      final result =
          await _askDoneDetails(needsCollect: needsCollect, expected: expected);
      if (result == null) return; // uživatel zrušil, nedokončujeme
      if (needsCollect) {
        cashCardTip = result.collected - expected;
        paidByCard = result.paidByCard;
      }
      handTip = result.handTip;
    }

    final orders = await OrdersStore.load();
    final idx = orders.indexWhere((o) => o.id == widget.order.id);
    if (idx != -1) {
      final settings = await AppSettingsStore.load();
      final startedAt = _startedAt ?? DateTime.now();
      final trip = KmService.classifyTrip(
        orders: orders,
        orderId: widget.order.id,
        startedAt: startedAt,
        startPos: _startPos,
        base: _baseFromSettings(settings),
      );
      final updated = orders[idx].copyWith(
        cashCardTip: cashCardTip,
        paidByCard: paidByCard,
        handTip: handTip,
        tripMode: trip.mode,
        chainPrev: trip.prevId,
        startLat: _startPos?.latitude,
        startLon: _startPos?.longitude,
        startedAt: startedAt,
      );
      updated.done = true;
      updated.completedAt = DateTime.now();
      orders[idx] = updated;
      await OrdersStore.save(orders);
      // vzdálenosti pro počítání kilometrů se dopočítají na pozadí
      unawaited(KmService.warmUp(widget.order.id));
    }
    if (mounted) Navigator.pop(context);
  }

  Widget _buildTileLayer(bool dark) {
    final layer = TileLayer(
      urlTemplate: 'https://tile.openstreetmap.org/{z}/{x}/{y}.png',
      userAgentPackageName: 'com.example.rozvozka',
    );
    if (!dark) return layer;
    return ColorFiltered(colorFilter: _darkMapFilter, child: layer);
  }

  @override
  Widget build(BuildContext context) {
    final o = widget.order;
    final cs = Theme.of(context).colorScheme;
    final isDark = Theme.of(context).brightness == Brightness.dark;
    return Scaffold(
      appBar: AppBar(
        title: Text(o.address, overflow: TextOverflow.ellipsis),
      ),
      body: Column(
        children: [
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
                    _buildTileLayer(isDark),
                    if (_routePoints.isNotEmpty)
                      PolylineLayer(polylines: [
                        Polyline(
                            points: _displayRoutePoints.isNotEmpty
                                ? _displayRoutePoints
                                : _routePoints,
                            strokeWidth: 6,
                            color: AppTheme.routeColor(
                                isDark ? Brightness.dark : Brightness.light)),
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
                    decoration: BoxDecoration(
                      color: cs.surface,
                      shape: BoxShape.circle,
                      boxShadow: const [
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
                    backgroundColor: _followMe ? cs.primary : cs.surface,
                    onPressed: () {
                      setState(() => _followMe = true);
                      _animateCameraTo(
                          _myLocation, _heading != null ? -_heading! : 0);
                    },
                    child: Icon(Icons.my_location,
                        color: _followMe ? cs.onPrimary : cs.onSurface),
                  ),
                ),
              ],
            ),
          ),
          // Bílá spodní lišta ve stylu navigace (příjezd / min / km) + tlačítka
          Container(
            decoration: BoxDecoration(
              color: cs.surface,
              borderRadius:
                  const BorderRadius.vertical(top: Radius.circular(28)),
              boxShadow: const [
                BoxShadow(color: Colors.black26, blurRadius: 16, offset: Offset(0, -4)),
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
                      color: cs.outlineVariant,
                      borderRadius: BorderRadius.circular(2),
                    ),
                  ),
                  const SizedBox(height: 12),
                  Padding(
                    padding: const EdgeInsets.symmetric(horizontal: 20),
                    child: Row(
                      crossAxisAlignment: CrossAxisAlignment.start,
                      children: [
                        Expanded(
                          child: Column(
                            crossAxisAlignment: CrossAxisAlignment.start,
                            children: [
                              Text('DORUČUJI',
                                  style: TextStyle(
                                      fontSize: 12,
                                      fontWeight: FontWeight.w700,
                                      letterSpacing: 0.6,
                                      color: cs.onSurfaceVariant)),
                              Text(o.address,
                                  maxLines: 2,
                                  overflow: TextOverflow.ellipsis,
                                  style: const TextStyle(
                                      fontSize: 22,
                                      fontWeight: FontWeight.w800,
                                      letterSpacing: -0.4)),
                              Text(o.phone,
                                  style: TextStyle(
                                      fontSize: 14,
                                      color: cs.onSurfaceVariant)),
                            ],
                          ),
                        ),
                        const SizedBox(width: 12),
                        Column(
                          crossAxisAlignment: CrossAxisAlignment.end,
                          children: [
                            Text(
                              '${(o.prePaid ? o.amount : o.amount + o.deliveryFee).toStringAsFixed(0)} Kč',
                              style: const TextStyle(
                                  fontSize: 22, fontWeight: FontWeight.w800),
                            ),
                            Text(
                              o.prePaid
                                  ? 'online${o.tip > 0 ? " · dýško ${o.tip.toStringAsFixed(0)}" : ""}'
                                  : 'vybrat na místě',
                              style: TextStyle(
                                  fontSize: 12, color: cs.onSurfaceVariant),
                            ),
                          ],
                        ),
                      ],
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
                        SizedBox(
                          width: 56,
                          height: 56,
                          child: OutlinedButton(
                            onPressed: _callCustomer,
                            style: OutlinedButton.styleFrom(
                              padding: EdgeInsets.zero,
                              minimumSize: const Size(56, 56),
                              shape: RoundedRectangleBorder(
                                  borderRadius: BorderRadius.circular(18)),
                            ),
                            child: const Icon(Icons.call),
                          ),
                        ),
                        const SizedBox(width: 10),
                        Expanded(
                          child: SizedBox(
                            height: 56,
                            child: FilledButton.icon(
                              onPressed: _markDone,
                              icon: const Icon(Icons.check),
                              label: const Text('Doručeno',
                                  style: TextStyle(fontSize: 18)),
                              style: FilledButton.styleFrom(
                                shape: RoundedRectangleBorder(
                                    borderRadius: BorderRadius.circular(18)),
                              ),
                            ),
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
    final cs = Theme.of(context).colorScheme;
    final dark = Theme.of(context).brightness == Brightness.dark;
    final fg = dark ? cs.onPrimaryContainer : Colors.white;
    return Container(
      width: double.infinity,
      padding: const EdgeInsets.fromLTRB(18, 14, 18, 16),
      decoration: BoxDecoration(
        color: dark ? cs.primaryContainer : cs.primary,
        boxShadow: const [
          BoxShadow(color: Colors.black26, blurRadius: 8, offset: Offset(0, 3)),
        ],
      ),
      child: Row(
        crossAxisAlignment: CrossAxisAlignment.center,
        children: [
          Icon(_maneuverIcon(step), color: fg, size: 46),
          const SizedBox(width: 16),
          Expanded(
            child: Column(
              crossAxisAlignment: CrossAxisAlignment.start,
              children: [
                Text(_formatDistance(distanceMeters),
                    style: TextStyle(
                        color: fg,
                        fontSize: 32,
                        fontWeight: FontWeight.w800,
                        height: 1.05)),
                const SizedBox(height: 2),
                Text(_maneuverText(step),
                    style: TextStyle(
                        color: fg,
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

  // --- kilometry ---
  Map<String, double> _kmByOrder = {};
  Set<String> _kmEstimated = {};
  List<_RouteReq> _kmMissing = [];
  bool _baseSet = false;
  bool _fillingKm = false;
  bool _stopFill = false;
  String _fillStatus = '';

  // --- vlastní období ---
  DateTimeRange? _range;

  @override
  void initState() {
    super.initState();
    _load();
  }

  @override
  void dispose() {
    _stopFill = true; // přeruší případné dopočítávání tras na pozadí
    super.dispose();
  }

  Future<void> _load() async {
    final orders = await OrdersStore.load();
    final settings = await AppSettingsStore.load();
    final cache = await KmService.loadCache();
    final report =
        KmService.compute(orders, _baseFromSettings(settings), cache);
    if (!mounted) return;
    setState(() {
      _orders = orders;
      _trackCashCardTips = settings['trackCashCardTips'] as bool? ?? false;
      _kmByOrder = report.kmByOrder;
      _kmEstimated = report.estimated;
      _kmMissing = report.missing;
      _baseSet = settings['baseLat'] != null && settings['baseLon'] != null;
      _loading = false;
    });
  }

  // Dopočítá chybějící trasy z mapy (jedna za ~1 vteřinu) a přepočítá km.
  Future<void> _fillKm() async {
    if (_fillingKm) return;
    setState(() {
      _fillingKm = true;
      _stopFill = false;
      _fillStatus = 'Dopočítávám trasy...';
    });
    final ok = await KmService.fillMissing(
      _kmMissing,
      shouldStop: () => _stopFill || !mounted,
      onProgress: (done, total) {
        if (mounted) {
          setState(() => _fillStatus = 'Dopočítávám trasy: $done z $total');
        }
      },
    );
    if (!mounted) return;
    await _load();
    if (!mounted) return;
    setState(() {
      _fillingKm = false;
      _fillStatus = ok == 0
          ? 'Nic se nepodařilo dopočítat - jsi online?'
          : 'Hotovo, doplněno $ok tras.';
    });
  }

  bool _isToday(DateTime d) {
    final now = DateTime.now();
    return d.year == now.year && d.month == now.month && d.day == now.day;
  }

  String _fmtDay(DateTime d) => '${d.day}. ${d.month}. ${d.year}';

  bool _inRange(DateTime d) {
    final r = _range;
    if (r == null) return false;
    final day = DateTime(d.year, d.month, d.day);
    return !day.isBefore(r.start) && !day.isAfter(r.end);
  }

  void _setRange(DateTime start, DateTime end) {
    setState(() {
      _range = DateTimeRange(
        start: DateTime(start.year, start.month, start.day),
        end: DateTime(end.year, end.month, end.day),
      );
    });
  }

  DateTime _todayDate() {
    final n = DateTime.now();
    return DateTime(n.year, n.month, n.day);
  }

  void _thisWeek() {
    final t = _todayDate();
    _setRange(DateTime(t.year, t.month, t.day - (t.weekday - 1)), t);
  }

  void _lastWeek() {
    final t = _todayDate();
    final monday = DateTime(t.year, t.month, t.day - (t.weekday - 1) - 7);
    _setRange(monday, DateTime(monday.year, monday.month, monday.day + 6));
  }

  void _thisMonth() {
    final t = _todayDate();
    _setRange(DateTime(t.year, t.month, 1), t);
  }

  void _lastDays(int n) {
    final t = _todayDate();
    _setRange(DateTime(t.year, t.month, t.day - (n - 1)), t);
  }

  Future<void> _pickRange() async {
    final t = _todayDate();
    final picked = await showDateRangePicker(
      context: context,
      firstDate: DateTime(2024, 1, 1),
      lastDate: t,
      initialDateRange: _range,
      helpText: 'Vyber období',
    );
    if (picked != null) _setRange(picked.start, picked.end);
  }

  String _kmText(_StatsAgg a) {
    final base = _fmtKm(a.km);
    return a.kmEstimated ? '~$base' : base;
  }

  List<Widget> _aggCards(_StatsAgg a) {
    return [
      _statCard('Doručené objednávky', '${a.count}'),
      _statCard('Celková tržba', '${a.revenue.toStringAsFixed(0)} Kč'),
      _statCard('Online platby', '${a.online.toStringAsFixed(0)} Kč'),
      _statCard('Dýšky z online plateb', '${a.onlineTips.toStringAsFixed(0)} Kč'),
      _statCard('Doprava', '${a.delivery.toStringAsFixed(0)} Kč'),
      _statCard('Počet online objednávek', '${a.onlineCount}'),
      if (_trackCashCardTips)
        _statCard('Dýška z hotovosti/karet',
            '${a.cashCardTips.toStringAsFixed(0)} Kč'),
      _statCard('Dýška na ruku', '${a.handTips.toStringAsFixed(0)} Kč'),
      _statCard('Najeté km', _kmText(a)),
    ];
  }

  static const List<String> _weekdays = [
    'po', 'út', 'st', 'čt', 'pá', 'so', 'ne'
  ];

  // Rozpis po dnech za vybrané období: v jaký den kolik objednávek / tržba / dýška / km.
  List<Widget> _dayRows(List<DeliveryOrder> orders) {
    final byDay = <DateTime, List<DeliveryOrder>>{};
    for (final o in orders) {
      final d = o.completedAt!;
      byDay.putIfAbsent(DateTime(d.year, d.month, d.day), () => []).add(o);
    }
    final days = byDay.keys.toList()..sort((a, b) => b.compareTo(a));
    final rows = <Widget>[];
    for (final day in days) {
      final a = _StatsAgg.of(byDay[day]!, _kmByOrder, _kmEstimated);
      final tips = byDay[day]!.fold<double>(0, (s, o) => s + o.totalTip);
      rows.add(const Divider(height: 1));
      rows.add(Padding(
        padding: const EdgeInsets.symmetric(vertical: 8),
        child: Column(
          crossAxisAlignment: CrossAxisAlignment.start,
          children: [
            Row(
              mainAxisAlignment: MainAxisAlignment.spaceBetween,
              children: [
                Text('${_weekdays[day.weekday - 1]} ${day.day}. ${day.month}.',
                    style: const TextStyle(fontWeight: FontWeight.bold)),
                Text('${a.revenue.toStringAsFixed(0)} Kč',
                    style: const TextStyle(fontWeight: FontWeight.bold)),
              ],
            ),
            const SizedBox(height: 2),
            Text(
              '${a.count} obj. · dýška ${tips.toStringAsFixed(0)} Kč · '
              'doprava ${a.delivery.toStringAsFixed(0)} Kč · ${_kmText(a)}',
              style: const TextStyle(fontSize: 12, color: Colors.grey),
            ),
          ],
        ),
      ));
    }
    return rows;
  }

  // Sloupcový graf tržby po dnech vybraného období (nejvyšší den = zvýrazněný).
  Widget _dayBars(List<DeliveryOrder> orders) {
    final r = _range;
    if (r == null) return const SizedBox.shrink();
    final cs = Theme.of(context).colorScheme;
    final days = <DateTime>[];
    var d = r.start;
    while (!d.isAfter(r.end) && days.length < 62) {
      days.add(d);
      d = DateTime(d.year, d.month, d.day + 1);
    }
    if (days.isEmpty) return const SizedBox.shrink();
    final sums = <double>[];
    for (final day in days) {
      double s = 0;
      for (final o in orders) {
        final c = o.completedAt!;
        if (c.year == day.year && c.month == day.month && c.day == day.day) {
          s += o.amount;
        }
      }
      sums.add(s);
    }
    final maxV = sums.fold<double>(0, (a, b) => b > a ? b : a);
    final showLabels = days.length <= 14;
    return SizedBox(
      height: 118,
      child: Row(
        crossAxisAlignment: CrossAxisAlignment.end,
        children: [
          for (int i = 0; i < days.length; i++)
            Expanded(
              child: Padding(
                padding: const EdgeInsets.symmetric(horizontal: 2),
                child: Column(
                  mainAxisAlignment: MainAxisAlignment.end,
                  children: [
                    Container(
                      height: maxV <= 0
                          ? 4
                          : (4 + 88 * (sums[i] / maxV)).clamp(4, 92).toDouble(),
                      decoration: BoxDecoration(
                        color: (maxV > 0 && sums[i] == maxV)
                            ? cs.primary
                            : cs.secondaryContainer,
                        borderRadius: BorderRadius.circular(6),
                      ),
                    ),
                    const SizedBox(height: 4),
                    SizedBox(
                      height: 14,
                      child: showLabels
                          ? Text(_weekdays[days[i].weekday - 1],
                              style: TextStyle(
                                  fontSize: 11,
                                  fontWeight: FontWeight.w700,
                                  color: cs.onSurfaceVariant))
                          : null,
                    ),
                  ],
                ),
              ),
            ),
        ],
      ),
    );
  }

  Widget _kmNotice(int missingUnique) {
    final cs = Theme.of(context).colorScheme;
    return Card(
      color: cs.tertiaryContainer,
      child: Padding(
        padding: const EdgeInsets.all(12),
        child: Column(
          crossAxisAlignment: CrossAxisAlignment.start,
          children: [
            if (!_baseSet)
              Text(
                'Základna (restaurace) není nastavená, kilometry se počítají '
                'od středu Chlumce. Nastav ji v Nastavení.',
                style: TextStyle(color: cs.onTertiaryContainer, fontSize: 13),
              ),
            if (missingUnique > 0) ...[
              if (!_baseSet) const SizedBox(height: 8),
              Text(
                'Pro přesné kilometry chybí $missingUnique tras z mapy '
                '(zatím jsou jen odhadem, označené ~). Dopočítání trvá zhruba '
                '${(missingUnique * 1.1 / 60).ceil()} min a musí být zapnutý internet; '
                'nech tuhle obrazovku otevřenou.',
                style: TextStyle(color: cs.onTertiaryContainer, fontSize: 13),
              ),
              const SizedBox(height: 8),
              Row(
                children: [
                  FilledButton(
                    onPressed: _fillingKm ? null : _fillKm,
                    child: Text(_fillingKm ? 'Počítám...' : 'Dopočítat km'),
                  ),
                  const SizedBox(width: 12),
                  Expanded(
                    child: Text(_fillStatus,
                        style: TextStyle(
                            color: cs.onTertiaryContainer, fontSize: 12)),
                  ),
                ],
              ),
            ] else if (_fillStatus.isNotEmpty)
              Text(_fillStatus,
                  style: TextStyle(color: cs.onTertiaryContainer, fontSize: 12)),
          ],
        ),
      ),
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

    final today = _StatsAgg.of(todayOrders, _kmByOrder, _kmEstimated);
    final total = _StatsAgg.of(doneOrders, _kmByOrder, _kmEstimated);

    final todayPendingRevenue =
        todayPending.fold<double>(0, (sum, o) => sum + o.amount);
    final todayAllCount = today.count + todayPending.length;
    final todayAllRevenue = today.revenue + todayPendingRevenue;

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
      final dayTips = dayOrders.fold<double>(0, (s, o) => s + o.totalTip);
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
      final orderTip = o.totalTip;
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

    // --- vlastní období ---
    final rangeOrders = _range == null
        ? <DeliveryOrder>[]
        : doneOrders.where((o) => _inRange(o.completedAt!)).toList();
    final rangeAgg = _StatsAgg.of(rangeOrders, _kmByOrder, _kmEstimated);
    final missingUnique = _kmMissing.map((r) => r.key).toSet().length;

    return Scaffold(
      appBar: AppBar(
        title: const Text('Statistiky'),
      ),
      body: _loading
          ? const Center(child: CircularProgressIndicator())
          : ListView(
              padding: const EdgeInsets.all(16),
              children: [
                if (!_baseSet || missingUnique > 0 || _fillStatus.isNotEmpty)
                  _kmNotice(missingUnique),
                const Text('Dnes',
                    style:
                        TextStyle(fontWeight: FontWeight.bold, fontSize: 18)),
                const SizedBox(height: 8),
                ..._aggCards(today),
                _statCard('Celkem dnes (s nevyřízenými)',
                    '$todayAllCount obj. · ${todayAllRevenue.toStringAsFixed(0)} Kč'),
                const SizedBox(height: 20),
                Card(
                  color: Colors.amber.withAlpha(40),
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
                  child: Padding(
                    padding: const EdgeInsets.all(14),
                    child: Column(
                      crossAxisAlignment: CrossAxisAlignment.start,
                      children: [
                        Row(
                          children: const [
                            Icon(Icons.date_range),
                            SizedBox(width: 8),
                            Text('Vlastní období',
                                style: TextStyle(
                                    fontWeight: FontWeight.bold, fontSize: 16)),
                          ],
                        ),
                        const SizedBox(height: 10),
                        Wrap(
                          spacing: 8,
                          runSpacing: 4,
                          children: [
                            ActionChip(
                                label: const Text('Tento týden'),
                                onPressed: _thisWeek),
                            ActionChip(
                                label: const Text('Minulý týden'),
                                onPressed: _lastWeek),
                            ActionChip(
                                label: const Text('Tento měsíc'),
                                onPressed: _thisMonth),
                            ActionChip(
                                label: const Text('Posledních 7 dní'),
                                onPressed: () => _lastDays(7)),
                            ActionChip(
                                label: const Text('Posledních 30 dní'),
                                onPressed: () => _lastDays(30)),
                            ActionChip(
                              avatar: const Icon(Icons.edit_calendar, size: 18),
                              label: const Text('Vybrat od - do'),
                              onPressed: _pickRange,
                            ),
                          ],
                        ),
                        const SizedBox(height: 12),
                        if (_range == null)
                          const Text(
                            'Vyber období (třeba týden nebo jen 4 dny) a uvidíš '
                            'stejné údaje jen za něj, i s rozpisem po dnech.',
                            style: TextStyle(color: Colors.grey, fontSize: 13),
                          )
                        else ...[
                          Text(
                            '${_fmtDay(_range!.start)} – ${_fmtDay(_range!.end)}',
                            style: const TextStyle(
                                fontWeight: FontWeight.bold, fontSize: 15),
                          ),
                          const SizedBox(height: 8),
                          Text(
                            '${_fmtThousands(rangeAgg.revenue)} Kč',
                            style: TextStyle(
                                fontSize: 40,
                                fontWeight: FontWeight.w800,
                                letterSpacing: -1.5,
                                color: Theme.of(context).colorScheme.primary),
                          ),
                          const SizedBox(height: 8),
                          _dayBars(rangeOrders),
                          const SizedBox(height: 12),
                          ..._aggCards(rangeAgg),
                          const SizedBox(height: 8),
                          const Text('Po dnech',
                              style: TextStyle(
                                  fontWeight: FontWeight.bold, fontSize: 15)),
                          if (rangeOrders.isEmpty)
                            const Padding(
                              padding: EdgeInsets.symmetric(vertical: 8),
                              child: Text('V tomhle období nic nedoručeno.',
                                  style: TextStyle(color: Colors.grey)),
                            )
                          else
                            ..._dayRows(rangeOrders),
                        ],
                      ],
                    ),
                  ),
                ),
                const SizedBox(height: 12),
                Card(
                  clipBehavior: Clip.antiAlias,
                  child: ExpansionTile(
                    leading: const Icon(Icons.calendar_month_outlined),
                    title: const Text('Od začátku',
                        style: TextStyle(fontWeight: FontWeight.bold)),
                    children: [
                      Padding(
                        padding: const EdgeInsets.fromLTRB(12, 0, 12, 12),
                        child: Column(children: _aggCards(total)),
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

class _StatsAgg {
  int count = 0;
  int onlineCount = 0;
  double revenue = 0;
  double online = 0;
  double onlineTips = 0;
  double delivery = 0;
  double cashCardTips = 0;
  double handTips = 0;
  double km = 0;
  bool kmEstimated = false;

  static _StatsAgg of(List<DeliveryOrder> orders, Map<String, double> kmByOrder,
      Set<String> estimated) {
    final a = _StatsAgg();
    for (final o in orders) {
      a.count++;
      a.revenue += o.amount;
      if (o.prePaid) {
        a.online += o.amount;
        a.onlineCount++;
        a.onlineTips += o.tip;
      } else {
        // doprava z objednávek, které vezl šéf, se do "mojí" dopravy nepočítá
        if (!o.bossDelivered) a.delivery += o.deliveryFee;
        a.cashCardTips += o.cashCardTip;
      }
      a.handTips += o.handTip;
      final k = kmByOrder[o.id];
      if (k != null) {
        a.km += k;
        if (estimated.contains(o.id)) a.kmEstimated = true;
      }
    }
    return a;
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
  bool _askHandTip = true;
  ThemeMode _themeMode = appThemeMode.value;

  @override
  void initState() {
    super.initState();
    _trackCashCardTips = widget.trackCashCardTips;
    _loadMore();
  }

  Future<void> _loadMore() async {
    final settings = await AppSettingsStore.load();
    if (!mounted) return;
    setState(() {
      _askHandTip = settings['askHandTip'] as bool? ?? true;
    });
  }

  Future<void> _setSetting(String key, Object value) async {
    final settings = await AppSettingsStore.load();
    settings[key] = value;
    await AppSettingsStore.save(settings);
  }

  Future<void> _save(bool value) async {
    setState(() => _trackCashCardTips = value);
    await _setSetting('trackCashCardTips', value);
  }

  Future<void> _saveAskHandTip(bool value) async {
    setState(() => _askHandTip = value);
    await _setSetting('askHandTip', value);
  }

  Future<void> _saveTheme(ThemeMode mode) async {
    setState(() => _themeMode = mode);
    appThemeMode.value = mode;
    await _setSetting('themeMode', _themeModeToString(mode));
  }

  Future<void> _savePalette(AppPalette pal) async {
    appPalette.value = pal;
    await _setSetting('palette', _paletteToString(pal));
  }

  Widget _paletteOption(AppPalette pal, bool selected) {
    final cs = Theme.of(context).colorScheme;
    final brightness = Theme.of(context).brightness;
    return Expanded(
      child: InkWell(
        borderRadius: BorderRadius.circular(16),
        onTap: () => _savePalette(pal),
        child: Container(
          padding: const EdgeInsets.symmetric(vertical: 12),
          decoration: BoxDecoration(
            borderRadius: BorderRadius.circular(16),
            border: Border.all(
              color: selected ? cs.primary : cs.outlineVariant,
              width: selected ? 2 : 1,
            ),
          ),
          child: Column(
            children: [
              CircleAvatar(
                radius: 16,
                backgroundColor: AppTheme.swatch(pal, brightness),
                child: selected
                    ? Icon(Icons.check, size: 18, color: cs.onPrimary)
                    : null,
              ),
              const SizedBox(height: 6),
              Text(_paletteName(pal),
                  style: TextStyle(
                      fontSize: 13,
                      fontWeight: selected ? FontWeight.w800 : FontWeight.w600)),
            ],
          ),
        ),
      ),
    );
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
          const Text('Vzhled',
              style: TextStyle(fontWeight: FontWeight.bold, fontSize: 16)),
          const SizedBox(height: 8),
          SegmentedButton<ThemeMode>(
            segments: const [
              ButtonSegment(
                  value: ThemeMode.light,
                  label: Text('Světlý'),
                  icon: Icon(Icons.light_mode_outlined)),
              ButtonSegment(
                  value: ThemeMode.dark,
                  label: Text('Tmavý'),
                  icon: Icon(Icons.dark_mode_outlined)),
              ButtonSegment(
                  value: ThemeMode.system,
                  label: Text('Auto'),
                  icon: Icon(Icons.phone_iphone)),
            ],
            selected: {_themeMode},
            onSelectionChanged: (s) => _saveTheme(s.first),
          ),
          const SizedBox(height: 4),
          const Text(
            'Auto = podle nastavení telefonu. Rychle přepnout jde i ikonou '
            'měsíce nahoře na hlavní obrazovce.',
            style: TextStyle(fontSize: 12, color: Colors.grey),
          ),
          const SizedBox(height: 16),
          const Text('Barva',
              style: TextStyle(fontWeight: FontWeight.bold, fontSize: 16)),
          const SizedBox(height: 8),
          ValueListenableBuilder<AppPalette>(
            valueListenable: appPalette,
            builder: (context, current, _) => Row(
              children: [
                for (final pal in AppPalette.values) ...[
                  _paletteOption(pal, pal == current),
                  if (pal != AppPalette.values.last) const SizedBox(width: 10),
                ],
              ],
            ),
          ),
          const SizedBox(height: 12),
          const Divider(),
          SwitchListTile(
            title: const Text('Počítat dýška i z hotovosti/karty'),
            subtitle: const Text(
                'Appka se při dokončení objednávky s platbou na místě '
                'zeptá, kolik jste reálně vybral/a. Rozdíl oproti ceně '
                'objednávky se počítá jako dýško ve statistikách.'),
            value: _trackCashCardTips,
            onChanged: _save,
          ),
          SwitchListTile(
            title: const Text('Ptát se na dýško na ruku'),
            subtitle: const Text(
                'Při "Doručeno" se appka zeptá na dýško, které ti dali na '
                'místě hotově navíc (u online objednávek i u karty). '
                'Když to vypneš, u online objednávek se neptá a dýško na ruku '
                'můžeš dopsat později v úpravě objednávky.'),
            value: _askHandTip,
            onChanged: _saveAskHandTip,
          ),
          const _BaseSection(),
          const _BackupSection(),
        ],
      ),
    );
  }
}

// ===================== ZÁKLADNA (odkud vyjíždíš) =====================
// Potřebuje ji počítání kilometrů: jízda začíná a končí na základně.
class _BaseSection extends StatefulWidget {
  const _BaseSection();

  @override
  State<_BaseSection> createState() => _BaseSectionState();
}

class _BaseSectionState extends State<_BaseSection> {
  final _addressController =
      TextEditingController(text: 'Zámecká, Chlumec nad Cidlinou');
  bool _isSet = false;
  bool _busy = false;
  String _label = '';
  String _status = '';

  @override
  void initState() {
    super.initState();
    _load();
  }

  @override
  void dispose() {
    _addressController.dispose();
    super.dispose();
  }

  Future<void> _load() async {
    final s = await AppSettingsStore.load();
    if (!mounted) return;
    setState(() {
      _isSet = s['baseLat'] != null && s['baseLon'] != null;
      _label = (s['baseLabel'] as String?) ?? '';
    });
  }

  Future<void> _store(double lat, double lon, String label) async {
    final s = await AppSettingsStore.load();
    s['baseLat'] = lat;
    s['baseLon'] = lon;
    s['baseLabel'] = label;
    await AppSettingsStore.save(s);
    if (!mounted) return;
    setState(() {
      _isSet = true;
      _label = label;
      _busy = false;
      _status = 'Základna uložená.';
    });
  }

  Future<void> _useMyLocation() async {
    setState(() {
      _busy = true;
      _status = 'Zjišťuju polohu...';
    });
    try {
      final pos = await Geolocator.getCurrentPosition(
        desiredAccuracy: LocationAccuracy.high,
        timeLimit: const Duration(seconds: 10),
      );
      await _store(pos.latitude, pos.longitude, 'Moje poloha při nastavení');
    } catch (e) {
      if (!mounted) return;
      setState(() {
        _busy = false;
        _status = 'Polohu se nepodařilo zjistit ($e).';
      });
    }
  }

  Future<void> _findAddress() async {
    final q = _addressController.text.trim();
    if (q.isEmpty) return;
    setState(() {
      _busy = true;
      _status = 'Hledám adresu...';
    });
    try {
      final r = await _geocodeInChlumec(q);
      if (r == null) {
        if (!mounted) return;
        setState(() {
          _busy = false;
          _status = 'Adresu se nepodařilo najít.';
        });
        return;
      }
      await _store(r.lat, r.lon, q);
    } catch (e) {
      if (!mounted) return;
      setState(() {
        _busy = false;
        _status = 'Hledání selhalo ($e).';
      });
    }
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
            'Základna (odkud vyjíždíš)',
            style: TextStyle(fontWeight: FontWeight.bold, fontSize: 16),
          ),
        ),
        const Text(
          'Podle základny se počítají kilometry: jízda začíná na základně a '
          'po poslední objednávce se počítá cesta zpátky. Nejpřesnější je '
          'nastavit ji, když stojíš u restaurace.',
          style: TextStyle(color: Colors.grey),
        ),
        const SizedBox(height: 8),
        Text(
          _isSet
              ? 'Nastaveno: ${_label.isEmpty ? 'vlastní poloha' : _label}'
              : 'Zatím nenastaveno (kilometry se počítají od středu Chlumce).',
          style: const TextStyle(fontWeight: FontWeight.w600),
        ),
        const SizedBox(height: 10),
        ElevatedButton.icon(
          onPressed: _busy ? null : _useMyLocation,
          icon: const Icon(Icons.my_location),
          label: const Text('Použít moji aktuální polohu'),
        ),
        const SizedBox(height: 10),
        Row(
          children: [
            Expanded(
              child: TextField(
                controller: _addressController,
                decoration: const InputDecoration(
                  labelText: 'Nebo adresa základny',
                  border: OutlineInputBorder(),
                  isDense: true,
                ),
              ),
            ),
            const SizedBox(width: 8),
            OutlinedButton(
              onPressed: _busy ? null : _findAddress,
              child: const Text('Najít'),
            ),
          ],
        ),
        if (_status.isNotEmpty)
          Padding(
            padding: const EdgeInsets.only(top: 8),
            child: Text(_status),
          ),
      ],
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
  double _todayHandTips = 0;
  double _todayBossAmount = 0;
  double _todayCardAmount = 0;

  final _stravenkyController = TextEditingController();
  final _platbyController = TextEditingController();

  List<DeliveryOrder> _orders = [];
  bool _exportingPdf = false;

  String _fmtDay(DateTime d) => '${d.day}. ${d.month}. ${d.year}';

  @override
  void initState() {
    super.initState();
    _load();
    for (final c in [_stravenkyController, _platbyController]) {
      c.addListener(() => setState(() {}));
    }
  }

  @override
  void dispose() {
    _stravenkyController.dispose();
    _platbyController.dispose();
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
    // dýška na ruku si řidič nechává, do vyúčtování nevstupují
    final handTips = todayOrders.fold<double>(0, (s, o) => s + o.handTip);
    // co vezl šéf - jen cena objednávky, bez dopravy (tu si nechává on na benzín)
    final bossAmount = todayOrders
        .where((o) => o.bossDelivered)
        .fold<double>(0, (s, o) => s + o.amount);
    // kolik se dnes reálně vybralo kartou (skutečně vybraná částka, ne jen
    // cena objednávky) - appka to ví sama z volby při "Doručeno"
    final cardAmount = todayOrders
        .where((o) => !o.prePaid && o.paidByCard)
        .fold<double>(
            0, (s, o) => s + o.amount + o.deliveryFee + o.cashCardTip);

    final saved = await ShiftSettlementStore.load();

    setState(() {
      _orders = orders;
      _trackCashCardTips = settings['trackCashCardTips'] as bool? ?? false;
      _todayRevenue = revenue;
      _todayOnline = online;
      _todayTips = tips;
      _todayDelivery = delivery;
      _todayHandTips = handTips;
      _todayBossAmount = bossAmount;
      _todayCardAmount = cardAmount;
      if (saved != null) {
        _stravenkyController.text = (saved['stravenky'] ?? '') as String;
        _platbyController.text = (saved['platby'] ?? '') as String;
      }
      _loading = false;
    });
  }

  // Sestaví PDF přesně ve stylu papírového rozpisu, co appka nahrazuje -
  // číslovaný seznam objednávek + vyhodnocení dne dole, stejný systém
  // sčítání/odečítání jako ve Vyúčtování směny.
  Future<void> _exportPdf() async {
    setState(() => _exportingPdf = true);
    try {
      await _persist(); // ať se do PDF dostanou právě zadané stravenky a platby
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

  double _num(TextEditingController c) =>
      double.tryParse(c.text.trim().replaceAll(',', '.')) ?? 0;

  Future<void> _persist() async {
    await ShiftSettlementStore.save({
      'stravenky': _stravenkyController.text.trim(),
      'platby': _platbyController.text.trim(),
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

    return Scaffold(
      appBar: AppBar(
        title: const Text('Vyúčtování směny'),
        actions: [
          IconButton(
            icon: _exportingPdf
                ? const SizedBox(
                    width: 20,
                    height: 20,
                    child: CircularProgressIndicator(strokeWidth: 2),
                  )
                : const Icon(Icons.picture_as_pdf_outlined),
            tooltip: 'Export do PDF pro šéfa',
            onPressed: _exportingPdf ? null : _exportPdf,
          ),
          const SizedBox(width: 8),
        ],
      ),
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
                        if (_todayHandTips > 0)
                          _readOnlyRow(
                              'Dýška na ruku (nechávám si)', _todayHandTips),
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
                      Text('Dát šéfovi',
                          style: TextStyle(
                              fontSize: 14,
                              color: Theme.of(context)
                                  .colorScheme
                                  .onPrimaryContainer)),
                      const SizedBox(height: 4),
                      Text('${result.toStringAsFixed(0)} Kč',
                          style: TextStyle(
                              fontSize: 34,
                              fontWeight: FontWeight.w800,
                              color: Theme.of(context)
                                  .colorScheme
                                  .onPrimaryContainer)),
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
