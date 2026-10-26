import 'package:firebase_core/firebase_core.dart';

// ===================== NASTAVENÍ FIREBASE =====================
// Sem vlož (nahraď) celý objekt firebaseConfig, který ti Firebase ukáže po
// přidání webové appky (Nastavení projektu -> Vaše aplikace -> Web).
// Stačí zkopírovat to, co je mezi složenými závorkami { ... }, tak jak to je.
// Dokud tu zůstane "VLOZ", sdílení polohy je vypnuté a appka se chová jako dřív.
const String _rawConfig = r'''
{
  apiKey: "VLOZ",
  authDomain: "VLOZ",
  projectId: "VLOZ",
  storageBucket: "VLOZ",
  messagingSenderId: "VLOZ",
  appId: "VLOZ"
}
''';

String _field(String name) {
  final m = RegExp('$name\\s*:\\s*["\']([^"\']*)["\']').firstMatch(_rawConfig);
  return m?.group(1) ?? '';
}

final FirebaseOptions kFirebaseOptions = FirebaseOptions(
  apiKey: _field('apiKey'),
  appId: _field('appId'),
  messagingSenderId: _field('messagingSenderId'),
  projectId: _field('projectId'),
  authDomain: _field('authDomain'),
  storageBucket: _field('storageBucket'),
);

bool get kFirebaseConfigured =>
    kFirebaseOptions.apiKey.isNotEmpty &&
    !kFirebaseOptions.apiKey.startsWith('VLOZ') &&
    kFirebaseOptions.projectId.isNotEmpty &&
    !kFirebaseOptions.projectId.startsWith('VLOZ');
