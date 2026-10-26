import 'package:firebase_core/firebase_core.dart';

// ===================== NASTAVENÍ FIREBASE ====================
// Hodnoty z Firebase konzole (projekt rozvozka-7aecc, webová appka).
const String _rawConfig = r'''
{
  apiKey: "AIzaSyCiTb7nUpQ-CIPkwwIApbD2D5HlV1rD-LA",
  authDomain: "rozvozka-7aecc.firebaseapp.com",
  projectId: "rozvozka-7aecc",
  storageBucket: "rozvozka-7aecc.firebasestorage.app",
  messagingSenderId: "112417914369",
  appId: "1:112417914369:web:9e2c6201c6186a50f38a00"
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
