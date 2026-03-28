import Mettapedia.Languages.MeTTa.Translation.HEPeTTaTranslateCore
import Mettapedia.Languages.MeTTa.Translation.HEPeTTaTranslateOperationalBridge
import Mettapedia.Languages.MeTTa.Translation.HEPeTTaTranslateValidatedRoundtrip

/-!
# Executable HE ↔ PeTTa Translator

Public import surface for the extracted translator modules:

- `HEPeTTaTranslateCore`: executable translators, optimizer, and early
  translation/pattern theorems
- `HEPeTTaTranslateValidatedRoundtrip`: validated stable-common and roundtrip
  theorems
- `HEPeTTaTranslateOperationalBridge`: sequential state/atomspace operational
  bridge theorems for the currently shared fragments
-/
