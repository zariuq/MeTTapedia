import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangControllerSource
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.BridgeEval

/-! The shared append operation retains its execution under the actor
library stack. Message occurrences and their order are preserved exactly.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorListOperations

open Mettapedia.GSLT.LanguageDef CettaWire
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Eval BridgeKit WireKit ErlangControllerSource

theorem append_returns {α : Type} (encode : α → Term) (state : State) (left right : List α) :
    PureReturns runtime [] state (apply "gslt:automata:append"
      [encoded (encodeList encode left), encoded (encodeList encode right)]) state
      (encoded (encodeList encode (left ++ right))) := by
  let returns := fun program => PureReturns program [] state (apply "gslt:automata:append"
    [encoded (encodeList encode left), encoded (encodeList encode right)]) state
    (encoded (encodeList encode (left ++ right)))
  have integer : returns IntegerWordLibrarySource.integerLibrary.runtime := by
    metta_lift IntegerWordLibrarySource.integer_checked ["left", "right"]
      (ProviderCacheExecution.list_append_returns encode state left right)
  have word : returns IntegerWordLibrarySource.runtime := by
    metta_lift IntegerWordLibrarySource.word_checked ["left", "right"] integer
  have sequential : returns library.runtime := by
    metta_lift checked ["left", "right"] word
  have rho : returns rhoLibrary.runtime := by
    metta_lift rho_checked ["left", "right"] sequential
  metta_lift actor_checked ["left", "right"] rho

#print axioms append_returns

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.MeTTaIL.ErlangActorListOperations
