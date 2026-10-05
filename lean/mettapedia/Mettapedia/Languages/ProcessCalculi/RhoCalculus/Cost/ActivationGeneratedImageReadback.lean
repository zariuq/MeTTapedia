import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedImage
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGeneratedClosureReadout

/-!
# With enough fuel the readout returns the image

The second half of "success of the readout is the image", stated for the readout with
guarantees attached, and the two halves together.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax

theorem NameImage.parser_eventually {depth : Nat} {source : Pattern}
    {name : CostName LiteralAuthority} (image : NameImage depth source name) :
    ∃ bound, ∀ fuel, bound ≤ fuel → (name? fuel depth source).map Subtype.val = some name := by
  simpa only [name?_val] using image.read_eventually

theorem CodeImage.parser_eventually {depth : Nat} {source : Pattern}
    {term : CostTerm LiteralAuthority} (image : CodeImage depth source term) :
    ∃ bound, ∀ fuel, bound ≤ fuel → (code? fuel depth source).map Subtype.val = some term := by
  simpa only [code?_val] using image.read_eventually

theorem ProcImage.parser_eventually {depth : Nat} {source : Pattern}
    {process : CostProc LiteralAuthority} (image : ProcImage depth source process) :
    ∃ bound, ∀ fuel, bound ≤ fuel → (proc? fuel depth source).map Subtype.val = some process := by
  simpa only [proc?_val] using image.read_eventually

theorem CodeListImage.parser_eventually {depth : Nat} {sources : List Pattern}
    {term : CostTerm LiteralAuthority} (image : CodeListImage depth sources term) :
    ∃ bound, ∀ fuel, bound ≤ fuel → (codeList? fuel depth sources).map Subtype.val = some term := by
  simpa only [codeList?_val] using image.read_eventually

theorem name_parser_iff_image {depth : Nat} {source : Pattern} {name : CostName LiteralAuthority} :
    (∃ fuel, (name? fuel depth source).map Subtype.val = some name) ↔ NameImage depth source name :=
  ⟨fun ⟨_, parsed⟩ => name_parser_image parsed,
    fun image => image.parser_eventually.imp fun bound readback => readback bound (le_refl bound)⟩

theorem code_parser_iff_image {depth : Nat} {source : Pattern} {term : CostTerm LiteralAuthority} :
    (∃ fuel, (code? fuel depth source).map Subtype.val = some term) ↔ CodeImage depth source term :=
  ⟨fun ⟨_, parsed⟩ => code_parser_image parsed,
    fun image => image.parser_eventually.imp fun bound readback => readback bound (le_refl bound)⟩

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationGenerated
