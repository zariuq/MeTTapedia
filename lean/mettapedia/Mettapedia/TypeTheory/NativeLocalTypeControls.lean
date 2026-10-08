import Mettapedia.TypeTheory.NativeLocalParameterControls
import Mettapedia.TypeTheory.NativeLocalPiEta

/-!
# Supplied witnesses in native local products and sums

The Boolean base chooses one or two arguments. The actual argument
selects zero or one, and the dependent body returns that supplied value
in `Fin (n + 1)`. Application, pairing and substitution retain these
witnesses in the native local model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.NativeLocalTypeControls

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafCwf
open ContextualLocalUniverses NativeLocalTypeFormers NativeLocalTypeOperations
open NativeLocalParameterControls

def argument : domain.decoded.sections where
  val point := ⟨if point.2 then 1 else 0, by
    change (if point.2 then 1 else 0) < (if point.2 then 1 else 0) + 1
    exact Nat.lt_succ_self _⟩
  property := by
    intro source target arrow
    apply Fin.ext
    change (if source.2 then 1 else 0) = (if target.2 then 1 else 0)
    exact congrArg (fun value : Bool => if value then 1 else 0) arrow.property

def dependentBody : codomain.decoded.sections where
  val point := ⟨point.2.2.val, Nat.lt_succ_self _⟩
  property := by
    intro source target arrow
    apply Fin.ext
    change source.2.2.val = target.2.2.val
    exact congrArg (fun receipt => receipt.2.val) arrow.property

noncomputable def function : (pi domain codomain).decoded.sections :=
  lam (A := domain) (B := codomain) dependentBody

noncomputable def returned := app function argument

theorem actual_application :
    returned = reindexDisplayedSection (sectionLift domain.decoded argument)
      codomain.decoded dependentBody := beta dependentBody argument

theorem returned_false : (returned.val ⟨world, false⟩).val = 0 := by
  rw [actual_application]
  rfl

theorem returned_true : (returned.val ⟨world, true⟩).val = 1 := by
  rw [actual_application]
  rfl

theorem distinct_actual_readouts :
    (returned.val ⟨world, false⟩).val ≠ (returned.val ⟨world, true⟩).val := by
  rw [returned_false, returned_true]
  decide

theorem abstraction_substitution :
    HEq (substituteTerm (type := pi domain codomain) function exchange)
      (lam (A := domain.reindex exchange)
        (B := codomain.reindex (totalReindexMap exchange domain.decoded))
        (substituteTerm (type := codomain) dependentBody
          (totalReindexMap exchange domain.decoded))) :=
  lam_reindex exchange dependentBody

noncomputable def exchangedReturn :=
  reindexDisplayedSection exchange
    (reindexDisplayed (sectionLift domain.decoded argument) codomain.decoded) returned

theorem exchanged_return_true : (exchangedReturn.val ⟨world, true⟩).val = 0 := by
  change (returned.val ⟨world, false⟩).val = 0
  exact returned_false

theorem omitted_substitution_changes_answer :
    (exchangedReturn.val ⟨world, true⟩).val ≠ (returned.val ⟨world, true⟩).val := by
  rw [exchanged_return_true, returned_true]
  decide

noncomputable def suppliedPair : (sigma domain codomain).decoded.sections :=
  pair argument returned

theorem supplied_first : fst suppliedPair = argument := fst_pair argument returned

theorem supplied_second : HEq (snd suppliedPair) returned := snd_pair argument returned

theorem supplied_pair_eta : pair (fst suppliedPair) (snd suppliedPair) = suppliedPair :=
  sum_eta suppliedPair

theorem supplied_function_eta :
    ContextualPiEta.genericSection (products World)
        (products_formation_substitution World) function = dependentBody := by
  rw [NativeLocalPiEta.genericSection_eq_inverse]
  exact (functionEquiv domain codomain).symm_apply_apply dependentBody

end Mettapedia.TypeTheory.NativeLocalTypeControls
