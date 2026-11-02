import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorActivityReadback
import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorPositionModel

/-!
# Source activity readback in the independent natural/list model

The canonical leading position has a closed retained proof for every length.
The original source is active there exactly when its shape guard holds. This
independently rules out replacing guarded source activity by the bare plan
witness, even though the position plan itself is unchanged.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorActivityReadbackControls
open Mettapedia.Logic Mettapedia.Logic.HOL
open IndexedContainerNativeVectorMethodReading (Base Const N E original)
open IndexedContainerNativeVectorPositionReading
open IndexedContainerNativeVectorPositionModel
open IndexedContainerNativeVectorActivityReadback
open OrderedPositionPrograms

theorem sound {formula : ClosedFormula Const} (proof : ProofSyntax Const [] formula) :
    (model.denote formula values).down :=
  Soundness.extDerivation_sound proof.erase
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (fun _ => trivial) (fun _ absent => False.elim (List.not_mem_nil absent))

def canonicalLeading (length : Nat) : ProofSyntax Const [] (positionWitness (numeral [] length) (numeral [] 0)) :=
  activeAt_intro original.zero original.successor
    (mixedPlan original.zero original.successor (numeral [] length) .top .top .top) (numeral [] 0) .top
    (mixedFirst original.zero original.successor (numeral [] length) .top .top .top)

theorem canonicalLeading_free (length : Nat) : (canonicalLeading length).FunctionExtensionalityFree :=
  activeAt_intro_free _ _ _ _ _ _ (mixedFirst_free _ _ _ _ _ _)

theorem canonicalLeading_holds (length : Nat) :
    (model.denote (positionWitness (numeral [] length) (numeral [] 0)) values).down :=
  sound (canonicalLeading length)

theorem guardedEquation_holds (length shape slot : Nat) :
    (model.denote (.app (sourceActivity payload (numeral [] length) tag (numeral [] shape)) (numeral [] slot)) values).down ↔
      (model.denote (sourceAllowed payload (numeral [] length) tag (numeral [] shape)) values).down ∧
      (model.denote (positionWitness (numeral [] length) (numeral [] slot)) values).down := by
  have comparison := sound (equation payload (numeral [] length) tag (numeral [] shape) (numeral [] slot))
  exact comparison

theorem wellFormed_leading_active (length : Nat) :
    (model.denote (.app (sourceActivity payload (numeral [] length) tag (numeral [] 0)) (numeral [] 0)) values).down := by
  change (model.denote (sourceActivity payload (numeral [] length) tag (numeral [] 0)) values (ULift.up 0)).down
  rw [sourceActivity_iff]
  exact ⟨rfl,by omega⟩

theorem malformed_leading_inactive (length : Nat) :
    ¬ (model.denote (.app (sourceActivity payload (numeral [] length) tag (numeral [] 9)) (numeral [] 0)) values).down := by
  change ¬ (model.denote (sourceActivity payload (numeral [] length) tag (numeral [] 9)) values (ULift.up 0)).down
  rw [sourceActivity_iff]
  simp

theorem dropped_guard_equation_refused (length : Nat) :
    ¬ Nonempty (ProofSyntax Const [] (.eq
      (.app (sourceActivity payload (numeral [] length) tag (numeral [] 9)) (numeral [] 0))
      (positionWitness (numeral [] length) (numeral [] 0)))) := by
  rintro ⟨claimed⟩
  exact malformed_leading_inactive length (sound (.impE (.eqPropER claimed) (canonicalLeading length)))

theorem bare_witness_does_not_activate_source (length : Nat) :
    ¬ Nonempty (ProofSyntax Const [] (.imp
      (positionWitness (numeral [] length) (numeral [] 0))
      (.app (sourceActivity payload (numeral [] length) tag (numeral [] 9)) (numeral [] 0)))) := by
  rintro ⟨claimed⟩
  exact malformed_leading_inactive length (sound (.impE claimed (canonicalLeading length)))

theorem source_guard_independent_of_plan (length : Nat) :
    (model.denote (positionWitness (numeral [] length) (numeral [] 0)) values).down ∧
    (model.denote (.app (sourceActivity payload (numeral [] length) tag (numeral [] 0)) (numeral [] 0)) values).down ∧
    ¬ (model.denote (.app (sourceActivity payload (numeral [] length) tag (numeral [] 9)) (numeral [] 0)) values).down :=
  ⟨canonicalLeading_holds length,wellFormed_leading_active length,malformed_leading_inactive length⟩

#print axioms guardedEquation_holds
#print axioms dropped_guard_equation_refused
#print axioms bare_witness_does_not_activate_source
end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorActivityReadbackControls
