import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLExactSpecialization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLFrameEncodingControls

/-! # Loaded exactness accepts normalization and rejects a strict extension

Removing a duplicate equation preserves every solution. Adding the equation
0 = 1 to empty information is consistent under a constant substitution but
is not exact: the identity substitution distinguishes the stores.
The naturals are object-term labels in this frame, not fixed arithmetic values.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLExactControls

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open Mettapedia.Logic.HOL.IndexedCarrier.Controls (family)
open HOLFrameEncoding.Controls (frame maps)
open HOLFrameCoding HOLFramesCoding

def equation : family true × family true := ((0 : Nat), (1 : Nat))

theorem duplicate_exact : ∀ (c : Bool) (sigma : maps true c),
    frame.Models (frame.comp sigma (frame.id true)) [equation, equation] → frame.Models sigma [equation] := by
  intro c sigma solves
  have back := (Frames.models_applyStore (frame.id true) sigma [equation, equation]).mpr solves
  rw [Frames.applyStore_id] at back
  exact Frames.models_of_subset (by simp) back

theorem added_equation_not_exact :
    ¬∀ (c : Bool) (sigma : maps true c),
      frame.Models (frame.comp sigma (frame.id true)) [] → frame.Models sigma [equation] := by
  intro claimed
  have wrong : (0 : Nat) = 1 := claimed true id (Frames.models_nil _) equation (List.mem_singleton_self _)
  omega

theorem added_equation_consistent : frame.Solvable [equation] := by
  refine ⟨true, (fun _ => (0 : Nat)), ?_⟩
  intro pair _
  rfl

theorem loaded_controls (other : TypeFamilySemantics.OperatorFamilies.{0})
    (prior : TypeFamilySemantics.Assignment.{0}) :
    ∃ (actual : HOL.HenkinModel.{0,0,1} AtomicTy Symbol) (code : Coding actual Bool family maps),
      HOLExactSpecialization.Agreement actual frame code ∧
      (actual.constDen HOLLoadedExact.symbol (homValue actual code) (equalValue actual frame code)
        (actionValue actual frame code) (compositionValue actual frame code)
        (code.objects.symm (some true)) (code.objects.symm (some true))
        (code.morphisms.symm (HOLFrameEncoding.encodeHom (frame.id true)))
        (storeValue actual code [equation, equation]) (storeValue actual code [equation])).down ∧
      ¬(actual.constDen HOLLoadedExact.symbol (homValue actual code) (equalValue actual frame code)
        (actionValue actual frame code) (compositionValue actual frame code)
        (code.objects.symm (some true)) (code.objects.symm (some true))
        (code.morphisms.symm (HOLFrameEncoding.encodeHom (frame.id true)))
        (storeValue actual code ([] : EquationStore (family true))) (storeValue actual code [equation])).down ∧
      (actual.constDen HOLLoadedSolvable.symbol (homValue actual code) (equalValue actual frame code)
        (actionValue actual frame code) (code.objects.symm (some true)) (storeValue actual code [equation])).down := by
  obtain ⟨actual, code, _, agreement⟩ := HOLExactSpecialization.constructed_agreement frame Nat other prior
  refine ⟨actual, code, agreement, ?_, ?_, ?_⟩
  · exact (agreement.exactKnowledge true true (frame.id true) _ _).mpr duplicate_exact
  · exact fun claimed => added_equation_not_exact ((agreement.exactKnowledge true true (frame.id true) _ _).mp claimed)
  · exact (agreement.solvable true [equation]).mpr added_equation_consistent

#print axioms duplicate_exact
#print axioms added_equation_not_exact
#print axioms loaded_controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLExactControls
