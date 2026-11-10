import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLSolutionSpecialization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLFrameEncodingControls

/-! # Actual loaded predicates on empty fibres and nonidentity substitutions

One constructed interpretation admits the empty frame's genuine identity
solution and a successor substitution in a nonempty frame. It rejects the
invalid raw target; an inhabited HOL carrier cannot create a valid solution.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLSolutionControls

open Mettapedia.Logic Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.HOLLight
open Mettapedia.Logic.HOL.IndexedCarrier.Controls (family)
open HOLFrameEncoding.Controls (frame maps)
open HOLFrameCoding

theorem concrete_loaded_controls (other : TypeFamilySemantics.OperatorFamilies.{0})
    (prior : TypeFamilySemantics.Assignment.{0}) :
    ∃ (actual : HOL.HenkinModel.{0,0,1} AtomicTy Symbol) (code : Coding actual Bool family maps),
      actual.FullDomains ∧
      (actual.constDen HOLLoadedSolvable.symbol (homValue actual code) (equalValue actual frame code)
        (actionValue actual frame code) (code.objects.symm (some false))
        (storeValue actual code ([] : EquationStore (family false)))).down ∧
      (actual.constDen HOLLoadedModels.symbol (homValue actual code) (equalValue actual frame code)
        (actionValue actual frame code) (code.objects.symm (some true)) (code.objects.symm (some true))
        (code.morphisms.symm (HOLFrameEncoding.encodeHom (Hom := maps) (a := true) (b := true) Nat.succ))
        (storeValue actual code (a := true) [((0 : Nat), (0 : Nat))])).down ∧
      ¬(actual.constDen HOLLoadedModels.symbol (homValue actual code) (equalValue actual frame code)
        (actionValue actual frame code) (code.objects.symm (some true)) (code.objects.symm none)
        (code.morphisms.symm none) (storeValue actual code ([] : EquationStore (family true)))).down := by
  obtain ⟨actual, same, full, equations⟩ := HOLFrameDomains.loaded_model_exists Bool family maps Nat other prior
  let code := (initialCoding (Obj := Bool) (Tm := family) (Hom := maps) Nat other prior).changeModel actual same
  refine ⟨actual, code, full, ?_, ?_, ?_⟩
  · apply (HOLSolutionSpecialization.solvable_iff actual frame code full equations []).mpr
    exact ⟨false, id, frame.models_nil id⟩
  · apply (HOLModelsSpecialization.models_iff actual frame code full equations (a := true) (b := true)
      Nat.succ [((0 : Nat), (0 : Nat))]).mpr
    intro equation member
    have sameEquation := List.mem_singleton.mp member
    subst equation
    rfl
  · exact HOLSolutionSpecialization.invalid_target_has_no_model actual frame code full equations true none []

#print axioms concrete_loaded_controls

namespace FutureRequired

abbrev values : Bool → Type
  | false => Bool
  | true => Unit

abbrev arrows : Bool → Bool → Type
  | true, false => Empty
  | _, _ => Unit

def futureFrame : Frames values arrows where
  E := Eq
  equivalence _ := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  act {a b} map term := match a, b, map, term with
    | false, false, _, value => value
    | false, true, _, _ => ()
    | true, true, _, value => value
    | true, false, impossible, _ => nomatch impossible
  id a := by cases a <;> exact ()
  comp {a b c} second first := by
    cases a <;> cases b <;> cases c
    all_goals first | exact () | exact Empty.elim first | exact Empty.elim second
  act_id := by intro a term; cases a <;> rfl
  act_comp := by
    intro a b c second first term
    cases a <;> cases b <;> cases c
    all_goals first | rfl | exact Empty.elim first | exact Empty.elim second
  preserves := by intro a b map first second same; cases same; rfl

def problem : EquationStore (values false) := [(true, false)]

theorem solvable_in_future : futureFrame.Solvable problem := by
  refine ⟨true, (), ?_⟩
  intro equation member
  have same := List.mem_singleton.mp member
  subst equation
  rfl

theorem no_current_frame_solution (map : arrows false false) : ¬futureFrame.Models map problem := by
  intro models
  have impossible := models (true, false) (List.mem_singleton_self _)
  change (true : Bool) = false at impossible
  cases impossible

/-- Restricting the loaded existential to the current frame would change
its answer on this actual interpretation. -/
theorem loaded_future_is_essential (other : TypeFamilySemantics.OperatorFamilies.{0})
    (prior : TypeFamilySemantics.Assignment.{0}) :
    ∃ (actual : HOL.HenkinModel.{0,0,1} AtomicTy Symbol) (code : Coding actual Bool values arrows),
      (actual.constDen HOLLoadedSolvable.symbol (homValue actual code) (equalValue actual futureFrame code)
        (actionValue actual futureFrame code) (code.objects.symm (some false))
        (storeValue actual code problem)).down ∧
      ∀ map : arrows false false,
        ¬(actual.constDen HOLLoadedModels.symbol (homValue actual code) (equalValue actual futureFrame code)
          (actionValue actual futureFrame code) (code.objects.symm (some false)) (code.objects.symm (some false))
          (code.morphisms.symm (HOLFrameEncoding.encodeHom (Hom := arrows) (a := false) (b := false) map))
          (storeValue actual code problem)).down := by
  obtain ⟨actual, same, full, equations⟩ := HOLFrameDomains.loaded_model_exists Bool values arrows Nat other prior
  let code := (initialCoding (Obj := Bool) (Tm := values) (Hom := arrows) Nat other prior).changeModel actual same
  refine ⟨actual, code,
    (HOLSolutionSpecialization.solvable_iff actual futureFrame code full equations problem).mpr solvable_in_future, ?_⟩
  intro map claimed
  exact no_current_frame_solution map
    ((HOLModelsSpecialization.models_iff actual futureFrame code full equations map problem).mp claimed)

#print axioms loaded_future_is_essential

end FutureRequired

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLSolutionControls
