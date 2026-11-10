import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLFrameEncoding

/-! # Empty valid fibres and invalid raw values are different

A valid frame may have no terms while still having an identity morphism and
a solution of its empty store. Conversely, inhabiting the raw morphism type
does not produce a map from a nonempty term fibre into an empty one.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLFrameEncoding.Controls

open Mettapedia.Logic.HOL.IndexedCarrier.Controls (family)

abbrev maps (a b : Bool) := family a → family b

def frame : Frames family maps where
  E := Eq
  equivalence _ := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  act f term := f term
  id _ := id
  comp g f := g ∘ f
  act_id _ := rfl
  act_comp _ _ _ := rfl
  preserves := by intro a b f s t same; exact congrArg f same

theorem empty_frame_is_valid : objects (some false) ∧ ¬∃ term : Terms family, terms (some false) term := by
  refine ⟨True.intro, ?_⟩
  rintro ⟨raw, valid⟩
  exact empty_fibre_stays_empty (Tm := family) false raw valid

theorem empty_frame_has_identity :
    hom (some false) (some false) (identity frame (some false)) :=
  identity_valid frame True.intro

theorem empty_frame_has_a_solution :
    solvable frame (some false) (store ([] : EquationStore (family false))) := by
  apply (solvable_encoded frame []).mpr
  exact ⟨false, id, frame.models_nil id⟩

theorem no_invented_map_to_empty :
    Nonempty (Morphisms maps) ∧ ¬∃ map : Morphisms maps, hom (some true) (some false) map := by
  refine ⟨⟨none⟩, ?_⟩
  rintro ⟨raw, map, _⟩
  exact Empty.elim (map (show family true from (0 : Nat)))

theorem raw_sentinel_is_not_a_solution :
    ¬models frame (some true) (some true) none (store ([] : EquationStore (family true))) := by
  rintro ⟨valid, _⟩
  exact Mettapedia.Logic.HOL.IndexedCarrier.invalid_sentinel
    (fun pair : Bool × Bool => maps pair.1 pair.2) (true, true) valid

theorem false_guard_not_licensed_by_empty_terms :
    ¬entails frame (some false) (store ([] : EquationStore (family false)))
      (guard (fun (_ : Bool) (_ : maps false _) => False)) := by
  intro claimed
  have asks := (entails_encoded frame [] (fun (_ : Bool) (_ : maps false _) => False)).mp claimed
  exact asks false id (frame.models_nil id)

#print axioms empty_frame_has_a_solution
#print axioms no_invented_map_to_empty
#print axioms false_guard_not_licensed_by_empty_terms

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLFrameEncoding.Controls
