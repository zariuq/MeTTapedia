import Mettapedia.TypeTheory.DisplayedPresheafRefinementTransport
import Mathlib.Data.Fintype.Card

/-!
# Refinement receipts for a genuinely varying finite family

The program map erases the natural-number source index. Source certificates
have type `Fin (n + 2)` and their refinement requires the final inhabitant
`n + 1`. The independent target specification retains the original index
with its finite certificate. Erasing either the origin or the predicate
membership changes what can be recovered from the target data.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.DisplayedPresheafRefinementTransportControls

open _root_.CategoryTheory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafEvidenceTransport DisplayedPresheafEvidenceUniversal
open DisplayedPresheafRefinementTransport

abbrev World := Discrete Unit

abbrev programs : Worldᵒᵖ ⥤ Type where
  obj _ := Nat
  map _ := 𝟙 Nat
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev targets : Worldᵒᵖ ⥤ Type := (Functor.const _).obj Unit

def erase : programs ⟶ targets where
  app _ := TypeCat.ofHom fun _ => ()
  naturality := by intros; rfl

abbrev finiteFamily : DisplayedFamily programs where
  obj point := Fin (point.2 + 2)
  map arrow := TypeCat.ofHom fun witness =>
    Fin.cast (congrArg (fun n : Nat => n + 2) arrow.property) witness
  map_id _ := by ext witness; rfl
  map_comp _ _ := by ext witness; rfl

def finalInhabitant : Subfunctor (totalSpace finiteFamily) where
  obj _ := {entry | entry.2.val = entry.1 + 1}
  map _ := by intro entry belongs; exact belongs

abbrev targetFamily : DisplayedFamily targets :=
  (Functor.const _).obj (Sigma fun n : Nat => Fin (n + 2))

def targetPredicate : Subfunctor (totalSpace targetFamily) where
  obj _ := {entry | entry.2.2.val = entry.2.1 + 1}
  map _ := by intro entry belongs; exact belongs

/-- The target family and its predicate are constructed independently
of the compiler receipt. This implementation keeps the supplied index. -/
def sourceImplementation : finiteFamily ⟶ reindexDisplayed erase targetFamily where
  app point := TypeCat.ofHom fun witness => ⟨point.2, witness⟩
  naturality first second arrow := by
    ext witness
    rcases first with ⟨firstWorld, firstProgram⟩
    rcases second with ⟨secondWorld, secondProgram⟩
    rcases arrow with ⟨arrow, same⟩
    change firstProgram = secondProgram at same
    subst secondProgram
    rfl

theorem implementation_respects :
    finalInhabitant ≤ targetPredicate.preimage (evidenceTotalMap erase sourceImplementation) := by
  intro world entry belongs
  exact belongs

def readout : transport erase (Refinement.displayed finiteFamily finalInhabitant) ⟶
    Refinement.displayed targetFamily targetPredicate :=
  descendRefined erase sourceImplementation finalInhabitant targetPredicate implementation_respects

def world : Worldᵒᵖ := Opposite.op (Discrete.mk ())

def point (n : Nat) : programs.Elements := ⟨world, n⟩

def supplied (n : Nat) : (Refinement.displayed finiteFamily finalInhabitant).obj (point n) :=
  ⟨⟨n + 1, Nat.lt_succ_self (n + 1)⟩, rfl⟩

def receipt (n : Nat) :
    (transport erase (Refinement.displayed finiteFamily finalInhabitant)).obj ⟨world, ()⟩ :=
  (unit erase (Refinement.displayed finiteFamily finalInhabitant)).app (point n) (supplied n)

/-- Both the actual dependent finite value and its source origin survive
universal elimination into the independently formed target refinement. -/
theorem readout_computes (n : Nat) :
    (readout.app ⟨world, ()⟩ (receipt n)).val =
      (⟨n, ⟨n + 1, Nat.lt_succ_self (n + 1)⟩⟩ : Sigma fun m : Nat => Fin (m + 2)) := by
  exact descendRefined_unit erase sourceImplementation finalInhabitant targetPredicate
    implementation_respects (point n) (supplied n)

theorem readout_membership (n : Nat) :
    (readout.app ⟨world, ()⟩ (receipt n)).val.2.val =
      (readout.app ⟨world, ()⟩ (receipt n)).val.1 + 1 :=
  (readout.app ⟨world, ()⟩ (receipt n)).property

theorem comparison_keeps_origin (n : Nat) :
    (((transportIso erase finiteFamily finalInhabitant).hom.app ⟨world, ()⟩
      (receipt n)).val.val).1 = n := rfl

theorem comparison_keeps_value (n : Nat) :
    (((transportIso erase finiteFamily finalInhabitant).hom.app ⟨world, ()⟩
      (receipt n)).val.val).2.val = n + 1 := rfl

/-- The fibre is genuinely dependent; its two consecutive original
contexts have different finite cardinalities. -/
theorem source_types_vary : finiteFamily.obj (point 0) ≠ finiteFamily.obj (point 1) := by
  change Fin 2 ≠ Fin 3
  intro same
  have cardinal := Fintype.card_congr (Equiv.cast same)
  simp only [Fintype.card_fin] at cardinal
  exact (by decide : (2 : Nat) ≠ 3) cardinal

/-- Having a value in the original family does not establish the
refinement predicate. The omitted premise is detected at an actual fibre. -/
theorem omitted_membership_is_invalid :
    (⟨0, (⟨0, by decide⟩ : Fin 2)⟩ : (totalSpace finiteFamily).obj world) ∉
      finalInhabitant.obj world := by
  change ¬ (0 : Nat) = 0 + 1
  decide

theorem receipts_distinguish_origins : receipt 0 ≠ receipt 1 := by
  intro same
  have origins := congrArg (fun candidate => candidate.val.1) same
  exact (by decide : (0 : Nat) ≠ 1) origins

/-- The erased target index has one value for these two distinct
receipts, so no decoder depending only on that index recovers origins. -/
theorem erased_index_cannot_recover_origins :
    ¬ ∃ decode : Unit → Nat, decode () = 0 ∧ decode () = 1 := by
  rintro ⟨decode, first, second⟩
  exact (by decide : (0 : Nat) ≠ 1) (first.symm.trans second)

/-- Independent target specifications still separate the two actual
certificates even though their compiled program indices coincide. -/
theorem readouts_distinguish_origins :
    readout.app ⟨world, ()⟩ (receipt 0) ≠ readout.app ⟨world, ()⟩ (receipt 1) := by
  intro same
  have origins := congrArg (fun selected => selected.val.1) same
  rw [readout_computes, readout_computes] at origins
  exact (by decide : (0 : Nat) ≠ 1) origins

end Mettapedia.TypeTheory.DisplayedPresheafRefinementTransportControls
