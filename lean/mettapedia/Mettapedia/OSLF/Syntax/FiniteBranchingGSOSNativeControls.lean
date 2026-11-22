import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSNativeInterpretation
import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSPresentationControls
import Mettapedia.OSLF.Syntax.GSOSNativeGuardControls
import Mathlib.CategoryTheory.SingleObj

/-!
# Retained nondeterministic witnesses under genuine context changes

Two repeated positive occurrences at one address select different successors
and retain different identifiers. The other child's passive source is present
in the independently authored target. Multiplication changes both the actual
endpoint and its dependent finite witness; zero identifies successor values
while retaining occurrence identifiers. A growing event presheaf separately
excludes an unrestricted present-absence interpretation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.NativeControls

open _root_.CategoryTheory Mettapedia.TypeTheory
open Premises NativeEdges NativePremises PresheafEventCertificates
open DisplayedPresheafTransport DisplayedPresheafComprehension
open GSOSControls (signature Operator naturals pure)
open PresentationControls (actions authored doublePattern doubleRule)

abbrev World := SingleObj Nat
def world : Worldᵒᵖ := Opposite.op (SingleObj.star Nat)

abbrev worlds : Worldᵒᵖ ⥤ signature.Families where
  obj _ := naturals
  map change := fun _ _ => ↾(fun (number : Nat) => Nat.mul (show Nat from change.unop) number)
  map_id _ := by
    funext base sort
    apply ConcreteCategory.hom_ext
    intro number
    exact Nat.one_mul number
  map_comp before after := by
    funext base sort
    apply ConcreteCategory.hom_ext
    intro number
    change Nat.mul (Nat.mul before.unop after.unop) number = Nat.mul after.unop (Nat.mul before.unop number)
    exact (Nat.mul_assoc before.unop after.unop number).trans
      (Nat.mul_left_comm before.unop after.unop number)

def variableSteps : worlds ⟶ worlds ⋙ behaviourFunctor signature actions where
  app _ := fun _ _ => ↾(fun (number : Nat) (action : Bool) =>
    if action then (∅ : Finset Nat) else ({number, 2 * number} : Finset Nat))
  naturality {first second} change := by
    funext base sort
    apply ConcreteCategory.hom_ext
    intro number
    funext action
    change (if action then (∅ : Finset Nat) else
      {Nat.mul change.unop number, 2 * Nat.mul change.unop number}) =
      Mettapedia.CategoryTheory.FinitePowerset.map (Nat.mul change.unop)
        (if action then (∅ : Finset Nat) else {number, 2 * number})
    cases action with
    | false =>
        simp only [Bool.false_eq_true, ↓reduceIte, Mettapedia.CategoryTheory.FinitePowerset.map,
          Finset.image_insert, Finset.image_singleton]
        apply Finset.ext
        intro target
        simp only [Finset.mem_insert, Finset.mem_singleton]
        exact or_congr Iff.rfl
          (Iff.of_eq (congrArg (fun value : Nat => target = value)
            (Nat.mul_left_comm 2 change.unop number)))
    | true => exact (Mettapedia.CategoryTheory.FinitePowerset.map_empty _).symm

def change (factor : Nat) : world ⟶ world :=
  (show SingleObj.star Nat ⟶ SingleObj.star Nat from factor).op

abbrev given : (NativePremises.children worlds (sort := ()) Operator.choose).obj world :=
  fun position => if position then pure (X := naturals) 20 else pure (X := naturals) 10

def positive (occurrence : Fin 2) :
    NativeEdges.Event (NativePremises.law authored) worlds variableSteps (Fin 2) () false world where
  origin := occurrence
  source := pure (X := naturals) 10
  target := pure (X := naturals) (if occurrence.val = 0 then 10 else 20)
  valid := by
    change pure (X := naturals) (if occurrence.val = 0 then 10 else 20) ∈
      Operational.coalgebra (NativePremises.law authored) (variableSteps.app world) PUnit.unit ()
        (pure (X := naturals) 10) false
    have computed := Operational.coalgebra_pure (S := signature) (law authored)
      (variableSteps.app world) (base := PUnit.unit) (sort := ()) (10 : Nat) false
    apply (congrArg (fun targets => pure (X := naturals)
      (if occurrence.val = 0 then 10 else 20) ∈ targets) computed).mpr
    apply (Mettapedia.CategoryTheory.FinitePowerset.mem_map _ _ _).mpr
    refine ⟨if occurrence.val = 0 then 10 else 20, ?_, rfl⟩
    change (if occurrence.val = 0 then 10 else 20) ∈ ({10, 20} : Finset Nat)
    split_ifs <;> decide

def firing (origin : Bool) :
    NativePremises.Firing authored worlds variableSteps (Fin 2) world (sort := ()) Operator.choose false where
  origin := origin
  children := given
  positive := positive
  positive_source _ := rfl
  negative address member := by
    have same : address = ⟨true, true⟩ := Finset.mem_singleton.mp member
    subst address
    apply (NativeEdges.noAction_iff_empty (NativePremises.law authored) worlds variableSteps
      () true world (pure (X := naturals) 20)).mpr
    exact (Operational.coalgebra_pure (S := signature) (law authored)
      (variableSteps.app world) (base := PUnit.unit) (sort := ()) (20 : Nat) true).trans
        (Mettapedia.CategoryTheory.FinitePowerset.map_empty _)

theorem repeated_occurrences_keep_different_targets :
    (firing false).input.derivatives (0 : Fin 2) = pure (X := naturals) 10 ∧
      (firing false).input.derivatives (1 : Fin 2) = pure (X := naturals) 20 := ⟨rfl, rfl⟩

theorem passive_source_retained : (firing false).input.originals true = pure (X := naturals) 20 := rfl

theorem actual_firing_is_an_operational_successor :
    (firing false).target ∈ Operational.coalgebra (NativePremises.law authored)
      (variableSteps.app world) PUnit.unit () (firing false).source false :=
  (firing false).target_member

theorem same_endpoint_distinct_authored_origins :
    firing false ≠ firing true ∧ (firing false).target = (firing true).target := by
  constructor
  · intro same
    exact Bool.false_ne_true (congrArg NativePremises.Firing.origin same)
  · rfl

def weightAlgebra : signature.polynomial.Algebra (fun _ _ => Nat) where
  act _ _ layer := match layer with
    | ⟨.stopped, _⟩ => 0
    | ⟨.choose, given⟩ => given false + given true

def weightAt (base : PUnit) (sort : signature.Srt)
    (term : signature.polynomial.Free naturals base sort) : Nat :=
  IndexedPolynomial.Free.fold signature.polynomial (fun _ _ number => number) weightAlgebra base sort term

abbrev weight := weightAt PUnit.unit ()

theorem weight_rename (factor : Nat) (term : signature.Term naturals ()) :
    weight (signature.rename (worlds.map (change factor)) term) = factor * weight term := by
  let scaled : ∀ base sort, naturals base sort → Nat := fun _ _ number => factor * number
  have mapped := IndexedPolynomial.Free.fold_unique signature.polynomial scaled weightAlgebra
    (fun base sort current => weightAt base sort
      (signature.termMonad.map (worlds.map (change factor)) base sort current))
    (fun _ _ _ => rfl)
    (fun base sort operator given => by
      cases operator <;> rfl)
  have multiplied := IndexedPolynomial.Free.fold_unique signature.polynomial scaled weightAlgebra
    (fun base sort current => factor * weightAt base sort current)
    (fun _ _ _ => rfl)
    (fun base sort operator given => by
      cases operator with
      | stopped => exact Nat.mul_zero factor
      | choose => exact Nat.mul_add factor _ _)
  exact (mapped PUnit.unit () term).trans (multiplied PUnit.unit () term).symm

abbrev programs := NativeEdges.terms worlds ()

theorem weight_map {first second : Worldᵒᵖ} (arrow : first ⟶ second)
    (term : programs.obj first) : weight (programs.map arrow term) = Nat.mul arrow.unop (weight term) := by
  exact weight_rename arrow.unop term

def targetFamily : DisplayedFamily programs where
  obj point := Fin (weight point.2 + 1)
  map {first second} arrow := ↾(fun witness =>
    ⟨Nat.mul arrow.val.unop witness.val, by
      have endpoint : weight second.2 = Nat.mul arrow.val.unop (weight first.2) :=
        (congrArg weight arrow.property).symm.trans (weight_map arrow.val first.2)
      rw [endpoint]
      exact Nat.lt_succ_of_le (Nat.mul_le_mul_left _ (Nat.le_of_lt_succ witness.isLt))⟩)
  map_id _ := by
    apply ConcreteCategory.hom_ext
    intro witness
    apply Fin.ext
    exact Nat.one_mul witness.val
  map_comp before after := by
    apply ConcreteCategory.hom_ext
    intro witness
    apply Fin.ext
    change Nat.mul (Nat.mul before.val.unop after.val.unop) witness.val =
      Nat.mul after.val.unop (Nat.mul before.val.unop witness.val)
    exact (Nat.mul_assoc _ _ _).trans (Nat.mul_left_comm _ _ _)

theorem actual_target_weight : weight (firing false).target = 50 := rfl

def witness : targetFamily.obj ⟨world, (firing false).target⟩ := ⟨50, by decide⟩

abbrev span := firingSpan authored worlds variableSteps (Fin 2) (sort := ()) Operator.choose false
def receipt := (firing false).certificate targetFamily witness

theorem native_receipt_keeps_whole_firing :
    (span.eventReadout targetFamily).app world ⟨(firing false).source, receipt⟩ = firing false :=
  (firing false).certificate_event targetFamily witness

theorem native_receipt_keeps_dependent_result :
    (span.resultReadout targetFamily).app world ⟨(firing false).source, receipt⟩ =
      ⟨(firing false).target, witness⟩ :=
  (firing false).certificate_result targetFamily witness

def mappedResult (factor : Nat) : (totalSpace targetFamily).obj world :=
  (span.resultReadout targetFamily).app world
    ((totalSpace (span.certificates targetFamily)).map (change factor)
      ⟨(firing false).source, receipt⟩)

/-- The actual transported certificate, not just its endpoint, changes
its supplied finite position through the independently varying family. -/
theorem mapped_witness_readout (factor : Nat) : (mappedResult factor).2.val = factor * 50 := by
  exact congrArg (fun result : (totalSpace targetFamily).obj world => result.2.val)
    ((firing false).certificate_result_substitution (change factor) targetFamily witness)

theorem twice_actual_witness : (mappedResult 2).2.val = 100 := mapped_witness_readout 2

theorem zero_actual_witness : (mappedResult 0).2.val = 0 := mapped_witness_readout 0

def mappedEvent (factor : Nat) :
    NativePremises.Firing authored worlds variableSteps (Fin 2) world (sort := ()) Operator.choose false :=
  (span.eventReadout targetFamily).app world
    ((totalSpace (span.certificates targetFamily)).map (change factor)
      ⟨(firing false).source, receipt⟩)

theorem mapped_event_readout (factor : Nat) : mappedEvent factor = (firing false).map (change factor) :=
  (firing false).certificate_event_substitution (change factor) targetFamily witness

abbrev decodedReceipt :=
  NativeInterpretation.certificateTotalEquiv authored worlds variableSteps (Fin 2) world
    (sort := ()) Operator.choose false targetFamily ⟨(firing false).source, receipt⟩

theorem independent_matching_readout :
    decodedReceipt.1.2.1.origin = false ∧
    decodedReceipt.1.2.1.input.derivatives (0 : Fin 2) = pure (X := naturals) 10 ∧
    decodedReceipt.1.2.1.input.derivatives (1 : Fin 2) = pure (X := naturals) 20 ∧
    decodedReceipt.1.2.2 (0 : Fin 2) = (0 : Fin 2) ∧
    decodedReceipt.1.2.2 (1 : Fin 2) = (1 : Fin 2) ∧
    decodedReceipt.2.val = 50 := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem genuine_future_sieve_matching :
    ((NativeInterpretation.guardCharacteristic authored worlds variableSteps doublePattern).app world given).arrows
      (change 2).unop := by
  apply (NativeInterpretation.guard_sieve_readout authored worlds variableSteps doublePattern (change 2) given).mpr
  exact ⟨((firing false).map (change 2)).input, ((firing false).map (change 2)).matching⟩

theorem empty_origins_do_not_supply_positive_occurrences :
    ¬ Nonempty (NativePremises.Firing authored worlds variableSteps Empty world
      (sort := ()) Operator.choose false) := by
  rintro ⟨present⟩
  exact (present.positive (0 : Fin 2)).origin.elim

theorem nonidentity_endpoint_changes :
    weight ((firing false).map (change 2)).target = 100 := by
  rw [NativePremises.Firing.target_map, weight_rename, actual_target_weight]

theorem zero_identifies_derivatives_retains_origins :
    (((firing false).map (change 0)).positive (0 : Fin 2)).target =
      (((firing false).map (change 0)).positive (1 : Fin 2)).target ∧
    (((firing false).map (change 0)).positive (0 : Fin 2)).origin ≠
      (((firing false).map (change 0)).positive (1 : Fin 2)).origin := by
  constructor
  · rfl
  · exact Fin.zero_ne_one

theorem actual_zero_receipt_retains_occurrence_origins :
    ((mappedEvent 0).positive (0 : Fin 2)).origin ≠ ((mappedEvent 0).positive (1 : Fin 2)).origin := by
  rw [mapped_event_readout]
  exact Fin.zero_ne_one

theorem finite_action_reconstruction_has_actual_native_domain :
    (firing false).target ∈ Operational.coalgebra PresentationControls.pairLaw
      (variableSteps.app world) PUnit.unit () (firing false).source false ↔
    ∃ present : NativePremises.Firing
      (NativeCorrespondence.canonical PresentationControls.pairLaw) worlds variableSteps (Fin 2) world
        (sort := ()) Operator.choose false,
      present.children = given ∧ present.target = (firing false).target :=
  NativeCorrespondence.operational_correspondence worlds variableSteps PresentationControls.pairLaw
    (Fin 2) world (sort := ()) Operator.choose false given (firing false).target

theorem no_target_to_clause_origin_decoder :
    ¬ ∃ decoder : signature.Term naturals () → Bool,
      ∀ origin, decoder (firing origin).target = origin := by
  rintro ⟨decoder, recovers⟩
  have same := congrArg decoder same_endpoint_distinct_authored_origins.2
  rw [recovers false, recovers true] at same
  exact Bool.false_ne_true same

namespace FutureEnabling

open Mettapedia.GSLT.Topos.PresheafPredicateHigherOrderControls
open Mettapedia.OSLF.DeterministicGSOS.NativeGuardControls.Growing

abbrev growingSpan := Mettapedia.OSLF.DeterministicGSOS.NativeGuardControls.Growing.span

theorem present_empty_future_enabled :
    (¬ ∃ event : growingSpan.events.obj spot, event ∈ (⊤ : Subfunctor growingSpan.events).obj spot ∧
      growingSpan.source.app spot event = ()) ∧
    () ∉ (Mettapedia.GSLT.Topos.PresheafEventAbsence.absent growingSpan.source ⊤).obj spot :=
  ⟨absence_now, native_absence_fails⟩

theorem complete_successor_equation_excludes_this_growth :
    ¬ ∃ system : PresheafFiniteSuccessorEvents.System
      Mettapedia.GSLT.Topos.PresheafPredicateHigherOrderControls.programs Unit,
      system.successors spot () () = ∅ ∧ system.successors future () () = {()} := by
  rintro ⟨system, empty, later⟩
  have same := (system.empty_substitution restriction () ()).mpr empty
  change system.successors future () () = ∅ at same
  rw [later] at same
  exact Finset.singleton_ne_empty () same

end FutureEnabling
end Mettapedia.OSLF.FiniteBranching.NativeControls
