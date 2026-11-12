import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ModalComparison
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.NarrowingToRho
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.HeatingBisimulation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.PeTTaAndHE
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.HEOnTheStep.HEMachine

/-!
# OSLF's modalities along the narrowings of the step

Each narrowing below is read through `ModalComparison`: an open map makes reindexing a
homomorphism of modal algebras (`pb_modal_hom`), a bisimulation is a span of open maps, and
predecessor necessity asks for lifting predecessors as well.

* **Rho** (`Rho.modal_hom`): reading a heated store as a rho process is open, so possibility,
  successor necessity and every Boolean combination pull back from rho to the store.
* **HE** (`HE.answers_diamond_iff`, `HE.answers_forwardBox_iff`, `HE.graph_open`): HE's
  read-only machine and the step under its rules are bisimilar through representation, so the
  graph of representation is a span of open maps, and a store and the configuration it represents
  satisfy possibility and successor necessity together for every observation of the published
  answers. The same holds for every local framed machine (`Framed.answers_diamond_iff`).
* **Sequential PeTTa** (`PeTTa.sequential_same_modalities`): with one-copy removal, on linear
  configurations, the atomic takes and their sequential encodings have the same possibility and
  successor necessity, for every predicate.
* **Unlocked hyperpose: the precise failure.** `PeTTa.hyperpose_step_fails`: a configuration and a
  configuration one interleaving step away from its image, possible after `embed` and impossible
  before it. `PeTTa.hyperpose_reach_fails`: along runs, a final configuration reached by
  interleaving the encodings and by no atomic run. Successor necessity fails dually
  (`PeTTa.hyperpose_forwardBox_fails`).
* **The first-order step through heating: the future lifts, the past does not.**
  `FirstOrder.drop_open`: on the rule set that takes `T` and makes nothing, reading a modelled
  store as its bag of labels is an open map onto the reaction's store step (the tree's
  `HeatingBisimulation.view_functionalBisimulation`), so possibility and successor necessity pull
  back (`FirstOrder.drop_modal_hom`). Predecessor necessity does not
  (`FirstOrder.drop_predecessorBox_fails`, `FirstOrder.drop_backZag_fails`): the empty store with no
  knowledge has no predecessor, because every firing records its matches in the knowledge, while
  its image, the empty bag, has the predecessor `{T}`. Knowledge records history; the narrowing
  forgets it.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Narrowings

open Mettapedia.OSLF.Framework.DerivedModalities
open FragmentsOfTheStep.TransitionMaps
open ModalComparison

/-! ## Rho -/

namespace Rho

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open RhoSchema RhoQuotationClassFibres
open FragmentsOfTheStep.NarrowingToRho FragmentsOfTheStep.RhoChannelFragment

variable {context : Ctx sig}

/-- **Reindexing from rho to heated stores is a homomorphism of modal algebras.** -/
theorem modal_hom :
    (∀ φ : Process context → Prop,
        pb narrow (derivedDiamond (span RhoStep) φ) =
          derivedDiamond (span (heatedStep (context := context))) (pb narrow φ)) ∧
      (∀ φ : Process context → Prop,
        pb narrow (derivedForwardBox (span RhoStep) φ) =
          derivedForwardBox (span (heatedStep (context := context))) (pb narrow φ)) ∧
      (∀ φ : Process context → Prop, pb narrow φᶜ = (pb narrow φ)ᶜ) ∧
      (∀ φ ψ : Process context → Prop,
        pb narrow (fun y => φ y ∧ ψ y) = fun x => pb narrow φ x ∧ pb narrow ψ x) ∧
      (∀ φ ψ : Process context → Prop,
        pb narrow (fun y => φ y ∨ ψ y) = fun x => pb narrow φ x ∨ pb narrow ψ x) :=
  pb_modal_hom narrowing_functionalBisimulation

end Rho

/-! ## Framed machines and HE -/

namespace Framed

open DialectsAsStrategies.HEOnTheStep
open MeTTaCalculus.OccurrenceCommits (labels)

variable {W C F A : Type} {M : FramedMachine W C F A}

/-- The published answers a store holds. -/
def storeAnswers (S : Store W C F A) : Multiset A := answersOf (labels Prod.fst S.present)

/-- A store holds the answers of the configuration it represents. -/
theorem storeAnswers_eq {S : Store W C F A} {x : Config W C F A} (represented : Represents S x) :
    storeAnswers S = (x.emitted : Multiset A) := by
  unfold storeAnswers
  rw [represented.2]
  exact answersOf_encode x

/-- **A local framed machine and the step under its rules satisfy possibility together**, for
every observation of the published answers. -/
theorem answers_diamond_iff (loc : M.Local) (P : Multiset A → Prop) {S : Store W C F A}
    {x : Config W C F A} (represented : Represents S x) :
    derivedDiamond (span (StoreStep M)) (fun S => P (storeAnswers S)) S ↔
      derivedDiamond (span M.Step) (fun x => P (x.emitted : Multiset A)) x :=
  diamond_iff_of_bisimulation (bisimulation loc)
    (fun _ _ related => by rw [storeAnswers_eq related]) represented

/-- **Successor necessity, likewise.** -/
theorem answers_forwardBox_iff (loc : M.Local) (P : Multiset A → Prop) {S : Store W C F A}
    {x : Config W C F A} (represented : Represents S x) :
    derivedForwardBox (span (StoreStep M)) (fun S => P (storeAnswers S)) S ↔
      derivedForwardBox (span M.Step) (fun x => P (x.emitted : Multiset A)) x :=
  forwardBox_iff_of_bisimulation (bisimulation loc)
    (fun _ _ related => by rw [storeAnswers_eq related]) represented

end Framed

namespace HE

open DialectsAsStrategies.HEOnTheStep
open Mettapedia.Languages.MeTTa.HE (Space)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval (GroundedDispatch)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup)

variable {dispatch : GroundedDispatch} {lookup : CastLookup} {policy : Policy}

/-- **The graph of representation is a span of open maps** between the step under HE's rules
and HE's read-only machine. -/
theorem graph_open :
    FunctionalBisimulation
        (graphStep (StoreStep (heMachine dispatch lookup policy))
          (heMachine dispatch lookup policy).Step Represents)
        (StoreStep (heMachine dispatch lookup policy)) (fun p => p.1.1) ∧
      FunctionalBisimulation
        (graphStep (StoreStep (heMachine dispatch lookup policy))
          (heMachine dispatch lookup policy).Step Represents)
        (heMachine dispatch lookup policy).Step (fun p => p.1.2) :=
  isBisimulation_iff_projections_open.mp he_on_the_step

/-- **HE and the step under its rules satisfy possibility together**, for every observation of
the published answers. -/
theorem answers_diamond_iff (P : Multiset Result → Prop)
    {S : Store Space Control Continuation Result} {x : Config Space Control Continuation Result}
    (represented : Represents S x) :
    derivedDiamond (span (StoreStep (heMachine dispatch lookup policy)))
        (fun S => P (Framed.storeAnswers S)) S ↔
      derivedDiamond (span (heMachine dispatch lookup policy).Step)
        (fun x => P (x.emitted : Multiset Result)) x :=
  Framed.answers_diamond_iff he_local P represented

/-- **Successor necessity, likewise.** -/
theorem answers_forwardBox_iff (P : Multiset Result → Prop)
    {S : Store Space Control Continuation Result} {x : Config Space Control Continuation Result}
    (represented : Represents S x) :
    derivedForwardBox (span (StoreStep (heMachine dispatch lookup policy)))
        (fun S => P (Framed.storeAnswers S)) S ↔
      derivedForwardBox (span (heMachine dispatch lookup policy).Step)
        (fun x => P (x.emitted : Multiset Result)) x :=
  Framed.answers_forwardBox_iff he_local P represented

end HE

/-! ## Sequential PeTTa and unlocked hyperpose -/

namespace PeTTa

open DialectsAsStrategies DialectsAsStrategies.Concurrency DialectsAsStrategies.PeTTaHE

section Sequential

variable {α : Type*} [DecidableEq α] {β : Type*}

/-- **Atomic takes and their sequential encodings have the same modalities**, for every predicate,
with one-copy removal on linear configurations. -/
theorem sequential_same_modalities (pol : Removal) (one : pol.all = false) :
    (∀ φ : SConfig α (Take α × β) β → Prop,
        derivedDiamond (span (sequentialStep pol)) φ = derivedDiamond (span atomicStep) φ) ∧
      ∀ φ : SConfig α (Take α × β) β → Prop,
        derivedForwardBox (span (sequentialStep pol)) φ = derivedForwardBox (span atomicStep) φ :=
  ⟨fun φ => pb_diamond (sequential_open pol one) φ,
    fun φ => pb_forwardBox (sequential_open pol one) φ⟩

end Sequential

/-- **Unlocked hyperpose, one step**: possibility does not pull back along `embed`. -/
theorem hyperpose_step_fails (pol : Removal) :
    ∃ (x : SConfig ℕ (Take ℕ × ℕ) ℕ) (y' : Concurrency.Config ℕ ℕ),
      pb embed (derivedDiamond (span (Interleave pol)) (· = y')) x ∧
        ¬ derivedDiamond (span (Serial atomic Prod.snd)) (pb embed (· = y')) x := by
  by_contra contra
  apply hyperpose_no_zag pol
  intro x y' step
  by_contra noLift
  refine contra ⟨x, y', (diamond_iff _ _ _).mpr ⟨y', step, rfl⟩, fun lifted => ?_⟩
  obtain ⟨x', s, mapped⟩ := (diamond_iff _ _ _).mp lifted
  exact noLift ⟨x', s, mapped⟩

/-- **Unlocked hyperpose, along runs**: a final configuration is reached by interleaving the
encodings from the image of a configuration and by no atomic run of its takes. -/
theorem hyperpose_reach_fails (pol : Removal) :
    ∃ (x : SConfig ℕ (Take ℕ × ℕ) ℕ) (y : Concurrency.Config ℕ ℕ), y.threads = [] ∧
      pb embed (derivedDiamond (span (Relation.ReflTransGen (Interleave pol))) (· = y)) x ∧
        ¬ derivedDiamond (span (Relation.ReflTransGen (Serial atomic Prod.snd))) (pb embed (· = y)) x := by
  obtain ⟨x, y, path, done, noLift⟩ := hyperpose_not_open pol
  refine ⟨x, y, done, (diamond_iff _ _ _).mpr ⟨y, path, rfl⟩, fun holds => noLift ?_⟩
  obtain ⟨x', run, mapped⟩ := (diamond_iff _ _ _).mp holds
  exact ⟨x', run, mapped⟩

/-- **Unlocked hyperpose, successor necessity**: true of every atomic successor and false of some
interleaving successor of the image. -/
theorem hyperpose_forwardBox_fails (pol : Removal) :
    ∃ (x : SConfig ℕ (Take ℕ × ℕ) ℕ) (φ : Concurrency.Config ℕ ℕ → Prop),
      derivedForwardBox (span (Serial atomic Prod.snd)) (pb embed φ) x ∧
        ¬ pb embed (derivedForwardBox (span (Interleave pol)) φ) x := by
  by_contra contra
  apply hyperpose_no_zag pol
  intro x y' step
  by_contra noLift
  exact contra ⟨x, (· ≠ y'),
    (forwardBox_iff _ _ _).mpr fun x' s mapped => noLift ⟨x', s, mapped⟩,
    fun all => (forwardBox_iff _ _ _).mp all y' step rfl⟩

end PeTTa

/-! ## The first-order step through heating -/

namespace FirstOrder

open FragmentsOfTheStep.HeatingBisimulation
open NamesOnTheStep NamesOnTheStep.IssuingControls
open NullsOnTheStep

/-- The rule set holding only `drop`: take `T`, make nothing. -/
def dropOnly : RuleSet Expr := (· = Separations.drop)

theorem dropOnly_takeMake : TakeMake dropOnly := by
  rintro _ rfl
  exact ⟨rfl, rfl⟩

/-- Fresh occurrences for every label. -/
theorem supply (used : Finset Occ) (value : Expr) : ∃ o : Occ, o ∉ used ∧ o.1 = value := by
  obtain ⟨n, unused⟩ := Infinite.exists_notMem_finset (used.image Prod.snd)
  exact ⟨(value, n), fun member => unused (Finset.mem_image.mpr ⟨_, member, rfl⟩), rfl⟩

/-- Stores modelled by the identity, stepping by `drop`. -/
abbrev dropStep : Modelled ground () (O := Occ) → Modelled ground () (O := Occ) → Prop :=
  modelledStep ground Prod.fst () dropOnly

/-- The reaction's store step. -/
abbrev dropReaction : Multiset Expr → Multiset Expr → Prop :=
  StoreComposition.StoreStep (reaction ground () dropOnly)

/-- A modelled store read as its bag of labels. -/
abbrev dropView (C : Modelled ground () (O := Occ)) : Multiset Expr := view ground Prod.fst () C.1

/-- **The narrowing is open**: the tree's heating theorem. -/
theorem drop_open : FunctionalBisimulation dropStep dropReaction dropView :=
  view_functionalBisimulation (A := ground) (label := Prod.fst) (σ := ()) dropOnly_takeMake rfl supply

/-- **Possibility, successor necessity and the Boolean operations pull back.** -/
theorem drop_modal_hom :
    (∀ φ : Multiset Expr → Prop,
        pb dropView (derivedDiamond (span dropReaction) φ) =
          derivedDiamond (span dropStep) (pb dropView φ)) ∧
      (∀ φ : Multiset Expr → Prop,
        pb dropView (derivedForwardBox (span dropReaction) φ) =
          derivedForwardBox (span dropStep) (pb dropView φ)) ∧
      (∀ φ : Multiset Expr → Prop, pb dropView φᶜ = (pb dropView φ)ᶜ) ∧
      (∀ φ ψ : Multiset Expr → Prop,
        pb dropView (fun y => φ y ∧ ψ y) = fun x => pb dropView φ x ∧ pb dropView ψ x) ∧
      (∀ φ ψ : Multiset Expr → Prop,
        pb dropView (fun y => φ y ∨ ψ y) = fun x => pb dropView φ x ∨ pb dropView ψ x) :=
  pb_modal_hom drop_open

/-- The empty store with no knowledge. -/
def emptyC : Modelled ground () (O := Occ) :=
  ⟨⟨[], ∅⟩, fun _ member => absurd member List.not_mem_nil⟩

/-- **The empty store with no knowledge has no predecessor**: a firing of `drop` records its match
in the knowledge. -/
theorem emptyC_no_predecessor (C : Modelled ground () (O := Occ)) : ¬ dropStep C emptyC := by
  rintro ⟨rule, member, ⟨selection, valid, same⟩, _⟩
  have isDrop : rule = Separations.drop := member
  subst isDrop
  obtain ⟨o, taken, _⟩ := match_one (takes_match valid)
  have recorded : (factT, o.1) ∈ (selection.result Prod.fst Separations.drop C.1).equations := by
    simp [Selection.result, Selection.problem, Selection.equations, taken, Separations.drop, rule]
  rw [← congrArg Configuration.equations same] at recorded
  exact absurd recorded List.not_mem_nil

/-- **Its image has a predecessor**: `drop` takes `{T}` to the empty bag. -/
theorem emptyC_image_has_predecessor :
    dropReaction (([factT] : List Expr) : Multiset Expr) (dropView emptyC) :=
  ⟨(([factT] : List Expr) : Multiset Expr), 0, 0,
    ⟨Separations.drop, rfl, fun _ member => absurd member List.not_mem_nil, rfl, rfl⟩, rfl, rfl⟩

/-- **The narrowing does not lift predecessors.** -/
theorem drop_backZag_fails : ¬ BackZag dropStep dropReaction dropView := by
  intro back
  obtain ⟨C, step, _⟩ := back emptyC_image_has_predecessor
  exact emptyC_no_predecessor C step

/-- **Predecessor necessity does not pull back**: "no predecessor" holds of the empty store with
no knowledge and fails of its image. -/
theorem drop_predecessorBox_fails :
    derivedBox (span dropStep) (pb dropView (fun _ => False)) emptyC ∧
      ¬ pb dropView (derivedBox (span dropReaction) (fun _ => False)) emptyC := by
  refine ⟨(box_iff _ _ _).mpr fun C step => emptyC_no_predecessor C step, fun all => ?_⟩
  exact (box_iff _ _ _).mp all _ emptyC_image_has_predecessor

end FirstOrder

#print axioms Rho.modal_hom
#print axioms Framed.answers_diamond_iff
#print axioms Framed.answers_forwardBox_iff
#print axioms HE.graph_open
#print axioms HE.answers_diamond_iff
#print axioms HE.answers_forwardBox_iff
#print axioms PeTTa.sequential_same_modalities
#print axioms PeTTa.hyperpose_step_fails
#print axioms PeTTa.hyperpose_reach_fails
#print axioms PeTTa.hyperpose_forwardBox_fails
#print axioms FirstOrder.drop_open
#print axioms FirstOrder.drop_modal_hom
#print axioms FirstOrder.emptyC_no_predecessor
#print axioms FirstOrder.drop_backZag_fails
#print axioms FirstOrder.drop_predecessorBox_fails

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Narrowings
