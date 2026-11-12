import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.RhoChannelFragment

/-!
# The narrowing from the whole store to rho's observations

The step sees the whole store. Reading a heated store as one rho process (`narrow`) is one
observation of it; the identity observation is the whole-store view itself (`whole_store_view`). On
the channel-communication fragment:

* `narrowing_functionalBisimulation`, `narrowing_onto`: the narrowing is a functional bisimulation
  from heated stores onto rho's communication, a map of transition systems that carries runs to runs
  (`narrowing_maps_runs`) and is **open** in the sense of Joyal, Nielsen and Winskel: every rho path
  out of an image lifts (`narrowing_lifts_paths`).
* `narrowing_observes`: rho's reduction is **exactly the step observed through the narrowing**.
* `narrowing_pb_diamond`, `narrowing_pb_forwardBox`: OSLF's possibility and necessity types over rho
  pull back to the same types over the store. `narrowing_bisimilar_iff`: two heated stores are
  bisimilar exactly when their processes are.

## How unique the lifts are

* `same_narrowing_iff_same_heating`: the fibre of the narrowing over a process is **one heating
  class**: heated stores with the same process have the same bag of labels. So lifts are unique up
  to heating (`lifts_unique_up_to_heating`), and the quotient of the step by heating is rho's
  reduction on the nose (`narrowing_observes`).
* `lift_footprint`: a lift of a given redex consumes exactly the redex's components and makes exactly
  its result's components; only occurrence identities are free.
* **Not a discrete opfibration on firings.** `Controls.lifts_not_unique_on_firings`: in the
  take–make fragment, two firings from one store consume different bags and reach the same bag. On
  rho's own communication the same happens (`RhoRedexAmbiguity.rho_lifts_not_unique_on_firings`:
  a forwarder and two dropped names). A relation-valued observation cannot tell which redex fired,
  so lifts of an observed step are unique only up to the heating of their ends, and lifts of a redex
  only up to occurrence identities.

## Only where desired

The narrowing is one choice of observation. Its target is closed under parallel composition
(`RhoScopedParallelEvents.step_join`). On the ground step, a firing without predicate queries stays
admitted beside every store put beside it (`KeptBeside`) when it has no check (`unguarded_kept`,
from `Composition.positive_monotone`), and an absence-guarded one is refused beside a store holding
its pattern (`absence_guarded_not_kept`, from `Composition.guarded_union_iff`): among such firings
whose checks are none or one absence guard, `kept_iff_unguarded`. Firings with equality checks are
kept as well (`LinearTake.union_monotone`), and reads alone are not carried by the narrowing
(`RhoPeekOutside.peek_not_rho`), so being kept beside every store is not the same as being carried
by the narrowing; no theorem links `KeptBeside` to the narrowing. Absence is seen by the whole-store
view.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.NarrowingToRho

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open RhoSchema RhoQuotationClassFibres
open RhoScopedParallelInventory
open ContextualCommunicationProfiles ContextualCommunicationAdequacy
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (labels)
open Mettapedia.OSLF.Framework.DerivedModalities (pb derivedDiamond derivedForwardBox)
open HeatingBisimulation TransitionMaps RhoChannelFragment

variable {context : Ctx sig}

local instance : DecidableEq (Process context) := Classical.decEq _

/-- Heated stores: exactly the components of the process they denote, with the identity a model
of their knowledge. -/
abbrev HeatedStore (context : Ctx sig) :=
  {C : Configuration (Process context) (Occurrence context) // RhoStoreBisimulation.Heated C}

/-- The channel-communication step between heated stores. -/
def heatedStep (C C' : HeatedStore context) : Prop := ChannelStep C.1 C'.1

/-- **The narrowing**: a heated store read as one rho process. -/
def narrow (C : HeatedStore context) : Process context := observe (action context).identity C.1.present

theorem represents_narrow (C : HeatedStore context) : Represents C.1 (narrow C) := C.2

/-- **The narrowing is a functional bisimulation** onto rho's communication. -/
theorem narrowing_functionalBisimulation :
    FunctionalBisimulation (heatedStep (context := context)) RhoStep narrow := by
  refine ⟨fun {C C'} step => ?_, fun {C target} event => ?_⟩
  · obtain ⟨target, event, represented⟩ := channel_fragment_bisimulation.1 (represents_narrow C) step
    have observed : narrow C' = target := (RhoStoreBisimulation.represents_iff_heated.mp represented).2
    rw [observed]
    exact event
  · obtain ⟨after, step, represented⟩ := channel_fragment_bisimulation.2 (represents_narrow C) event
    obtain ⟨heated, observed⟩ := RhoStoreBisimulation.represents_iff_heated.mp represented
    exact ⟨⟨after, heated⟩, step, observed⟩

theorem narrowing_onto : Function.Surjective (narrow (context := context)) := by
  intro process
  obtain ⟨state, heated, observed⟩ :=
    (RhoStoreBisimulation.observe_functional_bisimulation (admitted := RhoScopedParallelEvents.core)).2.2 process
  exact ⟨⟨state, heated⟩, observed⟩

/-- **The narrowing is open**: every rho path out of the image of a heated store lifts. -/
theorem narrowing_lifts_paths {C : HeatedStore context} {target : Process context}
    (path : Relation.ReflTransGen RhoStep (narrow C) target) :
    ∃ C', Relation.ReflTransGen heatedStep C C' ∧ narrow C' = target :=
  Zag.path narrowing_functionalBisimulation.zag path C rfl

/-- **Rho's reduction is the step observed through the narrowing.** -/
theorem narrowing_observes : observed (heatedStep (context := context)) narrow = RhoStep := by
  funext y y'
  apply propext
  exact (step_eq_image narrowing_functionalBisimulation narrowing_onto y y').symm

/-- **The whole-store view is the identity observation.** -/
theorem whole_store_view : observed (heatedStep (context := context)) id = heatedStep :=
  observed_id _

/-- **The narrowing carries runs to runs.** -/
theorem narrowing_maps_runs {C C' : HeatedStore context}
    (run : Relation.ReflTransGen heatedStep C C') :
    Relation.ReflTransGen RhoStep (narrow C) (narrow C') := by
  induction run with
  | refl => exact .refl
  | tail _ step earlier => exact earlier.tail (narrowing_functionalBisimulation.zig step)

/-- **OSLF possibility types pull back along the narrowing.** -/
theorem narrowing_pb_diamond (φ : Process context → Prop) :
    pb narrow (derivedDiamond (span RhoStep) φ) =
      derivedDiamond (span (heatedStep (context := context))) (pb narrow φ) :=
  pb_diamond narrowing_functionalBisimulation φ

/-- **OSLF necessity types pull back along the narrowing.** -/
theorem narrowing_pb_forwardBox (φ : Process context → Prop) :
    pb narrow (derivedForwardBox (span RhoStep) φ) =
      derivedForwardBox (span (heatedStep (context := context))) (pb narrow φ) :=
  pb_forwardBox narrowing_functionalBisimulation φ

/-- **Bisimilarity of heated stores is bisimilarity of their processes.** -/
theorem narrowing_bisimilar_iff {C C' : HeatedStore context} :
    (theoryOf _ (heatedStep (context := context))).Bisimilar C C' ↔
      (theoryOf _ RhoStep).Bisimilar (narrow C) (narrow C') :=
  bisimilar_iff_map narrowing_functionalBisimulation

/-! ## How unique the lifts are -/

/-- **The fibre of the narrowing is one heating class.** -/
theorem same_narrowing_iff_same_heating {C D : HeatedStore context} :
    narrow C = narrow D ↔ labels label C.1.present = labels label D.1.present := by
  constructor
  · intro same
    rw [(represents_narrow C).2, (represents_narrow D).2, same]
  · intro same
    unfold narrow observe
    rw [realized_identity, same]

/-- **Lifts are unique up to heating**: two lifts of one rho step end in stores of one heating. The
step hypotheses are not used: this is `same_narrowing_iff_same_heating` read at the ends of two
lifts, and it holds for any two stores with the same narrowing. -/
theorem lifts_unique_up_to_heating {C C₁ C₂ : HeatedStore context}
    (_first : heatedStep C C₁) (_second : heatedStep C C₂) (same : narrow C₁ = narrow C₂) :
    labels label C₁.1.present = labels label C₂.1.present :=
  same_narrowing_iff_same_heating.mp same

/-- **The footprint of a lift is fixed by its redex**: a firing of a communication redex at the
identity takes the redex's components and makes its result's components. -/
theorem lift_footprint {root : ContextualCommunicationProfiles.Root RhoScopedParallelEvents.core context}
    {C : Configuration (Process context) (Occurrence context)} {selection : Selection (Occurrence context)}
    (valid : selection.Valid (action context) label (instanceRule root) C)
    (solved : (action context).Models (action context).identity
      (selection.result label (instanceRule root) C).equations) :
    labels label selection.taken.toFinset = normalized root.source ∧
      labels label selection.made.toFinset = normalized root.target := by
  have takes := PositiveResourceProjection.take_observation (action context) rfl valid solved
  have makes := PositiveResourceProjection.output_observation (action context)
    (assignment := (action context).identity) valid
  rw [realized_identity, map_identity, instance_take] at takes
  rw [realized_identity, map_identity, instance_produce] at makes
  exact ⟨takes, makes⟩

end NarrowingToRho

/-! ## Only where desired -/

namespace NarrowingToRho.Beside

open NamesOnTheStep NamesOnTheStep.IssuingControls

/-- A firing's behaviour is **kept beside** every store whose occurrences its made identities avoid
and whose knowledge has the identity solution. -/
def KeptBeside (C : Conf) (f : Fir) : Prop :=
  ∀ D : Conf, (∀ o ∈ f.selection.made, o ∉ D.present) → (∀ e ∈ D.equations, e.1 = e.2) →
    base.Admits (s := NullsOnTheStep.Composition.union C D) f

/-- An unguarded firing is kept beside every store. -/
theorem unguarded_kept {C : Conf} {f : Fir} (noChecks : f.rule.checks = []) (noQueries : f.queries = [])
    (admitted : base.Admits (s := C) f) : KeptBeside C f :=
  fun _ fresh knowledge => NullsOnTheStep.Composition.positive_monotone noChecks noQueries admitted fresh knowledge

/-- An absence-guarded firing is refused beside a store holding its pattern. -/
theorem absence_guarded_not_kept {C : Conf} {f : Fir} {p : Expr} (guard : f.rule.checks = [.absent p])
    (noQueries : f.queries = []) (admitted : base.Admits (s := C) f) : ¬ KeptBeside C f := by
  intro kept
  obtain ⟨n, unused⟩ := Infinite.exists_notMem_finset ((f.selection.made.map Prod.snd).toFinset)
  let D : Conf := ⟨[], {(p, n)}⟩
  have freshD : ∀ o ∈ f.selection.made, o ∉ D.present := by
    intro o member inD
    have same : o = (p, n) := Finset.mem_singleton.mp inD
    subst same
    exact unused (List.mem_toFinset.mpr (List.mem_map.mpr ⟨(p, n), member, rfl⟩))
  have knowledgeD : ∀ e ∈ D.equations, e.1 = e.2 := fun e member => absurd member List.not_mem_nil
  have clear := (NullsOnTheStep.Composition.guarded_union_iff guard noQueries admitted freshD knowledgeD).mp
    (kept D freshD knowledgeD)
  exact clear (p, n) (Finset.mem_singleton_self _) rfl

/-- **On the ground step, exactly the firings without a check are kept beside every store**, among
firings without predicate queries whose checks are none or one absence guard. -/
theorem kept_iff_unguarded {C : Conf} {f : Fir}
    (shape : f.rule.checks = [] ∨ ∃ p, f.rule.checks = [.absent p]) (noQueries : f.queries = [])
    (admitted : base.Admits (s := C) f) : KeptBeside C f ↔ f.rule.checks = [] := by
  constructor
  · intro kept
    rcases shape with none | ⟨p, guard⟩
    · exact none
    · exact absurd kept (absence_guarded_not_kept guard noQueries admitted)
  · intro none
    exact unguarded_kept none noQueries admitted

end NarrowingToRho.Beside

/-! ## Not a discrete opfibration on firings -/

namespace NarrowingToRho.Controls

open NamesOnTheStep NamesOnTheStep.IssuingControls
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (labels)
open HeatingBisimulation

/-- A message carrying a value. -/
def msg (v : Expr) : Expr := .app (.sym 20) v
/-- The relayer. -/
def relayer : Expr := .sym 21
def valueA : Expr := .sym 22
def valueB : Expr := .sym 23

/-- Relay: take a message and the relayer, make the message again. -/
def relay (v : Expr) : RuleInstance Expr := rule [msg v, relayer] [] [msg v]

/-- The relay rule set, one rule per value. -/
def relays : RuleSet Expr := fun r => ∃ v, r = relay v

theorem relays_takeMake : TakeMake relays := by
  rintro _ ⟨v, rfl⟩
  exact ⟨rfl, rfl⟩

def start : Conf := ⟨[], {(msg valueA, 0), (msg valueB, 0), (relayer, 0)}⟩
def throughA : Selection Occ := ⟨[(msg valueA, 0), (relayer, 0)], [], [(msg valueA, 1)]⟩
def throughB : Selection Occ := ⟨[(msg valueB, 0), (relayer, 0)], [], [(msg valueB, 1)]⟩

/-- A trivial discipline: every ground firing may issue nothing. -/
abbrev anything : Disc := fun _ _ _ _ => True

theorem throughA_valid : throughA.Valid ground Prod.fst (relay valueA) start :=
  (PredicateQueryAdmission.valid_empty_iff ground Prod.fst _ _ _).mp
    (admits_of (D := anything) (σ := (start, ∅)) (r := relay valueA) (sel := throughA) (fresh := []) (by decide) (by decide) rfl rfl rfl
      (by decide) (by decide) rfl (no_checks rfl) trivial).1

theorem throughB_valid : throughB.Valid ground Prod.fst (relay valueB) start :=
  (PredicateQueryAdmission.valid_empty_iff ground Prod.fst _ _ _).mp
    (admits_of (D := anything) (σ := (start, ∅)) (r := relay valueB) (sel := throughB) (fresh := []) (by decide) (by decide) rfl rfl rfl
      (by decide) (by decide) rfl (no_checks rfl) trivial).1

/-- **Control.** Two firings of the relay rule set from one store consume different bags and reach
stores with the same bag of labels: the bag does not determine the firing. -/
theorem lifts_not_unique_on_firings :
    TakeMake relays ∧
      ConstraintMultisetRewriting.Step ground Prod.fst (relay valueA) start
        (throughA.result Prod.fst (relay valueA) start) ∧
      ConstraintMultisetRewriting.Step ground Prod.fst (relay valueB) start
        (throughB.result Prod.fst (relay valueB) start) ∧
      labels Prod.fst (throughA.result Prod.fst (relay valueA) start).present =
        labels Prod.fst (throughB.result Prod.fst (relay valueB) start).present ∧
      labels Prod.fst throughA.taken.toFinset ≠ labels Prod.fst throughB.taken.toFinset :=
  ⟨relays_takeMake, ⟨_, throughA_valid, rfl⟩, ⟨_, throughB_valid, rfl⟩, by decide, by decide⟩

end NarrowingToRho.Controls

open NarrowingToRho in
#print axioms narrowing_functionalBisimulation
open NarrowingToRho in
#print axioms narrowing_onto
open NarrowingToRho in
#print axioms narrowing_lifts_paths
open NarrowingToRho in
#print axioms narrowing_observes
open NarrowingToRho in
#print axioms whole_store_view
open NarrowingToRho in
#print axioms narrowing_maps_runs
open NarrowingToRho in
#print axioms narrowing_pb_diamond
open NarrowingToRho in
#print axioms narrowing_pb_forwardBox
open NarrowingToRho in
#print axioms narrowing_bisimilar_iff
open NarrowingToRho in
#print axioms same_narrowing_iff_same_heating
open NarrowingToRho in
#print axioms lift_footprint
#print axioms NarrowingToRho.Beside.kept_iff_unguarded
#print axioms NarrowingToRho.Controls.lifts_not_unique_on_firings

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep
