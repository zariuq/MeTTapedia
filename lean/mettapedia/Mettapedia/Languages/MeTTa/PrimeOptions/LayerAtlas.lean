import Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra
import Mettapedia.Languages.MeTTa.LayerEffects
import Mettapedia.GSLT.Contracts.CoordinationFreedom
import Mettapedia.GSLT.Contracts.AbsenceFrontier
import Mettapedia.Machines.Cursor.GapObservation
import Mettapedia.GSLT.Logic.KnowledgeBasedPrograms
import Mettapedia.PLN.WorldModel.EvidenceSpaces
import Mettapedia.CategoryTheory.NondeterminismProbability
import Mettapedia.Languages.MeTTa.Seal.ClosedResolver
import Mettapedia.GSLT.Dynamics.PriorityFairness
import Mettapedia.Languages.MeTTa.Seal.Eliminability
import Mettapedia.Languages.MeTTa.MeTTaZeroAnswerAlgebra
import Mettapedia.Languages.MeTTa.AnnotationCapabilities
import Mettapedia.Languages.MeTTa.SpecRunObserver
import Mettapedia.PLN.WorldModel.EvidenceContracts
import Mettapedia.PLN.WorldModel.PairedSampleDispersion
import Mettapedia.GSLT.Contracts.FrontierNegation
import Mettapedia.GSLT.Contracts.ConsumptionArbitration
import Mettapedia.CategoryTheory.SchedulerResolution
import Mettapedia.GSLT.Dynamics.BoundedOvertaking
import Mettapedia.GSLT.Logic.RankedDecision

/-!
# An atlas of layer and feature combinations

The layers of a rewriting and knowledge-base language, from the space up, and
the features that are separately primitive, combine in some pairs and not in
others.  Each theorem below is one cell of the atlas: either a combination
with its laws, or an impossibility with an explicit counterexample together
with its repair.  Every cell is assembled from theorems proved in the module
that owns the concept.

| Cell | Verdict | Theorem |
|---|---|---|
| space × answers | one annotation algebra; MeTTa Zero is `K = ℕ` | `cell_space_answers` |
| space capabilities | meet needs a lattice, subtract a monus; no inverse of idempotent merge | `cell_space_capabilities` |
| answers × answers | commutative exactly for commutative annotations | `cell_answers_commutative` |
| answers × evidence | possibility composes without zero divisors | `cell_answers_possibility` |
| choice × probability | no distributive law; one monad with additive choice | `cell_choice_probability` |
| choice × weights × cost × state | per-answer tensor, except reads and writes | `cell_speculative_tensor` |
| answer cost × failed work | no recovery of charges before failure | `cell_cost_account_boundary` |
| absence × state | a negative read does not commute with a write | `cell_absence_state` |
| presence × concurrency | coordination free, and only monotone programs are | `cell_presence_coordination` |
| absence × concurrency | not confluent; frontier-stratified repair | `cell_absence_concurrency` |
| absence × absence | stratified joins need common strata | `cell_absence_joins` |
| consumption × concurrency | not confluent | `cell_consumption` |
| absence × cursors | gaps are the footprint; phantoms otherwise | `cell_absence_cursors` |
| absence × self-modification | frontier is a closed region | `cell_absence_selfModification` |
| absence × evidence | negative evidence only at a frontier | `cell_absence_evidence` |
| absence × failures × time | no perfect detector without a delay bound | `cell_absence_failures` |
| priority × fairness | strict priority starves; class fairness and epochs | `cell_priority_fairness` |
| reflection × authority | late binding forges; closed resolver or owned heads | `cell_reflection_authority` |
| self-modification × proof | certified installation is sound | `cell_selfModification_proofs` |
| knowledge × laziness | grounded inquiry never commits early | `cell_knowledge_laziness` |
| knowledge × observers | knowledge is an S5 interior | `cell_knowledge_observers` |
| evidence derivation | revision and conjunction are forced by samples | `cell_evidence_derivation` |
| marginal evidence × same-world conjunction | no recovery without joint information | `cell_evidence_correlation` |
| evidence × coordination | additive revision double counts; source-keyed revision does not | `cell_evidence_coordination` |
| saturation × multiplicity | bag saturation never quiesces; idempotent does | `cell_saturation_multiplicity` |
| authority × core | sealing is not eliminable | `cell_authority_primitive` |
| multiplicity × sets | counts are not recoverable from supports | `cell_multiplicity_primitive` |
| answers × possibility (exact) | possibility composes iff the annotation is positive; no ring is | `cell_possibility_positive` |
| ordered runs × answer readout | the readout is a monad morphism that forgets order and failed cost | `cell_spec_observer` |
| identified evidence × revision | additive revision exact iff disjoint; overlap by inclusion–exclusion | `cell_evidence_ledger` |
| dependent evidence × conjunction | exactly the Fréchet interval; independence is one point | `cell_evidence_dependence` |
| paired samples × confidence | the paired total is a sample size only for single samples | `cell_evidence_pairs` |
| reports × fusion | PLN's tensor is conditional-independence fusion; not conjunction | `cell_evidence_testimony` |
| negative evidence × growth | evidential negation monotone; Heyting negation not | `cell_negation_presence` |
| PLN deduction × screening off | exact under screening off; fails without it | `cell_pln_deduction` |
| absence × intuitionistic negation | frontier absence is Kripke negation; sound, incomplete for refinements | `cell_absence_intuitionistic` |
| absence × ownership | owners certify frontiers; only owners revoke | `cell_absence_ownership` |
| choice × probability × schedulers | envelopes at deterministic schedulers; pure choice is vacuous | `cell_choice_scheduler` |
| priority × overtaking | bounded overtaking bounds waiting; deadlines are aging | `cell_priority_overtaking` |
| consumption × arbitration | first commit wins; exclusive authority restores confluence | `cell_consumption_arbitration` |
| knowledge × well-founded tests | ranked programs are decided and have one implementation | `cell_knowledge_ranked` |
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeOptions.LayerAtlas

open scoped NNReal ENNReal
open Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra

/-! ## Space and answers -/

/-- **Space × answers**: one annotation algebra.  Weighted bind is associative
over every semiring, MeTTa Zero's multiset answers are the natural-number case,
and the set quotient forgets multiplicity. -/
theorem cell_space_answers :
    (∀ (K : Type) [Semiring K] (X Y Z : Type) (A : Ans K X) (f : X → Ans K Y) (g : Y → Ans K Z),
        Ans.bind (Ans.bind A f) g = Ans.bind A fun x => Ans.bind (f x) g) ∧
      (∀ (X Y : Type) [DecidableEq X] [DecidableEq Y] (m : Multiset X) (f : X → Multiset Y),
        Multiset.toFinsupp (m.bind f) =
          Ans.bind (Multiset.toFinsupp m) fun x => Multiset.toFinsupp (f x)) ∧
      (∀ (X : Type) (x : X), Ans.mapK supportOfCount (Ans.pure x : Ans ℕ X) =
          Ans.mapK supportOfCount (Finsupp.single x 2 : Ans ℕ X) ∧
        (Ans.pure x : Ans ℕ X) ≠ Finsupp.single x 2) :=
  ⟨fun _ _ _ _ _ A f g => Ans.bind_assoc A f g, fun _ _ _ _ m f => toFinsupp_bind m f,
    fun _ x => supportOfCount_not_injective x⟩

/-- **Space capabilities**: no operation undoes an idempotent merge; monus
undoes merging and distributes over joins for counts, and not over joins in
`ℝ≥0∞`. -/
theorem cell_space_capabilities :
    (∀ (sub : Space Presence Unit → Space Presence Unit → Space Presence Unit),
        ¬ ∀ S T, sub (S + T) T = S) ∧
      (∀ S T : Space ℕ Unit, (S + T) - T = S) ∧
      (∀ S T U : Space ℕ Unit, S * (T - U) = S * T - S * U) ∧
      (∃ S T U : Space ℝ≥0∞ Unit, S * (T - U) ≠ S * T - S * U) :=
  ⟨fun sub => no_space_sub_undoes_merge Presence.add_self (by decide) () sub,
    nat_merge_sub_cancel, nat_join_tsub, Controls.ennreal_join_tsub_fails⟩

/-- **Answers × answers**: independent choices commute exactly when their
annotations do. -/
theorem cell_answers_commutative :
    (∀ (K : Type) [CommSemiring K] (X Y Z : Type) (A : Ans K X) (B : Ans K Y)
        (f : X → Y → Ans K Z),
        Ans.bind A (fun x => Ans.bind B (f x)) = Ans.bind B fun y => Ans.bind A fun x => f x y) ∧
      Ans.bind (Finsupp.single () Controls.upper)
          (fun _ => Ans.bind (Finsupp.single () Controls.lower) fun _ => Ans.pure ()) ≠
        Ans.bind (Finsupp.single () Controls.lower)
          (fun _ => Ans.bind (Finsupp.single () Controls.upper) fun _ => Ans.pure ()) :=
  ⟨fun _ _ _ _ _ A B f => Ans.bind_comm A B f, Controls.bind_not_comm_matrix⟩

open Mettapedia.PLN.WorldModel.EvidenceSpaces in
/-- **Answers × evidence**: possibility composes for answers weighted by
evidence counts; a zero divisor, as in the coordinatewise product, breaks it. -/
theorem cell_answers_possibility :
    (∀ (X Y : Type) [DecidableEq Y] (A : Ans (Evidence ℕ) X) (f : X → Ans (Evidence ℕ) Y),
        (Ans.bind A f).support = A.support.biUnion fun x => (f x).support) ∧
      (Ans.bind (Finsupp.single () ((1, 0) : ℕ × ℕ))
          (fun _ => Finsupp.single () ((0, 1) : ℕ × ℕ))).support = ∅ :=
  ⟨fun _ _ _ A f => support_bind_evidence A f,
    Controls.support_bind_fails_with_zero_divisors.1⟩

/-! ## Choice and probability -/

open Mettapedia.CategoryTheory.NondeterminismProbability in
/-- **Choice × probability**: no distributive law of distributions over sets;
in one weighted answer monad both choices are algebraic, probabilistic choice
is idempotent, nondeterministic choice is additive, and possibility is a
readout that identifies them. -/
theorem cell_choice_probability :
    IsEmpty (DistributiveLaw Point) ∧
      (∀ (X Y : Type) (p : ℝ≥0) (A B : Ans ℝ≥0 X) (f : X → Ans ℝ≥0 Y),
        Ans.bind (convex p A B) f = convex p (Ans.bind A f) (Ans.bind B f)) ∧
      (∀ (X : Type) (p : ℝ≥0), p ≤ 1 → ∀ A : Ans ℝ≥0 X, convex p A A = A) ∧
      (∀ (X : Type) (x : X), (Ans.pure x : Ans ℝ≥0 X) + Ans.pure x ≠ Ans.pure x) ∧
      (∀ (X : Type) [DecidableEq X] (p : ℝ≥0), 0 < p → p < 1 → ∀ A B : Ans ℝ≥0 X,
        (convex p A B).support = (A + B).support) :=
  ⟨no_distributiveLaw, fun _ _ p A B f => convex_bind p A B f,
    fun _ _ le A => convex_idem le A, fun _ x => choice_not_idem x,
    fun _ _ _ pos lt A B => support_convex pos lt A B⟩

/-! ## The speculative layer -/

open Mettapedia.Languages.MeTTa.LayerEffects in
/-- **Choice × weights × cost × state** in the per-answer speculative readout:
choice commutes with cost, weights and writes, costs commute, and a write does
not commute with a read. This does not identify operational histories. -/
theorem cell_speculative_tensor :
    (∀ (K : Type) [CommSemiring K] (C : Type) [CommMonoid C] (W X : Type) (cost : C)
        (first second : Spec K C W X),
        Spec.andThen (Spec.tick cost) (Spec.choose first second) =
          Spec.choose (Spec.andThen (Spec.tick cost) first) (Spec.andThen (Spec.tick cost) second)) ∧
      (∀ (K : Type) [CommSemiring K] (C : Type) [CommMonoid C] (W X : Type) (next : W)
        (first second : Spec K C W X),
        Spec.andThen (Spec.put next) (Spec.choose first second) =
          Spec.choose (Spec.andThen (Spec.put next) first) (Spec.andThen (Spec.put next) second)) ∧
      (∀ (K : Type) [CommSemiring K] (C : Type) [CommMonoid C] (W X : Type) (k : K) (cost : C)
        (m : Spec K C W X),
        Spec.andThen (Spec.tick cost) (Spec.weight k m) = Spec.weight k (Spec.andThen (Spec.tick cost) m)) ∧
      (∀ (K : Type) [CommSemiring K] (C : Type) [CommMonoid C] (W : Type) (first second : C),
        Spec.andThen (Spec.tick first) (Spec.tick second) =
          (Spec.andThen (Spec.tick second) (Spec.tick first) : Spec K C W Unit)) ∧
      Spec.andThen (Spec.put true) (Spec.get : Controls.BoolSpec Bool) ≠
        Spec.bind Spec.get (fun world => Spec.andThen (Spec.put true) (Spec.pure world)) :=
  ⟨fun _ _ _ _ _ _ cost first second => Spec.choose_tick cost first second,
    fun _ _ _ _ _ _ next first second => Spec.choose_put next first second,
    fun _ _ _ _ _ _ k cost m => Spec.weight_tick k cost m,
    fun _ _ _ _ _ first second => Spec.tick_tick first second,
    Controls.put_get_not_comm⟩

open Mettapedia.Languages.MeTTa.LayerEffects in
/-- **Answer cost × failed work**: cost in successful answers erases prior
charges on failure and cannot supply a complete paid-work account. -/
theorem cell_cost_account_boundary :
    ∀ (K : Type) [CommSemiring K] (C : Type) [CommMonoid C] [Nontrivial C]
      (W X : Type),
      (∀ cost : C, Spec.andThen (Spec.tick cost : Spec K C W Unit)
        (Spec.fail : Spec K C W X) = Spec.fail) ∧
      ¬ ∃ observe : Spec K C W X → C, ∀ cost : C,
        observe (Spec.andThen (Spec.tick cost) Spec.fail) = cost :=
  fun _ _ _ _ _ _ _ => ⟨Spec.tick_fail, Spec.no_failed_cost_recovery⟩

open Mettapedia.Languages.MeTTa.LayerEffects in
/-- **Absence × state**: a negative read of a key does not commute with a write
into it. -/
theorem cell_absence_state :
    Spec.andThen (Spec.put (Finsupp.single () 1)) (Spec.absentAt () : Controls.UnitSpec Unit) ≠
      Spec.andThen (Spec.absentAt ()) (Spec.put (Finsupp.single () 1)) :=
  Controls.put_absent_not_comm

/-! ## Presence, absence and coordination -/

open Mettapedia.GSLT.Contracts.Coordination in
/-- **Presence × concurrency (CALM)**: presence-only programs compute their
closure without coordination, and an inflationary program that computes a
function without coordination computes a monotone one. -/
theorem cell_presence_coordination :
    (∀ (α ι : Type) [CompleteLattice α] (rules : ι → α → α), PresenceOnly rules →
        CoordinationFree rules (closure rules)) ∧
      (∀ (α ι : Type) [CompleteLattice α] (rules : ι → α → α),
        (∀ rule store, store ≤ rules rule store) →
        (∀ store, ∃ schedule, Quiescent rules (run rules store schedule)) →
        ∀ outcome : α → α, CoordinationFree rules outcome → Monotone outcome) :=
  ⟨fun _ _ _ _ presence => coordinationFree_of_presenceOnly presence,
    fun _ _ _ _ inflationary terminates _ free =>
      monotone_of_coordinationFree inflationary terminates free⟩

open Mettapedia.GSLT.Contracts.Coordination in
/-- **Absence × concurrency**: an absence rule makes two schedules disagree, is
not monotone, and makes replicas agree on a store no single node reaches; a
frontier between strata restores determinacy, and is necessary. -/
theorem cell_absence_concurrency :
    (Quiescent Controls.rules (run Controls.rules ∅ [.addP, .absentPAddsQ]) ∧
        Quiescent Controls.rules (run Controls.rules ∅ [.absentPAddsQ, .addP]) ∧
        run Controls.rules ∅ [.addP, .absentPAddsQ] ≠ run Controls.rules ∅ [.absentPAddsQ, .addP]) ∧
      ¬ Monotone (Controls.rules .absentPAddsQ) ∧
      (∀ (L U ι κ : Type) [CompleteLattice L] [CompleteLattice U] (lower : ι → L → L)
        (upper : κ → L → U → U), Stratified lower upper →
        ∀ (start : L × U) (events : List (ι ⊕ κ)), RespectsFrontier lower upper start events →
          Quiescent lower (stratumRun lower upper start events).1 →
          Quiescent (fun rule => upper rule (stratumRun lower upper start events).1)
            (stratumRun lower upper start events).2 →
          stratumRun lower upper start events =
            (closure lower start.1, closure (fun rule => upper rule (closure lower start.1)) start.2)) ∧
      ¬ RespectsFrontier Controls.lowerAddP Controls.upperAbsentP (False, False) [.inr (), .inl ()] :=
  ⟨Controls.absence_not_confluent, Controls.absence_not_monotone,
    fun _ _ _ _ _ _ _ _ stratified start events respects quietLow quietHigh =>
      stratified_determinate stratified start events respects quietLow quietHigh,
    Controls.frontier_necessary.2.1⟩

open Mettapedia.GSLT.Contracts.Coordination in
/-- **Absence × absence**: the presence bubble and the stratified bubble over
fixed strata are closed under joins; joining stratified programs with opposite
strata gives a cycle through absence with two quiescent outcomes. -/
theorem cell_absence_joins :
    (∀ (α ι ι' : Type) [CompleteLattice α] (rules : ι → α → α) (rules' : ι' → α → α),
        PresenceOnly rules → PresenceOnly rules' → Confluent (Sum.elim rules rules')) ∧
      (∀ (L U ι κ ι' κ' : Type) [CompleteLattice L] [CompleteLattice U]
        (lower : ι → L → L) (upper : κ → L → U → U) (lower' : ι' → L → L) (upper' : κ' → L → U → U),
        Stratified lower upper → Stratified lower' upper' →
          Stratified (Sum.elim lower lower') (Sum.elim upper upper')) ∧
      (run Controls.cycleRules ∅ [true, false] = {Controls.Fact.q} ∧
        run Controls.cycleRules ∅ [false, true] = {Controls.Fact.p} ∧
        Quiescent Controls.cycleRules {Controls.Fact.q} ∧
        Quiescent Controls.cycleRules {Controls.Fact.p}) :=
  ⟨fun _ _ _ _ _ _ first second => join_confluent first second,
    fun _ _ _ _ _ _ _ _ _ _ _ _ first second => stratified_join first second,
    Controls.cycle_through_absence⟩

open Mettapedia.GSLT.Contracts.Coordination in
/-- **Consumption × concurrency**: two consumers of one token are not
confluent. -/
theorem cell_consumption : ¬ Confluent Controls.consumers :=
  Controls.consumption_not_confluent

/-! ## Absence at the backend and in the world -/

open Mettapedia.Machines.Cursor.GapObservation in
/-- **Absence × cursors**: every adaptive trie-cursor program replays in any
space that validates its footprint of gaps and children, the footprint is valid
where it was taken, and a footprint of positive reads alone misses phantoms. -/
theorem cell_absence_cursors :
    (∀ (β R : Type) [DecidableEq β] [LinearOrder β] (space other : Finset (List β))
        (program : SeekProgram β R),
        (∀ observation ∈ program.footprint space, SeekProgram.ObservationValid other observation) →
          program.run other = program.run space) ∧
      (∀ (β R : Type) [DecidableEq β] [LinearOrder β] (space : Finset (List β))
        (program : SeekProgram β R),
        ∀ observation ∈ program.footprint space, SeekProgram.ObservationValid space observation) ∧
      (Controls.absenceProbe.run Controls.before = true ∧
        Controls.absenceProbe.run Controls.after = false) :=
  ⟨fun _ _ _ _ _ _ program valid => (SeekProgram.run_eq_of_valid program valid).1,
    fun _ _ _ _ space program => SeekProgram.valid_self space program,
    ⟨Controls.probe_controls.1, Controls.probe_controls.2.1⟩⟩

open Mettapedia.GSLT.Contracts.AbsenceFrontier in
/-- **Absence × self-modification**: in a space whose executables create
executables, absence at a frontier is final, and a frontier is exactly a
closed region without matches; a pending producer flips a snapshot absence. -/
theorem cell_absence_selfModification :
    (∀ (Atom Pattern : Type) (model : SpaceModel Atom Pattern) (pattern : Pattern)
        (space later : Set Atom), Absent model pattern space → Frontier model pattern space →
        Relation.ReflTransGen (Step model) space later →
          Absent model pattern later ∧ Frontier model pattern later) ∧
      (∀ (Atom Pattern : Type) (model : SpaceModel Atom Pattern) (pattern : Pattern)
        (space : Set Atom),
        (Absent model pattern space ∧ Frontier model pattern space) ↔
          ∃ region : Set Atom, space ⊆ region ∧ ClosedRegion model region ∧
            Absent model pattern region) ∧
      (Absent Controls.items () {.producer, .fact} ∧ ¬ Absent Controls.items () {.fact, .target}) :=
  ⟨fun _ _ model _ _ _ absent frontier reaches => absent_of_reaches model absent frontier reaches,
    fun _ _ model pattern space => frontier_iff_closedRegion model pattern space,
    ⟨Controls.snapshot_absence_flips.1, Controls.snapshot_absence_flips.2.1⟩⟩

open Mettapedia.GSLT.Contracts.AbsenceFrontier in
/-- **Absence × evidence**: negative evidence read at a frontier is never
contradicted; read from a snapshot it can be. -/
theorem cell_absence_evidence :
    (∀ (Atom Pattern : Type) (model : SpaceModel Atom Pattern) (pattern : Pattern)
        (space : Set Atom), Absent model pattern space → Frontier model pattern space →
        ∀ later, Relation.ReflTransGen (Step model) space later →
          ∀ atom ∈ later, ¬ model.fits pattern atom) ∧
      (Absent Controls.items () {.producer, .fact} ∧
        ∃ later, Relation.ReflTransGen (Step Controls.items) {.producer, .fact} later ∧
          ∃ atom ∈ later, Controls.items.fits () atom) :=
  ⟨fun _ _ model _ _ absent frontier => negative_evidence_sound_at_frontier model absent frontier,
    Controls.negative_evidence_unsound_without_frontier⟩

open Mettapedia.GSLT.Contracts.AbsenceFrontier in
/-- **Absence × failures × time**: without a delay bound no complete detector
is accurate; a delay bound is a frontier in time that makes one perfect. -/
theorem cell_absence_failures :
    (∀ detector : Detector, Complete detector → ¬ Accurate detector fun _ => True) ∧
      (∀ bound, Complete (boundedDelay bound) ∧
        Accurate (boundedDelay bound) fun execution => ∀ arrival, execution = some arrival →
          arrival ≤ bound) :=
  ⟨no_perfect_detector, bounded_delay_detector⟩

/-! ## Priority -/

open Mettapedia.GSLT.Dynamics.PriorityFairness in
/-- **Priority × fairness**: least-first scheduling with work regenerated ahead
of an item is not weakly fair; with no arrivals ahead an item fires within a
bound; fairness within a class and epochs are the repairs. -/
theorem cell_priority_fairness :
    ¬ Controls.WeaklyFair Controls.starvingRun ∧
      (∀ (α : Type) [LinearOrder α] (run : Run α) (start : ℕ) (x : α), x ∈ run.pending start →
        (∀ t, start ≤ t → ∀ y ∈ run.arrivals t, x < y) →
        ∃ t, start ≤ t ∧ t ≤ start + (run.ahead start x).card ∧ run.fired t = x) ∧
      (∀ (Key : Type) [LinearOrder Key] (run : Run (Lex (ℕ × Key))) (start : ℕ)
        (x : Lex (ℕ × Key)), x ∈ run.pending start →
        (∀ t, ∀ y ∈ run.arrivals t, ∀ z ∈ run.pending t, (ofLex z).1 < (ofLex y).1) →
        ∃ t, start ≤ t ∧ run.fired t = x) :=
  ⟨Controls.priority_not_weakly_fair, fun _ _ run _ _ pending behind => run.fires_within pending behind,
    fun _ _ run _ _ pending stamped => epoch_fires_within run pending stamped⟩

/-! ## Reflection, authority and proof -/

open Mettapedia.Languages.MeTTa.Seal.ClosedResolver in
/-- **Reflection × authority**: an added equation for a kernel helper makes the
genuine step mint any claim; a closed resolver, or ownership of the helper's
head, keeps the kernel sound under every extension. -/
theorem cell_reflection_authority :
    (∀ (Head Arg Result : Type) [DecidableEq Head] [DecidableEq Arg]
        (space : Multiset (Equation Head Arg Result)) (helper : Head) (input : Arg) (claim : Result),
        claim ∈ step (space + {⟨helper, input, claim⟩}) helper input) ∧
      (∀ (Head Arg Result Module : Type) [DecidableEq Head] [DecidableEq Arg]
        (derivable : Result → Prop) (owner : Head → Option Module) (kernel module : Module),
        module ≠ kernel → ∀ helper, owner helper = some kernel →
        ∀ space : Multiset (Equation Head Arg Result), Sound derivable space helper →
        ∀ extension, Authorized owner module extension → Sound derivable (space + extension) helper) ∧
      ¬ Sound Controls.derivable (Controls.genuine + {⟨.stepClaim, (), .forged⟩}) .stepClaim ∧
      ¬ Authorized Controls.owner false
        ({⟨.stepClaim, (), .forged⟩} : Multiset (Equation Controls.HelperName Unit Controls.Claim)) :=
  ⟨fun _ _ _ _ _ space helper input claim => late_bound_forgery space helper input claim,
    fun _ _ _ _ _ _ _ _ _ _ other _ owned _ sound extension authorized =>
      owned_sound other owned sound extension authorized,
    Controls.forgery.2, Controls.forgery_unauthorized⟩

open Mettapedia.Languages.MeTTa.Seal.ClosedResolver in
/-- **Self-modification × proof**: a kernel may extend its own helpers when
each new equation carries a derivability certificate. -/
theorem cell_selfModification_proofs :
    (∀ (Head Arg Result : Type) [DecidableEq Head] [DecidableEq Arg]
        (derivable : Result → Prop) (helper : Head) (space : Multiset (Equation Head Arg Result)),
        Sound derivable space helper → ∀ extension, Certified derivable helper extension →
          Sound derivable (space + extension) helper) ∧
      Sound Controls.derivable (Controls.genuine + {⟨.stepClaim, (), .reflA⟩}) .stepClaim ∧
      ¬ Certified Controls.derivable .stepClaim
        ({⟨.stepClaim, (), .forged⟩} : Multiset (Equation Controls.HelperName Unit Controls.Claim)) :=
  ⟨fun _ _ _ _ _ _ _ _ sound extension certified => certified_sound sound extension certified,
    Controls.certified_install_sound, Controls.forgery_uncertified⟩

/-! ## Knowledge -/

open Mettapedia.GSLT.KripkeTruth Mettapedia.GSLT.KnowledgeBasedPrograms in
/-- **Knowledge × laziness**: every finite stage of the grounded inquiry is
below every implementation; a program can have none, exactly one, or two
implementations; and an inquiry can decide every act at a finite stage
without any stage deciding all. -/
theorem cell_knowledge_laziness :
    (∀ (Judgment Base : Type) (system : System Judgment Base) (baseValue : Base → Bool),
        BaseAgrees system baseValue → ∀ protocol, IsImplementation system baseValue protocol →
        ∀ n, (system.stage n).Le (toValuation protocol)) ∧
      (¬ ∃ protocol, IsImplementation (Examples.single.system Examples.Liar.program)
        Examples.single.baseValue protocol) ∧
      (IsImplementation (Examples.single.system Examples.Teller.program) Examples.single.baseValue
          (fun _ => true) ∧
        IsImplementation (Examples.single.system Examples.Teller.program) Examples.single.baseValue
          (fun _ => false)) ∧
      (∀ other, IsImplementation (Examples.Ask.frame.system Examples.Ask.program)
        Examples.Ask.frame.baseValue other → other = Examples.Ask.protocol) ∧
      ((∀ n, n ∈ Examples.Relay.system.least.holds) ∧
        ∀ k, ∃ n, n ∉ (Examples.Relay.system.stage k).holds) :=
  ⟨fun _ _ system _ agrees _ implements n => stage_sound system agrees implements n,
    Examples.Liar.no_implementation, Examples.Teller.two_implementations,
    Examples.Ask.unique_implementation, Examples.Relay.never_ends⟩

open Mettapedia.GSLT.KnowledgeBasedPrograms in
/-- **Knowledge × observers**: an observer's knowledge is the interior of its
partition, with the S5 laws. -/
theorem cell_knowledge_observers :
    ∀ (World : Type) (observes : Setoid World) (proposition : Set World),
      knows observes proposition ⊆ proposition ∧
        knows observes (knows observes proposition) = knows observes proposition ∧
        (knows observes proposition)ᶜ ⊆ knows observes (knows observes proposition)ᶜ :=
  fun _ observes proposition =>
    ⟨knows_le observes proposition, knows_knows observes proposition,
      not_knows_le_knows_not_knows observes proposition⟩

/-! ## Evidence -/

open Mettapedia.PLN.WorldModel.EvidenceSpaces in
/-- **Evidence derivation**: pooling samples is revision and pairing samples is
the paired product, both forced; strength is multiplicative over conjunction;
conditioning commutes with revision and satisfies Bayes' rule in counts. -/
theorem cell_evidence_derivation :
    (∀ (W : Type) (φ : W → Bool) (first second : Multiset W),
        ofSamples φ (first + second) = ofSamples φ first + ofSamples φ second) ∧
      (∀ (W V : Type) (φ : W → Bool) (ψ : V → Bool) (first : Multiset W) (second : Multiset V),
        ofSamples (fun pair => φ pair.1 && ψ pair.2) (first ×ˢ second) =
          ofSamples φ first * ofSamples ψ second) ∧
      (∀ op : Evidence ℕ → Evidence ℕ → Evidence ℕ,
        (∀ first second : Multiset Bool,
          ofSamples (fun pair : Bool × Bool => pair.1 && pair.2) (first ×ˢ second) =
            op (ofSamples (fun b => b) first) (ofSamples (fun b => b) second)) →
        op = (· * ·)) ∧
      (∀ a b : Evidence ℝ≥0, Evidence.strength (a * b) = Evidence.strength a * Evidence.strength b) ∧
      (∀ (W : Type) (φ event : W → Bool) (samples : Multiset W),
        (ofSamples φ (condition event samples)).pos = (ofSamples event (condition φ samples)).pos) :=
  ⟨fun _ φ first second => ofSamples_add φ first second,
    fun _ _ φ ψ first second => ofSamples_product φ ψ first second,
    fun op paired => conjunction_unique op paired,
    fun a b => Evidence.strength_mul a b,
    fun _ φ event samples => condition_pos_symm φ event samples⟩

open Mettapedia.PLN.WorldModel.EvidenceSpaces in
/-- **Marginal evidence × same-world conjunction**: pairing arbitrary sample
bags is sound, but marginal count pairs do not determine joint observations. -/
theorem cell_evidence_correlation :
    ¬ ∃ op : Evidence ℕ → Evidence ℕ → Evidence ℕ,
      ∀ (samples : Multiset Bool) (φ ψ : Bool → Bool),
        ofSamples (fun world => φ world && ψ world) samples =
          op (ofSamples φ samples) (ofSamples ψ samples) :=
  no_same_world_conjunction_from_marginals

open Mettapedia.PLN.WorldModel.EvidenceSpaces in
/-- **Evidence × coordination**: additive revision double counts a duplicated
copy; revision keyed by source and merged by maximum is idempotent and
commutative, and counts each source's latest evidence once. -/
theorem cell_evidence_coordination :
    (sourceReadout ((fun _ : Unit => (Evidence.positive : Evidence ℕ)) + fun _ => Evidence.positive) ≠
        sourceReadout (fun _ : Unit => (Evidence.positive : Evidence ℕ))) ∧
      (∀ (Source : Type) (state : Source → Evidence ℕ), sourceMerge state state = state) ∧
      (∀ (Source : Type) (first second : Source → Evidence ℕ),
        sourceMerge first second = sourceMerge second first) ∧
      (∀ (Source : Type) [Fintype Source] (history : Source → ℕ → Evidence ℕ),
        (∀ source, Monotone (history source)) → ∀ firstTime secondTime : Source → ℕ,
        sourceReadout (sourceMerge (fun source => history source (firstTime source))
            (fun source => history source (secondTime source))) =
          ∑ source, history source (max (firstTime source) (secondTime source))) :=
  ⟨additive_merge_double_counts.1, fun _ state => sourceMerge_idempotent state,
    fun _ first second => sourceMerge_comm first second,
    fun _ _ history grows firstTime secondTime =>
      readout_sourceMerge history grows firstTime secondTime⟩

/-- **Saturation × multiplicity**: re-deriving a delta is a fixed point over an
idempotent merge, and over counts only for the empty delta. -/
theorem cell_saturation_multiplicity :
    (∀ (K Key : Type) [IdemSemiring K] (S Δ : Space K Key), S + Δ + Δ = S + Δ) ∧
      (∀ (Key : Type) (S Δ : Space ℕ Key), S + Δ = S ↔ Δ = 0) :=
  ⟨fun _ _ _ S Δ => idem_rederive_fixed S Δ, fun _ S Δ => nat_rederive_fixed_iff S Δ⟩

/-! ## Primitive layers already settled in the tree -/

/-- **Authority × core**: sealing is not eliminable from a transparent core. -/
theorem cell_authority_primitive :
    IsEmpty Mettapedia.Languages.MeTTa.Seal.Eliminability.SealElimination :=
  Mettapedia.Languages.MeTTa.Seal.Eliminability.isEmpty_sealElimination

open Mettapedia.OSLF.MeTTaIL.Syntax in
/-- **Multiplicity × sets**: answer counts are not a function of the support. -/
theorem cell_multiplicity_primitive (answer : Pattern) :
    ¬ ∃ recover : Finset Pattern → Multiset Pattern,
        ∀ space : Multiset Pattern,
          recover space.toFinset =
            Mettapedia.Languages.MeTTa.MeTTaZero.queryAll
              (Mettapedia.Languages.MeTTa.MeTTaZero.structuralModel fun _ => 0) space :=
  Mettapedia.Languages.MeTTa.MeTTaZeroAnswerAlgebra.no_support_recovers_queryAll answer

/-! ## Observation contracts, absence, scheduling and consumption -/

open Mettapedia.Languages.MeTTa.AnnotationCapabilities in
/-- **Answers × possibility, exactly**: possibility composes for all answers if
and only if the annotation semiring is positive, and no nontrivial ring is
positive. -/
theorem cell_possibility_positive :
    (∀ (K : Type) [Semiring K], (∀ (A : Ans K Bool) (f : Bool → Ans K Unit),
        (Ans.bind A f).support = A.support.biUnion fun x => (f x).support) ↔ Positive K) ∧
      ¬ Positive ℤ ∧ Positive (Mettapedia.PLN.WorldModel.EvidenceSpaces.Evidence ℕ) ∧
      ¬ Positive (ℕ × ℕ) :=
  ⟨fun _ _ => support_bind_iff_positive, not_positive_of_ring, positive_evidence, not_positive_pair⟩

open Mettapedia.Languages.MeTTa.SpecRunObserver in
/-- **Ordered runs × answer readout**: the speculative readout observes ordered
runs as a monad morphism and forgets order and the cost of failed branches. -/
theorem cell_spec_observer :
    (∀ (C W X Y : Type) [CommMonoid C] (m : Ordered C W X) (f : X → Ordered C W Y),
        observeRun (Ordered.bind m f) =
          Mettapedia.Languages.MeTTa.LayerEffects.Spec.bind (observeRun m) fun x => observeRun (f x)) ∧
      (∀ (C W X : Type) (world : W) (cheap expensive : C),
        observe ([(none, world, cheap)] : List (Option X × W × C)) =
          observe ([(none, world, expensive)] : List (Option X × W × C))) :=
  ⟨fun _ _ _ _ _ m f => observe_bind m f,
    fun _ _ _ world cheap expensive => Controls.observe_forgets_failed_cost world cheap expensive⟩

open Mettapedia.PLN.WorldModel.EvidenceSpaces Mettapedia.PLN.WorldModel.EvidenceContracts in
/-- **Identified evidence × revision**: additive revision is exact exactly for
disjoint ledgers; overlap revision subtracts the evidence of the intersection;
source-keyed maximum is ledger union under per-source nesting and under-counts
otherwise. -/
theorem cell_evidence_ledger :
    (∀ (Id W : Type) [DecidableEq Id] (world : Id → W) (φ : W → Bool) (first second : Finset Id),
        ledgerEvidence world φ first + ledgerEvidence world φ second =
            ledgerEvidence world φ (first ∪ second) ↔ Disjoint first second) ∧
      (∀ (Id W : Type) [DecidableEq Id] (world : Id → W) (φ : W → Bool) (first second : Finset Id),
        ledgerEvidence world φ (first ∪ second) =
          ledgerEvidence world φ first + ledgerEvidence world φ second -
            ledgerEvidence world φ (first ∩ second)) ∧
      (∀ (Id W : Type) [DecidableEq Id] (world : Id → W) (φ : W → Bool) (first second : Finset Id),
        ledgerEvidence world φ (first ∪ second) ≤
          ledgerEvidence world φ first + ledgerEvidence world φ second) ∧
      ledgerEvidence (fun _ : Fin 2 => ()) (fun _ => true) ({0} ∪ {1}) = ⟨2, 0⟩ ∧
      sourceReadout (sourceMerge
        (fun src : Unit => ledgerEvidence (fun _ : Fin 2 => ()) (fun _ => true)
          (bySource (fun _ => ()) {0} src))
        (fun src : Unit => ledgerEvidence (fun _ : Fin 2 => ()) (fun _ => true)
          (bySource (fun _ => ()) {1} src))) = ⟨1, 0⟩ :=
  ⟨fun _ _ _ world φ first second => additive_revision_exact_iff_disjoint world φ first second,
    fun _ _ _ world φ first second => ledgerEvidence_union world φ first second,
    fun _ _ _ world φ first second => (unknown_overlap_bounds world φ first second).2,
    Controls.sourceMerge_undercounts.1, Controls.sourceMerge_undercounts.2⟩

open Mettapedia.PLN.WorldModel.EvidenceContracts in
/-- **Dependent evidence × conjunction**: the conjunction counts compatible with
marginal counts on one bag are exactly the Fréchet interval, and the
independence product lies in it. -/
theorem cell_evidence_dependence :
    (∀ n a b c : ℕ, (∃ bag : Multiset (Bool × Bool), Multiset.card bag = n ∧
        count bag Prod.fst = a ∧ count bag Prod.snd = b ∧ count bag (fun w => w.1 && w.2) = c) ↔
          a ≤ n ∧ b ≤ n ∧ a + b ≤ c + n ∧ c ≤ a ∧ c ≤ b) ∧
      (∀ n a b : ℕ, a ≤ n → b ≤ n → n * a + n * b ≤ a * b + n * n ∧ a * b ≤ n * a ∧ a * b ≤ n * b) :=
  ⟨conjunction_counts_iff, fun _ _ _ ha hb => independence_within_frechet ha hb⟩

open Mettapedia.PLN.WorldModel.PairedSampleDispersion in
/-- **Paired samples × confidence**: the variance of the paired count is the
joint-sample variance plus a nonnegative excess, which vanishes for interior
probabilities exactly when both bags hold one sample. -/
theorem cell_evidence_pairs :
    (∀ (p q : ℝ) (n m : ℕ), pairedVariance p q n m =
        jointVariance (p * q) (n * m) +
          n * m * (p * q) * ((m - 1) * q * (1 - p) + (n - 1) * p * (1 - q))) ∧
      (∀ (p q : ℝ), 0 < p → p < 1 → 0 < q → q < 1 → ∀ n m : ℕ, 1 ≤ n → 1 ≤ m →
        (pairedVariance p q n m = jointVariance (p * q) (n * m) ↔ n = 1 ∧ m = 1)) :=
  ⟨fun p q n m => paired_variance p q n m,
    fun _ _ hp hp1 hq hq1 _ _ hn hm => paired_variance_eq_joint_iff hp hp1 hq hq1 hn hm⟩

open Mettapedia.PLN.WorldModel.EvidenceSpaces Mettapedia.PLN.WorldModel.EvidenceContracts in
/-- **Reports × fusion**: PLN's binary-evidence tensor is the coordinatewise
fusion of likelihood evidence; its strength is the posterior under conditional
independence and a uniform prior; its zero divisor is total conflict; fusing
posteriors counts a non-uniform prior twice; and it is not the deduction direct
path. -/
theorem cell_evidence_testimony :
    (∀ x y : Mettapedia.PLN.Evidence.BinaryEvidence,
        toPaired (x * y) = fuse (toPaired x) (toPaired y)) ∧
      (∀ (c : ℝ) (first second : Bool → Bool → ℝ), c ≠ 0 → Stochastic first → Stochastic second →
        Evidence.strength (fuse (firstReport (fun _ => c) first second)
            (secondReport (fun _ => c) first second)) =
          ciJoint (fun _ => c) first second true true true /
            (ciJoint (fun _ => c) first second true true true +
              ciJoint (fun _ => c) first second false true true)) ∧
      fuse (⟨1, 0⟩ : Evidence ℕ) ⟨0, 1⟩ = 0 ∧
      Evidence.strength (jointReport Controls.skewedPrior Controls.coinReport Controls.coinReport) =
          3 / 4 ∧
      Evidence.strength (fuse (firstReport Controls.skewedPrior Controls.coinReport Controls.coinReport)
          (secondReport Controls.skewedPrior Controls.coinReport Controls.coinReport)) = 9 / 10 ∧
      Evidence.strength (fuse (⟨1, 1⟩ : Evidence ℚ) ⟨1, 1⟩) = 1 / 2 ∧
      Evidence.strength ((⟨1, 1⟩ : Evidence ℚ) * ⟨1, 1⟩) = 1 / 4 :=
  ⟨toPaired_tensor, fun _ first second hc s1 s2 => strength_fuse_uniform hc first second s1 s2,
    fuse_total_conflict, Controls.prior_counted_twice.1, Controls.prior_counted_twice.2,
    Controls.fuse_not_direct_path.1, Controls.fuse_not_direct_path.2⟩

open Mettapedia.PLN.WorldModel.EvidenceContracts in
/-- **Negative evidence × growth**: evidential negation and the truth-order
connectives are monotone in the information order, so they stay presence-only;
intuitionistic negation is not monotone on PLN's evidence frame. -/
theorem cell_negation_presence :
    (∀ a b : Mettapedia.PLN.WorldModel.EvidenceSpaces.Evidence ℕ, a ≤ b → against a ≤ against b) ∧
      (∀ a a' b b' : Mettapedia.PLN.WorldModel.EvidenceSpaces.Evidence ℕ, a ≤ a' → b ≤ b' →
        tmeet a b ≤ tmeet a' b' ∧ tjoin a b ≤ tjoin a' b') ∧
      ¬ Monotone fun a : Mettapedia.PLN.Evidence.BinaryEvidence => a ⇨ ⊥ :=
  ⟨fun _ _ le => against_mono le, fun _ _ _ _ ha hb => ⟨tmeet_mono ha hb, tjoin_mono ha hb⟩,
    binaryEvidence_hnot_not_monotone⟩

open Mettapedia.PLN.WorldModel.EvidenceContracts in
/-- **PLN deduction × screening off**: exact when `C` is screened off from `A`
by `B` in the counts; without screening off the formula gives `1/4` where the
true frequency is `0`. -/
theorem cell_pln_deduction :
    (∀ (W : Type) (bag : Multiset W) (A B C : W → Bool),
      count bag (fun w => A w && B w && C w) * count bag B =
          count bag (fun w => A w && B w) * count bag (fun w => B w && C w) →
      count bag (fun w => A w && !B w && C w) * count bag (fun w => !B w) =
          count bag (fun w => A w && !B w) * count bag (fun w => !B w && C w) →
      count bag A ≠ 0 → count bag B ≠ 0 → count bag (fun w => !B w) ≠ 0 →
      (count bag (fun w => A w && C w) : ℝ) / count bag A =
        (count bag (fun w => A w && B w) / count bag A : ℝ) *
            (count bag (fun w => B w && C w) / count bag B) +
          (1 - (count bag (fun w => A w && B w) / count bag A : ℝ)) *
            Mettapedia.PLN.RuleFamilies.FirstOrder.PLNDeduction.complementConditionalFromMarginal
              (count bag B / Multiset.card bag) (count bag C / Multiset.card bag)
              (count bag (fun w => B w && C w) / count bag B)) ∧
      count Controls.unscreened (fun w => w.1 && w.2.2) = 0 :=
  ⟨fun _ bag A B C sB sNB hA hB hNB => deduction_exact_of_screening bag A B C sB sNB hA hB hNB,
    Controls.deduction_fails_without_screening.1⟩

open Mettapedia.GSLT.Contracts.AbsenceFrontier Mettapedia.GSLT.Contracts.FrontierNegation in
/-- **Absence × intuitionistic negation**: under the over-approximation of
firing, absence at a frontier is exactly intuitionistic negation over reachable
states; it is sound for every refinement and not complete for them. -/
theorem cell_absence_intuitionistic :
    (∀ (Atom Pattern : Type) (model : SpaceModel Atom Pattern) (pattern : Pattern) (space : Set Atom),
        knot (Step model) (fun later => ¬ Absent model pattern later) space ↔
          Absent model pattern space ∧ Frontier model pattern space) ∧
      (knot Mettapedia.GSLT.Contracts.FrontierNegation.Controls.neverFires (fun later => ¬ Absent Mettapedia.GSLT.Contracts.AbsenceFrontier.Controls.items () later)
          {.producer, .fact} ∧
        ¬ Frontier Mettapedia.GSLT.Contracts.AbsenceFrontier.Controls.items () {.producer, .fact}) :=
  ⟨fun _ _ model pattern space => knot_iff_absent_frontier model pattern space,
    Mettapedia.GSLT.Contracts.FrontierNegation.Controls.refinement_incomplete⟩

open Mettapedia.GSLT.Contracts.AbsenceFrontier Mettapedia.GSLT.Contracts.FrontierNegation in
/-- **Absence × ownership**: a module that owns a pattern's head certifies a
frontier by a check on its own atoms; atoms of other modules never revoke it;
the owner revokes it by installing a producer. -/
theorem cell_absence_ownership :
    (∀ (Atom Pattern Head Module : Type) (model : SpaceModel Atom Pattern) (head : Atom → Head)
        (owner : Head → Option Module) (module : Module) (pattern : Pattern) (atoms space : Set Atom),
        Disciplined model head owner → OwnedPattern model head owner module pattern →
        FrozenAt model head owner module pattern atoms →
        (∀ atom ∈ space, owner (head atom) = some module → atom ∈ atoms) →
        Absent model pattern space ∧ Frontier model pattern space) ∧
      ((Absent Mettapedia.GSLT.Contracts.AbsenceFrontier.Controls.items () {.fact} ∧
          Frontier Mettapedia.GSLT.Contracts.AbsenceFrontier.Controls.items () {.fact}) ∧
        ∃ later, Reaches (Step Mettapedia.GSLT.Contracts.AbsenceFrontier.Controls.items) {.producer, .fact} later ∧
          ¬ Absent Mettapedia.GSLT.Contracts.AbsenceFrontier.Controls.items () later) :=
  ⟨fun _ _ _ _ model _ _ _ _ _ _ disciplined owned frozen within =>
      ownership_certifies_frontier model disciplined owned frozen within,
    Mettapedia.GSLT.Contracts.FrontierNegation.Controls.owner_revokes⟩

open Mettapedia.CategoryTheory.SchedulerResolution in
/-- **Choice × probability × schedulers**: without choice all schedulers agree;
the envelope of probabilities is attained by deterministic schedulers; pure
choice between two outcomes is the vacuous interval `[0, 1]`. -/
theorem cell_choice_scheduler :
    (∀ (X : Type) (E : X → Prop) [DecidablePred E] (σ τ : Scheduler) (program : Program X),
        program.ChoiceFree → ∀ position, prob σ E position program = prob τ E position program) ∧
      (∀ (X : Type) (E : X → Prop) [DecidablePred E] (σ : Scheduler), Admissible σ →
        ∀ (program : Program X), program.WellFormed → ∀ position,
          (∃ τ, Deterministic τ ∧ prob τ E position program ≤ prob σ E position program) ∧
          (∃ τ, Deterministic τ ∧ prob σ E position program ≤ prob τ E position program)) ∧
      {r | ∃ σ, Admissible σ ∧ prob σ (· = true) [] (Program.choose (.ret true) (.ret false)) = r} =
        Set.Icc 0 1 :=
  ⟨fun _ E _ σ τ program free position => prob_choiceFree E σ τ program free position,
    fun _ E _ _ admissible program wf position =>
      ⟨exists_deterministic_le E admissible program wf position,
        exists_deterministic_ge E admissible program wf position⟩,
    choice_probabilities⟩

open Mettapedia.GSLT.Dynamics.PriorityFairness in
/-- **Priority × overtaking**: at most `B` overtakers bound the wait by
`|ahead| + B`; stamped deadlines with bounded arrival rate bound it by
`|ahead| + k d`. -/
theorem cell_priority_overtaking :
    (∀ (α : Type) [LinearOrder α] (run : Run α) (start : ℕ) (x : α), x ∈ run.pending start →
        ∀ B : ℕ, (∀ k, ∑ s ∈ Finset.range k, (run.overtakers (start + s) x).card ≤ B) →
        ∃ t, start ≤ t ∧ t ≤ start + (run.ahead start x).card + B ∧ run.fired t = x) ∧
      (∀ (Key : Type) [LinearOrder Key] (run : Run (Lex (ℕ × Key))) (start : ℕ) (x : Lex (ℕ × Key)),
        x ∈ run.pending start → ∀ k : ℕ, (∀ t, (run.arrivals t).card ≤ k) →
        (∀ t, ∀ y ∈ run.arrivals t, t < (ofLex y).1) →
        ∃ t, start ≤ t ∧ t ≤ start + (run.ahead start x).card + k * (ofLex x).1 ∧ run.fired t = x) :=
  ⟨fun _ _ run _ _ pending B budget => run.fires_within_overtaking pending B budget,
    fun _ _ run _ _ pending k rate stamped => deadline_fires_within run pending k rate stamped⟩

open Mettapedia.GSLT.Contracts.Arbitration Mettapedia.GSLT.Contracts.Coordination
  Mettapedia.GSLT.SeparationAlgebra in
/-- **Consumption × arbitration**: the first commit takes the token in every
schedule; exclusive consume authority makes the consuming program confluent,
with the holder's outcome. -/
theorem cell_consumption_arbitration :
    (∀ (first : Bool) (rest : List Bool),
        run Controls.consumers {Controls.Token.token} (first :: rest) =
          Controls.consumers first {Controls.Token.token}) ∧
      (∀ authority : Bool → Mettapedia.GSLT.Contracts.Access,
        SepAlgebra.Separate (authority true) (authority false) → Confluent (gated authority)) :=
  ⟨first_committer_wins, fun authority separate => gated_confluent authority separate⟩

open Mettapedia.GSLT.RankedDecision Mettapedia.GSLT.KripkeTruth in
/-- **Knowledge × well-founded tests**: a system whose truth references are
ranked is decided by its least fixed point, so a ranked knowledge-based program
has exactly one implementation; the self-referential teller is not ranked. -/
theorem cell_knowledge_ranked :
    (∀ (Judgment Base : Type) (system : System Judgment Base) (rank : Judgment → ℕ),
        system.Bivalent → Ranked system rank → ∀ judgment, Decides system.least judgment) ∧
      (∀ rank, ¬ Ranked (Mettapedia.GSLT.KnowledgeBasedPrograms.Examples.single.system
        Mettapedia.GSLT.KnowledgeBasedPrograms.Examples.Teller.program) rank) :=
  ⟨fun _ _ _ _ bivalent ranked judgment => least_decides bivalent ranked judgment,
    Controls.teller_not_ranked⟩

end Mettapedia.Languages.MeTTa.PrimeOptions.LayerAtlas
