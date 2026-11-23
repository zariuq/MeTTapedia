import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Examples
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecSpecimens.RealCalculi
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FragmentsOfTheStep.MonotoneInference
import Mettapedia.GSLT.Core.NonFactorization

/-!
# Spec-by-example suite (Part I): Core operational dimensions D1, D2, D3, D4, D7

Each dimension is grounded in a real motivating specimen on `RuleSyntax.step`,
`Selection.Valid`, `FragmentsOfTheStep`, `NullsOnTheStep.ParallelClosed`, and real HE/PeTTa
matching calculi (`RealCalculi`), pairing a kernel-checked positive specimen with a
kernel-checked negative separation theorem:

* **D1 (`DualResourceEscrow`)** — Consensus & multi-party atomic join arity:
  two interdependent tokens are swapped atomically by a 2-take rule, whereas self-aliasing is
  refused, no `take = []` firing can consume either token (`withoutTake_present_subset_and_card_le`),
  and omitting `take` forces confluence (`MonotoneInference.confluent` vs `choice_not_confluent`).
* **D2 (`AllergyVetoPlanner`)** — CALM / non-monotonic coordination boundary:
  an action guarded by `none contraindicated` fires in a clean space, is atomically vetoed when
  a contraindication arrives, refutes parallel-context persistence, and admits no uniform
  translation into persistent HE or PeTTa matching (`RealCalculi`).
* **D3 (`BulkAttentionWave`)** — Firing cardinality (bounded arity vs. bulk every-match):
  any admitted firing on `RuleSyntax.step` with take-arity bounded by `B` leaves at least one
  occurrence in any space of size `B + 1` (`bounded_take_cannot_clear_k_plus_one`), whereas
  atomic bulk retraction (`bulkRetractState_clears_all`) and PeTTa `removeAtom`
  (`petta_removeAtom_clears_all_copies`) clear arbitrary `N` matches in one step.
* **D4 (`SymmetricTwinElection`)** — Symmetry breaking & anonymous choice:
  no equivariant deterministic selector can elect one of two symmetric agents, paired with
  real step occurrence-renaming equivariance (`NullsOnTheStep.ParallelClosed.Monotone.succeeds_rename`)
  versus identity-broken election.
* **D7 (`BudgetedLinearPruning`)** — Resource linearity, erasure, and bag multiplicity:
  a linear-take + persistent-read + erasure firing spends an attention token while retaining
  the axiom and refuses double-spending; paired with `withoutRead_cannot_preserve_matched_identity`,
  `withoutMake_subset_and_card_le`, and bag-vs-set collapse (`set_dedup_loses_bag_probability`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecSpecimens

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open Mettapedia.Logic.LP
open Mettapedia.GSLT.Core.NonFactorization
open RuleSyntax
open RuleSyntax.OneFrame (Terms frames ext)
open RuleSyntax.Controls (atoms action)
open RuleSyntax.Examples (Tm X E c fresh_of_ground)

/-! ## D1: Dual-Resource Belief Escrow (Herlihy Consensus / Atomic Join Arity) -/

namespace DualResourceEscrow

/-- Atomic 2-take escrow: consumes both `haveA` (`10`) and `haveB` (`20`) and commits `settled` (`30`). -/
def escrowSwap : Rule Tm :=
  ⟨PUnit.unit, ⟨[c 10, c 20], [], [], [], [c 30]⟩, []⟩

/-- Read-only observer rule (Herlihy-1 `match` profile: reads both tokens without consuming). -/
def readOnlyObserve : Rule Tm :=
  ⟨PUnit.unit, ⟨[], [c 10, c 20], [], [], [c 30]⟩, []⟩

def escrowProgram : Program Tm := {escrowSwap, readOnlyObserve}

/-- Initial space holding `haveA` at id `0` and `haveB` at id `1`. -/
def escrowState : State Tm ℕ :=
  ⟨PUnit.unit, [], {0, 1}, fun o => if o = 0 then c 10 else c 20⟩

/-- Atomic firing taking `{0, 1}` and making `2`. -/
def atomicSwapFiring : Firing ℕ E escrowProgram PUnit.unit :=
  ⟨escrowSwap, Or.inl rfl, PUnit.unit, Subst.id atoms, ⟨[0, 1], [], [2]⟩, []⟩

/-- Invalid self-aliased firing attempting to take `0` twice. -/
def aliasedSwapFiring : Firing ℕ E escrowProgram PUnit.unit :=
  ⟨escrowSwap, Or.inl rfl, PUnit.unit, Subst.id atoms, ⟨[0, 0], [], [2]⟩, []⟩

theorem atomicSwap_information :
    atomicSwapFiring.information X escrowState = [(c 10, c 10), (c 20, c 20)] := rfl

/-- **D1 Positive Control**: the atomic 2-take escrow firing is admitted and replaces
both tokens with `{2 ↦ settled}` in one indivisible step. -/
theorem escrow_atomic_admitted :
    (step X ℕ E escrowProgram).Admits (s := escrowState) atomicSwapFiring := by
  refine (admits_iff atomicSwapFiring).mpr ⟨?_, ⟨by decide, List.nodup_singleton 2,
    rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · apply fresh_of_ground action escrowState atomicSwapFiring
    intro t member σ
    simp only [atomicSwapFiring, escrowSwap, Rule.terms, List.map_nil, List.flatMap_nil,
      List.nil_append, List.append_nil, List.cons_append, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [atomicSwapFiring, escrowState, Selection.commit]
  · rw [atomicSwap_information]
    refine ⟨PUnit.unit, Subst.id atoms, fun e member => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  · intro check member
    simp [atomicSwapFiring, escrowSwap, Firing.opened, RuleInstance.map] at member
  · intro q member
    simp [atomicSwapFiring, escrowSwap, Firing.collectOpened] at member

theorem escrow_atomic_result_present :
    (atomicSwapFiring.result X escrowState).present = {2} := by
  ext o
  simp only [Firing.result, atomicSwapFiring, escrowState, fire, Selection.commit,
    Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
    List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- **D1 Negative Control (1)**: taking the same occurrence twice is refused. -/
theorem escrow_self_alias_refused :
    ¬ (step X ℕ E escrowProgram).Admits (s := escrowState) aliasedSwapFiring := by
  intro hadm
  have hnodup := ((admits_iff aliasedSwapFiring).mp hadm).2.1.1
  simp [aliasedSwapFiring] at hnodup

/-- **D1 Negative Control (2)**: no read-only (`take = []`) admitted firing can consume
either escrow token; both `0` and `1` always survive in the result space. -/
theorem readOnly_cannot_consume_escrow (f : Firing ℕ E escrowProgram PUnit.unit)
    (hro : f.rule.body.take = [])
    (hadm : (step X ℕ E escrowProgram).Admits (s := escrowState) f) :
    0 ∈ (f.result X escrowState).present ∧ 1 ∈ (f.result X escrowState).present := by
  have hlen : f.rule.body.take.length = f.selection.taken.length :=
    ((admits_iff f).mp hadm).2.1.2.2.1
  have htakeNil : f.selection.taken = [] := by
    rw [hro] at hlen
    exact List.eq_nil_of_length_eq_zero hlen.symm
  simp [Firing.result, escrowState, fire, Selection.commit, htakeNil]

/-- **D1 Real Fragment Wall**: omitting `take` (and checks) collapses the step to confluent
Datalog inference (`MonotoneInference.confluent`), whereas consuming `take` breaks confluence
via competitive choice (`MonotoneInference.Controls.choice_not_confluent`). -/
theorem take_separates_nonconfluent_choice_from_monotone :
    ¬ FragmentsOfTheStep.MonotoneInference.Monotone
        FragmentsOfTheStep.MonotoneInference.Controls.choice ∧
    Relation.ReflTransGen
      (FragmentsOfTheStep.GroundFirings.GroundStep FragmentsOfTheStep.MonotoneInference.Controls.choice)
      FragmentsOfTheStep.MonotoneInference.Controls.single
      FragmentsOfTheStep.MonotoneInference.Controls.afterLeft ∧
    Relation.ReflTransGen
      (FragmentsOfTheStep.GroundFirings.GroundStep FragmentsOfTheStep.MonotoneInference.Controls.choice)
      FragmentsOfTheStep.MonotoneInference.Controls.single
      FragmentsOfTheStep.MonotoneInference.Controls.afterRight ∧
    (∃ D, Relation.ReflTransGen
      (FragmentsOfTheStep.GroundFirings.GroundStep FragmentsOfTheStep.MonotoneInference.Controls.choice)
      FragmentsOfTheStep.MonotoneInference.Controls.afterRight D ∧
      FragmentsOfTheStep.MonotoneInference.Controls.right ∈ FragmentsOfTheStep.GroundFirings.facts D) ∧
    ¬ ∃ D, Relation.ReflTransGen
      (FragmentsOfTheStep.GroundFirings.GroundStep FragmentsOfTheStep.MonotoneInference.Controls.choice)
      FragmentsOfTheStep.MonotoneInference.Controls.afterLeft D ∧
      FragmentsOfTheStep.MonotoneInference.Controls.right ∈ FragmentsOfTheStep.GroundFirings.facts D :=
  FragmentsOfTheStep.MonotoneInference.Controls.choice_not_confluent

end DualResourceEscrow

/-! ## D2: Allergy-Vetoed Action Planner (CALM / Non-Monotonic Coordination) -/

namespace AllergyVetoPlanner

/-- Take `request` (`1`), guard `none contraindicated` (`99`), make `administered` (`2`). -/
def administerRule : Rule Tm :=
  ⟨PUnit.unit, ⟨[c 1], [], [], [.predicate .none (c 99)], [c 2]⟩, []⟩

def plannerProgram : Program Tm := {administerRule}

/-- Safe space: only the request at id `0`. -/
def safeState : State Tm ℕ :=
  ⟨PUnit.unit, [], {0}, fun o => if o = 0 then c 1 else c 99⟩

/-- Vetoed space: the same request at id `0` alongside a contraindication at id `2`. -/
def vetoedState : State Tm ℕ :=
  ⟨PUnit.unit, [], {0, 2}, fun o => if o = 0 then c 1 else c 99⟩

def administerFiring : Firing ℕ E plannerProgram PUnit.unit :=
  ⟨administerRule, rfl, PUnit.unit, Subst.id atoms, ⟨[0], [], [1]⟩, []⟩

theorem administer_safe_information :
    administerFiring.information X safeState = [(c 1, c 1)] := rfl

theorem administer_vetoed_information :
    administerFiring.information X vetoedState = [(c 1, c 1)] := rfl

/-- **D2 Positive Control**: without a contraindication, `administer` is admitted. -/
theorem administer_admitted_safe :
    (step X ℕ E plannerProgram).Admits (s := safeState) administerFiring := by
  refine (admits_iff administerFiring).mpr ⟨?_, ⟨List.nodup_singleton 0, List.nodup_singleton 1,
    rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · apply fresh_of_ground action safeState administerFiring
    intro t member σ
    simp only [administerFiring, administerRule, Rule.terms, checkTerms, List.map_nil,
      List.flatMap_cons, List.flatMap_nil, List.nil_append, List.append_nil,
      List.cons_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [administerFiring, safeState, Selection.commit]
  · rw [administer_safe_information]
    refine ⟨PUnit.unit, Subst.id atoms, fun e member => ?_⟩
    obtain rfl := List.mem_singleton.mp member
    rfl
  · intro check member b σ _
    simp only [administerFiring, administerRule, Firing.opened, RuleInstance.map,
      Check.map, List.map_cons, List.map_nil, List.mem_singleton] at member
    subst member
    intro o ho equated
    have ho0 : o = 0 := Finset.mem_singleton.mp ho
    subst ho0
    have hbad : (c 99 : Term atoms) = c 1 := equated
    exact absurd (Term.const.inj hbad) (by decide)
  · intro q member
    simp [administerFiring, administerRule, Firing.collectOpened] at member

/-- **D2 Negative Control**: adding the contraindication at id `2` switches off admission. -/
theorem administer_vetoed_by_allergy :
    ¬ (step X ℕ E plannerProgram).Admits (s := vetoedState) administerFiring := by
  intro hadm
  obtain ⟨-, -, -, -, hguard, -⟩ := (admits_iff administerFiring).mp hadm
  have hsol : X.Models (a := PUnit.unit) (b := PUnit.unit) (Subst.id atoms)
      (administerFiring.information X vetoedState) := by
    rw [administer_vetoed_information]
    intro e member
    obtain rfl := List.mem_singleton.mp member
    rfl
  have holds := hguard (.predicate .none (c 99)) (List.mem_singleton_self _) PUnit.unit _ hsol
  exact holds 2 (by simp [vetoedState]) rfl

/-- **CALM / Parallel-Context Obstruction**: `administer` breaks persistence under
parallel composition (expanding `safeState.present ⊆ vetoedState.present` disables a
previously admitted firing). -/
theorem allergy_refutes_parallel_persistence :
    safeState.present ⊆ vetoedState.present ∧
    (step X ℕ E plannerProgram).Admits (s := safeState) administerFiring ∧
    ¬ (step X ℕ E plannerProgram).Admits (s := vetoedState) administerFiring :=
  ⟨by intro o ho; simp [safeState, vetoedState] at ho ⊢; exact Or.inl ho,
   administer_admitted_safe, administer_vetoed_by_allergy⟩

/-- **D2 Real Non-Encodability Wall**: the absence-guarded step admits NO uniform
translation into persistent HE matching (`heMatchParallel`) OR persistent PeTTa
matching (`pettaMatchParallel`). -/
theorem absence_not_uniformly_encodable_into_he_or_petta
    (heRules : List (Mettapedia.Languages.MeTTa.OSLFCore.Atom ×
      Mettapedia.Languages.MeTTa.OSLFCore.Atom))
    (fuel : Nat) (heSucc : Mettapedia.Languages.MeTTa.OSLFCore.Atom)
    (pettaRules : List (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern ×
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern))
    (pettaSucc : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    IsEmpty (NullsOnTheStep.ParallelClosed.UniformTranslation
      NullsOnTheStep.ParallelClosed.source (heMatchParallel heRules fuel heSucc)) ∧
    IsEmpty (NullsOnTheStep.ParallelClosed.UniformTranslation
      NullsOnTheStep.ParallelClosed.source (pettaMatchParallel pettaRules pettaSucc)) :=
  ⟨no_uniformTranslation_absence_into_heMatch heRules fuel heSucc,
   no_uniformTranslation_absence_into_pettaMatch pettaRules pettaSucc⟩

end AllergyVetoPlanner

/-! ## D3: Axiom-Retraction Attention Wave (Bounded Arity vs. Bulk Every-Match) -/

namespace BulkAttentionWave

/-- A space holding `N` cached derivations `0, 1, ..., N-1` all tagged by axiom `c 7`. -/
def waveState (N : ℕ) : State Tm ℕ :=
  ⟨PUnit.unit, [], Finset.range N, fun _ => c 7⟩

/-- **D3 Positive Control (1 — Atomic Bulk Retraction on `RuleSyntax.State`)**:
a single bulk every-match retraction clears all `N` cached derivations atomically for arbitrary `N`. -/
theorem bulk_everyMatch_clears_entire_wave (N : ℕ) :
    (bulkRetractState (waveState N) (fun _ => true)).present = ∅ :=
  bulkRetractState_clears_all (waveState N) (fun _ => true) (fun _ _ => rfl)

/-- **D3 Positive Control (2 — Real PeTTa Bulk `removeAtom`)**:
PeTTa's `PeTTaSpace.removeAtom` clears all `N` matching copies of a pattern in one call. -/
theorem petta_bulk_removeAtom_clears_wave (N : ℕ)
    (p : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern) :
    (Mettapedia.Languages.MeTTa.PeTTa.PeTTaSpace.removeAtom ⟨List.replicate N p, []⟩ p).facts = [] :=
  petta_removeAtom_clears_all_copies N p

/-- **D3 Negative Control (1 — Real `RuleSyntax.step` Admitted Firing Arity Wall)**:
for ANY admitted firing `f` of ANY program `P` on `RuleSyntax.step` whose rule take-arity is
bounded by `B`, firing on `waveState (B + 1)` leaves at least one occurrence in the post-state. -/
theorem admitted_bounded_take_leaves_nonempty (B : ℕ)
    (P : Program Tm) (f : Firing ℕ E P PUnit.unit)
    (admitted : (step X ℕ E P).Admits (s := waveState (B + 1)) f)
    (harity : f.rule.body.take.length ≤ B) :
    1 ≤ (f.result X (waveState (B + 1))).present.card :=
  bounded_take_cannot_clear_k_plus_one admitted harity (by simp [waveState])

/-- **D3 Negative Control (2 — Specific Stale Witness)**: no single firing with selection
take-length `≤ B` can remove all `B + 1` cached lemmas of `waveState (B + 1)` in one step;
at least one stale lemma `o < B + 1` survives. -/
theorem bounded_arity_cannot_clear_unbounded_wave (B : ℕ)
    (P : Program Tm) (f : Firing ℕ E P PUnit.unit)
    (hbound : f.selection.taken.length ≤ B) :
    ∃ o ∈ (f.result X (waveState (B + 1))).present, o < B + 1 := by
  have hcardTaken : f.selection.taken.toFinset.card ≤ B :=
    (List.toFinset_card_le f.selection.taken).trans hbound
  have hlt : f.selection.taken.toFinset.card < (Finset.range (B + 1)).card := by
    rw [Finset.card_range]
    omega
  have hnotSub : ¬ Finset.range (B + 1) ⊆ f.selection.taken.toFinset := by
    intro hsub
    exact not_le.mpr hlt (Finset.card_le_card hsub)
  rw [Finset.not_subset] at hnotSub
  obtain ⟨o, hoRange, hoNotTaken⟩ := hnotSub
  refine ⟨o, ?_, Finset.mem_range.mp hoRange⟩
  simp only [Firing.result, waveState, fire, Selection.commit, Finset.mem_union, Finset.mem_sdiff]
  exact Or.inl ⟨hoRange, hoNotTaken⟩

end BulkAttentionWave

/-! ## D4: Twin-Agent Mutual-Exclusion Proposal (Symmetry Breaking & Step Equivariance) -/

namespace SymmetricTwinElection

/-- Swap symmetry on two twin agents `{false, true}`. -/
def twinSwap : Bool → Bool := Bool.not

/-- A state predicate over the two twin agents is symmetric when invariant under `twinSwap`. -/
def SymmetricConfig {α : Type*} (cfg : Bool → α) : Prop :=
  ∀ b, cfg (twinSwap b) = cfg b

/-- An equivariant deterministic selector commutes with `twinSwap`. -/
def EquivariantSelector {α : Type*} (pick : (Bool → α) → Bool) : Prop :=
  ∀ cfg : Bool → α, pick (cfg ∘ twinSwap) = twinSwap (pick cfg)

/-- **D4 Negative Control (Symmetry-Breaking Impossibility)**: no equivariant deterministic
selector can elect one agent in any symmetric twin configuration. -/
theorem no_equivariant_deterministic_election {α : Type*}
    (cfg : Bool → α) (hsym : SymmetricConfig cfg)
    (pick : (Bool → α) → Bool) (heq : EquivariantSelector pick) : False := by
  have hcomp : cfg ∘ twinSwap = cfg := funext hsym
  have hfix : pick cfg = twinSwap (pick cfg) := by
    have h := heq cfg
    rwa [hcomp] at h
  cases hp : pick cfg <;> simp [hp, twinSwap] at hfix

/-- **D4 Real Step Equivariance Control**: success of the constraint multiset step is
invariant under every label-preserving bijection `π : T × ℕ ≃ T × ℕ` on occurrence identities
(`NullsOnTheStep.ParallelClosed.Monotone.succeeds_rename`). -/
theorem step_equivariant_under_occurrence_renaming
    {T S : Type*} [DecidableEq T] {A : SubstitutionAction T S}
    {P : RuleInstance T → Prop} {row : T → Prop}
    (π : T × ℕ ≃ T × ℕ) (keeps : ∀ o, (π o).1 = o.1)
    {C : Configuration T (T × ℕ)} :
    (NullsOnTheStep.ParallelClosed.stepCalculus A (Prod.fst : T × ℕ → T) P row).Succeeds C →
    (NullsOnTheStep.ParallelClosed.stepCalculus A (Prod.fst : T × ℕ → T) P row).Succeeds
      (AnnotatedRuns.renameConfiguration π C) :=
  NullsOnTheStep.ParallelClosed.Monotone.succeeds_rename π keeps

/-- **D4 Positive Control**: breaking symmetry via distinct occurrence identities (`0 < 1`)
elects a unique winner cleanly. -/
def idBrokenElect (present : Finset ℕ) (hne : present.Nonempty) : ℕ :=
  present.min' hne

theorem idBroken_elects_unique_winner :
    idBrokenElect {0, 1} (by simp) = 0 ∧
    (0 : ℕ) ∈ ({0, 1} : Finset ℕ) ∧
    (1 : ℕ) ∉ ({idBrokenElect {0, 1} (by simp)} : Finset ℕ) := by
  decide

end SymmetricTwinElection

/-! ## D7: Budgeted Hypothesis Pruning & Bag Multiplicity (Linearity, Erasure, Bags) -/

namespace BudgetedLinearPruning

/-- Spend attention token (`1`), read persistent axiom (`50`), erase (make nothing). -/
def pruneRule : Rule Tm :=
  ⟨PUnit.unit, ⟨[c 1], [c 50], [], [], []⟩, []⟩

def pruneProgram : Program Tm := {pruneRule}

/-- Initial state: one attention token at id `0`, one persistent axiom at id `1`. -/
def initialState : State Tm ℕ :=
  ⟨PUnit.unit, [], {0, 1}, fun o => if o = 0 then c 1 else c 50⟩

def pruneFiring : Firing ℕ E pruneProgram PUnit.unit :=
  ⟨pruneRule, rfl, PUnit.unit, Subst.id atoms, ⟨[0], [1], []⟩, []⟩

theorem prune_information :
    pruneFiring.information X initialState = [(c 1, c 1), (c 50, c 50)] := rfl

/-- **D7 Positive Control (Linearity + Read + Erasure)**: `pruneFiring` is admitted,
consumes token `0`, preserves axiom `1`, and erases the spent token without creating junk. -/
theorem prune_admitted :
    (step X ℕ E pruneProgram).Admits (s := initialState) pruneFiring := by
  refine (admits_iff pruneFiring).mpr ⟨?_, ⟨List.nodup_singleton 0, List.nodup_nil,
    rfl, rfl, rfl, rfl⟩, ?_, ?_, ?_, ?_⟩
  · apply fresh_of_ground action initialState pruneFiring
    intro t member σ
    simp only [pruneFiring, pruneRule, Rule.terms, List.map_nil, List.flatMap_nil,
      List.nil_append, List.append_nil, List.cons_append, List.mem_cons, List.not_mem_nil,
      or_false] at member
    rcases member with rfl | rfl <;> rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [pruneFiring, initialState, Selection.commit]
  · rw [prune_information]
    refine ⟨PUnit.unit, Subst.id atoms, fun e member => ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rfl
  · intro check member
    simp [pruneFiring, pruneRule, Firing.opened, RuleInstance.map] at member
  · intro q member
    simp [pruneFiring, pruneRule, Firing.collectOpened] at member

theorem prune_result_present :
    (pruneFiring.result X initialState).present = {1} := by
  ext o
  simp only [Firing.result, pruneFiring, initialState, fire, Selection.commit,
    Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
    List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  omega

/-- **D7 Negative Control (1 — No Double Spending)**: once token `0` is spent, firing
`pruneFiring` a second time on the post-state is refused. -/
theorem prune_second_time_refused :
    ¬ (step X ℕ E pruneProgram).Admits (s := pruneFiring.result X initialState) pruneFiring := by
  intro hadm
  have hen := ((admits_iff pruneFiring).mp hadm).2.2.1.1
  have hzero : (0 : ℕ) ∈ (pruneFiring.result X initialState).present :=
    hen (by simp [pruneFiring, Selection.commit])
  rw [prune_result_present] at hzero
  simp at hzero

/-- **D7 Negative Control (2 — Bag Multiplicity vs. Set Collapse)**:
deduplicating outcome bags `[true, true, false]` and `[true, false]` to the same set
`{true, false}` collapses distinct uniform probabilities `2/3` and `1/2` (`NonTrivialFiber`). -/
def bagProbTrue (outcomes : List Bool) : ℚ :=
  if outcomes.length = 0 then 0
  else ((outcomes.count true : ℕ) : ℚ) / (outcomes.length : ℚ)

def setSupport (outcomes : List Bool) : Finset Bool :=
  outcomes.toFinset

def bag_vs_set_fiber : NonTrivialFiber setSupport bagProbTrue where
  left := [true, true, false]
  right := [true, false]
  sameShadow := by decide
  differentValue := by norm_num [bagProbTrue]

theorem set_dedup_loses_bag_probability : ¬ Factors setSupport bagProbTrue :=
  bag_vs_set_fiber.not_factors

end BudgetedLinearPruning

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SpecSpecimens
