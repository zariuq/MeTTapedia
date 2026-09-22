import Mettapedia.Ethics.VirtuePossessionUndecidability
import Mettapedia.Languages.PartrecMachine.BoundedReduction
import Mettapedia.Ethics.TargetCenteredVirtue

/-!
# Virtue possession over the authored machine

`VirtuePossessionUndecidability` stated virtue possession over Mathlib's program
codes.  This module states it over agents that are programs of the authored
partial-recursive machine, with every response read off reduction in that
`LanguageDef`.

* An agent **responds** in situation `s` with `r` when, run on `[s]`, it halts
  with an output list whose head is `r`, following Mathlib's convention that a
  single result is returned at the head of the output list.  An agent that halts
  with the empty list gives no response (`tail_never_responds`); this is the
  reading under which deliberation in the choice-point language takes the
  response as its action.
* **Possession depends only on what the agent computes**, so a nontrivial
  behavioral virtue has an undecidable possession problem
  (`hostPossession_not_computable`).  Responsiveness and faithful reporting are
  both instances.
* **The ontology's disposition.**  Host possession is `Theory.PossessesDisposition` of
  the one-virtue theory, with responding as choosing and certainty as likelihood
  (`hostPossesses_iff_possessesDisposition`); a vacuous likelihood would admit
  the silent agent (`vacuous_likelihood_admits_silent`).
* **Act judgments name no program.**  A produced act either hits the target or not
  (`ActHitsTarget`), and possession is exactly that every act the agent produces
  in the field hits it (`hostPossesses_iff_acts`).  For responsiveness every act
  hits, yet possession is undecidable (`responsiveness_acts_all_hit`): the
  undecidability is entirely in producing the acts.
* **Possession can be certified, its absence cannot.**  For a finite field and a
  computable target, possession is semi-decidable (`hostPossession_re`): run the
  agent with growing budgets.  When the virtue is nontrivial, failing to possess
  it is not semi-decidable (`hostPossession_failure_not_re`).
* **For an unbounded field, neither.**  Faithful reporting over every situation
  can be neither certified nor refuted by finite behavior
  (`faithfulReport_neither_certifiable_nor_refutable`); its possession has the
  form "for every situation, some budget" with a primitive recursive check
  inside (`faithfulReport_iff_forall_exists_within`).
* **Bounded possession escapes.**  Possession within a reduction budget is
  decidable for a finite field and computable target, possession is bounded
  possession at some budget, and the bounded check does not depend only on what
  agents compute.
* **The port is faithful.**  A compiled Mathlib code possesses a virtue as a host
  agent exactly when it possesses it as a Mathlib code (`hostPossesses_compile_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.Ethics.HostVirtuePossession

open Mettapedia.OSLF.MeTTaIL.Syntax
open Turing.ToPartrec
open Mettapedia.Computability
open Mettapedia.Languages.PartrecMachine
open Mettapedia.Ethics.VirtuePossessionUndecidability
open Mettapedia.Computability.ToPartrecCodeEncoding
open Primrec

/-! ## Responses read off reduction -/

/-- The agent, run on `[situation]`, halts with an output headed by `response`. -/
def RespondsWith (agent : Code) (situation response : ℕ) : Prop :=
  ∃ rest, HaltsWith agent [situation] (response :: rest)

/-- Possession of a behavioral virtue by a host agent. -/
def HostPossesses (virtue : BehavioralVirtue) (agent : Code) : Prop :=
  ∀ situation, virtue.field situation →
    ∃ response, RespondsWith agent situation response ∧ virtue.target situation response

/-- The host agents possessing a virtue. -/
def possessors (virtue : BehavioralVirtue) : Set Code :=
  {agent | HostPossesses virtue agent}

theorem possessors_invariant (virtue : BehavioralVirtue) :
    ObservationInvariant HaltsWith (possessors virtue) := by
  intro first second same
  simp only [possessors, Set.mem_ofPred_eq, HostPossesses, RespondsWith, same]

/-- **Rice's theorem for virtue possession by host agents.** -/
theorem hostPossession_not_computable (virtue : BehavioralVirtue)
    (nontrivial : (possessors virtue).Nonempty ∧ (possessors virtue)ᶜ.Nonempty) :
    ¬ ComputablePred (HostPossesses virtue) :=
  rice (possessors_invariant virtue) nontrivial

/-! ## Act judgments -/

/-- Whether a produced act hits the virtue's target.  No agent appears. -/
def ActHitsTarget (virtue : BehavioralVirtue) (situation response : ℕ) : Prop :=
  virtue.field situation → virtue.target situation response

theorem hostPossesses_iff_acts (virtue : BehavioralVirtue) (agent : Code) :
    HostPossesses virtue agent ↔
      ∀ situation, virtue.field situation →
        ∃ response, RespondsWith agent situation response ∧ ActHitsTarget virtue situation response := by
  constructor
  · intro possesses situation inField
    obtain ⟨response, responds, hits⟩ := possesses situation inField
    exact ⟨response, responds, fun _ => hits⟩
  · intro possesses situation inField
    obtain ⟨response, responds, hits⟩ := possesses situation inField
    exact ⟨response, responds, hits inField⟩

theorem zero'_responds (situation : ℕ) : RespondsWith .zero' situation 0 :=
  ⟨[situation], haltsWith_iff.mpr (by simp)⟩

theorem silent_never_responds (situation response : ℕ) : ¬ RespondsWith silent situation response := by
  rintro ⟨rest, halts⟩
  have := haltsWith_iff.mp halts
  simp [silent_eval] at this

/-- An agent that halts with the empty output gives no response. -/
theorem tail_never_responds (situation response : ℕ) : ¬ RespondsWith .tail situation response := by
  rintro ⟨rest, halts⟩
  have := haltsWith_iff.mp halts
  simp at this

theorem responsiveness_nontrivial :
    (possessors responsiveness).Nonempty ∧ (possessors responsiveness)ᶜ.Nonempty :=
  ⟨⟨.zero', fun situation _ => ⟨0, zero'_responds situation, trivial⟩⟩,
    ⟨silent, fun possesses => by
      obtain ⟨response, responds, -⟩ := possesses 0 rfl
      exact silent_never_responds 0 response responds⟩⟩

/-- **Every act hits, and possession is still undecidable.**  For responsiveness
the act judgment is constantly true; what cannot be decided is whether the agent
produces an act at all. -/
theorem responsiveness_acts_all_hit :
    (∀ situation response, ActHitsTarget responsiveness situation response) ∧
      ¬ ComputablePred (HostPossesses responsiveness) :=
  ⟨fun _ _ _ => trivial, hostPossession_not_computable _ responsiveness_nontrivial⟩

theorem id_possesses_faithfulReport : HostPossesses faithfulReport .id := fun situation _ =>
  ⟨situation, ⟨[], haltsWith_iff.mpr (by simp)⟩, rfl⟩

theorem zero'_not_possesses_faithfulReport : ¬ HostPossesses faithfulReport .zero' := by
  intro possesses
  obtain ⟨response, ⟨rest, halts⟩, onTarget⟩ := possesses 1 trivial
  have member := haltsWith_iff.mp halts
  simp only [Code.zero'_eval, Part.pure_eq_some, Part.mem_some_iff, List.cons.injEq] at member
  obtain ⟨rfl, -⟩ := member
  simp [faithfulReport] at onTarget

theorem faithfulReport_nontrivial :
    (possessors faithfulReport).Nonempty ∧ (possessors faithfulReport)ᶜ.Nonempty :=
  ⟨⟨.id, id_possesses_faithfulReport⟩, ⟨.zero', zero'_not_possesses_faithfulReport⟩⟩

theorem faithfulReport_not_computable : ¬ ComputablePred (HostPossesses faithfulReport) :=
  hostPossession_not_computable _ faithfulReport_nontrivial

/-! ## The ontology's disposition -/

open Mettapedia.Ethics.TargetCenteredVirtue in
/-- A behavioral virtue as the ontology's virtue specification: its field and
target, with any response counting as its mode. -/
def behavioralSpec (virtue : BehavioralVirtue) : VirtueSpec Code ℕ ℕ Unit where
  valence := .virtue
  field := virtue.field
  basis := Set.univ
  basis_nonempty := ⟨(), trivial⟩
  mode _ _ _ := True
  target _ situation response := virtue.target situation response

open Mettapedia.Ethics.TargetCenteredVirtue in
/-- The theory containing one behavioral virtue. -/
def behavioralTheory (virtue : BehavioralVirtue) : TargetCenteredVirtue.Theory Unit Code ℕ ℕ Unit where
  included := Set.univ
  spec _ := behavioralSpec virtue

open Mettapedia.Ethics.TargetCenteredVirtue in
/-- **Host possession is the ontology's disposition possession**, with responding
as choosing and certainty as likelihood. -/
theorem hostPossesses_iff_possessesDisposition (virtue : BehavioralVirtue) (agent : Code) :
    HostPossesses virtue agent ↔
      (behavioralTheory virtue).PossessesDisposition id RespondsWith agent () := by
  simp only [TargetCenteredVirtue.Theory.PossessesDisposition, behavioralTheory, behavioralSpec,
    TargetCenteredVirtue.VirtueSpec.ActionHitsTarget, HostPossesses, Set.mem_univ, true_and, id]
  exact forall₂_congr fun _ inField =>
    exists_congr fun _ => and_congr_right fun _ => ⟨fun onTarget => ⟨inField, onTarget⟩, And.right⟩

open Mettapedia.Ethics.TargetCenteredVirtue in
/-- **Likelihood is load-bearing.**  Read with a likelihood that holds of
everything, the silent agent would possess faithful reporting. -/
theorem vacuous_likelihood_admits_silent :
    (behavioralTheory faithfulReport).PossessesDisposition (fun _ => True) RespondsWith silent () ∧
      ¬ HostPossesses faithfulReport silent := by
  refine ⟨⟨trivial, fun _ _ => trivial⟩, fun possesses => ?_⟩
  obtain ⟨response, responds, -⟩ := possesses 0 trivial
  exact silent_never_responds 0 response responds

/-! ## Faithfulness of the port -/

theorem respondsWith_compile_iff (source : Nat.Partrec.Code) (situation response : ℕ) :
    RespondsWith (compile source) situation response ↔ response ∈ source.eval situation := by
  constructor
  · rintro ⟨rest, halts⟩
    have member := haltsWith_iff.mp halts
    rw [compile_eval] at member
    obtain ⟨value, valueMember, same⟩ := (Part.mem_map_iff _).mp member
    obtain ⟨rfl, -⟩ := List.cons_eq_cons.mp same
    simpa using valueMember
  · intro member
    exact ⟨[], haltsWith_iff.mpr (by rw [compile_eval]; exact Part.mem_map _ member)⟩

/-- A compiled Mathlib code possesses a virtue as a host agent exactly when it
possesses it as a Mathlib code. -/
theorem hostPossesses_compile_iff (virtue : BehavioralVirtue) (source : Nat.Partrec.Code) :
    HostPossesses virtue (compile source) ↔ Possesses virtue source := by
  simp only [HostPossesses, Possesses, respondsWith_compile_iff]

/-! ## Bounded possession -/

theorem reducesWithin_mono {budget : ℕ} {term target : Pattern}
    (within : ReducesWithin budget term target) (extra : ℕ) :
    ReducesWithin (budget + extra) term target := by
  induction within with
  | refl => exact .refl _ _
  | step reduces _ ih =>
      rw [Nat.add_right_comm]
      exact .step reduces ih

/-- The halted output within a budget, if any. -/
def outputWithin (budget : ℕ) (agent : Code) (input : List ℕ) : Option (List ℕ) :=
  match frameStep^[budget] (.inl (agent, [], input)) with
  | .inr (.inr output) => some output
  | _ => none

theorem outputWithin_eq_some_iff (budget : ℕ) (agent : Code) (input output : List ℕ) :
    outputWithin budget agent input = some output ↔
      ReducesWithin budget (normalTerm agent .halt input) (encCfg (.halt output)) := by
  rw [show normalTerm agent .halt input = encFrameState (.inl (agent, [], input)) from rfl,
    reducesWithin_halt_iff, outputWithin]
  split <;> simp_all

theorem outputWithin_primrec :
    Primrec fun query : (Code × List ℕ) × ℕ => outputWithin query.2 query.1.1 query.1.2 := by
  have iterated : Primrec fun query : (Code × List ℕ) × ℕ =>
      frameStep^[query.2] (.inl (query.1.1, [], query.1.2)) :=
    nat_iterate snd (sumInl.comp (pair (fst.comp fst) (pair (const []) (snd.comp fst))))
      (frameStep_primrec.comp snd).to₂
  refine (sumCasesOn iterated (const none).to₂
    (sumCasesOn snd (const none).to₂ (option_some.comp snd).to₂).to₂).of_eq ?_
  intro query
  simp only [outputWithin]
  generalize frameStep^[query.2] (.inl (query.1.1, [], query.1.2)) = state
  rcases state with _ | _ | _ <;> rfl

/-- Whether an agent responds on target at every listed situation within a budget.
The check runs at most `budget` simulated machine steps at each listed situation. -/
def hostRespondsWithin (virtue : FiniteBehavioralVirtue) (budget : ℕ) (agent : Code) : Bool :=
  virtue.field.all fun situation =>
    ((outputWithin budget agent [situation]).bind List.head?).any (virtue.target situation)

theorem hostRespondsWithin_primrec (virtue : FiniteBehavioralVirtue) :
    Primrec fun query : Code × ℕ => hostRespondsWithin virtue query.2 query.1 := by
  unfold hostRespondsWithin
  induction virtue.field with
  | nil => exact const true
  | cons situation rest ih =>
      have response : Primrec fun query : Code × ℕ =>
          (outputWithin query.2 query.1 [situation]).bind List.head? :=
        option_bind (outputWithin_primrec.comp (pair (pair fst (const [situation])) snd))
          (list_head?.comp snd).to₂
      have hits : Primrec fun query : Code × ℕ =>
          ((outputWithin query.2 query.1 [situation]).bind List.head?).any
            (virtue.target situation) := by
        refine (option_casesOn response (const false)
          (virtue.target_primrec.comp (const situation) snd).to₂).of_eq ?_
        intro query
        cases (outputWithin query.2 query.1 [situation]).bind List.head? <;> rfl
      exact (Primrec.and.comp hits ih).of_eq fun query => by simp [List.all_cons]

theorem hostBoundedPossession_decidable (virtue : FiniteBehavioralVirtue) (budget : ℕ) :
    ComputablePred fun agent => hostRespondsWithin virtue budget agent = true :=
  ComputablePred.computable_iff.mpr
    ⟨hostRespondsWithin virtue budget,
      ((hostRespondsWithin_primrec virtue).comp (pair Primrec.id (const budget))).to_comp, rfl⟩

theorem hostRespondsWithin_iff (virtue : FiniteBehavioralVirtue) (budget : ℕ) (agent : Code) :
    hostRespondsWithin virtue budget agent = true ↔
      ∀ situation ∈ virtue.field, ∃ response rest,
        ReducesWithin budget (normalTerm agent .halt [situation]) (encCfg (.halt (response :: rest))) ∧
          virtue.target situation response = true := by
  simp only [hostRespondsWithin, List.all_eq_true]
  refine forall₂_congr fun situation _ => ?_
  constructor
  · intro hits
    obtain ⟨response, found, onTarget⟩ := (Option.any_eq_true _ _).mp hits
    obtain ⟨output, within, head⟩ := Option.bind_eq_some_iff.mp found
    obtain ⟨rest, rfl⟩ := List.head?_eq_some_iff.mp head
    exact ⟨response, rest, (outputWithin_eq_some_iff _ _ _ _).mp within, onTarget⟩
  · rintro ⟨response, rest, within, onTarget⟩
    exact (Option.any_eq_true _ _).mpr
      ⟨response, Option.bind_eq_some_iff.mpr ⟨_, (outputWithin_eq_some_iff _ _ _ _).mpr within, rfl⟩,
        onTarget⟩

/-- Possession is bounded possession at some budget. -/
theorem hostPossesses_iff_exists_within (virtue : FiniteBehavioralVirtue) (agent : Code) :
    HostPossesses virtue.toVirtue agent ↔ ∃ budget, hostRespondsWithin virtue budget agent = true := by
  constructor
  · intro possesses
    suffices ∀ situations : List ℕ, (∀ situation ∈ situations, situation ∈ virtue.field) →
        ∃ budget, ∀ situation ∈ situations, ∃ response rest,
          ReducesWithin budget (normalTerm agent .halt [situation])
              (encCfg (.halt (response :: rest))) ∧
            virtue.target situation response = true by
      obtain ⟨budget, within⟩ := this virtue.field fun _ member => member
      exact ⟨budget, (hostRespondsWithin_iff virtue budget agent).mpr within⟩
    intro situations
    induction situations with
    | nil => exact fun _ => ⟨0, fun _ member => absurd member List.not_mem_nil⟩
    | cons situation rest ih =>
        intro inField
        obtain ⟨restBudget, restWithin⟩ :=
          ih fun other member => inField other (List.mem_cons_of_mem _ member)
        obtain ⟨response, ⟨tail, halts⟩, onTarget⟩ :=
          possesses situation (inField situation List.mem_cons_self)
        obtain ⟨headBudget, headWithin⟩ := exists_reducesWithin_of_reflTransGen halts
        refine ⟨headBudget + restBudget, fun other member => ?_⟩
        rcases List.mem_cons.mp member with rfl | member
        · exact ⟨response, tail, reducesWithin_mono headWithin restBudget, onTarget⟩
        · obtain ⟨otherResponse, otherTail, otherWithin, otherTarget⟩ := restWithin other member
          exact ⟨otherResponse, otherTail,
            by simpa [Nat.add_comm] using reducesWithin_mono otherWithin headBudget, otherTarget⟩
  · rintro ⟨budget, within⟩ situation inField
    obtain ⟨response, rest, reduces, onTarget⟩ :=
      (hostRespondsWithin_iff virtue budget agent).mp within situation inField
    exact ⟨response, ⟨rest, reflTransGen_of_reducesWithin reduces⟩, onTarget⟩

theorem hostBoundedResponsiveness_nontrivial :
    ({agent | hostRespondsWithin finiteResponsiveness 2 agent = true} : Set Code).Nonempty ∧
      ({agent | hostRespondsWithin finiteResponsiveness 2 agent = true} : Set Code)ᶜ.Nonempty := by
  refine ⟨⟨.zero', rfl⟩, ⟨silent, fun within => ?_⟩⟩
  obtain ⟨response, rest, reduces, -⟩ :=
    (hostRespondsWithin_iff finiteResponsiveness 2 silent).mp within 0 List.mem_cons_self
  have := haltsWith_iff.mp (reflTransGen_of_reducesWithin reduces)
  simp [silent_eval] at this

/-- **The budget is not what an agent computes**, for virtue possession over host
agents. -/
theorem hostBoundedResponsiveness_not_invariant :
    ¬ ObservationInvariant HaltsWith
      {agent | hostRespondsWithin finiteResponsiveness 2 agent = true} := fun invariant =>
  rice invariant hostBoundedResponsiveness_nontrivial
    (hostBoundedPossession_decidable finiteResponsiveness 2)

/-! ## Semi-decidability -/

/-- **Possession of a finite-field virtue is semi-decidable**: search for a budget
within which the agent responds on target throughout the field. -/
theorem hostPossession_re (virtue : FiniteBehavioralVirtue) :
    REPred (HostPossesses virtue.toVirtue) := by
  have search : Partrec fun agent : Code =>
      Nat.rfind fun budget => Part.some (hostRespondsWithin virtue budget agent) :=
    Partrec.rfind (hostRespondsWithin_primrec virtue).to_comp
  refine search.dom_re.of_eq fun agent => Nat.rfind_dom.trans ?_
  rw [hostPossesses_iff_exists_within]
  constructor
  · rintro ⟨budget, found, -⟩
    exact ⟨budget, (Part.mem_some_iff.mp found).symm⟩
  · rintro ⟨budget, within⟩
    exact ⟨budget, Part.mem_some_iff.mpr within.symm, fun _ => trivial⟩

/-- **Failing to possess a nontrivial finite-field virtue is not semi-decidable.**
Otherwise possession would be decidable. -/
theorem hostPossession_failure_not_re (virtue : FiniteBehavioralVirtue)
    (nontrivial : (possessors virtue.toVirtue).Nonempty ∧ (possessors virtue.toVirtue)ᶜ.Nonempty) :
    ¬ REPred fun agent => ¬ HostPossesses virtue.toVirtue agent := fun failureRE =>
  hostPossession_not_computable virtue.toVirtue nontrivial
    (ComputablePred.computable_iff_re_compl_re'.mpr ⟨hostPossession_re virtue, failureRE⟩)

theorem finiteResponsiveness_nontrivial :
    (possessors finiteResponsiveness.toVirtue).Nonempty ∧
      (possessors finiteResponsiveness.toVirtue)ᶜ.Nonempty :=
  ⟨⟨.zero', fun situation _ => ⟨0, zero'_responds situation, rfl⟩⟩,
    ⟨silent, fun possesses => by
      obtain ⟨response, responds, -⟩ := possesses 0 List.mem_cons_self
      exact silent_never_responds 0 response responds⟩⟩

/-- Responding at the base situation can be certified by a finite run; failing to
respond there cannot. -/
theorem finiteResponsiveness_certification :
    REPred (HostPossesses finiteResponsiveness.toVirtue) ∧
      ¬ REPred fun agent => ¬ HostPossesses finiteResponsiveness.toVirtue agent :=
  ⟨hostPossession_re _, hostPossession_failure_not_re _ finiteResponsiveness_nontrivial⟩

/-! ## Unbounded fields

For a virtue the silent agent lacks, failing to possess it is at least as hard as
not halting, whatever its field (`hostPossession_failure_not_re_of_silent_fails`).
Faithful reporting, over every situation, is harder still: possession is not
semi-decidable either (`faithfulReport_possession_not_re`), because a watcher
agent reports faithfully exactly while a given code has not yet halted.  Its
possession has the form "for every situation, some budget" with a primitive
recursive check inside (`faithfulReport_iff_forall_exists_within`). -/

/-- Gating a possessing agent: possession by the gated agent is halting of the gate's source. -/
theorem gate_possesses_iff (virtue : BehavioralVirtue) {program : Code}
    (programPossesses : HostPossesses virtue program) (silentFails : ¬ HostPossesses virtue silent)
    (source : Nat.Partrec.Code) :
    HostPossesses virtue (gate program source) ↔ (source.eval 0).Dom := by
  by_cases halts : (source.eval 0).Dom
  · exact iff_of_true ((possessors_invariant virtue _ _
      (haltingGate.observe_gate_of_halts program source halts)).mpr programPossesses) halts
  · exact iff_of_false (fun possesses => silentFails ((possessors_invariant virtue _ _
      (haltingGate.observe_gate_of_diverges program source halts)).mp possesses)) halts

/-- **Failing to possess a virtue the silent agent lacks is not semi-decidable**,
whatever the virtue's field. -/
theorem hostPossession_failure_not_re_of_silent_fails (virtue : BehavioralVirtue) {program : Code}
    (programPossesses : HostPossesses virtue program) (silentFails : ¬ HostPossesses virtue silent) :
    ¬ REPred fun agent => ¬ HostPossesses virtue agent := by
  intro failureRE
  apply ComputablePred.halting_problem_not_re 0
  have gated : REPred fun source : Nat.Partrec.Code => ¬ HostPossesses virtue (gate program source) :=
    Partrec.comp (f := fun agent => Part.assert (¬ HostPossesses virtue agent) fun _ => Part.some ())
      failureRE (gate_primrec program).to_comp
  exact gated.of_eq fun source => not_congr (gate_possesses_iff virtue programPossesses silentFails source)

theorem silent_not_possesses_faithfulReport : ¬ HostPossesses faithfulReport silent := fun possesses => by
  obtain ⟨response, responds, -⟩ := possesses 0 trivial
  exact silent_never_responds 0 response responds

theorem faithfulReport_failure_not_re : ¬ REPred fun agent => ¬ HostPossesses faithfulReport agent :=
  hostPossession_failure_not_re_of_silent_fails faithfulReport id_possesses_faithfulReport
    silent_not_possesses_faithfulReport

/-! ### A watcher -/

theorem watch_partrec : Partrec fun pair : ℕ =>
    (Nat.rfind fun _ => Part.some
      (!(Nat.Partrec.Code.evaln pair.unpair.2 (Denumerable.ofNat Nat.Partrec.Code pair.unpair.1) 0).isSome)).map
      fun _ => pair.unpair.2 := by
  have test : Primrec fun pair : ℕ =>
      !(Nat.Partrec.Code.evaln pair.unpair.2 (Denumerable.ofNat Nat.Partrec.Code pair.unpair.1) 0).isSome :=
    Primrec.not.comp (Primrec.option_isSome.comp (Nat.Partrec.Code.primrec_evaln.comp
      (Primrec.pair (Primrec.pair (Primrec.snd.comp Primrec.unpair)
        ((Primrec.ofNat Nat.Partrec.Code).comp (Primrec.fst.comp Primrec.unpair))) (Primrec.const 0))))
  exact Partrec.map (Partrec.rfind (Computable.partrec (test.to_comp.comp Computable.fst)))
    ((Primrec.snd.comp Primrec.unpair).to_comp.comp Computable.fst).to₂

theorem exists_watch : ∃ watch : Nat.Partrec.Code, ∀ index situation : ℕ,
    watch.eval (Nat.pair index situation) =
      (Nat.rfind fun _ => Part.some
        (!(Nat.Partrec.Code.evaln situation (Denumerable.ofNat Nat.Partrec.Code index) 0).isSome)).map
        fun _ => situation := by
  obtain ⟨watch, spec⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp watch_partrec)
  exact ⟨watch, fun index situation => by rw [spec]; simp⟩

/-- A code for the watcher function. -/
noncomputable def watch : Nat.Partrec.Code := Classical.choose exists_watch

/-- The agent that reports the situation `n` exactly when `source` has not halted
on `0` within `n` steps, and otherwise never responds. -/
noncomputable def watcher (source : Nat.Partrec.Code) : Code :=
  compile (Nat.Partrec.Code.curry watch (Encodable.encode source))

theorem watcher_primrec : Primrec watcher :=
  compile_primrec.comp (Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const watch) Primrec.encode)

theorem dom_iff_exists_evaln (source : Nat.Partrec.Code) :
    (source.eval 0).Dom ↔ ∃ steps, (Nat.Partrec.Code.evaln steps source 0).isSome := by
  rw [Part.dom_iff_mem]
  constructor
  · rintro ⟨output, member⟩
    obtain ⟨steps, found⟩ := Nat.Partrec.Code.evaln_complete.mp member
    exact ⟨steps, Option.isSome_iff_exists.mpr ⟨output, found⟩⟩
  · rintro ⟨steps, halted⟩
    obtain ⟨output, found⟩ := Option.isSome_iff_exists.mp halted
    exact ⟨output, Nat.Partrec.Code.evaln_sound found⟩

/-- **The watcher reports faithfully exactly when the source never halts on `0`.** -/
theorem watcher_possesses_iff (source : Nat.Partrec.Code) :
    HostPossesses faithfulReport (watcher source) ↔ ¬ (source.eval 0).Dom := by
  rw [watcher, hostPossesses_compile_iff, dom_iff_exists_evaln, not_exists]
  refine forall_congr' fun situation => ?_
  simp only [faithfulReport, true_implies, Nat.Partrec.Code.eval_curry, watch,
    Classical.choose_spec exists_watch, Denumerable.ofNat_encode, exists_eq_right, Part.mem_map_iff,
    and_true]
  rw [← Part.dom_iff_mem]
  refine Nat.rfind_dom.trans ?_
  constructor
  · rintro ⟨_, found, -⟩
    simpa using (Part.mem_some_iff.mp found).symm
  · intro notHalted
    exact ⟨0, Part.mem_some_iff.mpr (by simpa using notHalted), fun later => absurd later (Nat.not_lt_zero _)⟩

/-- **Possession of faithful reporting is not semi-decidable.** -/
theorem faithfulReport_possession_not_re : ¬ REPred (HostPossesses faithfulReport) := by
  intro possessionRE
  apply ComputablePred.halting_problem_not_re 0
  have watched : REPred fun source : Nat.Partrec.Code => HostPossesses faithfulReport (watcher source) :=
    Partrec.comp (f := fun agent => Part.assert (HostPossesses faithfulReport agent) fun _ => Part.some ())
      possessionRE watcher_primrec.to_comp
  exact watched.of_eq watcher_possesses_iff

/-- Faithful reporting at one situation, as a finite behavioral virtue. -/
def reportAt (situation : ℕ) : FiniteBehavioralVirtue where
  field := [situation]
  target reported response := decide (response = reported)
  target_primrec := (Primrec.eq.comp Primrec.snd Primrec.fst).decide

/-- **Faithful reporting has the form "for every situation, some budget"**, with a
primitive recursive check inside. -/
theorem faithfulReport_iff_forall_exists_within (agent : Code) :
    HostPossesses faithfulReport agent ↔
      ∀ situation, ∃ budget, hostRespondsWithin (reportAt situation) budget agent = true := by
  refine ⟨fun possesses situation => (hostPossesses_iff_exists_within _ agent).mp ?_,
    fun within situation _ => ?_⟩
  · intro other member
    obtain rfl := List.mem_singleton.mp member
    obtain ⟨response, responds, onTarget⟩ := possesses other trivial
    exact ⟨response, responds, by
      simpa [reportAt, FiniteBehavioralVirtue.toVirtue, faithfulReport] using onTarget⟩
  · obtain ⟨response, responds, onTarget⟩ :=
      (hostPossesses_iff_exists_within _ agent).mpr (within situation) situation List.mem_cons_self
    exact ⟨response, responds, by
      simpa [reportAt, FiniteBehavioralVirtue.toVirtue, faithfulReport] using onTarget⟩

/-- **Faithful reporting is neither certifiable nor refutable by finite
behavior**: neither possession nor its failure is semi-decidable. -/
theorem faithfulReport_neither_certifiable_nor_refutable :
    ¬ REPred (HostPossesses faithfulReport) ∧
      ¬ REPred fun agent => ¬ HostPossesses faithfulReport agent :=
  ⟨faithfulReport_possession_not_re, faithfulReport_failure_not_re⟩

/-! ## Axiom audit -/

#print axioms hostPossession_not_computable
#print axioms hostPossesses_iff_possessesDisposition
#print axioms tail_never_responds
#print axioms responsiveness_acts_all_hit
#print axioms faithfulReport_not_computable
#print axioms hostPossesses_compile_iff
#print axioms hostBoundedPossession_decidable
#print axioms hostPossesses_iff_exists_within
#print axioms hostBoundedResponsiveness_not_invariant
#print axioms hostPossession_re
#print axioms finiteResponsiveness_certification
#print axioms hostPossession_failure_not_re_of_silent_fails
#print axioms faithfulReport_iff_forall_exists_within
#print axioms faithfulReport_neither_certifiable_nor_refutable

end Mettapedia.Ethics.HostVirtuePossession
