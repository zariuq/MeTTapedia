import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersPrincipal
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardRefutation

/-!
# Equation firings guarded by the absence of other left-hand sides

The general form of an absence condition on the binder-bearing core. A firing of one equation
(`fire`) of a family carries one `.absent` check of the guarded contextual step per **carrier**: an
equation of the same family whose left-hand side must not match. The carriers' holes are freshened at
the firing's scope and no take equation constrains them, so a check asks, over every future solution
of the firing, that no instance of the carrier's left-hand side is the call.

- `guarded_checks_iff`: the checks hold exactly when, at every reading of the call that the firing
  equation matches, no carrier matches (`CarriersAbsent`, defined from `Matches` alone).
- `guarded_admitted_iff`, `guarded_admitted_iff_determined`: admission is the plain firing's admission
  together with that absence; at a call every solution reads the same way, it is "the firing equation
  matches and no carrier does".
- **Decision** (`certifiesGuarded`): each carrier's joint problem is refuted by the existing guard
  refuter `ContextualGuardRefutation.certifiesAbsence`. Sound (`certified_guarded`); complete for Miller
  patterns in the pattern fragment (`certifies_guarded_of_absent`); a matched carrier is never certified
  absent at any budget (`guarded_never_certified`), and zero fuel certifies nothing.
- **Host** (`guarded_is_guarded_step`): every such firing is a `ContextualGuardedStep.Step`. Its
  configuration and rows are those of the plain firing (`guarded_reads_as_plain`): checks observe.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open ContextualWorldScopeLedger ContextualScopeSupport
open ContextualPatternFragment (Pattern ProblemPattern generator_pattern instantiate_preserves map_patterns)

variable {S : Signature} {Γ : Ctx S} {sort : S.Srt} {ι : Type} (program : ι → Equation S Γ sort)

/-! ## The guarded rule -/

/-- The check of carrier `key`: its left-hand side over the rule's own holes. -/
def guardPattern {V : Type} (captures : V → MetaArity S) (key : ι) :
    Term (signature S (raw program captures)) Γ sort :=
  instantiate (schemaMap program captures key) (program key).lhs

/-- **The guarded rule**: the firing of `fire`, with one absence check per carrier. -/
def guardedRule {V : Type} (captures : V → MetaArity S) (fire : ι) (carriers : List ι) :
    RuleInstance (Term (signature S (raw program captures)) Γ sort) :=
  { rule program captures fire with checks := carriers.map fun key => .absent (guardPattern program captures key) }

/-- The check of carrier `key`, freshened at the firing's scope. -/
abbrev guardAt (state : State program) (key : ι) :
    Term (signature S (active program state.1.declarations)) Γ sort :=
  instantiate (schemaAt program state.1.declarations key (ruleScope state.1.occupied state.2)) (program key).lhs

/-- The guarded firing is admitted. -/
abbrev GuardedAdmitted (state : State program) (fire : ι) (carriers : List ι) : Prop :=
  ContextualGuardedStep.Valid (locals program) state.1.declarations state.1.occupied (selection state.2)
    (guardedRule program state.1.declarations fire carriers) state.1.inventory.rows state.1.inventory.configuration
    (fun _ => output program state.1.declarations fire state.1.occupied state.2)

/-- The checks of the guarded firing, as the guarded step asks them. -/
abbrev GuardedChecks (state : State program) (fire : ι) (carriers : List ι) : Prop :=
  ∀ check ∈ (ContextualActivatedStep.prepared (locals program) state.1.declarations state.1.occupied
      (selection state.2) (guardedRule program state.1.declarations fire carriers) state.1.inventory.rows).rule.checks,
    ContextualGuardSemantics.Ask (locals program)
      (ContextualActivatedStep.problem (locals program) state.1.declarations state.1.occupied (selection state.2)
        (guardedRule program state.1.declarations fire carriers) state.1.inventory.rows state.1.inventory.configuration)
      (ContextualGuardedStep.guardRows (locals program) state.1.declarations state.1.inventory.rows)
      state.1.inventory.configuration.present check

/-- **The reference condition.** At every reading of the call that the firing equation matches, no
carrier matches. -/
def CarriersAbsent (state : State program) (fire : ι) (carriers : List ι) : Prop :=
  ∀ {Future : Type} (future : Future → MetaArity S) (solution : Assignment state.1.declarations future)
    (call : Term S Γ sort), ReadsAt program state solution call →
      ∀ θ, Matches (program fire) call θ → ∀ key ∈ carriers, ∀ θ', ¬ Matches (program key) call θ'

/-- Checks add no equation: the firing problem is the plain firing's. -/
theorem guarded_problem (state : State program) (fire : ι) (carriers : List ι) :
    ContextualActivatedStep.problem (locals program) state.1.declarations state.1.occupied (selection state.2)
        (guardedRule program state.1.declarations fire carriers) state.1.inventory.rows
        state.1.inventory.configuration =
      ContextualActivatedStep.problem (locals program) state.1.declarations state.1.occupied (selection state.2)
        (rule program state.1.declarations fire) state.1.inventory.rows state.1.inventory.configuration := rfl

/-- The prepared checks are exactly the carriers' freshened left-hand sides. -/
theorem guarded_checks_list_iff (state : State program) (fire : ι) (carriers : List ι)
    (property : Check (Term (signature S (active program state.1.declarations)) Γ sort) → Prop) :
    (∀ check ∈ (ContextualActivatedStep.prepared (locals program) state.1.declarations state.1.occupied
        (selection state.2) (guardedRule program state.1.declarations fire carriers) state.1.inventory.rows).rule.checks,
      property check) ↔ ∀ key ∈ carriers, property (.absent (guardAt program state key)) := by
  have members : ∀ check, check ∈ (ContextualActivatedStep.prepared (locals program) state.1.declarations
      state.1.occupied (selection state.2) (guardedRule program state.1.declarations fire carriers)
      state.1.inventory.rows).rule.checks ↔ ∃ key ∈ carriers, check = .absent (guardAt program state key) := by
    intro check
    change check ∈ (carriers.map fun key => Check.absent (guardPattern program state.1.declarations key)).map
      (Check.map (ContextualFreshening.termAt (locals program) state.1.declarations
        (ruleScope state.1.occupied state.2))) ↔ _
    simp only [List.map_map, List.mem_map, Function.comp_def]
    constructor
    · rintro ⟨key, member, rfl⟩
      refine ⟨key, member, ?_⟩
      change Check.absent (ContextualFreshening.termAt (locals program) state.1.declarations
        (ruleScope state.1.occupied state.2) (guardPattern program state.1.declarations key)) = _
      rw [guardPattern, fresh_schema_map]
    · rintro ⟨key, member, rfl⟩
      refine ⟨key, member, ?_⟩
      change Check.absent (ContextualFreshening.termAt (locals program) state.1.declarations
        (ruleScope state.1.occupied state.2) (guardPattern program state.1.declarations key)) = _
      rw [guardPattern, fresh_schema_map]
  constructor
  · intro all key member
    exact all _ ((members _).mpr ⟨key, member, rfl⟩)
  · intro all check member
    obtain ⟨key, keyMember, rfl⟩ := (members check).mp member
    exact all key keyMember

/-! ## Ground solutions with two equations -/

/-- `θ` for the firing equation's holes, `θ'` for one carrier's, closed terms elsewhere. -/
def pairGround [DecidableEq ι] [ClosedTerms S] (fire : ι) (θ : (program fire).Ground) (key : ι)
    (θ' : (program key).Ground) : (name : Local program) → Term S (locals program name).1 (locals program name).2
  | ⟨other, hole⟩ =>
      if same : other = fire then by subst same; exact θ hole
      else if same' : other = key then by subst same'; exact θ' hole else closedAt _ _

theorem pairGround_fire [DecidableEq ι] [ClosedTerms S] (fire : ι) (θ : (program fire).Ground) (key : ι)
    (θ' : (program key).Ground) : (fun hole => pairGround program fire θ key θ' ⟨fire, hole⟩) = θ := by
  funext hole
  simp [pairGround]

theorem pairModel_schema [DecidableEq ι] [ClosedTerms S] {V W : Type} {captures : V → MetaArity S}
    {next : W → MetaArity S} (old : Assignment captures next) (fire : ι) (θ : (program fire).Ground) (key : ι)
    (θ' : (program key).Ground) (apart : key ≠ fire) (scope : Nat) :
    Assignment.compose (extendModel program captures old (pairGround program fire θ key θ'))
        (schemaAt program captures key scope) =
      (program key).assign θ' (active program next) := by
  funext hole
  change instantiate _ (generator _ _) = _
  rw [instantiate_generator]
  simp [extendModel, pairGround, apart, Equation.assign]

variable {program}

/-- **The checks are the absence of every carrier at every reading the firing matches.** -/
theorem guarded_checks_iff [DecidableEq ι] [ClosedTerms S] (state : State program)
    (value : Term (signature S state.1.declarations) Γ sort) (holds : Holds program state value)
    (fire : ι) (carriers : List ι) (apart : fire ∉ carriers) :
    GuardedChecks program state fire carriers ↔ CarriersAbsent program state fire carriers := by
  refine (guarded_checks_list_iff program state fire carriers _).trans ⟨?_, ?_⟩
  · intro asked Future future solution call reads θ matched key member θ' carried
    have different : key ≠ fire := fun same => apart (same ▸ member)
    have fired : Matches (program fire) call (fun hole => pairGround program fire θ key θ' ⟨fire, hole⟩) := by
      rw [pairGround_fire]
      exact matched
    have solved := extended_model_solves state fire solution call reads (pairGround program fire θ key θ') fired
    apply asked key member _ (active program future)
      (extendModel program state.1.declarations solution (pairGround program fire θ key θ')) solved
      state.2 (by rw [holds.1]; exact Finset.mem_singleton_self _)
    change ContextualGuardMatching.Matches (locals program) _ _
      ((state.1.inventory.rows state.2).map (locals program)
        (ContextualSelectionViews.capturedTarget (locals program) state.1.declarations))
    obtain ⟨read, ⟨_, readShared⟩, _, observed⟩ := reads
    have same : read = value := ContextualStoredRows.Row.shared.inj (readShared.symm.trans holds.2)
    rw [same] at observed
    rw [holds.2]
    change instantiate (extendModel program state.1.declarations solution (pairGround program fire θ key θ'))
        (instantiate (schemaAt program state.1.declarations key (ruleScope state.1.occupied state.2))
          (program key).lhs) =
      instantiate (extendModel program state.1.declarations solution (pairGround program fire θ key θ'))
        (instantiate (ContextualSelectionViews.capturedTarget (locals program) state.1.declarations) value)
    rw [← Assignment.instantiate_compose, pairModel_schema program solution fire θ key θ' different,
      ← Assignment.instantiate_compose, extendModel_captures, Assignment.instantiate_compose, observed,
      Rigid.instantiate_include]
    exact ((program key).reads_in_frame θ' (program key).lhs call _).mp carried
  · intro absent key member Future future candidate solved occurrence present matched
    have isCall : occurrence = state.2 := by
      rw [holds.1] at present
      exact Finset.mem_singleton.mp present
    subst isCall
    change ContextualGuardMatching.Matches (locals program) candidate _
      ((state.1.inventory.rows state.2).map (locals program)
        (ContextualSelectionViews.capturedTarget (locals program) state.1.declarations)) at matched
    rw [holds.2] at matched
    change instantiate candidate (instantiate (schemaAt program state.1.declarations key
        (ruleScope state.1.occupied state.2)) (program key).lhs) =
      instantiate candidate (instantiate (ContextualSelectionViews.capturedTarget (locals program)
        state.1.declarations) value) at matched
    have groundSolved := ContextualFrameUnifier.models_compose solved (close future)
    rw [guarded_problem, actual_problem program state fire value holds.2] at groundSolved
    obtain ⟨oldPart, newPart⟩ := (ContextualFrameUnifier.models_append _ _ _).mp groundSolved
    have oldSolved := (ContextualFrameUnifier.models_mapProblem _ _ _).mp oldPart
    have taken := newPart _ (List.mem_singleton_self _)
    dsimp only [Prod.fst, Prod.snd] at taken
    obtain ⟨call, readCall⟩ := holeFree (instantiate (Assignment.compose (Assignment.compose (close future) candidate)
      (ContextualSelectionViews.capturedTarget (locals program) state.1.declarations)) value)
    have reads : ReadsAt program state (Assignment.compose (Assignment.compose (close future) candidate)
        (ContextualSelectionViews.capturedTarget (locals program) state.1.declarations)) call :=
      ⟨value, holds, oldSolved, readCall⟩
    refine absent (ground S) _ call reads
      (fun hole => decode (Assignment.compose (Assignment.compose (close future) candidate)
        (schemaAt program state.1.declarations fire (ruleScope state.1.occupied state.2)) hole)) ?_ key member
      (fun hole => decode (Assignment.compose (Assignment.compose (close future) candidate)
        (schemaAt program state.1.declarations key (ruleScope state.1.occupied state.2)) hole)) ?_
    · unfold Matches
      rw [(program fire).ground_assignment (Assignment.compose (Assignment.compose (close future) candidate)
          (schemaAt program state.1.declarations fire (ruleScope state.1.occupied state.2))),
        Assignment.instantiate_compose, taken, ← Assignment.instantiate_compose]
      exact readCall
    · unfold Matches
      rw [(program key).ground_assignment (Assignment.compose (Assignment.compose (close future) candidate)
          (schemaAt program state.1.declarations key (ruleScope state.1.occupied state.2))),
        Assignment.instantiate_compose, Assignment.instantiate_compose, matched, ← Assignment.instantiate_compose,
        ← Assignment.instantiate_compose]
      exact readCall

/-- A guarded firing is in particular the plain firing of its equation. -/
theorem GuardedAdmitted.toPlain {state : State program} {fire : ι} {carriers : List ι}
    (valid : GuardedAdmitted program state fire carriers) : Admitted program state fire :=
  ⟨⟨valid.take_distinct, valid.output_distinct, valid.take_length, valid.read_length, valid.outputs,
    valid.occurrences, by intro check member; cases member⟩, valid.solvable⟩

/-- Add checks that hold to a plain firing. -/
theorem Admitted.guard {state : State program} {fire : ι} {carriers : List ι}
    (plain : Admitted program state fire) (checks : GuardedChecks program state fire carriers) :
    GuardedAdmitted program state fire carriers :=
  ⟨⟨plain.take_distinct, plain.output_distinct, plain.take_length, plain.read_length, plain.outputs,
    plain.occurrences, checks⟩, plain.solvable⟩

/-- **Admission of a guarded firing.** -/
theorem guarded_admitted_iff [DecidableEq ι] [ClosedTerms S] (state : State program)
    (value : Term (signature S state.1.declarations) Γ sort) (holds : Holds program state value)
    (fire : ι) (carriers : List ι) (apart : fire ∉ carriers) :
    GuardedAdmitted program state fire carriers ↔
      Admitted program state fire ∧ CarriersAbsent program state fire carriers := by
  constructor
  · intro valid
    exact ⟨valid.toPlain, (guarded_checks_iff state value holds fire carriers apart).mp valid.checks⟩
  · rintro ⟨plain, absent⟩
    exact plain.guard ((guarded_checks_iff state value holds fire carriers apart).mpr absent)

/-- **At a call every solution reads the same way**, a guarded firing is admitted exactly when the
firing equation matches the call and no carrier does. -/
theorem guarded_admitted_iff_determined [DecidableEq ι] [ClosedTerms S] (state : State program)
    (call : Term S Γ sort) (determined : Determines program state call)
    (fire : ι) (carriers : List ι) (apart : fire ∉ carriers) :
    GuardedAdmitted program state fire carriers ↔
      (∃ θ, Matches (program fire) call θ) ∧ ∀ key ∈ carriers, ∀ θ', ¬ Matches (program key) call θ' := by
  obtain ⟨⟨Future, future, solution, reads⟩, unique⟩ := determined
  obtain ⟨value, holds, solved, observed⟩ := reads
  have readsCall : ReadsAt program state solution call := ⟨value, holds, solved, observed⟩
  rw [guarded_admitted_iff state value holds fire carriers apart,
    valid_iff state call ⟨⟨Future, future, solution, readsCall⟩, unique⟩ fire]
  constructor
  · rintro ⟨⟨θ, matched⟩, absent⟩
    exact ⟨⟨θ, matched⟩, absent future solution call readsCall θ matched⟩
  · rintro ⟨matched, absent⟩
    refine ⟨matched, ?_⟩
    intro Later later other otherCall readsOther θ _
    rw [unique later other otherCall readsOther]
    exact absent

/-! ## The joint problems of the guard refuter -/

/-- The joint problem of a carrier has no model when the carriers are absent. -/
theorem guarded_joint_unsolvable [DecidableEq ι] [ClosedTerms S] (state : State program)
    (value : Term (signature S state.1.declarations) Γ sort) (holds : Holds program state value)
    (fire : ι) (carriers : List ι) (apart : fire ∉ carriers) (absent : CarriersAbsent program state fire carriers)
    (key : ι) (member : key ∈ carriers) {Next : Type} (next : Next → MetaArity S)
    (combined : Assignment (ContextualSelectionViews.source (locals program) (active program state.1.declarations)) next) :
    ¬ ContextualResidual.Models combined (ContextualGuardRefutation.observedJoint (locals program)
      (active program state.1.declarations)
      (ContextualActivatedStep.problem (locals program) state.1.declarations state.1.occupied (selection state.2)
        (guardedRule program state.1.declarations fire carriers) state.1.inventory.rows state.1.inventory.configuration)
      (ContextualGuardedStep.guardRows (locals program) state.1.declarations state.1.inventory.rows state.2)
      (guardAt program state key)) := by
  intro models
  have frameModels := (ContextualResidual.models_observeProblem combined
    (ContextualGuardRefutation.joint (locals program) (active program state.1.declarations)
      (ContextualActivatedStep.problem (locals program) state.1.declarations state.1.occupied (selection state.2)
        (guardedRule program state.1.declarations fire carriers) state.1.inventory.rows state.1.inventory.configuration)
      (ContextualGuardedStep.guardRows (locals program) state.1.declarations state.1.inventory.rows state.2)
      (guardAt program state key))).mp models
  obtain ⟨before, equation⟩ := (ContextualFrameUnifier.models_append _ _ _).mp frameModels
  have solved := (ContextualFrameUnifier.models_mapProblem _ _ _).mp before
  have asked := (guarded_checks_iff state value holds fire carriers apart).mpr absent
  apply ((guarded_checks_list_iff program state fire carriers _).mp asked key member) Next next _ solved state.2
    (by rw [holds.1]; exact Finset.mem_singleton_self _)
  have matched := equation _ (List.mem_singleton_self _)
  change instantiate combined (ContextualStoredRows.asTemplate (locals program) (active program state.1.declarations)
      ((state.1.inventory.rows state.2).map (locals program)
        (ContextualSelectionViews.capturedTarget (locals program) state.1.declarations))) =
    instantiate combined (instantiate (ContextualSelectionViews.capturedSource (locals program)
      (active program state.1.declarations)) (guardAt program state key)) at matched
  change ContextualGuardMatching.Matches (locals program) _ _
    ((state.1.inventory.rows state.2).map (locals program)
      (ContextualSelectionViews.capturedTarget (locals program) state.1.declarations))
  rw [holds.2] at matched ⊢
  change instantiate combined (instantiate (ContextualSelectionViews.capturedSource (locals program)
      (active program state.1.declarations))
      (instantiate (ContextualSelectionViews.capturedTarget (locals program) state.1.declarations) value)) = _ at matched
  exact (Assignment.instantiate_compose _ _ _).trans (matched.symm.trans (Assignment.instantiate_compose _ _ _).symm)

/-- The joint problem of a carrier is in the pattern fragment. -/
theorem guarded_joint_pattern (state : State program) (patterned : PatternState state) (fire : ι)
    (firePattern : Pattern S (program fire).arity (program fire).lhs) (carriers : List ι) (key : ι)
    (keyPattern : Pattern S (program key).arity (program key).lhs) :
    ProblemPattern (ContextualGuardRefutation.observedJoint (locals program) (active program state.1.declarations)
      (ContextualActivatedStep.problem (locals program) state.1.declarations state.1.occupied (selection state.2)
        (guardedRule program state.1.declarations fire carriers) state.1.inventory.rows state.1.inventory.configuration)
      (ContextualGuardedStep.guardRows (locals program) state.1.declarations state.1.inventory.rows state.2)
      (guardAt program state key)) := by
  obtain ⟨storePattern, value, holds, valuePattern⟩ := patterned
  have firing := firing_problem_pattern state fire ⟨storePattern, value, holds, valuePattern⟩ firePattern
  change ProblemPattern (ContextualResidual.observeProblem (ContextualFrameUnifier.mapProblem _ _ ++ _))
  rw [ContextualResidual.observeProblem, List.map_append]
  apply problem_pattern_append
  · rw [← ContextualResidual.observeProblem, ContextualResidual.observeProblem_mapProblem]
    exact map_patterns _ (fun _ => generator_pattern _) _ firing
  · intro equation member
    have only := List.mem_singleton.mp member
    subst equation
    have rowPattern : Pattern S (ContextualSelectionViews.source (locals program) (active program state.1.declarations))
        (ContextualStoredRows.asTemplate (locals program) (active program state.1.declarations)
          ((state.1.inventory.rows state.2).map (locals program)
            (ContextualSelectionViews.capturedTarget (locals program) state.1.declarations))) := by
      rw [holds.2]
      exact instantiate_preserves _ (fun _ => generator_pattern _) _
        (instantiate_preserves _ (fun _ => generator_pattern _) _ valuePattern)
    exact ⟨rowPattern, instantiate_preserves _ (fun _ => generator_pattern _) _
        (instantiate_preserves _ (fun _ => generator_pattern _) _ keyPattern)⟩

/-! ## Decision by certified refutation -/

section Decision

variable [DecidableEq ι] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

variable (program) in
/-- **The absence decision.** The existing guard refuter refutes every carrier's joint problem
within its budget. -/
def certifiesGuarded (budget : ι → Nat) (state : State program) (fire : ι) (carriers : List ι) : Bool :=
  letI := state.1.equality
  decide (∀ key ∈ carriers, ContextualGuardRefutation.certifiesAbsence (locals program)
    (active program state.1.declarations) (budget key)
    (ContextualActivatedStep.problem (locals program) state.1.declarations state.1.occupied (selection state.2)
      (guardedRule program state.1.declarations fire carriers) state.1.inventory.rows state.1.inventory.configuration)
    (ContextualGuardedStep.guardRows (locals program) state.1.declarations state.1.inventory.rows)
    state.1.inventory.configuration.present (guardAt program state key) = true)

/-- **Soundness.** A certified absence turns an admitted plain firing into an admitted guarded one. -/
theorem certified_guarded (budget : ι → Nat) (state : State program) (fire : ι) (carriers : List ι)
    (plain : Admitted program state fire) (accepted : certifiesGuarded program budget state fire carriers = true) :
    GuardedAdmitted program state fire carriers := by
  let _ : DecidableEq state.1.Names := state.1.equality
  have each := of_decide_eq_true accepted
  refine plain.guard ((guarded_checks_list_iff program state fire carriers _).mpr ?_)
  intro key member
  exact ContextualGuardRefutation.certifiesAbsence_sound (locals program) (active program state.1.declarations)
    (budget key) _ _ _ _ (each key member)

/-- **A residual never counts.** If a carrier matches a reading the firing matches, no budget certifies
the absence. -/
theorem guarded_never_certified [ClosedTerms S] (state : State program)
    (value : Term (signature S state.1.declarations) Γ sort) (holds : Holds program state value)
    (fire : ι) (carriers : List ι) (apart : fire ∉ carriers)
    {Future : Type} {future : Future → MetaArity S} {solution : Assignment state.1.declarations future}
    {call : Term S Γ sort} (reads : ReadsAt program state solution call) (θ : (program fire).Ground)
    (matched : Matches (program fire) call θ) (key : ι) (member : key ∈ carriers) (θ' : (program key).Ground)
    (carried : Matches (program key) call θ') (budget : ι → Nat) :
    certifiesGuarded program budget state fire carriers = false := by
  cases certified : certifiesGuarded program budget state fire carriers with
  | false => rfl
  | true =>
      have valid := certified_guarded budget state fire carriers
        (admitted_of_match state fire solution call reads θ matched) certified
      exact False.elim ((((guarded_admitted_iff state value holds fire carriers apart).mp valid).2
        future solution call reads θ matched) key member θ' carried)

/-- With no fuel, nothing is certified. -/
theorem guarded_zero_budget (state : State program) (value : Term (signature S state.1.declarations) Γ sort)
    (holds : Holds program state value) (fire : ι) (carriers : List ι) (nonempty : carriers ≠ []) :
    certifiesGuarded program (fun _ => 0) state fire carriers = false := by
  let _ : DecidableEq state.1.Names := state.1.equality
  apply decide_eq_false
  intro all
  obtain ⟨key, member⟩ := List.exists_mem_of_ne_nil carriers nonempty
  have atCall := of_decide_eq_true (all key member) state.2 (by rw [holds.1]; exact Finset.mem_singleton_self _)
  rw [ContextualGuardRefutation.zero_fuel_never_certifies_a_row] at atCall
  cases atCall

/-- **Completeness for Miller patterns.** -/
theorem certifies_guarded_of_absent [ClosedTerms S] (state : State program) (patterned : PatternState state)
    (fire : ι) (firePattern : Pattern S (program fire).arity (program fire).lhs) (carriers : List ι)
    (carrierPatterns : ∀ key ∈ carriers, Pattern S (program key).arity (program key).lhs)
    (apart : fire ∉ carriers) (absent : CarriersAbsent program state fire carriers) :
    ∃ budget, certifiesGuarded program budget state fire carriers = true := by
  let _ : DecidableEq state.1.Names := state.1.equality
  obtain ⟨storePattern, value, holds, valuePattern⟩ := patterned
  have each : ∀ key ∈ carriers, ∃ fuel, ContextualGuardRefutation.certifiesRowAbsence (locals program)
      (active program state.1.declarations) fuel
      (ContextualActivatedStep.problem (locals program) state.1.declarations state.1.occupied (selection state.2)
        (guardedRule program state.1.declarations fire carriers) state.1.inventory.rows state.1.inventory.configuration)
      (ContextualGuardedStep.guardRows (locals program) state.1.declarations state.1.inventory.rows state.2)
      (guardAt program state key) = true := by
    intro key member
    obtain ⟨fuel, proof, computed⟩ := ContextualPatternTermination.refutes_of_no_model _
      (guarded_joint_pattern state ⟨storePattern, value, holds, valuePattern⟩ fire firePattern carriers key
        (carrierPatterns key member))
      (fun next combined => guarded_joint_unsolvable state value holds fire carriers apart absent key member next combined)
    refine ⟨fuel, ?_⟩
    unfold ContextualGuardRefutation.certifiesRowAbsence
    rw [computed]
  classical
  refine ⟨fun key => if member : key ∈ carriers then Classical.choose (each key member) else 0,
    decide_eq_true fun key member => decide_eq_true ?_⟩
  intro occurrence present
  rw [holds.1] at present
  rw [Finset.mem_singleton.mp present]
  simpa only [dif_pos member] using Classical.choose_spec (each key member)

end Decision

/-! ## The firing and its host -/

theorem guarded_rule_covered (state : State program) (fire : ι) (carriers : List ι) :
    RuleCovered (privateScopes state.1.scopes) state.1.occupied (guardedRule program state.1.declarations fire carriers) := by
  intro value member
  have old := rule_covered program state fire
  simp only [ruleTerms, guardedRule, List.mem_append] at member
  rcases member with (((inTake | inRead) | inTell) | inChecks) | inProduce
  · exact old value (by simp only [ruleTerms, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inl inTake))))
  · exact old value (by simp only [ruleTerms, List.mem_append]; exact Or.inl (Or.inl (Or.inl (Or.inr inRead))))
  · exact old value (by simp only [ruleTerms, List.mem_append]; exact Or.inl (Or.inl (Or.inr inTell)))
  · obtain ⟨check, checkMember, inTerms⟩ := List.mem_flatMap.mp inChecks
    obtain ⟨key, _, rfl⟩ := List.mem_map.mp checkMember
    have only : value = guardPattern program state.1.declarations key := List.mem_singleton.mp inTerms
    subst only
    exact schema_covered program state.1.declarations state.1.scopes state.1.occupied key (program key).lhs
  · exact old value (by simp only [ruleTerms, List.mem_append]; exact Or.inr inProduce)

variable [DecidableEq ι]

variable (program) in
/-- The state after a guarded firing: the existing activation operations on the guarded rule. -/
def guardedDestination (state : State program) (fire : ι) (carriers : List ι)
    (valid : GuardedAdmitted program state fire carriers) : State program :=
  (⟨ScopedVar (Local program) ⊕ state.1.Names, by letI := state.1.equality; infer_instance,
      active program state.1.declarations, activeScopes state.1.scopes,
      ContextualActivationScopes.after state.1.occupied (selection state.2),
      afterInventory (locals program) state.1.declarations state.1.occupied (selection state.2)
        (guardedRule program state.1.declarations fire carriers) state.1.inventory
        (fun _ => output program state.1.declarations fire state.1.occupied state.2),
      afterInventory_covered (locals program) state.1.declarations state.1.scopes state.1.occupied
        (selection state.2) (guardedRule program state.1.declarations fire carriers) state.1.inventory
        (fun _ => output program state.1.declarations fire state.1.occupied state.2)
        state.1.covered (guarded_rule_covered state fire carriers) valid.occurrences valid.outputs⟩, state.2 + 1)

/-- **The host.** A guarded firing is a firing of `ContextualGuardedStep`, with its checks. -/
theorem guarded_is_guarded_step (state : State program) (fire : ι) (carriers : List ι)
    (valid : GuardedAdmitted program state fire carriers) :
    ContextualGuardedStep.Step (locals program) state.1.declarations state.1.occupied
      (guardedRule program state.1.declarations fire carriers) state.1.inventory.rows state.1.inventory.configuration
      (fun _ => output program state.1.declarations fire state.1.occupied state.2)
      (guardedDestination program state fire carriers valid).1.inventory.configuration
      (guardedDestination program state fire carriers valid).1.inventory.rows
      (guardedDestination program state fire carriers valid).1.occupied :=
  ⟨selection state.2,
    (ContextualGuardedStep.valid_iff_factors (locals program) state.1.declarations _ _ _ _ _ _).mp valid, rfl, rfl, rfl⟩

/-- A guarded firing reads exactly as the plain firing of its equation: checks observe. -/
theorem guarded_reads_as_plain (state : State program) (fire : ι) (carriers : List ι)
    (valid : GuardedAdmitted program state fire carriers) {Future : Type} {future : Future → MetaArity S}
    (solution : Assignment (guardedDestination program state fire carriers valid).1.declarations future)
    (call : Term S Γ sort) :
    ReadsAt program (guardedDestination program state fire carriers valid) solution call ↔
      ReadsAt program (destination program state fire valid.toPlain) solution call :=
  Iff.rfl

theorem guarded_holds_as_plain (state : State program) (fire : ι) (carriers : List ι)
    (valid : GuardedAdmitted program state fire carriers)
    (value : Term (signature S (active program state.1.declarations)) Γ sort) :
    Holds program (guardedDestination program state fire carriers valid) value ↔
      Holds program (destination program state fire valid.toPlain) value :=
  Iff.rfl

theorem guarded_equations_as_plain (state : State program) (fire : ι) (carriers : List ι)
    (valid : GuardedAdmitted program state fire carriers) :
    (guardedDestination program state fire carriers valid).1.inventory.configuration.equations =
      (destination program state fire valid.toPlain).1.inventory.configuration.equations :=
  rfl

#print axioms guarded_checks_list_iff
#print axioms guarded_checks_iff
#print axioms guarded_admitted_iff
#print axioms guarded_admitted_iff_determined
#print axioms guarded_joint_unsolvable
#print axioms guarded_joint_pattern
#print axioms certified_guarded
#print axioms guarded_never_certified
#print axioms guarded_zero_budget
#print axioms certifies_guarded_of_absent
#print axioms guarded_is_guarded_step
#print axioms guarded_reads_as_plain

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders
