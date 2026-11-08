import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBinders
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualExecutionEndpoints

/-!
# Pattern equations under binders as firings of the contextual step

One schema per equation. A firing takes the call occurrence and makes the right-hand side,
with the equation's holes freshened at the firing's own scope. The equation `lhs ≐ call` joins
the retained store; no matcher is computed by the firing.
- **States** are the endpoints of the contextual step, as for retained λ execution.
- **Readings:** a solution of the store, in any later frame, reads the current call as a source
  term (`ReadsAt`, `Reads`). Holes that no equation constrains stay unknown, so a state may have
  many readings.

**Adequacy.**
- `valid_iff` and `reads_iff`: at a call every solution reads the same way, the firing of an
  equation is admitted exactly when the equation matches, and its result reads exactly as that
  equation's answers. Each matching equation gives one branch.
- `execution_iff`: source rewriting runs from a call reach exactly the readings of the runs of
  the step from the initial state of the call. Answers with unknown holes are kept by the step and
  read at every instance.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open ContextualWorldScopeLedger ContextualScopeSupport

variable {S : Signature} {Γ : Ctx S} {sort : S.Srt} {ι : Type} (program : ι → Equation S Γ sort)

/-- The holes of the whole program, keyed by equation: one family for every firing. -/
abbrev Local := Σ index : ι, (program index).Holes

abbrev locals : Local program → MetaArity S := fun key => (program key.1).arity key.2

variable {V : Type} (captures : V → MetaArity S)

abbrev raw := ContextualActivatedStep.source (locals program) captures
abbrev active := ContextualActivatedStep.target (locals program) captures

def schemaMap (index : ι) : Assignment (program index).arity (raw program captures) :=
  fun hole => generator (raw program captures) (.inl ⟨index, hole⟩)

def schemaAt (index : ι) (scope : Nat) : Assignment (program index).arity (active program captures) :=
  fun hole => generator (active program captures) (.inl ⟨scope, ⟨index, hole⟩⟩)

theorem fresh_schema_map (index : ι) (scope : Nat) {Δ : Ctx S} {result : S.Srt}
    (term : Term (signature S (program index).arity) Δ result) :
    ContextualFreshening.termAt (locals program) captures scope (instantiate (schemaMap program captures index) term) =
      instantiate (schemaAt program captures index scope) term := by
  unfold ContextualFreshening.termAt
  rw [instantiate_comp]
  congr 1
  funext hole
  exact instantiate_generator _ _

/-- The equation itself as a rule over its own holes: take the call, make the right-hand side. -/
def baseRule (index : ι) : RuleInstance (Term (signature S (program index).arity) Γ sort) :=
  ⟨[(program index).lhs], [], [], [], [(program index).rhs]⟩

/-- The schema of one equation. -/
def rule (index : ι) : RuleInstance (Term (signature S (raw program captures)) Γ sort) :=
  (baseRule program index).map (instantiate (schemaMap program captures index))

def selection (current : Nat) : Selection Nat := ⟨[current], [], [current + 1]⟩

def ruleScope (occupied : Finset Nat) (current : Nat) :=
  ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.rulePort (selection current))

def output (index : ι) (occupied : Finset Nat) (current : Nat) :
    Term (signature S (active program captures)) Γ sort :=
  instantiate (schemaAt program captures index (ruleScope occupied current)) (program index).rhs

abbrev State := ContextualExecution.Endpoint (locals program) Nat Γ sort × Nat

theorem actual_problem (state : State program) (index : ι)
    (value : Term (signature S state.1.declarations) Γ sort)
    (isShared : state.1.inventory.rows state.2 = .shared value) :
    ContextualActivatedStep.problem (locals program) state.1.declarations state.1.occupied (selection state.2)
        (rule program state.1.declarations index) state.1.inventory.rows state.1.inventory.configuration =
      ContextualFrameUnifier.mapProblem
          (ContextualSelectionViews.capturedTarget (locals program) state.1.declarations)
          state.1.inventory.configuration.equations ++
        [(instantiate (schemaAt program state.1.declarations index (ruleScope state.1.occupied state.2))
            (program index).lhs,
          instantiate (ContextualSelectionViews.capturedTarget (locals program) state.1.declarations) value)] := by
  change _ ++ [(ContextualFreshening.termAt (locals program) _ _
      (instantiate (schemaMap program _ index) (program index).lhs),
    ContextualFreshening.termAt (locals program) _ _
      (ContextualStoredRows.asTemplate (locals program) _ (state.1.inventory.rows state.2)))] ++ [] ++ [] = _
  rw [isShared, fresh_schema_map]
  simp only [ContextualStoredRows.asTemplate, List.append_nil]
  rw [← ContextualSelectionViews.shared_value_at_port (locals program) state.1.declarations state.1.occupied
    (ContextualActivationScopes.takePort (selection state.2) ⟨0, by simp [selection]⟩) value]
  rfl

theorem admission (state : State program) (index : ι)
    (present : state.1.inventory.configuration.present = {state.2}) :
    ContextualGuardedStep.Requirements (locals program) state.1.declarations state.1.occupied (selection state.2)
      (rule program state.1.declarations index) state.1.inventory.rows state.1.inventory.configuration
      (fun _ => output program state.1.declarations index state.1.occupied state.2) := by
  refine ⟨by simp [selection], by simp [selection], rfl, rfl, ?_, ?_, ?_⟩
  · change [_] = [ContextualFreshening.termAt (locals program) _ _
      (instantiate (schemaMap program _ index) (program index).rhs)]
    rw [fresh_schema_map]
    rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · change ({state.2} : Finset Nat) ⊆ _
      rw [present]
    · exact Finset.empty_subset _
    · exact Finset.disjoint_empty_right _
    · change Disjoint ({state.2 + 1} : Finset Nat) _
      rw [present, Finset.disjoint_singleton_left, Finset.mem_singleton]
      omega
    · intro check member; cases member
  · intro check member; cases member

theorem schema_covered (scopes : V → Finset Nat) (occupied : Finset Nat) (index : ι) {Δ : Ctx S}
    {result : S.Srt} (value : Term (signature S (program index).arity) Δ result) :
    Covered (privateScopes scopes) occupied (instantiate (schemaMap program captures index) value) := by
  apply covered_instantiate
  intro hole _
  change term (privateScopes scopes) (generator (raw program captures) (.inl ⟨index, hole⟩)) ⊆ occupied
  rw [term_generator]
  exact Finset.empty_subset _

theorem rule_covered (state : State program) (index : ι) :
    RuleCovered (privateScopes state.1.scopes) state.1.occupied (rule program state.1.declarations index) := by
  intro value member
  rw [rule, ruleTerms_map] at member
  obtain ⟨original, _, rfl⟩ := List.mem_map.mp member
  exact schema_covered program state.1.declarations state.1.scopes state.1.occupied index original

/-- The firing of equation `index` at `state` is admitted. -/
abbrev Admitted (state : State program) (index : ι) : Prop :=
  ContextualGuardedStep.Valid (locals program) state.1.declarations state.1.occupied (selection state.2)
    (rule program state.1.declarations index) state.1.inventory.rows state.1.inventory.configuration
    (fun _ => output program state.1.declarations index state.1.occupied state.2)

/-! ## Readings -/

/-- The current call occurrence is present alone and holds the shared value `value`. -/
def Holds (state : State program) (value : Term (signature S state.1.declarations) Γ sort) : Prop :=
  state.1.inventory.configuration.present = {state.2} ∧ state.1.inventory.rows state.2 = .shared value

/-- The solution `solution` of the store reads the call as the source term `call`. -/
def ReadsAt (state : State program) {Future : Type} {future : Future → MetaArity S}
    (solution : Assignment state.1.declarations future) (call : Term S Γ sort) : Prop :=
  ∃ value, Holds program state value ∧
    ContextualFrameUnifier.Models solution state.1.inventory.configuration.equations ∧
    instantiate solution value = Rigid.includeTerm future call

/-- Some solution of the store, in some frame, reads the call as `call`. -/
def Reads (state : State program) (call : Term S Γ sort) : Prop :=
  ∃ (Future : Type) (future : Future → MetaArity S) (solution : Assignment state.1.declarations future),
    ReadsAt program state solution call

/-- Some solution reads the call as `call`, and every solution reads it so. -/
def Determines (state : State program) (call : Term S Γ sort) : Prop :=
  Reads program state call ∧
    ∀ {Future : Type} (future : Future → MetaArity S) (solution : Assignment state.1.declarations future)
      (other : Term S Γ sort), ReadsAt program state solution other → other = call

/-- An old solution together with ground solutions of the fresh holes. -/
def extendModel {W : Type} {next : W → MetaArity S} (old : Assignment captures next)
    (solution : (key : Local program) → Term S (locals program key).1 (locals program key).2) :
    Assignment (active program captures) (active program next)
  | .inr name => instantiate (ContextualSelectionViews.capturedTarget (locals program) next) (old name)
  | .inl key => Rigid.includeTerm (active program next) (solution key.name)

theorem extendModel_captures {W : Type} {next : W → MetaArity S} (old : Assignment captures next)
    (solution : (key : Local program) → Term S (locals program key).1 (locals program key).2) :
    Assignment.compose (extendModel program captures old solution)
        (ContextualSelectionViews.capturedTarget (locals program) captures) =
      Assignment.compose (ContextualSelectionViews.capturedTarget (locals program) next) old := by
  funext name
  rw [Assignment.compose, ContextualSelectionViews.capturedTarget, instantiate_generator]
  rfl

theorem extendModel_schema {W : Type} {next : W → MetaArity S} (old : Assignment captures next)
    (solution : (key : Local program) → Term S (locals program key).1 (locals program key).2)
    (index : ι) (scope : Nat) :
    Assignment.compose (extendModel program captures old solution) (schemaAt program captures index scope) =
      (program index).assign (fun hole => solution ⟨index, hole⟩) (active program next) := by
  funext hole
  exact instantiate_generator _ _

variable {program}

theorem ReadsAt.present {state : State program} {Future : Type} {future : Future → MetaArity S}
    {solution : Assignment state.1.declarations future} {call : Term S Γ sort}
    (reads : ReadsAt program state solution call) :
    state.1.inventory.configuration.present = {state.2} := by
  obtain ⟨_, ⟨present, _⟩, _, _⟩ := reads
  exact present

theorem extended_model_solves {W : Type} {next : W → MetaArity S} (state : State program) (index : ι)
    (old : Assignment state.1.declarations next) (call : Term S Γ sort)
    (reads : ReadsAt program state old call)
    (solution : (key : Local program) → Term S (locals program key).1 (locals program key).2)
    (matched : Matches (program index) call (fun hole => solution ⟨index, hole⟩)) :
    ContextualFrameUnifier.Models (extendModel program state.1.declarations old solution)
      (ContextualActivatedStep.problem (locals program) state.1.declarations state.1.occupied (selection state.2)
        (rule program state.1.declarations index) state.1.inventory.rows state.1.inventory.configuration) := by
  obtain ⟨value, ⟨_, isShared⟩, solved, observed⟩ := reads
  rw [actual_problem program state index value isShared]
  apply (ContextualFrameUnifier.models_append _ _ _).mpr
  constructor
  · apply (ContextualFrameUnifier.models_mapProblem _ _ _).mpr
    rw [extendModel_captures]
    exact ContextualFrameUnifier.models_compose solved _
  · intro equation member
    have only := List.mem_singleton.mp member
    subst equation
    dsimp only [Prod.fst, Prod.snd]
    rw [← Assignment.instantiate_compose, extendModel_schema,
      ← Assignment.instantiate_compose, extendModel_captures, Assignment.instantiate_compose, observed,
      Rigid.instantiate_include]
    exact ((program index).reads_in_frame _ (program index).lhs call _).mp matched

/-! ## The initial state of a call -/

def initial (call : Term S Γ sort) : State program := by
  refine (⟨Empty, inferInstance, ground S, (fun impossible => nomatch impossible), ∅,
    ⟨⟨[], {0}⟩, (fun _ => .shared (Rigid.includeTerm (ground S) call)), [], []⟩, ?_⟩, 0)
  refine ⟨Finset.empty_subset _, ?_, Finset.empty_subset _, Finset.empty_subset _⟩
  intro occurrence _
  apply row_shared
  apply (covered_iff _ _ _).mpr
  intro impossible _
  exact nomatch impossible

theorem initial_holds (call : Term S Γ sort) :
    Holds program (initial call) (Rigid.includeTerm (ground S) call) := ⟨rfl, rfl⟩

theorem initial_reads (call : Term S Γ sort) :
    ReadsAt program (initial call) (generator (ground S)) call := by
  refine ⟨_, initial_holds call, ?_, Rigid.instantiate_include _ call⟩
  intro equation member
  cases member

theorem initial_determines (call : Term S Γ sort) : Determines program (initial call) call := by
  refine ⟨⟨_, _, _, initial_reads call⟩, ?_⟩
  intro Future future solution other reads
  obtain ⟨value, ⟨_, isShared⟩, _, observed⟩ := reads
  have same : value = Rigid.includeTerm (ground S) call := ContextualStoredRows.Row.shared.inj isShared.symm
  subst same
  exact (Rigid.include_injective future call other
    ((Rigid.instantiate_include (source := ground S) solution call).symm.trans observed)).symm

/-! ## Firings -/

variable [DecidableEq ι]

variable (program) in
def destination (state : State program) (index : ι) (valid : Admitted program state index) : State program :=
  (⟨ScopedVar (Local program) ⊕ state.1.Names, by letI := state.1.equality; infer_instance,
      active program state.1.declarations, activeScopes state.1.scopes,
      ContextualActivationScopes.after state.1.occupied (selection state.2),
      afterInventory (locals program) state.1.declarations state.1.occupied (selection state.2)
        (rule program state.1.declarations index) state.1.inventory
        (fun _ => output program state.1.declarations index state.1.occupied state.2),
      afterInventory_covered (locals program) state.1.declarations state.1.scopes state.1.occupied
        (selection state.2) (rule program state.1.declarations index) state.1.inventory
        (fun _ => output program state.1.declarations index state.1.occupied state.2)
        state.1.covered (rule_covered program state index) valid.occurrences valid.outputs⟩, state.2 + 1)

variable (program) in
/-- A restriction of the existing contextual step to the program's schemas. Its target is the
inventory that step computes; no source rewrite or answer appears in it. -/
def Transition (before after : State program) : Prop :=
  ∃ (index : ι) (valid : Admitted program before index), after = destination program before index valid

theorem destination_is_core_step (state : State program) (index : ι) (valid : Admitted program state index) :
    ContextualGuardedStep.Step (locals program) state.1.declarations state.1.occupied
      (rule program state.1.declarations index) state.1.inventory.rows state.1.inventory.configuration
      (fun _ => output program state.1.declarations index state.1.occupied state.2)
      (destination program state index valid).1.inventory.configuration
      (destination program state index valid).1.inventory.rows (destination program state index valid).1.occupied :=
  ⟨selection state.2,
    (ContextualGuardedStep.valid_iff_factors (locals program) state.1.declarations _ _ _ _ _ _).mp valid, rfl, rfl, rfl⟩

theorem destination_holds (state : State program) (index : ι) (valid : Admitted program state index)
    (present : state.1.inventory.configuration.present = {state.2}) :
    Holds program (destination program state index valid)
      (output program state.1.declarations index state.1.occupied state.2) := by
  constructor
  · change (state.1.inventory.configuration.present \ {state.2}) ∪ {state.2 + 1} = {state.2 + 1}
    rw [present, Finset.sdiff_self, Finset.empty_union]
  · exact ContextualActivatedStep.produced_row_is_shared (locals program) state.1.declarations (selection state.2)
      (fun _ => output program state.1.declarations index state.1.occupied state.2) state.1.inventory.rows
      (List.mem_singleton_self _)

variable [ClosedTerms S]

omit [DecidableEq ι] in
/-- A solution of an admitted firing recovers a ground reading of the call, a ground solution of the
equation's holes, and the reading of the made right-hand side. -/
theorem model_recovers (state : State program) (index : ι)
    (value : Term (signature S state.1.declarations) Γ sort) (holds : Holds program state value)
    {Future : Type} {future : Future → MetaArity S}
    (candidate : Assignment (active program state.1.declarations) future)
    (solved : ContextualFrameUnifier.Models candidate
      (ContextualActivatedStep.problem (locals program) state.1.declarations state.1.occupied (selection state.2)
        (rule program state.1.declarations index) state.1.inventory.rows state.1.inventory.configuration)) :
    ∃ (old : Assignment state.1.declarations (ground S)) (call : Term S Γ sort) (θ : (program index).Ground),
      ReadsAt program state old call ∧ Matches (program index) call θ ∧
        ∀ answer, instantiate candidate (output program state.1.declarations index state.1.occupied state.2) =
            Rigid.includeTerm future answer →
          instantiate ((program index).assign θ (ground S)) (program index).rhs =
            Rigid.includeTerm (ground S) answer := by
  have groundSolved := ContextualFrameUnifier.models_compose solved (close future)
  rw [actual_problem program state index value holds.2] at groundSolved
  obtain ⟨oldPart, newPart⟩ := (ContextualFrameUnifier.models_append _ _ _).mp groundSolved
  have oldSolved := (ContextualFrameUnifier.models_mapProblem _ _ _).mp oldPart
  have matchedRaw := newPart _ (List.mem_singleton_self _)
  dsimp only [Prod.fst, Prod.snd] at matchedRaw
  obtain ⟨call, readCall⟩ := holeFree (instantiate (Assignment.compose (Assignment.compose (close future) candidate)
    (ContextualSelectionViews.capturedTarget (locals program) state.1.declarations)) value)
  have restored := (program index).ground_assignment (Assignment.compose (Assignment.compose (close future) candidate)
    (schemaAt program state.1.declarations index (ruleScope state.1.occupied state.2)))
  refine ⟨Assignment.compose (Assignment.compose (close future) candidate)
      (ContextualSelectionViews.capturedTarget (locals program) state.1.declarations), call,
    fun hole => decode (Assignment.compose (Assignment.compose (close future) candidate)
      (schemaAt program state.1.declarations index (ruleScope state.1.occupied state.2)) hole),
    ⟨value, holds, oldSolved, readCall⟩, ?_, ?_⟩
  · unfold Matches
    rw [restored, Assignment.instantiate_compose, matchedRaw, ← Assignment.instantiate_compose]
    exact readCall
  · intro answer observed
    unfold output at observed
    rw [restored, Assignment.instantiate_compose, Assignment.instantiate_compose, observed,
      Rigid.instantiate_include]

variable (program) in
/-- Solutions for every rule-local hole that extend one equation's ground solution. -/
def extendGround (index : ι) (θ : (program index).Ground) :
    (key : Local program) → Term S (locals program key).1 (locals program key).2
  | ⟨other, hole⟩ => if same : other = index then by subst same; exact θ hole else closedAt _ _

variable (program) in
theorem extendGround_at (index : ι) (θ : (program index).Ground) :
    (fun hole => extendGround program index θ ⟨index, hole⟩) = θ := by
  funext hole
  simp [extendGround]

theorem admitted_of_match (state : State program) (index : ι) {W : Type} {next : W → MetaArity S}
    (old : Assignment state.1.declarations next) (call : Term S Γ sort) (reads : ReadsAt program state old call)
    (θ : (program index).Ground) (matched : Matches (program index) call θ) :
    Admitted program state index := by
  refine ⟨admission program state index reads.present, ?_⟩
  rw [← extendGround_at program index θ] at matched
  exact ContextualFrameUnifier.solvable_of_model
    (extended_model_solves state index old call reads (extendGround program index θ) matched)

theorem destination_reads (state : State program) (index : ι) (valid : Admitted program state index)
    {W : Type} {next : W → MetaArity S} (old : Assignment state.1.declarations next) (call : Term S Γ sort)
    (reads : ReadsAt program state old call) (θ : (program index).Ground) (matched : Matches (program index) call θ)
    (answer : Term S Γ sort)
    (answered : instantiate ((program index).assign θ (ground S)) (program index).rhs =
      Rigid.includeTerm (ground S) answer) :
    ReadsAt program (destination program state index valid)
      (extendModel program state.1.declarations old (extendGround program index θ)) answer := by
  rw [← extendGround_at program index θ] at matched answered
  refine ⟨_, destination_holds state index valid reads.present,
    extended_model_solves state index old call reads (extendGround program index θ) matched, ?_⟩
  unfold output
  rw [← Assignment.instantiate_compose, extendModel_schema]
  exact ((program index).reads_in_frame _ (program index).rhs answer _).mp answered

theorem destination_reflected (state : State program) (index : ι) (valid : Admitted program state index)
    (value : Term (signature S state.1.declarations) Γ sort) (holds : Holds program state value)
    {Future : Type} {future : Future → MetaArity S}
    (solution : Assignment (destination program state index valid).1.declarations future)
    (answer : Term S Γ sort) (reads : ReadsAt program (destination program state index valid) solution answer) :
    ∃ (old : Assignment state.1.declarations (ground S)) (call : Term S Γ sort),
      ReadsAt program state old call ∧ Answers (program index) call answer := by
  obtain ⟨made, ⟨_, madeShared⟩, solved, observed⟩ := reads
  have produced := (destination_holds state index valid holds.1).2
  have same : made = output program state.1.declarations index state.1.occupied state.2 :=
    ContextualStoredRows.Row.shared.inj (madeShared.symm.trans produced)
  subst same
  obtain ⟨old, call, θ, readsCall, matched, answers⟩ :=
    model_recovers state index value holds solution solved
  exact ⟨old, call, readsCall, θ, matched, answers answer observed⟩

theorem transition_reflected {state after : State program} (transition : Transition program state after)
    (value : Term (signature S state.1.declarations) Γ sort) (holds : Holds program state value)
    {Future : Type} {future : Future → MetaArity S} (solution : Assignment after.1.declarations future)
    (answer : Term S Γ sort) (reads : ReadsAt program after solution answer) :
    ∃ (old : Assignment state.1.declarations (ground S)) (call : Term S Γ sort),
      ReadsAt program state old call ∧ Rewrites program call answer := by
  obtain ⟨index, valid, rfl⟩ := transition
  obtain ⟨old, call, readsCall, answered⟩ := destination_reflected state index valid value holds solution answer reads
  exact ⟨old, call, readsCall, index, answered⟩

/-! ## One firing -/

/-- **Admission is matching.** At a call that every solution reads the same way, the firing of an
equation is admitted exactly when the equation matches the call. -/
theorem valid_iff (state : State program) (call : Term S Γ sort) (determined : Determines program state call)
    (index : ι) : Admitted program state index ↔ ∃ θ, Matches (program index) call θ := by
  obtain ⟨⟨Future, future, solution, reads⟩, unique⟩ := determined
  constructor
  · intro valid
    obtain ⟨Later, later, candidate, solved⟩ := valid.solvable
    obtain ⟨value, holds, _, _⟩ := reads
    obtain ⟨old, other, θ, readsOther, matched, _⟩ := model_recovers state index value holds candidate solved
    rw [unique (ground S) old other readsOther] at matched
    exact ⟨θ, matched⟩
  · rintro ⟨θ, matched⟩
    exact admitted_of_match state index solution call reads θ matched

/-- **One branch per equation.** The result of an admitted firing reads exactly as the answers of
that equation at the call. -/
theorem reads_iff (state : State program) (call : Term S Γ sort) (determined : Determines program state call)
    (index : ι) (valid : Admitted program state index) (answer : Term S Γ sort) :
    Reads program (destination program state index valid) answer ↔ Answers (program index) call answer := by
  obtain ⟨⟨Future, future, solution, reads⟩, unique⟩ := determined
  constructor
  · rintro ⟨Later, later, other, readsAnswer⟩
    obtain ⟨value, holds, _, _⟩ := reads
    obtain ⟨old, recovered, readsCall, answered⟩ :=
      destination_reflected state index valid value holds other answer readsAnswer
    rw [unique (ground S) old recovered readsCall] at answered
    exact answered
  · rintro ⟨θ, matched, answered⟩
    exact ⟨_, _, _, destination_reads state index valid solution call reads θ matched answer answered⟩

/-! ## Runs -/

theorem runs_forward {call answer : Term S Γ sort}
    (runs : Relation.ReflTransGen (Rewrites program) call answer) (state : State program)
    {Future : Type} {future : Future → MetaArity S} (solution : Assignment state.1.declarations future)
    (reads : ReadsAt program state solution call) :
    ∃ after, Relation.ReflTransGen (Transition program) state after ∧ Reads program after answer := by
  induction runs with
  | refl => exact ⟨state, .refl, _, _, solution, reads⟩
  | tail _ rewriting ih =>
      obtain ⟨middle, path, Later, later, old, readsMiddle⟩ := ih
      obtain ⟨index, θ, matched, answered⟩ := rewriting
      let valid := admitted_of_match middle index old _ readsMiddle θ matched
      exact ⟨destination program middle index valid, path.tail ⟨index, valid, rfl⟩, _, _, _,
        destination_reads middle index valid old _ readsMiddle θ matched _ answered⟩

theorem runs_backward {call : Term S Γ sort} {after : State program}
    (path : Relation.ReflTransGen (Transition program) (initial call) after) :
    (∃ value, Holds program after value) ∧
      ∀ answer, Reads program after answer → Relation.ReflTransGen (Rewrites program) call answer := by
  induction path with
  | refl =>
      refine ⟨⟨_, initial_holds call⟩, ?_⟩
      rintro answer ⟨Future, future, solution, reads⟩
      obtain rfl := (initial_determines call).2 future solution answer reads
      exact .refl
  | tail _ transition ih =>
      obtain ⟨⟨value, holds⟩, earlier⟩ := ih
      refine ⟨?_, ?_⟩
      · obtain ⟨index, valid, rfl⟩ := transition
        exact ⟨_, destination_holds _ index valid holds.1⟩
      · rintro answer ⟨Future, future, solution, reads⟩
        obtain ⟨old, middle, readsMiddle, rewriting⟩ :=
          transition_reflected transition value holds solution answer reads
        exact (earlier middle ⟨_, _, old, readsMiddle⟩).tail rewriting

/-- **Adequacy for runs.** The source runs of a call reach exactly the readings of the runs of the
contextual step from its initial state. -/
theorem execution_iff (call answer : Term S Γ sort) :
    Relation.ReflTransGen (Rewrites program) call answer ↔
      ∃ after, Relation.ReflTransGen (Transition program) (initial call) after ∧ Reads program after answer := by
  constructor
  · intro runs
    exact runs_forward runs (initial call) _ (initial_reads call)
  · rintro ⟨after, path, reads⟩
    exact (runs_backward path).2 answer reads

#print axioms actual_problem
#print axioms destination_is_core_step
#print axioms model_recovers
#print axioms initial_determines
#print axioms valid_iff
#print axioms reads_iff
#print axioms runs_forward
#print axioms runs_backward
#print axioms execution_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders
