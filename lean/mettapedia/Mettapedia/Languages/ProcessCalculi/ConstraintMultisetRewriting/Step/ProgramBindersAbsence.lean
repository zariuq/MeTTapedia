import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramBindersAbsenceGuards

/-!
# Absence of a matching equation at a contextual firing

A call that no equation matches returns itself. That is a negative condition over binder-bearing
equations, so it is an absence guard of the contextual guarded step (`ContextualGuardedStep`),
whose checks are asked over every future solution at the firing's information cut. It is the guarded
firing of `ProgramBindersAbsenceGuards` for one rule and one family of carriers:

- **The rule** (`unmatchedRule`): the return rule `(= $C $C)` takes the call and makes it again; its
  carriers are all the program's equations, so it has one `.absent` check per equation. The take
  equation `$C ≐ call` constrains none of the carriers' holes, so a check asks that no instance of the
  left-hand side is the call, at any future solution.
- **Semantics** (`unmatched_admitted_iff`): the firing is admitted exactly when the store has a reading
  and no reading of the call is matched by any equation (`Unmatched`, defined from `Matches` alone).
- **Decision by certified refutation** (`certifiesUnmatched`): every equation's joint problem is
  refuted by the existing guard refuter (`ContextualGuardRefutation.certifiesAbsence`). It is sound
  (`certified_admitted`), and complete for Miller patterns at a state in the pattern fragment
  (`certifies_of_unmatched`). A residual, including a pending non-pattern problem or exhausted fuel,
  never counts (`matched_never_certified`, `zero_budget_never_certifies`).
- **Stability** (`absence_stable`): an absence observed at the cut stays true under every later
  binding of the call's unknowns.
- **Host** (`unmatched_is_guarded_step`): the firing is a `ContextualGuardedStep.Step`, with the
  checks; the equation firings of `ProgramBindersStep` are the same step with no checks.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualPatternFragment (Pattern generator_pattern)

variable {S : Signature} {Γ : Ctx S} {sort : S.Srt} {ι : Type}

/-! ## The return rule -/

/-- The hole of a whole call: it lists every constant. -/
abbrev callArity (Γ : Ctx S) (sort : S.Srt) : Unit → MetaArity S := fun _ => (Γ, sort)

/-- `(= $C $C)`: the rule an unmatched call fires, before its absence checks are added. -/
def returnEquation (Γ : Ctx S) (sort : S.Srt) : Equation S Γ sort :=
  ⟨Unit, inferInstance, callArity Γ sort, generator (callArity Γ sort) (), generator (callArity Γ sort) ()⟩

theorem return_matches (call : Term S Γ sort) : Matches (returnEquation Γ sort) call (fun _ => call) :=
  instantiate_generator _ _

theorem return_answers (call answer : Term S Γ sort) :
    Answers (returnEquation Γ sort) call answer ↔ answer = call := by
  constructor
  · rintro ⟨θ, matched, answered⟩
    exact Rigid.include_injective _ _ _ (answered.symm.trans matched)
  · intro same
    rw [same]
    exact ⟨fun _ => call, return_matches call, return_matches call⟩

variable (program : ι → Equation S Γ sort)

/-- The program with the return rule beside it. The return rule is never an equation firing: only
the unmatched firing uses it, and only with its absence checks. -/
def withReturn : Option ι → Equation S Γ sort
  | none => returnEquation Γ sort
  | some index => program index

/-- **The reference notion.** No equation of the program matches the call. -/
def Unmatched (call : Term S Γ sort) : Prop := ∀ index θ, ¬ Matches (program index) call θ

/-- Every reading of the current call, in every frame, is unmatched. -/
def UnmatchedReadings (state : State (withReturn program)) : Prop :=
  ∀ {Future : Type} (future : Future → MetaArity S) (solution : Assignment state.1.declarations future)
    (call : Term S Γ sort), ReadsAt (withReturn program) state solution call → Unmatched program call

/-- The check of equation `index`, freshened at the firing's scope. -/
abbrev checkAt (state : State (withReturn program)) (index : ι) :
    Term (signature S (active (withReturn program) state.1.declarations)) Γ sort :=
  guardAt (withReturn program) state (some index)

variable {program}

/-! ## Stability under later bindings -/

/-- **Absence is stable.** If no reading of the call is matched, then under every later binding of
the store's unknowns, in any frame, no instance of any left-hand side is the bound call. -/
theorem absence_stable [ClosedTerms S] (state : State (withReturn program))
    (value : Term (signature S state.1.declarations) Γ sort) (holds : Holds (withReturn program) state value)
    (absent : UnmatchedReadings program state)
    {Future : Type} (future : Future → MetaArity S) (solution : Assignment state.1.declarations future)
    (solved : ContextualFrameUnifier.Models solution state.1.inventory.configuration.equations)
    {Later : Type} (later : Later → MetaArity S) (binding : Assignment future later)
    (index : ι) (θ : Assignment (program index).arity later) :
    instantiate θ (program index).lhs ≠ instantiate binding (instantiate solution value) := by
  intro same
  have boundSolved : ContextualFrameUnifier.Models
      (Assignment.compose (close later) (Assignment.compose binding solution))
      state.1.inventory.configuration.equations :=
    ContextualFrameUnifier.models_compose (ContextualFrameUnifier.models_compose solved binding) (close later)
  obtain ⟨call, readCall⟩ :=
    holeFree (instantiate (Assignment.compose (close later) (Assignment.compose binding solution)) value)
  have reads : ReadsAt (withReturn program) state
      (Assignment.compose (close later) (Assignment.compose binding solution)) call :=
    ⟨value, holds, boundSolved, readCall⟩
  apply absent (ground S) _ call reads index (fun hole => decode (Assignment.compose (close later) θ hole))
  unfold Matches
  rw [(program index).ground_assignment (Assignment.compose (close later) θ), Assignment.instantiate_compose, same,
    ← Assignment.instantiate_compose binding solution, ← Assignment.instantiate_compose (close later)]
  exact readCall

/-! ## The unmatched rule -/

variable [Fintype ι]

variable (ι) in
/-- Every equation of the program, as a carrier of the return rule. -/
noncomputable def returnCarriers : List (Option ι) := (Finset.univ : Finset ι).toList.map some

theorem mem_returnCarriers (key : Option ι) : key ∈ returnCarriers ι ↔ ∃ index, key = some index := by
  simp only [returnCarriers, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
  exact ⟨fun ⟨index, same⟩ => ⟨index, same.symm⟩, fun ⟨index, same⟩ => ⟨index, same.symm⟩⟩

theorem none_apart : (none : Option ι) ∉ returnCarriers ι := by
  intro member
  obtain ⟨_, same⟩ := (mem_returnCarriers none).mp member
  cases same

variable (program) in
/-- **The unmatched rule**: take the call, make it again, provided no equation matches it. -/
noncomputable def unmatchedRule {V : Type} (captures : V → MetaArity S) :
    RuleInstance (Term (signature S (raw (withReturn program) captures)) Γ sort) :=
  guardedRule (withReturn program) captures none (returnCarriers ι)

variable (program) in
/-- The guarded firing of the unmatched rule at the current call is admitted. -/
abbrev UnmatchedAdmitted (state : State (withReturn program)) : Prop :=
  GuardedAdmitted (withReturn program) state none (returnCarriers ι)

/-- The absence of the carriers is unmatchedness at every reading. -/
theorem carriers_absent_iff (state : State (withReturn program)) :
    CarriersAbsent (withReturn program) state none (returnCarriers ι) ↔ UnmatchedReadings program state := by
  constructor
  · intro absent Future future solution call reads index θ matched
    exact absent future solution call reads (fun _ => call) (return_matches call) (some index)
      ((mem_returnCarriers _).mpr ⟨index, rfl⟩) θ matched
  · intro absent Future future solution call reads _ _ key member θ' matched
    obtain ⟨index, rfl⟩ := (mem_returnCarriers key).mp member
    exact absent future solution call reads index θ' matched

/-- **Admission of the unmatched firing.** At a single call, the guarded firing is admitted exactly
when the store has a reading and no equation matches any reading of the call. -/
theorem unmatched_admitted_iff [DecidableEq ι] [ClosedTerms S] (state : State (withReturn program))
    (value : Term (signature S state.1.declarations) Γ sort) (holds : Holds (withReturn program) state value) :
    UnmatchedAdmitted program state ↔
      (∃ call, Reads (withReturn program) state call) ∧ UnmatchedReadings program state := by
  refine (guarded_admitted_iff state value holds none (returnCarriers ι) none_apart).trans ?_
  rw [carriers_absent_iff]
  constructor
  · rintro ⟨plain, absent⟩
    obtain ⟨Later, later, candidate, solved⟩ := plain.solvable
    obtain ⟨old, call, _, reads, _, _⟩ := model_recovers state none value holds candidate solved
    exact ⟨⟨call, _, _, old, reads⟩, absent⟩
  · rintro ⟨⟨call, Future, future, solution, reads⟩, absent⟩
    exact ⟨admitted_of_match state none solution call reads (fun _ => call) (return_matches call), absent⟩

/-- An admitted unmatched firing is in particular an admitted firing of the return rule. -/
theorem UnmatchedAdmitted.toReturn {state : State (withReturn program)} (valid : UnmatchedAdmitted program state) :
    Admitted (withReturn program) state none :=
  GuardedAdmitted.toPlain valid

/-! ## Decision by certified refutation -/

section Decision

variable [DecidableEq ι] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

variable (program) in
/-- **The absence decision**: the guard refuter refutes every equation's joint problem within its
budget. The budget of the return rule itself is never used. -/
noncomputable def certifiesUnmatched (budget : Option ι → Nat) (state : State (withReturn program)) : Bool :=
  certifiesGuarded (withReturn program) budget state none (returnCarriers ι)

/-- **Soundness.** A certified absence at a state with a reading admits the unmatched firing. -/
theorem certified_admitted [ClosedTerms S] (budget : Option ι → Nat) (state : State (withReturn program))
    (reads : ∃ call, Reads (withReturn program) state call)
    (accepted : certifiesUnmatched program budget state = true) : UnmatchedAdmitted program state := by
  obtain ⟨call, Future, future, solution, readsCall⟩ := reads
  exact certified_guarded budget state none (returnCarriers ι)
    (admitted_of_match state none solution call readsCall (fun _ => call) (return_matches call)) accepted

/-- **A residual never counts.** If some reading of the call is matched, no budget certifies its
absence: a pending or solvable problem is never taken for a refutation. -/
theorem matched_never_certified [ClosedTerms S] (state : State (withReturn program))
    (value : Term (signature S state.1.declarations) Γ sort) (holds : Holds (withReturn program) state value)
    {Future : Type} {future : Future → MetaArity S} {solution : Assignment state.1.declarations future}
    {call : Term S Γ sort} (reads : ReadsAt (withReturn program) state solution call)
    (index : ι) (θ : (program index).Ground) (matched : Matches (program index) call θ) (budget : Option ι → Nat) :
    certifiesUnmatched program budget state = false :=
  guarded_never_certified state value holds none (returnCarriers ι) none_apart reads (fun _ => call)
    (return_matches call) (some index) ((mem_returnCarriers _).mpr ⟨index, rfl⟩) θ matched budget

/-- With no fuel, nothing is certified: exhausted fuel is never a refutation. -/
theorem zero_budget_never_certifies [Nonempty ι] (state : State (withReturn program))
    (value : Term (signature S state.1.declarations) Γ sort) (holds : Holds (withReturn program) state value) :
    certifiesUnmatched program (fun _ => 0) state = false := by
  obtain ⟨index⟩ := (inferInstance : Nonempty ι)
  exact guarded_zero_budget state value holds none (returnCarriers ι)
    (List.ne_nil_of_mem ((mem_returnCarriers _).mpr ⟨index, rfl⟩))

/-- **Completeness for Miller patterns.** At a state in the pattern fragment, if no reading of the
call is matched by any equation of a Miller-pattern program, some budget certifies the absence. -/
theorem certifies_of_unmatched [ClosedTerms S] (state : State (withReturn program))
    (patterned : PatternState state) (lhsPattern : ∀ index, Pattern S (program index).arity (program index).lhs)
    (absent : UnmatchedReadings program state) :
    ∃ budget, certifiesUnmatched program budget state = true := by
  refine certifies_guarded_of_absent state patterned none
    (generator_pattern (S := S) (declaration := callArity Γ sort) ()) (returnCarriers ι) ?_ none_apart
    ((carriers_absent_iff state).mpr absent)
  intro key member
  obtain ⟨index, rfl⟩ := (mem_returnCarriers key).mp member
  exact lhsPattern index

end Decision

/-! ## The firing and its host -/

variable [DecidableEq ι]

variable (program) in
/-- The state after the unmatched firing: the existing activation operations on the guarded rule. -/
noncomputable def unmatchedDestination (state : State (withReturn program)) (valid : UnmatchedAdmitted program state) :
    State (withReturn program) :=
  guardedDestination (withReturn program) state none (returnCarriers ι) valid

variable (program) in
/-- **The unmatched firing**, a restriction of the guarded contextual step. -/
def UnmatchedTransition (before after : State (withReturn program)) : Prop :=
  ∃ valid : UnmatchedAdmitted program before, after = unmatchedDestination program before valid

/-- **The host.** The unmatched firing is a firing of `ContextualGuardedStep`, with its checks. -/
theorem unmatched_is_guarded_step (state : State (withReturn program)) (valid : UnmatchedAdmitted program state) :
    ContextualGuardedStep.Step (locals (withReturn program)) state.1.declarations state.1.occupied
      (unmatchedRule program state.1.declarations) state.1.inventory.rows state.1.inventory.configuration
      (fun _ => output (withReturn program) state.1.declarations none state.1.occupied state.2)
      (unmatchedDestination program state valid).1.inventory.configuration
      (unmatchedDestination program state valid).1.inventory.rows
      (unmatchedDestination program state valid).1.occupied :=
  guarded_is_guarded_step state none (returnCarriers ι) valid

/-- The unmatched firing changes the configuration and rows exactly as the return rule does: its
checks observe, they add no equation and no occurrence. -/
theorem unmatched_reads_as_return (state : State (withReturn program)) (valid : UnmatchedAdmitted program state)
    {Future : Type} {future : Future → MetaArity S}
    (solution : Assignment (unmatchedDestination program state valid).1.declarations future) (call : Term S Γ sort) :
    ReadsAt (withReturn program) (unmatchedDestination program state valid) solution call ↔
      ReadsAt (withReturn program) (destination (withReturn program) state none valid.toReturn) solution call :=
  Iff.rfl

theorem unmatched_holds_as_return (state : State (withReturn program)) (valid : UnmatchedAdmitted program state)
    (value : Term (signature S (active (withReturn program) state.1.declarations)) Γ sort) :
    Holds (withReturn program) (unmatchedDestination program state valid) value ↔
      Holds (withReturn program) (destination (withReturn program) state none valid.toReturn) value :=
  Iff.rfl

#print axioms return_answers
#print axioms absence_stable
#print axioms carriers_absent_iff
#print axioms unmatched_admitted_iff
#print axioms certified_admitted
#print axioms matched_never_certified
#print axioms zero_budget_never_certifies
#print axioms certifies_of_unmatched
#print axioms unmatched_is_guarded_step
#print axioms unmatched_reads_as_return

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramBinders
