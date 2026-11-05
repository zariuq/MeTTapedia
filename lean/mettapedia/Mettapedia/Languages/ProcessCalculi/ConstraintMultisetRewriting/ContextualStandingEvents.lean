import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualStandingEntry
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceCensus

/-!
# Indexed source firings as concrete reactive events

Worlds package the actual declaration family and private bank. A publication
or installed invocation carries the existing compiler's actual firing; its
target is computed by that firing. This permits scheduler reasoning across
family changes without giving one shared syntax label to distinct row uses.
Publications may retain a complete negative source census at that same
input index; ordinary publications need no such observation.

Source readiness is independently stated with source admission. The compiler
constructs an invocation at any finite budget. Labels carry these dependent
mathematical indices; this is not a runtime world-copying prescription.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualStandingEvents

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ContextualRuleCode

variable {S : Signature} {atom : S.Srt} {O : Type} {Γ : Ctx S}

structure World (S : Signature) (atom : S.Srt) (O : Type) (context : Ctx S) : Type 1 where
  Local : Type
  locals : Local → MetaArity (codeSignature S atom)
  equality : DecidableEq Local
  current : ContextualConditionalExecution.State locals O context atom
  born : Finset O
  history : List (PropagationHistory.Key O O)

variable [DecidableEq O] [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)]

abbrev Clause (before : World S atom O Γ) {Query : Type}
    (queries : Query → MetaArity (codeSignature S atom)) (equality : DecidableEq Query)
    (plan : ContextualPublication.Plan
      (Term (signature (codeSignature S atom) (ContextualConjunctiveQueries.queryFamily queries before.current.declarations)) Γ atom))
    (picked : Selection O) :=
  letI := before.equality
  letI := equality
  ContextualConditionalClauses.Compiled queries before.locals (before := before.current) plan picked

structure Publication (before : World S atom O Γ) : Type 1 where
  Query : Type
  queries : Query → MetaArity (codeSignature S atom)
  equality : DecidableEq Query
  plan : ContextualPublication.Plan
    (Term (signature (codeSignature S atom) (ContextualConjunctiveQueries.queryFamily queries before.current.declarations)) Γ atom)
  picked : Selection O
  actual : Clause before queries equality plan picked
  negative : letI := before.equality
    Option (ContextualSourceCensus.EmptyCensus before.locals before.current) := none

structure Invocation (before : World S atom O Γ) : Type 1 where
  installation : O
  declaration : Declaration
    (Term (signature (codeSignature S atom) (ContextualSelectionViews.source before.locals before.current.declarations)) Γ atom)
  picked : Selection O
  actual : letI := before.equality
    ContextualStandingEntry.Compiled before.locals before.current installation declaration picked

def clauseTarget (before : World S atom O Γ) {Query : Type}
    (queries : Query → MetaArity (codeSignature S atom)) (equality : DecidableEq Query)
    {plan : ContextualPublication.Plan
      (Term (signature (codeSignature S atom) (ContextualConjunctiveQueries.queryFamily queries before.current.declarations)) Γ atom)}
    {picked : Selection O} (actual : Clause before queries equality plan picked) : World S atom O Γ := by
  letI := before.equality
  letI := equality
  letI := actual.firing.update.equality
  exact ⟨(before.Local ⊕ Query) ⊕ actual.firing.update.Variables,
    ContextualPublication.privateFamily (ContextualClauseFrames.bank queries before.locals) actual.firing.update.declaration,
    inferInstance, actual.firing.target, before.born ∪ picked.made.toFinset, before.history⟩

def Publication.target {before : World S atom O Γ} (publication : Publication before) : World S atom O Γ :=
  clauseTarget before publication.queries publication.equality publication.actual

def Invocation.target {before : World S atom O Γ} (invocation : Invocation before) : World S atom O Γ := by
  letI := before.equality
  exact { clauseTarget before before.locals before.equality invocation.actual.actual with
    history := StandingRuleRows.record invocation.installation invocation.declaration.mode invocation.picked before.history }

def Invocation.fuel {before : World S atom O Γ} (invocation : Invocation before) : Nat := by
  letI := before.equality
  exact invocation.actual.actual.firing.fuel

def Invocation.Admissible {before : World S atom O Γ} (invocation : Invocation before) : Prop :=
  Disjoint invocation.picked.made.toFinset before.born ∧
    StandingRuleRows.Fresh invocation.installation invocation.declaration.mode invocation.picked before.history

def Publication.Admissible {before : World S atom O Γ} (publication : Publication before) : Prop :=
  Disjoint publication.picked.made.toFinset before.born

inductive Action (before : World S atom O Γ) : Type 1 where
  | publish : Publication before → Action before
  | invoke : Invocation before → Action before

def Action.target {before : World S atom O Γ} : Action before → World S atom O Γ
  | .publish publication => publication.target
  | .invoke invocation => invocation.target

def Action.Admissible {before : World S atom O Γ} : Action before → Prop
  | .publish publication => publication.Admissible
  | .invoke invocation => invocation.Admissible

def Action.installation {before : World S atom O Γ} : Action before → Option O
  | .publish _ => none
  | .invoke invocation => some invocation.installation

def Action.taken {before : World S atom O Γ} : Action before → List O
  | .publish publication => publication.picked.taken
  | .invoke invocation => invocation.picked.taken

def Action.made {before : World S atom O Γ} : Action before → List O
  | .publish publication => publication.picked.made
  | .invoke invocation => invocation.picked.made

theorem Action.physical_result {before : World S atom O Γ} (action : Action before) :
    action.target.current.present =
      (before.current.present \ action.taken.toFinset) ∪ action.made.toFinset := by
  cases action with
  | publish publication =>
      let _ := before.equality
      let _ := publication.equality
      exact publication.actual.physical_result
  | invoke invocation =>
      let _ := before.equality
      exact invocation.actual.actual.physical_result

theorem Action.taken_present {before : World S atom O Γ} (action : Action before) :
    action.taken.toFinset ⊆ before.current.present := by
  cases action with
  | publish publication =>
      let _ := before.equality
      let _ := publication.equality
      exact publication.actual.source_admitted.taken_present
  | invoke invocation =>
      let _ := before.equality
      exact invocation.actual.source_admitted.body.taken_present

theorem Action.made_fresh {before : World S atom O Γ} (action : Action before) :
    Disjoint action.made.toFinset before.current.present := by
  cases action with
  | publish publication =>
      let _ := before.equality
      let _ := publication.equality
      exact publication.actual.source_admitted.fresh
  | invoke invocation =>
      let _ := before.equality
      exact invocation.actual.source_admitted.body.fresh

theorem Action.born_mono {before : World S atom O Γ} (action : Action before) :
    before.born ⊆ action.target.born := by
  cases action <;> exact Finset.subset_union_left

theorem Action.consumed_removed {before : World S atom O Γ} (action : Action before)
    {occurrence : O} (taken : occurrence ∈ action.taken) : occurrence ∉ action.target.current.present := by
  rw [action.physical_result]
  intro present
  rcases Finset.mem_union.mp present with kept | made
  · exact (Finset.mem_sdiff.mp kept).2 (List.mem_toFinset.mpr taken)
  · exact Finset.disjoint_left.mp action.made_fresh made
      (action.taken_present (List.mem_toFinset.mpr taken))

theorem Action.absent_stays_absent {before : World S atom O Γ} (action : Action before)
    (admissible : action.Admissible) {occurrence : O}
    (born : occurrence ∈ before.born) (absent : occurrence ∉ before.current.present) :
    occurrence ∉ action.target.current.present := by
  have fresh : Disjoint action.made.toFinset before.born := by
    cases action with
    | publish publication => exact admissible
    | invoke invocation => exact admissible.1
  rw [action.physical_result]
  intro present
  rcases Finset.mem_union.mp present with kept | made
  · exact absent (Finset.mem_sdiff.mp kept).1
  · exact Finset.disjoint_left.mp fresh made born

def Ready (before : World S atom O Γ) (installation : O) : Prop :=
  ∃ declaration picked, ContextualStandingEntry.Admitted before.locals before.current installation declaration picked ∧
    Disjoint picked.made.toFinset before.born ∧
    StandingRuleRows.Fresh installation declaration.mode picked before.history

theorem invocation_ready {before : World S atom O Γ} (invocation : Invocation before)
    (admissible : invocation.Admissible) : Ready before invocation.installation := by
  let _ := before.equality
  exact ⟨invocation.declaration, invocation.picked, invocation.actual.source_admitted, admissible⟩

theorem realize_ready {before : World S atom O Γ} {installation : O} (ready : Ready before installation) (fuel : Nat) :
    ∃ invocation : Invocation before, invocation.installation = installation ∧ invocation.Admissible ∧
      invocation.fuel = fuel := by
  let _ := before.equality
  obtain ⟨declaration, picked, admitted, fresh, history⟩ := ready
  obtain ⟨actual, budget⟩ := ContextualStandingEntry.realize before.locals before.current installation declaration picked admitted fuel
  exact ⟨⟨installation, declaration, picked, actual⟩, rfl, ⟨fresh, history⟩, budget⟩

def epoch (world : World S atom O Γ) : Nat := world.current.occupied.sup id

theorem clause_epoch_increases (before : World S atom O Γ) {Query : Type}
    (queries : Query → MetaArity (codeSignature S atom)) (equality : DecidableEq Query)
    {plan : ContextualPublication.Plan
      (Term (signature (codeSignature S atom) (ContextualConjunctiveQueries.queryFamily queries before.current.declarations)) Γ atom)}
    {picked : Selection O} (actual : Clause before queries equality plan picked) :
    epoch before < epoch (clauseTarget before queries equality actual) := by
  let _ := before.equality
  let _ := equality
  have oldSubset := ContextualActivationScopes.old_scopes_retained before.current.occupied actual.firing.selection
  have oldBound : before.current.occupied.sup id ≤
      (ContextualActivationScopes.after before.current.occupied actual.firing.selection).sup id :=
    Finset.sup_mono oldSubset
  have helper := ContextualFreshFrameScopeLedger.helper_scope_retained
    (ContextualActivationScopes.after before.current.occupied actual.firing.selection)
  have bound := Finset.le_sup (f := id) helper
  change epoch before <
    (ContextualFreshFrameScopeLedger.helperLedger
      (ContextualActivationScopes.after before.current.occupied actual.firing.selection)).sup id
  dsimp only [ContextualFreshFrameScopeLedger.helperScope, ContextualActivationScopes.start, id] at bound
  exact lt_of_lt_of_le (Nat.lt_succ_of_le oldBound) bound

theorem Publication.epoch_increases {before : World S atom O Γ} (publication : Publication before) :
    epoch before < epoch publication.target := clause_epoch_increases before _ _ publication.actual

theorem Invocation.epoch_increases {before : World S atom O Γ} (invocation : Invocation before) :
    epoch before < epoch invocation.target := by
  let _ := before.equality
  exact clause_epoch_increases before _ _ invocation.actual.actual

theorem Invocation.installation_kept {before : World S atom O Γ} (invocation : Invocation before) :
    invocation.installation ∈ invocation.target.current.present := by
  let _ := before.equality
  exact invocation.actual.installation_kept

theorem Action.epoch_increases {before : World S atom O Γ} (action : Action before) :
    epoch before < epoch action.target := by
  cases action with
  | publish publication => exact publication.epoch_increases
  | invoke invocation => exact invocation.epoch_increases

theorem clause_present_born (before : World S atom O Γ) {Query : Type}
    (queries : Query → MetaArity (codeSignature S atom)) (equality : DecidableEq Query)
    {plan : ContextualPublication.Plan
      (Term (signature (codeSignature S atom) (ContextualConjunctiveQueries.queryFamily queries before.current.declarations)) Γ atom)}
    {picked : Selection O} (actual : Clause before queries equality plan picked)
    (subset : before.current.present ⊆ before.born) :
    (clauseTarget before queries equality actual).current.present ⊆ (clauseTarget before queries equality actual).born := by
  let _ := before.equality
  let _ := equality
  change actual.firing.target.present ⊆ before.born ∪ picked.made.toFinset
  rw [actual.physical_result]
  intro occurrence member
  rcases Finset.mem_union.mp member with kept | made
  · exact Finset.mem_union_left _ (subset (Finset.mem_sdiff.mp kept).1)
  · exact Finset.mem_union_right _ made

theorem Action.present_born {before : World S atom O Γ} (action : Action before)
    (subset : before.current.present ⊆ before.born) : action.target.current.present ⊆ action.target.born := by
  cases action with
  | publish publication => exact clause_present_born before _ _ publication.actual subset
  | invoke invocation =>
      let _ := before.equality
      exact clause_present_born before _ _ invocation.actual.actual subset

omit [DecidableEq S.Srt] [∀ sort, DecidableEq (S.Op sort)] in
theorem ready_present {before : World S atom O Γ} {installation : O} (ready : Ready before installation) :
    installation ∈ before.current.present := by
  obtain ⟨declaration, picked, admitted, _, _⟩ := ready
  exact admitted.body.read_present (by simp [ContextualStandingEntry.selected, StandingRuleRows.selection])

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualStandingEvents
