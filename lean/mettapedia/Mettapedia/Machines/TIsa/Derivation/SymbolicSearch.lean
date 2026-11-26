import Mettapedia.Machines.TIsa.Derivation.SymbolicAllocation
import Mettapedia.Machines.TIsa.Derivation.SymbolicReopening

/-!
# Symbolic search over finite programs and occurrence stores

Search chooses one fresh opening and allocation per alternative. This
is complete at the level of rule and input occurrences, collection
claims, and result models, independently of the opening in a source
firing. A successful search publishes the residual knowledge; a failed
candidate consumes neither a live occurrence nor a fresh identity.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation.SymbolicFiring

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open RuleSyntax.OneFrame (Terms)
open RuleSyntax.JointFirings.SymmetricMatches (ResultModel)
open RuleSyntax.FirstOrderLicence (firingChecks admits_iff_checked)

variable {signature : LPSignature}

abbrev Rules (signature : LPSignature) := List (RuleSyntax.Rule (Terms (Term signature)))
def Rules.program (rules : Rules signature) : RuleSyntax.Program (Terms (Term signature)) :=
  {rule | rule ∈ rules}

structure Attempt (rules : Rules signature) (before : LiveWorld signature) where
  seed : Selection (program := rules.program) before.state
  allocation : seed.firing.selection.made = before.reserve 0 seed.firing.selection.made.length

structure Accepted (rules : Rules signature) (before : LiveWorld signature) where
  selected : Selection (program := rules.program) before.state
  allocation : selected.firing.selection.made = before.reserve 0 selected.firing.selection.made.length
  solution : Subst signature
  solved : (FirstOrder.action signature).Principal (problem selected) solution
  admissible : Admitted selected

namespace Accepted

def publish {rules : Rules signature} {before : LiveWorld signature}
    (success : Accepted rules before) : LiveWorld signature :=
  before.commit success.selected.firing success.allocation

theorem principal {rules : Rules signature} {before : LiveWorld signature}
    (success : Accepted rules before) :
    (FirstOrder.action signature).Principal success.publish.state.knowledge success.solution :=
  success.solved

end Accepted

variable [DecidableEq signature.vars] [DecidableEq signature.constants] [DecidableEq signature.functionSymbols]
  (slots : signature.vars ≃ ℕ) (rules : Rules signature) (before : LiveWorld signature)

def attemptAt (rule : { r // r ∈ rules })
    (pick : { p // p ∈ portChoices before.live rule.val.body.take.length rule.val.body.read.length }) :
    Attempt rules before :=
  let opened := before.prepare slots rule.val rule.property 0 0
  ⟨opened.selected before.live before.visible pick, by
    change before.reserve 0 rule.val.body.produce.length =
      before.reserve 0 (before.reserve 0 rule.val.body.produce.length).length
    rw [before.reserve_length]⟩

def attemptsOf (rule : { r // r ∈ rules }) : List (Attempt rules before) :=
  (portChoices before.live rule.val.body.take.length rule.val.body.read.length).attach.map
    (attemptAt slots rules before rule)

def attempts : List (Attempt rules before) :=
  rules.attach.flatMap (attemptsOf slots rules before)

structure Pending (rules : Rules signature) (before : LiveWorld signature) where
  selected : Selection (program := rules.program) before.state
  allocation : selected.firing.selection.made = before.reserve 0 selected.firing.selection.made.length
  solution : Subst signature
  solved : unifyTotal (problem selected) = some solution

def Attempt.solve {rules : Rules signature} {before : LiveWorld signature}
    (attempt : Attempt rules before) : Option (Pending rules before) :=
  match found : proposeCollections attempt.seed with
  | none => none
  | some (answer, chosen) =>
    have geometry := proposed_keeps_selection found
    have same : chosen.firing.selection.made = attempt.seed.firing.selection.made :=
      congrArg (fun f => f.selection.made) geometry
    some ⟨chosen, by rw [same]; exact attempt.allocation, answer, proposed_principal_solution found⟩

def Pending.check {rules : Rules signature} {before : LiveWorld signature}
    (trial : Pending rules before) : Option (Accepted rules before) :=
  if holds : firingChecks trial.solution before.state trial.selected.firing = true then
    some ⟨trial.selected, trial.allocation, trial.solution, FirstOrder.accepted_principal _ _ trial.solved,
      (admits_iff_checked _ _ _ trial.solved).mpr ⟨trial.selected.shaped, trial.selected.enabled, holds⟩⟩
  else none

def Attempt.check {rules : Rules signature} {before : LiveWorld signature}
    (attempt : Attempt rules before) : Option (Accepted rules before) :=
  attempt.solve.bind Pending.check

theorem Attempt.check_selected {rules : Rules signature} {before : LiveWorld signature}
    (attempt : Attempt rules before) (chosen : Selection (program := rules.program) before.state)
    (answer : Subst signature) (found : evaluateInferred attempt.seed = some (answer, chosen)) :
    ∃ success, attempt.check = some success ∧ success.selected = chosen := by
  obtain ⟨proposed, allowed⟩ := (evaluateInferred_exact attempt.seed answer chosen).mp found
  have passes := (admits_iff_checked _ _ _ (proposed_principal_solution proposed)).mp allowed
  simp only [Attempt.check, Attempt.solve]
  split
  · rename_i absent
    rw [proposed] at absent
    cases absent
  · rename_i foundAnswer foundSelection foundProposal
    have equal := Option.some.inj (foundProposal.symm.trans proposed)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj equal
    simp only [Option.bind_some, Pending.check, dif_pos passes.2.2]
    exact ⟨_, rfl, rfl⟩

/-- Completeness of search is stated with the original firing's resource
uses and collect claims. Made IDs may be freshened along with local variables. -/
theorem attempts_cover (source : Firing before.state rules.program)
    (admitted : source.Admits (act signature) before.state) :
    ∃ attempt ∈ attempts slots rules before, ∃ success, attempt.check = some success ∧
      SameInput source success.selected.firing := by
  let rule : { r // r ∈ rules } := ⟨source.rule, source.member⟩
  let opened := before.prepare (program := rules.program) slots rule.val rule.property 0 0
  let take := source.selection.taken
  let read := source.selection.read
  have listed : (take, read) ∈ opened.ports before.live := by
    apply (portChoices_iff before.live _ _ take read).mpr
    refine ⟨admitted.1.2.2.2.1.symm, admitted.1.2.2.2.2.1.symm, admitted.1.2.1, ?_, ?_⟩
    · intro i here
      exact List.mem_toFinset.mp (before.visible.symm ▸ admitted.2.1.taken_subset (List.mem_toFinset.mpr here))
    · intro i here
      have kept := List.mem_toFinset.mpr here
      exact ⟨List.mem_toFinset.mp (before.visible.symm ▸ admitted.2.1.kept_subset kept), fun also =>
        Finset.disjoint_left.mp admitted.2.1.apart (List.mem_toFinset.mpr also) kept⟩
  let pick : { choice // choice ∈ opened.ports before.live } := ⟨(take, read), listed⟩
  let seed := opened.selected before.live before.visible pick
  let chosen := seed.withSeen source.seen (show seed.firing.rule.collect.length = source.seen.length
    from admitted.1.2.2.2.2.2.2)
  have same : SameInput source chosen.firing := ⟨rfl, rfl, rfl, rfl⟩
  have license : Admitted chosen := same.admitted admitted chosen.shaped chosen.enabled
  obtain ⟨answer, solved⟩ := proposed_collections_include_every_admitted_choice seed _ _ license
  have found := (evaluateInferred_exact seed answer chosen).mpr ⟨solved, license⟩
  have allocation : seed.firing.selection.made = before.reserve 0 seed.firing.selection.made.length := by
    change before.reserve 0 rule.val.body.produce.length =
      before.reserve 0 (before.reserve 0 rule.val.body.produce.length).length
    rw [before.reserve_length]
  let attempt : Attempt rules before := ⟨seed, allocation⟩
  have member : attempt ∈ attempts slots rules before := by
    apply List.mem_flatMap.mpr
    refine ⟨rule, List.mem_attach _ _, ?_⟩
    apply List.mem_map.mpr
    exact ⟨pick, List.mem_attach _ _, rfl⟩
  obtain ⟨success, passed, selected⟩ := attempt.check_selected chosen answer found
  exact ⟨attempt, member, success, passed, selected ▸ same⟩

theorem attempts_cover_models (source : Firing before.state rules.program)
    (admitted : source.Admits (act signature) before.state) :
    ∃ attempt ∈ attempts slots rules before, ∃ success, attempt.check = some success ∧
      SameInput source success.selected.firing ∧
      ∀ incoming output,
        ResultModel before.state source incoming output ↔
          ResultModel before.state success.selected.firing incoming output := by
  obtain ⟨attempt, member, success, passed, same⟩ := attempts_cover slots rules before source admitted
  exact ⟨attempt, member, success, passed, same, same.result_models admitted success.admissible⟩

def search : Option (Accepted rules before) :=
  (attempts slots rules before).findSome? Attempt.check

theorem search_empty_iff :
    search slots rules before = none ↔
      ∀ source : Firing before.state rules.program, ¬source.Admits (act signature) before.state := by
  rw [search, List.findSome?_eq_none_iff]
  constructor
  · intro empty source allowed
    obtain ⟨attempt, member, success, chosen, _⟩ := attempts_cover slots rules before source allowed
    rw [empty attempt member] at chosen
    cases chosen
  · intro quiet attempt _
    cases found : attempt.check with
    | none => rfl
    | some success => exact (quiet success.selected.firing success.admissible).elim

end Mettapedia.Machines.TIsa.Derivation.SymbolicFiring
