import Mettapedia.Machines.TIsa.Derivation.SymbolicFiring
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.RoundEveryOrder

/-!
# A firing reads the action of an opening only on its rule

Agreement of raw substitution functions on unused variable names is
unnecessary. The opened premises, tells, guards, collects and outputs
are the finite support of the firing's visible action. This is the
congruence needed to transport a renamed opening through a run.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Derivation.OpeningAction

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open RuleSyntax (Rule Firing)
open RuleSyntax.OneFrame (Terms ext)
open SymbolicFiring (World act)

variable {σ : LPSignature}

theorem body_eq (rule : Rule (Terms (Term σ))) (left right : Subst σ)
    (agrees : ∀ term ∈ rule.terms, left.applyTerm term = right.applyTerm term) :
    rule.body.map left.applyTerm = rule.body.map right.applyTerm := by
  have takes : rule.body.take.map left.applyTerm = rule.body.take.map right.applyTerm :=
    List.map_congr_left fun t found => agrees t (by simp [Rule.terms, found])
  have reads : rule.body.read.map left.applyTerm = rule.body.read.map right.applyTerm :=
    List.map_congr_left fun t found => agrees t (by simp [Rule.terms, found])
  have produces : rule.body.produce.map left.applyTerm = rule.body.produce.map right.applyTerm :=
    List.map_congr_left fun t found => agrees t (by simp [Rule.terms, found])
  have tells : rule.body.tell.map (fun e => (left.applyTerm e.1, left.applyTerm e.2)) =
      rule.body.tell.map (fun e => (right.applyTerm e.1, right.applyTerm e.2)) := by
    apply List.map_congr_left
    intro e inside
    have fst : e.1 ∈ rule.body.tell.map Prod.fst := List.mem_map.mpr ⟨e, inside, rfl⟩
    have snd : e.2 ∈ rule.body.tell.map Prod.snd := List.mem_map.mpr ⟨e, inside, rfl⟩
    exact congrArg₂ Prod.mk (agrees _ (by simp [Rule.terms, fst])) (agrees _ (by simp [Rule.terms, snd]))
  have guards : rule.body.checks.map (Check.map left.applyTerm) = rule.body.checks.map (Check.map right.applyTerm) := by
    apply List.map_congr_left
    intro query found
    have terms (term : Term σ) (used : term ∈ RuleSyntax.checkTerms query) :
        left.applyTerm term = right.applyTerm term := by
      apply agrees
      have inside : term ∈ rule.body.checks.flatMap RuleSyntax.checkTerms :=
        List.mem_flatMap.mpr ⟨query, found, used⟩
      simp [Rule.terms, inside]
    cases query with
    | equal u v =>
      simp only [Check.map, terms u (by simp [RuleSyntax.checkTerms]), terms v (by simp [RuleSyntax.checkTerms])]
    | predicate q p =>
      simp only [Check.map, terms p (by simp [RuleSyntax.checkTerms])]
    | count p n =>
      simp only [Check.map, terms p (by simp [RuleSyntax.checkTerms])]
  unfold RuleInstance.map
  rw [takes, reads, tells, guards, produces]

variable {O : Type} [DecidableEq O] {program : RuleSyntax.Program (Terms (Term σ))} {before : World σ O}

def withOpening (f : Firing O (ext (FirstOrder.action σ)) program before.frame) (opening : Subst σ) :
    Firing O (ext (FirstOrder.action σ)) program before.frame :=
  {f with opening}

omit [DecidableEq O] in
theorem opened_eq (f : Firing O (ext (FirstOrder.action σ)) program before.frame) (opening : Subst σ)
    (agrees : ∀ term ∈ f.rule.terms, opening.applyTerm term = f.opening.applyTerm term) :
    (withOpening (before := before) f opening).opened (act σ) = f.opened (act σ) :=
  body_eq _ _ _ agrees

omit [DecidableEq O] in
theorem collect_eq (f : Firing O (ext (FirstOrder.action σ)) program before.frame) (opening : Subst σ)
    (agrees : ∀ term ∈ f.rule.terms, opening.applyTerm term = f.opening.applyTerm term) :
    (withOpening (before := before) f opening).collectOpened (act σ) = f.collectOpened (act σ) := by
  change f.rule.collect.map opening.applyTerm = f.rule.collect.map f.opening.applyTerm
  exact List.map_congr_left (fun term requested => agrees term (by simp [Rule.terms, requested]))

omit [DecidableEq O] in
theorem fresh_iff (f : Firing O (ext (FirstOrder.action σ)) program before.frame) (opening : Subst σ)
    (agrees : ∀ term ∈ f.rule.terms, opening.applyTerm term = f.opening.applyTerm term) :
    (withOpening (before := before) f opening).Fresh (act σ) before ↔ f.Fresh (act σ) before := by
  constructor
  · intro fresh frame caller localValues
    obtain ⟨ρ, incoming, localTerms⟩ := fresh frame caller localValues
    refine ⟨ρ, incoming, fun term used => ?_⟩
    have agreesBelow := congrArg ρ.applyTerm (agrees term used)
    exact agreesBelow.symm.trans (localTerms term used)
  · intro fresh frame caller localValues
    obtain ⟨ρ, incoming, localTerms⟩ := fresh frame caller localValues
    refine ⟨ρ, incoming, fun term used => ?_⟩
    have agreesBelow := congrArg ρ.applyTerm (agrees term used)
    exact agreesBelow.trans (localTerms term used)

omit [DecidableEq O] in
theorem information_eq (f : Firing O (ext (FirstOrder.action σ)) program before.frame) (opening : Subst σ)
    (agrees : ∀ term ∈ f.rule.terms, opening.applyTerm term = f.opening.applyTerm term) :
    (withOpening (before := before) f opening).information (act σ) before = f.information (act σ) before := by
  unfold Firing.information
  rw [opened_eq (before := before) f opening agrees]
  rfl

omit [DecidableEq O] in
theorem holds_iff (f : Firing O (ext (FirstOrder.action σ)) program before.frame) (opening : Subst σ)
    (agrees : ∀ term ∈ f.rule.terms, opening.applyTerm term = f.opening.applyTerm term)
    (frame : PUnit) (solution : Subst σ) :
    (withOpening (before := before) f opening).Holds (act σ) before (b := frame) solution ↔
      f.Holds (act σ) before (b := frame) solution := by
  unfold Firing.Holds
  rw [opened_eq (before := before) f opening agrees, collect_eq (before := before) f opening agrees]
  rfl

theorem admission_iff (f : Firing O (ext (FirstOrder.action σ)) program before.frame) (opening : Subst σ)
    (agrees : ∀ term ∈ f.rule.terms, opening.applyTerm term = f.opening.applyTerm term) :
    (withOpening (before := before) f opening).Admits (act σ) before ↔ f.Admits (act σ) before := by
  unfold Firing.Admits
  rw [information_eq f opening agrees]
  refine and_congr (and_congr (fresh_iff f opening agrees) Iff.rfl) (and_congr Iff.rfl (and_congr Iff.rfl ?_))
  constructor
  · intro allowed frame solution model
    exact (holds_iff f opening agrees frame solution).mp (allowed frame solution model)
  · intro allowed frame solution model
    exact (holds_iff f opening agrees frame solution).mpr (allowed frame solution model)

theorem result_eq (f : Firing O (ext (FirstOrder.action σ)) program before.frame) (opening : Subst σ)
    (agrees : ∀ term ∈ f.rule.terms, opening.applyTerm term = f.opening.applyTerm term) :
    (withOpening (before := before) f opening).result (act σ) before = f.result (act σ) before := by
  unfold Firing.result
  rw [information_eq f opening agrees, opened_eq (before := before) f opening agrees]
  rfl

open RuleSyntax.JointFirings (OneMember)
open RuleSyntax.StepWeb.Rounds (FiresInOrder stateAfter)

abbrev Member (σ : LPSignature) (O : Type) (program : RuleSyntax.Program (Terms (Term σ))) :=
  OneMember (FirstOrder.action σ) O program

structure SameAction (left right : Member σ O program) : Prop where
  rule : left.rule = right.rule
  select : left.selection = right.selection
  collect : left.seen = right.seen
  terms : ∀ term ∈ left.rule.terms, right.opening.applyTerm term = left.opening.applyTerm term

omit [DecidableEq O] in
private theorem replaces {left right : Member σ O program} (same : SameAction left right) :
    withOpening (before := before) left.firing right.opening = right.firing := by
  cases left
  cases right
  obtain ⟨sameRule, resources, collect, _⟩ := same
  dsimp only at sameRule resources collect
  cases sameRule
  cases resources
  cases collect
  rfl

theorem member_exact {left right : Member σ O program} (same : SameAction left right) :
    (left.firing.Admits (act σ) before ↔ right.firing.Admits (act σ) before) ∧
      left.firing.result (act σ) before = right.firing.result (act σ) before := by
  have forward := admission_iff (before := before) left.firing right.opening same.terms
  have result := result_eq (before := before) left.firing right.opening same.terms
  rw [replaces (before := before) same] at forward result
  exact ⟨forward.symm, result.symm⟩

/-- Every prefix of the serial evaluation uses exactly the same
action when the opened terms and the physical ports agree. -/
theorem sequence_exact {left right : List (Member σ O program)} (same : List.Forall₂ SameAction left right)
    (source : World σ O) :
    (FiresInOrder (FirstOrder.action σ) source left ↔ FiresInOrder (FirstOrder.action σ) source right) ∧
      stateAfter (FirstOrder.action σ) source left = stateAfter (FirstOrder.action σ) source right := by
  induction same generalizing source with
  | nil => exact ⟨Iff.rfl, rfl⟩
  | @cons l r ls rs equal tail ih =>
    obtain ⟨head, reached⟩ := member_exact (before := source) equal
    obtain ⟨legalTail, resultTail⟩ := ih (r.firing.result (act σ) source)
    refine ⟨?_, ?_⟩
    · change (l.firing.Admits _ _ ∧ FiresInOrder _ (l.firing.result _ _) ls) ↔
        r.firing.Admits _ _ ∧ FiresInOrder _ (r.firing.result _ _) rs
      rw [reached]
      exact and_congr head legalTail
    · change stateAfter _ (l.firing.result _ _) ls = stateAfter _ (r.firing.result _ _) rs
      rw [reached]
      exact resultTail

end Mettapedia.Machines.TIsa.Derivation.OpeningAction
