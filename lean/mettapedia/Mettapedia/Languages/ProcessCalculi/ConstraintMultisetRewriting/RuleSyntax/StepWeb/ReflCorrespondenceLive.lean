import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondence

/-!
# Live and dead child locations

The readout of a hosted state reads the root bag, with each root reflection whose child has taken its step read as
the listener of the child's bag (the commit point). It never reads below a child that has taken its step: such
locations can no longer close into their parent.

* `Live`: the children of the root are live; a child of a live location `m` is live while `m` holds its `Pending`
  token at every solution (the parent has not taken its step).
* A location that is not live is DEAD: its rows and tokens are ignored by the readout.
* `root_child_live` (positive); `grandchild_dead_after_commit` (negative): once the parent holds no `Pending`
  token, its children are dead.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondence

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open MeTTaOperationsComm (psubst PSubst)
open ReflNames (NameLaws nameAction)
open ReflLocated (rootLoc childLoc pendingTok)

variable {O : Type*}

/-- **Live child locations**: the children of the root, and the children of a live location that holds its
`Pending` token at every solution of the knowledge. Every other location is dead. -/
inductive Live (label : O → Pattern) (C : Configuration Pattern O) : Pattern → Prop where
  | root (x p : Pattern) : Live label C (childLoc rootLoc x p)
  | child {m : Pattern} (x p : Pattern) (parent : Live label C m)
      (pending : ∃ o ∈ C.present, ∀ σ : PSubst, nameAction.Models σ C.equations →
        ∃ m' : Pattern, NameLaws (psubst σ (label o)) (psubst σ (pendingTok m m'))) :
      Live label C (childLoc m x p)

/-- **Positive**: every child of the root is live. -/
theorem root_child_live (label : O → Pattern) (C : Configuration Pattern O) (x p : Pattern) :
    Live label C (childLoc rootLoc x p) :=
  .root x p

/-- **Negative**: when no row reads as a `Pending` token of the child `Child(Root, x, p)` at any solution of a
solvable knowledge (the child has taken its step), every child of it is dead. -/
theorem grandchild_dead_after_commit (label : O → Pattern) (C : Configuration Pattern O) (x p y q : Pattern)
    (solvable : ∃ σ : PSubst, nameAction.Models σ C.equations)
    (committed : ∀ o ∈ C.present, ∀ σ : PSubst, nameAction.Models σ C.equations → ∀ m' : Pattern,
      ¬ NameLaws (psubst σ (label o)) (psubst σ (pendingTok (childLoc rootLoc x p) m'))) :
    ¬ Live label C (childLoc (childLoc rootLoc x p) y q) := by
  suffices dead : ∀ l, Live label C l → l ≠ childLoc (childLoc rootLoc x p) y q from
    fun live => dead _ live rfl
  intro l live
  cases live with
  | root x' p' =>
      intro same
      have parents := congrArg (fun t : Pattern => match t with
        | .apply _ (a :: _) => a
        | other => other) same
      simp [childLoc, rootLoc] at parents
  | @child m x' p' _ pending =>
      intro same
      have parentEq : m = childLoc rootLoc x p := by
        have parents := congrArg (fun t : Pattern => match t with
          | .apply _ (a :: _) => a
          | other => other) same
        simpa [childLoc] using parents
      subst parentEq
      obtain ⟨o, present, reads⟩ := pending
      obtain ⟨σ, solved⟩ := solvable
      obtain ⟨m', same'⟩ := reads σ solved
      exact committed o present σ solved m' same'

#print axioms root_child_live
#print axioms grandchild_dead_after_commit

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb.ReflCorrespondence
