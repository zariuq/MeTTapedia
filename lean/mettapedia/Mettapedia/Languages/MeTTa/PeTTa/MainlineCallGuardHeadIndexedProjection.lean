import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan

/-!
# Head-indexed projection for PeTTa call-guard compilation

The reference compiler accepts a complete resolved declaration snapshot and
ignores declarations whose function differs from the requested call head.  A
runtime may instead use a head index, provided that the index retains the
resolved declarations in authored order.  This module proves that the latter
projection is semantically silent for compilation.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardHeadIndexedProjection

open Mettapedia.Languages.MeTTa.PeTTa.MainlineTypeQueryGSLT
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardProjection
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan

set_option autoImplicit false

/-- The authored-order declaration fibre selected by a function-head index. -/
def declarationsForHead (head : String)
    (declarations : List ArrowDeclaration) : List ArrowDeclaration :=
  declarations.filter fun declaration => decide (declaration.function = head)

/-- Selecting the requested head before guard compilation preserves the exact
compilation result, including plan order, source occurrences, and whole-family
outside-fragment fallback. -/
theorem compileRelevantGuards_declarationsForHead
    (owner : SpaceOwner) (revision : Nat) (head : String) (arity : Nat)
    (declarations : List ArrowDeclaration) :
    compileRelevantGuards owner revision head arity
        (declarationsForHead head declarations) =
      compileRelevantGuards owner revision head arity declarations := by
  induction declarations with
  | nil => simp [declarationsForHead, compileRelevantGuards]
  | cons declaration declarations inductionHypothesis =>
      by_cases sameHead : declaration.function = head
      · rw [show declarationsForHead head (declaration :: declarations) =
            declaration :: declarationsForHead head declarations by
          simp [declarationsForHead, sameHead]]
        simp only [compileRelevantGuards]
        by_cases relevant : Relevant declaration head arity
        · simp only [if_pos relevant]
          cases compiled : compileGuard declaration with
          | none => rfl
          | some plan => rw [inductionHypothesis]
        · simp only [if_neg relevant]
          exact inductionHypothesis
      · have notRelevant : ¬ Relevant declaration head arity := by
          intro relevant
          exact sameHead relevant.1
        rw [show declarationsForHead head (declaration :: declarations) =
            declarationsForHead head declarations by
          simp [declarationsForHead, sameHead]]
        simp only [compileRelevantGuards, if_neg notRelevant]
        exact inductionHypothesis

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardHeadIndexedProjection

#print axioms
  Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardHeadIndexedProjection.compileRelevantGuards_declarationsForHead
