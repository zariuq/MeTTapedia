import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.Presentations

/-!
# Control: authorizing the parallel frame is not enough

`DerivedContexts.RuleAuthorizesContext` asks only that a congruence premise supply the hole's
source and target and that the two sides be the frame filled with them. It does not ask the two
names to differ. The loop rule `LoopCong`, `{S, ...rest} ~> {S, ...rest}` if `S ~> S`, authorizes
the parallel frame in that sense (`loopCong_authorizes`) and is not a parallel context rule
(`loopCong_not_parallel`).

With it beside the root rule `a ~> b` (`withLoop`), `a ~> b` holds and `{a | z} ~> {b | z}` does
not (`withLoop_not_closed`): the loop rule lifts only steps that return to their source. This is why
`IsParallelContextRule` asks the names to be distinct.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.ContextRuleControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)
open ParallelClosed.Controls (atomA atomB atomZ aToB withoutContext step_aToB)

/-- **The loop rule**: `{S, ...rest} ~> {S, ...rest}` if `S ~> S`. -/
def loopCong : RewriteRule where
  name := "LoopCong"
  typeContext := []
  premises := [.congruence (.fvar "S") (.fvar "S")]
  left := .collection .hashBag [.fvar "S"] (some "rest")
  right := .collection .hashBag [.fvar "S"] (some "rest")

/-- The root rule `a ~> b` beside the loop rule. -/
def withLoop : LanguageDef := { withoutContext with rewrites := [aToB, loopCong] }

/-- The loop rule authorizes the parallel frame in the tree's sense. -/
theorem loopCong_authorizes : RuleAuthorizesContext loopCong (parallelFrame .hashBag "rest") :=
  ⟨"S", "S", by simp [loopCong], rfl, rfl⟩

/-- It is not a parallel context rule: its two names coincide. -/
theorem loopCong_not_parallel (kind : CollType) : ¬ IsParallelContextRule kind loopCong := by
  rintro ⟨source, target, rest, distinct, _, _, premises, _, _⟩
  simp only [loopCong, List.cons.injEq, Premise.congruence.injEq, Pattern.fvar.injEq,
    and_true] at premises
  exact distinct (premises.1.symm.trans premises.2)

/-- The loop rule's match at a collection selects an element and binds the rest. -/
theorem loopCong_match_shape {elements : List Pattern} {tail : Option String}
    {bindings : Bindings}
    (matched : bindings ∈ matchPattern loopCong.left (.collection .hashBag elements tail)) :
    ∃ index, ∃ bound : index < elements.length,
      bindings = [("rest", .collection .hashBag (elements.eraseIdx index) none),
        ("S", elements[index])] := by
  have relation := matchPattern_iff_matchRel.mp matched
  cases relation with
  | collection _ bag =>
      cases bag with
      | cons index bound head tailMatch merged =>
          cases head
          cases tailMatch
          refine ⟨index, bound, ?_⟩
          simp [mergeBindings] at merged
          exact merged.symm

/-- **The loop rule does not lift `a ~> b`**: `{a | z}` never steps to `{b | z}`. -/
theorem withLoop_stuck (base : BasePremiseEvaluator) :
    ¬ Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base withLoop
      (beside .hashBag atomA atomZ) (beside .hashBag atomB atomZ) := by
  rintro ⟨fuel, step⟩
  cases step with
  | rule member matched premises applied =>
      rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic] at matched
      simp only [withLoop, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · have relation := matchPattern_iff_matchRel.mp matched
        cases relation
      · obtain ⟨index, bound, rfl⟩ := loopCong_match_shape matched
        cases premises with
        | cons first rest =>
            cases rest
            cases first with
            | congruence _ premiseMatched merged =>
                have single := matchPattern_iff_matchRel.mp premiseMatched
                cases single
                simp [mergeBindings] at merged
                obtain ⟨_, rfl⟩ := merged
                rw [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
                  applyRuleBindings, applyBindingsScoped_zero_of_binderFree _ _ _ (by decide)]
                  at applied
                simp only [List.length_cons, List.length_nil] at bound
                have small : index = 0 ∨ index = 1 := by omega
                rcases small with rfl | rfl
                · simp [applyBindings, loopCong, beside, atomA, atomB, atomZ] at applied
                · simp [applyBindings, loopCong, beside, atomA, atomB, atomZ] at applied

/-- **Authorizing the parallel frame is not enough for closure**: with the loop rule, `a ~> b`
holds, `{a | z} ~> {b | z}` does not, and the reduction is not closed beside. -/
theorem withLoop_not_closed (base : BasePremiseEvaluator) :
    Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base withLoop atomA atomB ∧
      ¬ Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base withLoop
        (beside .hashBag atomA atomZ) (beside .hashBag atomB atomZ) ∧
      ¬ ClosedBeside (Mettapedia.OSLF.MeTTaIL.ContextualStep.Step base withLoop)
        (beside .hashBag) :=
  ⟨step_aToB (by simp [withLoop]), withLoop_stuck base,
    fun closed => withLoop_stuck base (closed _ _ atomZ (step_aToB (by simp [withLoop])))⟩

#print axioms loopCong_authorizes
#print axioms loopCong_not_parallel
#print axioms loopCong_match_shape
#print axioms withLoop_stuck
#print axioms withLoop_not_closed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.ParallelClosed.ContextRuleControls
