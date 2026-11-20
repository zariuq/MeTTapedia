import Mettapedia.OSLF.MeTTaIL.LawNormalReflective
import Mettapedia.OSLF.MeTTaIL.GeneralScopedMatchMachineComparison

/-!
# Firing at canonical forms

A rule fires at the canonical form of its focus when its captures have increasing spines, it
has no premises, and its left side decomposes no set (`CanonicalFiringAdmissible`). The captures
are the canonical forms of the original captures, and the reduct is a permutation of the original
(`rootFiring_canon`). A selected reflective binder must distinguish
parallel multiplicity from set equivalence (`binderOperation_same`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CanonicalBags

open Syntax Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted

/-- Without declared laws, a law move is a permutation. -/
theorem LawStep.bagStep_nil {left right : Pattern} (step : LawStep [] left right) : BagStep left right := by
  induction step with
  | permute unordered permutation => exact .permute unordered permutation
  | members same => exact .members same
  | flatten found => simp at found
  | unit found => simp at found
  | apply _ ih => exact .apply ih
  | lambda _ ih => exact .lambda ih
  | multiLambda _ ih => exact .multiLambda ih
  | substBody _ ih => exact .substBody ih
  | substReplacement _ ih => exact .substReplacement ih
  | element _ ih => exact .element ih

theorem same_iff_lawSame_nil (left right : Pattern) : Same left right ↔ LawSame [] left right := by
  rw [same_iff]
  constructor
  · exact fun related => Relation.EqvGen.mono (fun a b (step : BagStep a b) => step.lawStep []) _ _ related
  · exact fun related => Relation.EqvGen.mono (fun a b (step : LawStep [] a b) => step.bagStep_nil) _ _ related

/-- A compatible binder operation respects bag permutations and set
re-presentation in the other collection kinds. -/
theorem binderOperation_same (profile : Reflection.ReflectionProfile) (rule : RewriteRule)
    (compatible : BinderLawsFor [] profile rule)
    {replacement replacement' body body' : Pattern} (sameReplacement : Same replacement replacement')
    (sameBody : Same body body') :
    Same (ScopedReflectiveExecution.binderOperation profile rule replacement body)
      (ScopedReflectiveExecution.binderOperation profile rule replacement' body') :=
  (same_iff_lawSame_nil _ _).mpr (binderOperation_lawSame profile rule compatible
    ((same_iff_lawSame_nil _ _).mp sameReplacement)
    ((same_iff_lawSame_nil _ _).mp sameBody))

/-! ## Firing at the canonical focus -/

theorem assignSame_canon : ∀ assignment : ScopedRuleMatching.Assignment, AssignSame assignment (canonAssignment assignment)
  | [] => .nil
  | (_, value) :: rest => .cons ⟨rfl, rfl, rfl, (canon_idempotent value.body).symm⟩ (assignSame_canon rest)

/-- A rule fires at canonical forms when its captures have increasing spines, it has no
premises, and its left side decomposes no set. -/
def CanonicalFiringAdmissible (environment : GeneralPremise.Environment) (index : Nat) : Prop :=
  ∀ rule spec, environment.language.rewrites[index]? = some rule →
    GeneralPremise.specification? environment index = some spec →
    IncreasingSpines rule spec ∧ rule.premises = [] ∧ setFree rule.left = true ∧
      BinderLawsFor [] environment.reflection rule

/-- **A root firing has a counterpart at the canonical form of its focus**, with canonical
captures and a permutation-equal result. -/
theorem rootFiring_canon {environment : GeneralPremise.Environment} {bound : List TypeExpr} {type : TypeExpr}
    {source : Pattern} {index : Nat} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : ScopedRuleMatching.Assignment} {history : List GeneralPremise.Event} {target : Pattern}
    (fired : GeneralPremise.RootFiring environment bound type source index trace captured completed history target)
    (admissible : CanonicalFiringAdmissible environment index) :
    ∃ trace' target', GeneralPremise.RootFiring environment bound type (canon source) index trace'
        (canonAssignment captured) (canonAssignment completed) history target' ∧ Same target target' := by
  cases fired with
  | @fire _ _ _ _ _ rule spec _ _ _ _ selected specified admitted sourceSorted matched typed premises reduced
      targetSorted =>
    obtain ⟨increasing, unconditional, setFreeLeft, binderOk⟩ :=
      admissible rule spec selected specified
    rw [unconditional] at premises
    cases premises
    obtain ⟨trace', traced⟩ := GeneralScopedMatchMachine.traced_iff_matches.mpr
      (matches_canon increasing setFreeLeft (GeneralScopedMatchMachine.traced_iff_matches.mp ⟨_, matched⟩))
    obtain ⟨target', reduced', same⟩ := instantiateWith?_same rule spec bound.length
      (ScopedReflectiveExecution.binderOperation environment.reflection rule) (binderOperation_same _ rule binderOk) rule.right
      .right [] 0
      captured (canonAssignment captured) target (assignSame_canon captured) reduced
    refine ⟨trace', target', ?_, same⟩
    refine .fire selected specified admitted (openPatternWellSorted_canon sourceSorted) traced
      (typedAssignment_canon typed) ?_ reduced' (openPatternWellSorted_of_eqvGen ((same_iff _ _).mp same) targetSorted)
    rw [unconditional]
    exact .nil

end Mettapedia.OSLF.MeTTaIL.CanonicalBags
