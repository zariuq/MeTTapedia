import Mettapedia.GSLT.LanguageDef.InferenceChecker

/-!
# Exact lookup in finite inference signatures

Unique outer judgment heads turn membership into exact head-and-arity lookup.
This is the generic finite-signature fact used by generated and authored
calculi alike; individual language families need only prove membership and
head uniqueness.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

private theorem filter_judgments_by_head_eq_singleton
    (declarations : List JudgmentDecl) (declaration : JudgmentDecl)
    (headsNodup : (declarations.map JudgmentDecl.head).Nodup)
    (membership : declaration ∈ declarations) :
    declarations.filter (fun candidate =>
      candidate.head == declaration.head &&
        candidate.arity == declaration.arity) = [declaration] := by
  induction declarations with
  | nil => simp at membership
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, List.nodup_cons] at headsNodup
      rcases headsNodup with ⟨headFresh, tailNodup⟩
      rcases List.mem_cons.mp membership with equality | tailMembership
      · subst head
        simp only [List.filter_cons, beq_self_eq_true, Bool.true_and, if_true]
        have tailFilter :
            tail.filter (fun candidate =>
              candidate.head == declaration.head &&
                candidate.arity == declaration.arity) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro candidate candidateMembership matching
          simp only [Bool.and_eq_true, beq_iff_eq] at matching
          apply headFresh
          exact List.mem_map.mpr
            ⟨candidate, candidateMembership, matching.1⟩
        rw [tailFilter]
      · have headsDifferent : head.head ≠ declaration.head := by
          intro headsEqual
          apply headFresh
          exact List.mem_map.mpr
            ⟨declaration, tailMembership, headsEqual.symm⟩
        simp [headsDifferent,
          inductionHypothesis tailNodup tailMembership]

/-- A member of a duplicate-free judgment signature is the unique result of
lookup at its own head and arity. -/
theorem CalculusLanguageDef.lookupJudgment?_eq_some_of_mem
    (definition : CalculusLanguageDef) (declaration : JudgmentDecl)
    (headsNodup : (definition.judgments.map JudgmentDecl.head).Nodup)
    (membership : declaration ∈ definition.judgments) :
    definition.lookupJudgment? declaration.head declaration.arity =
      some declaration := by
  unfold CalculusLanguageDef.lookupJudgment?
  rw [filter_judgments_by_head_eq_singleton
    definition.judgments declaration headsNodup membership]

/-! ## Boundary controls -/

namespace Canary

private def first : JudgmentDecl := ⟨"lookup:first", 1⟩
private def second : JudgmentDecl := ⟨"lookup:second", 2⟩

private def uniqueDefinition : CalculusLanguageDef :=
  { name := "inference-signature-lookup"
    types := []
    terms := []
    equations := []
    rewrites := []
    judgments := [first, second]
    rules := [] }

theorem unique_member_is_found :
    uniqueDefinition.lookupJudgment? second.head second.arity = some second := by
  apply CalculusLanguageDef.lookupJudgment?_eq_some_of_mem
  · decide
  · simp [uniqueDefinition]

private def duplicateDefinition : CalculusLanguageDef :=
  { uniqueDefinition with judgments := [first, first] }

/-- Duplicate heads are rejected by lookup rather than resolved by order. -/
theorem duplicate_head_is_not_selected :
    duplicateDefinition.lookupJudgment? first.head first.arity = none := by
  decide

end Canary

#print axioms CalculusLanguageDef.lookupJudgment?_eq_some_of_mem
#print axioms Canary.unique_member_is_found
#print axioms Canary.duplicate_head_is_not_selected

end Mettapedia.GSLT.LanguageDef
