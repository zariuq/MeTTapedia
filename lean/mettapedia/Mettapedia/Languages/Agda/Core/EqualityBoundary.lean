import Mettapedia.Languages.Agda.Core.Qualification

/-!
# The typing boundary of public Agda conversion

The internal unit comparison intentionally ignores the two terms. Public
conversion may use it only after deriving the typing of both terms. This file
proves that requirement for every derivation of the actual presented judgment.
-/

namespace Mettapedia.Languages.Agda.Core

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker

private def equalitySchema : RuleSchema :=
  { id := ⟨"public-equal"⟩
    metavariables := [("D", 0), ("G", 0), ("A", 0), ("t", 0), ("u", 0), ("l", 0)]
    conclusion := ap[(AgdaEqual ?D ?G ?A ?t ?u)]
    premises := [ap[(Signature ?D)], ap[(Context ?D ?G)], ap[(IsType ?D ?G ?A ?l)],
      ap[(Check ?D ?G ?t ?A)], ap[(Check ?D ?G ?u ?A)], ap[(Eq ?D ?G ?A ?t ?u)]] }

private def hasHead (head : String) (rule : RuleSchema) : Bool :=
  match rule.conclusion with
  | .apply h _ => h == head
  | _ => false

set_option maxRecDepth 8192 in
private theorem equality_schema_unique :
    presentation.rules.filter (hasHead "AgdaEqual") = [equalitySchema] := by decide +kernel

private theorem equality_rule {ri : RuleInstance} {premises : List Pattern}
    {D G A t u : Pattern}
    (application : RuleApplication validated ri premises (.apply "AgdaEqual" [D, G, A, t, u])) :
    ∃ (_hp : InstantiatesList equalitySchema.metavariables ri.arguments equalitySchema.premises premises),
      Instantiates equalitySchema.metavariables ri.arguments equalitySchema.conclusion
        (.apply "AgdaEqual" [D, G, A, t, u]) := by
  rcases application with ⟨rule, hlookup, _, _, hp, hc⟩
  have hmem : rule ∈ presentation.rules := List.mem_of_find?_eq_some hlookup
  have hshape := RuleSchema.conclusion_hasJudgmentShape_of_validIn
    (rule_isValidIn_of_lookup validated hlookup)
  have hh : hasHead "AgdaEqual" rule = true := by
    cases he : rule.conclusion <;>
      simp only [he, CalculusLanguageDef.hasJudgmentShape] at hshape
    all_goals try contradiction
    case apply head args =>
      rw [he] at hc
      cases hc
      simp [hasHead, he]
  have hr := List.mem_filter.mpr ⟨hmem, hh⟩
  rw [equality_schema_unique] at hr
  have heq : rule = equalitySchema := by simpa only [List.mem_singleton] using hr
  subst rule
  exact ⟨hp, hc⟩

private theorem equality_premises {ri : RuleInstance} {premises : List Pattern}
    {D G A t u : Pattern}
    (application : RuleApplication validated ri premises (.apply "AgdaEqual" [D, G, A, t, u])) :
    .apply "Check" [D, G, t, A] ∈ premises ∧
      .apply "Check" [D, G, u, A] ∈ premises := by
  obtain ⟨hp, hc⟩ := equality_rule application
  change InstantiatesAt _ _ 0 (.apply "AgdaEqual" _) _ at hc
  cases hc with
  | apply items =>
    cases items with | cons hD rest =>
     cases rest with | cons hG rest =>
      cases rest with | cons hA rest =>
       cases rest with | cons ht rest =>
        cases rest with | cons hu rest =>
         cases rest
         change InstantiatesListAt _ _ 0 [_ , _, _, _, _, _] premises at hp
         cases hp with | cons _ rest =>
          cases rest with | cons _ rest =>
           cases rest with | cons _ rest =>
            cases rest with | cons hleft rest =>
             cases rest with | cons hright rest =>
              cases rest with | cons _ rest =>
               cases rest
               have hl := InstantiatesAt.functional hleft
                 (.apply (.cons hD (.cons hG (.cons ht (.cons hA (.nil 0))))))
               have hr := InstantiatesAt.functional hright
                 (.apply (.cons hD (.cons hG (.cons hu (.cons hA (.nil 0))))))
               simp_all

private theorem derivations_have_member {goals : List Pattern}
    (children : DerivationList validated goals) {p : Pattern} (hm : p ∈ goals) :
    Nonempty (Derivation validated p) := by
  cases children with
  | nil => simp at hm
  | cons head tail =>
    simp only [List.mem_cons] at hm
    rcases hm with rfl | hm
    · exact ⟨head⟩
    · exact derivations_have_member tail hm

/-- Unit eta, or any other internal conversion rule, cannot bypass the public
requirement that both terms inhabit the type being compared. -/
theorem public_equality_requires_typing {D G A t u : Pattern}
    (derivation : Derivation validated (.apply "AgdaEqual" [D, G, A, t, u])) :
    Nonempty (Derivation validated (.apply "Check" [D, G, t, A])) ∧
      Nonempty (Derivation validated (.apply "Check" [D, G, u, A])) := by
  cases derivation with
  | byRule ri application children =>
    have hp := equality_premises application
    exact ⟨derivations_have_member children hp.1, derivations_have_member children hp.2⟩

end Mettapedia.Languages.Agda.Core

#print axioms Mettapedia.Languages.Agda.Core.public_equality_requires_typing
