import Mettapedia.OSLF.MeTTaIL.ReferenceStep

/-!
# The canonical presentation of a language

Binder display names are metadata of a presentation: binding is carried by indices, and the semantic carrier is the
canonical section of the quotient by display names (`Pattern.eraseBinderMetadata`, `BinderAlphaSemantics`). The
canonical presentation of a language erases the display names of every pattern of its rules and equations
(`LanguageDef.eraseBinderMetadata`). Its patterns carry no display names (`rule_canonical`), and a pattern without
binders is its own erasure (`eraseBinderMetadata_of_binderFree`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Syntax

open Mettapedia.OSLF.MeTTaIL.Match (binderFree binderFreeList)

/-- A premise with the binder display names of its patterns erased. -/
def Premise.eraseBinderMetadata : Premise → Premise
  | .freshness condition => .freshness { condition with term := condition.term.eraseBinderMetadata }
  | .congruence source target => .congruence source.eraseBinderMetadata target.eraseBinderMetadata
  | .scopedStep step =>
      .scopedStep { step with source := step.source.eraseBinderMetadata, target := step.target.eraseBinderMetadata }
  | .relationQuery relation arguments => .relationQuery relation (arguments.map Pattern.eraseBinderMetadata)
  | .forAll collection parameter body => .forAll collection parameter body.eraseBinderMetadata

/-- A rule with the binder display names of its patterns erased. -/
def RewriteRule.eraseBinderMetadata (rule : RewriteRule) : RewriteRule :=
  { rule with
    premises := rule.premises.map Premise.eraseBinderMetadata
    left := rule.left.eraseBinderMetadata
    right := rule.right.eraseBinderMetadata }

/-- An equation with the binder display names of its patterns erased. -/
def Equation.eraseBinderMetadata (equation : Equation) : Equation :=
  { equation with
    premises := equation.premises.map Premise.eraseBinderMetadata
    left := equation.left.eraseBinderMetadata
    right := equation.right.eraseBinderMetadata }

/-- **The canonical presentation of a language**: every rule and equation with its binder display names erased. -/
def LanguageDef.eraseBinderMetadata (language : LanguageDef) : LanguageDef :=
  { language with
    rewrites := language.rewrites.map RewriteRule.eraseBinderMetadata
    equations := language.equations.map Equation.eraseBinderMetadata }

theorem Premise.eraseBinderMetadata_endpoints {premise : Premise} {source target : Pattern}
    (endpoints : Mettapedia.OSLF.MeTTaIL.ReferenceStep.stepEndpoints premise.eraseBinderMetadata =
      some (source, target)) :
    source.hasCanonicalBinderMetadata = true ∧ target.hasCanonicalBinderMetadata = true := by
  cases premise <;>
    simp_all [Premise.eraseBinderMetadata, Mettapedia.OSLF.MeTTaIL.ReferenceStep.stepEndpoints]
  all_goals
    obtain ⟨rfl, rfl⟩ := endpoints
    exact ⟨Pattern.eraseBinderMetadata_hasCanonicalBinderMetadata _,
      Pattern.eraseBinderMetadata_hasCanonicalBinderMetadata _⟩

/-- **The rules of the canonical presentation carry no binder display names**: neither on their sides nor on their
step premises. -/
theorem LanguageDef.rule_canonical {language : LanguageDef} {rule : RewriteRule}
    (member : rule ∈ language.eraseBinderMetadata.rewrites) :
    rule.left.hasCanonicalBinderMetadata = true ∧ rule.right.hasCanonicalBinderMetadata = true ∧
      ∀ premise ∈ rule.premises, ∀ source target,
        Mettapedia.OSLF.MeTTaIL.ReferenceStep.stepEndpoints premise = some (source, target) →
          source.hasCanonicalBinderMetadata = true ∧ target.hasCanonicalBinderMetadata = true := by
  simp only [LanguageDef.eraseBinderMetadata, List.mem_map] at member
  obtain ⟨original, -, rfl⟩ := member
  simp only [RewriteRule.eraseBinderMetadata]
  refine ⟨Pattern.eraseBinderMetadata_hasCanonicalBinderMetadata _,
    Pattern.eraseBinderMetadata_hasCanonicalBinderMetadata _, fun premise inside source target endpoints => ?_⟩
  simp only [List.mem_map] at inside
  obtain ⟨originalPremise, -, rfl⟩ := inside
  exact Premise.eraseBinderMetadata_endpoints endpoints

/-- **The equations of the canonical presentation carry no binder display names** on either side. -/
theorem LanguageDef.equation_canonical {language : LanguageDef} {equation : Equation}
    (member : equation ∈ language.eraseBinderMetadata.equations) :
    equation.left.hasCanonicalBinderMetadata = true ∧ equation.right.hasCanonicalBinderMetadata = true := by
  simp only [LanguageDef.eraseBinderMetadata, List.mem_map] at member
  obtain ⟨original, -, rfl⟩ := member
  exact ⟨Pattern.eraseBinderMetadata_hasCanonicalBinderMetadata _,
    Pattern.eraseBinderMetadata_hasCanonicalBinderMetadata _⟩

mutual
  /-- **A pattern without binders is its own erasure.** -/
  theorem Pattern.eraseBinderMetadata_of_binderFree : ∀ {pattern : Pattern}, binderFree pattern = true →
      pattern.eraseBinderMetadata = pattern
    | .fvar _, _ => by simp [Pattern.eraseBinderMetadata]
    | .bvar _, _ => by simp [Pattern.eraseBinderMetadata]
    | .apply _ arguments, free => by
        simp only [binderFree] at free
        simp only [Pattern.eraseBinderMetadata]
        rw [Pattern.eraseBinderMetadataList_of_binderFree free]
    | .collection _ elements _, free => by
        simp only [binderFree] at free
        simp only [Pattern.eraseBinderMetadata]
        rw [Pattern.eraseBinderMetadataList_of_binderFree free]
    | .lambda _ _, free => by simp [binderFree] at free
    | .multiLambda _ _ _, free => by simp [binderFree] at free
    | .subst _ _, free => by simp [binderFree] at free

  theorem Pattern.eraseBinderMetadataList_of_binderFree : ∀ {patterns : List Pattern}, binderFreeList patterns = true →
      patterns.map Pattern.eraseBinderMetadata = patterns
    | [], _ => rfl
    | pattern :: patterns, free => by
        simp only [binderFreeList, Bool.and_eq_true] at free
        simp only [List.map_cons, Pattern.eraseBinderMetadata_of_binderFree free.1,
          Pattern.eraseBinderMetadataList_of_binderFree free.2]
end

end Mettapedia.OSLF.MeTTaIL.Syntax
