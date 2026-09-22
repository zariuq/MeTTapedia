import Mettapedia.OSLF.Framework.WMCalculusCombinedSortedBoundary
import Mettapedia.OSLF.Framework.WMCalculusSortedBoundary
import Mettapedia.OSLF.Framework.WMCalculusStructuralPresentation
import Mettapedia.GSLT.LanguageDef.BindingSignatureTransport
import Mettapedia.GSLT.LanguageDef.StructuralSimulation
import Mettapedia.OSLF.Syntax.EquationTransport

/-!
# Intrinsic transport from the WM core to the combined guarded vertex

The core declarations and unconditional rewrites are literally retained by
the overlap-plus-scope vertex. Their inclusion is a structural language map,
so the existing binding-signature transport carries core typed terms and
their substitution action into the guarded extension. The extra constructors
remain distinct additions, not changes to core operators.
-/

namespace Mettapedia.OSLF.Framework.WMCalculusCombinedIntrinsicTransport

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusCombinedSortedBoundary
open Mettapedia.OSLF.Framework.WMCalculusSortedBoundary
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis

set_option autoImplicit false

def coreValidated : ValidatedLanguageDef :=
  ⟨wmCoreLanguageDef, core_validation⟩

def combinedValidated : ValidatedLanguageDef :=
  ⟨wmExtVertexLanguageDefGuarded combinedVertex, combined_validation⟩

def structuralValidated : ValidatedLanguageDef :=
  ⟨WMCalculusStructuralPresentation.wmStructuralLanguageDef,
    WMCalculusStructuralPresentation.structural_validation⟩

/-- The structural-equation presentation cannot embed by a *literal*
`StructuralMorphism` into this equation-free directed vertex: its authored
Combine commutativity equation has no target equation. This does not rule out
a richer interpretation preserving equation consequences. -/
theorem no_literal_structuralCore_to_combined :
    ¬ Nonempty (StructuralMorphism structuralValidated combinedValidated) := by
  rintro ⟨mapping⟩
  have impossible := mapping.mapsEquations
    WMCalculusStructuralPresentation.combineCommEquation
    WMCalculusStructuralPresentation.combine_comm_is_equation
  change mapEquation mapping.symbols
      WMCalculusStructuralPresentation.combineCommEquation ∈ ([] : List Equation)
      at impossible
  cases impossible

/-- A core declaration or rewrite embeds into the larger authored vertex. -/
def coreToCombined : StructuralMorphism coreValidated combinedValidated where
  symbols := LanguageDefSymbolMap.id
  mapsTypes := by
    intro declaration member
    simp only [mapTypeDecl_id]
    dsimp [coreValidated] at member
    change List.Mem declaration (wmExtVertexLanguageDefGuarded combinedVertex).types
    rw [combined_types]
    have small : List.Mem declaration
        (["State", "Query", "BinaryEvidence"] : List Mettapedia.OSLF.MeTTaIL.Syntax.TypeDecl) := by
      simpa only [wmCoreLanguageDef] using member
    cases small with
    | head => exact List.Mem.head _
    | tail _ rest =>
        cases rest with
        | head => exact List.Mem.tail _ (List.Mem.head _)
        | tail _ rest =>
            cases rest with
            | head => exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
            | tail _ impossible => cases impossible
  mapsTerms := by
    intro rule member
    simp only [mapGrammarRule_id]
    change rule ∈ coreTerms at member
    change rule ∈ coreTerms ++ [overlapMergeDecl, overlapFactorDecl,
      overlapCorrectDecl] ++ [forgetDecl]
    simp [member]
  mapsEquations := by
    intro equation member
    dsimp [coreValidated] at member
    change List.Mem equation ([] : List _) at member
    exact nomatch member
  mapsRewrites := by
    intro rewrite member
    simp only [mapRewriteRule_id]
    change rewrite ∈ coreRules at member
    change rewrite ∈ coreRules ++ [ruleOverlapExtract] ++
      [ruleForgetOutsideGuarded, ruleForgetIdempotent]
    simp [member]

def coreSignatureMap :
    SigMor (signatureOf wmCoreLanguageDef)
      (signatureOf (wmExtVertexLanguageDefGuarded combinedVertex)) :=
  signatureMorphism coreToCombined

abbrev CombinedSignature :=
  signatureOf (wmExtVertexLanguageDefGuarded combinedVertex)

private abbrev State := TypeExpr.base "State"
private abbrev Query := TypeExpr.base "Query"
private abbrev Evidence := TypeExpr.base "BinaryEvidence"
private abbrev Overlap := TypeExpr.base "Overlap"
private abbrev Scope := TypeExpr.base "Scope"

/-- The core constructors enter the larger signature through the structural
map, so the extension does not re-author their declarations. -/
def coreReviseOperator : (signatureOf wmCoreLanguageDef).Op State :=
  .constructor reviseDecl (by simp [wmCoreLanguageDef, coreTerms])
    (by simp [UsesBareCollection, reviseDecl])
    (.cons (.simple "first" State) (.cons (.simple "second" State) .nil))

def coreExtractOperator : (signatureOf wmCoreLanguageDef).Op Evidence :=
  .constructor extractDecl (by simp [wmCoreLanguageDef, coreTerms])
    (by simp [UsesBareCollection, extractDecl])
    (.cons (.simple "world" State) (.cons (.simple "query" Query) .nil))

def combinedReviseOperator : CombinedSignature.Op State :=
  mapOperator coreToCombined coreReviseOperator

def combinedExtractOperator : CombinedSignature.Op Evidence :=
  mapOperator coreToCombined coreExtractOperator

def combinedCombineOperator : CombinedSignature.Op Evidence :=
  .constructor combineDecl (by rw [combined_terms]; simp [coreTerms])
    (by simp [UsesBareCollection, combineDecl])
    (.cons (.simple "first" Evidence) (.cons (.simple "second" Evidence) .nil))

def combinedZeroOperator : CombinedSignature.Op Evidence :=
  .constructor evidenceZeroDecl (by rw [combined_terms]; simp [coreTerms])
    (by simp [UsesBareCollection, evidenceZeroDecl]) .nil

def coreRevise {Γ : Ctx (signatureOf wmCoreLanguageDef)}
    (first second : Term (signatureOf wmCoreLanguageDef) Γ State) :
    Term (signatureOf wmCoreLanguageDef) Γ State :=
  .op coreReviseOperator (.cons first (.cons second .nil))

def coreExtract {Γ : Ctx (signatureOf wmCoreLanguageDef)}
    (world : Term (signatureOf wmCoreLanguageDef) Γ State)
    (query : Term (signatureOf wmCoreLanguageDef) Γ Query) :
    Term (signatureOf wmCoreLanguageDef) Γ Evidence :=
  .op coreExtractOperator (.cons world (.cons query .nil))

def revise {Γ : Ctx CombinedSignature}
    (first second : Term CombinedSignature Γ State) :
    Term CombinedSignature Γ State :=
  .op combinedReviseOperator (.cons first (.cons second .nil))

def extract {Γ : Ctx CombinedSignature}
    (world : Term CombinedSignature Γ State)
    (query : Term CombinedSignature Γ Query) :
    Term CombinedSignature Γ Evidence :=
  .op combinedExtractOperator (.cons world (.cons query .nil))

def combine {Γ : Ctx CombinedSignature}
    (first second : Term CombinedSignature Γ Evidence) :
    Term CombinedSignature Γ Evidence :=
  .op combinedCombineOperator (.cons first (.cons second .nil))

def zero {Γ : Ctx CombinedSignature} : Term CombinedSignature Γ Evidence :=
  .op combinedZeroOperator .nil

theorem erase_revise {Γ : Ctx CombinedSignature}
    (first second : Term CombinedSignature Γ State) :
    erase (revise first second) = pRevise (erase first) (erase second) := rfl

theorem erase_extract {Γ : Ctx CombinedSignature}
    (world : Term CombinedSignature Γ State)
    (query : Term CombinedSignature Γ Query) :
    erase (extract world query) = pExtract (erase world) (erase query) := rfl

theorem erase_combine {Γ : Ctx CombinedSignature}
    (first second : Term CombinedSignature Γ Evidence) :
    erase (combine first second) = pCombine (erase first) (erase second) := rfl

theorem erase_zero {Γ : Ctx CombinedSignature} :
    erase (zero (Γ := Γ)) = pEvidenceZero := rfl

/-- The inclusion preserves the core `Revise` operation on intrinsic terms,
not just its erasure or its result sort. -/
theorem map_coreRevise {Γ : Ctx (signatureOf wmCoreLanguageDef)}
    (first second : Term (signatureOf wmCoreLanguageDef) Γ State) :
    coreSignatureMap.onTerm (coreRevise first second) =
      revise (coreSignatureMap.onTerm first) (coreSignatureMap.onTerm second) := rfl

/-- Observation itself is carried by the same binding-signature map. -/
theorem map_coreExtract {Γ : Ctx (signatureOf wmCoreLanguageDef)}
    (world : Term (signatureOf wmCoreLanguageDef) Γ State)
    (query : Term (signatureOf wmCoreLanguageDef) Γ Query) :
    coreSignatureMap.onTerm (coreExtract world query) =
      extract (coreSignatureMap.onTerm world) (coreSignatureMap.onTerm query) := rfl

/-- The core inclusion commutes with arbitrary sorted simultaneous
substitution through the generic signature-morphism law. -/
theorem coreMap_substitution
    {Γ Δ : Ctx (signatureOf wmCoreLanguageDef)}
    (sigma : Sub (signatureOf wmCoreLanguageDef) Γ Δ)
    {sort : TypeExpr}
    (term : Term (signatureOf wmCoreLanguageDef) Γ sort) :
    coreSignatureMap.onTerm (bind sigma term) =
      bind (coreSignatureMap.mapSub (mapVar coreSignatureMap.sortMap) sigma)
        (coreSignatureMap.onTerm term) :=
  coreSignatureMap.map_bind (mapVar coreSignatureMap.sortMap) sigma term

theorem bind_revise {Γ Δ : Ctx CombinedSignature}
    (sigma : Sub CombinedSignature Γ Δ)
    (first second : Term CombinedSignature Γ State) :
    bind sigma (revise first second) =
      revise (bind sigma first) (bind sigma second) := rfl

theorem bind_extract {Γ Δ : Ctx CombinedSignature}
    (sigma : Sub CombinedSignature Γ Δ)
    (world : Term CombinedSignature Γ State)
    (query : Term CombinedSignature Γ Query) :
    bind sigma (extract world query) =
      extract (bind sigma world) (bind sigma query) := rfl

theorem bind_combine {Γ Δ : Ctx CombinedSignature}
    (sigma : Sub CombinedSignature Γ Δ)
    (first second : Term CombinedSignature Γ Evidence) :
    bind sigma (combine first second) =
      combine (bind sigma first) (bind sigma second) := rfl

theorem bind_zero {Γ Δ : Ctx CombinedSignature}
    (sigma : Sub CombinedSignature Γ Δ) :
    bind sigma (zero (Γ := Γ)) = zero (Γ := Δ) := rfl

/-- The additional state merger is derived from the combined vertex's own
authored constructor declaration. -/
def overlapMergeOperator : CombinedSignature.Op State :=
  .constructor overlapMergeDecl (by rw [combined_terms]; simp)
    (by simp [UsesBareCollection, overlapMergeDecl])
    (.cons (.simple "first" State) (.cons (.simple "second" State) .nil))

def overlapFactorOperator : CombinedSignature.Op Overlap :=
  .constructor overlapFactorDecl (by rw [combined_terms]; simp)
    (by simp [UsesBareCollection, overlapFactorDecl])
    (.cons (.simple "first" State)
      (.cons (.simple "second" State) (.cons (.simple "query" Query) .nil)))

def overlapCorrectOperator : CombinedSignature.Op Evidence :=
  .constructor overlapCorrectDecl (by rw [combined_terms]; simp)
    (by simp [UsesBareCollection, overlapCorrectDecl])
    (.cons (.simple "first" Evidence)
      (.cons (.simple "second" Evidence) (.cons (.simple "factor" Overlap) .nil)))

def forgetOperator : CombinedSignature.Op State :=
  .constructor forgetDecl (by rw [combined_terms]; simp)
    (by simp [UsesBareCollection, forgetDecl])
    (.cons (.simple "scope" Scope) (.cons (.simple "world" State) .nil))

/-- The four added operator arities come from the authored parameter rows. -/
theorem extension_operator_arities :
    CombinedSignature.arity overlapMergeOperator = [([], State), ([], State)] ∧
    CombinedSignature.arity overlapFactorOperator =
      [([], State), ([], State), ([], Query)] ∧
    CombinedSignature.arity overlapCorrectOperator =
      [([], Evidence), ([], Evidence), ([], Overlap)] ∧
    CombinedSignature.arity forgetOperator = [([], Scope), ([], State)] :=
  ⟨rfl, rfl, rfl, rfl⟩

def overlapMerge {Γ : Ctx CombinedSignature}
    (first second : Term CombinedSignature Γ State) :
    Term CombinedSignature Γ State :=
  .op overlapMergeOperator (.cons first (.cons second .nil))

def overlapFactor {Γ : Ctx CombinedSignature}
    (first second : Term CombinedSignature Γ State)
    (query : Term CombinedSignature Γ Query) :
    Term CombinedSignature Γ Overlap :=
  .op overlapFactorOperator (.cons first (.cons second (.cons query .nil)))

def overlapCorrect {Γ : Ctx CombinedSignature}
    (first second : Term CombinedSignature Γ Evidence)
    (factor : Term CombinedSignature Γ Overlap) :
    Term CombinedSignature Γ Evidence :=
  .op overlapCorrectOperator (.cons first (.cons second (.cons factor .nil)))

def forget {Γ : Ctx CombinedSignature}
    (scope : Term CombinedSignature Γ Scope)
    (world : Term CombinedSignature Γ State) :
    Term CombinedSignature Γ State :=
  .op forgetOperator (.cons scope (.cons world .nil))

theorem erase_overlapMerge {Γ : Ctx CombinedSignature}
    (first second : Term CombinedSignature Γ State) :
    erase (overlapMerge first second) = pOverlapMerge (erase first) (erase second) := rfl

theorem erase_overlapFactor {Γ : Ctx CombinedSignature}
    (first second : Term CombinedSignature Γ State)
    (query : Term CombinedSignature Γ Query) :
    erase (overlapFactor first second query) =
      pOverlapFactor (erase first) (erase second) (erase query) := rfl

theorem erase_overlapCorrect {Γ : Ctx CombinedSignature}
    (first second : Term CombinedSignature Γ Evidence)
    (factor : Term CombinedSignature Γ Overlap) :
    erase (overlapCorrect first second factor) =
      pOverlapCorrect (erase first) (erase second) (erase factor) := rfl

theorem erase_forget {Γ : Ctx CombinedSignature}
    (scope : Term CombinedSignature Γ Scope)
    (world : Term CombinedSignature Γ State) :
    erase (forget scope world) = pForget (erase scope) (erase world) := rfl

theorem bind_overlapMerge {Γ Δ : Ctx CombinedSignature}
    (sigma : Sub CombinedSignature Γ Δ)
    (first second : Term CombinedSignature Γ State) :
    bind sigma (overlapMerge first second) =
      overlapMerge (bind sigma first) (bind sigma second) := rfl

theorem bind_overlapFactor {Γ Δ : Ctx CombinedSignature}
    (sigma : Sub CombinedSignature Γ Δ)
    (first second : Term CombinedSignature Γ State)
    (query : Term CombinedSignature Γ Query) :
    bind sigma (overlapFactor first second query) =
      overlapFactor (bind sigma first) (bind sigma second) (bind sigma query) := rfl

theorem bind_overlapCorrect {Γ Δ : Ctx CombinedSignature}
    (sigma : Sub CombinedSignature Γ Δ)
    (first second : Term CombinedSignature Γ Evidence)
    (factor : Term CombinedSignature Γ Overlap) :
    bind sigma (overlapCorrect first second factor) =
      overlapCorrect (bind sigma first) (bind sigma second) (bind sigma factor) := rfl

theorem bind_forget {Γ Δ : Ctx CombinedSignature}
    (sigma : Sub CombinedSignature Γ Δ)
    (scope : Term CombinedSignature Γ Scope)
    (world : Term CombinedSignature Γ State) :
    bind sigma (forget scope world) =
      forget (bind sigma scope) (bind sigma world) := rfl

/-- The combined vertex computes overlap extraction by its own authored
unconditional rule; the scope-dependent forgetting rule is not used here. -/
theorem overlapExtract_raw (first second query : Pattern) :
    langSemanticReduces
      (wmExtVertexLanguageDefGuarded combinedVertex)
      (pExtract (pOverlapMerge first second) query)
      (pOverlapCorrect (pExtract first query) (pExtract second query)
        (pOverlapFactor first second query)) := by
  apply langReduces_to_semantic
  unfold langReduces langReducesUsing
  let bs : Bindings := [("q", query), ("W2", second), ("W1", first)]
  apply step_of_rule (rule := ruleOverlapExtract)
    (initialBindings := bs) (finalBindings := bs)
  · simp [wmExtVertexLanguageDefGuarded, combinedVertex, overlapRules]
  · simp [bs, ruleOverlapExtract, pExtract, pOverlapMerge,
      matchPattern, matchArgs, mergeBindings]
  · exact .nil
  · simp [bs, ruleOverlapExtract, applyPremisesWithEnv]
  · simp [Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings,
      bs, ruleOverlapExtract, pExtract, pOverlapCorrect,
      pOverlapFactor, applyBindings]

/-- Intrinsic overlap observations compute after erasure at every context;
the correction factor has its distinct `Overlap` sort throughout. -/
theorem intrinsic_overlapExtract_computes {Γ : Ctx CombinedSignature}
    (first second : Term CombinedSignature Γ State)
    (query : Term CombinedSignature Γ Query) :
    langSemanticReduces
      (wmExtVertexLanguageDefGuarded combinedVertex)
      (erase (extract (overlapMerge first second) query))
      (erase (overlapCorrect (extract first query) (extract second query)
        (overlapFactor first second query))) := by
  simpa [erase_extract, erase_overlapMerge, erase_overlapCorrect,
    erase_overlapFactor] using
    overlapExtract_raw (erase first) (erase second) (erase query)

/-- One simultaneous substitution preserves the actual overlap computation
because all five intrinsic operators share the declaration-derived action. -/
theorem intrinsic_overlapExtract_substitution_stable {Γ Δ : Ctx CombinedSignature}
    (sigma : Sub CombinedSignature Γ Δ)
    (first second : Term CombinedSignature Γ State)
    (query : Term CombinedSignature Γ Query) :
    langSemanticReduces
      (wmExtVertexLanguageDefGuarded combinedVertex)
      (erase (bind sigma (extract (overlapMerge first second) query)))
      (erase (bind sigma (overlapCorrect (extract first query) (extract second query)
        (overlapFactor first second query)))) := by
  have step := intrinsic_overlapExtract_computes
    (bind sigma first) (bind sigma second) (bind sigma query)
  simpa only [bind_extract, bind_overlapMerge, bind_overlapCorrect,
    bind_overlapFactor] using step

/-- Repeating the same forgetting scope contracts by the authored
idempotence rule, independently of an outside-scope oracle. -/
theorem forgetIdempotent_raw (scope world : Pattern) :
    langSemanticReduces
      (wmExtVertexLanguageDefGuarded combinedVertex)
      (pForget scope (pForget scope world))
      (pForget scope world) := by
  apply langReduces_to_semantic
  unfold langReduces langReducesUsing
  let bs : Bindings := [("W", world), ("S", scope)]
  apply step_of_rule (rule := ruleForgetIdempotent)
    (initialBindings := bs) (finalBindings := bs)
  · simp [wmExtVertexLanguageDefGuarded, combinedVertex,
      forgettingRulesGuarded]
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
    simp [bs, ruleForgetIdempotent, pForget, matchPattern,
      matchArgs, mergeBindings]
  · exact .nil
  · simp [bs, ruleForgetIdempotent, applyPremisesWithEnv]
  · simp [Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings,
      bs, ruleForgetIdempotent, pForget, applyBindings]

/-- Intrinsically typed forgetting idempotence remains a computation after
any simultaneous substitution, unlike the guarded outside-scope rule. -/
theorem intrinsic_forgetIdempotent_substitution_stable
    {Γ Δ : Ctx CombinedSignature}
    (sigma : Sub CombinedSignature Γ Δ)
    (scope : Term CombinedSignature Γ Scope)
    (world : Term CombinedSignature Γ State) :
    langSemanticReduces
      (wmExtVertexLanguageDefGuarded combinedVertex)
      (erase (bind sigma (forget scope (forget scope world))))
      (erase (bind sigma (forget scope world))) := by
  have step := forgetIdempotent_raw (erase (bind sigma scope))
    (erase (bind sigma world))
  simpa only [bind_forget, erase_forget] using step

/-- The authored outside-scope rule requires a relation-query answer. The
empty provider supplies none, even though `Forget` is a typed constructor. -/
theorem forgetOutside_empty_premise (scope world query : Pattern) :
    applyPremisesWithEnv RelationEnv.empty
      (wmExtVertexLanguageDefGuarded combinedVertex)
      ruleForgetOutsideGuarded.premises
      [("q", query), ("W", world), ("S", scope)] = [] := by
  simp [applyPremisesWithEnv, ruleForgetOutsideGuarded, premiseStepWithEnv,
    relationQueryStep, builtinRelationTuples, RelationEnv.empty,
    applyBindings, mergeBindings]

/-- A successful explicit guard permits exactly the authored outside-scope
step. This says nothing about a provider's domain-level soundness. -/
theorem forgetOutside_raw_of_guard (relEnv : RelationEnv)
    (scope world query : Pattern)
    (guard : [("q", query), ("W", world), ("S", scope)] ∈
      applyPremisesWithEnv relEnv
        (wmExtVertexLanguageDefGuarded combinedVertex)
        ruleForgetOutsideGuarded.premises
        [("q", query), ("W", world), ("S", scope)]) :
    langSemanticReducesUsing relEnv
      (wmExtVertexLanguageDefGuarded combinedVertex)
      (pExtract (pForget scope world) query)
      (pExtract world query) := by
  apply langReducesUsing_to_semantic
  unfold langReducesUsing
  apply step_of_rule
    (rule := ruleForgetOutsideGuarded)
    (initialBindings := [("q", query), ("W", world), ("S", scope)])
    (finalBindings := [("q", query), ("W", world), ("S", scope)])
  · simp [wmExtVertexLanguageDefGuarded, combinedVertex,
      forgettingRulesGuarded]
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule_eq_syntactic]
    simp [ruleForgetOutsideGuarded, pExtract, pForget,
      matchPattern, matchArgs, mergeBindings]
  · exact .relationQuery .nil
  · exact guard
  · rw [Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_applyBindings
      _ _ _ (by decide +kernel)]
    simp [ruleForgetOutsideGuarded, pExtract, applyBindings]

/-- The guarded observation is available for typed combined terms exactly
when the supplied relation environment accepts their erased scope and query. -/
theorem intrinsic_forgetOutside_of_guard {Γ : Ctx CombinedSignature}
    (relEnv : RelationEnv)
    (scope : Term CombinedSignature Γ Scope)
    (world : Term CombinedSignature Γ State)
    (query : Term CombinedSignature Γ Query)
    (guard : [("q", erase query), ("W", erase world), ("S", erase scope)] ∈
      applyPremisesWithEnv relEnv
        (wmExtVertexLanguageDefGuarded combinedVertex)
        ruleForgetOutsideGuarded.premises
        [("q", erase query), ("W", erase world), ("S", erase scope)]) :
    langSemanticReducesUsing relEnv
      (wmExtVertexLanguageDefGuarded combinedVertex)
      (erase (extract (forget scope world) query))
      (erase (extract world query)) := by
  simpa [erase_extract, erase_forget] using
    forgetOutside_raw_of_guard relEnv (erase scope) (erase world) (erase query) guard

/-- The derived sort map is identity: the extension adds sorts but does not
rename or merge any existing sort. -/
theorem coreSignatureMap_sort (s : Mettapedia.OSLF.MeTTaIL.Syntax.TypeExpr) :
    coreSignatureMap.sortMap s = s := by
  simp [coreSignatureMap, signatureMorphism, coreToCombined]

/-- The generic binding-signature action retains the exact raw core term,
including binder wrappers, rather than making a second encoding. -/
theorem mappedCoreTerm_erasure {Γ : List Mettapedia.OSLF.MeTTaIL.Syntax.TypeExpr}
    {s : Mettapedia.OSLF.MeTTaIL.Syntax.TypeExpr}
    (term : Term (signatureOf wmCoreLanguageDef) Γ s) :
    erase (coreSignatureMap.onTerm term) = erase term := by
  have mapped := erase_onTerm coreToCombined term
  change erase (coreSignatureMap.onTerm term) =
    mapPattern LanguageDefSymbolMap.id (erase term) at mapped
  simpa only [mapPattern_id] using mapped

/-- A core typed term remains typed by the guarded overlap/scope vertex. -/
theorem mappedCoreTerm_typed {Γ : List Mettapedia.OSLF.MeTTaIL.Syntax.TypeExpr}
    {s : Mettapedia.OSLF.MeTTaIL.Syntax.TypeExpr}
    (term : Term (signatureOf wmCoreLanguageDef) Γ s) :
    Mettapedia.GSLT.LanguageDef.WellSorted.HasType
      (wmExtVertexLanguageDefGuarded combinedVertex)
      Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext.empty
      (Γ.map (mapTypeExpr LanguageDefSymbolMap.id))
      (erase (coreSignatureMap.onTerm term))
      (mapTypeExpr LanguageDefSymbolMap.id s) := by
  exact mapped_erase_typed coreToCombined term

/-- The generic structural simulation carries every core step into the
combined guarded vertex. The target is allowed to have additional steps. -/
theorem coreStep_in_combined {first second : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    (step : Mettapedia.OSLF.Framework.TypeSynthesis.langReduces
      wmCoreLanguageDef first second) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReduces
      (wmExtVertexLanguageDefGuarded combinedVertex) first second := by
  have transported :=
    Mettapedia.GSLT.LanguageDef.StructuralSimulation.langReduces_map_of_structuralMorphism
      coreToCombined (by intro x y equality; exact equality) rfl step
  change Mettapedia.OSLF.Framework.TypeSynthesis.langReduces
    (wmExtVertexLanguageDefGuarded combinedVertex)
    (mapPattern LanguageDefSymbolMap.id first)
    (mapPattern LanguageDefSymbolMap.id second) at transported
  simpa only [mapPattern_id] using transported

/-- The same forward simulation holds for the canonical equation-modulo
OSLF step relation, since the source core has no structural equations. -/
theorem coreSemanticStep_in_combined
    {first second : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    (step : langSemanticReduces wmCoreLanguageDef first second) :
    langSemanticReduces (wmExtVertexLanguageDefGuarded combinedVertex)
      first second := by
  have noEquations : wmCoreLanguageDef.isEquationFree = true := by decide +kernel
  have primitive :=
    (langSemanticReduces_iff_langReduces_of_equation_free
      noEquations first second).mp step
  exact langReduces_to_semantic _ (coreStep_in_combined primitive)

/-- Intrinsic core terms therefore retain their operational step when
embedded in the guarded extension; both endpoints keep their typing. -/
theorem mappedCoreStep_in_combined
    {Γ : List Mettapedia.OSLF.MeTTaIL.Syntax.TypeExpr}
    {s : Mettapedia.OSLF.MeTTaIL.Syntax.TypeExpr}
    {first second : Term (signatureOf wmCoreLanguageDef) Γ s}
    (step : Mettapedia.OSLF.Framework.TypeSynthesis.langReduces
      wmCoreLanguageDef (erase first) (erase second)) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langReduces
      (wmExtVertexLanguageDefGuarded combinedVertex)
      (erase (coreSignatureMap.onTerm first))
      (erase (coreSignatureMap.onTerm second)) := by
  rw [mappedCoreTerm_erasure, mappedCoreTerm_erasure]
  exact coreStep_in_combined step

#print axioms coreToCombined
#print axioms no_literal_structuralCore_to_combined
#print axioms extension_operator_arities
#print axioms map_coreRevise
#print axioms map_coreExtract
#print axioms coreMap_substitution
#print axioms overlapExtract_raw
#print axioms intrinsic_overlapExtract_substitution_stable
#print axioms forgetIdempotent_raw
#print axioms intrinsic_forgetIdempotent_substitution_stable
#print axioms forgetOutside_empty_premise
#print axioms intrinsic_forgetOutside_of_guard
#print axioms coreSignatureMap_sort
#print axioms mappedCoreTerm_erasure
#print axioms mappedCoreTerm_typed
#print axioms coreStep_in_combined
#print axioms coreSemanticStep_in_combined
#print axioms mappedCoreStep_in_combined

end Mettapedia.OSLF.Framework.WMCalculusCombinedIntrinsicTransport
