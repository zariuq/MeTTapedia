import Mettapedia.Languages.MeTTa.CoreProfile
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.TypedLangDef
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.PatternBridge
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Reduction
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.ProfileTheory
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# TwoSortPiSigmaId Embedding Into MeTTa Core Profiles

Contextual quotation of the fixed two-sort calculus (`ScopedTerm`) into the
MeTTa profile interface. This is an experiment-specific interpretation, not a
selection of a trusted Prime kernel.
-/

namespace Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.CoreEmbedding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.Languages.MeTTa.CoreProfile
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Reduction
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.PatternBridge
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.ProfileTheory
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Assembly
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core

/-- Minimal embedding contract for closed TwoSortPiSigmaId terms into a MeTTa profile. -/
structure KernelEmbedding where
  profile : MeTTaCoreProfile
  kernel : TypedKernelDef
  quoteClosed : ScopedTerm 0 → Pattern
  quoteClosed_lc : ∀ t, lc_at 0 (quoteClosed t) = true

/-- Canonical embedding of TwoSortPiSigmaId into the two-sort core profile. -/
def twoSortKernelIntoTwoSortProfile : KernelEmbedding where
  profile := twoSortProfile
  kernel := mettaTwoSortPiSigmaIdTyped
  quoteClosed := quoteClosedTm
  quoteClosed_lc := by
    intro t
    -- `quoteClosedTm` is `quoteTmWith defaultBinderName 0 emptyEnv`.
    simpa [quoteClosedTm, quoteTm, emptyEnv] using
      lc_quoteTmWith defaultBinderName 0 emptyEnv t

theorem twoSortKernel_embedding_target :
    twoSortKernelIntoTwoSortProfile.profile.lang.name = "MeTTaTwoSortExperiment" := by
  rfl

/-- Canonical embedding of the checked non-unfolding declaration kernel into
the two-sort core profile.

This is the strongest declaration-aware embedding currently available without
crossing the value-bearing/delta frontier: ordered checked specs, no
declaration values, and the packaged declaration-side boundary from
`TypedLangDef`. -/
def checkedNoValuesDeclKernelIntoTwoSortProfileOfPackage
    {specs : List Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.DeclSpec}
    (hSig :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.SignatureWellFormed
        specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    (hPkg :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.DeclSpecAndNoValuesPackage
        specs hNone) :
    KernelEmbedding where
  profile := twoSortProfile
  kernel := (checkedNoValuesDeclKernelBoundaryOfPackage hSig hNone hPkg).typed
  quoteClosed := quoteClosedTm
  quoteClosed_lc := by
    intro t
    simpa [quoteClosedTm, quoteTm, emptyEnv] using
      lc_quoteTmWith defaultBinderName 0 emptyEnv t

def checkedNoValuesDeclKernelIntoTwoSortProfile
    {specs : List Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.DeclSpec}
    (hSig :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.SignatureWellFormed
        specs)
    (hNone : ∀ s ∈ specs, s.value? = none) :
    KernelEmbedding :=
  checkedNoValuesDeclKernelIntoTwoSortProfileOfPackage
    hSig hNone
    (hSig.declSpecAndNoValuesPackage_of_all_none hNone)

theorem checkedNoValuesDeclKernelIntoTwoSortProfile_kernel
    {specs : List Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.DeclSpec}
    (hSig :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.SignatureWellFormed
        specs)
    (hNone : ∀ s ∈ specs, s.value? = none) :
    (checkedNoValuesDeclKernelIntoTwoSortProfile hSig hNone).kernel =
      checkedNoValuesDeclKernelTyped hSig hNone := by
  simpa [checkedNoValuesDeclKernelIntoTwoSortProfile,
    checkedNoValuesDeclKernelIntoTwoSortProfileOfPackage] using
    (checkedNoValuesDeclKernelBoundaryOfPackage
      hSig hNone
      (hSig.declSpecAndNoValuesPackage_of_all_none hNone)).typed_eq

theorem checkedNoValuesDeclKernelIntoTwoSortProfile_target
    {specs : List Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.DeclSpec}
    (hSig :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.SignatureWellFormed
        specs)
    (hNone : ∀ s ∈ specs, s.value? = none) :
    (checkedNoValuesDeclKernelIntoTwoSortProfile hSig hNone).profile.lang.name =
      "MeTTaTwoSortExperiment" := by
  rfl

/-- Canonical embedding of the checked declaration kernel into the two-sort core
profile under an explicit declaration-aware Church-Rosser hypothesis.

This is the current honest value-bearing embedding boundary: ordered checked
specs plus the packaged Church-Rosser frontier from `TypedLangDef`, without yet
claiming a declaration-side normalization/decision layer. -/
def checkedChurchRosserDeclKernelIntoTwoSortProfileOfPackage
    {specs : List Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.DeclSpec}
    (hSig :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.SignatureWellFormed
        specs)
    (hPkg :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.DeclSpecChurchRosserPackage
        specs) :
    KernelEmbedding where
  profile := twoSortProfile
  kernel := (checkedChurchRosserDeclKernelBoundaryOfPackage hSig hPkg).typed
  quoteClosed := quoteClosedTm
  quoteClosed_lc := by
    intro t
    simpa [quoteClosedTm, quoteTm, emptyEnv] using
      lc_quoteTmWith defaultBinderName 0 emptyEnv t

def checkedChurchRosserDeclKernelIntoTwoSortProfile
    {specs : List Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.DeclSpec}
    (hSig :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.SignatureWellFormed
        specs)
    (hCR :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSemantics.DeclChurchRosser
        (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.envOfSpecs specs)) :
    KernelEmbedding :=
  checkedChurchRosserDeclKernelIntoTwoSortProfileOfPackage
    hSig
    (hSig.declSpecChurchRosserPackage_of_church_rosser hCR)

theorem checkedChurchRosserDeclKernelIntoTwoSortProfile_kernel
    {specs : List Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.DeclSpec}
    (hSig :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.SignatureWellFormed
        specs)
    (hCR :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSemantics.DeclChurchRosser
        (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.envOfSpecs specs)) :
    (checkedChurchRosserDeclKernelIntoTwoSortProfile hSig hCR).kernel =
      checkedChurchRosserDeclKernelTyped hSig hCR := by
  simpa [checkedChurchRosserDeclKernelIntoTwoSortProfile,
    checkedChurchRosserDeclKernelIntoTwoSortProfileOfPackage] using
    (checkedChurchRosserDeclKernelBoundaryOfPackage
      hSig
      (hSig.declSpecChurchRosserPackage_of_church_rosser hCR)).typed_eq

theorem checkedChurchRosserDeclKernelIntoTwoSortProfile_target
    {specs : List Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.DeclSpec}
    (hSig :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.SignatureWellFormed
        specs)
    (hCR :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSemantics.DeclChurchRosser
        (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.envOfSpecs specs)) :
    (checkedChurchRosserDeclKernelIntoTwoSortProfile hSig hCR).profile.lang.name =
      "MeTTaTwoSortExperiment" := by
  rfl

theorem checkedChurchRosserDeclKernelIntoTwoSortProfile_profile
    {specs : List Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.DeclSpec}
    (hSig :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.SignatureWellFormed
        specs)
    (hCR :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSemantics.DeclChurchRosser
        (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.envOfSpecs specs)) :
    (checkedChurchRosserDeclKernelIntoTwoSortProfile hSig hCR).profile = twoSortProfile := by
  rfl

/-- The assembled value-bearing declaration boundary exposes the same
engine-facing kernel/profile interface as the generic Church-Rosser embedding.
This is the honest interface theorem for later clients: carrying the packaged
boundary is enough to recover the kernel identity and target profile without
re-proving anything about the embedding layer. -/
theorem checkedChurchRosserDeclKernelBoundary_kernel_and_target
    {specs : List Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.DeclSpec}
    {hSig :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.SignatureWellFormed
        specs}
    {hCR :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSemantics.DeclChurchRosser
        (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.envOfSpecs specs)}
    (hBoundary :
      CheckedChurchRosserDeclKernelBoundary hSig hCR) :
    (checkedChurchRosserDeclKernelIntoTwoSortProfile hSig hCR).kernel =
        hBoundary.typed ∧
      (checkedChurchRosserDeclKernelIntoTwoSortProfile hSig hCR).profile.lang.name =
        "MeTTaTwoSortExperiment" := by
  constructor
  · rw [hBoundary.typed_eq]
    exact checkedChurchRosserDeclKernelIntoTwoSortProfile_kernel hSig hCR
  · exact checkedChurchRosserDeclKernelIntoTwoSortProfile_target hSig hCR

theorem checkedChurchRosserDeclKernelBoundary_kernel_and_profile
    {specs : List Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.DeclSpec}
    {hSig :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.SignatureWellFormed
        specs}
    {hCR :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSemantics.DeclChurchRosser
        (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.envOfSpecs specs)}
    (hBoundary :
      CheckedChurchRosserDeclKernelBoundary hSig hCR) :
    (checkedChurchRosserDeclKernelIntoTwoSortProfile hSig hCR).kernel =
        hBoundary.typed ∧
      (checkedChurchRosserDeclKernelIntoTwoSortProfile hSig hCR).profile = twoSortProfile := by
  constructor
  · rw [hBoundary.typed_eq]
    exact checkedChurchRosserDeclKernelIntoTwoSortProfile_kernel hSig hCR
  · exact checkedChurchRosserDeclKernelIntoTwoSortProfile_profile hSig hCR

private def betaPiRule : RewriteRule :=
  { name := "BetaPi",
    typeContext := [("body", .base "Tm"), ("a", .base "Tm")],
    premises := [],
    left := .apply "App" [.apply "Lam" [.lambda none (.fvar "body")], .fvar "a"],
    right := .subst (.fvar "body") (.fvar "a") }

private def betaSigmaFstRule : RewriteRule :=
  { name := "BetaSigmaFst",
    typeContext := [("a", .base "Tm"), ("b", .base "Tm")],
    premises := [],
    left := .apply "Fst" [.apply "Pair" [.fvar "a", .fvar "b"]],
    right := .fvar "a" }

private def betaSigmaSndRule : RewriteRule :=
  { name := "BetaSigmaSnd",
    typeContext := [("a", .base "Tm"), ("b", .base "Tm")],
    premises := [],
    left := .apply "Snd" [.apply "Pair" [.fvar "a", .fvar "b"]],
    right := .fvar "b" }

/-- Positive bridge example (βΠ identity): quoted kernel step is a `langReduces` step. -/
theorem langReduces_quoteClosed_betaPi_id (a : ScopedTerm 0) :
    langReduces twoSortDependent (quoteClosedTm (.app (.lam (.var 0)) a)) (quoteClosedTm a) := by
  apply exec_to_langReducesUsing (relEnv := RelationEnv.empty) (lang := twoSortDependent)
  refine ⟨1, ?_⟩
  rw [rewriteAt_one_eq_rewriteStepWithPremisesUsing]
  unfold rewriteStepWithPremisesUsing
  rw [List.mem_flatMap]
  refine ⟨betaPiRule, ?_, ?_⟩
  · simp [betaPiRule, twoSortDependent]
  · unfold applyRuleWithPremisesUsing
    rw [List.mem_flatMap]
    let qbody : Pattern :=
      closeFVar 0 (defaultBinderName 0) (.fvar (defaultBinderName 0))
    let bs : Bindings := [("a", quoteClosedTm a), ("body", qbody)]
    refine ⟨bs, ?_, ?_⟩
    · simp [bs, qbody, betaPiRule, twoSortDependent, quoteClosedTm, quoteTm, quoteTmWith,
        mkApp, mkLam, matchPattern, matchArgs, mergeBindings, envCons, emptyEnv]
    · rw [List.mem_map]
      refine ⟨bs, ?_, ?_⟩
      · simp [applyPremisesWithEnv, bs, betaPiRule]
      · rw [OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
          Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings_eq_applyBindings betaPiRule _ (by decide)]
        simp [bs, qbody, betaPiRule, applyBindings, closeFVar,
          instantiateBVar, instantiateBVarAt, liftBVars_zero]

/-- Positive bridge example (βΣ fst): quoted kernel step is a `langReduces` step. -/
theorem langReduces_quoteClosed_betaSigmaFst (a b : ScopedTerm 0) :
    langReduces twoSortDependent (quoteClosedTm (.fst (.pair a b))) (quoteClosedTm a) := by
  apply exec_to_langReducesUsing (relEnv := RelationEnv.empty) (lang := twoSortDependent)
  refine ⟨1, ?_⟩
  rw [rewriteAt_one_eq_rewriteStepWithPremisesUsing]
  unfold rewriteStepWithPremisesUsing
  rw [List.mem_flatMap]
  refine ⟨betaSigmaFstRule, ?_, ?_⟩
  · simp [betaSigmaFstRule, twoSortDependent]
  · unfold applyRuleWithPremisesUsing
    rw [List.mem_flatMap]
    let bs : Bindings := [("b", quoteClosedTm b), ("a", quoteClosedTm a)]
    refine ⟨bs, ?_, ?_⟩
    · simp [bs, betaSigmaFstRule, twoSortDependent, quoteClosedTm, quoteTm, quoteTmWith,
        mkFst, mkPair, matchPattern, matchArgs, mergeBindings]
    · rw [List.mem_map]
      refine ⟨bs, ?_, ?_⟩
      · simp [applyPremisesWithEnv, bs, betaSigmaFstRule]
      · rw [OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
          Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings_eq_applyBindings betaSigmaFstRule _ (by decide)]
        simp [bs, betaSigmaFstRule, applyBindings]

/-- Positive bridge example (βΣ snd): quoted kernel step is a `langReduces` step. -/
theorem langReduces_quoteClosed_betaSigmaSnd (a b : ScopedTerm 0) :
    langReduces twoSortDependent (quoteClosedTm (.snd (.pair a b))) (quoteClosedTm b) := by
  apply exec_to_langReducesUsing (relEnv := RelationEnv.empty) (lang := twoSortDependent)
  refine ⟨1, ?_⟩
  rw [rewriteAt_one_eq_rewriteStepWithPremisesUsing]
  unfold rewriteStepWithPremisesUsing
  rw [List.mem_flatMap]
  refine ⟨betaSigmaSndRule, ?_, ?_⟩
  · simp [betaSigmaSndRule, twoSortDependent]
  · unfold applyRuleWithPremisesUsing
    rw [List.mem_flatMap]
    let bs : Bindings := [("b", quoteClosedTm b), ("a", quoteClosedTm a)]
    refine ⟨bs, ?_, ?_⟩
    · simp [bs, betaSigmaSndRule, twoSortDependent, quoteClosedTm, quoteTm, quoteTmWith,
        mkSnd, mkPair, matchPattern, matchArgs, mergeBindings]
    · rw [List.mem_map]
      refine ⟨bs, ?_, ?_⟩
      · simp [applyPremisesWithEnv, bs, betaSigmaSndRule]
      · rw [OSLF.MeTTaIL.ReflectiveSubstitution.applyBindingsForRule_eq_syntactic,
          Mettapedia.OSLF.MeTTaIL.Match.applyRuleBindings_eq_applyBindings betaSigmaSndRule _ (by decide)]
        simp [bs, betaSigmaSndRule, applyBindings]

/-- **A-layer (operational)**: the closed computational fragment executed as one
`langReduces` step by current `twoSortDependent` profile semantics. -/
inductive TwoSortOpStep : ScopedTerm 0 → ScopedTerm 0 → Prop where
  | betaPiId (a : ScopedTerm 0) :
      TwoSortOpStep (.app (.lam (.var 0)) a) a
  | betaSigmaFst (a b : ScopedTerm 0) :
      TwoSortOpStep (.fst (.pair a b)) a
  | betaSigmaSnd (a b : ScopedTerm 0) :
      TwoSortOpStep (.snd (.pair a b)) b

/-- **B-layer (theory)**: congruence-theoretic kernel step relation. -/
abbrev TwoSortTheoryStep : ScopedTerm 0 → ScopedTerm 0 → Prop := Red

/-- A-layer steps are B-layer steps. -/
theorem twoSortOpStep_to_twoSortTheoryStep {t u : ScopedTerm 0}
    (h : TwoSortOpStep t u) : TwoSortTheoryStep t u :=
  match h with
  | .betaPiId a => by
      simpa [TwoSortTheoryStep] using (Red.betaPi (.var 0) a)
  | .betaSigmaFst a b => by
      simpa [TwoSortTheoryStep] using (Red.betaSigmaFst a b)
  | .betaSigmaSnd a b => by
      simpa [TwoSortTheoryStep] using (Red.betaSigmaSnd a b)

/-- A-layer one-step soundness into declarative `langReduces`. -/
theorem twoSortOpStep_sound_langReduces_quoteClosed {t u : ScopedTerm 0}
    (h : TwoSortOpStep t u) :
    langReduces twoSortDependent (quoteClosedTm t) (quoteClosedTm u) :=
  match h with
  | .betaPiId a => by
      simpa using langReduces_quoteClosed_betaPi_id a
  | .betaSigmaFst a b => langReduces_quoteClosed_betaSigmaFst a b
  | .betaSigmaSnd a b => langReduces_quoteClosed_betaSigmaSnd a b

/-- Reflexive-transitive closure of the operational A-layer. -/
abbrev TwoSortOpStepStar (t u : ScopedTerm 0) : Prop := Relation.ReflTransGen TwoSortOpStep t u

/-- Reflexive-transitive closure of the theory B-layer. -/
abbrev TwoSortTheoryStepStar (t u : ScopedTerm 0) : Prop := RedStar t u

/-- A-layer stars embed into B-layer stars. -/
theorem twoSortOpStepStar_to_twoSortTheoryStepStar {t u : ScopedTerm 0}
    (h : TwoSortOpStepStar t u) : TwoSortTheoryStepStar t u := by
  induction h with
  | refl =>
      simpa [TwoSortTheoryStepStar] using RedStar.refl t
  | tail hxy hyz ih =>
      exact RedStar.tail ih (twoSortOpStep_to_twoSortTheoryStep hyz)

/-- A-layer multi-step soundness into profile-level multi-step reduction. -/
theorem twoSortOpStepStar_sound_langReduces_quoteClosed {t u : ScopedTerm 0}
    (h : TwoSortOpStepStar t u) :
    TwoSortProfileStepStar (quoteClosedTm t) (quoteClosedTm u) := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
      exact Relation.ReflTransGen.tail ih
        (twoSortOpStep_sound_langReduces_quoteClosed hyz)

/-- A-layer one-step soundness into the sealed C1 base. -/
theorem twoSortOpStep_sound_twoSortProfileBaseStep_quoteClosed {t u : ScopedTerm 0}
    (h : TwoSortOpStep t u) :
    TwoSortProfileBaseStep (quoteClosedTm t) (quoteClosedTm u) := by
  match h with
  | .betaPiId a =>
      let qbody : Pattern := closeFVar 0 (defaultBinderName 0) (.fvar (defaultBinderName 0))
      have hbase :
          TwoSortProfileBaseStep (quoteClosedTm (.app (.lam (.var 0)) a))
            (instantiateBVar (quoteClosedTm a) qbody) := by
        simpa [qbody, quoteClosedTm, quoteTm, quoteTmWith, emptyEnv, envCons, mkApp, mkLam] using
          (TwoSortProfileBaseStep.betaPi qbody (quoteClosedTm a))
      have hinstantiate : instantiateBVar (quoteClosedTm a) qbody = quoteClosedTm a := by
        simp [qbody, closeFVar, instantiateBVar, instantiateBVarAt, liftBVars_zero]
      exact hinstantiate ▸ hbase
  | .betaSigmaFst a b =>
      simpa [quoteClosedTm, quoteTm, quoteTmWith, mkFst, mkPair] using
        (TwoSortProfileBaseStep.betaSigmaFst (quoteClosedTm a) (quoteClosedTm b))
  | .betaSigmaSnd a b =>
      simpa [quoteClosedTm, quoteTm, quoteTmWith, mkSnd, mkPair] using
        (TwoSortProfileBaseStep.betaSigmaSnd (quoteClosedTm a) (quoteClosedTm b))

/-- A-layer one-step soundness into C1. -/
theorem twoSortOpStep_sound_twoSortProfileTheoryStep_quoteClosed {t u : ScopedTerm 0}
    (h : TwoSortOpStep t u) :
    TwoSortProfileTheoryStep (quoteClosedTm t) (quoteClosedTm u) := by
  exact .base (twoSortOpStep_sound_twoSortProfileBaseStep_quoteClosed h)

/-- A-layer multi-step soundness into C1 star closure. -/
theorem twoSortOpStepStar_sound_twoSortProfileTheoryStep_quoteClosed {t u : ScopedTerm 0}
    (h : TwoSortOpStepStar t u) :
    TwoSortProfileTheoryStepStar (quoteClosedTm t) (quoteClosedTm u) := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
      exact Relation.ReflTransGen.tail ih
        (twoSortOpStep_sound_twoSortProfileTheoryStep_quoteClosed hyz)

/-- **B -> C1 (parametric)**:
If kernel `inst0` commutes with quotation/opening for a naming policy `ν`,
then every kernel one-step reduction is sound into C1 at that quotation. -/
theorem twoSortTheoryStep_sound_twoSortProfileTheoryStep_quoteTmWith_assuming_inst0
    (ν : Nat → String)
    (hinst0 : Inst0OpenBridgeCompat ν)
    {n : Nat} (k : Nat) (ρ : QuoteEnv n) {t u : ScopedTerm n}
    (hcompat : QuoteCompat ν k ρ)
    (h : Red t u) :
    TwoSortProfileTheoryStep (quoteTmWith ν k ρ t) (quoteTmWith ν k ρ u) := by
  induction h generalizing k with
  | @betaPi n body a =>
      have hbase :
          TwoSortProfileTheoryStep
            (quoteTmWith ν k ρ (.app (.lam body) a))
            (instantiateBVar (quoteTmWith ν k ρ a)
              (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) body))) := by
        exact .base (TwoSortProfileBaseStep.betaPi
          (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) body))
          (quoteTmWith ν k ρ a))
      have hq := hinst0 k ρ a body hcompat
      have hinstantiate := quoteTmWith_instantiate_close_eq_open ν k ρ a body
      rw [hinstantiate, ← hq] at hbase
      simpa [quoteTmWith, mkApp, mkLam] using hbase
  | @betaSigmaFst n a b =>
      simpa [quoteTmWith, mkFst, mkPair] using
        (TwoSortProfileTheoryStep.base
          (TwoSortProfileBaseStep.betaSigmaFst (quoteTmWith ν k ρ a) (quoteTmWith ν k ρ b)))
  | @betaSigmaSnd n a b =>
      simpa [quoteTmWith, mkSnd, mkPair] using
        (TwoSortProfileTheoryStep.base
          (TwoSortProfileBaseStep.betaSigmaSnd (quoteTmWith ν k ρ a) (quoteTmWith ν k ρ b)))
  | @congPiDom n A A' B hAA' ih =>
      have hstep := ih (k := k) (ρ := ρ) hcompat
      have hctx :
          TwoSortProfileTheoryStep
            (mkPi (quoteTmWith ν k ρ A)
              (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) B)))
            (mkPi (quoteTmWith ν k ρ A')
              (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) B))) := by
        exact .ctx (K := .piDom .hole
          (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) B))) hstep
      simpa [quoteTmWith, mkPi] using hctx
  | @congPiCod n A B B' hBB' ih =>
      have hstep := ih (k := k + 1) (ρ := envCons (ν k) ρ)
        (QuoteCompat.envCons hcompat.1 hcompat)
      have hclose :
          TwoSortProfileTheoryStep
            (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) B))
            (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) B')) := by
        exact .ctx (K := .close (ν k) .hole) hstep
      have hctx :
          TwoSortProfileTheoryStep
            (mkPi (quoteTmWith ν k ρ A)
              (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) B)))
            (mkPi (quoteTmWith ν k ρ A)
              (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) B'))) := by
        exact .ctx (K := .piCod (quoteTmWith ν k ρ A) .hole) hclose
      simpa [quoteTmWith, mkPi] using hctx
  | @congSigmaDom n A A' B hAA' ih =>
      have hstep := ih (k := k) (ρ := ρ) hcompat
      have hctx :
          TwoSortProfileTheoryStep
            (mkSigma (quoteTmWith ν k ρ A)
              (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) B)))
            (mkSigma (quoteTmWith ν k ρ A')
              (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) B))) := by
        exact .ctx (K := .sigmaDom .hole
          (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) B))) hstep
      simpa [quoteTmWith, mkSigma] using hctx
  | @congSigmaCod n A B B' hBB' ih =>
      have hstep := ih (k := k + 1) (ρ := envCons (ν k) ρ)
        (QuoteCompat.envCons hcompat.1 hcompat)
      have hclose :
          TwoSortProfileTheoryStep
            (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) B))
            (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) B')) := by
        exact .ctx (K := .close (ν k) .hole) hstep
      have hctx :
          TwoSortProfileTheoryStep
            (mkSigma (quoteTmWith ν k ρ A)
              (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) B)))
            (mkSigma (quoteTmWith ν k ρ A)
              (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) B'))) := by
        exact .ctx (K := .sigmaCod (quoteTmWith ν k ρ A) .hole) hclose
      simpa [quoteTmWith, mkSigma] using hctx
  | @congIdTy n A A' a b hAA' ih =>
      have hstep := ih (k := k) (ρ := ρ) hcompat
      have hctx : TwoSortProfileTheoryStep
          (mkId (quoteTmWith ν k ρ A) (quoteTmWith ν k ρ a) (quoteTmWith ν k ρ b))
          (mkId (quoteTmWith ν k ρ A') (quoteTmWith ν k ρ a) (quoteTmWith ν k ρ b)) := by
        exact .ctx (K := .idTy .hole (quoteTmWith ν k ρ a) (quoteTmWith ν k ρ b)) hstep
      simpa [quoteTmWith, mkId] using hctx
  | @congIdLeft n A a a' b haa' ih =>
      have hstep := ih (k := k) (ρ := ρ) hcompat
      have hctx : TwoSortProfileTheoryStep
          (mkId (quoteTmWith ν k ρ A) (quoteTmWith ν k ρ a) (quoteTmWith ν k ρ b))
          (mkId (quoteTmWith ν k ρ A) (quoteTmWith ν k ρ a') (quoteTmWith ν k ρ b)) := by
        exact .ctx (K := .idLeft (quoteTmWith ν k ρ A) .hole (quoteTmWith ν k ρ b)) hstep
      simpa [quoteTmWith, mkId] using hctx
  | @congIdRight n A a b b' hbb' ih =>
      have hstep := ih (k := k) (ρ := ρ) hcompat
      have hctx : TwoSortProfileTheoryStep
          (mkId (quoteTmWith ν k ρ A) (quoteTmWith ν k ρ a) (quoteTmWith ν k ρ b))
          (mkId (quoteTmWith ν k ρ A) (quoteTmWith ν k ρ a) (quoteTmWith ν k ρ b')) := by
        exact .ctx (K := .idRight (quoteTmWith ν k ρ A) (quoteTmWith ν k ρ a) .hole) hstep
      simpa [quoteTmWith, mkId] using hctx
  | @congLam n b b' hbb' ih =>
      have hstep := ih (k := k + 1) (ρ := envCons (ν k) ρ)
        (QuoteCompat.envCons hcompat.1 hcompat)
      have hclose :
          TwoSortProfileTheoryStep
            (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) b))
            (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) b')) := by
        exact .ctx (K := .close (ν k) .hole) hstep
      have hctx :
          TwoSortProfileTheoryStep
            (mkLam (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) b)))
            (mkLam (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) b'))) := by
        exact .ctx (K := .lam .hole) hclose
      simpa [quoteTmWith, mkLam] using hctx
  | @congAppFun n f f' a hff' ih =>
      have hstep := ih (k := k) (ρ := ρ) hcompat
      have hctx : TwoSortProfileTheoryStep
          (mkApp (quoteTmWith ν k ρ f) (quoteTmWith ν k ρ a))
          (mkApp (quoteTmWith ν k ρ f') (quoteTmWith ν k ρ a)) := by
        exact .ctx (K := .appFun .hole (quoteTmWith ν k ρ a)) hstep
      simpa [quoteTmWith, mkApp] using hctx
  | @congAppArg n f a a' haa' ih =>
      have hstep := ih (k := k) (ρ := ρ) hcompat
      have hctx : TwoSortProfileTheoryStep
          (mkApp (quoteTmWith ν k ρ f) (quoteTmWith ν k ρ a))
          (mkApp (quoteTmWith ν k ρ f) (quoteTmWith ν k ρ a')) := by
        exact .ctx (K := .appArg (quoteTmWith ν k ρ f) .hole) hstep
      simpa [quoteTmWith, mkApp] using hctx
  | @congPairFst n a a' b haa' ih =>
      have hstep := ih (k := k) (ρ := ρ) hcompat
      have hctx : TwoSortProfileTheoryStep
          (mkPair (quoteTmWith ν k ρ a) (quoteTmWith ν k ρ b))
          (mkPair (quoteTmWith ν k ρ a') (quoteTmWith ν k ρ b)) := by
        exact .ctx (K := .pairFst .hole (quoteTmWith ν k ρ b)) hstep
      simpa [quoteTmWith, mkPair] using hctx
  | @congPairSnd n a b b' hbb' ih =>
      have hstep := ih (k := k) (ρ := ρ) hcompat
      have hctx : TwoSortProfileTheoryStep
          (mkPair (quoteTmWith ν k ρ a) (quoteTmWith ν k ρ b))
          (mkPair (quoteTmWith ν k ρ a) (quoteTmWith ν k ρ b')) := by
        exact .ctx (K := .pairSnd (quoteTmWith ν k ρ a) .hole) hstep
      simpa [quoteTmWith, mkPair] using hctx
  | @congFst n p p' hpp' ih =>
      have hstep := ih (k := k) (ρ := ρ) hcompat
      have hctx : TwoSortProfileTheoryStep
          (mkFst (quoteTmWith ν k ρ p))
          (mkFst (quoteTmWith ν k ρ p')) := by
        exact .ctx (K := .fst .hole) hstep
      simpa [quoteTmWith, mkFst] using hctx
  | @congSnd n p p' hpp' ih =>
      have hstep := ih (k := k) (ρ := ρ) hcompat
      have hctx : TwoSortProfileTheoryStep
          (mkSnd (quoteTmWith ν k ρ p))
          (mkSnd (quoteTmWith ν k ρ p')) := by
        exact .ctx (K := .snd .hole) hstep
      simpa [quoteTmWith, mkSnd] using hctx
  | @congRefl n a a' haa' ih =>
      have hstep := ih (k := k) (ρ := ρ) hcompat
      have hctx : TwoSortProfileTheoryStep
          (mkRefl (quoteTmWith ν k ρ a))
          (mkRefl (quoteTmWith ν k ρ a')) := by
        exact .ctx (K := .refl .hole) hstep
      simpa [quoteTmWith, mkRefl] using hctx

/-- Closed specialization of `twoSortTheoryStep_sound_twoSortProfileTheoryStep_quoteTmWith_assuming_inst0`
for the default binder naming policy. -/
theorem twoSortTheoryStep_sound_twoSortProfileTheoryStep_quoteClosed_assuming_inst0
    (hinst0 : Inst0OpenBridgeCompat defaultBinderName)
    (hcompat0 : QuoteCompat defaultBinderName 0 emptyEnv)
    {t u : ScopedTerm 0} (h : TwoSortTheoryStep t u) :
    TwoSortProfileTheoryStep (quoteClosedTm t) (quoteClosedTm u) := by
  simpa [quoteClosedTm, quoteTm, emptyEnv] using
    twoSortTheoryStep_sound_twoSortProfileTheoryStep_quoteTmWith_assuming_inst0
      (ν := defaultBinderName) hinst0 (k := 0) (ρ := emptyEnv) hcompat0 h

/-- Star-closure transport for B -> C1 under the same `inst0` bridge assumption. -/
theorem twoSortTheoryStepStar_sound_twoSortProfileTheoryStepStar_quoteClosed_assuming_inst0
    (hinst0 : Inst0OpenBridgeCompat defaultBinderName)
    (hcompat0 : QuoteCompat defaultBinderName 0 emptyEnv)
    {t u : ScopedTerm 0} (h : TwoSortTheoryStepStar t u) :
    TwoSortProfileTheoryStepStar (quoteClosedTm t) (quoteClosedTm u) := by
  induction h with
  | refl =>
      exact Relation.ReflTransGen.refl
  | tail hxy hyz ih =>
      exact Relation.ReflTransGen.tail ih
        (twoSortTheoryStep_sound_twoSortProfileTheoryStep_quoteClosed_assuming_inst0 hinst0 hcompat0 hyz)

/-- B -> C1 transport (parameterized by an `inst0` bridge witness). -/
theorem twoSortTheoryStep_sound_twoSortProfileTheoryStep_quoteTmWith
    (ν : Nat → String) (hinst0 : Inst0OpenBridgeCompat ν)
    {n : Nat} (k : Nat) (ρ : QuoteEnv n) {t u : ScopedTerm n}
    (hcompat : QuoteCompat ν k ρ)
    (h : Red t u) :
    TwoSortProfileTheoryStep (quoteTmWith ν k ρ t) (quoteTmWith ν k ρ u) :=
  twoSortTheoryStep_sound_twoSortProfileTheoryStep_quoteTmWith_assuming_inst0
    (ν := ν) hinst0 (k := k) (ρ := ρ) hcompat h

/-- Closed B -> C1 transport (parameterized by an `inst0` bridge witness). -/
theorem twoSortTheoryStep_sound_twoSortProfileTheoryStep_quoteClosed
    (hinst0 : Inst0OpenBridgeCompat defaultBinderName)
    (hcompat0 : QuoteCompat defaultBinderName 0 emptyEnv)
    {t u : ScopedTerm 0} (h : TwoSortTheoryStep t u) :
    TwoSortProfileTheoryStep (quoteClosedTm t) (quoteClosedTm u) :=
  twoSortTheoryStep_sound_twoSortProfileTheoryStep_quoteClosed_assuming_inst0 hinst0 hcompat0 h

/-- Closed star transport B* -> C1* (parameterized by an `inst0` bridge witness). -/
theorem twoSortTheoryStepStar_sound_twoSortProfileTheoryStepStar_quoteClosed
    (hinst0 : Inst0OpenBridgeCompat defaultBinderName)
    (hcompat0 : QuoteCompat defaultBinderName 0 emptyEnv)
    {t u : ScopedTerm 0} (h : TwoSortTheoryStepStar t u) :
    TwoSortProfileTheoryStepStar (quoteClosedTm t) (quoteClosedTm u) :=
  twoSortTheoryStepStar_sound_twoSortProfileTheoryStepStar_quoteClosed_assuming_inst0 hinst0 hcompat0 h

/-- Declaration-aware closed one-step soundness into C1 for the strongest
currently fully discharged declaration slice: ordered checked specs with no
declaration values. In that slice, declaration reduction collapses to the core
kernel reduction and therefore transports through the existing quotation bridge. -/
theorem checkedNoValuesDeclKernel_sound_twoSortProfileTheoryStep_quoteClosed
    {specs : List Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.DeclSpec}
    (_hSig :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.SignatureWellFormed
        specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    (hinst0 : Inst0OpenBridgeCompat defaultBinderName)
    (hcompat0 : QuoteCompat defaultBinderName 0 emptyEnv)
    {t u : ScopedTerm 0}
    (h : Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSemantics.RedDecl
      (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.envOfSpecs specs) t u) :
    TwoSortProfileTheoryStep (quoteClosedTm t) (quoteClosedTm u) := by
  have hNoValues :=
    Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.valueOf_envOfSpecs_eq_none_of_all_none
      specs hNone
  have hCore :
      Red t u :=
    Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSemantics.redDecl_to_core_of_no_values
      hNoValues h
  exact twoSortTheoryStep_sound_twoSortProfileTheoryStep_quoteClosed hinst0 hcompat0 hCore

/-- Declaration-aware closed star soundness into C1 for the all-none
declaration slice. This is the honest declaration-to-profile bridge available
today without crossing the value-bearing delta frontier. -/
theorem checkedNoValuesDeclKernel_star_sound_twoSortProfileTheoryStepStar_quoteClosed
    {specs : List Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.DeclSpec}
    (_hSig :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.SignatureWellFormed
        specs)
    (hNone : ∀ s ∈ specs, s.value? = none)
    (hinst0 : Inst0OpenBridgeCompat defaultBinderName)
    (hcompat0 : QuoteCompat defaultBinderName 0 emptyEnv)
    {t u : ScopedTerm 0}
    (h :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSemantics.RedStarDecl
        (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.envOfSpecs specs) t u) :
    TwoSortProfileTheoryStepStar (quoteClosedTm t) (quoteClosedTm u) := by
  have hNoValues :=
    Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.valueOf_envOfSpecs_eq_none_of_all_none
      specs hNone
  have hCore :
      RedStar t u :=
    Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSemantics.redStarDecl_to_core_of_no_values
      hNoValues h
  exact twoSortTheoryStepStar_sound_twoSortProfileTheoryStepStar_quoteClosed hinst0 hcompat0 hCore

/-- Packaged closed theoremic bridge for the strongest assumption-free
declaration boundary: declaration-level star subject reduction paired with the
quoted two-sort-profile execution witness. -/
theorem checkedNoValuesDeclKernelBoundary_closedSubjectReduction_and_profileBridge
    {specs : List Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.DeclSpec}
    {hSig :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.SignatureWellFormed
        specs}
    {hNone : ∀ s ∈ specs, s.value? = none}
    (hBoundary : CheckedNoValuesDeclKernelBoundary hSig hNone)
    (hinst0 : Inst0OpenBridgeCompat defaultBinderName)
    (hcompat0 : QuoteCompat defaultBinderName 0 emptyEnv)
    {t u A : ScopedTerm 0}
    (ht :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSemantics.HasTypeDecl
        (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.envOfSpecs specs) .nil t A)
    (h :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSemantics.RedStarDecl
        (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.envOfSpecs specs) t u) :
    Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSemantics.HasTypeDecl
        (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.envOfSpecs specs) .nil u A ∧
      TwoSortProfileTheoryStepStar (quoteClosedTm t) (quoteClosedTm u) := by
  exact
    ⟨ hBoundary.starSubjectReduction ht h
    , checkedNoValuesDeclKernel_star_sound_twoSortProfileTheoryStepStar_quoteClosed
        hSig hNone hinst0 hcompat0 h
    ⟩

/-- Packaged closed conversion bridge for the strongest assumption-free
declaration boundary: declaration conversion yields a quoted common reduct in
the two-sort profile theory step star. -/
theorem checkedNoValuesDeclKernelBoundary_closedCommonReduct_profileBridge
    {specs : List Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.DeclSpec}
    {hSig :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.SignatureWellFormed
        specs}
    {hNone : ∀ s ∈ specs, s.value? = none}
    (hBoundary : CheckedNoValuesDeclKernelBoundary hSig hNone)
    (hinst0 : Inst0OpenBridgeCompat defaultBinderName)
    (hcompat0 : QuoteCompat defaultBinderName 0 emptyEnv)
    {t u : ScopedTerm 0}
    (h :
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSemantics.ConvDecl
        (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec.envOfSpecs specs) t u) :
    ∃ q : Pattern,
      TwoSortProfileTheoryStepStar (quoteClosedTm t) q ∧
      TwoSortProfileTheoryStepStar (quoteClosedTm u) q := by
  rcases hBoundary.commonReduct h with ⟨w, ht, hu⟩
  exact
    ⟨ quoteClosedTm w
    , checkedNoValuesDeclKernel_star_sound_twoSortProfileTheoryStepStar_quoteClosed
        hSig hNone hinst0 hcompat0 ht
    , checkedNoValuesDeclKernel_star_sound_twoSortProfileTheoryStepStar_quoteClosed
        hSig hNone hinst0 hcompat0 hu
    ⟩

private def betaPiOneNestedLamRedex : ScopedTerm 0 :=
  .app (.lam (.lam (.var (Fin.succ (0 : Fin 1))))) .u0

private def betaPiOneNestedLamContractum : ScopedTerm 0 :=
  .lam .u0

private def betaPiTwoNestedLamRedex : ScopedTerm 0 :=
  .app (.lam (.lam (.lam (.var (Fin.succ (Fin.succ (0 : Fin 1))))))) .u0

private def betaPiTwoNestedLamContractum : ScopedTerm 0 :=
  .lam (.lam .u0)

/-- Regression: one nested binder in βΠ body still transports to C1. -/
theorem betaPi_bridge_regression_one_nestedLam_assuming_inst0
    (hinst0 : Inst0OpenBridgeCompat defaultBinderName)
    (hcompat0 : QuoteCompat defaultBinderName 0 emptyEnv) :
    TwoSortProfileTheoryStep
      (quoteClosedTm betaPiOneNestedLamRedex)
      (quoteClosedTm betaPiOneNestedLamContractum) := by
  have hred : Red betaPiOneNestedLamRedex betaPiOneNestedLamContractum := by
    unfold betaPiOneNestedLamRedex betaPiOneNestedLamContractum
    exact (Red.betaPi (.lam (.var (Fin.succ (0 : Fin 1)))) (.u0))
  exact twoSortTheoryStep_sound_twoSortProfileTheoryStep_quoteClosed_assuming_inst0 hinst0 hcompat0 hred

/-- Regression: two nested binders in βΠ body still transports to C1. -/
theorem betaPi_bridge_regression_two_nestedLam_assuming_inst0
    (hinst0 : Inst0OpenBridgeCompat defaultBinderName)
    (hcompat0 : QuoteCompat defaultBinderName 0 emptyEnv) :
    TwoSortProfileTheoryStep
      (quoteClosedTm betaPiTwoNestedLamRedex)
      (quoteClosedTm betaPiTwoNestedLamContractum) := by
  have hred : Red betaPiTwoNestedLamRedex betaPiTwoNestedLamContractum := by
    unfold betaPiTwoNestedLamRedex betaPiTwoNestedLamContractum
    exact (Red.betaPi (.lam (.lam (.var (Fin.succ (Fin.succ (0 : Fin 1)))))) (.u0))
  exact twoSortTheoryStep_sound_twoSortProfileTheoryStep_quoteClosed_assuming_inst0 hinst0 hcompat0 hred

/-- Backwards-compatible name for the A-layer step relation. -/
abbrev ClosedComputationStep : ScopedTerm 0 → ScopedTerm 0 → Prop := TwoSortOpStep

/-- Backwards-compatible name for A-layer star closure. -/
abbrev ClosedComputationStepStar (t u : ScopedTerm 0) : Prop := TwoSortOpStepStar t u

/-- Backwards-compatible theorem alias. -/
theorem closedComputationStep_to_red {t u : ScopedTerm 0}
    (h : ClosedComputationStep t u) : Red t u := by
  simpa [ClosedComputationStep, TwoSortTheoryStep] using
    (twoSortOpStep_to_twoSortTheoryStep (t := t) (u := u) h)

/-- Backwards-compatible theorem alias. -/
theorem closedComputationStepStar_to_redStar {t u : ScopedTerm 0}
    (h : ClosedComputationStepStar t u) : RedStar t u := by
  simpa [ClosedComputationStepStar, TwoSortTheoryStepStar] using
    (twoSortOpStepStar_to_twoSortTheoryStepStar (t := t) (u := u) h)

/-- Backwards-compatible theorem alias. -/
theorem closedComputationStep_sound_langReduces_quoteClosed {t u : ScopedTerm 0}
    (h : ClosedComputationStep t u) :
    langReduces twoSortDependent (quoteClosedTm t) (quoteClosedTm u) := by
  simpa [ClosedComputationStep] using
    (twoSortOpStep_sound_langReduces_quoteClosed (t := t) (u := u) h)

/-- Backwards-compatible theorem alias. -/
theorem closedComputationStepStar_sound_langReduces_quoteClosed {t u : ScopedTerm 0}
    (h : ClosedComputationStepStar t u) :
    TwoSortProfileStepStar (quoteClosedTm t) (quoteClosedTm u) := by
  simpa [ClosedComputationStepStar] using
    (twoSortOpStepStar_sound_langReduces_quoteClosed (t := t) (u := u) h)

/-- Negative bridge example:
the full kernel step relation (`Red`, with constructor congruence) is strictly
stronger than current `langReduces twoSortDependent` (top-level rewrite in this profile). -/
theorem not_all_twoSortTheoryStep_sound_to_langReduces_quoteClosed :
    ¬ (∀ {t u : ScopedTerm 0}, TwoSortTheoryStep t u →
        langReduces twoSortDependent (quoteClosedTm t) (quoteClosedTm u)) := by
  intro hsound
  let t : ScopedTerm 0 := .app .u1 (.fst (.pair .u0 .u1))
  let u : ScopedTerm 0 := .app .u1 .u0
  have hred : TwoSortTheoryStep t u := by
    simpa [TwoSortTheoryStep] using (Red.congAppArg (Red.betaSigmaFst _ _))
  have hlang : langReduces twoSortDependent (quoteClosedTm t) (quoteClosedTm u) := hsound hred
  have noMatch : ∀ rule, rule ∈ twoSortDependent.rewrites →
      Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical.matchPatternForRule
        twoSortDependent rule (quoteClosedTm t) = [] := by
    intro rule ruleMember
    simp only [twoSortDependent, List.mem_cons, List.not_mem_nil, or_false] at ruleMember
    rcases ruleMember with rfl | rfl | rfl <;>
      simp [t, quoteClosedTm, quoteTm, quoteTmWith, mkApp, mkFst, mkPair,
        twoSortDependent, u1, matchArgs, matchPattern]
  apply (not_step_of_matchPatternForRule_eq_nil noMatch)
  simpa [langReduces, langReducesUsing] using hlang

/-- Backwards-compatible name for the same mismatch fact. -/
theorem not_all_red_steps_sound_to_langReduces_quoteClosed :
    ¬ (∀ {t u : ScopedTerm 0}, Red t u →
        langReduces twoSortDependent (quoteClosedTm t) (quoteClosedTm u)) := by
  intro h
  exact not_all_twoSortTheoryStep_sound_to_langReduces_quoteClosed (fun hred => h hred)

end Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.CoreEmbedding
