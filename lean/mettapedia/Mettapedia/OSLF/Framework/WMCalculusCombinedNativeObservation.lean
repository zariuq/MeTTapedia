import Mettapedia.OSLF.Framework.WMCalculusCombinedIntrinsicTransport
import Mettapedia.OSLF.Syntax.SyntacticTermPresheaf
import Mettapedia.OSLF.PresheafNativeType.InternalLanguage
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes

/-!
# Native observation over the guarded overlap-and-scope WM vertex

The combined authored vertex has its own intrinsically sorted term presheaves.
Overlap correction and forgetting are natural term operations under simultaneous
substitution. Its unconditional overlap-extraction rule is also stable under
reindexing. The outside-scope forgetting computation remains conditional on a
relation provider; naturality of the `Forget` constructor does not discharge
that guard.
-/

namespace Mettapedia.OSLF.Framework.WMCalculusCombinedNativeObservation

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.Syntactic
open Mettapedia.OSLF.Framework.WMCalculusCombinedIntrinsicTransport

set_option autoImplicit false

private abbrev State := Mettapedia.OSLF.MeTTaIL.Syntax.TypeExpr.base "State"
private abbrev Query := Mettapedia.OSLF.MeTTaIL.Syntax.TypeExpr.base "Query"
private abbrev Evidence := Mettapedia.OSLF.MeTTaIL.Syntax.TypeExpr.base "BinaryEvidence"
private abbrev Overlap := Mettapedia.OSLF.MeTTaIL.Syntax.TypeExpr.base "Overlap"
private abbrev Scope := Mettapedia.OSLF.MeTTaIL.Syntax.TypeExpr.base "Scope"

abbrev CombinedCtxt := Syntactic.Ctxt CombinedSignature

def stateTerms : (CombinedCtxt)ᵒᵖ ⥤ Type := termPresheaf CombinedSignature State
def queryTerms : (CombinedCtxt)ᵒᵖ ⥤ Type := termPresheaf CombinedSignature Query
def evidenceTerms : (CombinedCtxt)ᵒᵖ ⥤ Type := termPresheaf CombinedSignature Evidence
def overlapTerms : (CombinedCtxt)ᵒᵖ ⥤ Type := termPresheaf CombinedSignature Overlap
def scopeTerms : (CombinedCtxt)ᵒᵖ ⥤ Type := termPresheaf CombinedSignature Scope

def statePairs : (CombinedCtxt)ᵒᵖ ⥤ Type :=
  FunctorToTypes.prod stateTerms stateTerms

def evidencePairs : (CombinedCtxt)ᵒᵖ ⥤ Type :=
  FunctorToTypes.prod evidenceTerms evidenceTerms

def overlapInputs : (CombinedCtxt)ᵒᵖ ⥤ Type :=
  FunctorToTypes.prod statePairs queryTerms

def observationInputs : (CombinedCtxt)ᵒᵖ ⥤ Type :=
  FunctorToTypes.prod stateTerms queryTerms

def forgetInputs : (CombinedCtxt)ᵒᵖ ⥤ Type :=
  FunctorToTypes.prod scopeTerms stateTerms

def overlapCorrectInputs : (CombinedCtxt)ᵒᵖ ⥤ Type :=
  FunctorToTypes.prod evidencePairs overlapTerms

/-- The authored overlap merger is natural in its two state arguments. -/
def overlapMergeNat : statePairs ⟶ stateTerms where
  app X := TypeCat.ofHom (fun input => overlapMerge input.1 input.2)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro input
    rcases input with ⟨first, second⟩
    rfl

/-- A guarded vertex's overlap factor has a separate sort and respects
simultaneous substitution in all three arguments. -/
def overlapFactorNat : overlapInputs ⟶ overlapTerms where
  app X := TypeCat.ofHom (fun input =>
    overlapFactor input.1.1 input.1.2 input.2)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro input
    rcases input with ⟨⟨first, second⟩, query⟩
    rfl

/-- Correction consumes two evidence terms and a separately typed factor;
it too commutes with arbitrary sorted simultaneous substitution. -/
def overlapCorrectNat : overlapCorrectInputs ⟶ evidenceTerms where
  app X := TypeCat.ofHom (fun input =>
    overlapCorrect input.1.1 input.1.2 input.2)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro input
    rcases input with ⟨⟨first, second⟩, factor⟩
    rfl

/-- Scope restriction is a natural syntax operation, not an unconditional
equation of observations. -/
def forgetNat : forgetInputs ⟶ stateTerms where
  app X := TypeCat.ofHom (fun input => forget input.1 input.2)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro input
    rcases input with ⟨scope, world⟩
    rfl

/-- The redex for the unconditional state-level idempotence computation. -/
def forgetIdempotenceRedexNat : forgetInputs ⟶ stateTerms where
  app X := TypeCat.ofHom (fun input =>
    forget input.1 (forget input.1 input.2))
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro input
    rcases input with ⟨scope, world⟩
    rfl

/-- Observation in the combined syntax is natural in substitution. -/
def extractNat : observationInputs ⟶ evidenceTerms where
  app X := TypeCat.ofHom (fun input => extract input.1 input.2)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro input
    rcases input with ⟨world, query⟩
    exact (bind_extract f.unop world query).symm

/-- The redex of the authored overlap computation, at each context. -/
def overlapRedexNat : overlapInputs ⟶ evidenceTerms where
  app X := TypeCat.ofHom (fun input =>
    extract (overlapMerge input.1.1 input.1.2) input.2)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro input
    rcases input with ⟨⟨first, second⟩, query⟩
    change bind f.unop (extract (overlapMerge first second) query) =
      extract (overlapMerge (bind f.unop first) (bind f.unop second))
        (bind f.unop query)
    rfl

/-- The contractum retains an explicit `Overlap`-sorted correction factor. -/
def overlapContractumNat : overlapInputs ⟶ evidenceTerms where
  app X := TypeCat.ofHom (fun input =>
    overlapCorrect (extract input.1.1 input.2)
      (extract input.1.2 input.2)
      (overlapFactor input.1.1 input.1.2 input.2))
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro input
    rcases input with ⟨⟨first, second⟩, query⟩
    change bind f.unop
      (overlapCorrect (extract first query) (extract second query)
        (overlapFactor first second query)) =
      overlapCorrect (extract (bind f.unop first) (bind f.unop query))
        (extract (bind f.unop second) (bind f.unop query))
        (overlapFactor (bind f.unop first) (bind f.unop second)
          (bind f.unop query))
    rfl

/-- The actual authored overlap rewrite connects the two natural term
operations at every syntactic context. -/
theorem overlap_computes_pointwise (X : (CombinedCtxt)ᵒᵖ)
    (input : overlapInputs.obj X) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langSemanticReduces
      (Mettapedia.OSLF.Framework.WMCalculusLanguageDef.wmExtVertexLanguageDefGuarded
        Mettapedia.OSLF.Framework.WMCalculusCombinedSortedBoundary.combinedVertex)
      (Mettapedia.GSLT.LanguageDef.BindingSyntax.erase
        (overlapRedexNat.app X input))
      (Mettapedia.GSLT.LanguageDef.BindingSyntax.erase
        (overlapContractumNat.app X input)) := by
  rcases input with ⟨⟨first, second⟩, query⟩
  exact intrinsic_overlapExtract_computes first second query

/-- Reindexing all inputs by any sorted simultaneous substitution preserves
the authored overlap step. -/
theorem overlap_computes_after_reindexing {X Y : (CombinedCtxt)ᵒᵖ}
    (f : X ⟶ Y) (input : overlapInputs.obj X) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langSemanticReduces
      (Mettapedia.OSLF.Framework.WMCalculusLanguageDef.wmExtVertexLanguageDefGuarded
        Mettapedia.OSLF.Framework.WMCalculusCombinedSortedBoundary.combinedVertex)
      (Mettapedia.GSLT.LanguageDef.BindingSyntax.erase
        ((evidenceTerms.map f) (overlapRedexNat.app X input)))
      (Mettapedia.GSLT.LanguageDef.BindingSyntax.erase
        ((evidenceTerms.map f) (overlapContractumNat.app X input))) := by
  rw [← NatTrans.naturality_apply overlapRedexNat f input,
    ← NatTrans.naturality_apply overlapContractumNat f input]
  exact overlap_computes_pointwise Y ((overlapInputs.map f) input)

/-- Idempotent forgetting is an authored computation at every intrinsic
context. It does not require an outside-scope answer. -/
theorem forget_idempotence_pointwise (X : (CombinedCtxt)ᵒᵖ)
    (input : forgetInputs.obj X) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langSemanticReduces
      (Mettapedia.OSLF.Framework.WMCalculusLanguageDef.wmExtVertexLanguageDefGuarded
        Mettapedia.OSLF.Framework.WMCalculusCombinedSortedBoundary.combinedVertex)
      (Mettapedia.GSLT.LanguageDef.BindingSyntax.erase
        (forgetIdempotenceRedexNat.app X input))
      (Mettapedia.GSLT.LanguageDef.BindingSyntax.erase
        (forgetNat.app X input)) := by
  rcases input with ⟨scope, world⟩
  change Mettapedia.OSLF.Framework.TypeSynthesis.langSemanticReduces
    (Mettapedia.OSLF.Framework.WMCalculusLanguageDef.wmExtVertexLanguageDefGuarded
      Mettapedia.OSLF.Framework.WMCalculusCombinedSortedBoundary.combinedVertex)
    (Mettapedia.OSLF.Framework.WMCalculusLanguageDef.pForget
      (Mettapedia.GSLT.LanguageDef.BindingSyntax.erase scope)
      (Mettapedia.OSLF.Framework.WMCalculusLanguageDef.pForget
        (Mettapedia.GSLT.LanguageDef.BindingSyntax.erase scope)
        (Mettapedia.GSLT.LanguageDef.BindingSyntax.erase world)))
    (Mettapedia.OSLF.Framework.WMCalculusLanguageDef.pForget
      (Mettapedia.GSLT.LanguageDef.BindingSyntax.erase scope)
      (Mettapedia.GSLT.LanguageDef.BindingSyntax.erase world))
  exact forgetIdempotent_raw
    (Mettapedia.GSLT.LanguageDef.BindingSyntax.erase scope)
    (Mettapedia.GSLT.LanguageDef.BindingSyntax.erase world)

/-- The same forgetting computation survives arbitrary sorted reindexing. -/
theorem forget_idempotence_after_reindexing {X Y : (CombinedCtxt)ᵒᵖ}
    (f : X ⟶ Y) (input : forgetInputs.obj X) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langSemanticReduces
      (Mettapedia.OSLF.Framework.WMCalculusLanguageDef.wmExtVertexLanguageDefGuarded
        Mettapedia.OSLF.Framework.WMCalculusCombinedSortedBoundary.combinedVertex)
      (Mettapedia.GSLT.LanguageDef.BindingSyntax.erase
        ((stateTerms.map f) (forgetIdempotenceRedexNat.app X input)))
      (Mettapedia.GSLT.LanguageDef.BindingSyntax.erase
        ((stateTerms.map f) (forgetNat.app X input))) := by
  rw [← NatTrans.naturality_apply forgetIdempotenceRedexNat f input,
    ← NatTrans.naturality_apply forgetNat f input]
  exact forget_idempotence_pointwise Y ((forgetInputs.map f) input)

/-- Observation gives a genuine dependent context in the existing native
predicate fibration, with both typed inputs retained. -/
def observationDepCtx :
    Mettapedia.OSLF.PresheafNativeType.PresheafDepCtx (C := CombinedCtxt) where
  A := observationInputs
  B := evidenceTerms
  f := extractNat

theorem observationSigmaIntro
    (φ : CategoryTheory.Subfunctor observationInputs) :
    φ ≤ observationDepCtx.pb (observationDepCtx.sigmaForm φ) :=
  observationDepCtx.sigmaIntro_presheaf φ

theorem observationPiElim
    (φ : CategoryTheory.Subfunctor observationInputs) :
    observationDepCtx.pb (observationDepCtx.piForm φ) ≤ φ :=
  observationDepCtx.piBeta_presheaf φ

#print axioms overlapMergeNat
#print axioms overlapFactorNat
#print axioms overlapCorrectNat
#print axioms forgetNat
#print axioms forget_idempotence_pointwise
#print axioms forget_idempotence_after_reindexing
#print axioms overlap_computes_pointwise
#print axioms overlap_computes_after_reindexing
#print axioms observationSigmaIntro
#print axioms observationPiElim

end Mettapedia.OSLF.Framework.WMCalculusCombinedNativeObservation
