import Mettapedia.OSLF.Framework.WMCalculusBindingSignature
import Mettapedia.OSLF.Syntax.SyntacticTermPresheaf
import Mettapedia.OSLF.PresheafNativeType.InternalLanguage
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes

/-!
# World-model observation over intrinsic syntactic contexts

The declaration-derived `Extract` constructor is natural in simultaneous
substitution of its state and query arguments. Thus it is a map of actual
context-indexed term presheaves, rather than merely a function on erased
patterns. The generic native predicate fibration can reindex along this map;
its dependent Σ and Π operators apply to predicates of observations.

This is an entry point into the native dependent-type machinery, not a claim
that the complete classifying λ-theory or internal-language functor exists.
-/

namespace Mettapedia.OSLF.Framework.WMCalculusIntrinsicPresheafObservation

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.Syntactic
open Mettapedia.OSLF.Framework.WMCalculusBindingSignature

set_option autoImplicit false

abbrev WMCtxt := Syntactic.Ctxt WMSignature
private abbrev State := Mettapedia.OSLF.MeTTaIL.Syntax.TypeExpr.base "State"
private abbrev Query := Mettapedia.OSLF.MeTTaIL.Syntax.TypeExpr.base "Query"
private abbrev Evidence := Mettapedia.OSLF.MeTTaIL.Syntax.TypeExpr.base "BinaryEvidence"

/-- Intrinsically sorted WM state terms over syntactic contexts. -/
def stateTerms : (WMCtxt)ᵒᵖ ⥤ Type := termPresheaf WMSignature State

/-- Intrinsically sorted WM query terms over syntactic contexts. -/
def queryTerms : (WMCtxt)ᵒᵖ ⥤ Type := termPresheaf WMSignature Query

/-- Intrinsically sorted WM evidence terms over syntactic contexts. -/
def evidenceTerms : (WMCtxt)ᵒᵖ ⥤ Type := termPresheaf WMSignature Evidence

/-- Pairs of states in one context, with simultaneous substitution. -/
def statePairs : (WMCtxt)ᵒᵖ ⥤ Type := FunctorToTypes.prod stateTerms stateTerms

/-- Pairs of evidence terms in one context. -/
def evidencePairs : (WMCtxt)ᵒᵖ ⥤ Type := FunctorToTypes.prod evidenceTerms evidenceTerms

/-- The one-element presheaf is the input arity of `EvidenceZero`. -/
def zeroInputs : (WMCtxt)ᵒᵖ ⥤ Type := (Functor.const (WMCtxt)ᵒᵖ).obj PUnit

/-- Authored `Revise` respects every sorted simultaneous substitution. -/
def reviseNat : statePairs ⟶ stateTerms where
  app X := TypeCat.ofHom (fun pair => revise pair.1 pair.2)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro pair
    rcases pair with ⟨first, second⟩
    rfl

/-- Authored `Combine` respects every sorted simultaneous substitution. -/
def combineNat : evidencePairs ⟶ evidenceTerms where
  app X := TypeCat.ofHom (fun pair => combine pair.1 pair.2)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro pair
    rcases pair with ⟨first, second⟩
    rfl

/-- Authored nullary `EvidenceZero` is a global section of evidence terms. -/
def zeroNat : zeroInputs ⟶ evidenceTerms where
  app X := TypeCat.ofHom (fun _ => zero)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro input
    rfl

/-- State and query terms in the same context, with componentwise substitution. -/
def observationInputs : (WMCtxt)ᵒᵖ ⥤ Type :=
  FunctorToTypes.prod stateTerms queryTerms

/-- Authored WM extraction is a natural map from state/query pairs to evidence. -/
def extractNat : observationInputs ⟶ evidenceTerms where
  app X := TypeCat.ofHom (fun pair => extract pair.1 pair.2)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro pair
    exact (bind_extract f.unop pair.1 pair.2).symm

/-- The component at a context is precisely the authored intrinsic `Extract`.
No second operation is inserted by the presheaf packaging. -/
theorem extractNat_app (X : (WMCtxt)ᵒᵖ)
    (world : Term WMSignature X.unop.vars State)
    (query : Term WMSignature X.unop.vars Query) :
    extractNat.app X (world, query) = extract world query := rfl

/-- Natural reindexing says that observation commutes with every sorted
simultaneous substitution, including substitutions that duplicate variables. -/
theorem extractNat_substitution {X Y : (WMCtxt)ᵒᵖ} (f : X ⟶ Y)
    (world : Term WMSignature X.unop.vars State)
    (query : Term WMSignature X.unop.vars Query) :
    (evidenceTerms.map f) (extractNat.app X (world, query)) =
      extractNat.app Y ((observationInputs.map f) (world, query)) := by
  exact bind_extract f.unop world query

/-- Two state terms and one shared query, reindexed together. -/
def revisionInputs : (WMCtxt)ᵒᵖ ⥤ Type :=
  FunctorToTypes.prod statePairs queryTerms

/-- The redex side of the authored extraction rule, natural in substitution. -/
def extractionRedexNat : revisionInputs ⟶ evidenceTerms where
  app X := TypeCat.ofHom (fun input => extract (revise input.1.1 input.1.2) input.2)
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro input
    rcases input with ⟨⟨first, second⟩, query⟩
    change bind f.unop (extract (revise first second) query) =
      extract (revise (bind f.unop first) (bind f.unop second)) (bind f.unop query)
    rfl

/-- The contractum side of the same rule, natural in substitution. -/
def extractionContractumNat : revisionInputs ⟶ evidenceTerms where
  app X := TypeCat.ofHom (fun input =>
    combine (extract input.1.1 input.2) (extract input.1.2 input.2))
  naturality X Y f := by
    apply ConcreteCategory.hom_ext
    intro input
    rcases input with ⟨⟨first, second⟩, query⟩
    change bind f.unop (combine (extract first query) (extract second query)) =
      combine (extract (bind f.unop first) (bind f.unop query))
        (extract (bind f.unop second) (bind f.unop query))
    rfl

/-- The authored computational step is pointwise between the two natural
maps, at every context and for every intrinsically sorted input triple. -/
theorem extraction_computes_pointwise (X : (WMCtxt)ᵒᵖ)
    (input : revisionInputs.obj X) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langSemanticReduces
      WMCalculusStructuralPresentation.wmStructuralLanguageDef
      (Mettapedia.GSLT.LanguageDef.BindingSyntax.erase
        (extractionRedexNat.app X input))
      (Mettapedia.GSLT.LanguageDef.BindingSyntax.erase
        (extractionContractumNat.app X input)) := by
  rcases input with ⟨⟨first, second⟩, query⟩
  exact (intrinsic_extraction_typed_computation first second query).2.2

/-- The same authored step remains valid after reindexing all three inputs
by an arbitrary sorted simultaneous substitution. -/
theorem extraction_computes_after_reindexing {X Y : (WMCtxt)ᵒᵖ}
    (f : X ⟶ Y) (input : revisionInputs.obj X) :
    Mettapedia.OSLF.Framework.TypeSynthesis.langSemanticReduces
      WMCalculusStructuralPresentation.wmStructuralLanguageDef
      (Mettapedia.GSLT.LanguageDef.BindingSyntax.erase
        ((evidenceTerms.map f) (extractionRedexNat.app X input)))
      (Mettapedia.GSLT.LanguageDef.BindingSyntax.erase
        ((evidenceTerms.map f) (extractionContractumNat.app X input))) := by
  rw [← NatTrans.naturality_apply extractionRedexNat f input,
    ← NatTrans.naturality_apply extractionContractumNat f input]
  exact extraction_computes_pointwise Y ((revisionInputs.map f) input)

/-- Raw patterns with trivial restriction maps, used only to state the
boundary between context-sensitive syntax and context-free erasure. -/
def constantRawPatterns : (WMCtxt)ᵒᵖ ⥤ Type :=
  (Functor.const (WMCtxt)ᵒᵖ).obj Mettapedia.OSLF.MeTTaIL.Syntax.Pattern

/-- No natural map to a constant raw-pattern presheaf can have erasure as
every component: a genuine substitution changes a bound-variable index. -/
theorem no_constant_erasure_nat :
    ¬ ∃ α : stateTerms ⟶ constantRawPatterns,
      ∀ (X : (WMCtxt)ᵒᵖ) (t : Term WMSignature X.unop.vars State),
        α.app X t = Mettapedia.GSLT.LanguageDef.BindingSyntax.erase t := by
  rintro ⟨α, hα⟩
  let σ : (⟨[State]⟩ : WMCtxt) ⟶ (⟨[State, State]⟩ : WMCtxt) :=
    extend (Term.var (S := WMSignature) (Γ := [State]) .zero)
  let t : Term WMSignature [State, State] State := .var (.succ .zero)
  have hnat := NatTrans.naturality_apply α (Quiver.Hom.op σ) t
  rw [hα (Opposite.op ⟨[State]⟩) ((stateTerms.map (Quiver.Hom.op σ)) t),
    hα (Opposite.op ⟨[State, State]⟩) t] at hnat
  have hChanged := erasure_not_constant_under_substitution
  apply hChanged
  change Mettapedia.GSLT.LanguageDef.BindingSyntax.erase (bind σ t) =
    (𝟙 Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
      (Mettapedia.GSLT.LanguageDef.BindingSyntax.erase t) at hnat
  simpa using hnat

/-- This is the actual dependent context exposed to the presheaf-native
predicate fibration: an observation map whose source retains both inputs. -/
def observationDepCtx :
    Mettapedia.OSLF.PresheafNativeType.PresheafDepCtx (C := WMCtxt) where
  A := observationInputs
  B := evidenceTerms
  f := extractNat

/-- Σ-introduction for predicates on actual authored WM observations. -/
theorem observationSigmaIntro
    (φ : CategoryTheory.Subfunctor observationInputs) :
    φ ≤ observationDepCtx.pb (observationDepCtx.sigmaForm φ) :=
  observationDepCtx.sigmaIntro_presheaf φ

/-- Π-elimination for predicates on actual authored WM observations. -/
theorem observationPiElim
    (φ : CategoryTheory.Subfunctor observationInputs) :
    observationDepCtx.pb (observationDepCtx.piForm φ) ≤ φ :=
  observationDepCtx.piBeta_presheaf φ

#print axioms extractNat_substitution
#print axioms reviseNat
#print axioms combineNat
#print axioms zeroNat
#print axioms extraction_computes_pointwise
#print axioms extraction_computes_after_reindexing
#print axioms no_constant_erasure_nat
#print axioms observationSigmaIntro
#print axioms observationPiElim

end Mettapedia.OSLF.Framework.WMCalculusIntrinsicPresheafObservation
