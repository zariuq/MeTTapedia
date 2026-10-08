import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalSyntacticTelescopes
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalContextualProducts
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalContextualSumElimination
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalHeaderFormation
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalModel

/-!
# Primitive meanings in the generated contextual model

An authored declaration's actual formation trees provide its parameter
context and its result type. Its meaning in the generated model is the
corresponding primitive family or section, transported to the chosen
comprehension presentation of that header. No interpretation of whole
derivations is assumed by these primitive data.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.SyntacticModel

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualTypeOperations

universe u
variable {S : Symbols.{u}} {D : Signature S}

noncomputable abbrev C (D : Signature S) := QuotientCwf.withTerminal D

def typeHeader (headers : HeaderFormation D) (symbol : S.TypeSymbol) : Context D :=
  ⟨S.typeArity symbol, D.typeParameters symbol,
    derivationContextFormation (headers.typeHeader symbol)⟩

def termHeader (headers : HeaderFormation D) (symbol : S.TermSymbol) : Context D :=
  ⟨S.termArity symbol, D.termParameters symbol,
    derivationContextFormation (headers.termHeader symbol)⟩

noncomputable def parameterContext (context : Context D) :
    Mettapedia.TypeTheory.ContextualModelTelescopes.Context (C D) context.arity :=
  ⟨(quotientProjection D).obj (Presentation.selectedContext context),
    Presentation.selectedTelescope context⟩

noncomputable def parameterComparison (context : Context D) :
    (quotientProjection D).obj (Presentation.selectedContext context) ≅
      (quotientProjection D).obj context :=
  (quotientProjection D).mapIso (Presentation.comparison context)

def originalFamily (headers : HeaderFormation D) (symbol : S.TypeSymbol) :
    TypeOver (typeHeader headers symbol) :=
  ⟨.family symbol TermExpr.var,
    conclude (.typeFamily (D.typeParameters symbol) symbol TermExpr.var)
      ⟨⟨headers.typeHeader symbol⟩, ⟨headers.typeHeader symbol⟩,
        conclude (.substitutionIdentity (D.typeParameters symbol))
          ⟨⟨headers.typeHeader symbol⟩, trivial⟩, trivial⟩⟩

def originalResult (headers : HeaderFormation D) (symbol : S.TermSymbol) :
    TypeOver (termHeader headers symbol) :=
  ⟨D.termResult symbol, ⟨headers.termResult symbol⟩⟩

def originalPrimitive (headers : HeaderFormation D) (symbol : S.TermSymbol) :
    Term (termHeader headers symbol) (originalResult headers symbol) where
  code := .primitive symbol TermExpr.var
  typed := by
    have supplied := conclude (.primitive (D.termParameters symbol) symbol TermExpr.var)
      ⟨⟨headers.termHeader symbol⟩, ⟨headers.termHeader symbol⟩, ⟨headers.termResult symbol⟩,
        conclude (.substitutionIdentity (D.termParameters symbol))
          ⟨⟨headers.termHeader symbol⟩, trivial⟩, trivial⟩
    change Holds D (.term (D.termParameters symbol) (.primitive symbol TermExpr.var)
      ((D.termResult symbol).substitute TermExpr.var)) at supplied
    rw [TypeExpr.substitute_identity] at supplied
    exact supplied

noncomputable def rawFamily (headers : HeaderFormation D) (symbol : S.TypeSymbol) :
    TypeOver (Presentation.selectedContext (typeHeader headers symbol)) :=
  ⟨.family symbol TermExpr.var,
    conclude (.typeFamily (Presentation.selectedContext (typeHeader headers symbol)).raw
      symbol TermExpr.var)
      ⟨(Presentation.selectedContext (typeHeader headers symbol)).formed.judgment,
        ⟨headers.typeHeader symbol⟩, (Presentation.comparison (typeHeader headers symbol)).hom.admitted,
        trivial⟩⟩

noncomputable def rawResult (headers : HeaderFormation D) (symbol : S.TermSymbol) :
    TypeOver (Presentation.selectedContext (termHeader headers symbol)) :=
  ⟨D.termResult symbol,
    conclude (.transportType (D.termParameters symbol)
      (Presentation.selectedContext (termHeader headers symbol)).raw (D.termResult symbol))
      ⟨Presentation.contextEquality_symm
        (Presentation.select (termHeader headers symbol).raw (termHeader headers symbol).formed).equivalent,
        ⟨headers.termResult symbol⟩, trivial⟩⟩

set_option backward.isDefEq.respectTransparency false in
noncomputable def rawPrimitive (headers : HeaderFormation D) (symbol : S.TermSymbol) :
    Term (Presentation.selectedContext (termHeader headers symbol)) (rawResult headers symbol) where
  code := .primitive symbol TermExpr.var
  typed := by
    have supplied := conclude
      (.primitive (Presentation.selectedContext (termHeader headers symbol)).raw symbol TermExpr.var)
      ⟨(Presentation.selectedContext (termHeader headers symbol)).formed.judgment,
        ⟨headers.termHeader symbol⟩, ⟨headers.termResult symbol⟩,
        (Presentation.comparison (termHeader headers symbol)).hom.admitted, trivial⟩
    change Holds D (.term (Presentation.selectedContext (termHeader headers symbol)).raw
      (.primitive symbol TermExpr.var) (D.termResult symbol))
    change Holds D (.term (Presentation.selectedContext (termHeader headers symbol)).raw
      (.primitive symbol TermExpr.var) ((D.termResult symbol).substitute TermExpr.var)) at supplied
    rw [TypeExpr.substitute_identity] at supplied
    exact supplied

noncomputable def data (headers : HeaderFormation D) : ModelData S (C D) where
  products := Products.operations D
  sums := SumElimination.stable D
  typeParameters symbol := parameterContext (typeHeader headers symbol)
  typeFamily symbol := QType.mk (rawFamily headers symbol)
  termParameters symbol := parameterContext (termHeader headers symbol)
  termType symbol := QType.mk (rawResult headers symbol)
  termValue symbol := ⟨QTerm.mk (rawPrimitive headers symbol), rfl⟩

theorem data_derivation_independent (first second : HeaderFormation D) :
    data first = data second := rfl

set_option backward.isDefEq.respectTransparency false in
theorem family_at_original_header (headers : HeaderFormation D) (symbol : S.TypeSymbol) :
    (C D).toCwf.tySub ((data headers).typeFamily symbol)
      (parameterComparison (typeHeader headers symbol)).inv = QType.mk (originalFamily headers symbol) := by
  change QType.mk ((rawFamily headers symbol).reindex
    (Presentation.comparison (typeHeader headers symbol)).inv) = _
  apply congrArg QType.mk
  apply TypeOver.ext
  change (.family symbol TermExpr.var : TypeExpr S _).substitute
    (Presentation.comparison (typeHeader headers symbol)).inv.substitution = _
  rw [Presentation.comparison_inv_substitution, TypeExpr.substitute_identity]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem result_at_original_header (headers : HeaderFormation D) (symbol : S.TermSymbol) :
    (C D).toCwf.tySub ((data headers).termType symbol)
      (parameterComparison (termHeader headers symbol)).inv = QType.mk (originalResult headers symbol) := by
  change QType.mk ((rawResult headers symbol).reindex
    (Presentation.comparison (termHeader headers symbol)).inv) = _
  apply congrArg QType.mk
  apply TypeOver.ext
  change (D.termResult symbol).substitute
    (Presentation.comparison (termHeader headers symbol)).inv.substitution = _
  rw [Presentation.comparison_inv_substitution, TypeExpr.substitute_identity]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem primitive_at_original_header (headers : HeaderFormation D) (symbol : S.TermSymbol) :
    ((C D).toCwf.tmSub ((data headers).termValue symbol)
      (parameterComparison (termHeader headers symbol)).inv).val =
        QTerm.mk (originalPrimitive headers symbol) := by
  change QTerm.mk ((rawPrimitive headers symbol).reindex
    (Presentation.comparison (termHeader headers symbol)).inv) = _
  apply (QTerm.mk_eq_iff _ _).mpr
  constructor
  · change Holds D (.typeEq (D.termParameters symbol)
      ((D.termResult symbol).substitute
        (Presentation.comparison (termHeader headers symbol)).inv.substitution) (D.termResult symbol))
    rw [Presentation.comparison_inv_substitution, TypeExpr.substitute_identity]
    exact typeEquality_refl (originalResult headers symbol)
  · change Holds D (.termEq (D.termParameters symbol)
      ((.primitive symbol TermExpr.var : TermExpr S _).substitute
        (Presentation.comparison (termHeader headers symbol)).inv.substitution)
      (.primitive symbol TermExpr.var)
      ((D.termResult symbol).substitute
        (Presentation.comparison (termHeader headers symbol)).inv.substitution))
    rw [Presentation.comparison_inv_substitution, TermExpr.substitute_identity, TypeExpr.substitute_identity]
    exact termEquality_refl (originalPrimitive headers symbol)

theorem family_code (headers : HeaderFormation D) (symbol : S.TypeSymbol) :
    (rawFamily headers symbol).code = .family symbol TermExpr.var := rfl

theorem result_code (headers : HeaderFormation D) (symbol : S.TermSymbol) :
    (rawResult headers symbol).code = D.termResult symbol := rfl

theorem primitive_code (headers : HeaderFormation D) (symbol : S.TermSymbol) :
    (rawPrimitive headers symbol).code = .primitive symbol TermExpr.var := rfl

theorem products_substitution (headers : HeaderFormation D) :
    StrictPiSubstitution (data headers).products := Products.substitution

theorem products_beta (headers : HeaderFormation D) :
    PiBeta (data headers).products := Products.beta

theorem products_eta (headers : HeaderFormation D) :
    Mettapedia.TypeTheory.ContextualPiEta.PiEta (data headers).products
      (products_substitution headers).1 := Products.eta

end Mettapedia.TypeTheory.Calculi.NativeDependent.External.Contextual.SyntacticModel
