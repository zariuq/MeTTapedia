import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSyntax
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementModelScope
import Mettapedia.TypeTheory.NativeLocalSumElimination
import Mettapedia.TypeTheory.NativeLocalPiEta
import Mettapedia.GSLT.Topos.PresheafPredicateHeyting

/-!
# Independent meanings for native refinement declarations

Primitive types, terms and predicates receive actual mixed semantic
parameter scopes and independent meanings. The logical operations are the
native presheaf constructions over the supplied small world category.
Agreement with raw declaration headers is a separate local obligation.
No generated-judgment soundness theorem is a field of these data.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

open _root_.CategoryTheory
open NativeLocalTypeFormers
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualSumComprehension

universe u v
variable (S : Symbols.{v}) (C : Type u) [Category.{u} C]

structure ModelData where
  typeParameters : (symbol : S.TypeSymbol) → Scope C (S.typeArity symbol)
  typeFamily : (symbol : S.TypeSymbol) → NativeType (typeParameters symbol).1
  termParameters : (symbol : S.TermSymbol) → Scope C (S.termArity symbol)
  termType : (symbol : S.TermSymbol) → NativeType (termParameters symbol).1
  termValue : (symbol : S.TermSymbol) → (termType symbol).decoded.sections
  predicateParameters : (symbol : S.PredicateSymbol) → Scope C (S.predicateArity symbol)
  predicateValue : (symbol : S.PredicateSymbol) → Subfunctor (predicateParameters symbol).1

namespace ModelData

variable {S C}

noncomputable def products (_model : ModelData S C) : PiOperations (NativeModel C).toCwf :=
  NativeLocalTypeOperations.products C

noncomputable def sums (_model : ModelData S C) : StableSums (NativeModel C).toCwf :=
  NativeLocalSumElimination.stableSums C

def familyAt (model : ModelData S C) {P : Cᵒᵖ ⥤ Type u} (symbol : S.TypeSymbol)
    (arguments : P ⟶ (model.typeParameters symbol).1) : NativeType P :=
  (model.typeFamily symbol).reindex arguments

def primitiveAt (model : ModelData S C) {P : Cᵒᵖ ⥤ Type u} (symbol : S.TermSymbol)
    (arguments : P ⟶ (model.termParameters symbol).1) : NativeValue P :=
  Value.substitute (K := (NativeModel C).toCwf)
    ⟨model.termType symbol, model.termValue symbol⟩ arguments

def predicateAt (model : ModelData S C) {P : Cᵒᵖ ⥤ Type u} (symbol : S.PredicateSymbol)
    (arguments : P ⟶ (model.predicateParameters symbol).1) : Subfunctor P :=
  (model.predicateValue symbol).preimage arguments

theorem familyAt_substitution (model : ModelData S C) {P Q : Cᵒᵖ ⥤ Type u}
    (symbol : S.TypeSymbol) (arguments : P ⟶ (model.typeParameters symbol).1)
    (σ : Q ⟶ P) :
    (model.familyAt symbol arguments).reindex σ = model.familyAt symbol (σ ≫ arguments) :=
  ((NativeModel C).toCwf.tySub_comp _ _ _).symm

theorem primitiveAt_substitution (model : ModelData S C) {P Q : Cᵒᵖ ⥤ Type u}
    (symbol : S.TermSymbol) (arguments : P ⟶ (model.termParameters symbol).1)
    (σ : Q ⟶ P) :
    Value.substitute (K := (NativeModel C).toCwf) (model.primitiveAt symbol arguments) σ =
      model.primitiveAt symbol (σ ≫ arguments) :=
  (Value.substitute_composition (K := (NativeModel C).toCwf)
    ⟨_, model.termValue symbol⟩ arguments σ).symm

theorem predicateAt_substitution (model : ModelData S C) {P Q : Cᵒᵖ ⥤ Type u}
    (symbol : S.PredicateSymbol) (arguments : P ⟶ (model.predicateParameters symbol).1)
    (σ : Q ⟶ P) :
    (model.predicateAt symbol arguments).preimage σ =
      model.predicateAt symbol (σ ≫ arguments) :=
  ((model.predicateValue symbol).preimage_comp σ arguments).symm

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
