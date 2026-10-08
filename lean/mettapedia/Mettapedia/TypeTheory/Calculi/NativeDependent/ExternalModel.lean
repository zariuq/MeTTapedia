import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalSyntax
import Mettapedia.TypeTheory.ContextualModelTelescopes
import Mettapedia.TypeTheory.ContextualSumComprehension

/-!
# Independent dependent models for external syntax

Primitive declarations have actual semantic parameter telescopes and typed
meanings. These data and the local dependent operations do not include a
soundness theorem, a source evaluator, or a declaration-formation assumption.
Agreement with authored declaration headers is a separate interpretation
obligation.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualSumComprehension

universe u c s t m

variable (S : Symbols.{u}) (C : CwfWithTerminal.{c, s, t, m})

/-- Independent primitive meanings and actual dependent operations. -/
structure ModelData where
  products : PiOperations C.toCwf
  sums : StableSums C.toCwf
  typeParameters : (symbol : S.TypeSymbol) → Context C (S.typeArity symbol)
  typeFamily : (symbol : S.TypeSymbol) → C.toCwf.Ty (typeParameters symbol).1
  termParameters : (symbol : S.TermSymbol) → Context C (S.termArity symbol)
  termType : (symbol : S.TermSymbol) → C.toCwf.Ty (termParameters symbol).1
  termValue : (symbol : S.TermSymbol) → C.toCwf.Tm (termParameters symbol).1 (termType symbol)

namespace ModelData

variable {S C}

/-- A family receives an actual model substitution into its declared
parameter telescope. -/
def familyAt (model : ModelData S C) {Γ : C.toCwf.Ctx} (symbol : S.TypeSymbol)
    (arguments : C.toCwf.Sub Γ (model.typeParameters symbol).1) : C.toCwf.Ty Γ :=
  C.toCwf.tySub (model.typeFamily symbol) arguments

/-- Primitive term evaluation retains the supplied semantic section. -/
def primitiveAt (model : ModelData S C) {Γ : C.toCwf.Ctx} (symbol : S.TermSymbol)
    (arguments : C.toCwf.Sub Γ (model.termParameters symbol).1) : Value C.toCwf Γ :=
  ⟨C.toCwf.tySub (model.termType symbol) arguments,
    C.toCwf.tmSub (model.termValue symbol) arguments⟩

theorem familyAt_substitution (model : ModelData S C) {Γ Δ : C.toCwf.Ctx}
    (symbol : S.TypeSymbol) (arguments : C.toCwf.Sub Γ (model.typeParameters symbol).1)
    (σ : C.toCwf.Sub Δ Γ) :
    C.toCwf.tySub (model.familyAt symbol arguments) σ =
      model.familyAt symbol (C.toCwf.compS arguments σ) :=
  (C.toCwf.tySub_comp _ _ _).symm

theorem primitiveAt_substitution (model : ModelData S C) {Γ Δ : C.toCwf.Ctx}
    (symbol : S.TermSymbol) (arguments : C.toCwf.Sub Γ (model.termParameters symbol).1)
    (σ : C.toCwf.Sub Δ Γ) :
    (model.primitiveAt symbol arguments).substitute σ =
      model.primitiveAt symbol (C.toCwf.compS arguments σ) :=
  (Value.substitute_composition ⟨_, model.termValue symbol⟩ arguments σ).symm

end ModelData

end Mettapedia.TypeTheory.Calculi.NativeDependent.External
