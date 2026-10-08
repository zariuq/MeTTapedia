import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementContextualInterpretation

/-!
# The semantic functor of generated refinement substitutions

Actual evaluated identities and composites earn a context functor. Typed
substitution-equation soundness earns its descent to the authored arrow
quotient, including the guards of every assumption position.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Interpretation

open _root_.CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Refinement.Abstract

universe u c s t m p
variable {S : Symbols.{u}} {D : Signature S} {C : CwfWithTerminal.{c, s, t, m}}
variable (model : QualifiedModel.{u,c,s,t,m,p} D C)

theorem rawArrow_id (context : Context D) :
    rawArrow model (𝟙 context) = C.toCwf.idS (contextValue model context).1 :=
  Abstract.Derivation.substitutionArrow_unique model.data model.realization
    model.products_substitution model.products_beta model.products_eta (Classical.choice (𝟙 context : context ⟶ context).admitted)
      _ _ (context_readout model context) (context_readout model context) _
        (model.data.evaluateSubstitution_identity (contextValue model context))

theorem rawArrow_comp {source middle target : Context D}
    (earlier : source ⟶ middle) (later : middle ⟶ target) :
    rawArrow model (earlier ≫ later) = C.toCwf.compS (rawArrow model later) (rawArrow model earlier) :=
  Abstract.Derivation.substitutionArrow_unique model.data model.realization
    model.products_substitution model.products_beta model.products_eta (Classical.choice (earlier ≫ later).admitted)
      _ _ (context_readout model source) (context_readout model target) _
        (model.data.evaluateSubstitution_composition model.products_substitution _ _ _
          later.substitution earlier.substitution (rawArrow model later) (rawArrow model earlier)
            (arrow_readout model later) (arrow_readout model earlier))

noncomputable def rawFunctor : Context D ⥤ C.toCwf.base.Context where
  obj context := ⟨(contextValue model context).1⟩
  map morphism := rawArrow model morphism
  map_id := rawArrow_id model
  map_comp := rawArrow_comp model

/-- Typed equation soundness earns categorical descent to the authored arrow
quotient, rather than assuming that the parser factors through it. -/
noncomputable def quotientFunctor : quotientContext D ⥤ C.toCwf.base.Context :=
  _root_.CategoryTheory.Quotient.lift (homEquality D) (rawFunctor model)
    (fun _ _ _ _ same => rawArrow_congruent model same)

@[simp] theorem quotientFunctor_object (context : quotientContext D) :
    (quotientFunctor model).obj context = ⟨(contextValue model context.as).1⟩ := rfl

@[simp] theorem quotientFunctor_project {source target : Context D} (morphism : source ⟶ target) :
    (quotientFunctor model).map ((quotientProjection D).map morphism) = rawArrow model morphism := rfl


end Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Contextual.Interpretation
