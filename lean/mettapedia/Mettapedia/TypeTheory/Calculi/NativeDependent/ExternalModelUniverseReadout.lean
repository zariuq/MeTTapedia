import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalModelUniverseCommutation
import Mettapedia.TypeTheory.Calculi.NativeDependent.ExternalContextualInterpretation

/-!
# Declaration and generated-certificate readouts at lifted sizes

Successful authored contexts and substitutions retain their exact telescope
and arrow. Primitive header realization and the local product equations
qualify the lifted model. Generated section extraction then returns the
original supplied section, independently of either certificate tree.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.External

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualModelTelescopes
open Mettapedia.TypeTheory.ContextualCwfUniverseLift
open Mettapedia.TypeTheory.ContextualTypeOperations
open Mettapedia.TypeTheory.ContextualPiEta

universe u c s t m uc vs wt ms
variable {S : Symbols.{u}} {C : CwfWithTerminal.{c, s, t, m}} {D : Signature S}

namespace ModelData

theorem evaluateContext_universeLift (model : ModelData S C) :
    {n : Nat} → (raw : ContextExpr S n) → (Γ : Context C n) →
    model.evaluateContext raw = some Γ →
    (model.universeLift.{u, c, s, t, m, uc, vs, wt, ms} : ModelData S (liftWithTerminal.{c, s, t, m, uc, vs, wt, ms} C)).evaluateContext
      raw = some (liftContext.{c, s, t, m, uc, vs, wt, ms} Γ)
  | _, .nil, Γ, evaluated => by
      have actual : Context.nil C = Γ := Option.some.inj evaluated
      rw [← actual]
      rfl
  | _, .snoc previous type, Γ, evaluated => by
      rw [evaluateContext] at evaluated
      rcases (bindResult_eq_some_iff _ _ _).mp evaluated with ⟨earlier, earlierRead, rest⟩
      rcases (bindResult_eq_some_iff _ _ _).mp rest with ⟨A, typeRead, last⟩
      rw [← Option.some.inj last]
      exact model.universeLift.evaluateContext_snoc previous type (liftContext.{c, s, t, m, uc, vs, wt, ms} earlier) (ULift.up A)
        (evaluateContext_universeLift model previous earlier earlierRead)
        (model.evaluateType_universeLift type earlier A typeRead)

theorem evaluateSubstitution_universeLift (model : ModelData S C) {n k : Nat}
    (Γ : Context C n) (Δ : Context C k) (substitution : Substitution S k n)
    (σ : C.toCwf.Sub Γ.1 Δ.1) (evaluated : model.evaluateSubstitution Γ Δ substitution = some σ) :
    (model.universeLift.{u, c, s, t, m, uc, vs, wt, ms} : ModelData S (liftWithTerminal.{c, s, t, m, uc, vs, wt, ms} C)).evaluateSubstitution
      (liftContext.{c, s, t, m, uc, vs, wt, ms} Γ) (liftContext.{c, s, t, m, uc, vs, wt, ms} Δ) substitution = some (ULift.up σ) := by
  apply (model.universeLift.evaluateSubstitution_eq_some_iff _ _ _ _).mpr
  intro index
  have read := (model.evaluateSubstitution_eq_some_iff _ _ _ _).mp evaluated index
  exact (model.evaluateTerm_universeLift (substitution index) Γ _ read).trans
    (congrArg some (liftTelescope_components.{c, s, t, m, uc, vs, wt, ms} Δ.2 σ index).symm)

/-- All four carriers use the same sufficiently large external level. -/
abbrev commonUniverseLift (model : ModelData S C) :
    ModelData S (commonLiftWithTerminal.{c, s, t, m, uc} C) :=
  model.universeLift.{u, c, s, t, m, max c s t m uc, max c s t m uc,
    max c s t m uc, max c s t m uc}

end ModelData

namespace SignatureRealization

theorem universeLift {model : ModelData S C} (realization : SignatureRealization model D) :
    SignatureRealization
      (model.universeLift.{u, c, s, t, m, uc, vs, wt, ms} : ModelData S (liftWithTerminal.{c, s, t, m, uc, vs, wt, ms} C)) D where
  typeHeader symbol := model.evaluateContext_universeLift _ _ (realization.typeHeader symbol)
  termHeader symbol := model.evaluateContext_universeLift _ _ (realization.termHeader symbol)
  termResult symbol := model.evaluateType_universeLift _ _ _ (realization.termResult symbol)

end SignatureRealization

namespace Contextual.Interpretation.QualifiedModel

def universeLift (model : Contextual.Interpretation.QualifiedModel D C) :
    Contextual.Interpretation.QualifiedModel D (liftWithTerminal.{c, s, t, m, uc, vs, wt, ms} C) where
  data := model.data.universeLift.{u, c, s, t, m, uc, vs, wt, ms}
  realization := model.realization.universeLift.{u, c, s, t, m, uc, vs, wt, ms}
  products_substitution := lifted_products_substitution model.data.products model.products_substitution
  products_beta := lifted_products_beta model.data.products model.products_beta
  products_eta := lifted_products_eta model.data.products model.products_substitution.1 model.products_eta

abbrev commonUniverseLift (model : Contextual.Interpretation.QualifiedModel D C) :
    Contextual.Interpretation.QualifiedModel D (commonLiftWithTerminal.{c, s, t, m, uc} C) :=
  model.universeLift.{u, c, s, t, m, max c s t m uc, max c s t m uc,
    max c s t m uc, max c s t m uc}

end Contextual.Interpretation.QualifiedModel

namespace Contextual.Interpretation

theorem contextValue_universeLift (model : QualifiedModel D C) (context : Contextual.Context D) :
    contextValue (model.universeLift : QualifiedModel D
      (liftWithTerminal.{c, s, t, m, uc, vs, wt, ms} C)) context =
      liftContext.{c, s, t, m, uc, vs, wt, ms} (contextValue model context) :=
  Option.some.inj ((context_readout model.universeLift context).symm.trans
    (model.data.evaluateContext_universeLift context.raw (contextValue model context)
      (context_readout model context)))

end Contextual.Interpretation

namespace Derivation

theorem termSection_universeLift
    (model : Contextual.Interpretation.QualifiedModel D C) {n : Nat}
    {raw : ContextExpr S n} {term : TermExpr S n} {type : TypeExpr S n}
    (first second : Derivation D (.term raw term type))
    (Γ : Context C n) (A : C.toCwf.Ty Γ.1)
    (contextRead : model.data.evaluateContext raw = some Γ)
    (typeRead : model.data.evaluateType Γ type = some A) :
    (second.termSection
      (model.universeLift.{u, c, s, t, m, uc, vs, wt, ms} : Contextual.Interpretation.QualifiedModel D
        (liftWithTerminal.{c, s, t, m, uc, vs, wt, ms} C)).data
      model.universeLift.realization model.universeLift.products_substitution
      model.universeLift.products_beta model.universeLift.products_eta
      (liftContext.{c, s, t, m, uc, vs, wt, ms} Γ) (ULift.up A)
      (model.data.evaluateContext_universeLift raw Γ contextRead)
      (model.data.evaluateType_universeLift type Γ A typeRead)).down =
      first.termSection model.data model.realization model.products_substitution
        model.products_beta model.products_eta Γ A contextRead typeRead := by
  have read := model.data.evaluateTerm_universeLift term Γ _
    (first.termSection_readout model.data model.realization model.products_substitution
      model.products_beta model.products_eta Γ A contextRead typeRead)
  have exactSection := second.termSection_unique model.universeLift.data model.universeLift.realization
    model.universeLift.products_substitution model.universeLift.products_beta model.universeLift.products_eta
    (liftContext.{c, s, t, m, uc, vs, wt, ms} Γ) (ULift.up A)
    (model.data.evaluateContext_universeLift raw Γ contextRead)
    (model.data.evaluateType_universeLift type Γ A typeRead) _ read
  exact congrArg ULift.down exactSection

end Derivation
end Mettapedia.TypeTheory.Calculi.NativeDependent.External
