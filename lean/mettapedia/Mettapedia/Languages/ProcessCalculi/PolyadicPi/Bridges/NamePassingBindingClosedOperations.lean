import Mettapedia.OSLF.Syntax.BindingClosedContextSemantics
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingContinuationOperations
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingConstructorInterpretation

/-!
# Continuation primitives as genuine generated binding operation data

The ordered function-argument domains of the independent binding signature
are retained. Empty-binder functions are evaluated at the actual unit value;
one-name functions are precomposed with the inverse right unitor. These
canonical arrows convert the declared arity domains to the independently
formed continuation constructor domains.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedOperations

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus
open NamePassingContinuationOperations

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]

/-- Evaluation of a complete function on the empty binder context. -/
def emptyValue (X : C) : (ihom (𝟙_ C)).obj X ⟶ X :=
  (λ_ ((ihom (𝟙_ C)).obj X)).inv ≫ (ihom.ev (𝟙_ C)).app X

/-- The full one-name body is precomposed with the actual unit insertion. -/
def boundValue (primitives : Operations C) :
    (ihom (primitives.names ⊗ 𝟙_ C)).obj primitives.termObject ⟶ primitives.boundBodyObject :=
  (MonoidalClosed.pre (ρ_ primitives.names).inv).app primitives.termObject

def generated (primitives : Operations C) : ClosedPresentation.Operations NamePassing.Presentation.signature C where
  sort := NamePassingConstructorInterpretation.sortValue primitives
  operation := fun {result} operator => match result, operator with
    | .tm, .reference => fst _ _ ≫ emptyValue primitives.names ≫ primitives.reference
    | .tm, .abstraction => fst _ _ ≫ boundValue primitives ≫ primitives.abstraction
    | .tm, .application =>
        lift (fst _ _ ≫ emptyValue primitives.termObject)
          (snd _ _ ≫ fst _ _ ≫ emptyValue primitives.names) ≫ primitives.application
    | .tm, .definition =>
        lift (fst _ _ ≫ emptyValue primitives.termObject)
          (snd _ _ ≫ fst _ _ ≫ boundValue primitives) ≫ primitives.definition
    | .tm, .carrier =>
        lift (fst _ _ ≫ emptyValue primitives.names)
          (lift (snd _ _ ≫ fst _ _ ≫ emptyValue primitives.termObject)
            (snd _ _ ≫ snd _ _ ≫ fst _ _ ≫ emptyValue primitives.termObject)) ≫ primitives.carrier

/-- Evaluation at the actual unit recovers the supplied whole arrow. -/
theorem empty_curry {Z X : C} (body : Z ⟶ X) :
    MonoidalClosed.curry (snd (𝟙_ C) Z ≫ body) ≫ emptyValue X = body := by
  unfold emptyValue
  rw [← Category.assoc, leftUnitor_inv_naturality, Category.assoc,
    MonoidalClosed.whiskerLeft_curry_ihom_ev_app]
  rw [← Category.assoc, ← leftUnitor_hom, Iso.inv_hom_id, Category.id_comp]

theorem context_value (primitives : Operations C) (context : Ctx NamePassing.Presentation.signature) :
    (generated primitives).context context = NamePassingConstructorInterpretation.contextValue primitives context := by
  induction context with
  | nil => rfl
  | cons sort context ih => exact congrArg (fun rest => NamePassingConstructorInterpretation.sortValue primitives sort ⊗ rest) ih

omit [MonoidalClosed C] in
theorem exchange_twice (first second : C) :
    Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.exchange first second ≫
      Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.exchange second first = 𝟙 (first ⊗ second) := by
  apply hom_ext <;> simp [Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.exchange]

theorem boundMeaning_curry (primitives : Operations C) {context : Ctx NamePassing.Presentation.signature}
    (body : primitives.names ⊗ NamePassingConstructorInterpretation.contextValue primitives context ⟶ primitives.termObject) :
    NamePassingConstructorInterpretation.boundMeaning primitives body = MonoidalClosed.curry body := by
  unfold NamePassingConstructorInterpretation.boundMeaning
    Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation.abstraction
  rw [← Category.assoc, exchange_twice, Category.id_comp]

theorem append_single (primitives : Operations C) (context : Ctx NamePassing.Presentation.signature) :
    (ρ_ primitives.names).inv ▷ (generated primitives).context context ≫
      (generated primitives).appendContext [.nm] context = 𝟙 (primitives.names ⊗ (generated primitives).context context) := by
  let Z := (generated primitives).context context
  change (ρ_ primitives.names).inv ▷ Z ≫
    lift (fst (primitives.names ⊗ 𝟙_ C) Z ≫ fst primitives.names (𝟙_ C))
      (lift (fst (primitives.names ⊗ 𝟙_ C) Z ≫ snd primitives.names (𝟙_ C))
        (snd (primitives.names ⊗ 𝟙_ C) Z) ≫ snd (𝟙_ C) Z) = 𝟙 (primitives.names ⊗ Z)
  apply hom_ext <;> simp

/-- The generated one-name binder supplies the same complete bound
continuation arrow, by actual currying and unit comparison laws. -/
theorem bound_curry (primitives : Operations C) {context : Ctx NamePassing.Presentation.signature}
    (body : (generated primitives).context (.nm :: context) ⟶ primitives.termObject) :
    MonoidalClosed.curry ((generated primitives).appendContext [.nm] context ≫ body) ≫ boundValue primitives =
      MonoidalClosed.curry body := by
  unfold boundValue
  rw [MonoidalClosed.curry_pre_app, ← Category.assoc, append_single, Category.id_comp]

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBindingClosedOperations
