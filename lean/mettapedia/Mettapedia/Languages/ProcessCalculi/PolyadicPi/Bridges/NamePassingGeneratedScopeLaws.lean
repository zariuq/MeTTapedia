import Mettapedia.Languages.ProcessCalculi.PolyadicPi.BindingClosedBinderExchange
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingContinuationValues

/-!
# Complete scope laws on independently formed continuation arrows

The structural schema laws imply extrusion and exchange for right-hand
private-name abstraction. The comparison with left-hand categorical currying
is earned from the actual exchange, associator and product projections.
Both private positions and the ambient parameter are retained separately.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedScopeLaws

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open CartesianMonoidalCategory
open Mettapedia.OSLF.Binding
open BindingClosedPrimitiveOperations BindingClosedStructuralLaws
open BindingClosedBinaryValues BindingClosedBinderExchange
open Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation (abstraction exchange)
open NamePassingContinuationOperations

universe u v

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C] [MonoidalClosed C]
variable (binding : ClosedPresentation.Operations AllArity.sig C)

theorem fresh_parallel
    (satisfied : binding.model.SchemaFamilySatisfaction AllArity.equations)
    {Z : C} (body : Z ⊗ names binding ⟶ processes binding) (frame : Z ⟶ processes binding) :
    lift (bindFresh (continuation binding) body) frame ≫ (continuation binding).parallel =
      bindFresh (continuation binding)
        (lift body (fst Z (names binding) ≫ frame) ≫ (continuation binding).parallel) := by
  have bodyComparison :
      lift (MonoidalClosed.uncurry (abstraction body)) (snd (names binding) Z ≫ frame) ≫
        (continuation binding).parallel =
      exchange (names binding) Z ≫
        lift body (fst Z (names binding) ≫ frame) ≫ (continuation binding).parallel := by
    unfold abstraction
    rw [MonoidalClosed.uncurry_curry]
    simp [exchange, comp_lift_assoc]
  have derived := private_parallel binding satisfied (abstraction body) frame
  rw [bodyComparison] at derived
  exact derived

def binderOrientation (Z : C) : names binding ⊗ (names binding ⊗ Z) ⟶
    (Z ⊗ names binding) ⊗ names binding :=
  (names binding ◁ exchange (names binding) Z) ≫ exchange (names binding) (Z ⊗ names binding)

def privateExchange (Z : C) : (Z ⊗ names binding) ⊗ names binding ⟶
    (Z ⊗ names binding) ⊗ names binding :=
  lift (lift (fst (Z ⊗ names binding) (names binding) ≫ fst Z (names binding))
    (snd (Z ⊗ names binding) (names binding)))
    (fst (Z ⊗ names binding) (names binding) ≫ snd Z (names binding))

@[reassoc]
theorem privateExchange_parameter (Z : C) :
    privateExchange binding Z ≫ fst (Z ⊗ names binding) (names binding) ≫ fst Z (names binding) =
      fst (Z ⊗ names binding) (names binding) ≫ fst Z (names binding) := by
  simp [privateExchange]

@[reassoc]
theorem privateExchange_newest (Z : C) :
    privateExchange binding Z ≫ snd (Z ⊗ names binding) (names binding) =
      fst (Z ⊗ names binding) (names binding) ≫ snd Z (names binding) := by
  simp [privateExchange]

@[reassoc]
theorem privateExchange_previous (Z : C) :
    privateExchange binding Z ≫ fst (Z ⊗ names binding) (names binding) ≫ snd Z (names binding) =
      snd (Z ⊗ names binding) (names binding) := by
  simp [privateExchange]

theorem privateExchange_involution (Z : C) :
    privateExchange binding Z ≫ privateExchange binding Z =
      𝟙 ((Z ⊗ names binding) ⊗ names binding) := by
  apply hom_ext
  · apply hom_ext <;> simp [privateExchange]
  · simp [privateExchange]

theorem orientation_exchange (Z : C) :
    binderExchange binding Z ≫ binderOrientation binding Z =
      binderOrientation binding Z ≫ privateExchange binding Z := by
  apply hom_ext
  · apply hom_ext <;> simp [binderExchange, binderOrientation, privateExchange, exchange]
  · simp [binderExchange, binderOrientation, privateExchange, exchange]

theorem nested_fresh_comparison {Z : C}
    (body : (Z ⊗ names binding) ⊗ names binding ⟶ processes binding) :
    bindFresh (continuation binding) (bindFresh (continuation binding) body) =
      MonoidalClosed.curry
        (MonoidalClosed.curry (binderOrientation binding Z ≫ body) ≫ (continuation binding).fresh) ≫
          (continuation binding).fresh := by
  unfold bindFresh abstraction binderOrientation
  rw [← Category.assoc, ← MonoidalClosed.curry_natural_left, Category.assoc]
  rfl

theorem fresh_swap
    (satisfied : binding.model.SchemaFamilySatisfaction AllArity.equations)
    {Z : C} (body : (Z ⊗ names binding) ⊗ names binding ⟶ processes binding) :
    bindFresh (continuation binding) (bindFresh (continuation binding) body) =
      bindFresh (continuation binding)
        (bindFresh (continuation binding) (privateExchange binding Z ≫ body)) := by
  rw [nested_fresh_comparison, nested_fresh_comparison]
  have derived := private_swap binding satisfied (binderOrientation binding Z ≫ body)
  rw [← Category.assoc, orientation_exchange, Category.assoc] at derived
  exact derived

theorem parallel_frame_exchange
    (satisfied : binding.model.SchemaFamilySatisfaction AllArity.equations)
    {Z : C} (body declaration message : Z ⟶ processes binding) :
    lift (lift body declaration ≫ (continuation binding).parallel) message ≫ (continuation binding).parallel =
      lift (lift body message ≫ (continuation binding).parallel) declaration ≫ (continuation binding).parallel :=
  (parallel_assoc binding satisfied body declaration message).trans
    ((congrArg (fun pair => lift body pair ≫ (continuation binding).parallel)
      (parallel_comm binding satisfied declaration message)).trans
        (parallel_assoc binding satisfied body message declaration).symm)

/-- Both private scopes retain their own frame, while the complete active
body is exchanged along the actual two-name permutation. -/
theorem nested_parallel_scope
    (satisfied : binding.model.SchemaFamilySatisfaction AllArity.equations)
    {Z : C} (body : (Z ⊗ names binding) ⊗ names binding ⟶ processes binding)
    (firstFrame secondFrame : Z ⊗ names binding ⟶ processes binding) :
    bindFresh (continuation binding)
      (lift (bindFresh (continuation binding)
        (lift body (privateExchange binding Z ≫
          fst (Z ⊗ names binding) (names binding) ≫ secondFrame) ≫
            (continuation binding).parallel)) firstFrame ≫ (continuation binding).parallel) =
    bindFresh (continuation binding)
      (lift (bindFresh (continuation binding)
        (lift (privateExchange binding Z ≫ body)
          (privateExchange binding Z ≫
            fst (Z ⊗ names binding) (names binding) ≫ firstFrame) ≫
              (continuation binding).parallel)) secondFrame ≫ (continuation binding).parallel) := by
  rw [fresh_parallel binding satisfied, fresh_parallel binding satisfied]
  rw [fresh_swap binding satisfied]
  apply congrArg (bindFresh (continuation binding))
  apply congrArg (bindFresh (continuation binding))
  simp only [comp_lift_assoc]
  rw [← Category.assoc, ← Category.assoc, privateExchange_involution]
  erw [Category.id_comp]
  exact parallel_frame_exchange binding satisfied _ _ _

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedScopeLaws
