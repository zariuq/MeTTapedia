import Mettapedia.CategoryTheory.RelativeClosedSyntaxCategory
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Monoidal.Closed.Basic

/-!
# Actual exponentials of the relative generated category

Annotated abstraction descends through the generated curry congruence.
Its inverse evaluates the complete supplied function at the generic argument.
The generated beta and eta equations earn both roundtrips. Substitution
naturality follows from those roundtrips and the actual product projections.

The resulting adjunction supplies a Cartesian closed category. Neither its
exponential objects nor its adjunction laws are assumed in semantic data.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.GeneratedCategory

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory

universe u v a

variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}
variable {signature : Signature (C := C) (symbols := symbols)}

def exponentialObject (argument result : Object signature) : Object signature :=
  ⟨.exponential argument.code result.code,
    ⟨.exponentialObject argument.formed.some result.formed.some⟩⟩

def evaluation (argument result : Object signature) :
    product (exponentialObject argument result) argument ⟶ result :=
  classOf ⟨.evaluation argument.code result.code,
    ⟨.evaluation argument.formed.some result.formed.some⟩⟩

def abstraction {context argument result : Object signature}
    (body : product context argument ⟶ result) : context ⟶ exponentialObject argument result :=
  Quotient.map
    (sa := RawHom.setoid (product context argument) result)
    (sb := RawHom.setoid context (exponentialObject argument result))
    (fun (representative : RawHom (product context argument) result) =>
      (⟨.curry context.code argument.code result.code representative.code,
        ⟨.curry context.formed.some argument.formed.some result.formed.some
          representative.admitted.some⟩⟩ : RawHom context (exponentialObject argument result)))
    (fun _ _ same => ⟨.curryCongruence context.formed.some argument.formed.some
      result.formed.some same.some⟩) body

def unabstract {context argument result : Object signature}
    (function : context ⟶ exponentialObject argument result) : product context argument ⟶ result :=
  pairing (first context argument ≫ function) (second context argument) ≫ evaluation argument result

@[simp] theorem unabstract_abstraction {context argument result : Object signature}
    (body : product context argument ⟶ result) : unabstract (abstraction body) = body := by
  refine Quotient.inductionOn body ?_
  intro representative
  exact Quotient.sound ⟨.exponentialBeta context.formed.some argument.formed.some
    result.formed.some representative.admitted.some⟩

@[simp] theorem abstraction_unabstract {context argument result : Object signature}
    (function : context ⟶ exponentialObject argument result) :
    abstraction (unabstract function) = function := by
  refine Quotient.inductionOn function ?_
  intro representative
  exact Quotient.sound ⟨.exponentialEta context.formed.some argument.formed.some
    result.formed.some representative.admitted.some⟩

def abstractionEquiv (context argument result : Object signature) :
    (product context argument ⟶ result) ≃ (context ⟶ exponentialObject argument result) where
  toFun := abstraction
  invFun := unabstract
  left_inv := unabstract_abstraction
  right_inv := abstraction_unabstract

def productChange {before after : Object signature} (argument : Object signature)
    (change : before ⟶ after) : product before argument ⟶ product after argument :=
  pairing (first before argument ≫ change) (second before argument)

private theorem pairing_first_after {source left right target : Object signature}
    (before : source ⟶ left) (after : source ⟶ right) (outgoing : left ⟶ target) :
    pairing before after ≫ (first left right ≫ outgoing) = before ≫ outgoing := by
  rw [← Category.assoc, pairing_first]

private theorem pairing_second_after {source left right target : Object signature}
    (before : source ⟶ left) (after : source ⟶ right) (outgoing : right ⟶ target) :
    pairing before after ≫ (second left right ≫ outgoing) = after ≫ outgoing := by
  rw [← Category.assoc, pairing_second]

theorem unabstract_precompose {before after argument result : Object signature}
    (change : before ⟶ after) (function : after ⟶ exponentialObject argument result) :
    unabstract (change ≫ function) = productChange argument change ≫ unabstract function := by
  symm
  unfold unabstract
  rw [← Category.assoc, pairing_precompose]
  simp only [productChange, Category.assoc, pairing_first_after, pairing_second]

theorem abstraction_precompose {before after argument result : Object signature}
    (change : before ⟶ after) (body : product after argument ⟶ result) :
    abstraction (productChange argument change ≫ body) = change ≫ abstraction body := by
  apply (abstractionEquiv before argument result).symm.injective
  change unabstract (abstraction (productChange argument change ≫ body)) =
    unabstract (change ≫ abstraction body)
  rw [unabstract_abstraction, unabstract_precompose, unabstract_abstraction]

def exchange (left right : Object signature) : product left right ≅ product right left where
  hom := pairing (second left right) (first left right)
  inv := pairing (second right left) (first right left)
  hom_inv_id := by
    apply product_joint_cancel <;>
      simp only [Category.assoc, pairing_first, pairing_second, Category.id_comp]
  inv_hom_id := by
    apply product_joint_cancel <;>
      simp only [Category.assoc, pairing_first, pairing_second, Category.id_comp]

instance cartesian (signature : Signature (C := C) (symbols := symbols)) :
    CartesianMonoidalCategory (Object signature) :=
  CartesianMonoidalCategory.ofChosenFiniteProducts
    ⟨asEmptyCone (terminal signature), terminalIsTerminal signature⟩
    (fun left right => ⟨BinaryFan.mk (first left right) (second left right), productIsLimit left right⟩)

@[simp] theorem tensor_object (left right : Object signature) :
    left ⊗ right = product left right := rfl

@[simp] theorem tensor_first (left right : Object signature) :
    CartesianMonoidalCategory.fst left right = first left right := rfl

@[simp] theorem tensor_second (left right : Object signature) :
    CartesianMonoidalCategory.snd left right = second left right := rfl

theorem tensorLeft_map {before after : Object signature} (argument : Object signature)
    (change : before ⟶ after) :
    (tensorLeft argument).map change =
      pairing (first argument before) (second argument before ≫ change) := by
  apply product_joint_cancel
  · change (argument ◁ change) ≫ CartesianMonoidalCategory.fst argument after = _
    rw [CartesianMonoidalCategory.whiskerLeft_fst, pairing_first]
    rfl
  · change (argument ◁ change) ≫ CartesianMonoidalCategory.snd argument after = _
    rw [CartesianMonoidalCategory.whiskerLeft_snd, pairing_second]
    rfl

theorem exchange_change {before after : Object signature} (argument : Object signature)
    (change : before ⟶ after) :
    (exchange before argument).hom ≫ (tensorLeft argument).map change =
      productChange argument change ≫ (exchange after argument).hom := by
  rw [tensorLeft_map]
  apply product_joint_cancel <;>
    simp only [Category.assoc, pairing_first, pairing_second, productChange, exchange,
      pairing_second_after]

def exponentialHomEquiv (argument context result : Object signature) :
    (argument ⊗ context ⟶ result) ≃ (context ⟶ exponentialObject argument result) where
  toFun body := abstraction ((exchange context argument).hom ≫ body)
  invFun function := (exchange context argument).inv ≫ unabstract function
  left_inv body := by
    change (exchange context argument).inv ≫
      unabstract (abstraction ((exchange context argument).hom ≫ body)) = body
    rw [unabstract_abstraction, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  right_inv function := by
    change abstraction ((exchange context argument).hom ≫
      ((exchange context argument).inv ≫ unabstract function)) = function
    rw [← Category.assoc, Iso.hom_inv_id, Category.id_comp, abstraction_unabstract]

theorem exponentialHomEquiv_naturality {before after : Object signature}
    (argument result : Object signature) (change : before ⟶ after)
    (body : argument ⊗ after ⟶ result) :
    exponentialHomEquiv argument before result ((tensorLeft argument).map change ≫ body) =
      change ≫ exponentialHomEquiv argument after result body := by
  change abstraction ((exchange before argument).hom ≫
    ((tensorLeft argument).map change ≫ body)) =
      change ≫ abstraction ((exchange after argument).hom ≫ body)
  rw [← Category.assoc, exchange_change, Category.assoc, abstraction_precompose]

def exponential (argument : Object signature) : Object signature ⥤ Object signature :=
  Adjunction.rightAdjointOfEquiv (F := tensorLeft argument)
    (fun context result => exponentialHomEquiv argument context result)
    (fun _ _ result change body => exponentialHomEquiv_naturality argument result change body)

def exponentialAdjunction (argument : Object signature) :
    tensorLeft argument ⊣ exponential argument :=
  Adjunction.adjunctionOfEquivRight (F := tensorLeft argument)
    (fun context result => exponentialHomEquiv argument context result)
    (fun _ _ result change body => exponentialHomEquiv_naturality argument result change body)

instance closed (signature : Signature (C := C) (symbols := symbols)) :
    MonoidalClosed (Object signature) where
  closed argument := ⟨exponential argument, exponentialAdjunction argument⟩

set_option backward.isDefEq.respectTransparency false in
theorem exponentialAdjunction_readout (argument context result : Object signature)
    (body : argument ⊗ context ⟶ result) :
    (exponentialAdjunction argument).homEquiv context result body =
      abstraction ((exchange context argument).hom ≫ body) := by
  simp only [exponentialAdjunction, Adjunction.adjunctionOfEquivRight,
    Adjunction.mkOfHomEquiv_homEquiv]
  rfl

end Mettapedia.CategoryTheory.RelativeClosedSyntax.GeneratedCategory
