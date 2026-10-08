import Mettapedia.TypeTheory.WiderPresheafDependentFunctions
import Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassPresheafProducts

/-!
# Constructed type-former maps from dependent signature equivalences

Shape and dependent-position maps retain their typed endpoints. From these
maps, dependent sums and full future dependent functions acquire actual
inverse transformations. The context, shape, position and consumer universes
are independent. No product equivalence or type-former law is supplied as
input, and no fibre inverse is selected from propositional surjectivity.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.WiderPresheafSignatureEquivalence

open CategoryTheory WiderPresheafDependentFunctions
open MaterialSets.Hypersets

universe u v w z h k
variable {E : Type v} [Category.{u} E]
variable {shape : E ⥤ Type w} {nextShape : E ⥤ Type h}
variable {position : shape.Elements ⥤ Type z} {nextPosition : nextShape.Elements ⥤ Type k}

structure Signature where
  shapes : (point : E) → shape.obj point ≃ nextShape.obj point
  shape_natural : ∀ {first second : E} (step : first ⟶ second) (label : shape.obj first),
    shapes second (shape.map step label) = nextShape.map step (shapes first label)
  positions : (point : E) → (label : shape.obj point) →
    position.obj ⟨point, label⟩ ≃ nextPosition.obj ⟨point, shapes point label⟩
  position_natural : ∀ {first second : E} (step : first ⟶ second) (label : shape.obj first)
    (value : position.obj ⟨first, label⟩),
    HEq (positions second (shape.map step label) (position.map (argumentMap shape step label) value))
      (nextPosition.map (argumentMap nextShape step (shapes first label)) (positions first label value))

variable (signature : Signature (shape := shape) (nextShape := nextShape)
  (position := position) (nextPosition := nextPosition))

theorem positions_heq {point : E} {first second : shape.obj point} (same : first = second)
    (left : position.obj ⟨point, first⟩) (right : position.obj ⟨point, second⟩) (values : HEq left right) :
    HEq (signature.positions point first left) (signature.positions point second right) := by
  cases same
  cases eq_of_heq values
  rfl

private def equalityEquiv {A B : Type k} (same : A = B) : A ≃ B := by
  cases same
  exact Equiv.refl A

private theorem equalityEquiv_value {A B : Type k} (same : A = B) (value : A) :
    HEq (equalityEquiv same value) value := by
  cases same
  rfl

def positionsAtNew (point : E) (label : nextShape.obj point) :
    position.obj ⟨point, (signature.shapes point).symm label⟩ ≃ nextPosition.obj ⟨point, label⟩ :=
  (signature.positions point ((signature.shapes point).symm label)).trans
    (equalityEquiv (congrArg (fun value => nextPosition.obj ⟨point, value⟩)
      ((signature.shapes point).apply_symm_apply label)))

theorem positionsAtNew_heq (point : E) (label : nextShape.obj point)
    (value : position.obj ⟨point, (signature.shapes point).symm label⟩) :
    HEq (positionsAtNew signature point label value)
      (signature.positions point ((signature.shapes point).symm label) value) :=
  equalityEquiv_value _ _

def piApply {point : E} (function : DependentSection shape position point)
    (future : E) (arrival : point ⟶ future) (label : nextShape.obj future) : nextPosition.obj ⟨future, label⟩ :=
  positionsAtNew signature future label
    (function.app future arrival ((signature.shapes future).symm label))

theorem piApply_on_shape {point : E} (function : DependentSection shape position point)
    (future : E) (arrival : point ⟶ future) (label : shape.obj future) :
    piApply signature function future arrival (signature.shapes future label) =
      signature.positions future label (function.app future arrival label) := by
  apply eq_of_heq
  exact (equalityEquiv_value _ _).trans
    (positions_heq signature ((signature.shapes future).symm_apply_apply label) _ _
      (DependentSection.app_heq shape position function rfl arrival arrival HEq.rfl _ _
        (heq_of_eq ((signature.shapes future).symm_apply_apply label))))

theorem piApply_labels_heq {point : E} (function : DependentSection shape position point)
    (future : E) (arrival : point ⟶ future) {first second : nextShape.obj future} (same : first = second) :
    HEq (piApply signature function future arrival first) (piApply signature function future arrival second) := by
  cases same
  rfl

theorem piApply_natural {point first second : E} (function : DependentSection shape position point)
    (step : first ⟶ second) (arrival : point ⟶ first) (label : nextShape.obj first) :
    nextPosition.map (argumentMap nextShape step label) (piApply signature function first arrival label) =
      piApply signature function second (arrival ≫ step) (nextShape.map step label) := by
  obtain ⟨original, rfl⟩ := (signature.shapes first).surjective label
  apply eq_of_heq
  have start := piApply_on_shape signature function first arrival original
  have moved := congrArg (signature.positions second (shape.map step original))
    (function.naturality step arrival original)
  have finish := piApply_on_shape signature function second (arrival ≫ step) (shape.map step original)
  exact (heq_of_eq (congrArg (nextPosition.map (argumentMap nextShape step (signature.shapes first original))) start)).trans
    ((signature.position_natural step original (function.app first arrival original)).symm.trans
      ((heq_of_eq moved).trans ((heq_of_eq finish.symm).trans
        (piApply_labels_heq signature function second (arrival ≫ step) (signature.shape_natural step original)))))

def piValue {point : E} (function : DependentSection shape position point) :
    DependentSection nextShape nextPosition point where
  app := piApply signature function
  naturality step arrival label := piApply_natural signature function step arrival label

def inversePiApply {point : E} (function : DependentSection nextShape nextPosition point)
    (future : E) (arrival : point ⟶ future) (label : shape.obj future) : position.obj ⟨future, label⟩ :=
  (signature.positions future label).symm (function.app future arrival (signature.shapes future label))

theorem inversePiApply_natural {point first second : E}
    (function : DependentSection nextShape nextPosition point)
    (step : first ⟶ second) (arrival : point ⟶ first) (label : shape.obj first) :
    position.map (argumentMap shape step label) (inversePiApply signature function first arrival label) =
      inversePiApply signature function second (arrival ≫ step) (shape.map step label) := by
  apply (signature.positions second (shape.map step label)).injective
  apply eq_of_heq
  have firstInv := (signature.positions first label).apply_symm_apply
    (function.app first arrival (signature.shapes first label))
  have secondInv := (signature.positions second (shape.map step label)).apply_symm_apply
    (function.app second (arrival ≫ step) (signature.shapes second (shape.map step label)))
  exact (signature.position_natural step label (inversePiApply signature function first arrival label)).trans
    ((heq_of_eq (congrArg (nextPosition.map (argumentMap nextShape step (signature.shapes first label))) firstInv)).trans
      ((heq_of_eq (function.naturality step arrival (signature.shapes first label))).trans
        ((DependentSection.app_heq nextShape nextPosition function rfl _ _ HEq.rfl _ _ (heq_of_eq (signature.shape_natural step label).symm)).trans
          (heq_of_eq secondInv.symm))))

def inversePiValue {point : E} (function : DependentSection nextShape nextPosition point) :
    DependentSection shape position point where
  app := inversePiApply signature function
  naturality step arrival label := inversePiApply_natural signature function step arrival label

theorem inverse_forward {point : E} (function : DependentSection shape position point) :
    inversePiValue signature (piValue signature function) = function := by
  apply DependentSection.ext
  intro future arrival label
  exact (congrArg (signature.positions future label).symm
    (piApply_on_shape signature function future arrival label)).trans
      ((signature.positions future label).symm_apply_apply (function.app future arrival label))

theorem forward_inverse {point : E} (function : DependentSection nextShape nextPosition point) :
    piValue signature (inversePiValue signature function) = function := by
  apply DependentSection.ext
  intro future arrival label
  obtain ⟨original, rfl⟩ := (signature.shapes future).surjective label
  exact (piApply_on_shape signature (inversePiValue signature function) future arrival original).trans
    ((signature.positions future original).apply_symm_apply (function.app future arrival (signature.shapes future original)))

def piEquiv (point : E) : DependentSection shape position point ≃ DependentSection nextShape nextPosition point where
  toFun := piValue signature
  invFun := inversePiValue signature
  left_inv := inverse_forward signature
  right_inv := forward_inverse signature

def piForward : Hom (dependentFunctions shape position) (dependentFunctions nextShape nextPosition) where
  app _ function := piValue signature function
  naturality _ _ := by
    apply DependentSection.ext
    intro _ _ _
    rfl

def piBackward : Hom (dependentFunctions nextShape nextPosition) (dependentFunctions shape position) where
  app _ function := inversePiValue signature function
  naturality _ _ := by
    apply DependentSection.ext
    intro _ _ _
    rfl

theorem pi_forward_backward : (piForward signature).comp (piBackward signature) = Hom.identity _ := by
  apply Hom.ext
  intro _ function
  exact inverse_forward signature function

theorem pi_backward_forward : (piBackward signature).comp (piForward signature) = Hom.identity _ := by
  apply Hom.ext
  intro _ function
  exact forward_inverse signature function

def piSections : (dependentFunctions shape position).sections ≃ (dependentFunctions nextShape nextPosition).sections where
  toFun := (piForward signature).mapSection
  invFun := (piBackward signature).mapSection
  left_inv term := by
    apply Subtype.ext
    funext point
    exact inverse_forward signature (term.val point)
  right_inv term := by
    apply Subtype.ext
    funext point
    exact forward_inverse signature (term.val point)

def sigmaValue (point : E) (term : Σ label : shape.obj point, position.obj ⟨point, label⟩) :
    Σ label : nextShape.obj point, nextPosition.obj ⟨point, label⟩ :=
  ⟨signature.shapes point term.1, signature.positions point term.1 term.2⟩

def inverseSigmaValue (point : E)
    (term : Σ label : nextShape.obj point, nextPosition.obj ⟨point, label⟩) :
    Σ label : shape.obj point, position.obj ⟨point, label⟩ :=
  ⟨(signature.shapes point).symm term.1, (positionsAtNew signature point term.1).symm term.2⟩

theorem sigmaValue_injective (point : E) : Function.Injective (sigmaValue signature point) := by
  rintro ⟨first, left⟩ ⟨second, right⟩ same
  have labels := (signature.shapes point).injective (congrArg Sigma.fst same)
  cases labels
  have values : signature.positions point first left = signature.positions point first right :=
    eq_of_heq (Sigma.mk.inj same).2
  exact congrArg (Sigma.mk first) ((signature.positions point first).injective values)

theorem sigmaValue_inverse (point : E)
    (term : Σ label : nextShape.obj point, nextPosition.obj ⟨point, label⟩) :
    sigmaValue signature point (inverseSigmaValue signature point term) = term := by
  refine Sigma.ext ((signature.shapes point).apply_symm_apply term.1) ?_
  exact (positionsAtNew_heq signature point term.1
    ((positionsAtNew signature point term.1).symm term.2)).symm.trans
    (heq_of_eq ((positionsAtNew signature point term.1).apply_symm_apply term.2))

theorem inverse_sigmaValue (point : E)
    (term : Σ label : shape.obj point, position.obj ⟨point, label⟩) :
    inverseSigmaValue signature point (sigmaValue signature point term) = term :=
  sigmaValue_injective signature point (sigmaValue_inverse signature point (sigmaValue signature point term))

def sigmaEquiv (point : E) : (Σ label : shape.obj point, position.obj ⟨point, label⟩) ≃
    (Σ label : nextShape.obj point, nextPosition.obj ⟨point, label⟩) where
  toFun := sigmaValue signature point
  invFun := inverseSigmaValue signature point
  left_inv := inverse_sigmaValue signature point
  right_inv := sigmaValue_inverse signature point

private theorem sigmaMap_heq {A : E ⥤ Type w} (B : A.Elements ⥤ Type z)
    {first second other : A.Elements} (same : second = other)
    (left : first ⟶ second) (right : first ⟶ other) (sameArrow : HEq left.1 right.1)
    (member : B.obj first) : HEq (B.map left member) (B.map right member) := by
  cases same
  have arrows : left = right := Subtype.ext (eq_of_heq sameArrow)
  cases arrows
  rfl

def sigmaFamily (A : E ⥤ Type w) (B : A.Elements ⥤ Type z) : E ⥤ Type (max w z) where
  obj point := Σ label : A.obj point, B.obj ⟨point, label⟩
  map step := TypeCat.ofHom fun term => ⟨A.map step term.1, B.map (argumentMap A step term.1) term.2⟩
  map_id point := by
    apply ConcreteCategory.hom_ext
    rintro ⟨label, value⟩
    apply Sigma.ext (A.map_id_apply point label)
    have target : (⟨point, A.map (𝟙 point) label⟩ : A.Elements) = ⟨point, label⟩ :=
      Sigma.ext rfl (heq_of_eq (A.map_id_apply point label))
    exact (sigmaMap_heq B target (argumentMap A (𝟙 point) label) (𝟙 _) HEq.rfl value).trans
      (heq_of_eq (B.map_id_apply _ value))
  map_comp {first middle last} earlier later := by
    apply ConcreteCategory.hom_ext
    rintro ⟨label, value⟩
    apply Sigma.ext (A.map_comp_apply earlier later label)
    have target : (⟨last, A.map (earlier ≫ later) label⟩ : A.Elements) =
        ⟨last, A.map later (A.map earlier label)⟩ :=
      Sigma.ext rfl (heq_of_eq (A.map_comp_apply earlier later label))
    exact (sigmaMap_heq B target (argumentMap A (earlier ≫ later) label)
      (argumentMap A earlier label ≫ argumentMap A later (A.map earlier label)) HEq.rfl value).trans
        (heq_of_eq (B.map_comp_apply _ _ value))

def sigmaForward : Hom (sigmaFamily shape position) (sigmaFamily nextShape nextPosition) where
  app point term := sigmaEquiv signature point term
  naturality {first second} step term := by
    change (⟨nextShape.map step (signature.shapes first term.1),
      nextPosition.map (argumentMap nextShape step (signature.shapes first term.1))
        (signature.positions first term.1 term.2)⟩ : (sigmaFamily nextShape nextPosition).obj second) =
      ⟨signature.shapes second (shape.map step term.1),
        signature.positions second (shape.map step term.1) (position.map (argumentMap shape step term.1) term.2)⟩
    exact Sigma.ext (signature.shape_natural step term.1).symm
      (signature.position_natural step term.1 term.2).symm

def sigmaBackward : Hom (sigmaFamily nextShape nextPosition) (sigmaFamily shape position) where
  app point := (sigmaEquiv signature point).symm
  naturality {first second} step term := by
    apply (sigmaEquiv signature second).injective
    exact ((sigmaForward signature).naturality step ((sigmaEquiv signature first).symm term)).symm.trans
      ((congrArg ((sigmaFamily nextShape nextPosition).map step)
        ((sigmaEquiv signature first).apply_symm_apply term)).trans
        ((sigmaEquiv signature second).apply_symm_apply ((sigmaFamily nextShape nextPosition).map step term)).symm)

theorem sigma_forward_backward : (sigmaForward signature).comp (sigmaBackward signature) = Hom.identity _ := by
  apply Hom.ext
  intro point term
  exact (sigmaEquiv signature point).symm_apply_apply term

theorem sigma_backward_forward : (sigmaBackward signature).comp (sigmaForward signature) = Hom.identity _ := by
  apply Hom.ext
  intro point term
  exact (sigmaEquiv signature point).apply_symm_apply term

def sigmaSections : (sigmaFamily shape position).sections ≃ (sigmaFamily nextShape nextPosition).sections where
  toFun := (sigmaForward signature).mapSection
  invFun := (sigmaBackward signature).mapSection
  left_inv term := by
    apply Subtype.ext
    funext point
    exact (sigmaEquiv signature point).symm_apply_apply (term.val point)
  right_inv term := by
    apply Subtype.ext
    funext point
    exact (sigmaEquiv signature point).apply_symm_apply (term.val point)

theorem sigma_first (point : E) (term : (sigmaFamily shape position).obj point) :
    (sigmaEquiv signature point term).1 = signature.shapes point term.1 := rfl

theorem sigma_second (point : E) (term : (sigmaFamily shape position).obj point) :
    (sigmaEquiv signature point term).2 = signature.positions point term.1 term.2 := rfl

end Mettapedia.TypeTheory.WiderPresheafSignatureEquivalence
