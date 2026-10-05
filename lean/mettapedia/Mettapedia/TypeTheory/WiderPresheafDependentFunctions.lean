import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Types.Basic

/-!
# Dependent sections with separate world and value universes

Every actual future world, arrow, and typed argument is retained. Natural
maps may have different value universes, so the universal property also
tests wider dependent consumers. The section carrier has its explicit
maximum universe; a smaller carrier requires a separate proved comparison.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.WiderPresheafDependentFunctions

open CategoryTheory

universe u v w z h k l

variable {E : Type v} [Category.{u} E]

structure Hom (source : E ⥤ Type w) (target : E ⥤ Type z) where
  app : ∀ point, source.obj point → target.obj point
  naturality : ∀ {first second} (step : first ⟶ second) (value : source.obj first),
    target.map step (app first value) = app second (source.map step value)

namespace Hom

variable {first : E ⥤ Type w} {second : E ⥤ Type z} {third : E ⥤ Type h}

theorem ext (left right : Hom first second)
    (same : ∀ point value, left.app point value = right.app point value) : left = right := by
  cases left with
  | mk left left_law =>
    cases right with
    | mk right right_law =>
      have equal : left = right := funext fun point => funext fun value => same point value
      cases equal
      rfl

def identity (family : E ⥤ Type w) : Hom family family where
  app _ value := value
  naturality _ _ := rfl

def comp (earlier : Hom first second) (later : Hom second third) : Hom first third where
  app point value := later.app point (earlier.app point value)
  naturality step value :=
    (later.naturality step (earlier.app _ value)).trans
      (congrArg (later.app _) (earlier.naturality step value))

theorem identity_comp (operation : Hom first second) :
    (identity first).comp operation = operation := by
  apply ext
  intro _ _
  rfl

theorem comp_identity (operation : Hom first second) :
    operation.comp (identity second) = operation := by
  apply ext
  intro _ _
  rfl

theorem assoc {fourth : E ⥤ Type k}
    (firstMap : Hom first second) (secondMap : Hom second third)
    (thirdMap : Hom third fourth) :
    (firstMap.comp secondMap).comp thirdMap = firstMap.comp (secondMap.comp thirdMap) := by
  apply ext
  intro _ _
  rfl

def ofNatTrans {source target : E ⥤ Type w} (operation : NatTrans source target) :
    Hom source target where
  app point := operation.app point
  naturality step value := (congrArg (fun map => map value) (operation.naturality step)).symm

def toNatTrans {source target : E ⥤ Type w} (operation : Hom source target) :
    NatTrans source target where
  app point := TypeCat.ofHom (operation.app point)
  naturality _ _ step := by
    apply ConcreteCategory.hom_ext
    intro value
    exact (operation.naturality step value).symm

def natTransEquiv (source target : E ⥤ Type w) : Hom source target ≃ NatTrans source target where
  toFun := toNatTrans
  invFun := ofNatTrans
  left_inv operation := by
    apply ext
    intro _ _
    rfl
  right_inv operation := by
    apply NatTrans.ext
    funext point
    apply ConcreteCategory.hom_ext
    intro _
    rfl

def mapSection (operation : Hom first second) (term : first.sections) : second.sections :=
  ⟨fun point => operation.app point (term.val point), by
    intro source target step
    exact (operation.naturality step (term.val source)).trans
      (congrArg (operation.app target) (term.property step))⟩

end Hom

def restrict {K : Type h} [Category.{u} K] (change : K ⥤ E) (family : E ⥤ Type w) :
    K ⥤ Type w where
  obj point := family.obj (change.obj point)
  map step := family.map (change.map step)
  map_id point := by rw [change.map_id, family.map_id]
  map_comp first second := by rw [change.map_comp, family.map_comp]

def over (domain : E ⥤ Type w) (family : E ⥤ Type h) : domain.Elements ⥤ Type h :=
  restrict (CategoryOfElements.π domain) family

def overHom (domain : E ⥤ Type w) {first : E ⥤ Type h} {second : E ⥤ Type k}
    (operation : Hom first second) : Hom (over domain first) (over domain second) where
  app point := operation.app point.1
  naturality step value := operation.naturality step.val value

variable (domain : E ⥤ Type w) (body : domain.Elements ⥤ Type z)

def argumentMap {first second : E} (step : first ⟶ second) (argument : domain.obj first) :
    domain.elementsMk first argument ⟶ domain.elementsMk second (domain.map step argument) :=
  CategoryOfElements.homMk _ _ step rfl

structure DependentSection (point : E) where
  app : ∀ future, (point ⟶ future) → (argument : domain.obj future) → body.obj ⟨future, argument⟩
  naturality : ∀ {first second} (step : first ⟶ second) (arrival : point ⟶ first)
      (argument : domain.obj first),
    body.map (argumentMap domain step argument) (app first arrival argument) =
      app second (arrival ≫ step) (domain.map step argument)

namespace DependentSection

theorem ext {point : E} (first second : DependentSection domain body point)
    (equal : ∀ future arrival argument,
      first.app future arrival argument = second.app future arrival argument) : first = second := by
  cases first with
  | mk first first_law =>
    cases second with
    | mk second second_law =>
      have same : first = second := funext fun future => funext fun arrival => funext fun argument =>
        equal future arrival argument
      cases same
      rfl

theorem app_heq {point first second : E} (term : DependentSection domain body point)
    (same : first = second) (arrival : point ⟶ first) (otherArrival : point ⟶ second)
    (arrows : HEq arrival otherArrival) (argument : domain.obj first) (otherArgument : domain.obj second)
    (arguments : HEq argument otherArgument) :
    HEq (term.app first arrival argument) (term.app second otherArrival otherArgument) := by
  cases same
  cases eq_of_heq arrows
  cases eq_of_heq arguments
  rfl

def restrict {first second : E} (step : first ⟶ second)
    (term : DependentSection domain body first) : DependentSection domain body second where
  app future arrival argument := term.app future (step ≫ arrival) argument
  naturality later arrival argument := by
    rw [← Category.assoc]
    exact term.naturality later (step ≫ arrival) argument

theorem restrict_id {point : E} (term : DependentSection domain body point) :
    restrict domain body (𝟙 point) term = term := by
  apply ext
  intro future arrival argument
  change term.app future (𝟙 point ≫ arrival) argument = term.app future arrival argument
  rw [Category.id_comp]

theorem restrict_comp {first middle last : E} (earlier : first ⟶ middle) (later : middle ⟶ last)
    (term : DependentSection domain body first) :
    restrict domain body later (restrict domain body earlier term) =
      restrict domain body (earlier ≫ later) term := by
  apply ext
  intro future arrival argument
  change term.app future (earlier ≫ later ≫ arrival) argument =
    term.app future ((earlier ≫ later) ≫ arrival) argument
  rw [Category.assoc]

end DependentSection

def dependentFunctions : E ⥤ Type (max u v w z) where
  obj := DependentSection domain body
  map step := TypeCat.ofHom (DependentSection.restrict domain body step)
  map_id _ := by
    apply ConcreteCategory.hom_ext
    exact DependentSection.restrict_id domain body
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro term
    exact (DependentSection.restrict_comp domain body first second term).symm

variable {domain body}

def curry {parameters : E ⥤ Type h} (operation : Hom (over domain parameters) body) :
    Hom parameters (dependentFunctions domain body) where
  app point parameter :=
    { app future arrival argument := operation.app ⟨future, argument⟩ (parameters.map arrival parameter)
      naturality later arrival argument := by
        rw [parameters.map_comp_apply]
        exact operation.naturality (argumentMap domain later argument)
          (parameters.map arrival parameter) }
  naturality step parameter := by
    apply DependentSection.ext
    intro future arrival argument
    change operation.app ⟨future, argument⟩ (parameters.map (step ≫ arrival) parameter) =
      operation.app ⟨future, argument⟩ (parameters.map arrival (parameters.map step parameter))
    rw [parameters.map_comp_apply]

def uncurry {parameters : E ⥤ Type h} (operation : Hom parameters (dependentFunctions domain body)) :
    Hom (over domain parameters) body where
  app point parameter := (operation.app point.1 parameter).app point.1 (𝟙 point.1) point.2
  naturality {first second} step parameter := by
    rcases first with ⟨first, argument⟩
    rcases second with ⟨second, nextArgument⟩
    rcases step with ⟨step, saved⟩
    change first ⟶ second at step
    change domain.map step argument = nextArgument at saved
    subst nextArgument
    change body.map (argumentMap domain step argument)
        ((operation.app first parameter).app first (𝟙 first) argument) =
      (operation.app second (parameters.map step parameter)).app second (𝟙 second)
        (domain.map step argument)
    rw [← operation.naturality step parameter]
    change _ = (operation.app first parameter).app second (step ≫ 𝟙 second) (domain.map step argument)
    rw [Category.comp_id]
    have natural := (operation.app first parameter).naturality step (𝟙 first) argument
    rw [Category.id_comp] at natural
    exact natural

theorem uncurry_curry {parameters : E ⥤ Type h} (operation : Hom (over domain parameters) body) :
    uncurry (curry operation) = operation := by
  apply Hom.ext
  rintro ⟨point, argument⟩ parameter
  exact congrArg (operation.app ⟨point, argument⟩) (parameters.map_id_apply point parameter)

theorem curry_uncurry {parameters : E ⥤ Type h}
    (operation : Hom parameters (dependentFunctions domain body)) : curry (uncurry operation) = operation := by
  apply Hom.ext
  intro point parameter
  apply DependentSection.ext
  intro future arrival argument
  change (operation.app future (parameters.map arrival parameter)).app future (𝟙 future) argument =
    (operation.app point parameter).app future arrival argument
  rw [← operation.naturality arrival parameter]
  change (operation.app point parameter).app future (arrival ≫ 𝟙 future) argument = _
  rw [Category.comp_id]

def homEquiv (domain : E ⥤ Type w) (body : domain.Elements ⥤ Type z) (parameters : E ⥤ Type h) :
    Hom (over domain parameters) body ≃ Hom parameters (dependentFunctions domain body) where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

def evaluate (domain : E ⥤ Type w) (body : domain.Elements ⥤ Type z) :
    Hom (over domain (dependentFunctions domain body)) body :=
  uncurry (Hom.identity (dependentFunctions domain body))

theorem beta {parameters : E ⥤ Type h} (operation : Hom (over domain parameters) body) :
    (overHom domain (curry operation)).comp (evaluate domain body) = operation :=
  uncurry_curry operation

theorem eta {parameters : E ⥤ Type h}
    (operation : Hom parameters (dependentFunctions domain body)) :
    curry ((overHom domain operation).comp (evaluate domain body)) = operation :=
  curry_uncurry operation

theorem transpose_unique {parameters : E ⥤ Type h}
    (operation : Hom (over domain parameters) body)
    (candidate : Hom parameters (dependentFunctions domain body))
    (computes : (overHom domain candidate).comp (evaluate domain body) = operation) :
    candidate = curry operation := by
  rw [← computes, eta]

def mapBody {other : domain.Elements ⥤ Type h} (operation : Hom body other) :
    Hom (dependentFunctions domain body) (dependentFunctions domain other) where
  app _ term :=
    { app future arrival argument := operation.app ⟨future, argument⟩ (term.app future arrival argument)
      naturality step arrival argument :=
        (operation.naturality (argumentMap domain step argument) (term.app _ arrival argument)).trans
          (congrArg (operation.app _) (term.naturality step arrival argument)) }
  naturality _ _ := by
    apply DependentSection.ext
    intro _ _ _
    rfl

theorem curry_natural_left {parameters : E ⥤ Type h} {other : E ⥤ Type k}
    (earlier : Hom other parameters) (operation : Hom (over domain parameters) body) :
    curry ((overHom domain earlier).comp operation) = earlier.comp (curry operation) := by
  apply Hom.ext
  intro point parameter
  apply DependentSection.ext
  intro future arrival argument
  exact congrArg (operation.app ⟨future, argument⟩) (earlier.naturality arrival parameter).symm

theorem curry_natural_right {parameters : E ⥤ Type h} {other : domain.Elements ⥤ Type k}
    (operation : Hom (over domain parameters) body) (later : Hom body other) :
    curry (operation.comp later) = (curry operation).comp (mapBody later) := by
  apply Hom.ext
  intro point parameter
  apply DependentSection.ext
  intro _ _ _
  rfl

end Mettapedia.TypeTheory.WiderPresheafDependentFunctions
