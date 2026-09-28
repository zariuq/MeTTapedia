import Mettapedia.GSLT.Topos.ConstructivePresheafDependentFunctions
import Mathlib.CategoryTheory.Category.Preorder

/-!
# Dependent function controls with growing argument domains

The fibre at argument `a` has `a + 1` possible results. Two sections agree on
all arguments at stage zero but differ at a future argument. A second family
has inhabited fibres at every current argument and an empty future fibre;
there is consequently no dependent section at stage zero.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.Controls

open CategoryTheory
open Mettapedia.GSLT.Topos.ConstructivePresheaf

def growing : Nat ⥤ Type where
  obj stage := Fin (stage + 1)
  map step := TypeCat.ofHom (fun argument =>
    ⟨argument.val, Nat.lt_of_lt_of_le argument.isLt (Nat.succ_le_succ (leOfHom step))⟩)
  map_id stage := by
    apply ConcreteCategory.hom_ext
    intro argument
    apply Fin.ext
    rfl
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro argument
    apply Fin.ext
    rfl

theorem argument_value {X Y : growing.Elements} (step : X ⟶ Y) : X.2.val = Y.2.val :=
  congrArg Fin.val step.property

def finiteResults : growing.Elements ⥤ Type where
  obj X := Fin (X.2.val + 1)
  map step := TypeCat.ofHom (fun result =>
    ⟨result.val, by simpa only [← argument_value step] using result.isLt⟩)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro result
    apply Fin.ext
    rfl
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro result
    apply Fin.ext
    rfl

def zeroSection (stage : Nat) : DependentSection growing finiteResults stage where
  app _ _ argument := ⟨0, Nat.zero_lt_succ argument.val⟩
  naturality _ _ _ := by apply Fin.ext; rfl

def lastSection (stage : Nat) : DependentSection growing finiteResults stage where
  app _ _ argument := ⟨argument.val, Nat.lt_succ_self argument.val⟩
  naturality _ _ _ := by apply Fin.ext; rfl

theorem sections_agree_at_zero (argument : growing.obj 0) :
    (zeroSection 0).app 0 (𝟙 0) argument = (lastSection 0).app 0 (𝟙 0) argument := by
  apply Fin.ext
  exact (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ argument.isLt)).symm

theorem future_sections_distinct : zeroSection 0 ≠ lastSection 0 := by
  intro same
  have impossible := congrArg
    (fun value => (value.app 1 (homOfLE (Nat.zero_le 1)) ⟨1, by decide⟩).val) same
  change (0 : Nat) = 1 at impossible
  cases impossible

theorem zero_fibre_has_one_value (result : finiteResults.obj ⟨0,⟨0,by decide⟩⟩) :
    result.val = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ result.isLt)

theorem later_fibre_has_distinct_values :
    (⟨0, by decide⟩ : finiteResults.obj ⟨1,⟨1,by decide⟩⟩) ≠ ⟨1,by decide⟩ := by
  intro same
  have impossible : (0 : Nat) = 1 := congrArg Fin.val same
  cases impossible

def partialResults : growing.Elements ⥤ Type where
  obj X := {result : Bool // X.2.val = 0}
  map step := TypeCat.ofHom (fun result =>
    ⟨result.val, (argument_value step).symm.trans result.property⟩)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro result
    apply Subtype.ext
    rfl
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro result
    apply Subtype.ext
    rfl

def currentFunction (argument : growing.obj 0) : partialResults.obj ⟨0,argument⟩ :=
  ⟨true, Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ argument.isLt)⟩

theorem current_argument_exists : Nonempty (growing.obj 0) := ⟨⟨0,by decide⟩⟩

theorem every_current_fibre_inhabited :
    ∀ argument : growing.obj 0, Nonempty (partialResults.obj ⟨0,argument⟩) :=
  fun argument => ⟨currentFunction argument⟩

theorem no_dependent_section : ¬ Nonempty (DependentSection growing partialResults 0) := by
  rintro ⟨value⟩
  have result := value.app 1 (homOfLE (Nat.zero_le 1)) ⟨1,by decide⟩
  have impossible : (1 : Nat) = 0 := result.property
  cases impossible

def parameters : Nat ⥤ Type where
  obj _ := Bool
  map _ := TypeCat.ofHom id

def selectResult : NatTrans (overElements growing parameters) finiteResults where
  app X := TypeCat.ofHom (fun (parameter : Bool) =>
    if parameter then ⟨X.2.val,Nat.lt_succ_self _⟩ else ⟨0,Nat.zero_lt_succ _⟩)
  naturality X Y step := by
    apply ConcreteCategory.hom_ext
    intro parameter
    cases parameter <;> apply Fin.ext
    · rfl
    · exact (argument_value step).symm

theorem curried_parameter_false : (curry selectResult).app 0 false = zeroSection 0 := by
  apply DependentSection.ext
  intro Y restriction argument
  rfl

theorem curried_parameter_true : (curry selectResult).app 0 true = lastSection 0 := by
  apply DependentSection.ext
  intro Y restriction argument
  rfl

theorem currying_keeps_parameter_distinction :
    (curry selectResult).app 0 false ≠ (curry selectResult).app 0 true := by
  rw [curried_parameter_false, curried_parameter_true]
  exact future_sections_distinct

theorem selected_operation_roundtrip : uncurry (curry selectResult) = selectResult :=
  uncurry_curry selectResult

#print axioms no_dependent_section
#print axioms currying_keeps_parameter_distinction

end Mettapedia.GSLT.Topos.ConstructivePresheaf.Dependent.Controls
