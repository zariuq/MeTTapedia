import Mettapedia.TypeTheory.PresheafNativeClosedAction
import Mathlib.Data.Fintype.Card

/-!
# Native closed substitution on a varying finite family

The context map advances a supplied natural-number index. Its native family
has fibre `Fin (n + 1)`, so substitution changes the actual evidence type.
A coherent reset map acts on complete receipts and remains distinguishable
from identity after substitution. Abstraction uses the actual native
exponential comparison for that body.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafNativeClosedActionControls

open _root_.CategoryTheory
open MonoidalCategory MonoidalClosed CartesianMonoidalCategory
open Mettapedia.GSLT.Core.ContextualLadder
open DisplayedPresheafTransport DisplayedPresheafComprehension
open DisplayedPresheafSlice
open ContextualLocalUniverses NativeLocalTheoryTransformation
open PresheafNativeClosedSubstitution PresheafNativeClosedAction

abbrev World := Discrete Unit

abbrev programs : Worldᵒᵖ ⥤ Type where
  obj _ := Nat
  map _ := 𝟙 Nat
  map_id _ := rfl
  map_comp _ _ := rfl

abbrev finiteFamily : DisplayedFamily programs where
  obj point := Fin (point.2 + 1)
  map arrow := TypeCat.ofHom fun witness =>
    Fin.cast (congrArg (fun n : Nat => n + 1) arrow.property) witness
  map_id _ := by ext witness; rfl
  map_comp _ _ := by ext witness; rfl

def advance : programs ⟶ programs where
  app _ := TypeCat.ofHom Nat.succ
  naturality := by intros; rfl

abbrev argument : TypeOver (nativeLocalModel World).toCwf programs :=
  ⟨LocalType.present finiteFamily⟩

def world : Worldᵒᵖ := Opposite.op (Discrete.mk ())

/-- This fibre is computed by the actual native reindexing functor. -/
theorem substituted_fibre (n : Nat) :
    ((substitution advance).obj argument).val.decoded.obj ⟨world, n⟩ =
      Fin (n + 2) := rfl

/-- Omitting the supplied context map changes the native evidence type. -/
theorem omitting_substitution_changes_the_type :
    ((substitution advance).obj argument).val.decoded.obj ⟨world, 0⟩ ≠
      argument.val.decoded.obj ⟨world, 0⟩ := by
  change Fin 2 ≠ Fin 1
  intro same
  have cardinal := Fintype.card_congr (Equiv.cast same)
  simp only [Fintype.card_fin] at cardinal
  exact (by decide : (2 : Nat) ≠ 1) cardinal

def resetFamily : finiteFamily ⟶ finiteFamily where
  app _ := TypeCat.ofHom fun _ => ⟨0, Nat.zero_lt_succ _⟩
  naturality := by
    intros
    apply ConcreteCategory.hom_ext
    intro witness
    apply Fin.ext
    rfl

def reset : argument ⟶ argument where
  substitution := totalHom resetFamily
  over := totalHom_projection resetFamily

abbrev shiftedArgument := (substitution advance).obj argument

def supplied (n : Nat) (witness : Fin (n + 2)) :
    (totalSpace shiftedArgument.val.decoded).obj world := ⟨n, witness⟩

set_option backward.isDefEq.respectTransparency false in
/-- The full native substitution square computes the supplied reset;
it does not replace the complete arrow by an equality of fibre types. -/
theorem substituted_reset_readout (n : Nat) (witness : Fin (n + 2)) :
    (((substitution advance).map reset).substitution.app world
      (supplied n witness)).2.val = 0 := by
  have square := reindex_arrow_square advance reset
  have readout := ConcreteCategory.congr_hom (NatTrans.congr_app square world)
    (supplied n witness)
  exact congrArg (fun receipt => receipt.2.val) readout

/-- The reset remains different from identity after native substitution. -/
theorem substituted_reset_is_not_identity :
    (substitution advance).map reset ≠ 𝟙 shiftedArgument := by
  intro same
  have readout := substituted_reset_readout 0 (⟨1, by decide⟩ : Fin 2)
  rw [same] at readout
  change (1 : Nat) = 0 at readout
  exact Nat.noConfusion readout

noncomputable def body : argument ⊗ argument ⟶ argument :=
  fst argument argument ≫ reset

/-- Substitution retains this supplied whole native function body. -/
theorem reset_abstraction_follows_substitution :
    (substitution advance).map (curry body) ≫
        (exponentialComparison advance argument argument).hom =
      curry (inv (prodComparison (substitution advance) argument argument) ≫
        (substitution advance).map body) :=
  abstraction_substitution advance body

/-- Applying the retained abstraction computes the actual substituted body. -/
theorem reset_abstraction_evaluation :
    uncurry ((substitution advance).map (curry body) ≫
      (exponentialComparison advance argument argument).hom) =
      inv (prodComparison (substitution advance) argument argument) ≫
        (substitution advance).map body := by
  rw [reset_abstraction_follows_substitution, uncurry_curry]

end Mettapedia.TypeTheory.PresheafNativeClosedActionControls
