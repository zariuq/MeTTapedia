import Mettapedia.GSLT.Core.ContextualLadderBaseCategory
import Mettapedia.GSLT.Core.ContextualLadderTerminal
import Mathlib.CategoryTheory.Types.Basic

/-!
# An unrestricted cartesian cell changes a primitive witness

The free one-sort context model has actual ordered variables, substitutions
and comprehension. Boolean valuations give an independent interpretation of
its context category. Simultaneously negating every supplied valuation is a
natural isomorphism preserving the complete cartesian display reading.
It fixes the empty context but changes the primitive generic witness.

Thus naturality, terminal preservation and cartesian coherence alone do not
impose declaration-fixed cell admission. This control concerns the structural
one-sort model, without attributing dependent products or sums to that model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.ContextualPrimitiveCellControls

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder

/-- The free variable-and-substitution structure of one declared sort. -/
def variableCore : Ucwf.{0,0,0} where
  Ctx := Nat
  Sub source target := Fin target → Fin source
  idS _ := id
  compS later earlier := earlier ∘ later
  id_comp _ := rfl
  comp_id _ := rfl
  comp_assoc _ _ _ := rfl
  Tm context := Fin context
  tmSub index substitution := substitution index
  tmSub_id _ := rfl
  tmSub_comp _ _ _ := rfl
  ext context := context + 1
  wk := Fin.succ
  vz := 0
  pair substitution term := Fin.cases term substitution
  wk_pair _ _ := rfl
  vz_pair _ _ := rfl
  pair_eta substitution := by
    funext position
    refine Fin.cases ?_ (fun index => ?_) position
    · rfl
    · rfl

/-- Actual comprehension and the chosen empty context are inherited from
the variable calculus, with no semantic equality fields added. -/
def variableModel : CwfWithTerminal.{0,0,0,0} where
  toCwf := variableCore.toScwf.toCwf
  empty := (0 : Nat)
  toEmpty _ := Fin.elim0
  toEmpty_unique _ substitution := by
    funext position
    exact Fin.elim0 position

/-- A context denotes all supplied Boolean valuations of its variables. -/
def valuations : variableModel.toCwf.base.Context ⥤ Type where
  obj context := Fin context.val → Bool
  map substitution := TypeCat.ofHom (fun valuation => valuation ∘ substitution)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Negation acts on complete valuations, not merely their existence. -/
def negate : valuations ⟶ valuations where
  app _ := TypeCat.ofHom (fun valuation position => !(valuation position))
  naturality {_ _} _ := rfl

def negationIso : valuations ≅ valuations where
  hom := negate
  inv := negate
  hom_inv_id := by
    apply NatTrans.ext
    funext context
    apply ConcreteCategory.hom_ext
    intro valuation
    funext position
    exact Bool.not_not _
  inv_hom_id := by
    apply NatTrans.ext
    funext context
    apply ConcreteCategory.hom_ext
    intro valuation
    funext position
    exact Bool.not_not _

/-- The image of actual comprehension is the supplied valuation together
with the exact newest witness. Both inverse directions are computational. -/
def comprehensionReading (context : Nat) :
    (Fin (context + 1) → Bool) ≃ ((Fin context → Bool) × Bool) where
  toFun valuation := (valuation ∘ Fin.succ, valuation 0)
  invFun pair := Fin.cases pair.2 pair.1
  left_inv valuation := by
    funext position
    refine Fin.cases ?_ (fun index => ?_) position
    · rfl
    · rfl
  right_inv pair := rfl

/-- Naturality preserves the actual display projection. -/
theorem projection_square (context : Nat) :
    valuations.map (variableModel.toCwf.wk PUnit.unit) ≫ negate.app ⟨context⟩ =
      negate.app ⟨context + 1⟩ ≫ valuations.map (variableModel.toCwf.wk PUnit.unit) :=
  negate.naturality _

/-- The complete comprehension square includes the independently supplied
primitive witness transformation. It is coherent, yet changes that witness. -/
theorem complete_cartesian_reading (context : Nat) (valuation : Fin (context + 1) → Bool) :
    comprehensionReading context (negate.app ⟨context + 1⟩ valuation) =
      ((fun position => !((comprehensionReading context valuation).1 position)),
        !((comprehensionReading context valuation).2)) := rfl

theorem empty_fixed : negate.app ⟨(0 : Nat)⟩ = 𝟙 (valuations.obj ⟨(0 : Nat)⟩) := by
  apply ConcreteCategory.hom_ext
  intro valuation
  funext position
  exact Fin.elim0 position

theorem newest_witness_changed :
    (negate.app ⟨(1 : Nat)⟩ (fun _ => false)) 0 = true := rfl

/-- Dropping the local primitive reading allows an actual nonidentity
natural and cartesian coherent cell. -/
theorem primitive_display_not_fixed : negate.app ⟨(1 : Nat)⟩ ≠ 𝟙 (valuations.obj ⟨(1 : Nat)⟩) := by
  intro same
  have witness := congrArg (fun transformation => transformation (fun _ => false) 0) same
  exact (by decide : true ≠ false) witness

theorem unrestricted_cell_not_identity : negate ≠ 𝟙 valuations := by
  intro same
  exact primitive_display_not_fixed (NatTrans.congr_app same ⟨(1 : Nat)⟩)

end Mettapedia.TypeTheory.ContextualPrimitiveCellControls
