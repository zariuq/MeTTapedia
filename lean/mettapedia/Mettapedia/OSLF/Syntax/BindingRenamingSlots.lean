import Mettapedia.OSLF.Syntax.BindingContextPositions
import Mathlib.Data.Fintype.Pi

/-!
# Deciding injectivity of typed variable maps through finite positions

A positional map represents the same typed renaming over the two finite
contexts. Its injectivity is equivalent to injectivity at every sort, so a
finite executable check needs no enumeration or equality test on the sort
carrier. Mixed sorts and repeated equal-sort positions remain distinct.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RenamingSlots

open ContextPositions

variable {S : Signature} {Δ Γ Θ : Ctx S}

def map (rho : Ren S Δ Γ) (slot : Fin Δ.length) : Fin Γ.length :=
  toSlot (rho _ (ofSlot Δ slot))

theorem map_toSlot (rho : Ren S Δ Γ) {sort : S.Srt} (position : Var Δ sort) :
    map rho (toSlot position) = toSlot (rho sort position) :=
  Fin.ext (map_index_ofSlot rho position)

theorem injective_of_typed (rho : Ren S Δ Γ) (injective : ∀ sort, Function.Injective (rho sort)) :
    Function.Injective (map rho) := by
  intro first second same
  have indices := congrArg Fin.val same
  change CommonABT.index (rho _ (ofSlot Δ first)) = CommonABT.index (rho _ (ofSlot Δ second)) at indices
  have sorts := sort_eq_of_equal_index (rho _ (ofSlot Δ first)) (rho _ (ofSlot Δ second)) indices
  have mapped : rho _ (castSort sorts (ofSlot Δ first)) = rho _ (ofSlot Δ second) := by
    apply CommonABT.index_injective
    rw [map_castSort (S := S) rho sorts, index_castSort]
    exact indices
  have original := congrArg (CommonABT.index (S := S)) (injective _ mapped)
  rw [index_castSort, index_ofSlot, index_ofSlot] at original
  exact Fin.ext original

theorem typed_of_injective (rho : Ren S Δ Γ) (injective : Function.Injective (map rho)) :
    ∀ sort, Function.Injective (rho sort) := by
  intro sort first second same
  apply CommonABT.index_injective
  have positional : map rho (toSlot first) = map rho (toSlot second) := by
    rw [map_toSlot, map_toSlot, same]
  exact congrArg Fin.val (injective positional)

theorem injective_iff (rho : Ren S Δ Γ) :
    Function.Injective (map rho) ↔ ∀ sort, Function.Injective (rho sort) :=
  ⟨typed_of_injective rho, injective_of_typed rho⟩

def check (rho : Ren S Δ Γ) : Bool := decide (Function.Injective (map rho))

theorem check_iff (rho : Ren S Δ Γ) : check rho = true ↔ ∀ sort, Function.Injective (rho sort) := by
  rw [check, decide_eq_true_eq, injective_iff]

theorem lift_injective (rho : Ren S Δ Γ) (injective : ∀ sort, Function.Injective (rho sort)) :
    ∀ binders sort, Function.Injective (liftRen rho binders sort)
  | [], sort => injective sort
  | _ :: rest, sort => by
      intro first second same
      cases first with
      | zero =>
          cases second with
          | zero => rfl
          | succ _ => cases same
      | succ first =>
          cases second with
          | zero => cases same
          | succ second => exact congrArg Var.succ (lift_injective rho injective rest sort (Var.succ.inj same))

theorem compose_injective (rho : Ren S Δ Γ) (tau : Ren S Γ Θ)
    (first : ∀ sort, Function.Injective (rho sort)) (second : ∀ sort, Function.Injective (tau sort)) :
    ∀ sort, Function.Injective (fun position => tau sort (rho sort position)) :=
  fun sort => (second sort).comp (first sort)

end Mettapedia.OSLF.Binding.RenamingSlots
