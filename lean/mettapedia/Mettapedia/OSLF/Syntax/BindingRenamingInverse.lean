import Mettapedia.OSLF.Syntax.BindingContextPositions
import Mettapedia.OSLF.Syntax.Strengthening

/-!
# Executable partial inverses for injective typed variable maps

The search enumerates variables of the requested sort in the finite parameter
context. An injective map supplies the existing `Strengthener` contract, so
the common capture-avoiding strengthening operation applies to reordered
spines as well as ordinary inclusions. This executable profile requires sort
equality, but no finite sort carrier or global bound on declarations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RenamingInverse

variable {S : Signature} [DecidableEq S.Srt]

def ofSort : (context : Ctx S) → (sort : S.Srt) → List (Var context sort)
  | [], _ => []
  | head :: rest, sort =>
      (if same : head = sort then [ContextPositions.castSort (S := S) same Var.zero] else []) ++
        (ofSort rest sort).map Var.succ

theorem ofSort_complete : ∀ (context : Ctx S) (sort : S.Srt) (position : Var context sort),
    position ∈ ofSort context sort
  | [], _, position => nomatch position
  | _ :: _, _, .zero => by simp [ofSort, ContextPositions.castSort]
  | head :: rest, sort, .succ position => by
      apply List.mem_append_right
      exact List.mem_map.mpr ⟨position, ofSort_complete rest sort position, rfl⟩

def inverse {parameters context : Ctx S} (rho : Ren S parameters context)
    (sort : S.Srt) (position : Var context sort) : Option (Var parameters sort) :=
  (ofSort parameters sort).find? fun original => decide (rho sort original = position)

theorem inverse_sound {parameters context : Ctx S} (rho : Ren S parameters context)
    (sort : S.Srt) (position : Var context sort) (original : Var parameters sort)
    (found : inverse rho sort position = some original) : rho sort original = position :=
  of_decide_eq_true (List.find?_some (p := fun candidate => decide (rho sort candidate = position)) found)

theorem inverse_complete {parameters context : Ctx S} (rho : Ren S parameters context)
    (injective : ∀ sort, Function.Injective (rho sort)) (sort : S.Srt) (original : Var parameters sort) :
    inverse rho sort (rho sort original) = some original := by
  unfold inverse
  cases found : (ofSort parameters sort).find? (fun candidate => decide (rho sort candidate = rho sort original)) with
  | none =>
      have excluded := List.find?_eq_none.mp found original (ofSort_complete parameters sort original)
      simp at excluded
  | some candidate =>
      have same := of_decide_eq_true (List.find?_some
        (p := fun candidate => decide (rho sort candidate = rho sort original)) found)
      exact congrArg some (injective sort same)

def strengthener {parameters context : Ctx S} (rho : Ren S parameters context)
    (injective : ∀ sort, Function.Injective (rho sort)) : Strengthener rho where
  un := inverse rho
  un_rho := inverse_complete rho injective
  rho_un := inverse_sound rho

end Mettapedia.OSLF.Binding.RenamingInverse
