import Mettapedia.OSLF.Syntax.ContextualFamily

/-!
# Executable recovery of variable-only argument spines

The arguments are the existing typed binding `Args`. The recognizer recovers
their variable map, permitting reordering and repeated variables. This recovers
the given arguments; it does not assert unique recovery of a metavariable body
from an application equation. That stronger fragment additionally requires an
injective map. A compound argument makes this recognizer decline.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.VariableSpines

variable {S : Signature}

def recognize : (parameters : Ctx S) → {Γ : Ctx S} →
    Args S (parameters.map fun sort => ([], sort)) Γ → Option (Ren S parameters Γ)
  | [], _, .nil => some (fun _ index => nomatch index)
  | _ :: rest, _, .cons (.var position) remaining =>
      (recognize rest remaining).map fun rho sort index => match index with
        | .zero => position
        | .succ previous => rho sort previous
  | _ :: _, _, .cons (.op _ _) _ => none

theorem sound : ∀ (parameters : Ctx S) {Γ : Ctx S}
    (arguments : Args S (parameters.map fun sort => ([], sort)) Γ)
    (rho : Ren S parameters Γ), recognize parameters arguments = some rho →
      ∀ sort index, argsToSub arguments sort index = Term.var (rho sort index)
  | [], _, .nil, _, _ => by intro sort index; nomatch index
  | _ :: _, _, .cons (.op _ _) _, _, impossible => by cases impossible
  | _ :: rest, _, .cons (.var position) remaining, rho, computed => by
      cases tail : recognize rest remaining with
      | none => simp only [recognize, tail, Option.map_none, reduceCtorEq] at computed
      | some tailMap =>
          simp only [recognize, tail, Option.map_some, Option.some.injEq] at computed
          subst rho
          intro sort index
          cases index with
          | zero => rfl
          | succ previous => exact sound rest remaining tailMap tail sort previous

theorem complete : ∀ (parameters : Ctx S) {Γ : Ctx S}
    (arguments : Args S (parameters.map fun sort => ([], sort)) Γ)
    (rho : Ren S parameters Γ),
    (∀ sort index, argsToSub arguments sort index = Term.var (rho sort index)) →
      recognize parameters arguments = some rho
  | [], _, .nil, rho, _ => by
      apply congrArg some
      funext sort index
      nomatch index
  | first :: rest, _, .cons head remaining, rho, images => by
      have firstImage : head = Term.var (rho first .zero) := images first .zero
      cases head with
      | op _ _ => cases firstImage
      | var position =>
          have firstPosition := Term.var.inj firstImage
          have tail := complete rest remaining (fun sort index => rho sort (.succ index))
            (fun sort index => images sort (.succ index))
          rw [recognize, tail, Option.map_some]
          apply congrArg some
          funext sort index
          cases index with
          | zero => exact firstPosition
          | succ _ => rfl

theorem recognizes_iff (parameters : Ctx S) {Γ : Ctx S}
    (arguments : Args S (parameters.map fun sort => ([], sort)) Γ) (rho : Ren S parameters Γ) :
    recognize parameters arguments = some rho ↔
      ∀ sort index, argsToSub arguments sort index = Term.var (rho sort index) :=
  ⟨sound parameters arguments rho, complete parameters arguments rho⟩

end Mettapedia.OSLF.Binding.VariableSpines
