import Mettapedia.OSLF.Syntax.PartialRenaming

/-!
# Common dependencies of one hole at two parameter maps

An equalizer retains the formal positions whose two ambient images agree.
It lifts through every object binder. A term with equal images under the two
maps therefore has a unique body over this retained interface.

The resulting strengthening operation is the existing one. These are
structural binding laws, without a conversion or normalization assumption.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding

variable {S : Signature} {Δ Γ : Ctx S}

structure ScopeEqualizer (left right : Ren S Δ Γ) where
  context : Ctx S
  inclusion : Ren S context Δ
  commutes : ∀ sort (position : Var context sort),
    left sort (inclusion sort position) = right sort (inclusion sort position)
  recover : ∀ sort (position : Var Δ sort), left sort position = right sort position → Var context sort
  recover_inclusion : ∀ sort (position : Var Δ sort) (same : left sort position = right sort position),
    inclusion sort (recover sort position same) = position
  recover_pair : ∀ sort (position : Var context sort),
    recover sort (inclusion sort position) (commutes sort position) = position

namespace ScopeEqualizer

variable {left right : Ren S Δ Γ} (equalizer : ScopeEqualizer left right)

def liftRecover : (binders : Ctx S) → ∀ sort (position : Var (binders ++ Δ) sort),
    liftRen left binders sort position = liftRen right binders sort position →
      Var (binders ++ equalizer.context) sort
  | [], sort, position, same => equalizer.recover sort position same
  | _ :: _, _, .zero, _ => .zero
  | _ :: binders, sort, .succ position, same =>
      .succ (liftRecover binders sort position (Var.succ.inj same))

theorem lift_commutes : ∀ (binders : Ctx S) sort (position : Var (binders ++ equalizer.context) sort),
    liftRen left binders sort (liftRen equalizer.inclusion binders sort position) =
      liftRen right binders sort (liftRen equalizer.inclusion binders sort position)
  | [], sort, position => equalizer.commutes sort position
  | _ :: _, _, .zero => rfl
  | _ :: binders, sort, .succ position => congrArg Var.succ (lift_commutes binders sort position)

theorem liftRecover_inclusion : ∀ (binders : Ctx S) sort (position : Var (binders ++ Δ) sort)
    (same : liftRen left binders sort position = liftRen right binders sort position),
    liftRen equalizer.inclusion binders sort (equalizer.liftRecover binders sort position same) = position
  | [], sort, position, same => equalizer.recover_inclusion sort position same
  | _ :: _, _, .zero, _ => rfl
  | _ :: binders, sort, .succ position, same =>
      congrArg Var.succ (liftRecover_inclusion binders sort position (Var.succ.inj same))

theorem liftRecover_pair : ∀ (binders : Ctx S) sort (position : Var (binders ++ equalizer.context) sort),
    equalizer.liftRecover binders sort (liftRen equalizer.inclusion binders sort position)
      (equalizer.lift_commutes binders sort position) = position
  | [], sort, position => equalizer.recover_pair sort position
  | _ :: _, _, .zero => rfl
  | _ :: binders, sort, .succ position => congrArg Var.succ (liftRecover_pair binders sort position)

def liftS (binders : Ctx S) : ScopeEqualizer (liftRen left binders) (liftRen right binders) where
  context := binders ++ equalizer.context
  inclusion := liftRen equalizer.inclusion binders
  commutes := equalizer.lift_commutes binders
  recover := equalizer.liftRecover binders
  recover_inclusion := equalizer.liftRecover_inclusion binders
  recover_pair := equalizer.liftRecover_pair binders

def recognize (sort : S.Srt) (position : Var Δ sort) : Option (Var equalizer.context sort) :=
  letI : DecidableEq (Var Γ sort) := decEqVar (S := S)
  if same : left sort position = right sort position then some (equalizer.recover sort position same) else none

/-- The equality test recognizes exactly the inclusion's variable image. -/
def strengthener : Strengthener equalizer.inclusion where
  un := equalizer.recognize
  un_rho := by
    intro sort position
    unfold recognize
    rw [dif_pos (equalizer.commutes sort position), equalizer.recover_pair]
  rho_un := by
    intro sort position original found
    unfold recognize at found
    split at found
    · have same := Option.some.inj found
      subst original
      exact equalizer.recover_inclusion sort position (by assumption)
    · cases found

mutual

theorem factor_term : ∀ {Δ Γ : Ctx S} {left right : Ren S Δ Γ}
    (equalizer : ScopeEqualizer left right) {sort : S.Srt} (term : Term S Δ sort),
    rename left term = rename right term →
      ∃ common : Term S equalizer.context sort, rename equalizer.inclusion common = term
  | _, _, _, _, equalizer, sort, .var position, same =>
      ⟨.var (equalizer.recover sort position (Term.var.inj same)),
        congrArg Term.var (equalizer.recover_inclusion sort position (Term.var.inj same))⟩
  | _, _, _, _, equalizer, _, .op operator arguments, same => by
      obtain ⟨common, restored⟩ :=
        factor_arguments equalizer arguments (eq_of_heq (Term.op.inj same).2)
      exact ⟨.op operator common, congrArg (Term.op operator) restored⟩

theorem factor_arguments : ∀ {Δ Γ : Ctx S} {left right : Ren S Δ Γ}
    (equalizer : ScopeEqualizer left right) {arities : List (List S.Srt × S.Srt)}
    (arguments : Args S arities Δ),
    renameArgs left arguments = renameArgs right arguments →
      ∃ common : Args S arities equalizer.context, renameArgs equalizer.inclusion common = arguments
  | _, _, _, _, _, _, .nil, _ => ⟨.nil, rfl⟩
  | _, _, _, _, equalizer, _, .cons (bs := binders) head tail, same => by
      have fields := Args.cons.inj same
      obtain ⟨commonHead, headRestored⟩ := (equalizer.liftS binders).factor_term head fields.1
      obtain ⟨commonTail, tailRestored⟩ := factor_arguments equalizer tail fields.2
      exact ⟨.cons commonHead commonTail, congrArg₂ Args.cons headRestored tailRestored⟩

end

theorem factor_term_unique {sort : S.Srt} (term : Term S Δ sort)
    (same : rename left term = rename right term) :
    ∃! common : Term S equalizer.context sort, rename equalizer.inclusion common = term := by
  obtain ⟨common, restored⟩ := equalizer.factor_term term same
  exact ⟨common, restored, fun other otherRestored =>
    rename_injective equalizer.strengthener (otherRestored.trans restored.symm)⟩

end ScopeEqualizer
end Mettapedia.OSLF.Binding
