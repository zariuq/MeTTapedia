import Mettapedia.Languages.Agda.StaticSpecification.TypedSubstitution

/-! Function eta expansion derived from the typed extensionality rule. -/

namespace Mettapedia.Languages.Agda.StaticSpecification

def FormCtx.lookup {Γ : RawContext n} (d : FormCtx Γ) (i : Fin n) : FormTy Γ (Γ.lookup i) := by
  cases d with
  | nil => exact Fin.elim0 i
  | snoc tail domain =>
      exact Fin.cases (domain.weaken domain) (fun j => (tail.lookup j).weaken domain) i
termination_by structural d

def Typing.applyNewest {Γ : RawContext n} {a : Ty n} {b : TyAbs n} {f : Term n}
    (d : Typing Γ f (Ty.pi a b)) (domain : FormTy Γ a) :
    Typing (Γ.snoc a) (f.weaken.app (.var 0)) b.open := by
  have hf := d.weaken domain
  have hx := Typing.var 0 (FormCtx.snoc domain.context domain)
  simpa only [TyAbs.instantiate_weaken_var] using
    Typing.app (b := b.rename Fin.succ)
      (by simpa only [Ty.weaken, Ty.pi_rename, RawContext.lookup_zero] using hf) hx

/-- Eta expansion preserves the original dependent codomain and context. -/
def Typing.etaExpand {Γ : RawContext n} {a : Ty n} {b : TyAbs n} {f : Term n}
    (d : Typing Γ f (Ty.pi a b)) (domain : FormTy Γ a)
    (codomain : FormTy (Γ.snoc a) b.open) :
    Typing Γ (.lam (.bind (f.weaken.app (.var 0)))) (Ty.pi a b) :=
  .lam domain codomain (d.applyNewest domain)

/-- This relates distinct raw terms; no raw quotient or untyped eta rule is used. -/
def TermEq.etaExpand {Γ : RawContext n} {a : Ty n} {b : TyAbs n} {f : Term n}
    (d : Typing Γ f (Ty.pi a b)) (domain : FormTy Γ a)
    (codomain : FormTy (Γ.snoc a) b.open) :
    TermEq Γ f (.lam (.bind (f.weaken.app (.var 0)))) (Ty.pi a b) := by
  have formed := FormCtx.snoc domain.context domain
  have da := domain.weaken domain
  have lifted := (Renaming.respects_weaken Γ a).lift a
  have db := codomain.rename (Renaming.lift Fin.succ) lifted (.snoc formed da)
  have dt := (d.applyNewest domain).rename (Renaming.lift Fin.succ) lifted (.snoc formed da)
  have dx := Typing.var 0 formed
  apply TermEq.eta domain codomain d (d.etaExpand domain codomain)
  apply TermEq.symm
  have beta := TermEq.beta (a := a.weaken) (b := b.rename Fin.succ)
    (body := Abs.bind ((f.weaken.app (.var 0)).rename (Renaming.lift Fin.succ))) da
    (by simpa only [TyAbs.open_rename, Ty.weaken] using db)
    (by simpa only [TyAbs.open_rename, Abs.open, Ty.weaken] using dt) dx
  simpa only [TyAbs.instantiate_weaken_var, Abs.instantiate, Abs.open,
    Term.rename_lift_single_var, Term.weaken, Term.rename, Abs.rename] using beta

end Mettapedia.Languages.Agda.StaticSpecification
