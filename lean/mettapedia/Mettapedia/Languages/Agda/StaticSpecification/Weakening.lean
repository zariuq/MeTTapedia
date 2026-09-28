import Mettapedia.Languages.Agda.StaticSpecification.Regularity

/-!
# Admissible renaming and weakening

The functions below recursively transform the retained derivation trees.
Renaming is not an extra inference rule in the static specification.
-/

namespace Mettapedia.Languages.Agda.StaticSpecification

mutual
  def FormTy.rename {Γ : RawContext n} {a : Ty n} (d : FormTy Γ a)
      {Δ : RawContext m} (ρ : Renaming n m) (hρ : ρ.Respects Γ Δ) (formed : FormCtx Δ) :
      FormTy Δ (a.rename ρ) :=
    match d with
    | .ofTyping h => .ofTyping (h.rename ρ hρ formed)

  termination_by structural d

  def Typing.rename {Γ : RawContext n} {t : Term n} {a : Ty n} (d : Typing Γ t a)
      {Δ : RawContext m} (ρ : Renaming n m) (hρ : ρ.Respects Γ Δ) (formed : FormCtx Δ) :
      Typing Δ (t.rename ρ) (a.rename ρ) :=
    match d with
    | .sort k _ => .sort k formed
    | .var i _ => hρ i ▸ Typing.var (ρ i) formed
    | .pi (a := a) (b := b) da db => by
        have ra := da.rename ρ hρ formed
        have rb := db.rename (Renaming.lift ρ) (hρ.lift a) (.snoc formed ra)
        simpa only [Term.rename, Ty.universe_rename, Ty.level_rename, TyAbs.level_rename]
          using Typing.pi (b := b.rename ρ) ra (by simpa only [TyAbs.open_rename] using rb)
    | .lam (a := a) (b := b) (body := body) da db dt => by
        have ra := da.rename ρ hρ formed
        have rb := db.rename (Renaming.lift ρ) (hρ.lift a) (.snoc formed ra)
        have rt := dt.rename (Renaming.lift ρ) (hρ.lift a) (.snoc formed ra)
        simpa only [Term.rename, Ty.pi_rename] using
          Typing.lam (b := b.rename ρ) (body := body.rename ρ) ra
            (by simpa only [TyAbs.open_rename] using rb)
            (by simpa only [Abs.open_rename, TyAbs.open_rename] using rt)
    | .app (a := a) (b := b) df du => by
        have rf := df.rename ρ hρ formed
        have ru := du.rename ρ hρ formed
        simpa only [Term.app_rename, TyAbs.instantiate_rename] using
          Typing.app (b := b.rename ρ) (by simpa only [Ty.pi_rename] using rf) ru
    | .conv dt de => .conv (dt.rename ρ hρ formed) (de.rename ρ hρ formed)

  termination_by structural d

  def TypeEq.rename {Γ : RawContext n} {a b : Ty n} (d : TypeEq Γ a b)
      {Δ : RawContext m} (ρ : Renaming n m) (hρ : ρ.Respects Γ Δ) (formed : FormCtx Δ) :
      TypeEq Δ (a.rename ρ) (b.rename ρ) :=
    match d with
    | .atSort h => .atSort (h.rename ρ hρ formed)

  termination_by structural d

  def TermEq.rename {Γ : RawContext n} {t u : Term n} {a : Ty n} (d : TermEq Γ t u a)
      {Δ : RawContext m} (ρ : Renaming n m) (hρ : ρ.Respects Γ Δ) (formed : FormCtx Δ) :
      TermEq Δ (t.rename ρ) (u.rename ρ) (a.rename ρ) :=
    match d with
    | .refl h => .refl (h.rename ρ hρ formed)
    | .symm h => .symm (h.rename ρ hρ formed)
    | .trans h k => .trans (h.rename ρ hρ formed) (k.rename ρ hρ formed)
    | .conv h k => .conv (h.rename ρ hρ formed) (k.rename ρ hρ formed)
    | .piCong (a := a) (b := b) (b' := b') da de db => by
        have ra := da.rename ρ hρ formed
        have rb := db.rename (Renaming.lift ρ) (hρ.lift a) (.snoc formed ra)
        simpa only [Term.rename, Ty.universe_rename, Ty.level_rename, TyAbs.level_rename] using
          TermEq.piCong (b := b.rename ρ) (b' := b'.rename ρ) ra (de.rename ρ hρ formed)
            (by simpa only [TyAbs.open_rename] using rb)
    | .appCong (b := b) df du => by
        have rf := df.rename ρ hρ formed
        simpa only [Term.app_rename, TyAbs.instantiate_rename] using
          TermEq.appCong (b := b.rename ρ) (by simpa only [Ty.pi_rename] using rf)
            (du.rename ρ hρ formed)
    | .beta (a := a) (b := b) (body := body) da db dt du => by
        have ra := da.rename ρ hρ formed
        have rb := db.rename (Renaming.lift ρ) (hρ.lift a) (.snoc formed ra)
        have rt := dt.rename (Renaming.lift ρ) (hρ.lift a) (.snoc formed ra)
        simpa only [Term.app_rename, Term.rename, Abs.instantiate_rename,
          TyAbs.instantiate_rename] using
          TermEq.beta (b := b.rename ρ) (body := body.rename ρ) ra
            (by simpa only [TyAbs.open_rename] using rb)
            (by simpa only [Abs.open_rename, TyAbs.open_rename] using rt)
            (du.rename ρ hρ formed)
    | .eta (a := a) (b := b) (f := f) (g := g) da db df dg de => by
        have ra := da.rename ρ hρ formed
        have rb := db.rename (Renaming.lift ρ) (hρ.lift a) (.snoc formed ra)
        have re := de.rename (Renaming.lift ρ) (hρ.lift a) (.snoc formed ra)
        simpa only [Ty.pi_rename] using
          TermEq.eta (b := b.rename ρ) (f := f.rename ρ) (g := g.rename ρ) ra
            (by simpa only [TyAbs.open_rename] using rb)
            (by simpa only [Ty.pi_rename] using df.rename ρ hρ formed)
            (by simpa only [Ty.pi_rename] using dg.rename ρ hρ formed)
            (by simpa only [TyAbs.open_rename, Term.app_rename, Term.rename_weaken,
              Term.rename, Renaming.lift_zero] using re)
  termination_by structural d
end

def FormTy.weaken {Γ : RawContext n} {a b : Ty n} (d : FormTy Γ b) (added : FormTy Γ a) :
    FormTy (Γ.snoc a) b.weaken :=
  d.rename Fin.succ (Renaming.respects_weaken Γ a) (.snoc added.context added)

def Typing.weaken {Γ : RawContext n} {t : Term n} {a b : Ty n}
    (d : Typing Γ t b) (added : FormTy Γ a) :
    Typing (Γ.snoc a) t.weaken b.weaken :=
  d.rename Fin.succ (Renaming.respects_weaken Γ a) (.snoc added.context added)

def TypeEq.weaken {Γ : RawContext n} {a b c : Ty n}
    (d : TypeEq Γ a b) (added : FormTy Γ c) : TypeEq (Γ.snoc c) a.weaken b.weaken :=
  d.rename Fin.succ (Renaming.respects_weaken Γ c) (.snoc added.context added)

def TermEq.weaken {Γ : RawContext n} {t u : Term n} {a b : Ty n}
    (d : TermEq Γ t u b) (added : FormTy Γ a) :
    TermEq (Γ.snoc a) t.weaken u.weaken b.weaken :=
  d.rename Fin.succ (Renaming.respects_weaken Γ a) (.snoc added.context added)

end Mettapedia.Languages.Agda.StaticSpecification
