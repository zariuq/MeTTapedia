import Mettapedia.Languages.Agda.StaticSpecification.Weakening

/-!
# Admissible substitution with retained typing evidence

A substitution stores actual source/target formation and one actual typing tree
for each image. Substitution on judgments is constructed by structural recursion
on the given derivation; it is not added to the inductive inference rules.
The composition functions do not assert equality of chosen derivation trees.
-/

namespace Mettapedia.Languages.Agda.StaticSpecification

structure SubDeriv (Γ : RawContext n) (Δ : RawContext m) (σ : Substitution n m) where
  source : FormCtx Γ
  target : FormCtx Δ
  lookup : (i : Fin n) → Typing Δ (σ i) ((Γ.lookup i).subst σ)

/-- Lifting fixes the newest variable and weakens all older images. -/
def SubDeriv.lift {Γ : RawContext n} {Δ : RawContext m} {σ : Substitution n m}
    (d : SubDeriv Γ Δ σ) {a : Ty n} (domain : FormTy Γ a)
    (image : FormTy Δ (a.subst σ)) :
    SubDeriv (Γ.snoc a) (Δ.snoc (a.subst σ)) (Substitution.lift σ) where
  source := .snoc d.source domain
  target := .snoc d.target image
  lookup := fun i => Fin.cases
    (by simpa only [Substitution.lift_zero, RawContext.lookup_zero, Ty.subst_weaken] using
      Typing.var 0 (FormCtx.snoc d.target image))
    (fun j => by simpa only [Substitution.lift_succ, RawContext.lookup_succ,
      Ty.subst_weaken] using (d.lookup j).weaken image) i

mutual
  def FormTy.substitute {Γ : RawContext n} {a : Ty n} (d : FormTy Γ a)
      {Δ : RawContext m} {σ : Substitution n m} (hσ : SubDeriv Γ Δ σ) :
      FormTy Δ (a.subst σ) :=
    match d with
    | .ofTyping h => .ofTyping (h.substitute hσ)

  termination_by structural d

  def Typing.substitute {Γ : RawContext n} {t : Term n} {a : Ty n} (d : Typing Γ t a)
      {Δ : RawContext m} {σ : Substitution n m} (hσ : SubDeriv Γ Δ σ) :
      Typing Δ (t.subst σ) (a.subst σ) :=
    match d with
    | .sort k _ => .sort k hσ.target
    | .var i _ => hσ.lookup i
    | .pi (a := a) (b := b) da db => by
        have ra := da.substitute hσ
        have rb := db.substitute (hσ.lift da ra)
        simpa only [Term.subst, Ty.universe_subst, Ty.level_subst, TyAbs.level_subst]
          using Typing.pi (b := b.subst σ) ra (by simpa only [TyAbs.open_subst] using rb)
    | .lam (a := a) (b := b) (body := body) da db dt => by
        have ra := da.substitute hσ
        have rb := db.substitute (hσ.lift da ra)
        have rt := dt.substitute (hσ.lift da ra)
        simpa only [Term.subst, Ty.pi_subst] using
          Typing.lam (b := b.subst σ) (body := body.subst σ) ra
            (by simpa only [TyAbs.open_subst] using rb)
            (by simpa only [Abs.open_subst, TyAbs.open_subst] using rt)
    | .app (a := a) (b := b) df du => by
        have rf := df.substitute hσ
        have ru := du.substitute hσ
        simpa only [Term.app_subst, TyAbs.instantiate_subst] using
          Typing.app (b := b.subst σ) (by simpa only [Ty.pi_subst] using rf) ru
    | .conv dt de => .conv (dt.substitute hσ) (de.substitute hσ)

  termination_by structural d

  def TypeEq.substitute {Γ : RawContext n} {a b : Ty n} (d : TypeEq Γ a b)
      {Δ : RawContext m} {σ : Substitution n m} (hσ : SubDeriv Γ Δ σ) :
      TypeEq Δ (a.subst σ) (b.subst σ) :=
    match d with
    | .atSort h => .atSort (h.substitute hσ)

  termination_by structural d

  def TermEq.substitute {Γ : RawContext n} {t u : Term n} {a : Ty n} (d : TermEq Γ t u a)
      {Δ : RawContext m} {σ : Substitution n m} (hσ : SubDeriv Γ Δ σ) :
      TermEq Δ (t.subst σ) (u.subst σ) (a.subst σ) :=
    match d with
    | .refl h => .refl (h.substitute hσ)
    | .symm h => .symm (h.substitute hσ)
    | .trans h k => .trans (h.substitute hσ) (k.substitute hσ)
    | .conv h k => .conv (h.substitute hσ) (k.substitute hσ)
    | .piCong (a := a) (b := b) (b' := b') da de db => by
        have ra := da.substitute hσ
        have rb := db.substitute (hσ.lift da ra)
        simpa only [Term.subst, Ty.universe_subst, Ty.level_subst, TyAbs.level_subst] using
          TermEq.piCong (b := b.subst σ) (b' := b'.subst σ) ra (de.substitute hσ)
            (by simpa only [TyAbs.open_subst] using rb)
    | .appCong (b := b) df du => by
        have rf := df.substitute hσ
        simpa only [Term.app_subst, TyAbs.instantiate_subst] using
          TermEq.appCong (b := b.subst σ) (by simpa only [Ty.pi_subst] using rf)
            (du.substitute hσ)
    | .beta (a := a) (b := b) (body := body) da db dt du => by
        have ra := da.substitute hσ
        have rb := db.substitute (hσ.lift da ra)
        have rt := dt.substitute (hσ.lift da ra)
        simpa only [Term.app_subst, Term.subst, Abs.instantiate_subst,
          TyAbs.instantiate_subst] using
          TermEq.beta (b := b.subst σ) (body := body.subst σ) ra
            (by simpa only [TyAbs.open_subst] using rb)
            (by simpa only [Abs.open_subst, TyAbs.open_subst] using rt)
            (du.substitute hσ)
    | .eta (a := a) (b := b) (f := f) (g := g) da db df dg de => by
        have ra := da.substitute hσ
        have rb := db.substitute (hσ.lift da ra)
        have re := de.substitute (hσ.lift da ra)
        simpa only [Ty.pi_subst] using
          TermEq.eta (b := b.subst σ) (f := f.subst σ) (g := g.subst σ) ra
            (by simpa only [TyAbs.open_subst] using rb)
            (by simpa only [Ty.pi_subst] using df.substitute hσ)
            (by simpa only [Ty.pi_subst] using dg.substitute hσ)
            (by simpa only [TyAbs.open_subst, Term.app_subst, Term.subst_weaken,
              Term.subst, Substitution.lift_zero] using re)
  termination_by structural d
end

/-- Identity substitution keeps all supplied context formation evidence. -/
def SubDeriv.identity {Γ : RawContext n} (formed : FormCtx Γ) :
    SubDeriv Γ Γ Term.var where
  source := formed
  target := formed
  lookup := fun i => by simpa only [Ty.subst_id] using Typing.var i formed

/-- Compose actual typing trees by the proved admissible substitution action. -/
def SubDeriv.comp {Γ : RawContext n} {Δ : RawContext m} {Θ : RawContext k}
    {σ : Substitution n m} {τ : Substitution m k}
    (d : SubDeriv Γ Δ σ) (e : SubDeriv Δ Θ τ) :
    SubDeriv Γ Θ (fun i => (σ i).subst τ) where
  source := d.source
  target := e.target
  lookup := fun i => by simpa only [Ty.subst_comp] using (d.lookup i).substitute e

/-- The one-variable substitution used by beta conversion is actually typed. -/
def SubDeriv.single {Γ : RawContext n} {a : Ty n} {u : Term n}
    (domain : FormTy Γ a) (argument : Typing Γ u a) :
    SubDeriv (Γ.snoc a) Γ (Substitution.single u) where
  source := .snoc domain.context domain
  target := domain.context
  lookup := fun i => Fin.cases
    (by simpa only [Substitution.single_zero, RawContext.lookup_zero,
      Ty.subst_single_weaken] using argument)
    (fun j => by simpa only [Substitution.single_succ, RawContext.lookup_succ,
      Ty.subst_single_weaken] using Typing.var j domain.context) i

/-- Raw pairing, with the newest variable first in de Bruijn order. -/
def Substitution.pair (σ : Substitution n m) (u : Term m) : Substitution (n + 1) m :=
  Fin.cases u σ

def SubDeriv.pair {Γ : RawContext n} {Δ : RawContext m} {σ : Substitution n m}
    (d : SubDeriv Γ Δ σ) {a : Ty n} (domain : FormTy Γ a) {u : Term m}
    (argument : Typing Δ u (a.subst σ)) :
    SubDeriv (Γ.snoc a) Δ (Substitution.pair σ u) where
  source := .snoc d.source domain
  target := d.target
  lookup := fun i => Fin.cases
    (by simpa only [Substitution.pair, RawContext.lookup_zero, Ty.weaken,
      Ty.subst_rename, Function.comp_def, Fin.cases_succ, Fin.cases_zero] using argument)
    (fun j => by simpa only [Substitution.pair, RawContext.lookup_succ, Ty.weaken,
      Ty.subst_rename, Function.comp_def, Fin.cases_succ] using d.lookup j) i

/-- In particular the beta reduct receives an actual typing derivation. -/
def Typing.instantiate {Γ : RawContext n} {a : Ty n} {b : TyAbs n} {body : Abs n}
    (d : Typing (Γ.snoc a) body.open b.open)
    (domain : FormTy Γ a) {u : Term n} (argument : Typing Γ u a) :
    Typing Γ (body.instantiate u) (b.instantiate u) :=
  d.substitute (SubDeriv.single domain argument)

def SpineTyping.rename {Γ : RawContext n} {f : Term n} {a b : Ty n} {es : Spine n}
    (d : SpineTyping Γ f a es b) {Δ : RawContext m}
    (ρ : Renaming n m) (hρ : ρ.Respects Γ Δ) (formed : FormCtx Δ) :
    SpineTyping Δ (f.rename ρ) (a.rename ρ) (es.map (Elim.rename ρ)) (b.rename ρ) :=
  match d with
  | .nil h => .nil (h.rename ρ hρ formed)
  | .cons (b := b) df du rest => by
      have rf := df.rename ρ hρ formed
      have rr := rest.rename ρ hρ formed
      simpa only [Ty.pi_rename, List.map_cons, Elim.rename] using
        SpineTyping.cons (b := b.rename ρ)
          (by simpa only [Ty.pi_rename] using rf) (du.rename ρ hρ formed)
          (by simpa only [Term.app_rename, TyAbs.instantiate_rename] using rr)
termination_by structural d

def SpineTyping.substitute {Γ : RawContext n} {f : Term n} {a b : Ty n} {es : Spine n}
    (d : SpineTyping Γ f a es b) {Δ : RawContext m} {σ : Substitution n m}
    (hσ : SubDeriv Γ Δ σ) :
    SpineTyping Δ (f.subst σ) (a.subst σ) (es.map (Elim.subst σ)) (b.subst σ) :=
  match d with
  | .nil h => .nil (h.substitute hσ)
  | .cons (b := b) df du rest => by
      have rf := df.substitute hσ
      have rr := rest.substitute hσ
      simpa only [Ty.pi_subst, List.map_cons, Elim.subst] using
        SpineTyping.cons (b := b.subst σ)
          (by simpa only [Ty.pi_subst] using rf) (du.substitute hσ)
          (by simpa only [Term.app_subst, TyAbs.instantiate_subst] using rr)
termination_by structural d

end Mettapedia.Languages.Agda.StaticSpecification
