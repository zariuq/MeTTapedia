import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.AwodeyButzApplicativeSubstitution

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

universe u v w

/--
Archive-free higher-order applicative interpretations whose application and
lambda operations are stable under context reindexing.
-/
structure ReindexableApplicativeTopologicalInterpretation
    (Base : Type u) (Const : Ty Base → Type v)
    (X : Type w) [TopologicalSpace X] where
  toApplicative : ApplicativeTopologicalInterpretation Base Const X
  app_reindex :
    ∀ {Γ Δ : Ctx Base} {σ τ : Ty Base}
      (f : toApplicative.toBasic.CtxTerm Γ (σ ⇒ τ))
      (t : toApplicative.toBasic.CtxTerm Γ σ)
      (ρ : toApplicative.toBasic.CtxHom Δ Γ),
      (toApplicative.app f t).reindex ρ =
        toApplicative.app (f.reindex ρ) (t.reindex ρ)
  lam_reindex :
    ∀ {Γ Δ : Ctx Base} {σ τ : Ty Base}
      (t : toApplicative.toBasic.CtxTerm (σ :: Γ) τ)
      (ρ : toApplicative.toBasic.CtxHom Δ Γ),
      (toApplicative.lam t).reindex ρ =
        toApplicative.lam
          (t.reindex
            (EtaleSpace.BasicTopologicalInterpretation.CtxHom.lift
              (I := toApplicative.toBasic) (τ := σ) ρ))

namespace ReindexableApplicativeTopologicalInterpretation

variable {Base : Type u} {Const : Ty Base → Type v}
variable {X : Type w} [TopologicalSpace X]

instance :
    Coe (ReindexableApplicativeTopologicalInterpretation Base Const X)
      (ApplicativeTopologicalInterpretation Base Const X) where
  coe := ReindexableApplicativeTopologicalInterpretation.toApplicative

variable (I : ReindexableApplicativeTopologicalInterpretation Base Const X)
variable {Γ Δ : Ctx Base} {σ τ υ : Ty Base}

/-- Application commutes with reindexing along any semantic context morphism. -/
@[simp] theorem app_reindex_apply
    (f : I.toApplicative.toBasic.CtxTerm Γ (σ ⇒ τ))
    (t : I.toApplicative.toBasic.CtxTerm Γ σ)
    (ρ : I.toApplicative.toBasic.CtxHom Δ Γ) :
    (I.toApplicative.app f t).reindex ρ =
      I.toApplicative.app (f.reindex ρ) (t.reindex ρ) :=
  I.app_reindex f t ρ

/--
Specialization of applicative reindexing to weakening by a new head variable in
the context.
-/
@[simp] theorem app_weaken
    (f : I.toApplicative.toBasic.CtxTerm Γ (σ ⇒ τ))
    (t : I.toApplicative.toBasic.CtxTerm Γ σ) :
    (I.toApplicative.app f t).weaken υ =
      I.toApplicative.app (f.weaken υ) (t.weaken υ) := by
  rw [EtaleSpace.BasicTopologicalInterpretation.CtxTerm.weaken]
  rw [EtaleSpace.BasicTopologicalInterpretation.CtxTerm.weaken]
  rw [EtaleSpace.BasicTopologicalInterpretation.CtxTerm.weaken]
  exact
    I.app_reindex f t
      (EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
        I.toApplicative.toBasic υ Γ)

/-- Lambda abstraction commutes with reindexing along any semantic context morphism. -/
@[simp] theorem lam_reindex_apply
    (t : I.toApplicative.toBasic.CtxTerm (σ :: Γ) τ)
    (ρ : I.toApplicative.toBasic.CtxHom Δ Γ) :
    (I.toApplicative.lam t).reindex ρ =
      I.toApplicative.lam
        (t.reindex
          (EtaleSpace.BasicTopologicalInterpretation.CtxHom.lift
            (I := I.toApplicative.toBasic) (τ := σ) ρ)) :=
  I.lam_reindex t ρ

/--
Specialization of lambda reindexing to weakening by a new head variable in the
ambient context.
-/
@[simp] theorem lam_weaken
    (t : I.toApplicative.toBasic.CtxTerm (σ :: Γ) τ) :
    (I.toApplicative.lam t).weaken υ =
      I.toApplicative.lam
        (t.reindex
          (EtaleSpace.BasicTopologicalInterpretation.CtxHom.lift
            (I := I.toApplicative.toBasic) (τ := σ)
            (EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
              I.toApplicative.toBasic υ Γ))) := by
  rw [EtaleSpace.BasicTopologicalInterpretation.CtxTerm.weaken]
  exact
    I.lam_reindex t
      (EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
        I.toApplicative.toBasic υ Γ)

/--
Reindexing a lambda along the identity context morphism is definitionally
trivial after transporting the body along the lifted identity.
-/
@[simp] theorem lam_reindex_id
    (t : I.toApplicative.toBasic.CtxTerm (σ :: Γ) τ) :
    (I.toApplicative.lam t).reindex
        (EtaleSpace.BasicTopologicalInterpretation.CtxHom.id
          I.toApplicative.toBasic Γ) =
      I.toApplicative.lam t := by
  rw [I.lam_reindex]
  rw [show EtaleSpace.BasicTopologicalInterpretation.CtxHom.lift
      (I := I.toApplicative.toBasic) (τ := σ)
      (EtaleSpace.BasicTopologicalInterpretation.CtxHom.id
        I.toApplicative.toBasic Γ) =
    EtaleSpace.BasicTopologicalInterpretation.CtxHom.id
      I.toApplicative.toBasic (σ :: Γ) by
        simp [EtaleSpace.BasicTopologicalInterpretation.CtxHom.lift]]
  simp

/--
Reindexing an applicative application along the identity context morphism is
definitionally trivial.
-/
@[simp] theorem app_reindex_id
    (f : I.toApplicative.toBasic.CtxTerm Γ (σ ⇒ τ))
    (t : I.toApplicative.toBasic.CtxTerm Γ σ) :
    (I.toApplicative.app f t).reindex
        (EtaleSpace.BasicTopologicalInterpretation.CtxHom.id
          I.toApplicative.toBasic Γ) =
      I.toApplicative.app f t := by
  rw [I.app_reindex]
  simp

end ReindexableApplicativeTopologicalInterpretation

namespace ApplicativeTerm

variable {Base : Type u} {Const : Ty Base → Type v}
variable {X : Type w} [TopologicalSpace X]

variable (I : ReindexableApplicativeTopologicalInterpretation Base Const X)
variable {Γ Δ : Ctx Base} {σ τ υ : Ty Base}

def renameTail (ρ : Rename Base (σ :: Γ) Δ) : Rename Base Γ Δ :=
  fun {_} x => ρ (.vs x)

@[simp] theorem renameTail_apply
    (ρ : Rename Base (σ :: Γ) Δ) (x : Var Γ τ) :
    renameTail (σ := σ) (Γ := Γ) ρ x = ρ (.vs x) :=
  rfl

def weakenRename (ρ : Rename Base Γ Δ) : Rename Base Γ (σ :: Δ) :=
  fun {_} x => .vs (ρ x)

@[simp] theorem weakenRename_apply
    (ρ : Rename Base Γ Δ) (x : Var Γ τ) :
    weakenRename (σ := σ) ρ x = .vs (ρ x) :=
  rfl

def evalRename :
    {Γ Δ : Ctx Base} →
      Rename Base Γ Δ → I.toApplicative.toBasic.CtxHom Δ Γ
  | [], Δ, _ =>
      EtaleSpace.BasicTopologicalInterpretation.CtxHom.terminal I.toApplicative.toBasic Δ
  | σ :: Γ, Δ, ρ =>
      EtaleSpace.BasicTopologicalInterpretation.CtxTerm.cons
        (EtaleSpace.BasicTopologicalInterpretation.CtxTerm.var
          I.toApplicative.toBasic (ρ (Var.vz : Var (σ :: Γ) σ)))
        (evalRename (Γ := Γ) (Δ := Δ)
          (renameTail (σ := σ) (Γ := Γ) ρ))

@[simp] theorem var_reindex_evalRename
    (ρ : Rename Base Γ Δ) (x : Var Γ τ) :
    (EtaleSpace.BasicTopologicalInterpretation.CtxTerm.var
        I.toApplicative.toBasic x).reindex (evalRename I (Γ := Γ) (Δ := Δ) ρ) =
      EtaleSpace.BasicTopologicalInterpretation.CtxTerm.var
        I.toApplicative.toBasic (ρ x) := by
  induction x generalizing Δ with
  | vz =>
      simp [evalRename]
  | @vs Γ τ σ x ih =>
      calc
        (EtaleSpace.BasicTopologicalInterpretation.CtxTerm.var
            I.toApplicative.toBasic (.vs x)).reindex
              (evalRename I (Γ := σ :: Γ) (Δ := Δ) ρ)
            =
          (EtaleSpace.BasicTopologicalInterpretation.CtxTerm.var
            I.toApplicative.toBasic x).reindex
              (evalRename I (Γ := Γ) (Δ := Δ)
                (renameTail (σ := σ) (Γ := Γ) ρ)) := by
                rw [evalRename]
                exact
                  (EtaleSpace.BasicTopologicalInterpretation.CtxTerm.var_vs_reindex_cons
                    (I := I.toApplicative.toBasic)
                    (x := x)
                    (t := EtaleSpace.BasicTopologicalInterpretation.CtxTerm.var
                      I.toApplicative.toBasic (ρ (Var.vz : Var (σ :: Γ) σ)))
                    (σ := evalRename I (Γ := Γ) (Δ := Δ)
                      (renameTail (σ := σ) (Γ := Γ) ρ)))
        _ =
          EtaleSpace.BasicTopologicalInterpretation.CtxTerm.var
            I.toApplicative.toBasic ((renameTail (σ := σ) (Γ := Γ) ρ) x) := by
              exact ih (Δ := Δ) (ρ := renameTail (σ := σ) (Γ := Γ) ρ)
        _ =
          EtaleSpace.BasicTopologicalInterpretation.CtxTerm.var
            I.toApplicative.toBasic (ρ (.vs x)) :=
          rfl

@[simp] theorem evalRename_tail
    (ρ : Rename Base (σ :: Γ) Δ) :
    (evalRename I (Γ := σ :: Γ) (Δ := Δ) ρ).comp
        (EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
          I.toApplicative.toBasic σ Γ) =
      evalRename I (Γ := Γ) (Δ := Δ) (renameTail (σ := σ) (Γ := Γ) ρ) := by
  rw [evalRename]
  exact
    (EtaleSpace.BasicTopologicalInterpretation.CtxTerm.tail_cons
      (I := I.toApplicative.toBasic)
      (t := EtaleSpace.BasicTopologicalInterpretation.CtxTerm.var
        I.toApplicative.toBasic (ρ (Var.vz : Var (σ :: Γ) σ)))
      (σ := evalRename I (Γ := Γ) (Δ := Δ)
        (renameTail (σ := σ) (Γ := Γ) ρ)))

@[simp] theorem evalRename_weaken
    (ρ : Rename Base Γ Δ) :
    evalRename I (Γ := Γ) (Δ := σ :: Δ) (weakenRename (σ := σ) ρ) =
      (EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
        I.toApplicative.toBasic σ Δ).comp
          (evalRename I (Γ := Γ) (Δ := Δ) ρ) := by
  induction Γ generalizing Δ with
  | nil =>
      exact
        (EtaleSpace.BasicTopologicalInterpretation.CtxHom.toEmpty_eq_terminal
          (I := I.toApplicative.toBasic)
          (σ := (EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
            I.toApplicative.toBasic σ Δ).comp (evalRename I (Γ := []) (Δ := Δ) ρ))).symm
  | cons τ Γ ih =>
      let rhs :
          I.toApplicative.toBasic.CtxHom (σ :: Δ) (τ :: Γ) :=
        (EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
          I.toApplicative.toBasic σ Δ).comp
            (evalRename I (Γ := τ :: Γ) (Δ := Δ) ρ)
      have hhead :
          (EtaleSpace.BasicTopologicalInterpretation.CtxTerm.head
              I.toApplicative.toBasic τ Γ).reindex rhs =
            EtaleSpace.BasicTopologicalInterpretation.CtxTerm.var
              I.toApplicative.toBasic
              ((weakenRename (σ := σ) ρ) (Var.vz : Var (τ :: Γ) τ)) := by
        calc
          (EtaleSpace.BasicTopologicalInterpretation.CtxTerm.head
              I.toApplicative.toBasic τ Γ).reindex rhs
              =
            ((EtaleSpace.BasicTopologicalInterpretation.CtxTerm.head
                I.toApplicative.toBasic τ Γ).reindex
                (evalRename I (Γ := τ :: Γ) (Δ := Δ) ρ)).reindex
                  (EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
                    I.toApplicative.toBasic σ Δ) := by
                      symm
                      exact
                        EtaleSpace.BasicTopologicalInterpretation.CtxTerm.reindex_comp
                          (t := EtaleSpace.BasicTopologicalInterpretation.CtxTerm.head
                            I.toApplicative.toBasic τ Γ)
                          (σ := EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
                            I.toApplicative.toBasic σ Δ)
                          (ρ := evalRename I (Γ := τ :: Γ) (Δ := Δ) ρ)
          _ =
            ((EtaleSpace.BasicTopologicalInterpretation.CtxTerm.var
                I.toApplicative.toBasic (ρ (Var.vz : Var (τ :: Γ) τ))).reindex
                  (EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
                    I.toApplicative.toBasic σ Δ)) := by
                      simpa [EtaleSpace.BasicTopologicalInterpretation.CtxTerm.var_vz]
                        using congrArg
                          (fun t =>
                            t.reindex
                              (EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
                                I.toApplicative.toBasic σ Δ))
                          (var_reindex_evalRename (I := I) (Γ := τ :: Γ) (Δ := Δ)
                            (ρ := ρ) (x := (Var.vz : Var (τ :: Γ) τ)))
          _ =
            EtaleSpace.BasicTopologicalInterpretation.CtxTerm.var
              I.toApplicative.toBasic
              (Var.vs (σ := σ) (ρ (Var.vz : Var (τ :: Γ) τ))) := by
                simp [EtaleSpace.BasicTopologicalInterpretation.CtxTerm.var_vs,
                  EtaleSpace.BasicTopologicalInterpretation.CtxTerm.weaken]
          _ =
            EtaleSpace.BasicTopologicalInterpretation.CtxTerm.var
              I.toApplicative.toBasic
              ((weakenRename (σ := σ) ρ) (Var.vz : Var (τ :: Γ) τ)) := by
                rfl
      have htail :
          rhs.comp
              (EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
                I.toApplicative.toBasic τ Γ) =
            evalRename I (Γ := Γ) (Δ := σ :: Δ)
              (renameTail (σ := τ) (Γ := Γ) (weakenRename (σ := σ) ρ)) := by
        calc
          rhs.comp
              (EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
                I.toApplicative.toBasic τ Γ)
              =
            (EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
              I.toApplicative.toBasic σ Δ).comp
                ((evalRename I (Γ := τ :: Γ) (Δ := Δ) ρ).comp
                  (EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
                    I.toApplicative.toBasic τ Γ)) := by
                      exact
                        EtaleSpace.BasicTopologicalInterpretation.CtxHom.comp_assoc
                          (σ := EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
                            I.toApplicative.toBasic σ Δ)
                          (ρ := evalRename I (Γ := τ :: Γ) (Δ := Δ) ρ)
                          (θ := EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
                            I.toApplicative.toBasic τ Γ)
          _ =
            (EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
              I.toApplicative.toBasic σ Δ).comp
                (evalRename I (Γ := Γ) (Δ := Δ)
                  (renameTail (σ := τ) (Γ := Γ) ρ)) := by
                    rw [evalRename_tail (I := I) (σ := τ) (Γ := Γ) (Δ := Δ) (ρ := ρ)]
          _ =
            evalRename I (Γ := Γ) (Δ := σ :: Δ)
              (weakenRename (σ := σ) (renameTail (σ := τ) (Γ := Γ) ρ)) := by
                symm
                exact ih (Δ := Δ) (ρ := renameTail (σ := τ) (Γ := Γ) ρ)
          _ =
            evalRename I (Γ := Γ) (Δ := σ :: Δ)
              (renameTail (σ := τ) (Γ := Γ) (weakenRename (σ := σ) ρ)) := by
                rfl
      calc
        evalRename I (Γ := τ :: Γ) (Δ := σ :: Δ)
            (weakenRename (σ := σ) ρ)
            =
          EtaleSpace.BasicTopologicalInterpretation.CtxTerm.cons
            (EtaleSpace.BasicTopologicalInterpretation.CtxTerm.var
              I.toApplicative.toBasic
              ((weakenRename (σ := σ) ρ) (Var.vz : Var (τ :: Γ) τ)))
            (evalRename I (Γ := Γ) (Δ := σ :: Δ)
              (renameTail (σ := τ) (Γ := Γ) (weakenRename (σ := σ) ρ))) := by
                simp [evalRename]
        _ =
          EtaleSpace.BasicTopologicalInterpretation.CtxTerm.cons
            ((EtaleSpace.BasicTopologicalInterpretation.CtxTerm.head
              I.toApplicative.toBasic τ Γ).reindex rhs)
            (rhs.comp
              (EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
                I.toApplicative.toBasic τ Γ)) := by
                  rw [hhead, htail]
        _ = rhs := by
          exact
            EtaleSpace.BasicTopologicalInterpretation.CtxHom.cons_reconstruct
              (I := I.toApplicative.toBasic)
              (Γ := σ :: Δ)
              (Δ := Γ)
              (τ := τ)
              rhs

@[simp] theorem evalRename_lift
    (ρ : Rename Base Γ Δ) :
    evalRename I (Γ := σ :: Γ) (Δ := σ :: Δ)
        (Rename.lift (Base := Base) (Γ := Γ) (Δ := Δ) (σ := σ) ρ) =
      EtaleSpace.BasicTopologicalInterpretation.CtxHom.lift
        (I := I.toApplicative.toBasic) (τ := σ)
        (evalRename I (Γ := Γ) (Δ := Δ) ρ) := by
  calc
    evalRename I (Γ := σ :: Γ) (Δ := σ :: Δ)
        (Rename.lift (Base := Base) (Γ := Γ) (Δ := Δ) (σ := σ) ρ)
        =
      EtaleSpace.BasicTopologicalInterpretation.CtxTerm.cons
        (EtaleSpace.BasicTopologicalInterpretation.CtxTerm.var
          I.toApplicative.toBasic
            ((Rename.lift (Base := Base) (Γ := Γ) (Δ := Δ) (σ := σ) ρ)
              (Var.vz : Var (σ :: Γ) σ)))
        (evalRename I (Γ := Γ) (Δ := σ :: Δ)
          (renameTail (σ := σ) (Γ := Γ)
            (Rename.lift (Base := Base) (Γ := Γ) (Δ := Δ) (σ := σ) ρ))) := by
              simp [evalRename]
    _ =
      EtaleSpace.BasicTopologicalInterpretation.CtxTerm.cons
        (EtaleSpace.BasicTopologicalInterpretation.CtxTerm.head
          I.toApplicative.toBasic σ Δ)
        (evalRename I (Γ := Γ) (Δ := σ :: Δ)
          (renameTail (σ := σ) (Γ := Γ)
            (Rename.lift (Base := Base) (Γ := Γ) (Δ := Δ) (σ := σ) ρ))) := by
              simp [Rename.lift, EtaleSpace.BasicTopologicalInterpretation.CtxTerm.var_vz]
    _ =
      EtaleSpace.BasicTopologicalInterpretation.CtxTerm.cons
        (EtaleSpace.BasicTopologicalInterpretation.CtxTerm.head
          I.toApplicative.toBasic σ Δ)
        ((EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
          I.toApplicative.toBasic σ Δ).comp
            (evalRename I (Γ := Γ) (Δ := Δ) ρ)) := by
              congr
              change
                evalRename I (Γ := Γ) (Δ := σ :: Δ) (weakenRename (σ := σ) ρ) =
                  (EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
                    I.toApplicative.toBasic σ Δ).comp
                      (evalRename I (Γ := Γ) (Δ := Δ) ρ)
              exact evalRename_weaken (I := I) (Γ := Γ) (Δ := Δ) (σ := σ) (ρ := ρ)
    _ =
      EtaleSpace.BasicTopologicalInterpretation.CtxHom.lift
        (I := I.toApplicative.toBasic) (τ := σ)
        (evalRename I (Γ := Γ) (Δ := Δ) ρ) := by
          rfl

@[simp] theorem eval_rename
    (ρ : Rename Base Γ Δ)
    (t : ApplicativeTerm Base Const Γ τ) :
    ApplicativeTopologicalInterpretation.evalTerm I.toApplicative
        (ApplicativeTerm.rename ρ t) =
      (ApplicativeTopologicalInterpretation.evalTerm I.toApplicative t).reindex
        (evalRename I (Γ := Γ) (Δ := Δ) ρ) := by
  induction t generalizing Δ with
  | @var Γ τ v =>
      exact (var_reindex_evalRename (I := I) (ρ := ρ) (x := v)).symm
  | @const τ Γ c =>
      exact
        (EtaleSpace.BasicTopologicalInterpretation.CtxTerm.const_reindex
          (I := I.toApplicative.toBasic)
          (Γ := Γ)
          (Δ := Δ)
          (t := evalRename I (Γ := Γ) (Δ := Δ) ρ)
          (τ := τ)
          c).symm
  | @app Γ σ τ f t ihf iht =>
      calc
        ApplicativeTopologicalInterpretation.evalTerm I.toApplicative
            (ApplicativeTerm.rename ρ (.app f t))
            =
          I.toApplicative.app
            (ApplicativeTopologicalInterpretation.evalTerm I.toApplicative
              (ApplicativeTerm.rename ρ f))
            (ApplicativeTopologicalInterpretation.evalTerm I.toApplicative
              (ApplicativeTerm.rename ρ t)) := by
                rfl
        _ =
          I.toApplicative.app
            ((ApplicativeTopologicalInterpretation.evalTerm I.toApplicative f).reindex
              (evalRename I (Γ := Γ) (Δ := Δ) ρ))
            ((ApplicativeTopologicalInterpretation.evalTerm I.toApplicative t).reindex
              (evalRename I (Γ := Γ) (Δ := Δ) ρ)) := by
                rw [ihf (Δ := Δ) (ρ := ρ), iht (Δ := Δ) (ρ := ρ)]
        _ =
          (I.toApplicative.app
            (ApplicativeTopologicalInterpretation.evalTerm I.toApplicative f)
            (ApplicativeTopologicalInterpretation.evalTerm I.toApplicative t)).reindex
              (evalRename I (Γ := Γ) (Δ := Δ) ρ) := by
                exact
                  (I.app_reindex
                    (ApplicativeTopologicalInterpretation.evalTerm I.toApplicative f)
                    (ApplicativeTopologicalInterpretation.evalTerm I.toApplicative t)
                    (evalRename I (Γ := Γ) (Δ := Δ) ρ)).symm
  | @lam σ Γ τ t ih =>
      calc
        ApplicativeTopologicalInterpretation.evalTerm I.toApplicative
            (ApplicativeTerm.rename ρ (.lam t))
            =
          I.toApplicative.lam
            (ApplicativeTopologicalInterpretation.evalTerm I.toApplicative
              (ApplicativeTerm.rename
                (Rename.lift (Base := Base) (σ := _) ρ) t)) := by
                  rfl
        _ =
          I.toApplicative.lam
            ((ApplicativeTopologicalInterpretation.evalTerm I.toApplicative t).reindex
              (evalRename I (Γ := σ :: Γ) (Δ := σ :: Δ)
                (Rename.lift (Base := Base) (Γ := Γ) (Δ := Δ) (σ := σ) ρ))) := by
                  rw [ih (Δ := σ :: Δ)
                    (ρ := Rename.lift (Base := Base) (Γ := Γ) (Δ := Δ) (σ := σ) ρ)]
        _ =
          I.toApplicative.lam
            ((ApplicativeTopologicalInterpretation.evalTerm I.toApplicative t).reindex
              (EtaleSpace.BasicTopologicalInterpretation.CtxHom.lift
                (I := I.toApplicative.toBasic) (τ := σ)
                (evalRename I (Γ := Γ) (Δ := Δ) ρ))) := by
                  rw [@evalRename_lift Base Const X _ I Γ Δ σ ρ]
        _ =
          (I.toApplicative.lam
            (ApplicativeTopologicalInterpretation.evalTerm I.toApplicative t)).reindex
              (evalRename I (Γ := Γ) (Δ := Δ) ρ) := by
                exact
                  (I.lam_reindex
                    (ApplicativeTopologicalInterpretation.evalTerm I.toApplicative t)
                    (evalRename I (Γ := Γ) (Δ := Δ) ρ)).symm

@[simp] theorem evalRename_id :
    evalRename I (Γ := Γ) (Δ := Γ)
        (Mettapedia.Logic.HOL.Rename.id (Base := Base) (Γ := Γ)) =
      EtaleSpace.BasicTopologicalInterpretation.CtxHom.id
        I.toApplicative.toBasic Γ := by
  induction Γ with
  | nil =>
      exact
        (EtaleSpace.BasicTopologicalInterpretation.CtxHom.toEmpty_eq_terminal
          (I := I.toApplicative.toBasic)
          (σ := EtaleSpace.BasicTopologicalInterpretation.CtxHom.id
            I.toApplicative.toBasic [])).symm
  | cons σ Γ ih =>
      calc
        evalRename I (Γ := σ :: Γ) (Δ := σ :: Γ)
            (Mettapedia.Logic.HOL.Rename.id (Base := Base) (Γ := σ :: Γ)) =
          evalRename I (Γ := σ :: Γ) (Δ := σ :: Γ)
            (Mettapedia.Logic.HOL.Rename.lift
              (Base := Base) (Γ := Γ) (Δ := Γ) (σ := σ)
              (Mettapedia.Logic.HOL.Rename.id (Base := Base) (Γ := Γ))) := by
                rfl
        _ =
          EtaleSpace.BasicTopologicalInterpretation.CtxHom.lift
            (I := I.toApplicative.toBasic) (τ := σ)
              (evalRename I (Γ := Γ) (Δ := Γ)
                (Mettapedia.Logic.HOL.Rename.id (Base := Base) (Γ := Γ))) := by
                  exact
                    (evalRename_lift (I := I)
                      (Γ := Γ)
                      (Δ := Γ)
                      (σ := σ)
                      (ρ := Mettapedia.Logic.HOL.Rename.id (Base := Base) (Γ := Γ)))
        _ =
          EtaleSpace.BasicTopologicalInterpretation.CtxHom.lift
            (I := I.toApplicative.toBasic) (τ := σ)
              (EtaleSpace.BasicTopologicalInterpretation.CtxHom.id
                I.toApplicative.toBasic Γ) := by
                  rw [ih]
        _ =
          EtaleSpace.BasicTopologicalInterpretation.CtxHom.id
            I.toApplicative.toBasic (σ :: Γ) := by
              simp [EtaleSpace.BasicTopologicalInterpretation.CtxHom.lift]

@[simp] theorem evalRename_weaken_eq_tail :
    evalRename I (Γ := Γ) (Δ := υ :: Γ)
        (Rename.weaken (Base := Base) (Γ := Γ) (σ := υ)) =
      EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
        I.toApplicative.toBasic υ Γ := by
  calc
    evalRename I (Γ := Γ) (Δ := υ :: Γ)
        (Rename.weaken (Base := Base) (Γ := Γ) (σ := υ)) =
      evalRename I (Γ := Γ) (Δ := υ :: Γ)
        (weakenRename (σ := υ)
          (Mettapedia.Logic.HOL.Rename.id (Base := Base) (Γ := Γ))) := by
            rfl
    _ =
      (EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
        I.toApplicative.toBasic υ Γ).comp
          (evalRename I (Γ := Γ) (Δ := Γ)
            (Mettapedia.Logic.HOL.Rename.id (Base := Base) (Γ := Γ))) := by
              exact
                (evalRename_weaken (I := I)
                  (Γ := Γ)
                  (Δ := Γ)
                  (σ := υ)
                  (ρ := Mettapedia.Logic.HOL.Rename.id (Base := Base) (Γ := Γ)))
    _ =
      (EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
        I.toApplicative.toBasic υ Γ).comp
          (EtaleSpace.BasicTopologicalInterpretation.CtxHom.id
            I.toApplicative.toBasic Γ) := by
              rw [evalRename_id (I := I) (Γ := Γ)]
    _ =
      EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
        I.toApplicative.toBasic υ Γ := by
          simp

@[simp] theorem eval_weaken
    (t : ApplicativeTerm Base Const Γ τ) :
    ApplicativeTopologicalInterpretation.evalTerm I.toApplicative
        (ApplicativeTerm.weaken (Base := Base) (Const := Const) (υ := υ) t) =
      (ApplicativeTopologicalInterpretation.evalTerm I.toApplicative t).weaken υ := by
  calc
    ApplicativeTopologicalInterpretation.evalTerm I.toApplicative
        (ApplicativeTerm.weaken (Base := Base) (Const := Const) (υ := υ) t) =
      (ApplicativeTopologicalInterpretation.evalTerm I.toApplicative t).reindex
        (evalRename I (Γ := Γ) (Δ := υ :: Γ)
          (Rename.weaken (Base := Base) (Γ := Γ) (σ := υ))) := by
            change
              ApplicativeTopologicalInterpretation.evalTerm I.toApplicative
                  (ApplicativeTerm.rename
                    (Rename.weaken (Base := Base) (Γ := Γ) (σ := υ)) t) =
                (ApplicativeTopologicalInterpretation.evalTerm I.toApplicative t).reindex
                  (evalRename I (Γ := Γ) (Δ := υ :: Γ)
                    (Rename.weaken (Base := Base) (Γ := Γ) (σ := υ)))
            exact
              (eval_rename (I := I)
                (Γ := Γ)
                (Δ := υ :: Γ)
                (τ := τ)
                (ρ := Rename.weaken (Base := Base) (Γ := Γ) (σ := υ))
                (t := t))
    _ =
      (ApplicativeTopologicalInterpretation.evalTerm I.toApplicative t).reindex
        (EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
          I.toApplicative.toBasic υ Γ) := by
            rw [evalRename_weaken_eq_tail (I := I) (Γ := Γ) (υ := υ)]
    _ =
      (ApplicativeTopologicalInterpretation.evalTerm I.toApplicative t).weaken υ := by
        rfl

end ApplicativeTerm

private def applicativeSubstEval
    {Base : Type u} {Const : Ty Base → Type v}
    {X : Type w} [TopologicalSpace X]
    (I : ReindexableApplicativeTopologicalInterpretation Base Const X) :
    {Γ Δ : Ctx Base} →
      ApplicativeSubst Base Const Γ Δ → I.toApplicative.toBasic.CtxHom Δ Γ
  | [], Δ, _ =>
      EtaleSpace.BasicTopologicalInterpretation.CtxHom.terminal
        I.toApplicative.toBasic Δ
  | σ :: Γ, Δ, σs =>
      let tailσs : ApplicativeSubst Base Const Γ Δ := fun {τ} x => @σs τ (.vs x)
      EtaleSpace.BasicTopologicalInterpretation.CtxTerm.cons
        (ApplicativeTopologicalInterpretation.evalTerm I.toApplicative
          (@σs σ (Var.vz : Var (σ :: Γ) σ)))
        (applicativeSubstEval I tailσs)

namespace ApplicativeSubst

variable {Base : Type u} {Const : Ty Base → Type v}
variable {X : Type w} [TopologicalSpace X]

variable (I : ReindexableApplicativeTopologicalInterpretation Base Const X)
variable {Γ Δ Ξ : Ctx Base} {σ τ υ : Ty Base}

/-- Interpret an applicative substitution as a semantic context morphism. -/
def eval :
    {Γ Δ : Ctx Base} →
      ApplicativeSubst Base Const Γ Δ → I.toApplicative.toBasic.CtxHom Δ Γ
  | Γ, Δ, σs => applicativeSubstEval I (Γ := Γ) (Δ := Δ) σs

@[simp] theorem eval_nil
    (σs : ApplicativeSubst Base Const [] Δ) :
    eval I σs =
      EtaleSpace.BasicTopologicalInterpretation.CtxHom.terminal
        I.toApplicative.toBasic Δ :=
  rfl

@[simp] theorem eval_cons
    (σs : ApplicativeSubst Base Const (σ :: Γ) Δ) :
    eval I σs =
      EtaleSpace.BasicTopologicalInterpretation.CtxTerm.cons
        (ApplicativeTopologicalInterpretation.evalTerm I.toApplicative
          (@σs σ (Var.vz : Var (σ :: Γ) σ)))
        (eval I (Γ := Γ) (Δ := Δ)
          (fun {τ} x => @σs τ (.vs x))) :=
  rfl

@[simp] theorem var_reindex_eval
    (σs : ApplicativeSubst Base Const Γ Δ) (x : Var Γ τ) :
    (EtaleSpace.BasicTopologicalInterpretation.CtxTerm.var
        I.toApplicative.toBasic x).reindex (eval I (Γ := Γ) (Δ := Δ) σs) =
      ApplicativeTopologicalInterpretation.evalTerm I.toApplicative (σs x) := by
  induction x generalizing Δ with
  | @vz τ' Γ' =>
      change
        (EtaleSpace.BasicTopologicalInterpretation.CtxTerm.head
          I.toApplicative.toBasic τ' Γ').reindex
            (EtaleSpace.BasicTopologicalInterpretation.CtxTerm.cons
              (ApplicativeTopologicalInterpretation.evalTerm I.toApplicative
                (@σs τ' (Var.vz : Var (τ' :: Γ') τ')))
              (applicativeSubstEval I
                (fun {ρ} (y : Var Γ' ρ) => @σs ρ (.vs y)))) =
          ApplicativeTopologicalInterpretation.evalTerm I.toApplicative
            (@σs τ' (Var.vz : Var (τ' :: Γ') τ'))
      exact
        EtaleSpace.BasicTopologicalInterpretation.CtxTerm.head_reindex_cons
          (I := I.toApplicative.toBasic)
          (t := ApplicativeTopologicalInterpretation.evalTerm I.toApplicative
            (@σs τ' (Var.vz : Var (τ' :: Γ') τ')))
          (σ := applicativeSubstEval I (fun {ρ} (y : Var Γ' ρ) => @σs ρ (.vs y)))
  | @vs Γ' υ' τ' x ih =>
      let tailσs : ApplicativeSubst Base Const Γ' Δ := fun {ρ} (y : Var Γ' ρ) => @σs ρ (.vs y)
      calc
        (EtaleSpace.BasicTopologicalInterpretation.CtxTerm.var
            I.toApplicative.toBasic (.vs x)).reindex
              (eval I (Γ := τ' :: Γ') (Δ := Δ) σs)
            =
          (EtaleSpace.BasicTopologicalInterpretation.CtxTerm.var
            I.toApplicative.toBasic x).reindex
              (applicativeSubstEval I tailσs) := by
                change
                  (EtaleSpace.BasicTopologicalInterpretation.CtxTerm.var
                    I.toApplicative.toBasic (.vs x)).reindex
                      (EtaleSpace.BasicTopologicalInterpretation.CtxTerm.cons
                        (ApplicativeTopologicalInterpretation.evalTerm I.toApplicative
                          (@σs τ' (Var.vz : Var (τ' :: Γ') τ')))
                        (applicativeSubstEval I tailσs))
                    =
                  (EtaleSpace.BasicTopologicalInterpretation.CtxTerm.var
                    I.toApplicative.toBasic x).reindex
                      (applicativeSubstEval I tailσs)
                exact
                  EtaleSpace.BasicTopologicalInterpretation.CtxTerm.var_vs_reindex_cons
                    (I := I.toApplicative.toBasic)
                    (x := x)
                    (t := ApplicativeTopologicalInterpretation.evalTerm I.toApplicative
                      (@σs τ' (Var.vz : Var (τ' :: Γ') τ')))
                    (σ := applicativeSubstEval I tailσs)
        _ =
          ApplicativeTopologicalInterpretation.evalTerm I.toApplicative (tailσs x) := by
              exact ih (Δ := Δ) (σs := tailσs)
        _ =
          ApplicativeTopologicalInterpretation.evalTerm I.toApplicative (σs (.vs x)) := by
              rfl

@[simp] theorem eval_weaken
    (σs : ApplicativeSubst Base Const Γ Δ) :
    eval I (Γ := Γ) (Δ := υ :: Δ)
        (fun {ρ} x => ApplicativeTerm.weaken (υ := υ) (@σs ρ x)) =
      (EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
        I.toApplicative.toBasic υ Δ).comp
          (eval I (Γ := Γ) (Δ := Δ) σs) := by
  induction Γ generalizing Δ with
  | nil =>
      exact
        (EtaleSpace.BasicTopologicalInterpretation.CtxHom.toEmpty_eq_terminal
          (I := I.toApplicative.toBasic)
          (σ := (EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
            I.toApplicative.toBasic υ Δ).comp
              (eval I (Γ := []) (Δ := Δ) σs))).symm
  | cons τ Γ ih =>
      let weakenedσs : ApplicativeSubst Base Const (τ :: Γ) (υ :: Δ) :=
        fun {ρ} x => ApplicativeTerm.weaken (υ := υ) (@σs ρ x)
      let tailσs : ApplicativeSubst Base Const Γ Δ :=
        fun {ρ} x => @σs ρ (.vs x)
      let weakenedTail : ApplicativeSubst Base Const Γ (υ :: Δ) :=
        fun {ρ} x => ApplicativeTerm.weaken (υ := υ) (@σs ρ (.vs x))
      calc
        eval I (Γ := τ :: Γ) (Δ := υ :: Δ) weakenedσs
            =
          EtaleSpace.BasicTopologicalInterpretation.CtxTerm.cons
            (ApplicativeTopologicalInterpretation.evalTerm I.toApplicative
              (ApplicativeTerm.weaken (υ := υ)
                (@σs τ (Var.vz : Var (τ :: Γ) τ))))
            (eval I (Γ := Γ) (Δ := υ :: Δ) weakenedTail) := by
                simp [weakenedσs, weakenedTail, eval_cons]
        _ =
          EtaleSpace.BasicTopologicalInterpretation.CtxTerm.cons
            ((EtaleSpace.BasicTopologicalInterpretation.CtxTerm.head
              I.toApplicative.toBasic τ Γ).reindex
                ((EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
                  I.toApplicative.toBasic υ Δ).comp
                    (eval I (Γ := τ :: Γ) (Δ := Δ) σs)))
            ((((EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
              I.toApplicative.toBasic υ Δ).comp
                (eval I (Γ := τ :: Γ) (Δ := Δ) σs)).comp
                  (EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
                    I.toApplicative.toBasic τ Γ))) := by
                      congr 1
                      · calc
                          ApplicativeTopologicalInterpretation.evalTerm I.toApplicative
                              (ApplicativeTerm.weaken (υ := υ)
                                (@σs τ (Var.vz : Var (τ :: Γ) τ))) =
                            (ApplicativeTopologicalInterpretation.evalTerm I.toApplicative
                              (@σs τ (Var.vz : Var (τ :: Γ) τ))).weaken υ := by
                                exact
                                  ApplicativeTerm.eval_weaken
                                    (I := I)
                                    (υ := υ)
                                    (t := @σs τ (Var.vz : Var (τ :: Γ) τ))
                          _ =
                            ((EtaleSpace.BasicTopologicalInterpretation.CtxTerm.var
                              I.toApplicative.toBasic
                              (Var.vz : Var (τ :: Γ) τ)).reindex
                                (eval I (Γ := τ :: Γ) (Δ := Δ) σs)).weaken υ := by
                                  rw [← var_reindex_eval (I := I)
                                    (σs := σs)
                                    (x := (Var.vz : Var (τ :: Γ) τ))]
                          _ =
                            ((EtaleSpace.BasicTopologicalInterpretation.CtxTerm.head
                              I.toApplicative.toBasic τ Γ).reindex
                                (eval I (Γ := τ :: Γ) (Δ := Δ) σs)).weaken υ := by
                                  rfl
                          _ =
                            ((EtaleSpace.BasicTopologicalInterpretation.CtxTerm.head
                              I.toApplicative.toBasic τ Γ).reindex
                                (eval I (Γ := τ :: Γ) (Δ := Δ) σs)).reindex
                                  (EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
                                    I.toApplicative.toBasic υ Δ) := by
                                      rfl
                          _ =
                            (EtaleSpace.BasicTopologicalInterpretation.CtxTerm.head
                              I.toApplicative.toBasic τ Γ).reindex
                                ((EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
                                  I.toApplicative.toBasic υ Δ).comp
                                    (eval I (Γ := τ :: Γ) (Δ := Δ) σs)) := by
                                      exact
                                        (EtaleSpace.BasicTopologicalInterpretation.CtxTerm.reindex_comp
                                          (t := EtaleSpace.BasicTopologicalInterpretation.CtxTerm.head
                                            I.toApplicative.toBasic τ Γ)
                                          (σ := EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
                                            I.toApplicative.toBasic υ Δ)
                                          (ρ := eval I (Γ := τ :: Γ) (Δ := Δ) σs)).symm
                      · calc
                          eval I (Γ := Γ) (Δ := υ :: Δ) weakenedTail =
                            (EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
                              I.toApplicative.toBasic υ Δ).comp
                                (eval I (Γ := Γ) (Δ := Δ) tailσs) := by
                                  exact ih (Δ := Δ) (σs := tailσs)
                          _ =
                            (EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
                              I.toApplicative.toBasic υ Δ).comp
                                ((eval I (Γ := τ :: Γ) (Δ := Δ) σs).comp
                                  (EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
                                    I.toApplicative.toBasic τ Γ)) := by
                                      simp [tailσs, eval_cons]
                          _ =
                            (((EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
                              I.toApplicative.toBasic υ Δ).comp
                                (eval I (Γ := τ :: Γ) (Δ := Δ) σs)).comp
                                  (EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
                                    I.toApplicative.toBasic τ Γ)) := by
                                      exact
                                        (EtaleSpace.BasicTopologicalInterpretation.CtxHom.comp_assoc
                                          (σ := EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
                                            I.toApplicative.toBasic υ Δ)
                                          (ρ := eval I (Γ := τ :: Γ) (Δ := Δ) σs)
                                          (θ := EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
                                            I.toApplicative.toBasic τ Γ)).symm
        _ =
          (EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
            I.toApplicative.toBasic υ Δ).comp
              (eval I (Γ := τ :: Γ) (Δ := Δ) σs) := by
                exact
                  (EtaleSpace.BasicTopologicalInterpretation.CtxHom.cons_reconstruct
                    (I := I.toApplicative.toBasic)
                    (Γ := υ :: Δ)
                    (Δ := Γ)
                    (τ := τ)
                    ((EtaleSpace.BasicTopologicalInterpretation.CtxHom.tail
                      I.toApplicative.toBasic υ Δ).comp
                        (eval I (Γ := τ :: Γ) (Δ := Δ) σs))).symm

/-- Semantic evaluation of lifted substitutions matches lifted context morphisms. -/
@[simp] theorem eval_lift
    (σs : ApplicativeSubst Base Const Γ Δ) :
    eval I (Γ := υ :: Γ) (Δ := υ :: Δ)
        (ApplicativeSubst.lift (υ := υ) σs) =
      EtaleSpace.BasicTopologicalInterpretation.CtxHom.lift
        (I := I.toApplicative.toBasic) (τ := υ)
          (eval I (Γ := Γ) (Δ := Δ) σs) := by
  apply
    (EtaleSpace.BasicTopologicalInterpretation.CtxHom.splitEquiv
      I.toApplicative.toBasic (υ :: Δ) υ Γ).injective
  simp [EtaleSpace.BasicTopologicalInterpretation.CtxHom.lift,
    ApplicativeSubst.lift, eval_cons, eval_weaken]

@[simp] theorem term_eval_subst
    (σs : ApplicativeSubst Base Const Γ Δ)
    (t : ApplicativeTerm Base Const Γ τ) :
    ApplicativeTopologicalInterpretation.evalTerm I.toApplicative
        (ApplicativeTerm.subst σs t) =
      (ApplicativeTopologicalInterpretation.evalTerm I.toApplicative t).reindex
        (eval I (Γ := Γ) (Δ := Δ) σs) := by
  induction t generalizing Δ with
  | var x =>
      exact (var_reindex_eval (I := I) (σs := σs) (x := x)).symm
  | @const τ Γ c =>
      exact
        (EtaleSpace.BasicTopologicalInterpretation.CtxTerm.const_reindex
          (I := I.toApplicative.toBasic)
          (Γ := Γ)
          (Δ := Δ)
          (t := eval I (Γ := Γ) (Δ := Δ) σs)
          (τ := τ)
          c).symm
  | @app Γ σ τ f t ihf iht =>
      calc
        ApplicativeTopologicalInterpretation.evalTerm I.toApplicative
            (ApplicativeTerm.subst σs (.app f t)) =
          I.toApplicative.app
            (ApplicativeTopologicalInterpretation.evalTerm I.toApplicative
              (ApplicativeTerm.subst σs f))
            (ApplicativeTopologicalInterpretation.evalTerm I.toApplicative
              (ApplicativeTerm.subst σs t)) := by
                rfl
        _ =
          I.toApplicative.app
            ((ApplicativeTopologicalInterpretation.evalTerm I.toApplicative f).reindex
              (eval I (Γ := Γ) (Δ := Δ) σs))
            ((ApplicativeTopologicalInterpretation.evalTerm I.toApplicative t).reindex
              (eval I (Γ := Γ) (Δ := Δ) σs)) := by
                rw [ihf (Δ := Δ) (σs := σs), iht (Δ := Δ) (σs := σs)]
        _ =
          (I.toApplicative.app
            (ApplicativeTopologicalInterpretation.evalTerm I.toApplicative f)
            (ApplicativeTopologicalInterpretation.evalTerm I.toApplicative t)).reindex
              (eval I (Γ := Γ) (Δ := Δ) σs) := by
                exact
                  (I.app_reindex
                    (ApplicativeTopologicalInterpretation.evalTerm I.toApplicative f)
                    (ApplicativeTopologicalInterpretation.evalTerm I.toApplicative t)
                    (eval I (Γ := Γ) (Δ := Δ) σs)).symm
  | @lam σ Γ τ t ih =>
      calc
        ApplicativeTopologicalInterpretation.evalTerm I.toApplicative
            (ApplicativeTerm.subst σs (.lam t)) =
          I.toApplicative.lam
            (ApplicativeTopologicalInterpretation.evalTerm I.toApplicative
              (ApplicativeTerm.subst (ApplicativeSubst.lift (υ := σ) σs) t)) := by
                rfl
        _ =
          I.toApplicative.lam
            ((ApplicativeTopologicalInterpretation.evalTerm I.toApplicative t).reindex
              (eval I (Γ := σ :: Γ) (Δ := σ :: Δ)
                (ApplicativeSubst.lift (υ := σ) σs))) := by
                  rw [ih (Δ := σ :: Δ) (σs := ApplicativeSubst.lift (υ := σ) σs)]
        _ =
          I.toApplicative.lam
            ((ApplicativeTopologicalInterpretation.evalTerm I.toApplicative t).reindex
              (EtaleSpace.BasicTopologicalInterpretation.CtxHom.lift
                (I := I.toApplicative.toBasic) (τ := σ)
                  (eval I (Γ := Γ) (Δ := Δ) σs))) := by
                    rw [eval_lift (I := I) (υ := σ) (σs := σs)]
        _ =
          (I.toApplicative.lam
            (ApplicativeTopologicalInterpretation.evalTerm I.toApplicative t)).reindex
              (eval I (Γ := Γ) (Δ := Δ) σs) := by
                exact
                  (I.lam_reindex
                    (ApplicativeTopologicalInterpretation.evalTerm I.toApplicative t)
                    (eval I (Γ := Γ) (Δ := Δ) σs)).symm

end ApplicativeSubst

namespace HigherOrderPointTopologicalGlobalModelBridge

namespace basicInterp

variable {Base : Type u} {Const : Ty Base → Type v}
variable (M : GlobalModel Base Const)

@[simp] theorem lift_apply_consCtx
    {Γ Δ : Ctx Base} {σ : Ty Base}
    (ρ : (basicInterp M).CtxHom Δ Γ)
    (x : (ctxSpace (M := M) Δ).Carrier)
    (a : M.Carrier σ) :
    (EtaleSpace.BasicTopologicalInterpretation.CtxHom.lift
      (I := basicInterp M) (τ := σ) ρ).toContinuousMap
        (consCtx (M := M) a x) =
      consCtx (M := M) a (ρ.toContinuousMap x) := by
  apply Subtype.ext
  apply Prod.ext <;> rfl

/--
The one-point archive-free applicative model satisfies the semantic
reindexing laws required by the general reindexable interface.
-/
noncomputable def reindexableApplicativeInterp :
    ReindexableApplicativeTopologicalInterpretation Base Const PUnit where
  toApplicative := applicativeInterp M
  app_reindex := by
    intro Γ Δ σ τ f t ρ
    ext x
    rfl
  lam_reindex := by
    intro Γ Δ σ τ t ρ
    ext x
    apply congrArg (pointCarrier (M := M) (τ := σ ⇒ τ))
    apply congrArg M.lam
    funext a
    change pointCarrierVal (M := M)
        (t.toContinuousMap (consCtx (M := M) a (ρ.toContinuousMap x))) =
      pointCarrierVal (M := M)
        (t.toContinuousMap
          ((EtaleSpace.BasicTopologicalInterpretation.CtxHom.lift
            (I := basicInterp M) (τ := σ) ρ).toContinuousMap
              (consCtx (M := M) a x)))
    rw [lift_apply_consCtx (M := M) (ρ := ρ) (x := x) (a := a)]
    rfl

@[simp] theorem toApplicative_reindexableApplicativeInterp :
    (reindexableApplicativeInterp (M := M)).toApplicative = applicativeInterp M :=
  rfl

@[simp] theorem decodeEnv_eval
    {Γ Δ : Ctx Base}
    (σs : ApplicativeSubst Base Const Γ Δ)
    (γ : (ctxSpace (M := M) Δ).Carrier) :
    (decodeEnv (M := M)
        ((ApplicativeSubst.eval
          (I := reindexableApplicativeInterp (M := M))
          (Γ := Γ) (Δ := Δ) σs).toContinuousMap γ) :
      NativeEnv (M := M) Γ) =
      (SemilocalModel.substEnv M.toSemilocalModel
        (ApplicativeSubst.toSubst σs)
        (decodeEnv (M := M) γ) :
      NativeEnv (M := M) Γ) := by
    funext τ x
    have hvar := by
      simpa [toApplicative_reindexableApplicativeInterp (M := M), applicativeInterp] using
        congrArg
          (fun t => pointCarrierVal (M := M) (t.toContinuousMap γ))
        (ApplicativeSubst.var_reindex_eval
          (I := reindexableApplicativeInterp (M := M))
          (Γ := Γ) (Δ := Δ) (σs := σs) (x := x))
    calc
      decodeEnv (M := M)
          ((ApplicativeSubst.eval
            (I := reindexableApplicativeInterp (M := M))
            (Γ := Γ) (Δ := Δ) σs).toContinuousMap γ) x =
        pointCarrierVal (M := M)
          (((EtaleSpace.BasicTopologicalInterpretation.CtxTerm.var
            (basicInterp M) x).reindex
              (ApplicativeSubst.eval
                (I := reindexableApplicativeInterp (M := M))
                (Γ := Γ) (Δ := Δ) σs)).toContinuousMap γ) := by
              rw [EtaleSpace.BasicTopologicalInterpretation.CtxTerm.reindex_apply]
              symm
              exact var_val_decode (M := M) x _
      _ =
        pointCarrierVal (M := M)
          (((applicativeInterp M).evalTerm (σs x)).toContinuousMap γ) := hvar
      _ =
        SemilocalModel.eval M.toSemilocalModel
          (decodeEnv (M := M) γ)
          (ApplicativeTerm.toTerm (σs x)) := by
            exact
              ApplicativeTopologicalInterpretation.eval_val_decode
                (M := M) (t := σs x) γ
      _ =
        SemilocalModel.substEnv M.toSemilocalModel
          (ApplicativeSubst.toSubst σs)
          (decodeEnv (M := M) γ) x := by
            rfl

namespace ApplicativeTopologicalInterpretation

@[simp] theorem eval_val_decode_subst
    {Γ Δ : Ctx Base} {τ : Ty Base}
    (σs : ApplicativeSubst Base Const Γ Δ)
    (t : ApplicativeTerm Base Const Γ τ)
    (γ : (ctxSpace (M := M) Δ).Carrier) :
    pointCarrierVal (M := M)
      (((applicativeInterp M).evalTerm (ApplicativeTerm.subst σs t)).toContinuousMap γ) =
      SemilocalModel.eval M.toSemilocalModel
        (decodeEnv (M := M) γ)
        (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.subst
          (ApplicativeSubst.toSubst σs) (ApplicativeTerm.toTerm t)) := by
  have happ :
      pointCarrierVal (M := M)
        (((applicativeInterp M).evalTerm (ApplicativeTerm.subst σs t)).toContinuousMap γ) =
      pointCarrierVal (M := M)
        (eval (M := M)
          (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.subst
            (ApplicativeSubst.toSubst σs) (ApplicativeTerm.toTerm t)) γ) := by
    simp [ApplicativeTopologicalInterpretation.eval_val_decode,
      HigherOrderPointTopologicalGlobalModelBridge.basicInterp.eval_val_decode,
      ApplicativeTerm.toTerm_subst]
  calc
    pointCarrierVal (M := M)
        (((applicativeInterp M).evalTerm (ApplicativeTerm.subst σs t)).toContinuousMap γ) =
      pointCarrierVal (M := M)
        (eval (M := M)
          (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.subst
            (ApplicativeSubst.toSubst σs) (ApplicativeTerm.toTerm t)) γ) := happ
    _ =
      SemilocalModel.eval M.toSemilocalModel
        (decodeEnv (M := M) γ)
        (Mettapedia.AutoBooks.Codex.IntuitionisticHOL.subst
          (ApplicativeSubst.toSubst σs) (ApplicativeTerm.toTerm t)) := by
          exact
            (HigherOrderPointTopologicalGlobalModelBridge.basicInterp.eval_val_decode
              (M := M)
              (t :=
                Mettapedia.AutoBooks.Codex.IntuitionisticHOL.subst
                  (ApplicativeSubst.toSubst σs) (ApplicativeTerm.toTerm t))
              (γ := γ))

end ApplicativeTopologicalInterpretation

end basicInterp

end HigherOrderPointTopologicalGlobalModelBridge

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
