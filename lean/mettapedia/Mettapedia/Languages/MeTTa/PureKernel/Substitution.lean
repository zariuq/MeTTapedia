import Mettapedia.Languages.MeTTa.PureKernel.Renaming

namespace Mettapedia.Languages.MeTTa.PureKernel.Substitution

open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Renaming

abbrev Sub (n m : Nat) := Fin n → PureTm m

def ids : Sub n n := fun i => .var i

def liftSub (σ : Sub n m) : Sub (n + 1) (m + 1) :=
  Fin.cases (.var 0) (fun i => rename wk (σ i))

def subst (σ : Sub n m) : PureTm n → PureTm m
  | .var i => σ i
  | .u0 => .u0
  | .u1 => .u1
  | .pi A B => .pi (subst σ A) (subst (liftSub σ) B)
  | .sigma A B => .sigma (subst σ A) (subst (liftSub σ) B)
  | .id A a b => .id (subst σ A) (subst σ a) (subst σ b)
  | .lam b => .lam (subst (liftSub σ) b)
  | .app f a => .app (subst σ f) (subst σ a)
  | .pair a b => .pair (subst σ a) (subst σ b)
  | .fst p => .fst (subst σ p)
  | .snd p => .snd (subst σ p)
  | .refl a => .refl (subst σ a)

def subst0 (u : PureTm n) : Sub (n + 1) n :=
  Fin.cases u (fun i => .var i)

def inst0 (u : PureTm n) (t : PureTm (n + 1)) : PureTm n :=
  subst (subst0 u) t

@[simp] theorem subst0_zero (u : PureTm n) :
    subst0 u 0 = u := rfl

@[simp] theorem subst0_succ (u : PureTm n) (i : Fin n) :
    subst0 u i.succ = .var i := rfl

@[simp] theorem inst0_var_zero (u : PureTm n) :
    inst0 u (.var 0) = u := rfl

@[simp] theorem inst0_var_succ (u : PureTm n) (i : Fin n) :
    inst0 u (.var i.succ) = .var i := rfl

@[simp] theorem subst_var (σ : Sub n m) (i : Fin n) :
    subst σ (.var i) = σ i := rfl

@[simp] theorem liftSub_zero (σ : Sub n m) :
    liftSub σ 0 = (.var 0 : PureTm (m + 1)) := rfl

@[simp] theorem liftSub_succ (σ : Sub n m) (i : Fin n) :
    liftSub σ i.succ = rename wk (σ i) := rfl

theorem subst_ext {σ τ : Sub n m} (hστ : ∀ i, σ i = τ i) :
    ∀ t : PureTm n, subst σ t = subst τ t := by
  intro t
  induction t generalizing m with
  | var i =>
    simp [subst, hστ i]
  | u0 =>
    rfl
  | u1 =>
    rfl
  | pi A B ihA ihB =>
    simp [subst, ihA (σ := σ) (τ := τ) hστ]
    exact ihB (σ := liftSub σ) (τ := liftSub τ) (by
      intro i
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro j
        simp [liftSub, hστ j])
  | sigma A B ihA ihB =>
    simp [subst, ihA (σ := σ) (τ := τ) hστ]
    exact ihB (σ := liftSub σ) (τ := liftSub τ) (by
      intro i
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro j
        simp [liftSub, hστ j])
  | id A a b ihA iha ihb =>
    simp [subst, ihA (σ := σ) (τ := τ) hστ, iha (σ := σ) (τ := τ) hστ,
      ihb (σ := σ) (τ := τ) hστ]
  | lam b ih =>
    simp [subst]
    exact ih (σ := liftSub σ) (τ := liftSub τ) (by
      intro i
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro j
        simp [liftSub, hστ j])
  | app f a ihf iha =>
    simp [subst, ihf (σ := σ) (τ := τ) hστ, iha (σ := σ) (τ := τ) hστ]
  | pair a b iha ihb =>
    simp [subst, iha (σ := σ) (τ := τ) hστ, ihb (σ := σ) (τ := τ) hστ]
  | fst p ih =>
    simpa [subst] using ih (σ := σ) (τ := τ) hστ
  | snd p ih =>
    simpa [subst] using ih (σ := σ) (τ := τ) hστ
  | refl a iha =>
    simpa [subst] using iha (σ := σ) (τ := τ) hστ

@[simp] theorem liftSub_ids : liftSub (ids (n := n)) = ids := by
  funext i
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

@[simp] theorem subst_ids : ∀ t : PureTm n, subst ids t = t := by
  intro t
  induction t with
  | var i =>
    rfl
  | u0 =>
    rfl
  | u1 =>
    rfl
  | pi A B ihA ihB =>
    simp [subst, ihA, ihB, liftSub_ids]
  | sigma A B ihA ihB =>
    simp [subst, ihA, ihB, liftSub_ids]
  | id A a b ihA iha ihb =>
    simp [subst, ihA, iha, ihb]
  | lam b ih =>
    simp [subst, ih, liftSub_ids]
  | app f a ihf iha =>
    simp [subst, ihf, iha]
  | pair a b iha ihb =>
    simp [subst, iha, ihb]
  | fst p ih =>
    simp [subst, ih]
  | snd p ih =>
    simp [subst, ih]
  | refl a iha =>
    simp [subst, iha]

@[simp] theorem rename_liftSub (ρ : Ren m k) (σ : Sub n m) (i : Fin (n + 1)) :
    rename (liftRen ρ) (liftSub σ i) = liftSub (fun j => rename ρ (σ j)) i := by
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    calc
      rename (liftRen ρ) (liftSub σ j.succ)
          = rename (liftRen ρ) (rename wk (σ j)) := by rfl
      _ = rename (fun x => liftRen ρ (wk x)) (σ j) := by
            simp [rename_comp]
      _ = rename (fun x => wk (ρ x)) (σ j) := by
            exact rename_ext
              (ρ := fun x => liftRen ρ (wk x))
              (ξ := fun x => wk (ρ x))
              (by intro x; simp [wk, liftRen])
              (σ j)
      _ = rename wk (rename ρ (σ j)) := by
            simp [rename_comp]
      _ = liftSub (fun x => rename ρ (σ x)) j.succ := by rfl

theorem rename_subst :
    ∀ {n m k} (ρ : Ren m k) (σ : Sub n m) (t : PureTm n),
      rename ρ (subst σ t) = subst (fun i => rename ρ (σ i)) t := by
  intro n m k ρ σ t
  induction t generalizing m k ρ with
  | var i =>
    rfl
  | u0 =>
    rfl
  | u1 =>
    rfl
  | pi A B ihA ihB =>
    simp [rename, subst, ihA (ρ := ρ) (σ := σ)]
    calc
      rename (liftRen ρ) (subst (liftSub σ) B)
          = subst (fun i => rename (liftRen ρ) (liftSub σ i)) B := by
              simpa using ihB (ρ := liftRen ρ) (σ := liftSub σ)
      _ = subst (liftSub (fun i => rename ρ (σ i))) B := by
            apply subst_ext
            intro i
            exact rename_liftSub ρ σ i
  | sigma A B ihA ihB =>
    simp [rename, subst, ihA (ρ := ρ) (σ := σ)]
    calc
      rename (liftRen ρ) (subst (liftSub σ) B)
          = subst (fun i => rename (liftRen ρ) (liftSub σ i)) B := by
              simpa using ihB (ρ := liftRen ρ) (σ := liftSub σ)
      _ = subst (liftSub (fun i => rename ρ (σ i))) B := by
            apply subst_ext
            intro i
            exact rename_liftSub ρ σ i
  | id A a b ihA iha ihb =>
    simp [rename, subst, ihA (ρ := ρ) (σ := σ), iha (ρ := ρ) (σ := σ),
      ihb (ρ := ρ) (σ := σ)]
  | lam b ih =>
    simp [rename, subst]
    calc
      rename (liftRen ρ) (subst (liftSub σ) b)
          = subst (fun i => rename (liftRen ρ) (liftSub σ i)) b := by
              simpa using ih (ρ := liftRen ρ) (σ := liftSub σ)
      _ = subst (liftSub (fun i => rename ρ (σ i))) b := by
            apply subst_ext
            intro i
            exact rename_liftSub ρ σ i
  | app f a ihf iha =>
    simp [rename, subst, ihf (ρ := ρ) (σ := σ), iha (ρ := ρ) (σ := σ)]
  | pair a b iha ihb =>
    simp [rename, subst, iha (ρ := ρ) (σ := σ), ihb (ρ := ρ) (σ := σ)]
  | fst p ih =>
    simpa [rename, subst] using ih (ρ := ρ) (σ := σ)
  | snd p ih =>
    simpa [rename, subst] using ih (ρ := ρ) (σ := σ)
  | refl a iha =>
    simpa [rename, subst] using iha (ρ := ρ) (σ := σ)

@[simp] theorem liftSub_liftRen_apply (σ : Sub m k) (ρ : Ren n m) (i : Fin (n + 1)) :
    liftSub σ (liftRen ρ i) = liftSub (fun j => σ (ρ j)) i := by
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    rfl

theorem subst_rename :
    ∀ {n m k} (σ : Sub m k) (ρ : Ren n m) (t : PureTm n),
      subst σ (rename ρ t) = subst (fun i => σ (ρ i)) t := by
  intro n m k σ ρ t
  induction t generalizing m k σ with
  | var i =>
    rfl
  | u0 =>
    rfl
  | u1 =>
    rfl
  | pi A B ihA ihB =>
    simp [subst, rename, ihA (σ := σ) (ρ := ρ)]
    calc
      subst (liftSub σ) (rename (liftRen ρ) B)
          = subst (fun i => liftSub σ (liftRen ρ i)) B := by
              simpa using ihB (σ := liftSub σ) (ρ := liftRen ρ)
      _ = subst (liftSub (fun i => σ (ρ i))) B := by
            apply subst_ext
            intro i
            exact liftSub_liftRen_apply σ ρ i
  | sigma A B ihA ihB =>
    simp [subst, rename, ihA (σ := σ) (ρ := ρ)]
    calc
      subst (liftSub σ) (rename (liftRen ρ) B)
          = subst (fun i => liftSub σ (liftRen ρ i)) B := by
              simpa using ihB (σ := liftSub σ) (ρ := liftRen ρ)
      _ = subst (liftSub (fun i => σ (ρ i))) B := by
            apply subst_ext
            intro i
            exact liftSub_liftRen_apply σ ρ i
  | id A a b ihA iha ihb =>
    simp [subst, rename, ihA (σ := σ) (ρ := ρ), iha (σ := σ) (ρ := ρ),
      ihb (σ := σ) (ρ := ρ)]
  | lam b ih =>
    simp [subst, rename]
    calc
      subst (liftSub σ) (rename (liftRen ρ) b)
          = subst (fun i => liftSub σ (liftRen ρ i)) b := by
              simpa using ih (σ := liftSub σ) (ρ := liftRen ρ)
      _ = subst (liftSub (fun i => σ (ρ i))) b := by
            apply subst_ext
            intro i
            exact liftSub_liftRen_apply σ ρ i
  | app f a ihf iha =>
    simp [subst, rename, ihf (σ := σ) (ρ := ρ), iha (σ := σ) (ρ := ρ)]
  | pair a b iha ihb =>
    simp [subst, rename, iha (σ := σ) (ρ := ρ), ihb (σ := σ) (ρ := ρ)]
  | fst p ih =>
    simpa [subst, rename] using ih (σ := σ) (ρ := ρ)
  | snd p ih =>
    simpa [subst, rename] using ih (σ := σ) (ρ := ρ)
  | refl a iha =>
    simpa [subst, rename] using iha (σ := σ) (ρ := ρ)

@[simp] theorem subst_liftSub_wk (σ : Sub n m) (t : PureTm n) :
    subst (liftSub σ) (rename wk t) = rename wk (subst σ t) := by
  calc
    subst (liftSub σ) (rename wk t)
        = subst (fun i => liftSub σ (wk i)) t := by
            simpa using (subst_rename (σ := liftSub σ) (ρ := wk) (t := t))
    _ = subst (fun i => rename wk (σ i)) t := by
          rfl
    _ = rename wk (subst σ t) := by
          symm
          simpa using (rename_subst (ρ := wk) (σ := σ) (t := t))

@[simp] theorem rename_inst0 (ρ : Ren n m) (a : PureTm n) (b : PureTm (n + 1)) :
    rename ρ (inst0 a b) = inst0 (rename ρ a) (rename (liftRen ρ) b) := by
  calc
    rename ρ (inst0 a b)
        = subst (fun i => rename ρ (subst0 a i)) b := by
            simpa [inst0] using
              (rename_subst (ρ := ρ) (σ := subst0 a) (t := b))
    _ = subst (fun i => subst0 (rename ρ a) (liftRen ρ i)) b := by
          apply subst_ext
          intro i
          refine Fin.cases ?_ ?_ i
          · rfl
          · intro j
            rfl
    _ = subst (subst0 (rename ρ a)) (rename (liftRen ρ) b) := by
          symm
          simpa using
            (subst_rename (σ := subst0 (rename ρ a)) (ρ := liftRen ρ) (t := b))
    _ = inst0 (rename ρ a) (rename (liftRen ρ) b) := by
          rfl

@[simp] theorem liftSub_comp_apply (τ : Sub m k) (σ : Sub n m) (i : Fin (n + 1)) :
    subst (liftSub τ) (liftSub σ i) = liftSub (fun x => subst τ (σ x)) i := by
  refine Fin.cases ?_ ?_ i
  · rfl
  · intro j
    calc
      subst (liftSub τ) (liftSub σ j.succ)
          = subst (liftSub τ) (rename wk (σ j)) := by rfl
      _ = subst (fun x => liftSub τ (wk x)) (σ j) := by
            simpa using (subst_rename (σ := liftSub τ) (ρ := wk) (t := σ j))
      _ = subst (fun x => rename wk (τ x)) (σ j) := by rfl
      _ = rename wk (subst τ (σ j)) := by
            symm
            simpa using (rename_subst (ρ := wk) (σ := τ) (t := σ j))
      _ = liftSub (fun x => subst τ (σ x)) j.succ := by rfl

@[simp] theorem subst_comp :
    ∀ {n m k} (τ : Sub m k) (σ : Sub n m) (t : PureTm n),
      subst τ (subst σ t) = subst (fun i => subst τ (σ i)) t := by
  intro n m k τ σ t
  induction t generalizing m k τ with
  | var i =>
    rfl
  | u0 =>
    rfl
  | u1 =>
    rfl
  | pi A B ihA ihB =>
    simp [subst, ihA (τ := τ) (σ := σ)]
    calc
      subst (liftSub τ) (subst (liftSub σ) B)
          = subst (fun i => subst (liftSub τ) (liftSub σ i)) B := by
              simpa using ihB (τ := liftSub τ) (σ := liftSub σ)
      _ = subst (liftSub (fun i => subst τ (σ i))) B := by
            apply subst_ext
            intro i
            exact liftSub_comp_apply τ σ i
  | sigma A B ihA ihB =>
    simp [subst, ihA (τ := τ) (σ := σ)]
    calc
      subst (liftSub τ) (subst (liftSub σ) B)
          = subst (fun i => subst (liftSub τ) (liftSub σ i)) B := by
              simpa using ihB (τ := liftSub τ) (σ := liftSub σ)
      _ = subst (liftSub (fun i => subst τ (σ i))) B := by
            apply subst_ext
            intro i
            exact liftSub_comp_apply τ σ i
  | id A a b ihA iha ihb =>
    simp [subst, ihA (τ := τ) (σ := σ), iha (τ := τ) (σ := σ),
      ihb (τ := τ) (σ := σ)]
  | lam b ih =>
    simp [subst]
    calc
      subst (liftSub τ) (subst (liftSub σ) b)
          = subst (fun i => subst (liftSub τ) (liftSub σ i)) b := by
              simpa using ih (τ := liftSub τ) (σ := liftSub σ)
      _ = subst (liftSub (fun i => subst τ (σ i))) b := by
            apply subst_ext
            intro i
            exact liftSub_comp_apply τ σ i
  | app f a ihf iha =>
    simp [subst, ihf (τ := τ) (σ := σ), iha (τ := τ) (σ := σ)]
  | pair a b iha ihb =>
    simp [subst, iha (τ := τ) (σ := σ), ihb (τ := τ) (σ := σ)]
  | fst p ih =>
    simp [subst, ih (τ := τ) (σ := σ)]
  | snd p ih =>
    simp [subst, ih (τ := τ) (σ := σ)]
  | refl a iha =>
    simp [subst, iha (τ := τ) (σ := σ)]

@[simp] theorem subst_inst0 (σ : Sub n m) (a : PureTm n) (b : PureTm (n + 1)) :
    subst σ (inst0 a b) = inst0 (subst σ a) (subst (liftSub σ) b) := by
  calc
    subst σ (inst0 a b)
        = subst (fun i => subst σ (subst0 a i)) b := by
            simp [inst0, subst_comp]
    _ = subst (fun i => subst (subst0 (subst σ a)) (liftSub σ i)) b := by
          apply subst_ext
          intro i
          refine Fin.cases ?_ ?_ i
          · rfl
          · intro j
            calc
              subst σ (subst0 a j.succ) = subst σ (.var j) := by
                rfl
              _ = σ j := by
                rfl
              _ = subst (subst0 (subst σ a)) (rename wk (σ j)) := by
                symm
                calc
                  subst (subst0 (subst σ a)) (rename wk (σ j))
                      = subst (fun i => subst0 (subst σ a) (wk i)) (σ j) := by
                          simpa using
                            (subst_rename (σ := subst0 (subst σ a)) (ρ := wk) (t := σ j))
                  _ = subst ids (σ j) := by
                        apply subst_ext
                        intro i
                        rfl
                  _ = σ j := by
                        exact subst_ids (t := σ j)
              _ = subst (subst0 (subst σ a)) (liftSub σ j.succ) := by
                rfl
    _ = subst (subst0 (subst σ a)) (subst (liftSub σ) b) := by
          symm
          exact
            (subst_comp (τ := subst0 (subst σ a)) (σ := liftSub σ) (t := b))
    _ = inst0 (subst σ a) (subst (liftSub σ) b) := by
          rfl

end Mettapedia.Languages.MeTTa.PureKernel.Substitution
