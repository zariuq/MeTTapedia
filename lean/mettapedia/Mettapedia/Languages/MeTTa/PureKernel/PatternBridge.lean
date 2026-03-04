import Mettapedia.Languages.MeTTa.Pure.Core
import Mettapedia.Languages.MeTTa.PureKernel.Context
import Mettapedia.Languages.MeTTa.PureKernel.Substitution
import Mettapedia.OSLF.MeTTaIL.Substitution

namespace Mettapedia.Languages.MeTTa.PureKernel.PatternBridge

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.Pure.Core
open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Context
open Mettapedia.Languages.MeTTa.PureKernel.Renaming
open Mettapedia.Languages.MeTTa.PureKernel.Substitution
open Mettapedia.OSLF.MeTTaIL.Substitution

abbrev QuoteEnv (n : Nat) := Fin n → String

def envCons (x : String) (ρ : QuoteEnv n) : QuoteEnv (n + 1) :=
  Fin.cases x (fun i => ρ i)

/-- Legacy raw quote (debug only): maps scoped vars directly to bvars. -/
def quoteRaw : PureTm n → Pattern
  | .var i => .bvar i.1
  | .u0 => u0
  | .u1 => u1
  | .pi A B => mkPi (quoteRaw A) (quoteRaw B)
  | .sigma A B => mkSigma (quoteRaw A) (quoteRaw B)
  | .id A a b => mkId (quoteRaw A) (quoteRaw a) (quoteRaw b)
  | .lam b => mkLam (quoteRaw b)
  | .app f a => mkApp (quoteRaw f) (quoteRaw a)
  | .pair a b => mkPair (quoteRaw a) (quoteRaw b)
  | .fst p => mkFst (quoteRaw p)
  | .snd p => mkSnd (quoteRaw p)
  | .refl a => mkRefl (quoteRaw a)

def defaultBinderName (k : Nat) : String := "__pk_" ++ toString k

/-- Contextual locally-nameless quote:
`PureTm` variables are mapped to `fvar`s via `ρ`,
and binders are encoded by `closeFVar` with fresh binder names from `ν`. -/
def quoteTmWith (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n) : PureTm n → Pattern
  | .var i => .fvar (ρ i)
  | .u0 => u0
  | .u1 => u1
  | .pi A B =>
      let x := ν k
      mkPi (quoteTmWith ν k ρ A)
        (closeFVar 0 x (quoteTmWith ν (k + 1) (envCons x ρ) B))
  | .sigma A B =>
      let x := ν k
      mkSigma (quoteTmWith ν k ρ A)
        (closeFVar 0 x (quoteTmWith ν (k + 1) (envCons x ρ) B))
  | .id A a b => mkId (quoteTmWith ν k ρ A) (quoteTmWith ν k ρ a) (quoteTmWith ν k ρ b)
  | .lam b =>
      let x := ν k
      mkLam (closeFVar 0 x (quoteTmWith ν (k + 1) (envCons x ρ) b))
  | .app f a => mkApp (quoteTmWith ν k ρ f) (quoteTmWith ν k ρ a)
  | .pair a b => mkPair (quoteTmWith ν k ρ a) (quoteTmWith ν k ρ b)
  | .fst p => mkFst (quoteTmWith ν k ρ p)
  | .snd p => mkSnd (quoteTmWith ν k ρ p)
  | .refl a => mkRefl (quoteTmWith ν k ρ a)

@[simp] theorem envCons_comp_liftRen
    (x : String) (ρdst : QuoteEnv m) (ρ : Ren n m) :
    (fun j : Fin (n + 1) => envCons x ρdst (liftRen ρ j)) =
      envCons x (fun i => ρdst (ρ i)) := by
  funext j
  refine Fin.cases ?_ ?_ j
  · rfl
  · intro i
    rfl

/-- Contextual quotation commutes with kernel renaming. -/
theorem quoteTmWith_rename (ν : Nat → String) :
    ∀ {n m : Nat} (k : Nat) (ρdst : QuoteEnv m) (ρ : Ren n m) (t : PureTm n),
      quoteTmWith ν k ρdst (rename ρ t) =
        quoteTmWith ν k (fun i => ρdst (ρ i)) t := by
  intro n m k ρdst ρ t
  induction t generalizing m k ρdst with
  | var i =>
      rfl
  | u0 =>
      rfl
  | u1 =>
      rfl
  | pi A B ihA ihB =>
      have hB :=
        ihB (k := k + 1) (ρdst := envCons (ν k) ρdst) (ρ := liftRen ρ)
      calc
        quoteTmWith ν k ρdst (rename ρ (.pi A B))
            = mkPi (quoteTmWith ν k ρdst (rename ρ A))
                (closeFVar 0 (ν k)
                  (quoteTmWith ν (k + 1) (envCons (ν k) ρdst) (rename (liftRen ρ) B))) := by
                    rfl
        _ = mkPi (quoteTmWith ν k (fun i => ρdst (ρ i)) A)
                (closeFVar 0 (ν k)
                  (quoteTmWith ν (k + 1) (envCons (ν k) ρdst) (rename (liftRen ρ) B))) := by
                    simp [ihA (k := k) (ρdst := ρdst) (ρ := ρ)]
        _ = mkPi (quoteTmWith ν k (fun i => ρdst (ρ i)) A)
                (closeFVar 0 (ν k)
                  (quoteTmWith ν (k + 1)
                    (fun j => envCons (ν k) ρdst (liftRen ρ j)) B)) := by
                    simpa using congrArg
                      (fun q => mkPi (quoteTmWith ν k (fun i => ρdst (ρ i)) A)
                        (closeFVar 0 (ν k) q)) hB
        _ = mkPi (quoteTmWith ν k (fun i => ρdst (ρ i)) A)
                (closeFVar 0 (ν k)
                  (quoteTmWith ν (k + 1)
                    (envCons (ν k) (fun i => ρdst (ρ i))) B)) := by
                    simp [envCons_comp_liftRen]
        _ = quoteTmWith ν k (fun i => ρdst (ρ i)) (.pi A B) := by
            rfl
  | sigma A B ihA ihB =>
      have hB :=
        ihB (k := k + 1) (ρdst := envCons (ν k) ρdst) (ρ := liftRen ρ)
      calc
        quoteTmWith ν k ρdst (rename ρ (.sigma A B))
            = mkSigma (quoteTmWith ν k ρdst (rename ρ A))
                (closeFVar 0 (ν k)
                  (quoteTmWith ν (k + 1) (envCons (ν k) ρdst) (rename (liftRen ρ) B))) := by
                    rfl
        _ = mkSigma (quoteTmWith ν k (fun i => ρdst (ρ i)) A)
                (closeFVar 0 (ν k)
                  (quoteTmWith ν (k + 1) (envCons (ν k) ρdst) (rename (liftRen ρ) B))) := by
                    simp [ihA (k := k) (ρdst := ρdst) (ρ := ρ)]
        _ = mkSigma (quoteTmWith ν k (fun i => ρdst (ρ i)) A)
                (closeFVar 0 (ν k)
                  (quoteTmWith ν (k + 1)
                    (fun j => envCons (ν k) ρdst (liftRen ρ j)) B)) := by
                    simpa using congrArg
                      (fun q => mkSigma (quoteTmWith ν k (fun i => ρdst (ρ i)) A)
                        (closeFVar 0 (ν k) q)) hB
        _ = mkSigma (quoteTmWith ν k (fun i => ρdst (ρ i)) A)
                (closeFVar 0 (ν k)
                  (quoteTmWith ν (k + 1)
                    (envCons (ν k) (fun i => ρdst (ρ i))) B)) := by
                    simp [envCons_comp_liftRen]
        _ = quoteTmWith ν k (fun i => ρdst (ρ i)) (.sigma A B) := by
            rfl
  | id A a b ihA iha ihb =>
      simp [quoteTmWith, rename,
        ihA (k := k) (ρdst := ρdst) (ρ := ρ),
        iha (k := k) (ρdst := ρdst) (ρ := ρ),
        ihb (k := k) (ρdst := ρdst) (ρ := ρ)]
  | lam b ih =>
      have hb := ih (k := k + 1) (ρdst := envCons (ν k) ρdst) (ρ := liftRen ρ)
      calc
        quoteTmWith ν k ρdst (rename ρ (.lam b))
            = mkLam
              (closeFVar 0 (ν k)
                (quoteTmWith ν (k + 1)
                  (envCons (ν k) ρdst) (rename (liftRen ρ) b))) := by
                    rfl
        _ = mkLam
              (closeFVar 0 (ν k)
                (quoteTmWith ν (k + 1)
                  (fun j => envCons (ν k) ρdst (liftRen ρ j)) b)) := by
                    simpa using congrArg (fun q => mkLam (closeFVar 0 (ν k) q)) hb
        _ = mkLam
              (closeFVar 0 (ν k)
                (quoteTmWith ν (k + 1)
                  (envCons (ν k) (fun i => ρdst (ρ i))) b)) := by
                    simp [envCons_comp_liftRen]
        _ = quoteTmWith ν k (fun i => ρdst (ρ i)) (.lam b) := by
            rfl
  | app f a ihf iha =>
      simp [quoteTmWith, rename,
        ihf (k := k) (ρdst := ρdst) (ρ := ρ),
        iha (k := k) (ρdst := ρdst) (ρ := ρ)]
  | pair a b iha ihb =>
      simp [quoteTmWith, rename,
        iha (k := k) (ρdst := ρdst) (ρ := ρ),
        ihb (k := k) (ρdst := ρdst) (ρ := ρ)]
  | fst p ih =>
      simpa [quoteTmWith, rename] using congrArg mkFst (ih (k := k) (ρdst := ρdst) (ρ := ρ))
  | snd p ih =>
      simpa [quoteTmWith, rename] using congrArg mkSnd (ih (k := k) (ρdst := ρdst) (ρ := ρ))
  | refl a iha =>
      simpa [quoteTmWith, rename] using congrArg mkRefl (iha (k := k) (ρdst := ρdst) (ρ := ρ))

/-- Useful weakening corollary for bridge proofs. -/
theorem quoteTmWith_rename_wk_envCons
    (ν : Nat → String) (k : Nat) (x : String) (ρ : QuoteEnv n) (t : PureTm n) :
    quoteTmWith ν k (envCons x ρ) (rename wk t) =
      quoteTmWith ν k ρ t := by
  simpa [wk, envCons] using
    (quoteTmWith_rename ν (k := k) (ρdst := envCons x ρ) (ρ := wk) (t := t))

/-- Body-quotation mode under the current binder name `ν k`. -/
def quoteBodyWith (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n)
    (b : PureTm (n + 1)) : Pattern :=
  quoteTmWith ν (k + 1) (envCons (ν k) ρ) b

/-- Under body-quotation mode, weakening by `wk` cancels the outer binder extension. -/
@[simp] theorem quoteBodyWith_wk
    (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n) (t : PureTm n) :
    quoteBodyWith ν k ρ (rename wk t) = quoteTmWith ν (k + 1) ρ t := by
  simpa [quoteBodyWith] using quoteTmWith_rename_wk_envCons ν (k + 1) (ν k) ρ t

def quoteTm (ρ : QuoteEnv n) (t : PureTm n) : Pattern :=
  quoteTmWith defaultBinderName 0 ρ t

def emptyEnv : QuoteEnv 0 := fun i => False.elim (Nat.not_lt_zero _ i.isLt)

def quoteClosedTm (t : PureTm 0) : Pattern :=
  quoteTm (ρ := emptyEnv) t

def quoteCtx (ρ : QuoteEnv n) : Ctx n → Pattern
  | .nil => mkCtxEmpty
  | .snoc Γ A =>
      let ρprev : QuoteEnv _ := fun i => ρ i.succ
      mkCtxExtend (quoteCtx ρprev Γ) (quoteTm ρprev A)

/-- Binder naming policy for contextual quotation. -/
structure BinderPolicy where
  name : Nat → String
  inj : Function.Injective name

/-- Compatibility assumptions for contextual quotation:
`ν` is injective and all future binder names `ν j` (j ≥ k) are absent from `ρ`. -/
def QuoteCompat (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n) : Prop :=
  Function.Injective ν ∧ (∀ i j, k ≤ j → ρ i ≠ ν j)

/-- Strong quotation invariant for open terms:
the quote environment is injective and compatible with the binder naming policy. -/
structure QuoteEnvGood (P : BinderPolicy) (k : Nat) (ρ : QuoteEnv n) : Prop where
  env_inj : Function.Injective ρ
  compat : QuoteCompat P.name k ρ

/-- Bridge contract (open-form): kernel `inst0` commutes with contextual quotation. -/
def Inst0OpenBridge (ν : Nat → String) : Prop :=
  ∀ {n : Nat} (k : Nat) (ρ : QuoteEnv n) (a : PureTm n) (body : PureTm (n + 1)),
    quoteTmWith ν k ρ (inst0 a body) =
      openBVar 0 (quoteTmWith ν k ρ a)
        (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) body))

/-- Bridge contract (apply-form): kernel `inst0` commutes with singleton `applySubst`. -/
def Inst0ApplyBridge (ν : Nat → String) : Prop :=
  ∀ {n : Nat} (k : Nat) (ρ : QuoteEnv n) (a : PureTm n) (body : PureTm (n + 1)),
    quoteTmWith ν k ρ (inst0 a body) =
      applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν k ρ a))
        (quoteTmWith ν (k + 1) (envCons (ν k) ρ) body)

/-- Compatibility-aware bridge contract (open-form). -/
def Inst0OpenBridgeCompat (ν : Nat → String) : Prop :=
  ∀ {n : Nat} (k : Nat) (ρ : QuoteEnv n) (a : PureTm n) (body : PureTm (n + 1)),
    QuoteCompat ν k ρ →
    quoteTmWith ν k ρ (inst0 a body) =
      openBVar 0 (quoteTmWith ν k ρ a)
        (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) body))

/-- Compatibility-aware bridge contract (apply-form). -/
def Inst0ApplyBridgeCompat (ν : Nat → String) : Prop :=
  ∀ {n : Nat} (k : Nat) (ρ : QuoteEnv n) (a : PureTm n) (body : PureTm (n + 1)),
    QuoteCompat ν k ρ →
    quoteTmWith ν k ρ (inst0 a body) =
      applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν k ρ a))
        (quoteTmWith ν (k + 1) (envCons (ν k) ρ) body)

theorem quoteCompat_empty (ν : Nat → String) (hν : Function.Injective ν) (k : Nat) :
    QuoteCompat ν k emptyEnv := by
  refine ⟨hν, ?_⟩
  intro i
  exact Fin.elim0 i

theorem QuoteEnvGood.empty (P : BinderPolicy) (k : Nat) :
    QuoteEnvGood P k emptyEnv := by
  refine ⟨?_, ?_⟩
  · intro i
    exact Fin.elim0 i
  · exact quoteCompat_empty P.name P.inj k

theorem QuoteCompat.envCons {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hν : Function.Injective ν) (hρ : QuoteCompat ν k ρ) :
    QuoteCompat ν (k + 1) (envCons (ν k) ρ) := by
  refine ⟨hν, ?_⟩
  intro i j hj
  refine Fin.cases ?h0 ?hs i
  · intro hEq
    have hkj : k ≠ j := by omega
    exact hkj (hν hEq)
  · intro i'
    exact hρ.2 i' j (by omega)

theorem QuoteEnvGood.envCons {P : BinderPolicy} {k : Nat} {ρ : QuoteEnv n}
    (hρ : QuoteEnvGood P k ρ) :
    QuoteEnvGood P (k + 1) (envCons (P.name k) ρ) := by
  refine ⟨?_, ?_⟩
  · intro i j hij
    cases i using Fin.cases with
    | zero =>
        cases j using Fin.cases with
        | zero =>
            rfl
        | succ j' =>
            exfalso
            have hneq : ρ j' ≠ P.name k := hρ.compat.2 j' k (by omega)
            exact hneq hij.symm
    | succ i' =>
        cases j using Fin.cases with
        | zero =>
            exfalso
            have hneq : ρ i' ≠ P.name k := hρ.compat.2 i' k (by omega)
            exact hneq hij
        | succ j' =>
            have hij' : ρ i' = ρ j' := by simpa [envCons] using hij
            have heq : i' = j' := hρ.env_inj hij'
            cases heq
            rfl
  · exact QuoteCompat.envCons P.inj hρ.compat

theorem envCons_injective_of_injective_of_compat
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hρinj : Function.Injective ρ) (hcompat : QuoteCompat ν k ρ) :
    Function.Injective (envCons (ν k) ρ) := by
  let P : BinderPolicy := { name := ν, inj := hcompat.1 }
  have hgood : QuoteEnvGood P k ρ := ⟨hρinj, hcompat⟩
  exact (QuoteEnvGood.envCons (P := P) hgood).env_inj

/-- Quote a kernel substitution as a MeTTaIL substitution environment. -/
def quoteSubstEnv (ν : Nat → String) (k : Nat) (ρsrc : QuoteEnv n)
    (ρdst : QuoteEnv m) (σ : Sub n m) : SubstEnv :=
  match n with
  | 0 => SubstEnv.empty
  | n + 1 =>
      let ρtail : QuoteEnv n := fun i => ρsrc i.succ
      let σtail : Sub n m := fun i => σ i.succ
      SubstEnv.extend (quoteSubstEnv ν k ρtail ρdst σtail)
        (ρsrc 0) (quoteTmWith ν k ρdst (σ 0))
termination_by n

theorem SubstEnv.find_extend_eq {env : SubstEnv} {x : String} {q : Pattern} :
    (SubstEnv.extend env x q).find x = some q := by
  simp [SubstEnv.extend, SubstEnv.find]

theorem SubstEnv.find_extend_ne {env : SubstEnv} {x y : String} {q : Pattern}
    (hxy : x ≠ y) :
    (SubstEnv.extend env x q).find y = env.find y := by
  simp [SubstEnv.extend, SubstEnv.find, beq_eq_false_iff_ne.mpr hxy]

/-- `applySubst` is extensional in `SubstEnv.find`. -/
theorem applySubst_congr_find
    {env₁ env₂ : SubstEnv}
    (hfind : ∀ name, env₁.find name = env₂.find name) :
    ∀ p : Pattern, applySubst env₁ p = applySubst env₂ p := by
  intro p
  induction p using Pattern.inductionOn with
  | hbvar n =>
      simp [applySubst]
  | hfvar name =>
      simp [applySubst, hfind name]
  | happly c args ih =>
      simp [applySubst]
      intro a ha
      exact ih a ha
  | hlambda body ih =>
      simpa [applySubst] using ih
  | hmultiLambda n body ih =>
      simpa [applySubst] using ih
  | hsubst body repl ihb ihr =>
      simp [applySubst, ihb, ihr]
  | hcollection ct elems rest ih =>
      simp [applySubst]
      intro a ha
      exact ih a ha

/-- `closeFVar` transport over extensionally equal substitution environments. -/
theorem closeFVar_applySubst_congr_find
    {env₁ env₂ : SubstEnv}
    (hfind : ∀ name, env₁.find name = env₂.find name)
    (ℓ : Nat) (x : String) (p : Pattern) :
    closeFVar ℓ x (applySubst env₁ p) = closeFVar ℓ x (applySubst env₂ p) := by
  simp [applySubst_congr_find hfind p]

/-- Extending an environment with `x ↦ fvar x` is a no-op when `x` is not already bound. -/
theorem applySubst_extend_fvar_self_of_find_none
    (env : SubstEnv) (x : String) (p : Pattern)
    (hfind : env.find x = none) :
    applySubst (SubstEnv.extend env x (.fvar x)) p = applySubst env p := by
  induction p using Pattern.inductionOn with
  | hbvar n =>
      simp [applySubst]
  | hfvar name =>
      by_cases hname : name = x
      · subst hname
        simp [applySubst, SubstEnv.find_extend_eq, hfind]
      · have hne : x ≠ name := by
          exact fun h => hname h.symm
        simp [applySubst, SubstEnv.find_extend_ne hne]
  | happly c args ih =>
      simp [applySubst]
      intro a ha
      exact ih a ha
  | hlambda body ih =>
      simpa [applySubst] using ih
  | hmultiLambda n body ih =>
      simpa [applySubst] using ih
  | hsubst body repl ihb ihr =>
      simp [applySubst, ihb, ihr]
  | hcollection ct elems rest ih =>
      simp [applySubst]
      intro a ha
      exact ih a ha

theorem quoteSubstEnv_find
    (ν : Nat → String) (k : Nat) (ρsrc : QuoteEnv n) (ρdst : QuoteEnv m) (σ : Sub n m)
    (hsrcInj : Function.Injective ρsrc) (i : Fin n) :
    (quoteSubstEnv ν k ρsrc ρdst σ).find (ρsrc i) =
      some (quoteTmWith ν k ρdst (σ i)) := by
  induction n with
  | zero =>
      exact Fin.elim0 i
  | succ n ih =>
      cases i using Fin.cases with
      | zero =>
          simp [quoteSubstEnv, SubstEnv.find_extend_eq]
      | succ j =>
          have hneq : ρsrc 0 ≠ ρsrc j.succ := by
            intro heq
            have : (0 : Fin (n + 1)) = j.succ := hsrcInj heq
            cases this
          have htailInj : Function.Injective (fun t : Fin n => ρsrc t.succ) := by
            intro a b hab
            have hEq : (a.succ : Fin (n + 1)) = b.succ := hsrcInj (by simpa using hab)
            exact Fin.ext (by simpa using congrArg Fin.val hEq)
          simpa [quoteSubstEnv, SubstEnv.find_extend_ne hneq] using
            ih (ρsrc := fun t : Fin n => ρsrc t.succ)
              (σ := fun t : Fin n => σ t.succ) htailInj j

theorem quoteSubstEnv_find_none_future
    (ν : Nat → String) (k : Nat) (ρsrc : QuoteEnv n) (ρdst : QuoteEnv m) (σ : Sub n m)
    (hcompatSrc : QuoteCompat ν k ρsrc) {j : Nat} (hj : k ≤ j) :
    (quoteSubstEnv ν k ρsrc ρdst σ).find (ν j) = none := by
  induction n with
  | zero =>
      simp [quoteSubstEnv, SubstEnv.find, SubstEnv.empty]
  | succ n ih =>
      have hheadneq : ρsrc 0 ≠ ν j := hcompatSrc.2 0 j hj
      have htailCompat : QuoteCompat ν k (fun t : Fin n => ρsrc t.succ) := by
        refine ⟨hcompatSrc.1, ?_⟩
        intro i j' hk
        exact hcompatSrc.2 i.succ j' hk
      simpa [quoteSubstEnv, SubstEnv.find_extend_ne hheadneq] using
        ih (ρsrc := fun t : Fin n => ρsrc t.succ)
          (σ := fun t : Fin n => σ t.succ) htailCompat

theorem quoteSubstEnv_find_some_exists
    (ν : Nat → String) (k : Nat) (ρsrc : QuoteEnv n) (ρdst : QuoteEnv m) (σ : Sub n m)
    {name : String} {r : Pattern}
    (hfind : (quoteSubstEnv ν k ρsrc ρdst σ).find name = some r) :
    ∃ i : Fin n, ρsrc i = name ∧ r = quoteTmWith ν k ρdst (σ i) := by
  induction n with
  | zero =>
      simp [quoteSubstEnv, SubstEnv.find, SubstEnv.empty] at hfind
  | succ n ih =>
      by_cases hEq : ρsrc 0 = name
      · refine ⟨0, hEq, ?_⟩
        have hhead :
            (quoteSubstEnv ν k ρsrc ρdst σ).find name =
              some (quoteTmWith ν k ρdst (σ 0)) := by
          simp [quoteSubstEnv, SubstEnv.find, hEq, SubstEnv.extend]
        rw [hhead] at hfind
        exact (Option.some.inj hfind).symm
      · have hEqBool : (ρsrc 0 == name) = false := by
          exact beq_eq_false_iff_ne.mpr hEq
        have htail :
            (quoteSubstEnv ν k (fun t : Fin n => ρsrc t.succ) ρdst
              (fun t : Fin n => σ t.succ)).find name = some r := by
          simpa [quoteSubstEnv, SubstEnv.find, hEqBool, SubstEnv.extend] using hfind
        rcases ih (ρsrc := fun t : Fin n => ρsrc t.succ) (σ := fun t : Fin n => σ t.succ) htail with
          ⟨i, hiName, hiVal⟩
        exact ⟨i.succ, hiName, hiVal⟩

abbrev SubstEnvIsIdentity (env : SubstEnv) : Prop :=
  ∀ name r, env.find name = some r → r = .fvar name

private theorem list_map_eq_self_local {f : Pattern → Pattern} {l : List Pattern}
    (h : ∀ a ∈ l, f a = a) : l.map f = l := by
  induction l with
  | nil =>
      rfl
  | cons a as ih =>
      simp [h a List.mem_cons_self, ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem applySubst_of_isIdentity
    (env : SubstEnv) (hId : SubstEnvIsIdentity env)
    (p : Pattern) (hnes : noExplicitSubst p = true) :
    applySubst env p = p := by
  induction p using Pattern.inductionOn with
  | hbvar n =>
      simp [applySubst]
  | hfvar name =>
      cases hfind : env.find name with
      | none =>
          simp [applySubst, hfind]
      | some r =>
          have hr : r = .fvar name := hId name r hfind
          simp [applySubst, hfind, hr]
  | happly c args ih =>
      simp [applySubst]
      exact list_map_eq_self_local (fun a ha => ih a ha (allNoExplicitSubst_mem hnes ha))
  | hlambda body ih =>
      simpa [applySubst, noExplicitSubst] using ih (by simpa [noExplicitSubst] using hnes)
  | hmultiLambda n body ih =>
      simpa [applySubst, noExplicitSubst] using ih (by simpa [noExplicitSubst] using hnes)
  | hsubst body repl ihb ihr =>
      exact absurd hnes Bool.false_ne_true
  | hcollection ct elems rest ih =>
      simp [applySubst]
      exact list_map_eq_self_local (fun a ha => ih a ha (allNoExplicitSubst_mem hnes ha))

/-- If `env` is identity-on-lookup, extending it with `x ↦ q` is observationally
equivalent to extending `empty` with `x ↦ q` on patterns without explicit substitutions. -/
theorem applySubst_extend_identity_inert
    (env : SubstEnv) (hId : SubstEnvIsIdentity env)
    (x : String) (q : Pattern) (p : Pattern)
    (hnes : noExplicitSubst p = true) :
    applySubst (SubstEnv.extend env x q) p =
      applySubst (SubstEnv.extend SubstEnv.empty x q) p := by
  induction p using Pattern.inductionOn with
  | hbvar n =>
      simp [applySubst]
  | hfvar name =>
      by_cases hname : name = x
      · subst hname
        simp [applySubst, SubstEnv.find_extend_eq]
      · have hne : x ≠ name := fun h => hname h.symm
        have hleft : (SubstEnv.extend env x q).find name = env.find name :=
          SubstEnv.find_extend_ne hne
        have hright : (SubstEnv.extend SubstEnv.empty x q).find name = none :=
          by
            rw [SubstEnv.find_extend_ne hne]
            simp [SubstEnv.find, SubstEnv.empty]
        cases hEnv : env.find name with
        | none =>
            simp [applySubst, hleft, hright, hEnv]
        | some r =>
            have hr : r = .fvar name := hId name r hEnv
            simp [applySubst, hleft, hright, hEnv, hr]
  | happly c args ih =>
      simp [applySubst]
      intro a ha
      exact ih a ha (allNoExplicitSubst_mem hnes ha)
  | hlambda body ih =>
      simpa [applySubst, noExplicitSubst] using
        ih (by simpa [noExplicitSubst] using hnes)
  | hmultiLambda n body ih =>
      simpa [applySubst, noExplicitSubst] using
        ih (by simpa [noExplicitSubst] using hnes)
  | hsubst body repl _ _ =>
      exact absurd hnes Bool.false_ne_true
  | hcollection ct elems rest ih =>
      simp [applySubst]
      intro a ha
      exact ih a ha (allNoExplicitSubst_mem hnes ha)

theorem quoteSubstEnv_ids_isIdentity
    (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n) :
    SubstEnvIsIdentity (quoteSubstEnv ν k ρ ρ ids) := by
  intro name r hfind
  rcases quoteSubstEnv_find_some_exists ν k ρ ρ ids hfind with ⟨i, hiName, hiVal⟩
  calc
    r = quoteTmWith ν k ρ (ids i) := hiVal
    _ = .fvar (ρ i) := by simp [ids, quoteTmWith]
    _ = .fvar name := by simp [hiName]

theorem applySubst_quoteSubstEnv_ids
    (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n) (p : Pattern)
    (hnes : noExplicitSubst p = true) :
    applySubst (quoteSubstEnv ν k ρ ρ ids) p = p := by
  exact applySubst_of_isIdentity (quoteSubstEnv ν k ρ ρ ids)
    (quoteSubstEnv_ids_isIdentity ν k ρ) p hnes

theorem quoteSubstEnv_subst0_decompose
    (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n) (a : PureTm n) :
    quoteSubstEnv ν k (envCons (ν k) ρ) ρ (subst0 a) =
      SubstEnv.extend (quoteSubstEnv ν k ρ ρ ids) (ν k) (quoteTmWith ν k ρ a) := by
  simpa [ids] using (by
    simp [quoteSubstEnv, envCons, subst0] :
      quoteSubstEnv ν k (envCons (ν k) ρ) ρ (subst0 a) =
        SubstEnv.extend (quoteSubstEnv ν k (fun i => ρ i) ρ (fun i => PureTm.var i))
          (ν k) (quoteTmWith ν k ρ a))

theorem quoteSubstEnv_rename_wk_envCons_find
    (ν : Nat → String) (k : Nat) (x : String)
    (ρsrc : QuoteEnv n) (ρdst : QuoteEnv m) (σ : Sub n m) (name : String) :
    (quoteSubstEnv ν k ρsrc (envCons x ρdst) (fun i => rename wk (σ i))).find name =
      (quoteSubstEnv ν k ρsrc ρdst σ).find name := by
  induction n with
  | zero =>
      simp [quoteSubstEnv]
  | succ n ih =>
      by_cases hhead : ρsrc 0 = name
      · subst hhead
        have hheadVal :
            quoteTmWith ν k (envCons x ρdst) (rename wk (σ 0)) =
              quoteTmWith ν k ρdst (σ 0) := by
          simpa using quoteTmWith_rename_wk_envCons ν k x ρdst (σ 0)
        simp [quoteSubstEnv, hheadVal, SubstEnv.find_extend_eq]
      · have hhead' : (ρsrc 0 == name) = false := beq_eq_false_iff_ne.mpr hhead
        have hheadVal :
            quoteTmWith ν k (envCons x ρdst) (rename wk (σ 0)) =
              quoteTmWith ν k ρdst (σ 0) := by
          simpa using quoteTmWith_rename_wk_envCons ν k x ρdst (σ 0)
        have htail := ih (ρsrc := fun i => ρsrc i.succ) (σ := fun i => σ i.succ)
        let leftTail : SubstEnv :=
          quoteSubstEnv ν k (fun i => ρsrc i.succ) (envCons x ρdst) (fun i => rename wk (σ i.succ))
        let rightTail : SubstEnv :=
          quoteSubstEnv ν k (fun i => ρsrc i.succ) ρdst (fun i => σ i.succ)
        have hleftExpand :
            (quoteSubstEnv ν k ρsrc (envCons x ρdst) (fun i => rename wk (σ i))).find name =
              (leftTail.extend (ρsrc 0) (quoteTmWith ν k ρdst (σ 0))).find name := by
          simp [quoteSubstEnv, leftTail, hheadVal]
        have hrightExpand :
            (quoteSubstEnv ν k ρsrc ρdst σ).find name =
              (rightTail.extend (ρsrc 0) (quoteTmWith ν k ρdst (σ 0))).find name := by
          simp [quoteSubstEnv, rightTail]
        have hleft :
            (leftTail.extend (ρsrc 0) (quoteTmWith ν k ρdst (σ 0))).find name =
              leftTail.find name := by
          exact SubstEnv.find_extend_ne hhead
        have hright :
            (rightTail.extend (ρsrc 0) (quoteTmWith ν k ρdst (σ 0))).find name =
              rightTail.find name := by
          exact SubstEnv.find_extend_ne hhead
        calc
          (quoteSubstEnv ν k ρsrc (envCons x ρdst) (fun i => rename wk (σ i))).find name
              = (leftTail.extend (ρsrc 0) (quoteTmWith ν k ρdst (σ 0))).find name := hleftExpand
          _ = leftTail.find name := hleft
          _ = rightTail.find name := by simpa [leftTail, rightTail] using htail
          _ = (rightTail.extend (ρsrc 0) (quoteTmWith ν k ρdst (σ 0))).find name := by
                symm; exact hright
          _ = (quoteSubstEnv ν k ρsrc ρdst σ).find name := hrightExpand.symm

theorem quoteSubstEnv_liftSub_find
    (ν : Nat → String) (k : Nat) (ρsrc : QuoteEnv n) (ρdst : QuoteEnv m)
    (σ : Sub n m) (name : String) :
    (quoteSubstEnv ν (k + 1) (envCons (ν k) ρsrc) (envCons (ν k) ρdst) (liftSub σ)).find name =
      ((quoteSubstEnv ν (k + 1) ρsrc ρdst σ).extend (ν k) (.fvar (ν k))).find name := by
  by_cases hnk : ν k = name
  · subst hnk
    simp [quoteSubstEnv, envCons, quoteTmWith, SubstEnv.find_extend_eq]
  · have hnk' : ν k ≠ name := hnk
    calc
      (quoteSubstEnv ν (k + 1) (envCons (ν k) ρsrc) (envCons (ν k) ρdst) (liftSub σ)).find name
          = (quoteSubstEnv ν (k + 1) ρsrc (envCons (ν k) ρdst)
              (fun i => rename wk (σ i))).find name := by
              simp [quoteSubstEnv, envCons, liftSub, SubstEnv.find_extend_ne hnk']
      _ = (quoteSubstEnv ν (k + 1) ρsrc ρdst σ).find name :=
            quoteSubstEnv_rename_wk_envCons_find ν (k + 1) (ν k) ρsrc ρdst σ name
      _ = ((quoteSubstEnv ν (k + 1) ρsrc ρdst σ).extend (ν k) (.fvar (ν k))).find name := by
            symm
            exact SubstEnv.find_extend_ne hnk'

mutual
  theorem noExplicitSubst_closeFVar (k : Nat) (x : String) (p : Pattern) :
      noExplicitSubst (closeFVar k x p) = noExplicitSubst p := by
    induction p using Pattern.inductionOn generalizing k with
    | hbvar _ =>
        simp [closeFVar, noExplicitSubst]
    | hfvar y =>
        by_cases hy : y = x
        · simp [closeFVar, noExplicitSubst, hy]
        · simp [closeFVar, noExplicitSubst, hy]
    | happly c args ih =>
        simpa [closeFVar, noExplicitSubst] using
          allNoExplicitSubst_map_closeFVar k x args ih
    | hlambda body ih =>
        simpa [closeFVar, noExplicitSubst] using ih (k + 1)
    | hmultiLambda n body ih =>
        simpa [closeFVar, noExplicitSubst] using ih (k + n)
    | hsubst body repl ihb ihr =>
        simp [closeFVar, noExplicitSubst]
    | hcollection ct elems rest ih =>
        simpa [closeFVar, noExplicitSubst] using
          allNoExplicitSubst_map_closeFVar k x elems ih

  theorem allNoExplicitSubst_map_closeFVar (k : Nat) (x : String)
      (ps : List Pattern)
      (ih : ∀ p, p ∈ ps → ∀ k, noExplicitSubst (closeFVar k x p) = noExplicitSubst p) :
      allNoExplicitSubst (ps.map (closeFVar k x)) = allNoExplicitSubst ps := by
    induction ps with
    | nil =>
        simp [allNoExplicitSubst]
    | cons p ps ihps =>
        simp [allNoExplicitSubst, ih p List.mem_cons_self k,
          ihps (fun q hq => ih q (List.mem_cons_of_mem _ hq))]
end

theorem lc_at_closeFVar_of_lt {k l : Nat} (x : String) (p : Pattern)
    (hl : l < k) (hp : lc_at k p = true) :
    lc_at k (closeFVar l x p) = true := by
  induction p using Pattern.inductionOn generalizing k l with
  | hbvar n =>
      simpa [closeFVar, lc_at] using hp
  | hfvar y =>
      by_cases hy : y = x
      · simp [closeFVar, lc_at, hy, hl]
      · simp [closeFVar, lc_at, hy]
  | happly c args ih =>
      simp only [lc_at] at hp
      simp only [closeFVar, lc_at]
      induction args with
      | nil =>
          simp [lc_at_list]
      | cons a as ihas =>
          simp only [List.map_cons, lc_at_list, Bool.and_eq_true] at hp ⊢
          exact ⟨ih a List.mem_cons_self hl hp.1,
                 ihas (fun q hq => ih q (List.mem_cons_of_mem _ hq)) hp.2⟩
  | hlambda body ih =>
      simp only [closeFVar, lc_at] at hp ⊢
      exact ih (Nat.succ_lt_succ hl) hp
  | hmultiLambda n body ih =>
      simp only [closeFVar, lc_at] at hp ⊢
      exact ih (Nat.add_lt_add_right hl n) hp
  | hsubst body repl ihb ihr =>
      simp only [closeFVar, lc_at, Bool.and_eq_true] at hp ⊢
      exact ⟨ihb (Nat.succ_lt_succ hl) hp.1, ihr hl hp.2⟩
  | hcollection ct elems rest ih =>
      simp only [lc_at] at hp
      simp only [closeFVar, lc_at]
      induction elems with
      | nil =>
          simp [lc_at_list]
      | cons a as ihas =>
          simp only [List.map_cons, lc_at_list, Bool.and_eq_true] at hp ⊢
          exact ⟨ih a List.mem_cons_self hl hp.1,
                 ihas (fun q hq => ih q (List.mem_cons_of_mem _ hq)) hp.2⟩

theorem not_mem_freeVars_closeFVar_self (k : Nat) (x : String) (p : Pattern) :
    x ∉ freeVars (closeFVar k x p) := by
  induction p using Pattern.inductionOn generalizing k with
  | hbvar _ =>
      simp [closeFVar, freeVars]
  | hfvar y =>
      by_cases hy : y = x
      · simp [closeFVar, freeVars, hy]
      · have hxy : x ≠ y := fun h => hy h.symm
        simp [closeFVar, freeVars, hy, hxy]
  | happly c args ih =>
      intro hx
      simp [closeFVar, freeVars, List.mem_flatMap] at hx
      rcases hx with ⟨a, ha, hxa⟩
      exact (ih a ha k) hxa
  | hlambda body ih =>
      simpa [closeFVar, freeVars] using ih (k + 1)
  | hmultiLambda n body ih =>
      simpa [closeFVar, freeVars] using ih (k + n)
  | hsubst body repl ihb ihr =>
      intro hx
      simp [closeFVar, freeVars, List.mem_append] at hx
      cases hx with
      | inl hxBody => exact (ihb (k + 1) hxBody)
      | inr hxRepl => exact (ihr k hxRepl)
  | hcollection ct elems rest ih =>
      intro hx
      simp [closeFVar, freeVars, List.mem_flatMap] at hx
      rcases hx with ⟨a, ha, hxa⟩
      exact (ih a ha k) hxa

theorem isFresh_closeFVar_self (k : Nat) (x : String) (p : Pattern) :
    isFresh x (closeFVar k x p) = true := by
  have hnot : x ∉ freeVars (closeFVar k x p) := not_mem_freeVars_closeFVar_self k x p
  unfold isFresh
  rw [Bool.not_eq_true']
  apply Bool.eq_false_iff.mpr
  intro htrue
  exact hnot (List.contains_iff_mem.mp htrue)

private theorem list_map_eq_map {f g : Pattern → Pattern} {l : List Pattern}
    (h : ∀ a ∈ l, f a = g a) : l.map f = l.map g := by
  induction l with
  | nil => rfl
  | cons a as ih =>
      simp [h a List.mem_cons_self, ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

private theorem list_map_eq_self {f : Pattern → Pattern} {l : List Pattern}
    (h : ∀ a ∈ l, f a = a) : l.map f = l := by
  simpa [List.map_id] using
    (list_map_eq_map (f := f) (g := fun a => a) (l := l) h)

theorem closeFVar_fresh_id (k : Nat) (x : String) (p : Pattern)
    (hfresh : isFresh x p = true) :
    closeFVar k x p = p := by
  suffices h : ∀ p : Pattern, ∀ k : Nat, isFresh x p = true → closeFVar k x p = p from
    h p k hfresh
  intro p
  induction p using Pattern.inductionOn with
  | hbvar n =>
      intro k _
      simp [closeFVar]
  | hfvar y =>
      intro k hfresh
      have hne : y ≠ x := Ne.symm (isFresh_fvar_neq (x := x) (y := y) hfresh)
      simp [closeFVar, hne]
  | happly c args ih =>
      intro k hfresh
      simp [closeFVar]
      exact list_map_eq_self (fun a ha => by
        simpa using ih a ha k (isFresh_mem_of_flatMap hfresh ha))
  | hlambda body ih =>
      intro k hfresh
      simpa [closeFVar, isFresh_lambda_iff] using ih (k + 1) (by simpa [isFresh_lambda_iff] using hfresh)
  | hmultiLambda n body ih =>
      intro k hfresh
      have hbody : isFresh x body = true := by simpa [isFresh, freeVars] using hfresh
      simpa [closeFVar] using ih (k + n) hbody
  | hsubst body repl ihb ihr =>
      intro k hfresh
      have hparts : (freeVars body).contains x = false ∧ (freeVars repl).contains x = false := by
        simpa [isFresh, freeVars, Bool.not_eq_true', List.contains_append, Bool.or_eq_false_iff] using hfresh
      have hbody : isFresh x body = true := by simpa [isFresh, Bool.not_eq_true'] using hparts.1
      have hrepl : isFresh x repl = true := by simpa [isFresh, Bool.not_eq_true'] using hparts.2
      simp [closeFVar, ihb (k + 1) hbody, ihr k hrepl]
  | hcollection ct elems rest ih =>
      intro k hfresh
      simp [closeFVar]
      exact list_map_eq_self (fun a ha => by
        simpa using ih a ha k (isFresh_collection_mem hfresh ha))

/-- Closing two distinct free names commutes (same binder depth). -/
theorem closeFVar_comm (k : Nat) {x y : String} (hxy : x ≠ y) (p : Pattern) :
    closeFVar k x (closeFVar k y p) = closeFVar k y (closeFVar k x p) := by
  induction p using Pattern.inductionOn generalizing k with
  | hbvar n =>
      simp [closeFVar]
  | hfvar z =>
      by_cases hzx : z = x
      · subst hzx
        simp [closeFVar, hxy]
      · by_cases hzy : z = y
        · subst hzy
          simp [closeFVar, hzx]
        · simp [closeFVar, hzx, hzy]
  | happly c args ih =>
      simp [closeFVar]
      intro a ha
      exact ih a ha k
  | hlambda body ih =>
      simpa [closeFVar] using ih (k + 1)
  | hmultiLambda n body ih =>
      simpa [closeFVar] using ih (k + n)
  | hsubst body repl ihb ihr =>
      simp [closeFVar, ihb (k + 1), ihr k]
  | hcollection ct elems rest ih =>
      simp [closeFVar]
      intro a ha
      exact ih a ha k

theorem applySubst_single_closeFVar_comm
    {x y : String} {q p : Pattern} {k : Nat}
    (hxy : y ≠ x) (hfresh : isFresh y q = true) (hnes : noExplicitSubst p = true) :
    applySubst (SubstEnv.extend SubstEnv.empty x q) (closeFVar k y p) =
      closeFVar k y (applySubst (SubstEnv.extend SubstEnv.empty x q) p) := by
  suffices h : ∀ p : Pattern, ∀ k : Nat, noExplicitSubst p = true →
      applySubst (SubstEnv.extend SubstEnv.empty x q) (closeFVar k y p) =
        closeFVar k y (applySubst (SubstEnv.extend SubstEnv.empty x q) p) from
    h p k hnes
  intro p
  induction p using Pattern.inductionOn with
  | hbvar n =>
      intro k _
      simp [applySubst, closeFVar]
  | hfvar name =>
      intro k _
      by_cases hny : name = y
      · subst hny
        simp [closeFVar, applySubst, SubstEnv.find_extend_empty_ne (Ne.symm hxy)]
      · by_cases hnx : name = x
        · subst hnx
          simpa [closeFVar, applySubst, hny, SubstEnv.find_extend_empty_eq] using
            (closeFVar_fresh_id k y q hfresh).symm
        · have hxn' : x ≠ name := fun h => hnx h.symm
          simp [closeFVar, applySubst, hny, SubstEnv.find_extend_empty_ne hxn']
  | happly c args ih =>
      intro k hnes
      simp [applySubst, closeFVar]
      intro a ha
      simpa using ih a ha k (allNoExplicitSubst_mem hnes ha)
  | hlambda body ih =>
      intro k hnes
      simpa [applySubst, closeFVar] using ih (k + 1) (by simpa [noExplicitSubst] using hnes)
  | hmultiLambda n body ih =>
      intro k hnes
      simpa [applySubst, closeFVar] using ih (k + n) (by simpa [noExplicitSubst] using hnes)
  | hsubst body repl _ _ =>
      intro _ hnes
      exact absurd hnes Bool.false_ne_true
  | hcollection ct elems rest ih =>
      intro k hnes
      simp [applySubst, closeFVar]
      intro a ha
      simpa using ih a ha k (allNoExplicitSubst_mem hnes ha)

theorem freeVars_closeFVar_mem_of_ne (k : Nat) {x z : String} (p : Pattern)
    (hneq : z ≠ x) :
    z ∈ freeVars (closeFVar k x p) → z ∈ freeVars p := by
  induction p using Pattern.inductionOn generalizing k with
  | hbvar _ =>
      intro hz
      simp [closeFVar, freeVars] at hz
  | hfvar y =>
      intro hz
      by_cases hy : y = x
      · subst hy
        simp [closeFVar, freeVars] at hz
      · simpa [closeFVar, freeVars, hy] using hz
  | happly c args ih =>
      intro hz
      simp [closeFVar, freeVars, List.mem_flatMap] at hz ⊢
      rcases hz with ⟨a, ha, hza⟩
      exact ⟨a, ha, ih a ha k hza⟩
  | hlambda body ih =>
      intro hz
      simp [closeFVar, freeVars] at hz
      simpa [freeVars] using ih (k + 1) hz
  | hmultiLambda n body ih =>
      intro hz
      simp [closeFVar, freeVars] at hz
      simpa [freeVars] using ih (k + n) hz
  | hsubst body repl ihb ihr =>
      intro hz
      simp [closeFVar, freeVars, List.mem_append] at hz ⊢
      cases hz with
      | inl hzBody => exact Or.inl (ihb (k + 1) hzBody)
      | inr hzRepl => exact Or.inr (ihr k hzRepl)
  | hcollection ct elems rest ih =>
      intro hz
      simp [closeFVar, freeVars, List.mem_flatMap] at hz ⊢
      rcases hz with ⟨a, ha, hza⟩
      exact ⟨a, ha, ih a ha k hza⟩

theorem isFresh_closeFVar_ne (k : Nat) {x z : String} {p : Pattern}
    (hneq : z ≠ x) (hfresh : isFresh z p = true) :
    isFresh z (closeFVar k x p) = true := by
  have hcontFalse : (freeVars p).contains z = false := by
    by_cases hcz : (freeVars p).contains z = false
    · exact hcz
    · have htmp : z ∉ freeVars p := by simpa [isFresh] using hfresh
      have hctrue : (freeVars p).contains z = true := by
        cases hc : (freeVars p).contains z with
        | false => exact False.elim (hcz hc)
        | true => rfl
      have hz : z ∈ freeVars p := List.contains_iff_mem.mp hctrue
      exact False.elim (htmp hz)
  unfold isFresh
  rw [Bool.not_eq_true']
  apply Bool.eq_false_iff.mpr
  intro htrue
  have hzClose : z ∈ freeVars (closeFVar k x p) := List.contains_iff_mem.mp htrue
  have hz : z ∈ freeVars p := freeVars_closeFVar_mem_of_ne k p hneq hzClose
  have hpTrue : (freeVars p).contains z = true := List.contains_iff_mem.mpr hz
  have hcontra : false = true := (Eq.symm hcontFalse).trans hpTrue
  exact Bool.false_ne_true hcontra

/-- Every free variable in a contextual quote comes from the context environment `ρ`. -/
theorem freeVars_quoteTmWith_mem_env
    (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n) (t : PureTm n)
    {z : String} :
    z ∈ freeVars (quoteTmWith ν k ρ t) → ∃ i : Fin n, ρ i = z := by
  induction t generalizing k with
  | var i =>
      intro hz
      simp [quoteTmWith, freeVars] at hz
      exact ⟨i, hz.symm⟩
  | u0 =>
      intro hz
      simp [quoteTmWith, u0, freeVars] at hz
  | u1 =>
      intro hz
      simp [quoteTmWith, u1, freeVars] at hz
  | pi A B ihA ihB =>
      intro hz
      simp [quoteTmWith, mkPi, freeVars, List.mem_append] at hz
      cases hz with
      | inl hzA =>
          exact ihA (k := k) (ρ := ρ) hzA
      | inr hzClose =>
          let x := ν k
          have hzNeX : z ≠ x := by
            intro hzx
            subst hzx
            exact (not_mem_freeVars_closeFVar_self 0 x
              (quoteTmWith ν (k + 1) (envCons x ρ) B)) hzClose
          have hzBody : z ∈ freeVars (quoteTmWith ν (k + 1) (envCons x ρ) B) := by
            exact freeVars_closeFVar_mem_of_ne 0
              (p := quoteTmWith ν (k + 1) (envCons x ρ) B) hzNeX hzClose
          rcases ihB (k := k + 1) (ρ := envCons x ρ) hzBody with ⟨i, hi⟩
          exact Fin.cases
            (motive := fun i => envCons x ρ i = z → ∃ j, ρ j = z)
            (fun h0 => False.elim (hzNeX (by simpa [envCons] using h0.symm)))
            (fun j hs => ⟨j, by simpa [envCons] using hs⟩)
            i hi
  | sigma A B ihA ihB =>
      intro hz
      simp [quoteTmWith, mkSigma, freeVars, List.mem_append] at hz
      cases hz with
      | inl hzA =>
          exact ihA (k := k) (ρ := ρ) hzA
      | inr hzClose =>
          let x := ν k
          have hzNeX : z ≠ x := by
            intro hzx
            subst hzx
            exact (not_mem_freeVars_closeFVar_self 0 x
              (quoteTmWith ν (k + 1) (envCons x ρ) B)) hzClose
          have hzBody : z ∈ freeVars (quoteTmWith ν (k + 1) (envCons x ρ) B) := by
            exact freeVars_closeFVar_mem_of_ne 0
              (p := quoteTmWith ν (k + 1) (envCons x ρ) B) hzNeX hzClose
          rcases ihB (k := k + 1) (ρ := envCons x ρ) hzBody with ⟨i, hi⟩
          exact Fin.cases
            (motive := fun i => envCons x ρ i = z → ∃ j, ρ j = z)
            (fun h0 => False.elim (hzNeX (by simpa [envCons] using h0.symm)))
            (fun j hs => ⟨j, by simpa [envCons] using hs⟩)
            i hi
  | id A a b ihA iha ihb =>
      intro hz
      simp [quoteTmWith, mkId, freeVars, List.mem_append] at hz
      rcases hz with hz | hz
      · exact ihA (k := k) (ρ := ρ) hz
      · rcases hz with hz | hz
        · exact iha (k := k) (ρ := ρ) hz
        · exact ihb (k := k) (ρ := ρ) hz
  | lam b ih =>
      intro hz
      simp [quoteTmWith, mkLam, freeVars] at hz
      let x := ν k
      have hzNeX : z ≠ x := by
        intro hzx
        subst hzx
        exact (not_mem_freeVars_closeFVar_self 0 x
          (quoteTmWith ν (k + 1) (envCons x ρ) b)) hz
      have hzBody : z ∈ freeVars (quoteTmWith ν (k + 1) (envCons x ρ) b) := by
        exact freeVars_closeFVar_mem_of_ne 0
          (p := quoteTmWith ν (k + 1) (envCons x ρ) b) hzNeX hz
      rcases ih (k := k + 1) (ρ := envCons x ρ) hzBody with ⟨i, hi⟩
      exact Fin.cases
        (motive := fun i => envCons x ρ i = z → ∃ j, ρ j = z)
        (fun h0 => False.elim (hzNeX (by simpa [envCons] using h0.symm)))
        (fun j hs => ⟨j, by simpa [envCons] using hs⟩)
        i hi
  | app f a ihf iha =>
      intro hz
      simp [quoteTmWith, mkApp, freeVars, List.mem_append] at hz
      cases hz with
      | inl hzf => exact ihf (k := k) (ρ := ρ) hzf
      | inr hza => exact iha (k := k) (ρ := ρ) hza
  | pair a b iha ihb =>
      intro hz
      simp [quoteTmWith, mkPair, freeVars, List.mem_append] at hz
      cases hz with
      | inl hza => exact iha (k := k) (ρ := ρ) hza
      | inr hzb => exact ihb (k := k) (ρ := ρ) hzb
  | fst p ih =>
      intro hz
      simp [quoteTmWith, mkFst, freeVars] at hz
      exact ih (k := k) (ρ := ρ) hz
  | snd p ih =>
      intro hz
      simp [quoteTmWith, mkSnd, freeVars] at hz
      exact ih (k := k) (ρ := ρ) hz
  | refl a iha =>
      intro hz
      simp [quoteTmWith, mkRefl, freeVars] at hz
      exact iha (k := k) (ρ := ρ) hz

/-- Any future binder name `ν j` (`j ≥ k`) is fresh in the quote under `QuoteCompat`. -/
theorem isFresh_quoteTmWith_future
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ) (t : PureTm n) {j : Nat} (hj : k ≤ j) :
    isFresh (ν j) (quoteTmWith ν k ρ t) = true := by
  unfold isFresh
  rw [Bool.not_eq_true']
  apply Bool.eq_false_iff.mpr
  intro hcontains
  have hz : ν j ∈ freeVars (quoteTmWith ν k ρ t) := List.contains_iff_mem.mp hcontains
  rcases freeVars_quoteTmWith_mem_env ν k ρ t hz with ⟨i, hi⟩
  exact (hcompat.2 i j hj) hi

/-- Specialization of `isFresh_quoteTmWith_future` at the next binder index. -/
theorem isFresh_quoteTmWith_next
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ) (t : PureTm n) :
    isFresh (ν (k + 1)) (quoteTmWith ν k ρ t) = true :=
  isFresh_quoteTmWith_future hcompat t (j := k + 1) (by omega)

theorem quoteSubstEnv_liftSub_find_head
    (ν : Nat → String) (k : Nat) (ρsrc : QuoteEnv n) (ρdst : QuoteEnv m)
    (σ : Sub n m) :
    (quoteSubstEnv ν (k + 1) (envCons (ν k) ρsrc) (envCons (ν k) ρdst) (liftSub σ)).find (ν k)
      = some (.fvar (ν k)) := by
  simpa [SubstEnv.find_extend_eq] using
    (quoteSubstEnv_liftSub_find ν k ρsrc ρdst σ (ν k))

theorem quoteSubstEnv_liftSub_find_ne
    (ν : Nat → String) (k : Nat) (ρsrc : QuoteEnv n) (ρdst : QuoteEnv m)
    (σ : Sub n m) (name : String) (hneq : name ≠ ν k) :
    (quoteSubstEnv ν (k + 1) (envCons (ν k) ρsrc) (envCons (ν k) ρdst) (liftSub σ)).find name =
      (quoteSubstEnv ν (k + 1) ρsrc ρdst σ).find name := by
  calc
    (quoteSubstEnv ν (k + 1) (envCons (ν k) ρsrc) (envCons (ν k) ρdst) (liftSub σ)).find name
        = ((quoteSubstEnv ν (k + 1) ρsrc ρdst σ).extend (ν k) (.fvar (ν k))).find name :=
            quoteSubstEnv_liftSub_find ν k ρsrc ρdst σ name
    _ = (quoteSubstEnv ν (k + 1) ρsrc ρdst σ).find name :=
          SubstEnv.find_extend_ne (fun h => hneq h.symm)

/-- At quote depth `k + 1`, the previous binder name `ν k` remains fresh under `QuoteCompat ν k`. -/
theorem isFresh_quoteTmWith_prev
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ) (t : PureTm n) :
    isFresh (ν k) (quoteTmWith ν (k + 1) ρ t) = true := by
  unfold isFresh
  rw [Bool.not_eq_true']
  apply Bool.eq_false_iff.mpr
  intro hcontains
  have hz : ν k ∈ freeVars (quoteTmWith ν (k + 1) ρ t) := List.contains_iff_mem.mp hcontains
  rcases freeVars_quoteTmWith_mem_env ν (k + 1) ρ t hz with ⟨i, hi⟩
  exact (hcompat.2 i k (by omega)) hi

/-- Binder transport for the lifted substitution environment under explicit closing.
This aligns the lifted env (`k+1`, `envCons`, `liftSub`) with the base env at
the same quote depth (`k+1`) through a `closeFVar` at arbitrary depth `ℓ`. -/
theorem closeFVar_applySubst_quoteSubstEnv_liftSub_align
    (ν : Nat → String) (k : Nat) (ρsrc : QuoteEnv n) (ρdst : QuoteEnv m)
    (σ : Sub n m) (hcompatDst : QuoteCompat ν k ρdst)
    (p : Pattern) (ℓ : Nat) (hnes : noExplicitSubst p = true) :
    closeFVar ℓ (ν k)
      (applySubst
        (quoteSubstEnv ν (k + 1) (envCons (ν k) ρsrc) (envCons (ν k) ρdst) (liftSub σ))
        p)
    =
    applySubst (quoteSubstEnv ν (k + 1) ρsrc ρdst σ)
      (closeFVar ℓ (ν k) p) := by
  induction p using Pattern.inductionOn generalizing ℓ with
  | hbvar n =>
      simp [applySubst, closeFVar]
  | hfvar name =>
      by_cases hname : name = ν k
      · subst hname
        simp [applySubst, closeFVar, quoteSubstEnv_liftSub_find_head]
      · have hfind := quoteSubstEnv_liftSub_find_ne ν k ρsrc ρdst σ name hname
        cases hbase : (quoteSubstEnv ν (k + 1) ρsrc ρdst σ).find name with
        | none =>
            simp [applySubst, closeFVar, hname, hfind, hbase]
        | some r =>
            have hsome : (quoteSubstEnv ν (k + 1) ρsrc ρdst σ).find name = some r := hbase
            rcases quoteSubstEnv_find_some_exists ν (k + 1) ρsrc ρdst σ hsome with ⟨i, _, hr⟩
            have hfresh : isFresh (ν k) r = true := by
              subst hr
              exact isFresh_quoteTmWith_prev hcompatDst (σ i)
            have hclose : closeFVar ℓ (ν k) r = r := closeFVar_fresh_id ℓ (ν k) r hfresh
            simp [applySubst, closeFVar, hname, hfind, hbase, hclose]
  | happly c args ih =>
      simp [applySubst, closeFVar]
      intro a ha
      exact ih a ha ℓ (allNoExplicitSubst_mem hnes ha)
  | hlambda body ih =>
      simpa [applySubst, closeFVar] using
        ih (ℓ + 1) (by simpa [noExplicitSubst] using hnes)
  | hmultiLambda n body ih =>
      simpa [applySubst, closeFVar] using
        ih (ℓ + n) (by simpa [noExplicitSubst] using hnes)
  | hsubst body repl ihb ihr =>
      exact absurd hnes Bool.false_ne_true
  | hcollection ct elems rest ih =>
      simp [applySubst, closeFVar]
      intro a ha
      exact ih a ha ℓ (allNoExplicitSubst_mem hnes ha)

/-- Commute singleton substitution past closing the *next* binder name, for quoted arguments. -/
theorem applySubst_single_closeFVar_comm_quote_next
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    (hcompat : QuoteCompat ν k ρ) {p : Pattern}
    (hnes : noExplicitSubst p = true) :
    applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν k ρ a))
      (closeFVar 0 (ν (k + 1)) p) =
    closeFVar 0 (ν (k + 1))
      (applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν k ρ a)) p) := by
  refine applySubst_single_closeFVar_comm ?hneq ?hfresh hnes
  · intro hEq
    have hk : k = k + 1 := hcompat.1 hEq.symm
    omega
  · exact isFresh_quoteTmWith_next hcompat a

theorem quoteSubstEnv_find_some_fresh_future
    (ν : Nat → String) (k : Nat) (ρsrc : QuoteEnv n) (ρdst : QuoteEnv m) (σ : Sub n m)
    (hcompatDst : QuoteCompat ν k ρdst) {name : String} {r : Pattern} {j : Nat} (hj : k ≤ j)
    (hfind : (quoteSubstEnv ν k ρsrc ρdst σ).find name = some r) :
    isFresh (ν j) r = true := by
  rcases quoteSubstEnv_find_some_exists ν k ρsrc ρdst σ hfind with ⟨i, _, rfl⟩
  exact isFresh_quoteTmWith_future hcompatDst (σ i) (j := j) hj

theorem applySubst_quoteSubstEnv_closeFVar_comm_future
    (ν : Nat → String) (k : Nat) (ρsrc : QuoteEnv n) (ρdst : QuoteEnv m) (σ : Sub n m)
    (hcompatSrc : QuoteCompat ν k ρsrc) (hcompatDst : QuoteCompat ν k ρdst)
    {j : Nat} (hj : k ≤ j) {p : Pattern} {ℓ : Nat}
    (hnes : noExplicitSubst p = true) :
    applySubst (quoteSubstEnv ν k ρsrc ρdst σ) (closeFVar ℓ (ν j) p) =
      closeFVar ℓ (ν j) (applySubst (quoteSubstEnv ν k ρsrc ρdst σ) p) := by
  suffices h :
      ∀ p : Pattern, ∀ ℓ : Nat, noExplicitSubst p = true →
        applySubst (quoteSubstEnv ν k ρsrc ρdst σ) (closeFVar ℓ (ν j) p) =
          closeFVar ℓ (ν j) (applySubst (quoteSubstEnv ν k ρsrc ρdst σ) p) from
    h p ℓ hnes
  intro p
  induction p using Pattern.inductionOn with
  | hbvar n =>
      intro ℓ _
      simp [applySubst, closeFVar]
  | hfvar name =>
      intro ℓ _
      by_cases hname : name = ν j
      · subst hname
        have hnone :
            (quoteSubstEnv ν k ρsrc ρdst σ).find (ν j) = none :=
          quoteSubstEnv_find_none_future ν k ρsrc ρdst σ hcompatSrc hj
        simp [applySubst, closeFVar, hnone]
      · by_cases hfind : (quoteSubstEnv ν k ρsrc ρdst σ).find name = none
        · simp [applySubst, closeFVar, hname, hfind]
        · rcases Option.ne_none_iff_exists'.mp hfind with ⟨r, hr⟩
          have hfreshR : isFresh (ν j) r = true :=
            quoteSubstEnv_find_some_fresh_future ν k ρsrc ρdst σ hcompatDst hj hr
          have hclose : closeFVar ℓ (ν j) r = r := closeFVar_fresh_id ℓ (ν j) r hfreshR
          simp [applySubst, closeFVar, hname, hr, hclose]
  | happly c args ih =>
      intro ℓ hnes
      simp [applySubst, closeFVar]
      intro a ha
      simpa using ih a ha ℓ (allNoExplicitSubst_mem hnes ha)
  | hlambda body ih =>
      intro ℓ hnes
      simpa [applySubst, closeFVar] using ih (ℓ + 1) (by simpa [noExplicitSubst] using hnes)
  | hmultiLambda n body ih =>
      intro ℓ hnes
      simpa [applySubst, closeFVar] using ih (ℓ + n) (by simpa [noExplicitSubst] using hnes)
  | hsubst body repl _ _ =>
      intro _ hnes
      exact absurd hnes Bool.false_ne_true
  | hcollection ct elems rest ih =>
      intro ℓ hnes
      simp [applySubst, closeFVar]
      intro a ha
      simpa using ih a ha ℓ (allNoExplicitSubst_mem hnes ha)

theorem noExplicitSubst_quoteTmWith (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n)
    (t : PureTm n) :
    noExplicitSubst (quoteTmWith ν k ρ t) = true := by
  induction t generalizing k with
  | var =>
      simp [quoteTmWith, noExplicitSubst]
  | u0 =>
      simp [quoteTmWith, u0, noExplicitSubst, allNoExplicitSubst]
  | u1 =>
      simp [quoteTmWith, u1, noExplicitSubst, allNoExplicitSubst]
  | pi A B ihA ihB =>
      simp [quoteTmWith, mkPi, noExplicitSubst, allNoExplicitSubst,
        ihA (k := k), noExplicitSubst_closeFVar,
        ihB (k := k + 1) (ρ := envCons (ν k) ρ)]
  | sigma A B ihA ihB =>
      simp [quoteTmWith, mkSigma, noExplicitSubst, allNoExplicitSubst,
        ihA (k := k), noExplicitSubst_closeFVar,
        ihB (k := k + 1) (ρ := envCons (ν k) ρ)]
  | id A a b ihA iha ihb =>
      simp [quoteTmWith, mkId, noExplicitSubst, allNoExplicitSubst,
        ihA (k := k), iha (k := k), ihb (k := k)]
  | lam b ih =>
      simp [quoteTmWith, mkLam, noExplicitSubst, allNoExplicitSubst,
        noExplicitSubst_closeFVar, ih (k := k + 1) (ρ := envCons (ν k) ρ)]
  | app f a ihf iha =>
      simp [quoteTmWith, mkApp, noExplicitSubst, allNoExplicitSubst,
        ihf (k := k), iha (k := k)]
  | pair a b iha ihb =>
      simp [quoteTmWith, mkPair, noExplicitSubst, allNoExplicitSubst,
        iha (k := k), ihb (k := k)]
  | fst p ih =>
      simp [quoteTmWith, mkFst, noExplicitSubst, allNoExplicitSubst, ih (k := k)]
  | snd p ih =>
      simp [quoteTmWith, mkSnd, noExplicitSubst, allNoExplicitSubst, ih (k := k)]
  | refl a iha =>
      simp [quoteTmWith, mkRefl, noExplicitSubst, allNoExplicitSubst, iha (k := k)]

theorem lc_quoteTmWith (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n) (t : PureTm n) :
    lc_at 0 (quoteTmWith ν k ρ t) = true := by
  induction t generalizing k with
  | var =>
      simp [quoteTmWith, lc_at]
  | u0 =>
      simp [quoteTmWith, u0, lc_at, lc_at_list]
  | u1 =>
      simp [quoteTmWith, u1, lc_at, lc_at_list]
  | pi A B ihA ihB =>
      have hA := ihA (k := k)
      have hB0 := ihB (k := k + 1) (ρ := envCons (ν k) ρ)
      have hB1 : lc_at 1 (quoteTmWith ν (k + 1) (envCons (ν k) ρ) B) = true :=
        lc_at_mono hB0 (Nat.zero_le 1)
      have hBClosed : lc_at 1 (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) B)) = true :=
        lc_at_closeFVar_of_lt (x := ν k) (p := quoteTmWith ν (k + 1) (envCons (ν k) ρ) B)
          (by omega) hB1
      simp [quoteTmWith, mkPi, lc_at, lc_at_list, hA, hBClosed]
  | sigma A B ihA ihB =>
      have hA := ihA (k := k)
      have hB0 := ihB (k := k + 1) (ρ := envCons (ν k) ρ)
      have hB1 : lc_at 1 (quoteTmWith ν (k + 1) (envCons (ν k) ρ) B) = true :=
        lc_at_mono hB0 (Nat.zero_le 1)
      have hBClosed : lc_at 1 (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) B)) = true :=
        lc_at_closeFVar_of_lt (x := ν k) (p := quoteTmWith ν (k + 1) (envCons (ν k) ρ) B)
          (by omega) hB1
      simp [quoteTmWith, mkSigma, lc_at, lc_at_list, hA, hBClosed]
  | id A a b ihA iha ihb =>
      simp [quoteTmWith, mkId, lc_at, lc_at_list, ihA (k := k), iha (k := k), ihb (k := k)]
  | lam b ih =>
      have hb0 := ih (k := k + 1) (ρ := envCons (ν k) ρ)
      have hb1 : lc_at 1 (quoteTmWith ν (k + 1) (envCons (ν k) ρ) b) = true :=
        lc_at_mono hb0 (Nat.zero_le 1)
      have hbClosed : lc_at 1 (closeFVar 0 (ν k) (quoteTmWith ν (k + 1) (envCons (ν k) ρ) b)) = true :=
        lc_at_closeFVar_of_lt (x := ν k) (p := quoteTmWith ν (k + 1) (envCons (ν k) ρ) b)
          (by omega) hb1
      simp [quoteTmWith, mkLam, lc_at, lc_at_list, hbClosed]
  | app f a ihf iha =>
      simp [quoteTmWith, mkApp, lc_at, lc_at_list, ihf (k := k), iha (k := k)]
  | pair a b iha ihb =>
      simp [quoteTmWith, mkPair, lc_at, lc_at_list, iha (k := k), ihb (k := k)]
  | fst p ih =>
      simp [quoteTmWith, mkFst, lc_at, lc_at_list, ih (k := k)]
  | snd p ih =>
      simp [quoteTmWith, mkSnd, lc_at, lc_at_list, ih (k := k)]
  | refl a iha =>
      simp [quoteTmWith, mkRefl, lc_at, lc_at_list, iha (k := k)]

/-- β-critical bridge step for contextual LN quotation:
opening the closed quoted body by an argument equals singleton substitution on the quoted body. -/
theorem quoteTmWith_open_close_as_applySubst
    (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n)
    (a : PureTm n) (body : PureTm (n + 1)) :
    let x := ν k
    let qb := quoteTmWith ν (k + 1) (envCons x ρ) body
    openBVar 0 (quoteTmWith ν k ρ a) (closeFVar 0 x qb) =
      applySubst (SubstEnv.extend SubstEnv.empty x (quoteTmWith ν k ρ a)) qb := by
  simp only
  let x := ν k
  let qb := quoteTmWith ν (k + 1) (envCons x ρ) body
  have hLcQb : lc_at 0 qb = true := by
    simpa [qb] using lc_quoteTmWith ν (k + 1) (envCons x ρ) body
  have hFreshClosed : isFresh x (closeFVar 0 x qb) = true := by
    simpa [qb] using isFresh_closeFVar_self 0 x qb
  have hNesClosed : noExplicitSubst (closeFVar 0 x qb) = true := by
    have hNesQb : noExplicitSubst qb = true := by
      simpa [qb] using noExplicitSubst_quoteTmWith ν (k + 1) (envCons x ρ) body
    simpa [noExplicitSubst_closeFVar] using hNesQb
  have hSubstIntro :=
    subst_intro (z := x) (u := quoteTmWith ν k ρ a) (p := closeFVar 0 x qb)
      hFreshClosed hNesClosed
  have hOpenClose : openBVar 0 (.fvar x) (closeFVar 0 x qb) = qb := by
    simpa [qb] using open_close_id 0 x qb hLcQb
  rw [hOpenClose] at hSubstIntro
  simpa using hSubstIntro.symm

/-- Contextual quotation commutes with kernel `inst0` into LN opening form. -/
theorem quoteTmWith_inst0_open
    (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n)
    (a : PureTm n) (body : PureTm (n + 1))
    (hinst0 :
      quoteTmWith ν k ρ (inst0 a body) =
        applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν k ρ a))
          (quoteTmWith ν (k + 1) (envCons (ν k) ρ) body)) :
    quoteTmWith ν k ρ (inst0 a body) =
      openBVar 0 (quoteTmWith ν k ρ a)
        (closeFVar 0 (ν k)
          (quoteTmWith ν (k + 1) (envCons (ν k) ρ) body)) := by
  calc
    quoteTmWith ν k ρ (inst0 a body)
        = applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν k ρ a))
            (quoteTmWith ν (k + 1) (envCons (ν k) ρ) body) := hinst0
    _ = openBVar 0 (quoteTmWith ν k ρ a)
          (closeFVar 0 (ν k)
            (quoteTmWith ν (k + 1) (envCons (ν k) ρ) body)) := by
          symm
          simpa using quoteTmWith_open_close_as_applySubst ν k ρ a body

theorem inst0ApplyBridge_to_openBridge
    {ν : Nat → String} (hinst0 : Inst0ApplyBridge ν) :
    Inst0OpenBridge ν := by
  intro n k ρ a body
  exact quoteTmWith_inst0_open ν k ρ a body (hinst0 k ρ a body)

theorem inst0ApplyBridgeCompat_to_openBridgeCompat
    {ν : Nat → String} (hinst0 : Inst0ApplyBridgeCompat ν) :
    Inst0OpenBridgeCompat ν := by
  intro n k ρ a body hcompat
  exact quoteTmWith_inst0_open ν k ρ a body (hinst0 k ρ a body hcompat)

/-- Canonical `inst0` bridge at the quoted-pattern layer:
kernel substitution commutes with contextual LN quotation via singleton `applySubst`. -/
theorem quoteTmWith_inst0
    (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n)
    (a : PureTm n) (body : PureTm (n + 1))
    (hinst0 :
      quoteTmWith ν k ρ (inst0 a body) =
        applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν k ρ a))
          (quoteTmWith ν (k + 1) (envCons (ν k) ρ) body)) :
    quoteTmWith ν k ρ (inst0 a body) =
      applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν k ρ a))
        (quoteTmWith ν (k + 1) (envCons (ν k) ρ) body) := by
  exact hinst0

/-- Explicit-compat specialization requested by bridge clients.
Carries an explicit `inst0` bridge hypothesis until the unconditional theorem is proved. -/
theorem quoteTmWith_defaultBinderName_inst0_open
    (k : Nat) (ρ : QuoteEnv n) (hcompat : QuoteCompat defaultBinderName k ρ)
    (a : PureTm n) (body : PureTm (n + 1))
    (hinst0 :
      quoteTmWith defaultBinderName k ρ (inst0 a body) =
        applySubst (SubstEnv.extend SubstEnv.empty (defaultBinderName k)
          (quoteTmWith defaultBinderName k ρ a))
          (quoteTmWith defaultBinderName (k + 1)
            (envCons (defaultBinderName k) ρ) body)) :
    quoteTmWith defaultBinderName k ρ (inst0 a body) =
      openBVar 0 (quoteTmWith defaultBinderName k ρ a)
        (closeFVar 0 (defaultBinderName k)
          (quoteTmWith defaultBinderName (k + 1)
            (envCons (defaultBinderName k) ρ) body)) := by
  have _ := hcompat
  simpa using quoteTmWith_inst0_open defaultBinderName k ρ a body hinst0

theorem quoteTmWith_defaultBinderName_inst0_open_assuming_inst0Compat
    (hinst0 : Inst0ApplyBridgeCompat defaultBinderName)
    (k : Nat) (ρ : QuoteEnv n) (hcompat : QuoteCompat defaultBinderName k ρ)
    (a : PureTm n) (body : PureTm (n + 1)) :
    quoteTmWith defaultBinderName k ρ (inst0 a body) =
      openBVar 0 (quoteTmWith defaultBinderName k ρ a)
        (closeFVar 0 (defaultBinderName k)
          (quoteTmWith defaultBinderName (k + 1)
            (envCons (defaultBinderName k) ρ) body)) := by
  exact quoteTmWith_inst0_open defaultBinderName k ρ a body
    (hinst0 k ρ a body hcompat)

@[simp] theorem quoteTmWith_inst0_var_zero
    (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n) (a : PureTm n) :
    quoteTmWith ν k ρ (inst0 a (.var 0)) =
      applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν k ρ a))
        (quoteTmWith ν (k + 1) (envCons (ν k) ρ) (.var 0)) := by
  simp [inst0, quoteTmWith, envCons, applySubst, SubstEnv.find_extend_empty_eq]

@[simp] theorem quoteTmWith_inst0_var_succ
    (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n) (hcompat : QuoteCompat ν k ρ)
    (a : PureTm n) (i : Fin n) :
    quoteTmWith ν k ρ (inst0 a (.var i.succ)) =
      applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν k ρ a))
        (quoteTmWith ν (k + 1) (envCons (ν k) ρ) (.var i.succ)) := by
  have hne : ρ i ≠ ν k := hcompat.2 i k (by omega)
  have hne' : ν k ≠ ρ i := fun h => hne h.symm
  simp [inst0, quoteTmWith, envCons, applySubst, SubstEnv.find_extend_empty_ne hne']

/--
Counterexample: scoped `inst0` and ambient `openBVar 0` do not agree under quoting.
This exposes the non-shifting behavior of `openBVar` in the ambient Pattern layer.
-/
theorem quoteRaw_inst0_ne_openBVar_witness :
    quoteRaw (inst0 (.u0 : PureTm 1) (.var (Fin.succ (0 : Fin 1)) : PureTm 2))
      ≠ openBVar 0 (quoteRaw (.u0 : PureTm 1))
          (quoteRaw (.var (Fin.succ (0 : Fin 1)) : PureTm 2)) := by
  have hleft :
      quoteRaw (inst0 (.u0 : PureTm 1) (.var (Fin.succ (0 : Fin 1)) : PureTm 2))
        = Pattern.bvar 0 := by
    rfl
  have hright :
      openBVar 0 (quoteRaw (.u0 : PureTm 1))
        (quoteRaw (.var (Fin.succ (0 : Fin 1)) : PureTm 2))
        = Pattern.bvar 1 := by
    simp [openBVar, quoteRaw]
  rw [hleft, hright]
  intro h
  cases h

end Mettapedia.Languages.MeTTa.PureKernel.PatternBridge
