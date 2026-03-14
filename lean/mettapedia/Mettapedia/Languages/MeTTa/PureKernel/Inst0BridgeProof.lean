import Mettapedia.Languages.MeTTa.PureKernel.PatternBridge
import Mettapedia.Languages.MeTTa.PureKernel.Substitution
import Mettapedia.OSLF.MeTTaIL.Substitution

/-!
# Inst0 Bridge Proof Core

This module contains the internal proof core for the theoremic default-binder
`inst0` bridge.

It is not the user-facing API surface. The durable public theorems live in
`PatternBridge` and `Inst0BridgeDerived`. This file keeps the ambient/distinct
proof family and its support lemmas in one place so downstream modules can rely
on a stable theoremic interface without threading bridge assumptions.
-/

namespace Mettapedia.Languages.MeTTa.PureKernel.PatternBridge.Inst0BridgeProof

open Mettapedia.Languages.MeTTa.PureKernel.PatternBridge
open Mettapedia.Languages.MeTTa.PureKernel.Renaming
open Mettapedia.Languages.MeTTa.PureKernel.Syntax
open Mettapedia.Languages.MeTTa.PureKernel.Substitution
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution

def liftSubN : (i : Nat) -> Sub n m -> Sub (n + i) (m + i)
  | 0, σ => σ
  | i + 1, σ => liftSub (liftSubN i σ)

@[simp] theorem liftSubN_zero (σ : Sub n m) :
    liftSubN 0 σ = σ := rfl

@[simp] theorem liftSubN_succ (i : Nat) (σ : Sub n m) :
    liftSubN (i + 1) σ = liftSub (liftSubN i σ) := rfl

def buildEnv (ν : Nat → String) (k : Nat) : (i : Nat) -> QuoteEnv n -> QuoteEnv (n + i)
  | 0, ρ => ρ
  | i + 1, ρ => envCons (ν (k + i)) (buildEnv ν k i ρ)

@[simp] theorem buildEnv_zero (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n) :
    buildEnv ν k 0 ρ = ρ := rfl

@[simp] theorem buildEnv_succ (ν : Nat → String) (k i : Nat) (ρ : QuoteEnv n) :
    buildEnv ν k (i + 1) ρ = envCons (ν (k + i)) (buildEnv ν k i ρ) := rfl

def closeRange (ν : Nat → String) (k : Nat) : Nat -> Pattern -> Pattern
  | 0, p => p
  | i + 1, p => closeRange ν k i (closeFVar 0 (ν (k + i)) p)

@[simp] theorem closeRange_zero (ν : Nat → String) (k : Nat) (p : Pattern) :
    closeRange ν k 0 p = p := rfl

@[simp] theorem closeRange_succ (ν : Nat → String) (k i : Nat) (p : Pattern) :
    closeRange ν k (i + 1) p = closeRange ν k i (closeFVar 0 (ν (k + i)) p) := rfl

def closeRangeAt (d : Nat) (ν : Nat → String) (k : Nat) : Nat -> Pattern -> Pattern
  | 0, p => p
  | i + 1, p => closeRangeAt d ν k i (closeFVar d (ν (k + i)) p)

@[simp] theorem closeRangeAt_zero (d : Nat) (ν : Nat → String) (k : Nat) (p : Pattern) :
    closeRangeAt d ν k 0 p = p := rfl

@[simp] theorem closeRangeAt_succ
    (d : Nat) (ν : Nat → String) (k i : Nat) (p : Pattern) :
    closeRangeAt d ν k (i + 1) p = closeRangeAt d ν k i (closeFVar d (ν (k + i)) p) := rfl

/-- Close `e` ambient binder names `ν k, ..., ν (k+e-1)` so the newest closes to
`bvar d` and older ones shift outwards. -/
def closeAmbient (d : Nat) (ν : Nat → String) (k : Nat) : Nat -> Pattern -> Pattern
  | 0, p => p
  | i + 1, p => closeAmbient (d + 1) ν k i (closeFVar d (ν (k + i)) p)

@[simp] theorem closeAmbient_zero
    (d : Nat) (ν : Nat → String) (k : Nat) (p : Pattern) :
    closeAmbient d ν k 0 p = p := rfl

@[simp] theorem closeAmbient_succ
    (d : Nat) (ν : Nat → String) (k i : Nat) (p : Pattern) :
    closeAmbient d ν k (i + 1) p = closeAmbient (d + 1) ν k i (closeFVar d (ν (k + i)) p) := rfl

@[simp] theorem closeAmbient_one
    (d : Nat) (ν : Nat → String) (k : Nat) (p : Pattern) :
    closeAmbient d ν k 1 p = closeFVar d (ν k) p := by
  simp [closeAmbient]

@[simp] theorem closeAmbient_bvar
    (d : Nat) (ν : Nat → String) (k m j : Nat) :
    closeAmbient d ν k m (.bvar j) = .bvar j := by
  induction m generalizing d with
  | zero =>
      rfl
  | succ m ih =>
      simp [closeAmbient, ih, closeFVar]

theorem closeAmbient_mkLam
    (d : Nat) (ν : Nat → String) (k e : Nat) (body : Pattern) :
    closeAmbient d ν k e (Mettapedia.Languages.MeTTa.Pure.Core.mkLam body)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkLam
      (closeAmbient (d + 1) ν k e body) := by
  induction e generalizing d k body with
  | zero =>
      simp [closeAmbient, Mettapedia.Languages.MeTTa.Pure.Core.mkLam]
  | succ e ih =>
      simpa [closeAmbient, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkLam, Nat.add_assoc] using
        ih (d := d + 1) (k := k) (body := closeFVar (d + 1) (ν (k + e)) body)

theorem closeAmbient_mkPi
    (d : Nat) (ν : Nat → String) (k e : Nat) (A B : Pattern) :
    closeAmbient d ν k e (Mettapedia.Languages.MeTTa.Pure.Core.mkPi A B)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkPi
      (closeAmbient d ν k e A)
      (closeAmbient (d + 1) ν k e B) := by
  induction e generalizing d k A B with
  | zero =>
      simp [closeAmbient, Mettapedia.Languages.MeTTa.Pure.Core.mkPi]
  | succ e ih =>
      simpa [closeAmbient, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkPi, Nat.add_assoc] using
        ih (d := d + 1) (k := k)
          (A := closeFVar d (ν (k + e)) A)
          (B := closeFVar (d + 1) (ν (k + e)) B)

theorem closeAmbient_mkSigma
    (d : Nat) (ν : Nat → String) (k e : Nat) (A B : Pattern) :
    closeAmbient d ν k e (Mettapedia.Languages.MeTTa.Pure.Core.mkSigma A B)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkSigma
      (closeAmbient d ν k e A)
      (closeAmbient (d + 1) ν k e B) := by
  induction e generalizing d k A B with
  | zero =>
      simp [closeAmbient, Mettapedia.Languages.MeTTa.Pure.Core.mkSigma]
  | succ e ih =>
      simpa [closeAmbient, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkSigma, Nat.add_assoc] using
        ih (d := d + 1) (k := k)
          (A := closeFVar d (ν (k + e)) A)
          (B := closeFVar (d + 1) (ν (k + e)) B)

theorem closeAmbient_push_next
    (d : Nat) (ν : Nat → String) (k e : Nat) (p : Pattern) :
    closeAmbient (d + 1) ν k e (closeFVar d (ν (k + e)) p)
      =
    closeAmbient d ν k (e + 1) p := by
  simp [closeAmbient]

theorem closeAmbient_split
    (d : Nat) (ν : Nat → String) (k m e : Nat) (p : Pattern) :
    closeAmbient d ν k (m + e) p =
      closeAmbient (d + e) ν k m
        (closeAmbient d ν (k + m) e p) := by
  induction e generalizing d k p with
  | zero =>
      simp
  | succ e ih =>
      calc
        closeAmbient d ν k (m + (e + 1)) p
            = closeAmbient d ν k ((m + e) + 1) p := by
                simp [Nat.add_assoc]
        _ = closeAmbient (d + 1) ν k (m + e)
              (closeFVar d (ν (k + (m + e))) p) := by
                simp [closeAmbient]
        _ = closeAmbient ((d + 1) + e) ν k m
              (closeAmbient (d + 1) ν (k + m) e
                (closeFVar d (ν (k + (m + e))) p)) := by
                rw [ih (d := d + 1) (k := k)
                  (p := closeFVar d (ν (k + (m + e))) p)]
        _ = closeAmbient (d + (e + 1)) ν k m
              (closeAmbient d ν (k + m) (e + 1) p) := by
                simp [closeAmbient, Nat.add_left_comm, Nat.add_comm]

theorem closeRange_eq_closeRangeAt_zero
    (ν : Nat → String) (k m : Nat) (p : Pattern) :
    closeRange ν k m p = closeRangeAt 0 ν k m p := by
  induction m generalizing p with
  | zero =>
      rfl
  | succ m ih =>
      simp [closeRange, closeRangeAt, ih]

def renameWkN : (i : Nat) -> PureTm n -> PureTm (n + i)
  | 0, t => t
  | i + 1, t => rename wk (renameWkN i t)

@[simp] theorem renameWkN_zero (t : PureTm n) :
    renameWkN 0 t = t := rfl

@[simp] theorem renameWkN_succ (i : Nat) (t : PureTm n) :
    renameWkN (i + 1) t = rename wk (renameWkN i t) := rfl

def castPureTm {n m : Nat} (h : n = m) (t : PureTm n) : PureTm m := by
  subst h
  exact t

@[simp] theorem castPureTm_rfl (t : PureTm n) :
    castPureTm rfl t = t := rfl

def castAmbientBody
    {n m e : Nat}
    (b : PureTm (((n + 1) + (m + e)) + 1)) :
    PureTm ((n + 1) + (m + (e + 1))) :=
  castPureTm (by omega) b

def wkN : (i : Nat) -> Ren n (n + i)
  | 0 => idRen
  | i + 1 => fun x => wk (wkN i x)

@[simp] theorem wkN_zero :
    wkN (n := n) 0 = idRen := rfl

@[simp] theorem wkN_succ (i : Nat) :
    wkN (n := n) (i + 1) = fun x => wk (wkN i x) := rfl

@[simp] theorem wkN_val (m : Nat) (i : Fin n) :
    (wkN (n := n) m i).1 = m + i.1 := by
  induction m generalizing n with
  | zero =>
      simp [wkN, idRen]
  | succ m ih =>
      simp [wk, wkN, ih, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

def prefixIdx (tail : Nat) {m : Nat} (i : Fin m) : Fin (tail + m) :=
  ⟨i.1, by omega⟩

@[simp] theorem prefixIdx_val (tail : Nat) {m : Nat} (i : Fin m) :
    (prefixIdx tail i).1 = i.1 := rfl

@[simp] theorem renameWkN_eq_rename_wkN (i : Nat) (t : PureTm n) :
    renameWkN i t = rename (wkN (n := n) i) t := by
  induction i generalizing n with
  | zero =>
      simp [renameWkN, wkN]
  | succ i ih =>
      simp [renameWkN, wkN, ih, rename_comp]

@[simp] theorem buildEnv_wkN_apply
    (ν : Nat → String) (k m : Nat) (ρ : QuoteEnv n) (i : Fin n) :
    buildEnv ν k m ρ (wkN (n := n) m i) = ρ i := by
  induction m generalizing n k ρ with
  | zero =>
      simp [buildEnv, wkN, idRen]
  | succ m ih =>
      simpa [buildEnv, wkN, envCons] using ih (k := k) (ρ := ρ) i

theorem quoteTmWith_renameWkN_buildEnv
    (ν : Nat → String) (k m : Nat) (ρ : QuoteEnv n) (t : PureTm n) :
    quoteTmWith ν (k + m) (buildEnv ν k m ρ) (renameWkN m t) =
      quoteTmWith ν (k + m) ρ t := by
  rw [renameWkN_eq_rename_wkN]
  calc
    quoteTmWith ν (k + m) (buildEnv ν k m ρ) (rename (wkN (n := n) m) t)
        =
      quoteTmWith ν (k + m)
        (fun i => buildEnv ν k m ρ (wkN (n := n) m i)) t := by
          simpa using
            (quoteTmWith_rename ν (k := k + m)
              (ρdst := buildEnv ν k m ρ) (ρ := wkN (n := n) m) (t := t))
    _ = quoteTmWith ν (k + m) ρ t := by
          congr
          funext i
          exact buildEnv_wkN_apply ν k m ρ i

theorem quoteTmWith_renameWkN_buildEnv_any
    (ν : Nat → String) (l k m : Nat) (ρ : QuoteEnv n) (t : PureTm n) :
    quoteTmWith ν l (buildEnv ν k m ρ) (renameWkN m t) =
      quoteTmWith ν l ρ t := by
  rw [renameWkN_eq_rename_wkN]
  calc
    quoteTmWith ν l (buildEnv ν k m ρ) (rename (wkN (n := n) m) t)
        =
      quoteTmWith ν l
        (fun i => buildEnv ν k m ρ (wkN (n := n) m i)) t := by
          simpa using
            (quoteTmWith_rename ν (k := l)
              (ρdst := buildEnv ν k m ρ) (ρ := wkN (n := n) m) (t := t))
    _ = quoteTmWith ν l ρ t := by
          congr
          funext i
          exact buildEnv_wkN_apply ν k m ρ i

theorem quoteCompat_mono
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ) {j : Nat} (hkj : k ≤ j) :
    QuoteCompat ν j ρ := by
  refine ⟨hcompat.1, ?_⟩
  intro i j' hj'
  exact hcompat.2 i j' (le_trans hkj hj')

theorem buildEnv_compat
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ) :
    ∀ m : Nat, QuoteCompat ν (k + m) (buildEnv ν k m ρ) := by
  intro m
  induction m with
  | zero =>
      simpa using hcompat
  | succ m ih =>
      simpa [buildEnv, Nat.add_assoc] using
        (QuoteCompat.envCons hcompat.1 ih)

theorem isFresh_quoteTmWith_of_compat
    {ν : Nat → String} {j : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν j ρ) (l : Nat) (t : PureTm n) :
    isFresh (ν j) (quoteTmWith ν l ρ t) = true := by
  unfold isFresh
  rw [Bool.not_eq_true']
  apply Bool.eq_false_iff.mpr
  intro hcontains
  have hz : ν j ∈ freeVars (quoteTmWith ν l ρ t) := List.contains_iff_mem.mp hcontains
  rcases freeVars_quoteTmWith_mem_env ν l ρ t hz with ⟨i, hi⟩
  exact (hcompat.2 i j (by omega)) hi

theorem closeRange_quoteTmWith_id
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ) :
    ∀ (m l : Nat) (t : PureTm n),
      closeRange ν k m (quoteTmWith ν l ρ t) = quoteTmWith ν l ρ t := by
  intro m
  induction m with
  | zero =>
      intro l t
      simp [closeRange]
  | succ m ih =>
      intro l t
      have hcompat' : QuoteCompat ν (k + m) ρ :=
        quoteCompat_mono hcompat (j := k + m) (by omega)
      have hfresh :
          isFresh (ν (k + m)) (quoteTmWith ν l ρ t) = true :=
        isFresh_quoteTmWith_of_compat hcompat' l t
      calc
        closeRange ν k (m + 1) (quoteTmWith ν l ρ t)
            = closeRange ν k m
                (closeFVar 0 (ν (k + m)) (quoteTmWith ν l ρ t)) := by
                  simp [closeRange]
        _ = closeRange ν k m (quoteTmWith ν l ρ t) := by
              simp [closeFVar_fresh_id 0 (ν (k + m)) (quoteTmWith ν l ρ t) hfresh]
        _ = quoteTmWith ν l ρ t := ih l t

theorem closeRangeAt_quoteTmWith_id
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ) (d : Nat) :
    ∀ (m l : Nat) (t : PureTm n),
      closeRangeAt d ν k m (quoteTmWith ν l ρ t) = quoteTmWith ν l ρ t := by
  intro m
  induction m with
  | zero =>
      intro l t
      simp [closeRangeAt]
  | succ m ih =>
      intro l t
      have hcompat' : QuoteCompat ν (k + m) ρ :=
        quoteCompat_mono hcompat (j := k + m) (by omega)
      have hfresh :
          isFresh (ν (k + m)) (quoteTmWith ν l ρ t) = true :=
        isFresh_quoteTmWith_of_compat hcompat' l t
      calc
        closeRangeAt d ν k (m + 1) (quoteTmWith ν l ρ t)
            = closeRangeAt d ν k m
                (closeFVar d (ν (k + m)) (quoteTmWith ν l ρ t)) := by
                  simp [closeRangeAt]
        _ = closeRangeAt d ν k m (quoteTmWith ν l ρ t) := by
              simp [closeFVar_fresh_id d (ν (k + m)) (quoteTmWith ν l ρ t) hfresh]
        _ = quoteTmWith ν l ρ t := ih l t

theorem closeAmbient_quoteTmWith_id
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ) (d : Nat) :
    ∀ (m l : Nat) (t : PureTm n),
      closeAmbient d ν k m (quoteTmWith ν l ρ t) = quoteTmWith ν l ρ t := by
  intro m
  induction m generalizing d with
  | zero =>
      intro l t
      simp [closeAmbient]
  | succ m ih =>
      intro l t
      have hcompat' : QuoteCompat ν (k + m) ρ :=
        quoteCompat_mono hcompat (j := k + m) (by omega)
      have hfresh :
          isFresh (ν (k + m)) (quoteTmWith ν l ρ t) = true :=
        isFresh_quoteTmWith_of_compat hcompat' l t
      calc
        closeAmbient d ν k (m + 1) (quoteTmWith ν l ρ t)
            = closeAmbient (d + 1) ν k m
                (closeFVar d (ν (k + m)) (quoteTmWith ν l ρ t)) := by
                  simp [closeAmbient]
        _ = closeAmbient (d + 1) ν k m (quoteTmWith ν l ρ t) := by
              simp [closeFVar_fresh_id d (ν (k + m)) (quoteTmWith ν l ρ t) hfresh]
        _ = quoteTmWith ν l ρ t := ih (d := d + 1) l t

/-- Staging-only multi-open used to recover plain depth-independence. -/
def multiOpenAtStaging (d : Nat) {n : Nat} (ρ : QuoteEnv n) : Pattern → Pattern
  | .bvar j =>
      if h : d ≤ j ∧ j < d + n then
        .fvar (ρ ⟨j - d, by omega⟩)
      else
        .bvar j
  | .fvar x => .fvar x
  | .apply c args => .apply c (args.map (multiOpenAtStaging d ρ))
  | .lambda body => .lambda (multiOpenAtStaging (d + 1) ρ body)
  | .multiLambda m body => .multiLambda m (multiOpenAtStaging (d + m) ρ body)
  | .subst body repl => .subst (multiOpenAtStaging (d + 1) ρ body) (multiOpenAtStaging d ρ repl)
  | .collection ct elems rest =>
      .collection ct (elems.map (multiOpenAtStaging d ρ)) rest
termination_by p => sizeOf p

theorem freeVars_quoteRaw_staging {n : Nat} (t : PureTm n) : freeVars (quoteRaw t) = [] := by
  induction t with
  | var i => simp [quoteRaw, freeVars]
  | const c =>
      simp [quoteRaw, quoteConst, freeVars]
  | u0 => simp [quoteRaw, Mettapedia.Languages.MeTTa.Pure.Core.u0, freeVars]
  | u1 => simp [quoteRaw, Mettapedia.Languages.MeTTa.Pure.Core.u1, freeVars]
  | pi A B ihA ihB =>
      simp [quoteRaw, Mettapedia.Languages.MeTTa.Pure.Core.mkPi, freeVars, List.flatMap, ihA, ihB]
  | sigma A B ihA ihB =>
      simp [quoteRaw, Mettapedia.Languages.MeTTa.Pure.Core.mkSigma, freeVars, List.flatMap, ihA, ihB]
  | id A a b ihA iha ihb =>
      simp [quoteRaw, Mettapedia.Languages.MeTTa.Pure.Core.mkId, freeVars, List.flatMap, ihA, iha, ihb]
  | lam b ih =>
      simp [quoteRaw, Mettapedia.Languages.MeTTa.Pure.Core.mkLam, freeVars, List.flatMap, ih]
  | app f a ihf iha =>
      simp [quoteRaw, Mettapedia.Languages.MeTTa.Pure.Core.mkApp, freeVars, List.flatMap, ihf, iha]
  | pair a b iha ihb =>
      simp [quoteRaw, Mettapedia.Languages.MeTTa.Pure.Core.mkPair, freeVars, List.flatMap, iha, ihb]
  | fst p ih =>
      simp [quoteRaw, Mettapedia.Languages.MeTTa.Pure.Core.mkFst, freeVars, List.flatMap, ih]
  | snd p ih =>
      simp [quoteRaw, Mettapedia.Languages.MeTTa.Pure.Core.mkSnd, freeVars, List.flatMap, ih]
  | refl a ih =>
      simp [quoteRaw, Mettapedia.Languages.MeTTa.Pure.Core.mkRefl, freeVars, List.flatMap, ih]

theorem closeFVar_multiOpenAt_envCons_staging
    {n : Nat} (d : Nat) (x : String) (ρ : QuoteEnv n) (p : Pattern)
    (hfresh : freeVars p = []) (hρ : ∀ i : Fin n, ρ i ≠ x) :
    closeFVar d x (multiOpenAtStaging d (envCons x ρ) p) = multiOpenAtStaging (d + 1) ρ p := by
  induction p using Pattern.inductionOn generalizing d with
  | hbvar j =>
      simp only [multiOpenAtStaging]
      rcases Nat.lt_or_ge j d with hjd | hjd
      · rw [dif_neg (by omega), dif_neg (by omega)]
        simp [closeFVar]
      · rcases Nat.eq_or_lt_of_le hjd with rfl | hjd
        · rw [dif_pos (by omega : d ≤ d ∧ d < d + (n + 1)),
            dif_neg (by omega : ¬(d + 1 ≤ d ∧ d < d + 1 + n))]
          have hfin0 : (⟨d - d, by omega⟩ : Fin (n + 1)) = (0 : Fin (n + 1)) := by
            apply Fin.ext
            simp
          rw [hfin0]
          simp [envCons, closeFVar]
        · rcases Nat.lt_or_ge j (d + (n + 1)) with hjn | hjn
          · rw [dif_pos (by omega), dif_pos (by omega)]
            have hfin_succ :
                (⟨j - d, by omega⟩ : Fin (n + 1)) =
                  Fin.succ ⟨j - d - 1, by omega⟩ := by
              ext
              simp
              omega
            have hρneq : ρ ⟨j - d - 1, by omega⟩ ≠ x := hρ ⟨j - d - 1, by omega⟩
            have hidx :
                (⟨j - d - 1, by omega⟩ : Fin n) =
                  ⟨j - (d + 1), by omega⟩ := by
              apply Fin.ext
              have hnat : j - d - 1 = j - (d + 1) := by omega
              simpa using hnat
            rw [hfin_succ]
            simpa [envCons, closeFVar, hρneq, hidx]
          · rw [dif_neg (by omega), dif_neg (by omega)]
            simp [closeFVar]
  | hfvar y =>
      simp [freeVars] at hfresh
  | happly c args ih =>
      simp only [multiOpenAtStaging, closeFVar, List.map_map]
      congr 1
      have hargs : ∀ a ∈ args, freeVars a = [] :=
        List.flatMap_eq_nil_iff.mp (show args.flatMap freeVars = [] by simpa [freeVars] using hfresh)
      exact List.map_eq_map_iff.mpr fun a ha => ih a ha d (hargs a ha)
  | hlambda body ih =>
      simp only [multiOpenAtStaging, closeFVar]
      congr 1
      exact ih (d + 1) (by simpa [freeVars] using hfresh)
  | hmultiLambda m body ih =>
      simp only [multiOpenAtStaging, closeFVar]
      have heq : d + 1 + m = d + m + 1 := by omega
      rw [heq]
      congr 1
      exact ih (d + m) (by simpa [freeVars] using hfresh)
  | hsubst body repl ihb ihr =>
      simp only [multiOpenAtStaging, closeFVar]
      have hparts : freeVars body = [] ∧ freeVars repl = [] := by
        simpa [freeVars, List.append_eq_nil_iff] using hfresh
      have heq : d + 1 + 1 = (d + 1) + 1 := by omega
      congr
      · rw [heq]
        exact ihb (d + 1) hparts.1
      · exact ihr d hparts.2
  | hcollection ct elems rest ih =>
      simp only [multiOpenAtStaging, closeFVar, List.map_map]
      congr 1
      have helems : ∀ a ∈ elems, freeVars a = [] :=
        List.flatMap_eq_nil_iff.mp (show elems.flatMap freeVars = [] by simpa [freeVars] using hfresh)
      exact List.map_eq_map_iff.mpr fun a ha => ih a ha d (helems a ha)

theorem quoteTmWith_eq_multiOpenAt_quoteRaw_staging
    (ν : Nat → String) (k : Nat) {n : Nat} (ρ : QuoteEnv n) (t : PureTm n)
    (hcompat : QuoteCompat ν k ρ) :
    quoteTmWith ν k ρ t = multiOpenAtStaging 0 ρ (quoteRaw t) := by
  induction t generalizing k with
  | var i =>
      simp only [quoteTmWith, quoteRaw, multiOpenAtStaging]
      split
      · rename_i h
        simp
      · exfalso
        rename_i h
        apply h
        constructor
        · exact Nat.zero_le _
        · simp [i.isLt]
  | const c =>
      simp [quoteTmWith, quoteRaw, quoteConst, multiOpenAtStaging]
  | u0 =>
      simp [quoteTmWith, quoteRaw, Mettapedia.Languages.MeTTa.Pure.Core.u0, multiOpenAtStaging, List.map]
  | u1 =>
      simp [quoteTmWith, quoteRaw, Mettapedia.Languages.MeTTa.Pure.Core.u1, multiOpenAtStaging, List.map]
  | id A a b ihA iha ihb =>
      simp only [quoteTmWith, quoteRaw, Mettapedia.Languages.MeTTa.Pure.Core.mkId, multiOpenAtStaging, List.map]
      rw [ihA k ρ hcompat, iha k ρ hcompat, ihb k ρ hcompat]
  | app f a ihf iha =>
      simp only [quoteTmWith, quoteRaw, Mettapedia.Languages.MeTTa.Pure.Core.mkApp, multiOpenAtStaging, List.map]
      rw [ihf k ρ hcompat, iha k ρ hcompat]
  | pair a b iha ihb =>
      simp only [quoteTmWith, quoteRaw, Mettapedia.Languages.MeTTa.Pure.Core.mkPair, multiOpenAtStaging, List.map]
      rw [iha k ρ hcompat, ihb k ρ hcompat]
  | fst p ih =>
      simp only [quoteTmWith, quoteRaw, Mettapedia.Languages.MeTTa.Pure.Core.mkFst, multiOpenAtStaging, List.map]
      rw [ih k ρ hcompat]
  | snd p ih =>
      simp only [quoteTmWith, quoteRaw, Mettapedia.Languages.MeTTa.Pure.Core.mkSnd, multiOpenAtStaging, List.map]
      rw [ih k ρ hcompat]
  | refl a ih =>
      simp only [quoteTmWith, quoteRaw, Mettapedia.Languages.MeTTa.Pure.Core.mkRefl, multiOpenAtStaging, List.map]
      rw [ih k ρ hcompat]
  | lam b ih =>
      have hcompat' := QuoteCompat.envCons hcompat.1 hcompat
      simp only [quoteTmWith, quoteRaw, Mettapedia.Languages.MeTTa.Pure.Core.mkLam, multiOpenAtStaging, List.map]
      congr 1
      congr 1
      congr 1
      rw [ih (k + 1) (envCons (ν k) ρ) hcompat']
      simpa using congrArg Pattern.lambda
        (closeFVar_multiOpenAt_envCons_staging 0 (ν k) ρ (quoteRaw b)
          (freeVars_quoteRaw_staging b)
          (fun i => hcompat.2 i k (by omega)))
  | pi A B ihA ihB =>
      have hcompat' := QuoteCompat.envCons hcompat.1 hcompat
      simp only [quoteTmWith, quoteRaw, Mettapedia.Languages.MeTTa.Pure.Core.mkPi, multiOpenAtStaging, List.map]
      rw [ihA k ρ hcompat]
      congr 1
      congr 1
      congr 1
      rw [ihB (k + 1) (envCons (ν k) ρ) hcompat']
      simpa using congrArg Pattern.lambda
        (closeFVar_multiOpenAt_envCons_staging 0 (ν k) ρ (quoteRaw B)
          (freeVars_quoteRaw_staging B)
          (fun i => hcompat.2 i k (by omega)))
  | sigma A B ihA ihB =>
      have hcompat' := QuoteCompat.envCons hcompat.1 hcompat
      simp only [quoteTmWith, quoteRaw, Mettapedia.Languages.MeTTa.Pure.Core.mkSigma, multiOpenAtStaging, List.map]
      rw [ihA k ρ hcompat]
      congr 1
      congr 1
      congr 1
      rw [ihB (k + 1) (envCons (ν k) ρ) hcompat']
      simpa using congrArg Pattern.lambda
        (closeFVar_multiOpenAt_envCons_staging 0 (ν k) ρ (quoteRaw B)
          (freeVars_quoteRaw_staging B)
          (fun i => hcompat.2 i k (by omega)))

theorem quoteTmWith_depth_indep_staging
    (ν : Nat → String) {n : Nat} (k k' : Nat) (ρ : QuoteEnv n) (t : PureTm n)
    (hcompat : QuoteCompat ν k ρ) (hcompat' : QuoteCompat ν k' ρ) :
    quoteTmWith ν k ρ t = quoteTmWith ν k' ρ t := by
  rw [quoteTmWith_eq_multiOpenAt_quoteRaw_staging ν k ρ t hcompat,
      quoteTmWith_eq_multiOpenAt_quoteRaw_staging ν k' ρ t hcompat']

theorem closeRange_quoteTmWith_renameWkN_buildEnv
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ) (m : Nat) (t : PureTm n) :
    closeRange ν k m
      (quoteTmWith ν (k + m) (buildEnv ν k m ρ) (renameWkN m t))
    =
    quoteTmWith ν (k + m) ρ t := by
  rw [quoteTmWith_renameWkN_buildEnv]
  exact closeRange_quoteTmWith_id hcompat m (k + m) t

theorem closeRangeAt_quoteTmWith_renameWkN_buildEnv
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ) (d m : Nat) (t : PureTm n) :
    closeRangeAt d ν k m
      (quoteTmWith ν (k + m) (buildEnv ν k m ρ) (renameWkN m t))
    =
    quoteTmWith ν (k + m) ρ t := by
  rw [quoteTmWith_renameWkN_buildEnv]
  exact closeRangeAt_quoteTmWith_id hcompat d m (k + m) t

theorem closeRangeAt_quoteTmWith_renameWkN_buildEnv_any
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ) (d m l : Nat) (t : PureTm n) :
    closeRangeAt d ν k m
      (quoteTmWith ν l (buildEnv ν k m ρ) (renameWkN m t))
    =
    quoteTmWith ν l ρ t := by
  rw [quoteTmWith_renameWkN_buildEnv_any]
  exact closeRangeAt_quoteTmWith_id hcompat d m l t

theorem closeAmbient_quoteTmWith_renameWkN_buildEnv_any
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ) (d m l : Nat) (t : PureTm n) :
    closeAmbient d ν k m
      (quoteTmWith ν l (buildEnv ν k m ρ) (renameWkN m t))
    =
    quoteTmWith ν l ρ t := by
  rw [quoteTmWith_renameWkN_buildEnv_any]
  exact closeAmbient_quoteTmWith_id hcompat d m l t

theorem closeFVar_quoteTmWith_renameWkN_buildEnv_head
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ) (m : Nat) (t : PureTm n) :
    closeFVar 0 (ν (k + m))
      (quoteTmWith ν (k + m + 1) (buildEnv ν k (m + 1) ρ) (renameWkN (m + 1) t))
    =
    quoteTmWith ν (k + m + 1) (buildEnv ν k m ρ) (renameWkN m t) := by
  have hbuild : QuoteCompat ν (k + m) (buildEnv ν k m ρ) :=
    buildEnv_compat hcompat m
  simpa [buildEnv, renameWkN, Nat.add_assoc] using
    (closeFVar_quoteTmWith_rename_wk_envCons
      (ν := ν) (k := k + m) (ρ := buildEnv ν k m ρ)
      (hcompat := hbuild) (t := renameWkN m t))

@[simp] theorem liftSubN_wkN_apply
    (m : Nat) (σ : Sub n k) (i : Fin n) :
    liftSubN m σ (wkN (n := n) m i) = renameWkN m (σ i) := by
  induction m generalizing n k with
  | zero =>
      simp [liftSubN, wkN, renameWkN, idRen]
  | succ m ih =>
      calc
        liftSubN (m + 1) σ (wkN (n := n) (m + 1) i)
            = liftSub (liftSubN m σ) (wk (wkN (n := n) m i)) := by
                simp [liftSubN, wkN]
        _ = rename wk (liftSubN m σ (wkN (n := n) m i)) := by
              rfl
        _ = rename wk (renameWkN m (σ i)) := by
              rw [ih]
        _ = renameWkN (m + 1) (σ i) := by
              simp [renameWkN]

@[simp] theorem liftSubN_prefix_apply
    (m : Nat) (σ : Sub n k) (i : Fin m) :
    liftSubN m σ (prefixIdx n i) = .var (prefixIdx k i) := by
  induction m generalizing n k with
  | zero =>
      exact Fin.elim0 i
  | succ m ih =>
      cases i using Fin.cases with
      | zero =>
          simp [liftSubN, prefixIdx]
      | succ j =>
          simpa [liftSubN, prefixIdx, wk] using congrArg (rename wk) (ih (n := n) (k := k) σ j)

@[simp] theorem closeRange_bvar (ν : Nat → String) (k m j : Nat) :
    closeRange ν k m (.bvar j) = .bvar j := by
  induction m with
  | zero =>
      simp [closeRange]
  | succ m ih =>
      simp [closeRange, closeFVar, ih]

@[simp] theorem closeRangeAt_bvar (d : Nat) (ν : Nat → String) (k m j : Nat) :
    closeRangeAt d ν k m (.bvar j) = .bvar j := by
  induction m with
  | zero =>
      simp [closeRangeAt]
  | succ m ih =>
      simp [closeRangeAt, closeFVar, ih]

theorem closeRange_fvar_of_ne
    (ν : Nat → String) (k m : Nat) (x : String)
    (hneq : ∀ r, r < m → x ≠ ν (k + r)) :
    closeRange ν k m (.fvar x) = .fvar x := by
  induction m with
  | zero =>
      simp [closeRange]
  | succ m ih =>
      calc
        closeRange ν k (m + 1) (.fvar x)
            = closeRange ν k m (closeFVar 0 (ν (k + m)) (.fvar x)) := by
                  simp [closeRange]
        _ = closeRange ν k m (.fvar x) := by
              simp [closeFVar, hneq m (by omega)]
        _ = .fvar x := by
              apply ih
              intro r hr
              exact hneq r (by omega)

theorem closeRangeAt_fvar_of_ne
    (d : Nat) (ν : Nat → String) (k m : Nat) (x : String)
    (hneq : ∀ r, r < m → x ≠ ν (k + r)) :
    closeRangeAt d ν k m (.fvar x) = .fvar x := by
  induction m with
  | zero =>
      simp [closeRangeAt]
  | succ m ih =>
      calc
        closeRangeAt d ν k (m + 1) (.fvar x)
            = closeRangeAt d ν k m (closeFVar d (ν (k + m)) (.fvar x)) := by
                  simp [closeRangeAt]
        _ = closeRangeAt d ν k m (.fvar x) := by
              simp [closeFVar, hneq m (by omega)]
        _ = .fvar x := by
              apply ih
              intro r hr
              exact hneq r (by omega)

theorem closeAmbient_fvar_of_ne
    (d : Nat) (ν : Nat → String) (k m : Nat) (x : String)
    (hneq : ∀ r, r < m → x ≠ ν (k + r)) :
    closeAmbient d ν k m (.fvar x) = .fvar x := by
  induction m generalizing d with
  | zero =>
      simp [closeAmbient]
  | succ m ih =>
      calc
        closeAmbient d ν k (m + 1) (.fvar x)
            = closeAmbient (d + 1) ν k m (closeFVar d (ν (k + m)) (.fvar x)) := by
                  simp [closeAmbient]
        _ = closeAmbient (d + 1) ν k m (.fvar x) := by
              simp [closeFVar, hneq m (by omega)]
        _ = .fvar x := by
              apply ih
              intro r hr
              exact hneq r (by omega)

theorem buildEnv_prefix_name
    (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n) :
    ∀ {m : Nat} (i : Fin m), ∃ r, r < m ∧ buildEnv ν k m ρ (prefixIdx n i) = ν (k + r) := by
  intro m
  induction m generalizing n k ρ with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ m ih =>
      intro i
      cases i using Fin.cases with
      | zero =>
          refine ⟨m, by omega, ?_⟩
          simp [buildEnv, prefixIdx, envCons]
      | succ j =>
          rcases ih (n := n) (k := k) (ρ := ρ) j with ⟨r, hr, hEq⟩
          refine ⟨r, by omega, ?_⟩
          simpa [buildEnv, prefixIdx, envCons] using hEq

theorem buildEnv_prefix_name_exact
    (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n) :
    ∀ {m : Nat} (i : Fin m),
      buildEnv ν k m ρ (prefixIdx n i) = ν (k + (m - 1 - i.1)) := by
  intro m
  induction m generalizing n k ρ with
  | zero =>
      intro i
      exact Fin.elim0 i
  | succ m ih =>
      intro i
      cases i using Fin.cases with
      | zero =>
          simp [buildEnv, prefixIdx, envCons]
      | succ j =>
          have hEq := ih (n := n) (k := k) (ρ := ρ) j
          calc
            buildEnv ν k (m + 1) ρ (prefixIdx n (Fin.succ j))
                = buildEnv ν k m ρ (prefixIdx n j) := by
                    simp [buildEnv, prefixIdx, envCons]
            _ = ν (k + (m - 1 - j.1)) := hEq
            _ = ν (k + ((m + 1) - 1 - (Fin.succ j).1)) := by
                    have hsucc : (Fin.succ j).1 = j.1 + 1 := rfl
                    rw [hsucc]
                    congr 1
                    omega

theorem closeRange_bound_name
    {ν : Nat → String} (hinj : Function.Injective ν) (k : Nat) :
    ∀ (m r : Nat), r < m → closeRange ν k m (.fvar (ν (k + r))) = .bvar 0 := by
  intro m
  induction m with
  | zero =>
      intro r hr
      omega
  | succ m ih =>
      intro r hr
      by_cases hrm : r = m
      · subst hrm
        simp [closeRange, closeFVar, closeRange_bvar]
      · have hr' : r < m := by omega
        have hneq : ν (k + r) ≠ ν (k + m) := by
          intro hEq
          have : k + r = k + m := hinj hEq
          omega
        calc
          closeRange ν k (m + 1) (.fvar (ν (k + r)))
              = closeRange ν k m (closeFVar 0 (ν (k + m)) (.fvar (ν (k + r)))) := by
                  simp [closeRange]
          _ = closeRange ν k m (.fvar (ν (k + r))) := by
                simp [closeFVar, hneq]
          _ = .bvar 0 := ih r hr'

theorem closeRangeAt_bound_name
    {ν : Nat → String} (hinj : Function.Injective ν) (d k : Nat) :
    ∀ (m r : Nat), r < m → closeRangeAt d ν k m (.fvar (ν (k + r))) = .bvar d := by
  intro m
  induction m with
  | zero =>
      intro r hr
      omega
  | succ m ih =>
      intro r hr
      by_cases hrm : r = m
      · subst hrm
        simp [closeRangeAt, closeFVar, closeRangeAt_bvar]
      · have hr' : r < m := by omega
        have hneq : ν (k + r) ≠ ν (k + m) := by
          intro hEq
          have : k + r = k + m := hinj hEq
          omega
        calc
          closeRangeAt d ν k (m + 1) (.fvar (ν (k + r)))
              = closeRangeAt d ν k m (closeFVar d (ν (k + m)) (.fvar (ν (k + r)))) := by
                  simp [closeRangeAt]
          _ = closeRangeAt d ν k m (.fvar (ν (k + r))) := by
                simp [closeFVar, hneq]
          _ = .bvar d := ih r hr'

theorem closeAmbient_bound_name
    {ν : Nat → String} (hinj : Function.Injective ν) (d k : Nat) :
    ∀ (m r : Nat), r < m →
      closeAmbient d ν k m (.fvar (ν (k + r))) = .bvar (d + (m - 1 - r)) := by
  intro m
  induction m generalizing d k with
  | zero =>
      intro r hr
      omega
  | succ m ih =>
      intro r hr
      by_cases hrm : r = m
      · subst r
        have hb :
            closeAmbient (d + 1) ν k m (.bvar d) = .bvar d :=
          closeAmbient_bvar (d := d + 1) (ν := ν) (k := k) (m := m) (j := d)
        calc
          closeAmbient d ν k (m + 1) (.fvar (ν (k + m)))
              = closeAmbient (d + 1) ν k m (.bvar d) := by
                  simp [closeAmbient, closeFVar]
          _ = .bvar d := hb
          _ = .bvar (d + ((m + 1) - 1 - m)) := by
                congr 1
                omega
      · have hr' : r < m := by omega
        have hneq : ν (k + r) ≠ ν (k + m) := by
          intro hEq
          have : k + r = k + m := hinj hEq
          omega
        have hrec :
            closeAmbient (d + 1) ν k m (.fvar (ν (k + r))) =
              .bvar ((d + 1) + (m - 1 - r)) :=
          ih (d := d + 1) (k := k) r hr'
        have hidx :
            (d + 1) + (m - 1 - r) = d + ((m + 1) - 1 - r) := by
          omega
        calc
          closeAmbient d ν k (m + 1) (.fvar (ν (k + r)))
              = closeAmbient (d + 1) ν k m (.fvar (ν (k + r))) := by
                  simp [closeAmbient, closeFVar, hneq]
          _ = .bvar ((d + 1) + (m - 1 - r)) := hrec
          _ = .bvar (d + ((m + 1) - 1 - r)) := by
                simp [hidx]

def inst0BinderClosedTarget
    (ν : Nat → String) {n : Nat}
    (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) (t : PureTm ((n + 1) + m)) : Pattern :=
  applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν (k + m) ρ a))
    (closeRange ν (k + 1) m
      (quoteTmWith ν (k + m + 1)
        (buildEnv ν (k + 1) m (envCons (ν k) ρ)) t))

def inst0BinderClosedLhs
    (ν : Nat → String) {n : Nat}
    (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) (t : PureTm ((n + 1) + m)) : Pattern :=
  closeRange ν k m
    (quoteTmWith ν (k + m) (buildEnv ν k m ρ)
      (subst (liftSubN m (subst0 a)) t))

def inst0BinderTargetEq
    (ν : Nat → String) {n : Nat}
    (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) (t : PureTm ((n + 1) + m)) : Prop :=
  inst0BinderClosedLhs ν m k ρ a t = inst0BinderClosedTarget ν m k ρ a t

/-- Generalized closed-codomain family with `e` ambient binders beyond the
preserved prefix `m`. `e = 0` recovers the top-level term family, `e = 1`
recovers the current body family. -/
def inst0AmbientClosedLhs
    (e : Nat) (ν : Nat → String) {n : Nat}
    (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) (t : PureTm ((n + 1) + (m + e))) : Pattern :=
  closeRangeAt e ν k m
    (closeAmbient 0 ν (k + m) e
      (quoteTmWith ν (k + m + e) (buildEnv ν k (m + e) ρ)
        (subst (liftSubN (m + e) (subst0 a)) t)))

def inst0AmbientClosedTarget
    (e : Nat) (ν : Nat → String) {n : Nat}
    (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) (t : PureTm ((n + 1) + (m + e))) : Pattern :=
  applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν (k + m) ρ a))
    (closeRangeAt e ν (k + 1) m
      (closeAmbient 0 ν (k + m + 1) e
        (quoteTmWith ν (k + m + e + 1)
          (buildEnv ν (k + 1) (m + e) (envCons (ν k) ρ)) t)))

def inst0AmbientTargetEq
    (e : Nat) (ν : Nat → String) {n : Nat}
    (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) (t : PureTm ((n + 1) + (m + e))) : Prop :=
  inst0AmbientClosedLhs e ν m k ρ a t = inst0AmbientClosedTarget e ν m k ρ a t

/-- Variant of the ambient family that preserves the `m` prefix binders as distinct
de Bruijn indices rather than collapsing them all to depth `e`. -/
def inst0AmbientDistinctClosedLhs
    (e : Nat) (ν : Nat → String) {n : Nat}
    (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) (t : PureTm ((n + 1) + (m + e))) : Pattern :=
  closeAmbient e ν k m
    (closeAmbient 0 ν (k + m) e
      (quoteTmWith ν (k + m + e) (buildEnv ν k (m + e) ρ)
        (subst (liftSubN (m + e) (subst0 a)) t)))

def inst0AmbientDistinctClosedTarget
    (e : Nat) (ν : Nat → String) {n : Nat}
    (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) (t : PureTm ((n + 1) + (m + e))) : Pattern :=
  applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν (k + m) ρ a))
    (closeAmbient e ν (k + 1) m
      (closeAmbient 0 ν (k + m + 1) e
        (quoteTmWith ν (k + m + e + 1)
          (buildEnv ν (k + 1) (m + e) (envCons (ν k) ρ)) t)))

def inst0AmbientDistinctTargetEq
    (e : Nat) (ν : Nat → String) {n : Nat}
    (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) (t : PureTm ((n + 1) + (m + e))) : Prop :=
  inst0AmbientDistinctClosedLhs e ν m k ρ a t =
    inst0AmbientDistinctClosedTarget e ν m k ρ a t

def inst0BinderClosedLhsDistinct
    (ν : Nat → String) {n : Nat}
    (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) (t : PureTm ((n + 1) + m)) : Pattern :=
  closeAmbient 0 ν k m
    (quoteTmWith ν (k + m) (buildEnv ν k m ρ)
      (subst (liftSubN m (subst0 a)) t))

def inst0BinderClosedTargetDistinct
    (ν : Nat → String) {n : Nat}
    (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) (t : PureTm ((n + 1) + m)) : Pattern :=
  applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν (k + m) ρ a))
    (closeAmbient 0 ν (k + 1) m
      (quoteTmWith ν (k + m + 1)
        (buildEnv ν (k + 1) m (envCons (ν k) ρ)) t))

def inst0BinderTargetEqDistinct
    (ν : Nat → String) {n : Nat}
    (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) (t : PureTm ((n + 1) + m)) : Prop :=
  inst0BinderClosedLhsDistinct ν m k ρ a t =
    inst0BinderClosedTargetDistinct ν m k ρ a t

theorem inst0AmbientDistinctClosedLhs_zero_eq
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (t : PureTm ((n + 1) + m)) :
    inst0AmbientDistinctClosedLhs 0 ν m k ρ a t =
      inst0BinderClosedLhsDistinct ν m k ρ a t := by
  simp [inst0AmbientDistinctClosedLhs, inst0BinderClosedLhsDistinct]

theorem inst0AmbientDistinctClosedTarget_zero_eq
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (t : PureTm ((n + 1) + m)) :
    inst0AmbientDistinctClosedTarget 0 ν m k ρ a t =
      inst0BinderClosedTargetDistinct ν m k ρ a t := by
  simp [inst0AmbientDistinctClosedTarget, inst0BinderClosedTargetDistinct]

theorem inst0AmbientDistinctTargetEq_zero_iff
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (t : PureTm ((n + 1) + m)) :
    inst0AmbientDistinctTargetEq 0 ν m k ρ a t ↔
      inst0BinderTargetEqDistinct ν m k ρ a t := by
  simp [inst0AmbientDistinctTargetEq, inst0BinderTargetEqDistinct,
    inst0AmbientDistinctClosedLhs_zero_eq, inst0AmbientDistinctClosedTarget_zero_eq]

theorem inst0AmbientDistinctClosedLhs_eq_total
    (ν : Nat → String) (e m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (t : PureTm ((n + 1) + (m + e))) :
    inst0AmbientDistinctClosedLhs e ν m k ρ a t =
      inst0BinderClosedLhsDistinct ν (m + e) k ρ a t := by
  unfold inst0AmbientDistinctClosedLhs inst0BinderClosedLhsDistinct
  rw [closeAmbient_split]
  simp [Nat.add_left_comm, Nat.add_comm]

theorem inst0AmbientDistinctClosedTarget_eq_total
    (ν : Nat → String) (e m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (hcompat : QuoteCompat ν k ρ)
    (t : PureTm ((n + 1) + (m + e))) :
    inst0AmbientDistinctClosedTarget e ν m k ρ a t =
      inst0BinderClosedTargetDistinct ν (m + e) k ρ a t := by
  unfold inst0AmbientDistinctClosedTarget inst0BinderClosedTargetDistinct
  have hq :
      quoteTmWith ν (k + m) ρ a = quoteTmWith ν (k + (m + e)) ρ a := by
    apply quoteTmWith_depth_indep_staging
    · exact quoteCompat_mono hcompat (j := k + m) (by omega)
    · exact quoteCompat_mono hcompat (j := k + (m + e)) (by omega)
  rw [hq, closeAmbient_split]
  simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

theorem inst0AmbientDistinctTargetEq_total_iff
    (ν : Nat → String) (e m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (hcompat : QuoteCompat ν k ρ)
    (t : PureTm ((n + 1) + (m + e))) :
    inst0AmbientDistinctTargetEq e ν m k ρ a t ↔
      inst0BinderTargetEqDistinct ν (m + e) k ρ a t := by
  simp [inst0AmbientDistinctTargetEq, inst0BinderTargetEqDistinct,
    inst0AmbientDistinctClosedLhs_eq_total, inst0AmbientDistinctClosedTarget_eq_total,
    hcompat]

theorem inst0AmbientClosedLhs_zero_eq
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (t : PureTm ((n + 1) + m)) :
    inst0AmbientClosedLhs 0 ν m k ρ a t = inst0BinderClosedLhs ν m k ρ a t := by
  simp [inst0AmbientClosedLhs, inst0BinderClosedLhs, closeRange_eq_closeRangeAt_zero]

theorem inst0AmbientClosedTarget_zero_eq
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (t : PureTm ((n + 1) + m)) :
    inst0AmbientClosedTarget 0 ν m k ρ a t = inst0BinderClosedTarget ν m k ρ a t := by
  simp [inst0AmbientClosedTarget, inst0BinderClosedTarget, closeRange_eq_closeRangeAt_zero]

theorem inst0AmbientTargetEq_zero_iff
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (t : PureTm ((n + 1) + m)) :
    inst0AmbientTargetEq 0 ν m k ρ a t ↔ inst0BinderTargetEq ν m k ρ a t := by
  simp [inst0AmbientTargetEq, inst0BinderTargetEq, inst0AmbientClosedLhs_zero_eq,
    inst0AmbientClosedTarget_zero_eq]

theorem inst0BinderTargetEq_wkN_var
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ) (m : Nat) (a : PureTm n) (i : Fin (n + 1)) :
    inst0BinderClosedLhs ν m k ρ a (.var (wkN (n := n + 1) m i))
    =
    inst0BinderClosedTarget ν m k ρ a (.var (wkN (n := n + 1) m i)) := by
  have hL :
      inst0BinderClosedLhs ν m k ρ a (.var (wkN (n := n + 1) m i))
      =
      quoteTmWith ν (k + m) ρ (subst0 a i) := by
    calc
      inst0BinderClosedLhs ν m k ρ a (.var (wkN (n := n + 1) m i))
          =
        closeRange ν k m
          (quoteTmWith ν (k + m) (buildEnv ν k m ρ)
            (liftSubN m (subst0 a) (wkN (n := n + 1) m i))) := by
              simp [inst0BinderClosedLhs]
      _ =
        closeRange ν k m
          (quoteTmWith ν (k + m) (buildEnv ν k m ρ)
            (renameWkN m (subst0 a i))) := by
              simp [liftSubN_wkN_apply]
      _ = quoteTmWith ν (k + m) ρ (subst0 a i) := by
              exact closeRange_quoteTmWith_renameWkN_buildEnv hcompat m (subst0 a i)
  cases i using Fin.cases with
  | zero =>
      have hclose :
          closeRange ν (k + 1) m (.fvar (ν k)) = .fvar (ν k) := by
        apply closeRange_fvar_of_ne
        intro r hr hEq
        have hk : k ≠ k + 1 + r := by omega
        exact hk (hcompat.1 hEq)
      calc
        inst0BinderClosedLhs ν m k ρ a (.var (wkN (n := n + 1) m 0))
            = quoteTmWith ν (k + m) ρ a := by
                simpa using hL
        _ =
          applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν (k + m) ρ a))
            (closeRange ν (k + 1) m
              (quoteTmWith ν (k + m + 1)
                (buildEnv ν (k + 1) m (envCons (ν k) ρ))
                (.var (wkN (n := n + 1) m 0)))) := by
                  simp [quoteTmWith, buildEnv_wkN_apply, envCons]
                  rw [hclose]
                  simp [applySubst, SubstEnv.find_extend_eq]
        _ = inst0BinderClosedTarget ν m k ρ a (.var (wkN (n := n + 1) m 0)) := by
              rfl
  | succ j =>
      have hclose :
          closeRange ν (k + 1) m (.fvar (ρ j)) = .fvar (ρ j) := by
        apply closeRange_fvar_of_ne
        intro r hr
        exact hcompat.2 j (k + 1 + r) (by omega)
      have hne : ρ j ≠ ν k := hcompat.2 j k (by omega)
      calc
        inst0BinderClosedLhs ν m k ρ a (.var (wkN (n := n + 1) m j.succ))
            = quoteTmWith ν (k + m) ρ (.var j) := by
                simpa using hL
        _ =
          applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν (k + m) ρ a))
            (closeRange ν (k + 1) m
              (quoteTmWith ν (k + m + 1)
                (buildEnv ν (k + 1) m (envCons (ν k) ρ))
                (.var (wkN (n := n + 1) m j.succ)))) := by
                  simp [quoteTmWith, buildEnv_wkN_apply, envCons]
                  rw [hclose]
                  have hfind :
                      (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν (k + m) ρ a)).find (ρ j)
                        = none :=
                    SubstEnv.find_extend_ne hne.symm
                  rw [applySubst, hfind]
        _ = inst0BinderClosedTarget ν m k ρ a (.var (wkN (n := n + 1) m j.succ)) := by
              rfl

theorem inst0BinderTargetEq_preserved_zero
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (_hcompat : QuoteCompat ν k ρ) (m : Nat) (a : PureTm n) :
    inst0BinderClosedLhs ν (m + 1) k ρ a (.var 0)
    =
    inst0BinderClosedTarget ν (m + 1) k ρ a (.var 0) := by
  calc
    inst0BinderClosedLhs ν (m + 1) k ρ a (.var 0)
        =
      closeRange ν k m (.bvar 0) := by
        simp [inst0BinderClosedLhs, closeRange, buildEnv, quoteTmWith, liftSubN, subst, closeFVar, envCons]
    _ = .bvar 0 := by
        exact closeRange_bvar ν k m 0
    _ = inst0BinderClosedTarget ν (m + 1) k ρ a (.var 0) := by
        simp [inst0BinderClosedTarget, buildEnv, quoteTmWith, closeFVar, envCons, closeRange_bvar, applySubst]

theorem inst0BinderClosedLhs_prefix_var
    {ν : Nat → String} (hinj : Function.Injective ν)
    (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) (i : Fin m) :
    inst0BinderClosedLhs ν m k ρ a (.var (prefixIdx (n + 1) i)) = .bvar 0 := by
  rcases buildEnv_prefix_name ν k ρ i with ⟨r, hr, hname⟩
  calc
    inst0BinderClosedLhs ν m k ρ a (.var (prefixIdx (n + 1) i))
        =
      closeRange ν k m (.fvar (ν (k + r))) := by
        simp [inst0BinderClosedLhs, liftSubN_prefix_apply, quoteTmWith, hname]
    _ = .bvar 0 := closeRange_bound_name hinj k m r hr

theorem inst0BinderClosedTarget_prefix_var
    {ν : Nat → String} (hinj : Function.Injective ν)
    (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) (i : Fin m) :
    inst0BinderClosedTarget ν m k ρ a (.var (prefixIdx (n + 1) i)) = .bvar 0 := by
  rcases buildEnv_prefix_name ν (k + 1) (envCons (ν k) ρ) i with ⟨r, hr, hname⟩
  calc
    inst0BinderClosedTarget ν m k ρ a (.var (prefixIdx (n + 1) i))
        =
      applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν (k + m) ρ a))
        (closeRange ν (k + 1) m (.fvar (ν (k + 1 + r)))) := by
          simp [inst0BinderClosedTarget, quoteTmWith, hname]
    _ =
      applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν (k + m) ρ a))
        (.bvar 0) := by
          rw [closeRange_bound_name hinj (k + 1) m r hr]
    _ = .bvar 0 := by
          simp [applySubst]

theorem inst0BinderTargetEq_prefix_var
    {ν : Nat → String} (hinj : Function.Injective ν)
    (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) (i : Fin m) :
    inst0BinderClosedLhs ν m k ρ a (.var (prefixIdx (n + 1) i))
    =
    inst0BinderClosedTarget ν m k ρ a (.var (prefixIdx (n + 1) i)) := by
  rw [inst0BinderClosedLhs_prefix_var hinj m k ρ a i,
    inst0BinderClosedTarget_prefix_var hinj m k ρ a i]

theorem fin_prefix_or_wkN
    (m : Nat) (i : Fin ((n + 1) + m)) :
    (∃ j : Fin m, i = prefixIdx (n + 1) j) ∨
    (∃ j : Fin (n + 1), i = wkN (n := n + 1) m j) := by
  by_cases h : i.1 < m
  · left
    refine ⟨⟨i.1, h⟩, ?_⟩
    apply Fin.ext
    simp [prefixIdx]
  · right
    have hm : m ≤ i.1 := by omega
    refine ⟨⟨i.1 - m, by omega⟩, ?_⟩
    apply Fin.ext
    simp [wkN_val, hm]

theorem inst0BinderTargetEq_var
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ) (m : Nat) (a : PureTm n) (i : Fin ((n + 1) + m)) :
    inst0BinderClosedLhs ν m k ρ a (.var i)
    =
    inst0BinderClosedTarget ν m k ρ a (.var i) := by
  rcases fin_prefix_or_wkN (n := n) m i with hprefix | hwk
  · rcases hprefix with ⟨j, rfl⟩
    exact inst0BinderTargetEq_prefix_var hcompat.1 m k ρ a j
  · rcases hwk with ⟨j, rfl⟩
    exact inst0BinderTargetEq_wkN_var hcompat m a j

theorem inst0BinderTargetEqDistinct_wkN_var
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ) (m : Nat) (a : PureTm n) (i : Fin (n + 1)) :
    inst0BinderClosedLhsDistinct ν m k ρ a (.var (wkN (n := n + 1) m i))
    =
    inst0BinderClosedTargetDistinct ν m k ρ a (.var (wkN (n := n + 1) m i)) := by
  have hL :
      inst0BinderClosedLhsDistinct ν m k ρ a (.var (wkN (n := n + 1) m i))
      =
      quoteTmWith ν (k + m) ρ (subst0 a i) := by
    calc
      inst0BinderClosedLhsDistinct ν m k ρ a (.var (wkN (n := n + 1) m i))
          =
        closeAmbient 0 ν k m
          (quoteTmWith ν (k + m) (buildEnv ν k m ρ)
            (liftSubN m (subst0 a) (wkN (n := n + 1) m i))) := by
              simp [inst0BinderClosedLhsDistinct]
      _ =
        closeAmbient 0 ν k m
          (quoteTmWith ν (k + m) (buildEnv ν k m ρ)
            (renameWkN m (subst0 a i))) := by
              simp [liftSubN_wkN_apply]
      _ = quoteTmWith ν (k + m) ρ (subst0 a i) := by
            exact closeAmbient_quoteTmWith_renameWkN_buildEnv_any hcompat 0 m (k + m) (subst0 a i)
  cases i using Fin.cases with
  | zero =>
      have hclose :
          closeAmbient 0 ν (k + 1) m (.fvar (ν k)) = .fvar (ν k) := by
        apply closeAmbient_fvar_of_ne
        intro r hr hEq
        have hk : k ≠ k + 1 + r := by omega
        exact hk (hcompat.1 hEq)
      calc
        inst0BinderClosedLhsDistinct ν m k ρ a (.var (wkN (n := n + 1) m 0))
            = quoteTmWith ν (k + m) ρ a := by
                simpa using hL
        _ =
          applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν (k + m) ρ a))
            (closeAmbient 0 ν (k + 1) m
              (quoteTmWith ν (k + m + 1)
                (buildEnv ν (k + 1) m (envCons (ν k) ρ))
                (.var (wkN (n := n + 1) m 0)))) := by
                  simp [quoteTmWith, buildEnv_wkN_apply, envCons]
                  rw [hclose]
                  simp [applySubst, SubstEnv.find_extend_eq]
        _ = inst0BinderClosedTargetDistinct ν m k ρ a (.var (wkN (n := n + 1) m 0)) := by
              rfl
  | succ j =>
      have hclose :
          closeAmbient 0 ν (k + 1) m (.fvar (ρ j)) = .fvar (ρ j) := by
        apply closeAmbient_fvar_of_ne
        intro r hr
        exact hcompat.2 j (k + 1 + r) (by omega)
      have hne : ρ j ≠ ν k := hcompat.2 j k (by omega)
      calc
        inst0BinderClosedLhsDistinct ν m k ρ a (.var (wkN (n := n + 1) m j.succ))
            = .fvar (ρ j) := by
                simpa [quoteTmWith] using hL
        _ =
          applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν (k + m) ρ a))
            (closeAmbient 0 ν (k + 1) m
              (quoteTmWith ν (k + m + 1)
                (buildEnv ν (k + 1) m (envCons (ν k) ρ))
                (.var (wkN (n := n + 1) m j.succ)))) := by
                  simp [quoteTmWith, buildEnv_wkN_apply, envCons]
                  rw [hclose]
                  rw [applySubst, SubstEnv.find_extend_ne hne.symm]
                  simp [SubstEnv.find, SubstEnv.empty]
        _ = inst0BinderClosedTargetDistinct ν m k ρ a (.var (wkN (n := n + 1) m j.succ)) := by
              rfl

theorem inst0BinderClosedLhsDistinct_prefix_var
    {ν : Nat → String} (hinj : Function.Injective ν)
    (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) (i : Fin m) :
    inst0BinderClosedLhsDistinct ν m k ρ a (.var (prefixIdx (n + 1) i)) = .bvar i.1 := by
  have hname :
      buildEnv ν k m ρ (prefixIdx n i) = ν (k + (m - 1 - i.1)) :=
    buildEnv_prefix_name_exact ν k ρ i
  have hr : m - 1 - i.1 < m := by omega
  calc
    inst0BinderClosedLhsDistinct ν m k ρ a (.var (prefixIdx (n + 1) i))
        =
      closeAmbient 0 ν k m (.fvar (ν (k + (m - 1 - i.1)))) := by
        simp [inst0BinderClosedLhsDistinct, liftSubN_prefix_apply, quoteTmWith, hname]
    _ = .bvar (0 + (m - 1 - (m - 1 - i.1))) := closeAmbient_bound_name hinj 0 k m (m - 1 - i.1) hr
    _ = .bvar i.1 := by
          congr 1
          omega

theorem inst0BinderClosedTargetDistinct_prefix_var
    {ν : Nat → String} (hinj : Function.Injective ν)
    (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) (i : Fin m) :
    inst0BinderClosedTargetDistinct ν m k ρ a (.var (prefixIdx (n + 1) i)) = .bvar i.1 := by
  have hname :
      buildEnv ν (k + 1) m (envCons (ν k) ρ) (prefixIdx (n + 1) i)
        = ν ((k + 1) + (m - 1 - i.1)) :=
    buildEnv_prefix_name_exact ν (k + 1) (envCons (ν k) ρ) i
  have hr : m - 1 - i.1 < m := by omega
  calc
    inst0BinderClosedTargetDistinct ν m k ρ a (.var (prefixIdx (n + 1) i))
        =
      applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν (k + m) ρ a))
        (closeAmbient 0 ν (k + 1) m (.fvar (ν ((k + 1) + (m - 1 - i.1))))) := by
          simp [inst0BinderClosedTargetDistinct, quoteTmWith, hname]
    _ =
      applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν (k + m) ρ a))
        (.bvar (0 + (m - 1 - (m - 1 - i.1)))) := by
          rw [closeAmbient_bound_name hinj 0 (k + 1) m (m - 1 - i.1) hr]
    _ = .bvar i.1 := by
          have hidx : 0 + (m - 1 - (m - 1 - i.1)) = i.1 := by omega
          simp [applySubst, hidx]

theorem inst0BinderTargetEqDistinct_prefix_var
    {ν : Nat → String} (hinj : Function.Injective ν)
    (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) (i : Fin m) :
    inst0BinderClosedLhsDistinct ν m k ρ a (.var (prefixIdx (n + 1) i))
    =
    inst0BinderClosedTargetDistinct ν m k ρ a (.var (prefixIdx (n + 1) i)) := by
  rw [inst0BinderClosedLhsDistinct_prefix_var hinj m k ρ a i,
    inst0BinderClosedTargetDistinct_prefix_var hinj m k ρ a i]

theorem inst0BinderTargetEqDistinct_var
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ) (m : Nat) (a : PureTm n) (i : Fin ((n + 1) + m)) :
    inst0BinderClosedLhsDistinct ν m k ρ a (.var i)
    =
    inst0BinderClosedTargetDistinct ν m k ρ a (.var i) := by
  rcases fin_prefix_or_wkN (n := n) m i with hprefix | hwk
  · rcases hprefix with ⟨j, rfl⟩
    exact inst0BinderTargetEqDistinct_prefix_var hcompat.1 m k ρ a j
  · rcases hwk with ⟨j, rfl⟩
    exact inst0BinderTargetEqDistinct_wkN_var hcompat m a j

@[simp] theorem applySubst_u0 (env : SubstEnv) :
    applySubst env Mettapedia.Languages.MeTTa.Pure.Core.u0 = Mettapedia.Languages.MeTTa.Pure.Core.u0 := by
  simp [Mettapedia.Languages.MeTTa.Pure.Core.u0, applySubst]

@[simp] theorem applySubst_u1 (env : SubstEnv) :
    applySubst env Mettapedia.Languages.MeTTa.Pure.Core.u1 = Mettapedia.Languages.MeTTa.Pure.Core.u1 := by
  simp [Mettapedia.Languages.MeTTa.Pure.Core.u1, applySubst]

@[simp] theorem applySubst_quoteConst (env : SubstEnv) (c : DeclName) :
    applySubst env (quoteConst c) = quoteConst c := by
  simp [quoteConst, applySubst]

@[simp] theorem closeRange_u0 (ν : Nat → String) (k m : Nat) :
    closeRange ν k m Mettapedia.Languages.MeTTa.Pure.Core.u0 = Mettapedia.Languages.MeTTa.Pure.Core.u0 := by
  induction m generalizing k with
  | zero =>
      simp [closeRange, Mettapedia.Languages.MeTTa.Pure.Core.u0]
  | succ m ih =>
      simpa [closeRange, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.u0] using ih (k := k)

@[simp] theorem closeRange_u1 (ν : Nat → String) (k m : Nat) :
    closeRange ν k m Mettapedia.Languages.MeTTa.Pure.Core.u1 = Mettapedia.Languages.MeTTa.Pure.Core.u1 := by
  induction m generalizing k with
  | zero =>
      simp [closeRange, Mettapedia.Languages.MeTTa.Pure.Core.u1]
  | succ m ih =>
      simpa [closeRange, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.u1] using ih (k := k)

@[simp] theorem applySubst_mkId
    (env : SubstEnv) (A a b : Pattern) :
    applySubst env (Mettapedia.Languages.MeTTa.Pure.Core.mkId A a b)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkId
      (applySubst env A) (applySubst env a) (applySubst env b) := by
  simp [Mettapedia.Languages.MeTTa.Pure.Core.mkId, applySubst]

@[simp] theorem applySubst_mkApp
    (env : SubstEnv) (f a : Pattern) :
    applySubst env (Mettapedia.Languages.MeTTa.Pure.Core.mkApp f a)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkApp (applySubst env f) (applySubst env a) := by
  simp [Mettapedia.Languages.MeTTa.Pure.Core.mkApp, applySubst]

@[simp] theorem applySubst_mkPair
    (env : SubstEnv) (a b : Pattern) :
    applySubst env (Mettapedia.Languages.MeTTa.Pure.Core.mkPair a b)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkPair (applySubst env a) (applySubst env b) := by
  simp [Mettapedia.Languages.MeTTa.Pure.Core.mkPair, applySubst]

@[simp] theorem applySubst_mkFst
    (env : SubstEnv) (p : Pattern) :
    applySubst env (Mettapedia.Languages.MeTTa.Pure.Core.mkFst p)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkFst (applySubst env p) := by
  simp [Mettapedia.Languages.MeTTa.Pure.Core.mkFst, applySubst]

@[simp] theorem applySubst_mkSnd
    (env : SubstEnv) (p : Pattern) :
    applySubst env (Mettapedia.Languages.MeTTa.Pure.Core.mkSnd p)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkSnd (applySubst env p) := by
  simp [Mettapedia.Languages.MeTTa.Pure.Core.mkSnd, applySubst]

@[simp] theorem applySubst_mkRefl
    (env : SubstEnv) (a : Pattern) :
    applySubst env (Mettapedia.Languages.MeTTa.Pure.Core.mkRefl a)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkRefl (applySubst env a) := by
  simp [Mettapedia.Languages.MeTTa.Pure.Core.mkRefl, applySubst]

@[simp] theorem applySubst_mkPi
    (env : SubstEnv) (A B : Pattern) :
    applySubst env (Mettapedia.Languages.MeTTa.Pure.Core.mkPi A B)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkPi (applySubst env A) (applySubst env B) := by
  simp [Mettapedia.Languages.MeTTa.Pure.Core.mkPi, applySubst]

@[simp] theorem applySubst_mkSigma
    (env : SubstEnv) (A B : Pattern) :
    applySubst env (Mettapedia.Languages.MeTTa.Pure.Core.mkSigma A B)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkSigma (applySubst env A) (applySubst env B) := by
  simp [Mettapedia.Languages.MeTTa.Pure.Core.mkSigma, applySubst]

@[simp] theorem applySubst_mkLam
    (env : SubstEnv) (body : Pattern) :
    applySubst env (Mettapedia.Languages.MeTTa.Pure.Core.mkLam body)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkLam (applySubst env body) := by
  simp [Mettapedia.Languages.MeTTa.Pure.Core.mkLam, applySubst]

@[simp] theorem closeRangeAt_u0
    (d : Nat) (ν : Nat → String) (k m : Nat) :
    closeRangeAt d ν k m Mettapedia.Languages.MeTTa.Pure.Core.u0 = Mettapedia.Languages.MeTTa.Pure.Core.u0 := by
  induction m generalizing k with
  | zero =>
      simp [closeRangeAt, Mettapedia.Languages.MeTTa.Pure.Core.u0]
  | succ m ih =>
      simpa [closeRangeAt, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.u0] using ih (k := k)

@[simp] theorem closeRangeAt_u1
    (d : Nat) (ν : Nat → String) (k m : Nat) :
    closeRangeAt d ν k m Mettapedia.Languages.MeTTa.Pure.Core.u1 = Mettapedia.Languages.MeTTa.Pure.Core.u1 := by
  induction m generalizing k with
  | zero =>
      simp [closeRangeAt, Mettapedia.Languages.MeTTa.Pure.Core.u1]
  | succ m ih =>
      simpa [closeRangeAt, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.u1] using ih (k := k)

@[simp] theorem closeAmbient_u0
    (d : Nat) (ν : Nat → String) (k m : Nat) :
    closeAmbient d ν k m Mettapedia.Languages.MeTTa.Pure.Core.u0 = Mettapedia.Languages.MeTTa.Pure.Core.u0 := by
  induction m generalizing d k with
  | zero =>
      simp [closeAmbient, Mettapedia.Languages.MeTTa.Pure.Core.u0]
  | succ m ih =>
      simpa [closeAmbient, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.u0] using ih (d := d + 1) (k := k)

@[simp] theorem closeAmbient_u1
    (d : Nat) (ν : Nat → String) (k m : Nat) :
    closeAmbient d ν k m Mettapedia.Languages.MeTTa.Pure.Core.u1 = Mettapedia.Languages.MeTTa.Pure.Core.u1 := by
  induction m generalizing d k with
  | zero =>
      simp [closeAmbient, Mettapedia.Languages.MeTTa.Pure.Core.u1]
  | succ m ih =>
      simpa [closeAmbient, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.u1] using ih (d := d + 1) (k := k)

@[simp] theorem closeAmbient_quoteConst
    (d : Nat) (ν : Nat → String) (k m : Nat) (c : DeclName) :
    closeAmbient d ν k m (quoteConst c) = quoteConst c := by
  induction m generalizing d k with
  | zero =>
      simp [closeAmbient, quoteConst]
  | succ m ih =>
      simpa [closeAmbient, closeFVar, quoteConst] using ih (d := d + 1) (k := k)

@[simp] theorem closeAmbient_mkId
    (d : Nat) (ν : Nat → String) (k m : Nat) (A a b : Pattern) :
    closeAmbient d ν k m (Mettapedia.Languages.MeTTa.Pure.Core.mkId A a b)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkId
      (closeAmbient d ν k m A) (closeAmbient d ν k m a) (closeAmbient d ν k m b) := by
  induction m generalizing d k A a b with
  | zero =>
      simp [closeAmbient, Mettapedia.Languages.MeTTa.Pure.Core.mkId]
  | succ m ih =>
      simpa [closeAmbient, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkId] using
        ih (d := d + 1) (k := k)
          (A := closeFVar d (ν (k + m)) A)
          (a := closeFVar d (ν (k + m)) a)
          (b := closeFVar d (ν (k + m)) b)

@[simp] theorem closeAmbient_mkApp
    (d : Nat) (ν : Nat → String) (k m : Nat) (f a : Pattern) :
    closeAmbient d ν k m (Mettapedia.Languages.MeTTa.Pure.Core.mkApp f a)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkApp (closeAmbient d ν k m f) (closeAmbient d ν k m a) := by
  induction m generalizing d k f a with
  | zero =>
      simp [closeAmbient, Mettapedia.Languages.MeTTa.Pure.Core.mkApp]
  | succ m ih =>
      simpa [closeAmbient, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkApp] using
        ih (d := d + 1) (k := k)
          (f := closeFVar d (ν (k + m)) f)
          (a := closeFVar d (ν (k + m)) a)

@[simp] theorem closeAmbient_mkPair
    (d : Nat) (ν : Nat → String) (k m : Nat) (a b : Pattern) :
    closeAmbient d ν k m (Mettapedia.Languages.MeTTa.Pure.Core.mkPair a b)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkPair (closeAmbient d ν k m a) (closeAmbient d ν k m b) := by
  induction m generalizing d k a b with
  | zero =>
      simp [closeAmbient, Mettapedia.Languages.MeTTa.Pure.Core.mkPair]
  | succ m ih =>
      simpa [closeAmbient, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkPair] using
        ih (d := d + 1) (k := k)
          (a := closeFVar d (ν (k + m)) a)
          (b := closeFVar d (ν (k + m)) b)

@[simp] theorem closeAmbient_mkFst
    (d : Nat) (ν : Nat → String) (k m : Nat) (p : Pattern) :
    closeAmbient d ν k m (Mettapedia.Languages.MeTTa.Pure.Core.mkFst p)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkFst (closeAmbient d ν k m p) := by
  induction m generalizing d k p with
  | zero =>
      simp [closeAmbient, Mettapedia.Languages.MeTTa.Pure.Core.mkFst]
  | succ m ih =>
      simpa [closeAmbient, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkFst] using
        ih (d := d + 1) (k := k) (p := closeFVar d (ν (k + m)) p)

@[simp] theorem closeAmbient_mkSnd
    (d : Nat) (ν : Nat → String) (k m : Nat) (p : Pattern) :
    closeAmbient d ν k m (Mettapedia.Languages.MeTTa.Pure.Core.mkSnd p)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkSnd (closeAmbient d ν k m p) := by
  induction m generalizing d k p with
  | zero =>
      simp [closeAmbient, Mettapedia.Languages.MeTTa.Pure.Core.mkSnd]
  | succ m ih =>
      simpa [closeAmbient, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkSnd] using
        ih (d := d + 1) (k := k) (p := closeFVar d (ν (k + m)) p)

@[simp] theorem closeAmbient_mkRefl
    (d : Nat) (ν : Nat → String) (k m : Nat) (a : Pattern) :
    closeAmbient d ν k m (Mettapedia.Languages.MeTTa.Pure.Core.mkRefl a)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkRefl (closeAmbient d ν k m a) := by
  induction m generalizing d k a with
  | zero =>
      simp [closeAmbient, Mettapedia.Languages.MeTTa.Pure.Core.mkRefl]
  | succ m ih =>
      simpa [closeAmbient, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkRefl] using
        ih (d := d + 1) (k := k) (a := closeFVar d (ν (k + m)) a)

@[simp] theorem closeRange_mkId
    (ν : Nat → String) (k m : Nat) (A a b : Pattern) :
    closeRange ν k m (Mettapedia.Languages.MeTTa.Pure.Core.mkId A a b)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkId
      (closeRange ν k m A) (closeRange ν k m a) (closeRange ν k m b) := by
  induction m generalizing k A a b with
  | zero =>
      simp [closeRange, Mettapedia.Languages.MeTTa.Pure.Core.mkId]
  | succ m ih =>
      simpa [closeRange, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkId] using
        ih (k := k)
          (A := closeFVar 0 (ν (k + m)) A)
          (a := closeFVar 0 (ν (k + m)) a)
          (b := closeFVar 0 (ν (k + m)) b)

@[simp] theorem closeRange_mkApp
    (ν : Nat → String) (k m : Nat) (f a : Pattern) :
    closeRange ν k m (Mettapedia.Languages.MeTTa.Pure.Core.mkApp f a)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkApp (closeRange ν k m f) (closeRange ν k m a) := by
  induction m generalizing k f a with
  | zero =>
      simp [closeRange, Mettapedia.Languages.MeTTa.Pure.Core.mkApp]
  | succ m ih =>
      simpa [closeRange, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkApp] using
        ih (k := k)
          (f := closeFVar 0 (ν (k + m)) f)
          (a := closeFVar 0 (ν (k + m)) a)

@[simp] theorem closeRange_mkPair
    (ν : Nat → String) (k m : Nat) (a b : Pattern) :
    closeRange ν k m (Mettapedia.Languages.MeTTa.Pure.Core.mkPair a b)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkPair (closeRange ν k m a) (closeRange ν k m b) := by
  induction m generalizing k a b with
  | zero =>
      simp [closeRange, Mettapedia.Languages.MeTTa.Pure.Core.mkPair]
  | succ m ih =>
      simpa [closeRange, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkPair] using
        ih (k := k)
          (a := closeFVar 0 (ν (k + m)) a)
          (b := closeFVar 0 (ν (k + m)) b)

@[simp] theorem closeRange_mkFst
    (ν : Nat → String) (k m : Nat) (p : Pattern) :
    closeRange ν k m (Mettapedia.Languages.MeTTa.Pure.Core.mkFst p)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkFst (closeRange ν k m p) := by
  induction m generalizing k p with
  | zero =>
      simp [closeRange, Mettapedia.Languages.MeTTa.Pure.Core.mkFst]
  | succ m ih =>
      simpa [closeRange, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkFst] using
        ih (k := k) (p := closeFVar 0 (ν (k + m)) p)

@[simp] theorem closeRange_mkSnd
    (ν : Nat → String) (k m : Nat) (p : Pattern) :
    closeRange ν k m (Mettapedia.Languages.MeTTa.Pure.Core.mkSnd p)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkSnd (closeRange ν k m p) := by
  induction m generalizing k p with
  | zero =>
      simp [closeRange, Mettapedia.Languages.MeTTa.Pure.Core.mkSnd]
  | succ m ih =>
      simpa [closeRange, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkSnd] using
        ih (k := k) (p := closeFVar 0 (ν (k + m)) p)

@[simp] theorem closeRange_mkRefl
    (ν : Nat → String) (k m : Nat) (a : Pattern) :
    closeRange ν k m (Mettapedia.Languages.MeTTa.Pure.Core.mkRefl a)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkRefl (closeRange ν k m a) := by
  induction m generalizing k a with
  | zero =>
      simp [closeRange, Mettapedia.Languages.MeTTa.Pure.Core.mkRefl]
  | succ m ih =>
      simpa [closeRange, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkRefl] using
        ih (k := k) (a := closeFVar 0 (ν (k + m)) a)

theorem closeRangeAt_mkLam
    (d : Nat) (ν : Nat → String) (k m : Nat) (body : Pattern) :
    closeRangeAt d ν k m (Mettapedia.Languages.MeTTa.Pure.Core.mkLam body)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkLam
      (closeRangeAt (d + 1) ν k m body) := by
  induction m generalizing k body with
  | zero =>
      simp [closeRangeAt, Mettapedia.Languages.MeTTa.Pure.Core.mkLam]
  | succ m ih =>
      calc
        closeRangeAt d ν k (m + 1) (Mettapedia.Languages.MeTTa.Pure.Core.mkLam body)
            =
          closeRangeAt d ν k m
            (closeFVar d (ν (k + m)) (Mettapedia.Languages.MeTTa.Pure.Core.mkLam body)) := by
              simp [closeRangeAt]
        _ =
          closeRangeAt d ν k m
            (Mettapedia.Languages.MeTTa.Pure.Core.mkLam
              (closeFVar (d + 1) (ν (k + m)) body)) := by
                simp [Mettapedia.Languages.MeTTa.Pure.Core.mkLam, closeFVar]
        _ =
          Mettapedia.Languages.MeTTa.Pure.Core.mkLam
            (closeRangeAt (d + 1) ν k m
              (closeFVar (d + 1) (ν (k + m)) body)) := by
                simpa using ih (k := k) (body := closeFVar (d + 1) (ν (k + m)) body)
        _ =
          Mettapedia.Languages.MeTTa.Pure.Core.mkLam
            (closeRangeAt (d + 1) ν k (m + 1) body) := by
                simp [closeRangeAt]

theorem closeRangeAt_mkPi
    (d : Nat) (ν : Nat → String) (k m : Nat) (A B : Pattern) :
    closeRangeAt d ν k m (Mettapedia.Languages.MeTTa.Pure.Core.mkPi A B)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkPi
      (closeRangeAt d ν k m A)
      (closeRangeAt (d + 1) ν k m B) := by
  induction m generalizing k A B with
  | zero =>
      simp [closeRangeAt, Mettapedia.Languages.MeTTa.Pure.Core.mkPi]
  | succ m ih =>
      calc
        closeRangeAt d ν k (m + 1) (Mettapedia.Languages.MeTTa.Pure.Core.mkPi A B)
            =
          closeRangeAt d ν k m
            (closeFVar d (ν (k + m)) (Mettapedia.Languages.MeTTa.Pure.Core.mkPi A B)) := by
              simp [closeRangeAt]
        _ =
          closeRangeAt d ν k m
            (Mettapedia.Languages.MeTTa.Pure.Core.mkPi
              (closeFVar d (ν (k + m)) A)
              (closeFVar (d + 1) (ν (k + m)) B)) := by
                simp [Mettapedia.Languages.MeTTa.Pure.Core.mkPi, closeFVar]
        _ =
          Mettapedia.Languages.MeTTa.Pure.Core.mkPi
            (closeRangeAt d ν k m (closeFVar d (ν (k + m)) A))
            (closeRangeAt (d + 1) ν k m (closeFVar (d + 1) (ν (k + m)) B)) := by
                simpa using ih (k := k)
                  (A := closeFVar d (ν (k + m)) A)
                  (B := closeFVar (d + 1) (ν (k + m)) B)
        _ =
          Mettapedia.Languages.MeTTa.Pure.Core.mkPi
            (closeRangeAt d ν k (m + 1) A)
            (closeRangeAt (d + 1) ν k (m + 1) B) := by
                simp [closeRangeAt]

theorem closeRangeAt_mkSigma
    (d : Nat) (ν : Nat → String) (k m : Nat) (A B : Pattern) :
    closeRangeAt d ν k m (Mettapedia.Languages.MeTTa.Pure.Core.mkSigma A B)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkSigma
      (closeRangeAt d ν k m A)
      (closeRangeAt (d + 1) ν k m B) := by
  induction m generalizing k A B with
  | zero =>
      simp [closeRangeAt, Mettapedia.Languages.MeTTa.Pure.Core.mkSigma]
  | succ m ih =>
      calc
        closeRangeAt d ν k (m + 1) (Mettapedia.Languages.MeTTa.Pure.Core.mkSigma A B)
            =
          closeRangeAt d ν k m
            (closeFVar d (ν (k + m)) (Mettapedia.Languages.MeTTa.Pure.Core.mkSigma A B)) := by
              simp [closeRangeAt]
        _ =
          closeRangeAt d ν k m
            (Mettapedia.Languages.MeTTa.Pure.Core.mkSigma
              (closeFVar d (ν (k + m)) A)
              (closeFVar (d + 1) (ν (k + m)) B)) := by
                simp [Mettapedia.Languages.MeTTa.Pure.Core.mkSigma, closeFVar]
        _ =
          Mettapedia.Languages.MeTTa.Pure.Core.mkSigma
            (closeRangeAt d ν k m (closeFVar d (ν (k + m)) A))
            (closeRangeAt (d + 1) ν k m (closeFVar (d + 1) (ν (k + m)) B)) := by
                simpa using ih (k := k)
                  (A := closeFVar d (ν (k + m)) A)
                  (B := closeFVar (d + 1) (ν (k + m)) B)
        _ =
          Mettapedia.Languages.MeTTa.Pure.Core.mkSigma
            (closeRangeAt d ν k (m + 1) A)
            (closeRangeAt (d + 1) ν k (m + 1) B) := by
                simp [closeRangeAt]

@[simp] theorem closeRangeAt_mkId
    (d : Nat) (ν : Nat → String) (k m : Nat) (A a b : Pattern) :
    closeRangeAt d ν k m (Mettapedia.Languages.MeTTa.Pure.Core.mkId A a b)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkId
      (closeRangeAt d ν k m A) (closeRangeAt d ν k m a) (closeRangeAt d ν k m b) := by
  induction m generalizing k A a b with
  | zero =>
      simp [closeRangeAt, Mettapedia.Languages.MeTTa.Pure.Core.mkId]
  | succ m ih =>
      simpa [closeRangeAt, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkId] using
        ih (k := k)
          (A := closeFVar d (ν (k + m)) A)
          (a := closeFVar d (ν (k + m)) a)
          (b := closeFVar d (ν (k + m)) b)

@[simp] theorem closeRangeAt_mkApp
    (d : Nat) (ν : Nat → String) (k m : Nat) (f a : Pattern) :
    closeRangeAt d ν k m (Mettapedia.Languages.MeTTa.Pure.Core.mkApp f a)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkApp (closeRangeAt d ν k m f) (closeRangeAt d ν k m a) := by
  induction m generalizing k f a with
  | zero =>
      simp [closeRangeAt, Mettapedia.Languages.MeTTa.Pure.Core.mkApp]
  | succ m ih =>
      simpa [closeRangeAt, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkApp] using
        ih (k := k)
          (f := closeFVar d (ν (k + m)) f)
          (a := closeFVar d (ν (k + m)) a)

@[simp] theorem closeRangeAt_mkPair
    (d : Nat) (ν : Nat → String) (k m : Nat) (a b : Pattern) :
    closeRangeAt d ν k m (Mettapedia.Languages.MeTTa.Pure.Core.mkPair a b)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkPair (closeRangeAt d ν k m a) (closeRangeAt d ν k m b) := by
  induction m generalizing k a b with
  | zero =>
      simp [closeRangeAt, Mettapedia.Languages.MeTTa.Pure.Core.mkPair]
  | succ m ih =>
      simpa [closeRangeAt, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkPair] using
        ih (k := k)
          (a := closeFVar d (ν (k + m)) a)
          (b := closeFVar d (ν (k + m)) b)

@[simp] theorem closeRangeAt_mkFst
    (d : Nat) (ν : Nat → String) (k m : Nat) (p : Pattern) :
    closeRangeAt d ν k m (Mettapedia.Languages.MeTTa.Pure.Core.mkFst p)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkFst (closeRangeAt d ν k m p) := by
  induction m generalizing k p with
  | zero =>
      simp [closeRangeAt, Mettapedia.Languages.MeTTa.Pure.Core.mkFst]
  | succ m ih =>
      simpa [closeRangeAt, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkFst] using
        ih (k := k) (p := closeFVar d (ν (k + m)) p)

@[simp] theorem closeRangeAt_mkSnd
    (d : Nat) (ν : Nat → String) (k m : Nat) (p : Pattern) :
    closeRangeAt d ν k m (Mettapedia.Languages.MeTTa.Pure.Core.mkSnd p)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkSnd (closeRangeAt d ν k m p) := by
  induction m generalizing k p with
  | zero =>
      simp [closeRangeAt, Mettapedia.Languages.MeTTa.Pure.Core.mkSnd]
  | succ m ih =>
      simpa [closeRangeAt, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkSnd] using
        ih (k := k) (p := closeFVar d (ν (k + m)) p)

@[simp] theorem closeRangeAt_mkRefl
    (d : Nat) (ν : Nat → String) (k m : Nat) (a : Pattern) :
    closeRangeAt d ν k m (Mettapedia.Languages.MeTTa.Pure.Core.mkRefl a)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkRefl (closeRangeAt d ν k m a) := by
  induction m generalizing k a with
  | zero =>
      simp [closeRangeAt, Mettapedia.Languages.MeTTa.Pure.Core.mkRefl]
  | succ m ih =>
      simpa [closeRangeAt, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkRefl] using
        ih (k := k) (a := closeFVar d (ν (k + m)) a)

theorem closeRange_mkLam_shifted
    (ν : Nat → String) (k m : Nat) (body : Pattern) :
    closeRange ν k m (Mettapedia.Languages.MeTTa.Pure.Core.mkLam body)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkLam
      (closeRangeAt 1 ν k m body) := by
  rw [closeRange_eq_closeRangeAt_zero]
  simpa using closeRangeAt_mkLam 0 ν k m body

theorem closeRange_mkPi_shifted
    (ν : Nat → String) (k m : Nat) (A B : Pattern) :
    closeRange ν k m (Mettapedia.Languages.MeTTa.Pure.Core.mkPi A B)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkPi
      (closeRangeAt 0 ν k m A)
      (closeRangeAt 1 ν k m B) := by
  rw [closeRange_eq_closeRangeAt_zero]
  simpa using closeRangeAt_mkPi 0 ν k m A B

theorem closeRange_mkSigma_shifted
    (ν : Nat → String) (k m : Nat) (A B : Pattern) :
    closeRange ν k m (Mettapedia.Languages.MeTTa.Pure.Core.mkSigma A B)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkSigma
      (closeRangeAt 0 ν k m A)
      (closeRangeAt 1 ν k m B) := by
  rw [closeRange_eq_closeRangeAt_zero]
  simpa using closeRangeAt_mkSigma 0 ν k m A B

theorem inst0BinderClosedLhs_lam_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (b : PureTm (((n + 1) + m) + 1)) :
    inst0BinderClosedLhs ν m k ρ a (.lam b)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkLam
      (closeRangeAt 1 ν k m
        (closeFVar 0 (ν (k + m))
          (quoteTmWith ν (k + m + 1) (buildEnv ν k (m + 1) ρ)
            (subst (liftSubN (m + 1) (subst0 a)) b)))) := by
  simp [inst0BinderClosedLhs, quoteTmWith, subst, closeRange_mkLam_shifted, buildEnv, liftSubN,
    Nat.add_assoc, Nat.add_comm]

theorem inst0BinderClosedTarget_lam_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (b : PureTm (((n + 1) + m) + 1)) :
    inst0BinderClosedTarget ν m k ρ a (.lam b)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkLam
      (applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν (k + m) ρ a))
        (closeRangeAt 1 ν (k + 1) m
          (closeFVar 0 (ν (k + m + 1))
            (quoteTmWith ν (k + m + 2)
              (buildEnv ν (k + 1) (m + 1) (envCons (ν k) ρ)) b)))) := by
  simp [inst0BinderClosedTarget, quoteTmWith, closeRange_mkLam_shifted, applySubst_mkLam, buildEnv,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

def inst0BinderBodyClosedLhs
    (ν : Nat → String) {n : Nat}
    (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) (b : PureTm (((n + 1) + m) + 1)) : Pattern :=
  closeRangeAt 1 ν k m
    (closeFVar 0 (ν (k + m))
      (quoteTmWith ν (k + m + 1) (buildEnv ν k (m + 1) ρ)
        (subst (liftSubN (m + 1) (subst0 a)) b)))

def inst0BinderBodyClosedTarget
    (ν : Nat → String) {n : Nat}
    (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) (b : PureTm (((n + 1) + m) + 1)) : Pattern :=
  applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν (k + m) ρ a))
    (closeRangeAt 1 ν (k + 1) m
      (closeFVar 0 (ν (k + m + 1))
        (quoteTmWith ν (k + m + 2)
          (buildEnv ν (k + 1) (m + 1) (envCons (ν k) ρ)) b)))

def inst0BinderBodyTargetEq
    (ν : Nat → String) {n : Nat}
    (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) (b : PureTm (((n + 1) + m) + 1)) : Prop :=
  inst0BinderBodyClosedLhs ν m k ρ a b = inst0BinderBodyClosedTarget ν m k ρ a b

theorem inst0AmbientClosedLhs_one_eq
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (b : PureTm (((n + 1) + m) + 1)) :
    inst0AmbientClosedLhs 1 ν m k ρ a b = inst0BinderBodyClosedLhs ν m k ρ a b := by
  simp [inst0AmbientClosedLhs, inst0BinderBodyClosedLhs]

theorem inst0AmbientClosedTarget_one_eq
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (b : PureTm (((n + 1) + m) + 1)) :
    inst0AmbientClosedTarget 1 ν m k ρ a b = inst0BinderBodyClosedTarget ν m k ρ a b := by
  simp [inst0AmbientClosedTarget, inst0BinderBodyClosedTarget]

theorem inst0AmbientTargetEq_one_iff
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (b : PureTm (((n + 1) + m) + 1)) :
    inst0AmbientTargetEq 1 ν m k ρ a b ↔ inst0BinderBodyTargetEq ν m k ρ a b := by
  simp [inst0AmbientTargetEq, inst0BinderBodyTargetEq, inst0AmbientClosedLhs_one_eq,
    inst0AmbientClosedTarget_one_eq]

def inst0BinderBodyClosedLhsDistinct
    (ν : Nat → String) {n : Nat}
    (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) (b : PureTm (((n + 1) + m) + 1)) : Pattern :=
  closeAmbient 1 ν k m
    (closeFVar 0 (ν (k + m))
      (quoteTmWith ν (k + m + 1) (buildEnv ν k (m + 1) ρ)
        (subst (liftSubN (m + 1) (subst0 a)) b)))

def inst0BinderBodyClosedTargetDistinct
    (ν : Nat → String) {n : Nat}
    (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) (b : PureTm (((n + 1) + m) + 1)) : Pattern :=
  applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν (k + m) ρ a))
    (closeAmbient 1 ν (k + 1) m
      (closeFVar 0 (ν (k + m + 1))
        (quoteTmWith ν (k + m + 2)
          (buildEnv ν (k + 1) (m + 1) (envCons (ν k) ρ)) b)))

def inst0BinderBodyTargetEqDistinct
    (ν : Nat → String) {n : Nat}
    (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) (b : PureTm (((n + 1) + m) + 1)) : Prop :=
  inst0BinderBodyClosedLhsDistinct ν m k ρ a b =
    inst0BinderBodyClosedTargetDistinct ν m k ρ a b

theorem inst0AmbientDistinctClosedLhs_one_eq
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (b : PureTm (((n + 1) + m) + 1)) :
    inst0AmbientDistinctClosedLhs 1 ν m k ρ a b =
      inst0BinderBodyClosedLhsDistinct ν m k ρ a b := by
  simp [inst0AmbientDistinctClosedLhs, inst0BinderBodyClosedLhsDistinct]

theorem inst0AmbientDistinctClosedTarget_one_eq
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (b : PureTm (((n + 1) + m) + 1)) :
    inst0AmbientDistinctClosedTarget 1 ν m k ρ a b =
      inst0BinderBodyClosedTargetDistinct ν m k ρ a b := by
  simp [inst0AmbientDistinctClosedTarget, inst0BinderBodyClosedTargetDistinct]

theorem inst0AmbientDistinctTargetEq_one_iff
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (b : PureTm (((n + 1) + m) + 1)) :
    inst0AmbientDistinctTargetEq 1 ν m k ρ a b ↔
      inst0BinderBodyTargetEqDistinct ν m k ρ a b := by
  simp [inst0AmbientDistinctTargetEq, inst0BinderBodyTargetEqDistinct,
    inst0AmbientDistinctClosedLhs_one_eq, inst0AmbientDistinctClosedTarget_one_eq]

theorem inst0BinderBodyTargetEq_zero
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) :
    inst0BinderBodyTargetEq ν m k ρ a (.var 0) := by
  unfold inst0BinderBodyTargetEq inst0BinderBodyClosedLhs inst0BinderBodyClosedTarget
  have hhead :
      closeFVar 0 (ν (k + m))
        (quoteTmWith ν (k + m + 1) (buildEnv ν k (m + 1) ρ)
          (subst (liftSubN (m + 1) (subst0 a)) (.var 0)))
      = .bvar 0 := by
    simp [quoteTmWith, buildEnv, subst, liftSubN, envCons, closeFVar, Nat.add_assoc, Nat.add_comm]
  calc
    closeRangeAt 1 ν k m
        (closeFVar 0 (ν (k + m))
          (quoteTmWith ν (k + m + 1) (buildEnv ν k (m + 1) ρ)
            (subst (liftSubN (m + 1) (subst0 a)) (.var 0))))
      = closeRangeAt 1 ν k m (.bvar 0) := by
          rw [hhead]
    _ = .bvar 0 := by
          simp [closeRangeAt_bvar]
    _ = applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν (k + m) ρ a))
          (closeRangeAt 1 ν (k + 1) m
            (closeFVar 0 (ν (k + m + 1))
              (quoteTmWith ν (k + m + 2)
                (buildEnv ν (k + 1) (m + 1) (envCons (ν k) ρ)) (.var 0)))) := by
          simp [quoteTmWith, buildEnv, envCons, closeFVar, closeRangeAt_bvar,
            Nat.add_assoc, Nat.add_comm, applySubst]

theorem inst0BinderBodyTargetEqDistinct_zero
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) :
    inst0BinderBodyTargetEqDistinct ν m k ρ a (.var 0) := by
  unfold inst0BinderBodyTargetEqDistinct inst0BinderBodyClosedLhsDistinct inst0BinderBodyClosedTargetDistinct
  have hhead :
      closeFVar 0 (ν (k + m))
        (quoteTmWith ν (k + m + 1) (buildEnv ν k (m + 1) ρ)
          (subst (liftSubN (m + 1) (subst0 a)) (.var 0)))
      = .bvar 0 := by
    simp [quoteTmWith, buildEnv, subst, liftSubN, envCons, closeFVar, Nat.add_assoc, Nat.add_comm]
  calc
    closeAmbient 1 ν k m
        (closeFVar 0 (ν (k + m))
          (quoteTmWith ν (k + m + 1) (buildEnv ν k (m + 1) ρ)
            (subst (liftSubN (m + 1) (subst0 a)) (.var 0))))
      = closeAmbient 1 ν k m (.bvar 0) := by
          rw [hhead]
    _ = .bvar 0 := by
          simp [closeAmbient_bvar]
    _ = applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν (k + m) ρ a))
          (closeAmbient 1 ν (k + 1) m
            (closeFVar 0 (ν (k + m + 1))
              (quoteTmWith ν (k + m + 2)
                (buildEnv ν (k + 1) (m + 1) (envCons (ν k) ρ)) (.var 0)))) := by
          simp [quoteTmWith, buildEnv, envCons, closeFVar, closeAmbient_bvar,
            Nat.add_assoc, Nat.add_comm, applySubst]

theorem inst0BinderBodyClosedLhs_prefix_succ
    {ν : Nat → String} (hinj : Function.Injective ν)
    (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) (i : Fin m) :
    inst0BinderBodyClosedLhs ν m k ρ a (.var (Fin.succ (prefixIdx (n + 1) i))) = .bvar 1 := by
  rcases buildEnv_prefix_name ν k ρ i with ⟨r, hr, hname⟩
  have hneq : ν (k + r) ≠ ν (k + m) := by
    intro hEq
    have : k + r = k + m := hinj hEq
    omega
  calc
    inst0BinderBodyClosedLhs ν m k ρ a (.var (Fin.succ (prefixIdx (n + 1) i)))
        =
      closeRangeAt 1 ν k m
        (closeFVar 0 (ν (k + m)) (.fvar (buildEnv ν k m ρ (prefixIdx n i)))) := by
          simp [inst0BinderBodyClosedLhs, liftSubN_prefix_apply, quoteTmWith, buildEnv, envCons,
            rename, wk, Nat.add_assoc, Nat.add_comm]
    _ = closeRangeAt 1 ν k m (.fvar (buildEnv ν k m ρ (prefixIdx n i))) := by
          simp [closeFVar, hneq, hname]
    _ = closeRangeAt 1 ν k m (.fvar (ν (k + r))) := by
          simp [hname]
    _ = .bvar 1 := closeRangeAt_bound_name hinj 1 k m r hr

theorem inst0BinderBodyClosedTarget_prefix_succ
    {ν : Nat → String} (hinj : Function.Injective ν)
    (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) (i : Fin m) :
    inst0BinderBodyClosedTarget ν m k ρ a (.var (Fin.succ (prefixIdx (n + 1) i))) = .bvar 1 := by
  rcases buildEnv_prefix_name ν (k + 1) (envCons (ν k) ρ) i with ⟨r, hr, hname⟩
  have hneq : ν (k + 1 + r) ≠ ν (k + m + 1) := by
    intro hEq
    have : k + 1 + r = k + m + 1 := hinj hEq
    omega
  calc
    inst0BinderBodyClosedTarget ν m k ρ a (.var (Fin.succ (prefixIdx (n + 1) i)))
        =
      applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν (k + m) ρ a))
        (closeRangeAt 1 ν (k + 1) m (.fvar (ν (k + 1 + r)))) := by
          simp [inst0BinderBodyClosedTarget, quoteTmWith, buildEnv, hname, closeFVar, hneq, envCons]
    _ =
      applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν (k + m) ρ a)) (.bvar 1) := by
        rw [closeRangeAt_bound_name hinj 1 (k + 1) m r hr]
    _ = .bvar 1 := by
        simp [applySubst]

theorem inst0BinderBodyTargetEq_prefix_succ
    {ν : Nat → String} (hinj : Function.Injective ν)
    (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) (i : Fin m) :
    inst0BinderBodyTargetEq ν m k ρ a (.var (Fin.succ (prefixIdx (n + 1) i))) := by
  unfold inst0BinderBodyTargetEq
  rw [inst0BinderBodyClosedLhs_prefix_succ hinj m k ρ a i,
    inst0BinderBodyClosedTarget_prefix_succ hinj m k ρ a i]

theorem inst0BinderBodyClosedLhsDistinct_prefix_succ
    {ν : Nat → String} (hinj : Function.Injective ν)
    (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) (i : Fin m) :
    inst0BinderBodyClosedLhsDistinct ν m k ρ a (.var (Fin.succ (prefixIdx (n + 1) i)))
      = .bvar (i.1 + 1) := by
  have hname :
      buildEnv ν k m ρ (prefixIdx n i) = ν (k + (m - 1 - i.1)) :=
    buildEnv_prefix_name_exact ν k ρ i
  have hneq : ν (k + (m - 1 - i.1)) ≠ ν (k + m) := by
    intro hEq
    have : k + (m - 1 - i.1) = k + m := hinj hEq
    omega
  have hr : m - 1 - i.1 < m := by
    omega
  calc
    inst0BinderBodyClosedLhsDistinct ν m k ρ a (.var (Fin.succ (prefixIdx (n + 1) i)))
        =
      closeAmbient 1 ν k m
        (closeFVar 0 (ν (k + m)) (.fvar (buildEnv ν k m ρ (prefixIdx n i)))) := by
          simp [inst0BinderBodyClosedLhsDistinct, liftSubN_prefix_apply, quoteTmWith, buildEnv, envCons,
            rename, wk, Nat.add_assoc, Nat.add_comm]
    _ = closeAmbient 1 ν k m (.fvar (buildEnv ν k m ρ (prefixIdx n i))) := by
          simp [closeFVar, hneq, hname]
    _ = closeAmbient 1 ν k m (.fvar (ν (k + (m - 1 - i.1)))) := by
          simp [hname]
    _ = .bvar (1 + (m - 1 - (m - 1 - i.1))) := closeAmbient_bound_name hinj 1 k m (m - 1 - i.1) hr
    _ = .bvar (i.1 + 1) := by
          have hidx : 1 + (m - 1 - (m - 1 - i.1)) = i.1 + 1 := by
            omega
          simp [hidx]

theorem inst0BinderBodyClosedTargetDistinct_prefix_succ
    {ν : Nat → String} (hinj : Function.Injective ν)
    (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) (i : Fin m) :
    inst0BinderBodyClosedTargetDistinct ν m k ρ a (.var (Fin.succ (prefixIdx (n + 1) i)))
      = .bvar (i.1 + 1) := by
  have hname :
      buildEnv ν (k + 1) m (envCons (ν k) ρ) (prefixIdx (n + 1) i)
        = ν ((k + 1) + (m - 1 - i.1)) :=
    buildEnv_prefix_name_exact ν (k + 1) (envCons (ν k) ρ) i
  have hneq : ν ((k + 1) + (m - 1 - i.1)) ≠ ν (k + m + 1) := by
    intro hEq
    have : (k + 1) + (m - 1 - i.1) = k + m + 1 := hinj hEq
    omega
  have hr : m - 1 - i.1 < m := by
    omega
  calc
    inst0BinderBodyClosedTargetDistinct ν m k ρ a (.var (Fin.succ (prefixIdx (n + 1) i)))
        =
      applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν (k + m) ρ a))
        (closeAmbient 1 ν (k + 1) m (.fvar (ν ((k + 1) + (m - 1 - i.1))))) := by
          simp [inst0BinderBodyClosedTargetDistinct, quoteTmWith, buildEnv, hname, closeFVar, hneq,
            envCons]
    _ =
      applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν (k + m) ρ a))
        (.bvar (1 + (m - 1 - (m - 1 - i.1)))) := by
          rw [closeAmbient_bound_name hinj 1 (k + 1) m (m - 1 - i.1) hr]
    _ = .bvar (i.1 + 1) := by
        have hidx : 1 + (m - 1 - (m - 1 - i.1)) = i.1 + 1 := by
          omega
        simp [applySubst, hidx]

theorem inst0BinderBodyTargetEqDistinct_prefix_succ
    {ν : Nat → String} (hinj : Function.Injective ν)
    (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) (i : Fin m) :
    inst0BinderBodyTargetEqDistinct ν m k ρ a (.var (Fin.succ (prefixIdx (n + 1) i))) := by
  unfold inst0BinderBodyTargetEqDistinct
  rw [inst0BinderBodyClosedLhsDistinct_prefix_succ hinj m k ρ a i,
    inst0BinderBodyClosedTargetDistinct_prefix_succ hinj m k ρ a i]

theorem inst0BinderBodyTargetEqDistinct_wkN_succ
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ)
    (m : Nat) (a : PureTm n) (j : Fin n) :
    inst0BinderBodyTargetEqDistinct ν m k ρ a (.var (wkN (n := n + 1) (m + 1) j.succ)) := by
  have hrename :
      liftSubN (m + 1) (subst0 a) (wkN (n := n + 1) (m + 1) j.succ)
        = renameWkN (m + 1) (.var j) := by
    simpa using
      (liftSubN_wkN_apply (m := m + 1) (σ := subst0 a) (i := j.succ))
  have hL :
      inst0BinderBodyClosedLhsDistinct ν m k ρ a (.var (wkN (n := n + 1) (m + 1) j.succ))
        = .fvar (ρ j) := by
    calc
      inst0BinderBodyClosedLhsDistinct ν m k ρ a (.var (wkN (n := n + 1) (m + 1) j.succ))
          =
        closeAmbient 1 ν k m
          (closeFVar 0 (ν (k + m))
            (quoteTmWith ν (k + m + 1) (buildEnv ν k (m + 1) ρ)
              (liftSubN (m + 1) (subst0 a) (wkN (n := n + 1) (m + 1) j.succ)))) := by
                simp [inst0BinderBodyClosedLhsDistinct]
      _ =
        closeAmbient 1 ν k m
          (closeFVar 0 (ν (k + m))
            (quoteTmWith ν (k + m + 1) (buildEnv ν k (m + 1) ρ)
              (renameWkN (m + 1) (.var j)))) := by
                rw [hrename]
      _ =
        closeAmbient 1 ν k m
          (quoteTmWith ν (k + m + 1) (buildEnv ν k m ρ) (renameWkN m (.var j))) := by
            rw [closeFVar_quoteTmWith_renameWkN_buildEnv_head hcompat]
      _ = .fvar (ρ j) := by
            rw [closeAmbient_quoteTmWith_renameWkN_buildEnv_any hcompat]
            simp [quoteTmWith]
  have hclose :
      closeAmbient 1 ν (k + 1) m (.fvar (ρ j)) = .fvar (ρ j) := by
    apply closeAmbient_fvar_of_ne
    intro r hr
    exact hcompat.2 j (k + 1 + r) (by omega)
  have hne : ρ j ≠ ν k := hcompat.2 j k (by omega)
  have hR :
      inst0BinderBodyClosedTargetDistinct ν m k ρ a (.var (wkN (n := n + 1) (m + 1) j.succ))
        = .fvar (ρ j) := by
    have hlookup :
        buildEnv ν (k + 1) (m + 1) (envCons (ν k) ρ)
          (wkN (n := n + 1) (m + 1) j.succ) = ρ j := by
      simpa [envCons] using
        (buildEnv_wkN_apply ν (k + 1) (m + 1) (envCons (ν k) ρ) j.succ)
    have hlookup' :
        envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))
          (wk (wkN (n := n + 1) m j.succ)) = ρ j := by
      simpa [buildEnv, wkN, envCons, Nat.add_assoc] using hlookup
    have hvar :
        quoteTmWith ν (k + m + 2)
          (buildEnv ν (k + 1) (m + 1) (envCons (ν k) ρ))
          (.var (wkN (n := n + 1) (m + 1) j.succ))
        = .fvar (ρ j) := by
      simp [quoteTmWith, hlookup']
    have hfuture : ρ j ≠ ν (k + m + 1) := hcompat.2 j (k + m + 1) (by omega)
    calc
      inst0BinderBodyClosedTargetDistinct ν m k ρ a (.var (wkN (n := n + 1) (m + 1) j.succ))
          =
        applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν (k + m) ρ a))
          (closeAmbient 1 ν (k + 1) m (.fvar (ρ j))) := by
            unfold inst0BinderBodyClosedTargetDistinct
            rw [hvar]
            simp [closeFVar, hfuture]
      _ =
        applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν (k + m) ρ a))
          (.fvar (ρ j)) := by
            rw [hclose]
      _ = .fvar (ρ j) := by
            rw [applySubst, SubstEnv.find_extend_ne hne.symm]
            simp [SubstEnv.find, SubstEnv.empty]
  unfold inst0BinderBodyTargetEqDistinct
  rw [hL, hR]

theorem inst0BinderBodyClosedLhsDistinct_wkN_zero
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ)
    (m : Nat) (a : PureTm n) :
    inst0BinderBodyClosedLhsDistinct ν m k ρ a (.var (wkN (n := n + 1) (m + 1) 0))
      = quoteTmWith ν (k + m + 1) ρ a := by
  have hrename :
      liftSubN (m + 1) (subst0 a) (wkN (n := n + 1) (m + 1) 0)
        = renameWkN (m + 1) a := by
    simpa using
      (liftSubN_wkN_apply (m := m + 1) (σ := subst0 a) (i := (0 : Fin (n + 1))))
  calc
    inst0BinderBodyClosedLhsDistinct ν m k ρ a (.var (wkN (n := n + 1) (m + 1) 0))
        =
      closeAmbient 1 ν k m
        (closeFVar 0 (ν (k + m))
          (quoteTmWith ν (k + m + 1) (buildEnv ν k (m + 1) ρ)
            (liftSubN (m + 1) (subst0 a) (wkN (n := n + 1) (m + 1) 0)))) := by
              simp [inst0BinderBodyClosedLhsDistinct]
    _ =
      closeAmbient 1 ν k m
        (closeFVar 0 (ν (k + m))
          (quoteTmWith ν (k + m + 1) (buildEnv ν k (m + 1) ρ)
            (renameWkN (m + 1) a))) := by
              rw [hrename]
    _ =
      closeAmbient 1 ν k m
        (quoteTmWith ν (k + m + 1) (buildEnv ν k m ρ) (renameWkN m a)) := by
          rw [closeFVar_quoteTmWith_renameWkN_buildEnv_head hcompat]
    _ = quoteTmWith ν (k + m + 1) ρ a := by
          rw [closeAmbient_quoteTmWith_renameWkN_buildEnv_any hcompat]

theorem inst0BinderBodyClosedTargetDistinct_wkN_zero
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ)
    (m : Nat) (a : PureTm n) :
    inst0BinderBodyClosedTargetDistinct ν m k ρ a (.var (wkN (n := n + 1) (m + 1) 0))
      = quoteTmWith ν (k + m) ρ a := by
  have hlookup :
      buildEnv ν (k + 1) (m + 1) (envCons (ν k) ρ)
        (wkN (n := n + 1) (m + 1) 0) = ν k := by
    simpa [envCons] using
      (buildEnv_wkN_apply ν (k + 1) (m + 1) (envCons (ν k) ρ) (0 : Fin (n + 1)))
  have hlookup' :
      envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))
        (wk (wkN (n := n + 1) m 0)) = ν k := by
    simpa [buildEnv, wkN, envCons, Nat.add_assoc] using hlookup
  have hvar :
      quoteTmWith ν (k + m + 2)
        (buildEnv ν (k + 1) (m + 1) (envCons (ν k) ρ))
        (.var (wkN (n := n + 1) (m + 1) 0))
      = .fvar (ν k) := by
    simp [quoteTmWith, hlookup']
  have hfuture : ν k ≠ ν (k + m + 1) := by
    intro hEq
    have : k = k + m + 1 := hcompat.1 hEq
    omega
  have hclose :
      closeAmbient 1 ν (k + 1) m (.fvar (ν k)) = .fvar (ν k) := by
    apply closeAmbient_fvar_of_ne
    intro r hr hEq
    have : k = k + 1 + r := hcompat.1 hEq
    omega
  calc
    inst0BinderBodyClosedTargetDistinct ν m k ρ a (.var (wkN (n := n + 1) (m + 1) 0))
        =
      applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν (k + m) ρ a))
        (closeAmbient 1 ν (k + 1) m (.fvar (ν k))) := by
          unfold inst0BinderBodyClosedTargetDistinct
          rw [hvar]
          simp [closeFVar, hfuture]
    _ =
      applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν (k + m) ρ a))
        (.fvar (ν k)) := by
          rw [hclose]
    _ = quoteTmWith ν (k + m) ρ a := by
          rw [applySubst, SubstEnv.find_extend_eq]

theorem inst0BinderBodyTargetEqDistinct_wkN_zero_of
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ)
    (m : Nat) (a : PureTm n)
    (hstep : quoteTmWith ν (k + m + 1) ρ a = quoteTmWith ν (k + m) ρ a) :
    inst0BinderBodyTargetEqDistinct ν m k ρ a (.var (wkN (n := n + 1) (m + 1) 0)) := by
  unfold inst0BinderBodyTargetEqDistinct
  rw [inst0BinderBodyClosedLhsDistinct_wkN_zero hcompat m a,
    inst0BinderBodyClosedTargetDistinct_wkN_zero hcompat m a]
  exact hstep

theorem inst0BinderBodyTargetEqDistinct_wkN_zero
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ)
    (m : Nat) (a : PureTm n) :
    inst0BinderBodyTargetEqDistinct ν m k ρ a (.var (wkN (n := n + 1) (m + 1) 0)) := by
  apply inst0BinderBodyTargetEqDistinct_wkN_zero_of hcompat m a
  exact quoteTmWith_depth_indep_staging ν (k + m + 1) (k + m) ρ a
    (quoteCompat_mono hcompat (j := k + m + 1) (by omega))
    (quoteCompat_mono hcompat (j := k + m) (by omega))

theorem inst0BinderBodyTargetEq_wkN_succ
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ)
    (m : Nat) (a : PureTm n) (j : Fin n) :
    inst0BinderBodyTargetEq ν m k ρ a (.var (wkN (n := n + 1) (m + 1) j.succ)) := by
  have hrename :
      liftSubN (m + 1) (subst0 a) (wkN (n := n + 1) (m + 1) j.succ)
        = renameWkN (m + 1) (.var j) := by
    simpa using
      (liftSubN_wkN_apply (m := m + 1) (σ := subst0 a) (i := j.succ))
  have hL :
      inst0BinderBodyClosedLhs ν m k ρ a (.var (wkN (n := n + 1) (m + 1) j.succ))
        = .fvar (ρ j) := by
    calc
      inst0BinderBodyClosedLhs ν m k ρ a (.var (wkN (n := n + 1) (m + 1) j.succ))
          =
        closeRangeAt 1 ν k m
          (closeFVar 0 (ν (k + m))
            (quoteTmWith ν (k + m + 1) (buildEnv ν k (m + 1) ρ)
              (liftSubN (m + 1) (subst0 a) (wkN (n := n + 1) (m + 1) j.succ)))) := by
                simp [inst0BinderBodyClosedLhs]
      _ =
        closeRangeAt 1 ν k m
          (closeFVar 0 (ν (k + m))
            (quoteTmWith ν (k + m + 1) (buildEnv ν k (m + 1) ρ)
              (renameWkN (m + 1) (.var j)))) := by
                rw [hrename]
      _ =
        closeRangeAt 1 ν k m
          (quoteTmWith ν (k + m + 1) (buildEnv ν k m ρ) (renameWkN m (.var j))) := by
            rw [closeFVar_quoteTmWith_renameWkN_buildEnv_head hcompat]
      _ = .fvar (ρ j) := by
            rw [closeRangeAt_quoteTmWith_renameWkN_buildEnv_any hcompat]
            simp [quoteTmWith]
  have hclose :
      closeRangeAt 1 ν (k + 1) m (.fvar (ρ j)) = .fvar (ρ j) := by
    apply closeRangeAt_fvar_of_ne
    intro r hr
    exact hcompat.2 j (k + 1 + r) (by omega)
  have hne : ρ j ≠ ν k := hcompat.2 j k (by omega)
  have hR :
      inst0BinderBodyClosedTarget ν m k ρ a (.var (wkN (n := n + 1) (m + 1) j.succ))
        = .fvar (ρ j) := by
    have hlookup :
        buildEnv ν (k + 1) (m + 1) (envCons (ν k) ρ)
          (wkN (n := n + 1) (m + 1) j.succ) = ρ j := by
      simpa [envCons] using
        (buildEnv_wkN_apply ν (k + 1) (m + 1) (envCons (ν k) ρ) j.succ)
    have hlookup' :
        envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))
          (wk (wkN (n := n + 1) m j.succ)) = ρ j := by
      simpa [buildEnv, wkN, envCons, Nat.add_assoc] using hlookup
    have hvar :
        quoteTmWith ν (k + m + 2)
          (buildEnv ν (k + 1) (m + 1) (envCons (ν k) ρ))
          (.var (wkN (n := n + 1) (m + 1) j.succ))
        = .fvar (ρ j) := by
      simp [quoteTmWith, hlookup']
    have hfuture : ρ j ≠ ν (k + m + 1) := hcompat.2 j (k + m + 1) (by omega)
    calc
      inst0BinderBodyClosedTarget ν m k ρ a (.var (wkN (n := n + 1) (m + 1) j.succ))
          =
        applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν (k + m) ρ a))
          (closeRangeAt 1 ν (k + 1) m (.fvar (ρ j))) := by
            unfold inst0BinderBodyClosedTarget
            rw [hvar]
            simp [closeFVar, hfuture]
      _ =
        applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν (k + m) ρ a))
          (.fvar (ρ j)) := by
            rw [hclose]
      _ = .fvar (ρ j) := by
            rw [applySubst, SubstEnv.find_extend_ne hne.symm]
            simp [SubstEnv.find, SubstEnv.empty]
  unfold inst0BinderBodyTargetEq
  rw [hL, hR]

theorem inst0BinderBodyClosedLhs_wkN_zero
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ)
    (m : Nat) (a : PureTm n) :
    inst0BinderBodyClosedLhs ν m k ρ a (.var (wkN (n := n + 1) (m + 1) 0))
      = quoteTmWith ν (k + m + 1) ρ a := by
  have hrename :
      liftSubN (m + 1) (subst0 a) (wkN (n := n + 1) (m + 1) 0)
        = renameWkN (m + 1) a := by
    simpa using
      (liftSubN_wkN_apply (m := m + 1) (σ := subst0 a) (i := (0 : Fin (n + 1))))
  calc
    inst0BinderBodyClosedLhs ν m k ρ a (.var (wkN (n := n + 1) (m + 1) 0))
        =
      closeRangeAt 1 ν k m
        (closeFVar 0 (ν (k + m))
          (quoteTmWith ν (k + m + 1) (buildEnv ν k (m + 1) ρ)
            (liftSubN (m + 1) (subst0 a) (wkN (n := n + 1) (m + 1) 0)))) := by
              simp [inst0BinderBodyClosedLhs]
    _ =
      closeRangeAt 1 ν k m
        (closeFVar 0 (ν (k + m))
          (quoteTmWith ν (k + m + 1) (buildEnv ν k (m + 1) ρ)
            (renameWkN (m + 1) a))) := by
              rw [hrename]
    _ =
      closeRangeAt 1 ν k m
        (quoteTmWith ν (k + m + 1) (buildEnv ν k m ρ) (renameWkN m a)) := by
          rw [closeFVar_quoteTmWith_renameWkN_buildEnv_head hcompat]
    _ = quoteTmWith ν (k + m + 1) ρ a := by
          rw [closeRangeAt_quoteTmWith_renameWkN_buildEnv_any hcompat]

theorem inst0BinderBodyClosedTarget_wkN_zero
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ)
    (m : Nat) (a : PureTm n) :
    inst0BinderBodyClosedTarget ν m k ρ a (.var (wkN (n := n + 1) (m + 1) 0))
      = quoteTmWith ν (k + m) ρ a := by
  have hlookup :
      buildEnv ν (k + 1) (m + 1) (envCons (ν k) ρ)
        (wkN (n := n + 1) (m + 1) 0) = ν k := by
    simpa [envCons] using
      (buildEnv_wkN_apply ν (k + 1) (m + 1) (envCons (ν k) ρ) (0 : Fin (n + 1)))
  have hlookup' :
      envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))
        (wk (wkN (n := n + 1) m 0)) = ν k := by
    simpa [buildEnv, wkN, envCons, Nat.add_assoc] using hlookup
  have hvar :
      quoteTmWith ν (k + m + 2)
        (buildEnv ν (k + 1) (m + 1) (envCons (ν k) ρ))
        (.var (wkN (n := n + 1) (m + 1) 0))
      = .fvar (ν k) := by
    simp [quoteTmWith, hlookup']
  have hfuture : ν k ≠ ν (k + m + 1) := by
    intro hEq
    have : k = k + m + 1 := hcompat.1 hEq
    omega
  have hclose :
      closeRangeAt 1 ν (k + 1) m (.fvar (ν k)) = .fvar (ν k) := by
    apply closeRangeAt_fvar_of_ne
    intro r hr hEq
    have : k = k + 1 + r := hcompat.1 hEq
    omega
  calc
    inst0BinderBodyClosedTarget ν m k ρ a (.var (wkN (n := n + 1) (m + 1) 0))
        =
      applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν (k + m) ρ a))
        (closeRangeAt 1 ν (k + 1) m (.fvar (ν k))) := by
          unfold inst0BinderBodyClosedTarget
          rw [hvar]
          simp [closeFVar, hfuture]
    _ =
      applySubst (SubstEnv.extend SubstEnv.empty (ν k) (quoteTmWith ν (k + m) ρ a))
        (.fvar (ν k)) := by
          rw [hclose]
    _ = quoteTmWith ν (k + m) ρ a := by
          rw [applySubst, SubstEnv.find_extend_eq]

theorem inst0BinderBodyTargetEq_wkN_zero_of
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ)
    (m : Nat) (a : PureTm n)
    (hstep : quoteTmWith ν (k + m + 1) ρ a = quoteTmWith ν (k + m) ρ a) :
    inst0BinderBodyTargetEq ν m k ρ a (.var (wkN (n := n + 1) (m + 1) 0)) := by
  unfold inst0BinderBodyTargetEq
  rw [inst0BinderBodyClosedLhs_wkN_zero hcompat m a,
    inst0BinderBodyClosedTarget_wkN_zero hcompat m a]
  exact hstep

theorem inst0BinderBodyTargetEq_wkN_zero
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ)
    (m : Nat) (a : PureTm n) :
    inst0BinderBodyTargetEq ν m k ρ a (.var (wkN (n := n + 1) (m + 1) 0)) := by
  apply inst0BinderBodyTargetEq_wkN_zero_of hcompat m a
  exact quoteTmWith_depth_indep_staging ν (k + m + 1) (k + m) ρ a
    (quoteCompat_mono hcompat (j := k + m + 1) (by omega))
    (quoteCompat_mono hcompat (j := k + m) (by omega))

@[simp] theorem succ_wkN_zero_eq_wkN_zero
    (m : Nat) :
    Fin.succ (wkN (n := n + 1) m 0) = wkN (n := n + 1) (m + 1) 0 := by
  apply Fin.ext
  simp [wk, wkN_val]

@[simp] theorem succ_wkN_succ_eq_wkN_succ
    (m : Nat) (j : Fin n) :
    Fin.succ (wkN (n := n + 1) m j.succ) = wkN (n := n + 1) (m + 1) j.succ := by
  apply Fin.ext
  simp [wk, wkN_val, Nat.add_assoc]

theorem fin_body_cases
    (m : Nat) (i : Fin (((n + 1) + m) + 1)) :
    i = 0 ∨
      (∃ j : Fin m, i = Fin.succ (prefixIdx (n + 1) j)) ∨
      i = wkN (n := n + 1) (m + 1) 0 ∨
      (∃ j : Fin n, i = wkN (n := n + 1) (m + 1) j.succ) := by
  cases i using Fin.cases with
  | zero =>
      exact Or.inl rfl
  | succ i =>
      rcases fin_prefix_or_wkN (n := n) m i with hprefix | hwk
      · right
        left
        rcases hprefix with ⟨j, rfl⟩
        exact ⟨j, rfl⟩
      · rcases hwk with ⟨j, rfl⟩
        cases j using Fin.cases with
        | zero =>
            right
            right
            left
            simp
        | succ j =>
            right
            right
            right
            exact ⟨j, by simp⟩

theorem inst0BinderBodyTargetEqDistinct_var
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ)
    (m : Nat) (a : PureTm n) (i : Fin (((n + 1) + m) + 1)) :
    inst0BinderBodyTargetEqDistinct ν m k ρ a (.var i) := by
  rcases fin_body_cases (n := n) m i with rfl | hprefix | hwk0 | hwk
  · exact inst0BinderBodyTargetEqDistinct_zero ν m k ρ a
  · rcases hprefix with ⟨j, rfl⟩
    exact inst0BinderBodyTargetEqDistinct_prefix_succ hcompat.1 m k ρ a j
  · rw [hwk0]
    exact inst0BinderBodyTargetEqDistinct_wkN_zero hcompat m a
  · rcases hwk with ⟨j, rfl⟩
    exact inst0BinderBodyTargetEqDistinct_wkN_succ hcompat m a j

theorem inst0BinderBodyTargetEq_var
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ)
    (m : Nat) (a : PureTm n) (i : Fin (((n + 1) + m) + 1)) :
    inst0BinderBodyTargetEq ν m k ρ a (.var i) := by
  rcases fin_body_cases (n := n) m i with rfl | hprefix | hwk0 | hwk
  · exact inst0BinderBodyTargetEq_zero ν m k ρ a
  · rcases hprefix with ⟨j, rfl⟩
    exact inst0BinderBodyTargetEq_prefix_succ hcompat.1 m k ρ a j
  · rw [hwk0]
    exact inst0BinderBodyTargetEq_wkN_zero hcompat m a
  · rcases hwk with ⟨j, rfl⟩
    exact inst0BinderBodyTargetEq_wkN_succ hcompat m a j

theorem inst0BinderBodyTargetEq_u0
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) :
    inst0BinderBodyTargetEq ν m k ρ a .u0 := by
  unfold inst0BinderBodyTargetEq inst0BinderBodyClosedLhs inst0BinderBodyClosedTarget
  calc
    closeRangeAt 1 ν k m
        (closeFVar 0 (ν (k + m))
          (quoteTmWith ν (k + m + 1) (buildEnv ν k (m + 1) ρ)
            (subst (liftSubN (m + 1) (subst0 a)) PureTm.u0)))
        = Mettapedia.Languages.MeTTa.Pure.Core.u0 := by
          simpa [quoteTmWith, subst, buildEnv_succ, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.u0] using
            (closeRangeAt_u0 1 ν k m)
    _ = applySubst (SubstEnv.empty.extend (ν k) (quoteTmWith ν (k + m) ρ a))
          Mettapedia.Languages.MeTTa.Pure.Core.u0 := by
          simp [Mettapedia.Languages.MeTTa.Pure.Core.u0, applySubst]
    _ = applySubst (SubstEnv.empty.extend (ν k) (quoteTmWith ν (k + m) ρ a))
          (closeRangeAt 1 ν (k + 1) m
            (closeFVar 0 (ν (k + m + 1))
              (quoteTmWith ν (k + m + 2) (buildEnv ν (k + 1) (m + 1) (envCons (ν k) ρ))
                PureTm.u0))) := by
          simpa [quoteTmWith, subst, buildEnv_succ, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.u0] using
            (congrArg
              (applySubst (SubstEnv.empty.extend (ν k) (quoteTmWith ν (k + m) ρ a)))
              (closeRangeAt_u0 1 ν (k + 1) m)).symm

theorem inst0BinderBodyTargetEq_u1
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) :
    inst0BinderBodyTargetEq ν m k ρ a .u1 := by
  unfold inst0BinderBodyTargetEq inst0BinderBodyClosedLhs inst0BinderBodyClosedTarget
  calc
    closeRangeAt 1 ν k m
        (closeFVar 0 (ν (k + m))
          (quoteTmWith ν (k + m + 1) (buildEnv ν k (m + 1) ρ)
            (subst (liftSubN (m + 1) (subst0 a)) PureTm.u1)))
        = Mettapedia.Languages.MeTTa.Pure.Core.u1 := by
          simpa [quoteTmWith, subst, buildEnv_succ, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.u1] using
            (closeRangeAt_u1 1 ν k m)
    _ = applySubst (SubstEnv.empty.extend (ν k) (quoteTmWith ν (k + m) ρ a))
          Mettapedia.Languages.MeTTa.Pure.Core.u1 := by
          simp [Mettapedia.Languages.MeTTa.Pure.Core.u1, applySubst]
    _ = applySubst (SubstEnv.empty.extend (ν k) (quoteTmWith ν (k + m) ρ a))
          (closeRangeAt 1 ν (k + 1) m
            (closeFVar 0 (ν (k + m + 1))
              (quoteTmWith ν (k + m + 2) (buildEnv ν (k + 1) (m + 1) (envCons (ν k) ρ))
                PureTm.u1))) := by
          simpa [quoteTmWith, subst, buildEnv_succ, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.u1] using
            (congrArg
              (applySubst (SubstEnv.empty.extend (ν k) (quoteTmWith ν (k + m) ρ a)))
              (closeRangeAt_u1 1 ν (k + 1) m)).symm

theorem inst0BinderBodyTargetEqDistinct_u0
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) :
    inst0BinderBodyTargetEqDistinct ν m k ρ a .u0 := by
  unfold inst0BinderBodyTargetEqDistinct inst0BinderBodyClosedLhsDistinct inst0BinderBodyClosedTargetDistinct
  calc
    closeAmbient 1 ν k m
        (closeFVar 0 (ν (k + m))
          (quoteTmWith ν (k + m + 1) (buildEnv ν k (m + 1) ρ)
            (subst (liftSubN (m + 1) (subst0 a)) PureTm.u0)))
        = Mettapedia.Languages.MeTTa.Pure.Core.u0 := by
          simpa [quoteTmWith, subst, buildEnv_succ, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.u0] using
            (closeAmbient_u0 1 ν k m)
    _ = applySubst (SubstEnv.empty.extend (ν k) (quoteTmWith ν (k + m) ρ a))
          Mettapedia.Languages.MeTTa.Pure.Core.u0 := by
          simp [Mettapedia.Languages.MeTTa.Pure.Core.u0, applySubst]
    _ = applySubst (SubstEnv.empty.extend (ν k) (quoteTmWith ν (k + m) ρ a))
          (closeAmbient 1 ν (k + 1) m
            (closeFVar 0 (ν (k + m + 1))
              (quoteTmWith ν (k + m + 2) (buildEnv ν (k + 1) (m + 1) (envCons (ν k) ρ))
                PureTm.u0))) := by
          simpa [quoteTmWith, subst, buildEnv_succ, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.u0] using
            (congrArg
              (applySubst (SubstEnv.empty.extend (ν k) (quoteTmWith ν (k + m) ρ a)))
              (closeAmbient_u0 1 ν (k + 1) m)).symm

theorem inst0BinderBodyTargetEqDistinct_u1
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) :
    inst0BinderBodyTargetEqDistinct ν m k ρ a .u1 := by
  unfold inst0BinderBodyTargetEqDistinct inst0BinderBodyClosedLhsDistinct inst0BinderBodyClosedTargetDistinct
  calc
    closeAmbient 1 ν k m
        (closeFVar 0 (ν (k + m))
          (quoteTmWith ν (k + m + 1) (buildEnv ν k (m + 1) ρ)
            (subst (liftSubN (m + 1) (subst0 a)) PureTm.u1)))
        = Mettapedia.Languages.MeTTa.Pure.Core.u1 := by
          simpa [quoteTmWith, subst, buildEnv_succ, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.u1] using
            (closeAmbient_u1 1 ν k m)
    _ = applySubst (SubstEnv.empty.extend (ν k) (quoteTmWith ν (k + m) ρ a))
          Mettapedia.Languages.MeTTa.Pure.Core.u1 := by
          simp [Mettapedia.Languages.MeTTa.Pure.Core.u1, applySubst]
    _ = applySubst (SubstEnv.empty.extend (ν k) (quoteTmWith ν (k + m) ρ a))
          (closeAmbient 1 ν (k + 1) m
            (closeFVar 0 (ν (k + m + 1))
              (quoteTmWith ν (k + m + 2) (buildEnv ν (k + 1) (m + 1) (envCons (ν k) ρ))
                PureTm.u1))) := by
          simpa [quoteTmWith, subst, buildEnv_succ, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.u1] using
            (congrArg
              (applySubst (SubstEnv.empty.extend (ν k) (quoteTmWith ν (k + m) ρ a)))
              (closeAmbient_u1 1 ν (k + 1) m)).symm

theorem inst0BinderBodyClosedLhs_app_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (f b : PureTm (((n + 1) + m) + 1)) :
    inst0BinderBodyClosedLhs ν m k ρ a (.app f b)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkApp
      (inst0BinderBodyClosedLhs ν m k ρ a f)
      (inst0BinderBodyClosedLhs ν m k ρ a b) := by
  unfold inst0BinderBodyClosedLhs
  simp [quoteTmWith, subst, buildEnv_succ, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkApp]
  simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkApp] using
    closeRangeAt_mkApp 1 ν k m
      (closeFVar 0 (ν (k + m))
        (quoteTmWith ν (k + m + 1) (envCons (ν (k + m)) (buildEnv ν k m ρ))
          (subst (liftSub (liftSubN m (subst0 a))) f)))
      (closeFVar 0 (ν (k + m))
        (quoteTmWith ν (k + m + 1) (envCons (ν (k + m)) (buildEnv ν k m ρ))
          (subst (liftSub (liftSubN m (subst0 a))) b)))

theorem inst0BinderBodyClosedTarget_app_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (f b : PureTm (((n + 1) + m) + 1)) :
    inst0BinderBodyClosedTarget ν m k ρ a (.app f b)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkApp
      (inst0BinderBodyClosedTarget ν m k ρ a f)
      (inst0BinderBodyClosedTarget ν m k ρ a b) := by
  unfold inst0BinderBodyClosedTarget
  simp [quoteTmWith, buildEnv_succ, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkApp]
  rw [show closeRangeAt 1 ν (k + 1) m
      (Pattern.apply "App"
        [closeFVar 0 (ν (k + m + 1))
            (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) f),
          closeFVar 0 (ν (k + m + 1))
            (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) b)])
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkApp
      (closeRangeAt 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) f)))
      (closeRangeAt 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) b))) by
        simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkApp] using
          closeRangeAt_mkApp 1 ν (k + 1) m
            (closeFVar 0 (ν (k + m + 1))
              (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) f))
            (closeFVar 0 (ν (k + m + 1))
              (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) b))]
  simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkApp] using
    applySubst_mkApp
      (SubstEnv.empty.extend (ν k) (quoteTmWith ν (k + m) ρ a))
      (closeRangeAt 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2)
            (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) f)))
      (closeRangeAt 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2)
            (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) b)))

theorem inst0BinderBodyTargetEq_app_of
    {ν : Nat → String} {m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    {f b : PureTm (((n + 1) + m) + 1)}
    (hf : inst0BinderBodyTargetEq ν m k ρ a f)
    (hb : inst0BinderBodyTargetEq ν m k ρ a b) :
    inst0BinderBodyTargetEq ν m k ρ a (.app f b) := by
  unfold inst0BinderBodyTargetEq at hf hb ⊢
  rw [inst0BinderBodyClosedLhs_app_expand, inst0BinderBodyClosedTarget_app_expand]
  simpa using congrArg₂ Mettapedia.Languages.MeTTa.Pure.Core.mkApp hf hb

theorem inst0BinderBodyClosedLhsDistinct_app_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (f b : PureTm (((n + 1) + m) + 1)) :
    inst0BinderBodyClosedLhsDistinct ν m k ρ a (.app f b)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkApp
      (inst0BinderBodyClosedLhsDistinct ν m k ρ a f)
      (inst0BinderBodyClosedLhsDistinct ν m k ρ a b) := by
  unfold inst0BinderBodyClosedLhsDistinct
  simp [quoteTmWith, subst, buildEnv_succ, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkApp]
  simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkApp] using
    closeAmbient_mkApp 1 ν k m
      (closeFVar 0 (ν (k + m))
        (quoteTmWith ν (k + m + 1) (envCons (ν (k + m)) (buildEnv ν k m ρ))
          (subst (liftSub (liftSubN m (subst0 a))) f)))
      (closeFVar 0 (ν (k + m))
        (quoteTmWith ν (k + m + 1) (envCons (ν (k + m)) (buildEnv ν k m ρ))
          (subst (liftSub (liftSubN m (subst0 a))) b)))

theorem inst0BinderBodyClosedTargetDistinct_app_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (f b : PureTm (((n + 1) + m) + 1)) :
    inst0BinderBodyClosedTargetDistinct ν m k ρ a (.app f b)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkApp
      (inst0BinderBodyClosedTargetDistinct ν m k ρ a f)
      (inst0BinderBodyClosedTargetDistinct ν m k ρ a b) := by
  unfold inst0BinderBodyClosedTargetDistinct
  simp [quoteTmWith, buildEnv_succ, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkApp]
  rw [show closeAmbient 1 ν (k + 1) m
      (Pattern.apply "App"
        [closeFVar 0 (ν (k + m + 1))
            (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) f),
          closeFVar 0 (ν (k + m + 1))
            (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) b)])
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkApp
      (closeAmbient 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) f)))
      (closeAmbient 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) b))) by
        simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkApp] using
          closeAmbient_mkApp 1 ν (k + 1) m
            (closeFVar 0 (ν (k + m + 1))
              (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) f))
            (closeFVar 0 (ν (k + m + 1))
              (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) b))]
  simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkApp] using
    applySubst_mkApp
      (SubstEnv.empty.extend (ν k) (quoteTmWith ν (k + m) ρ a))
      (closeAmbient 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2)
            (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) f)))
      (closeAmbient 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2)
            (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) b)))

theorem inst0BinderBodyTargetEqDistinct_app_of
    {ν : Nat → String} {m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    {f b : PureTm (((n + 1) + m) + 1)}
    (hf : inst0BinderBodyTargetEqDistinct ν m k ρ a f)
    (hb : inst0BinderBodyTargetEqDistinct ν m k ρ a b) :
    inst0BinderBodyTargetEqDistinct ν m k ρ a (.app f b) := by
  unfold inst0BinderBodyTargetEqDistinct at hf hb ⊢
  rw [inst0BinderBodyClosedLhsDistinct_app_expand, inst0BinderBodyClosedTargetDistinct_app_expand]
  simpa using congrArg₂ Mettapedia.Languages.MeTTa.Pure.Core.mkApp hf hb

theorem inst0BinderBodyClosedLhs_id_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (A a₁ b₁ : PureTm (((n + 1) + m) + 1)) :
    inst0BinderBodyClosedLhs ν m k ρ a (.id A a₁ b₁)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkId
      (inst0BinderBodyClosedLhs ν m k ρ a A)
      (inst0BinderBodyClosedLhs ν m k ρ a a₁)
      (inst0BinderBodyClosedLhs ν m k ρ a b₁) := by
  unfold inst0BinderBodyClosedLhs
  simp [quoteTmWith, subst, buildEnv_succ, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkId]
  simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkId] using
    closeRangeAt_mkId 1 ν k m
      (closeFVar 0 (ν (k + m))
        (quoteTmWith ν (k + m + 1) (envCons (ν (k + m)) (buildEnv ν k m ρ))
          (subst (liftSub (liftSubN m (subst0 a))) A)))
      (closeFVar 0 (ν (k + m))
        (quoteTmWith ν (k + m + 1) (envCons (ν (k + m)) (buildEnv ν k m ρ))
          (subst (liftSub (liftSubN m (subst0 a))) a₁)))
      (closeFVar 0 (ν (k + m))
        (quoteTmWith ν (k + m + 1) (envCons (ν (k + m)) (buildEnv ν k m ρ))
          (subst (liftSub (liftSubN m (subst0 a))) b₁)))

theorem inst0BinderBodyClosedTarget_id_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (A a₁ b₁ : PureTm (((n + 1) + m) + 1)) :
    inst0BinderBodyClosedTarget ν m k ρ a (.id A a₁ b₁)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkId
      (inst0BinderBodyClosedTarget ν m k ρ a A)
      (inst0BinderBodyClosedTarget ν m k ρ a a₁)
      (inst0BinderBodyClosedTarget ν m k ρ a b₁) := by
  unfold inst0BinderBodyClosedTarget
  simp [quoteTmWith, buildEnv_succ, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkId]
  rw [show closeRangeAt 1 ν (k + 1) m
      (Pattern.apply "Id"
        [closeFVar 0 (ν (k + m + 1))
            (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) A),
          closeFVar 0 (ν (k + m + 1))
            (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) a₁),
          closeFVar 0 (ν (k + m + 1))
            (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) b₁)])
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkId
      (closeRangeAt 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) A)))
      (closeRangeAt 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) a₁)))
      (closeRangeAt 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) b₁))) by
        simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkId] using
          closeRangeAt_mkId 1 ν (k + 1) m
            (closeFVar 0 (ν (k + m + 1))
              (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) A))
            (closeFVar 0 (ν (k + m + 1))
              (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) a₁))
            (closeFVar 0 (ν (k + m + 1))
              (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) b₁))]
  simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkId] using
    applySubst_mkId
      (SubstEnv.empty.extend (ν k) (quoteTmWith ν (k + m) ρ a))
      (closeRangeAt 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2)
            (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) A)))
      (closeRangeAt 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2)
            (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) a₁)))
      (closeRangeAt 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2)
            (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) b₁)))

theorem inst0BinderBodyTargetEq_id_of
    {ν : Nat → String} {m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    {A a₁ b₁ : PureTm (((n + 1) + m) + 1)}
    (hA : inst0BinderBodyTargetEq ν m k ρ a A)
    (ha₁ : inst0BinderBodyTargetEq ν m k ρ a a₁)
    (hb₁ : inst0BinderBodyTargetEq ν m k ρ a b₁) :
    inst0BinderBodyTargetEq ν m k ρ a (.id A a₁ b₁) := by
  unfold inst0BinderBodyTargetEq at hA ha₁ hb₁ ⊢
  rw [inst0BinderBodyClosedLhs_id_expand, inst0BinderBodyClosedTarget_id_expand]
  rw [hA, ha₁, hb₁]

theorem inst0BinderBodyClosedLhs_pair_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (p q : PureTm (((n + 1) + m) + 1)) :
    inst0BinderBodyClosedLhs ν m k ρ a (.pair p q)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkPair
      (inst0BinderBodyClosedLhs ν m k ρ a p)
      (inst0BinderBodyClosedLhs ν m k ρ a q) := by
  unfold inst0BinderBodyClosedLhs
  simp [quoteTmWith, subst, buildEnv_succ, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkPair]
  simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkPair] using
    closeRangeAt_mkPair 1 ν k m
      (closeFVar 0 (ν (k + m))
        (quoteTmWith ν (k + m + 1) (envCons (ν (k + m)) (buildEnv ν k m ρ))
          (subst (liftSub (liftSubN m (subst0 a))) p)))
      (closeFVar 0 (ν (k + m))
        (quoteTmWith ν (k + m + 1) (envCons (ν (k + m)) (buildEnv ν k m ρ))
          (subst (liftSub (liftSubN m (subst0 a))) q)))

theorem inst0BinderBodyClosedTarget_pair_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (p q : PureTm (((n + 1) + m) + 1)) :
    inst0BinderBodyClosedTarget ν m k ρ a (.pair p q)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkPair
      (inst0BinderBodyClosedTarget ν m k ρ a p)
      (inst0BinderBodyClosedTarget ν m k ρ a q) := by
  unfold inst0BinderBodyClosedTarget
  simp [quoteTmWith, buildEnv_succ, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkPair]
  rw [show closeRangeAt 1 ν (k + 1) m
      (Pattern.apply "Pair"
        [closeFVar 0 (ν (k + m + 1))
            (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) p),
          closeFVar 0 (ν (k + m + 1))
            (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) q)])
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkPair
      (closeRangeAt 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) p)))
      (closeRangeAt 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) q))) by
        simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkPair] using
          closeRangeAt_mkPair 1 ν (k + 1) m
            (closeFVar 0 (ν (k + m + 1))
              (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) p))
            (closeFVar 0 (ν (k + m + 1))
              (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) q))]
  simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkPair] using
    applySubst_mkPair
      (SubstEnv.empty.extend (ν k) (quoteTmWith ν (k + m) ρ a))
      (closeRangeAt 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2)
            (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) p)))
      (closeRangeAt 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2)
            (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) q)))

theorem inst0BinderBodyTargetEq_pair_of
    {ν : Nat → String} {m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    {p q : PureTm (((n + 1) + m) + 1)}
    (hp : inst0BinderBodyTargetEq ν m k ρ a p)
    (hq : inst0BinderBodyTargetEq ν m k ρ a q) :
    inst0BinderBodyTargetEq ν m k ρ a (.pair p q) := by
  unfold inst0BinderBodyTargetEq at hp hq ⊢
  rw [inst0BinderBodyClosedLhs_pair_expand, inst0BinderBodyClosedTarget_pair_expand]
  simpa using congrArg₂ Mettapedia.Languages.MeTTa.Pure.Core.mkPair hp hq

theorem inst0BinderBodyClosedLhs_fst_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (p : PureTm (((n + 1) + m) + 1)) :
    inst0BinderBodyClosedLhs ν m k ρ a (.fst p)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkFst
      (inst0BinderBodyClosedLhs ν m k ρ a p) := by
  unfold inst0BinderBodyClosedLhs
  simp [quoteTmWith, subst, buildEnv_succ, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkFst]
  simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkFst] using
    closeRangeAt_mkFst 1 ν k m
      (closeFVar 0 (ν (k + m))
        (quoteTmWith ν (k + m + 1) (envCons (ν (k + m)) (buildEnv ν k m ρ))
          (subst (liftSub (liftSubN m (subst0 a))) p)))

theorem inst0BinderBodyClosedTarget_fst_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (p : PureTm (((n + 1) + m) + 1)) :
    inst0BinderBodyClosedTarget ν m k ρ a (.fst p)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkFst
      (inst0BinderBodyClosedTarget ν m k ρ a p) := by
  unfold inst0BinderBodyClosedTarget
  simp [quoteTmWith, buildEnv_succ, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkFst]
  rw [show closeRangeAt 1 ν (k + 1) m
      (Pattern.apply "Fst"
        [closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) p)])
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkFst
      (closeRangeAt 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) p))) by
        simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkFst] using
          closeRangeAt_mkFst 1 ν (k + 1) m
            (closeFVar 0 (ν (k + m + 1))
              (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) p))]
  simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkFst] using
    applySubst_mkFst
      (SubstEnv.empty.extend (ν k) (quoteTmWith ν (k + m) ρ a))
      (closeRangeAt 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2)
            (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) p)))

theorem inst0BinderBodyTargetEq_fst_of
    {ν : Nat → String} {m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    {p : PureTm (((n + 1) + m) + 1)}
    (hp : inst0BinderBodyTargetEq ν m k ρ a p) :
    inst0BinderBodyTargetEq ν m k ρ a (.fst p) := by
  unfold inst0BinderBodyTargetEq at hp ⊢
  rw [inst0BinderBodyClosedLhs_fst_expand, inst0BinderBodyClosedTarget_fst_expand]
  simpa using congrArg Mettapedia.Languages.MeTTa.Pure.Core.mkFst hp

theorem inst0BinderBodyClosedLhs_snd_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (p : PureTm (((n + 1) + m) + 1)) :
    inst0BinderBodyClosedLhs ν m k ρ a (.snd p)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkSnd
      (inst0BinderBodyClosedLhs ν m k ρ a p) := by
  unfold inst0BinderBodyClosedLhs
  simp [quoteTmWith, subst, buildEnv_succ, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkSnd]
  simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkSnd] using
    closeRangeAt_mkSnd 1 ν k m
      (closeFVar 0 (ν (k + m))
        (quoteTmWith ν (k + m + 1) (envCons (ν (k + m)) (buildEnv ν k m ρ))
          (subst (liftSub (liftSubN m (subst0 a))) p)))

theorem inst0BinderBodyClosedTarget_snd_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (p : PureTm (((n + 1) + m) + 1)) :
    inst0BinderBodyClosedTarget ν m k ρ a (.snd p)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkSnd
      (inst0BinderBodyClosedTarget ν m k ρ a p) := by
  unfold inst0BinderBodyClosedTarget
  simp [quoteTmWith, buildEnv_succ, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkSnd]
  rw [show closeRangeAt 1 ν (k + 1) m
      (Pattern.apply "Snd"
        [closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) p)])
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkSnd
      (closeRangeAt 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) p))) by
        simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkSnd] using
          closeRangeAt_mkSnd 1 ν (k + 1) m
            (closeFVar 0 (ν (k + m + 1))
              (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) p))]
  simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkSnd] using
    applySubst_mkSnd
      (SubstEnv.empty.extend (ν k) (quoteTmWith ν (k + m) ρ a))
      (closeRangeAt 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2)
            (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) p)))

theorem inst0BinderBodyTargetEq_snd_of
    {ν : Nat → String} {m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    {p : PureTm (((n + 1) + m) + 1)}
    (hp : inst0BinderBodyTargetEq ν m k ρ a p) :
    inst0BinderBodyTargetEq ν m k ρ a (.snd p) := by
  unfold inst0BinderBodyTargetEq at hp ⊢
  rw [inst0BinderBodyClosedLhs_snd_expand, inst0BinderBodyClosedTarget_snd_expand]
  simpa using congrArg Mettapedia.Languages.MeTTa.Pure.Core.mkSnd hp

theorem inst0BinderBodyClosedLhs_refl_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (p : PureTm (((n + 1) + m) + 1)) :
    inst0BinderBodyClosedLhs ν m k ρ a (.refl p)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkRefl
      (inst0BinderBodyClosedLhs ν m k ρ a p) := by
  unfold inst0BinderBodyClosedLhs
  simp [quoteTmWith, subst, buildEnv_succ, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkRefl]
  simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkRefl] using
    closeRangeAt_mkRefl 1 ν k m
      (closeFVar 0 (ν (k + m))
        (quoteTmWith ν (k + m + 1) (envCons (ν (k + m)) (buildEnv ν k m ρ))
          (subst (liftSub (liftSubN m (subst0 a))) p)))

theorem inst0BinderBodyClosedTarget_refl_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (p : PureTm (((n + 1) + m) + 1)) :
    inst0BinderBodyClosedTarget ν m k ρ a (.refl p)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkRefl
      (inst0BinderBodyClosedTarget ν m k ρ a p) := by
  unfold inst0BinderBodyClosedTarget
  simp [quoteTmWith, buildEnv_succ, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkRefl]
  rw [show closeRangeAt 1 ν (k + 1) m
      (Pattern.apply "Refl"
        [closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) p)])
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkRefl
      (closeRangeAt 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) p))) by
        simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkRefl] using
          closeRangeAt_mkRefl 1 ν (k + 1) m
            (closeFVar 0 (ν (k + m + 1))
              (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) p))]
  simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkRefl] using
    applySubst_mkRefl
      (SubstEnv.empty.extend (ν k) (quoteTmWith ν (k + m) ρ a))
      (closeRangeAt 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2)
            (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) p)))

theorem inst0BinderBodyTargetEq_refl_of
    {ν : Nat → String} {m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    {p : PureTm (((n + 1) + m) + 1)}
    (hp : inst0BinderBodyTargetEq ν m k ρ a p) :
    inst0BinderBodyTargetEq ν m k ρ a (.refl p) := by
  unfold inst0BinderBodyTargetEq at hp ⊢
  rw [inst0BinderBodyClosedLhs_refl_expand, inst0BinderBodyClosedTarget_refl_expand]
  simpa using congrArg Mettapedia.Languages.MeTTa.Pure.Core.mkRefl hp

theorem inst0BinderBodyClosedLhsDistinct_id_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (A a₁ b₁ : PureTm (((n + 1) + m) + 1)) :
    inst0BinderBodyClosedLhsDistinct ν m k ρ a (.id A a₁ b₁)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkId
      (inst0BinderBodyClosedLhsDistinct ν m k ρ a A)
      (inst0BinderBodyClosedLhsDistinct ν m k ρ a a₁)
      (inst0BinderBodyClosedLhsDistinct ν m k ρ a b₁) := by
  unfold inst0BinderBodyClosedLhsDistinct
  simp [quoteTmWith, subst, buildEnv_succ, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkId]
  simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkId] using
    closeAmbient_mkId 1 ν k m
      (closeFVar 0 (ν (k + m))
        (quoteTmWith ν (k + m + 1) (envCons (ν (k + m)) (buildEnv ν k m ρ))
          (subst (liftSub (liftSubN m (subst0 a))) A)))
      (closeFVar 0 (ν (k + m))
        (quoteTmWith ν (k + m + 1) (envCons (ν (k + m)) (buildEnv ν k m ρ))
          (subst (liftSub (liftSubN m (subst0 a))) a₁)))
      (closeFVar 0 (ν (k + m))
        (quoteTmWith ν (k + m + 1) (envCons (ν (k + m)) (buildEnv ν k m ρ))
          (subst (liftSub (liftSubN m (subst0 a))) b₁)))

theorem inst0BinderBodyClosedTargetDistinct_id_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (A a₁ b₁ : PureTm (((n + 1) + m) + 1)) :
    inst0BinderBodyClosedTargetDistinct ν m k ρ a (.id A a₁ b₁)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkId
      (inst0BinderBodyClosedTargetDistinct ν m k ρ a A)
      (inst0BinderBodyClosedTargetDistinct ν m k ρ a a₁)
      (inst0BinderBodyClosedTargetDistinct ν m k ρ a b₁) := by
  unfold inst0BinderBodyClosedTargetDistinct
  simp [quoteTmWith, buildEnv_succ, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkId]
  rw [show closeAmbient 1 ν (k + 1) m
      (Pattern.apply "Id"
        [closeFVar 0 (ν (k + m + 1))
            (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) A),
          closeFVar 0 (ν (k + m + 1))
            (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) a₁),
          closeFVar 0 (ν (k + m + 1))
            (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) b₁)])
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkId
      (closeAmbient 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) A)))
      (closeAmbient 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) a₁)))
      (closeAmbient 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) b₁))) by
        simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkId] using
          closeAmbient_mkId 1 ν (k + 1) m
            (closeFVar 0 (ν (k + m + 1))
              (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) A))
            (closeFVar 0 (ν (k + m + 1))
              (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) a₁))
            (closeFVar 0 (ν (k + m + 1))
              (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) b₁))]
  simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkId] using
    applySubst_mkId
      (SubstEnv.empty.extend (ν k) (quoteTmWith ν (k + m) ρ a))
      (closeAmbient 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2)
            (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) A)))
      (closeAmbient 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2)
            (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) a₁)))
      (closeAmbient 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2)
            (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) b₁)))

theorem inst0BinderBodyTargetEqDistinct_id_of
    {ν : Nat → String} {m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    {A a₁ b₁ : PureTm (((n + 1) + m) + 1)}
    (hA : inst0BinderBodyTargetEqDistinct ν m k ρ a A)
    (ha₁ : inst0BinderBodyTargetEqDistinct ν m k ρ a a₁)
    (hb₁ : inst0BinderBodyTargetEqDistinct ν m k ρ a b₁) :
    inst0BinderBodyTargetEqDistinct ν m k ρ a (.id A a₁ b₁) := by
  unfold inst0BinderBodyTargetEqDistinct at hA ha₁ hb₁ ⊢
  rw [inst0BinderBodyClosedLhsDistinct_id_expand, inst0BinderBodyClosedTargetDistinct_id_expand]
  rw [hA, ha₁, hb₁]

theorem inst0BinderBodyClosedLhsDistinct_pair_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (p q : PureTm (((n + 1) + m) + 1)) :
    inst0BinderBodyClosedLhsDistinct ν m k ρ a (.pair p q)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkPair
      (inst0BinderBodyClosedLhsDistinct ν m k ρ a p)
      (inst0BinderBodyClosedLhsDistinct ν m k ρ a q) := by
  unfold inst0BinderBodyClosedLhsDistinct
  simp [quoteTmWith, subst, buildEnv_succ, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkPair]
  simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkPair] using
    closeAmbient_mkPair 1 ν k m
      (closeFVar 0 (ν (k + m))
        (quoteTmWith ν (k + m + 1) (envCons (ν (k + m)) (buildEnv ν k m ρ))
          (subst (liftSub (liftSubN m (subst0 a))) p)))
      (closeFVar 0 (ν (k + m))
        (quoteTmWith ν (k + m + 1) (envCons (ν (k + m)) (buildEnv ν k m ρ))
          (subst (liftSub (liftSubN m (subst0 a))) q)))

theorem inst0BinderBodyClosedTargetDistinct_pair_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (p q : PureTm (((n + 1) + m) + 1)) :
    inst0BinderBodyClosedTargetDistinct ν m k ρ a (.pair p q)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkPair
      (inst0BinderBodyClosedTargetDistinct ν m k ρ a p)
      (inst0BinderBodyClosedTargetDistinct ν m k ρ a q) := by
  unfold inst0BinderBodyClosedTargetDistinct
  simp [quoteTmWith, buildEnv_succ, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkPair]
  rw [show closeAmbient 1 ν (k + 1) m
      (Pattern.apply "Pair"
        [closeFVar 0 (ν (k + m + 1))
            (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) p),
          closeFVar 0 (ν (k + m + 1))
            (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) q)])
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkPair
      (closeAmbient 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) p)))
      (closeAmbient 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) q))) by
        simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkPair] using
          closeAmbient_mkPair 1 ν (k + 1) m
            (closeFVar 0 (ν (k + m + 1))
              (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) p))
            (closeFVar 0 (ν (k + m + 1))
              (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) q))]
  simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkPair] using
    applySubst_mkPair
      (SubstEnv.empty.extend (ν k) (quoteTmWith ν (k + m) ρ a))
      (closeAmbient 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2)
            (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) p)))
      (closeAmbient 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2)
            (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) q)))

theorem inst0BinderBodyTargetEqDistinct_pair_of
    {ν : Nat → String} {m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    {p q : PureTm (((n + 1) + m) + 1)}
    (hp : inst0BinderBodyTargetEqDistinct ν m k ρ a p)
    (hq : inst0BinderBodyTargetEqDistinct ν m k ρ a q) :
    inst0BinderBodyTargetEqDistinct ν m k ρ a (.pair p q) := by
  unfold inst0BinderBodyTargetEqDistinct at hp hq ⊢
  rw [inst0BinderBodyClosedLhsDistinct_pair_expand, inst0BinderBodyClosedTargetDistinct_pair_expand]
  simpa using congrArg₂ Mettapedia.Languages.MeTTa.Pure.Core.mkPair hp hq

theorem inst0BinderBodyClosedLhsDistinct_fst_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (p : PureTm (((n + 1) + m) + 1)) :
    inst0BinderBodyClosedLhsDistinct ν m k ρ a (.fst p)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkFst
      (inst0BinderBodyClosedLhsDistinct ν m k ρ a p) := by
  unfold inst0BinderBodyClosedLhsDistinct
  simp [quoteTmWith, subst, buildEnv_succ, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkFst]
  simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkFst] using
    closeAmbient_mkFst 1 ν k m
      (closeFVar 0 (ν (k + m))
        (quoteTmWith ν (k + m + 1) (envCons (ν (k + m)) (buildEnv ν k m ρ))
          (subst (liftSub (liftSubN m (subst0 a))) p)))

theorem inst0BinderBodyClosedTargetDistinct_fst_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (p : PureTm (((n + 1) + m) + 1)) :
    inst0BinderBodyClosedTargetDistinct ν m k ρ a (.fst p)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkFst
      (inst0BinderBodyClosedTargetDistinct ν m k ρ a p) := by
  unfold inst0BinderBodyClosedTargetDistinct
  simp [quoteTmWith, buildEnv_succ, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkFst]
  rw [show closeAmbient 1 ν (k + 1) m
      (Pattern.apply "Fst"
        [closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) p)])
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkFst
      (closeAmbient 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) p))) by
        simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkFst] using
          closeAmbient_mkFst 1 ν (k + 1) m
            (closeFVar 0 (ν (k + m + 1))
              (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) p))]
  simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkFst] using
    applySubst_mkFst
      (SubstEnv.empty.extend (ν k) (quoteTmWith ν (k + m) ρ a))
      (closeAmbient 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2)
            (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) p)))

theorem inst0BinderBodyTargetEqDistinct_fst_of
    {ν : Nat → String} {m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    {p : PureTm (((n + 1) + m) + 1)}
    (hp : inst0BinderBodyTargetEqDistinct ν m k ρ a p) :
    inst0BinderBodyTargetEqDistinct ν m k ρ a (.fst p) := by
  unfold inst0BinderBodyTargetEqDistinct at hp ⊢
  rw [inst0BinderBodyClosedLhsDistinct_fst_expand, inst0BinderBodyClosedTargetDistinct_fst_expand]
  simpa using congrArg Mettapedia.Languages.MeTTa.Pure.Core.mkFst hp

theorem inst0BinderBodyClosedLhsDistinct_snd_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (p : PureTm (((n + 1) + m) + 1)) :
    inst0BinderBodyClosedLhsDistinct ν m k ρ a (.snd p)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkSnd
      (inst0BinderBodyClosedLhsDistinct ν m k ρ a p) := by
  unfold inst0BinderBodyClosedLhsDistinct
  simp [quoteTmWith, subst, buildEnv_succ, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkSnd]
  simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkSnd] using
    closeAmbient_mkSnd 1 ν k m
      (closeFVar 0 (ν (k + m))
        (quoteTmWith ν (k + m + 1) (envCons (ν (k + m)) (buildEnv ν k m ρ))
          (subst (liftSub (liftSubN m (subst0 a))) p)))

theorem inst0BinderBodyClosedTargetDistinct_snd_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (p : PureTm (((n + 1) + m) + 1)) :
    inst0BinderBodyClosedTargetDistinct ν m k ρ a (.snd p)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkSnd
      (inst0BinderBodyClosedTargetDistinct ν m k ρ a p) := by
  unfold inst0BinderBodyClosedTargetDistinct
  simp [quoteTmWith, buildEnv_succ, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkSnd]
  rw [show closeAmbient 1 ν (k + 1) m
      (Pattern.apply "Snd"
        [closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) p)])
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkSnd
      (closeAmbient 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) p))) by
        simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkSnd] using
          closeAmbient_mkSnd 1 ν (k + 1) m
            (closeFVar 0 (ν (k + m + 1))
              (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) p))]
  simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkSnd] using
    applySubst_mkSnd
      (SubstEnv.empty.extend (ν k) (quoteTmWith ν (k + m) ρ a))
      (closeAmbient 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2)
            (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) p)))

theorem inst0BinderBodyTargetEqDistinct_snd_of
    {ν : Nat → String} {m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    {p : PureTm (((n + 1) + m) + 1)}
    (hp : inst0BinderBodyTargetEqDistinct ν m k ρ a p) :
    inst0BinderBodyTargetEqDistinct ν m k ρ a (.snd p) := by
  unfold inst0BinderBodyTargetEqDistinct at hp ⊢
  rw [inst0BinderBodyClosedLhsDistinct_snd_expand, inst0BinderBodyClosedTargetDistinct_snd_expand]
  simpa using congrArg Mettapedia.Languages.MeTTa.Pure.Core.mkSnd hp

theorem inst0BinderBodyClosedLhsDistinct_refl_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (p : PureTm (((n + 1) + m) + 1)) :
    inst0BinderBodyClosedLhsDistinct ν m k ρ a (.refl p)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkRefl
      (inst0BinderBodyClosedLhsDistinct ν m k ρ a p) := by
  unfold inst0BinderBodyClosedLhsDistinct
  simp [quoteTmWith, subst, buildEnv_succ, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkRefl]
  simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkRefl] using
    closeAmbient_mkRefl 1 ν k m
      (closeFVar 0 (ν (k + m))
        (quoteTmWith ν (k + m + 1) (envCons (ν (k + m)) (buildEnv ν k m ρ))
          (subst (liftSub (liftSubN m (subst0 a))) p)))

theorem inst0BinderBodyClosedTargetDistinct_refl_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (p : PureTm (((n + 1) + m) + 1)) :
    inst0BinderBodyClosedTargetDistinct ν m k ρ a (.refl p)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkRefl
      (inst0BinderBodyClosedTargetDistinct ν m k ρ a p) := by
  unfold inst0BinderBodyClosedTargetDistinct
  simp [quoteTmWith, buildEnv_succ, closeFVar, Mettapedia.Languages.MeTTa.Pure.Core.mkRefl]
  rw [show closeAmbient 1 ν (k + 1) m
      (Pattern.apply "Refl"
        [closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) p)])
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkRefl
      (closeAmbient 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) p))) by
        simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkRefl] using
          closeAmbient_mkRefl 1 ν (k + 1) m
            (closeFVar 0 (ν (k + m + 1))
              (quoteTmWith ν (k + m + 2) (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) p))]
  simpa [Mettapedia.Languages.MeTTa.Pure.Core.mkRefl] using
    applySubst_mkRefl
      (SubstEnv.empty.extend (ν k) (quoteTmWith ν (k + m) ρ a))
      (closeAmbient 1 ν (k + 1) m
        (closeFVar 0 (ν (k + m + 1))
          (quoteTmWith ν (k + m + 2)
            (envCons (ν (k + 1 + m)) (buildEnv ν (k + 1) m (envCons (ν k) ρ))) p)))

theorem inst0BinderBodyTargetEqDistinct_refl_of
    {ν : Nat → String} {m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    {p : PureTm (((n + 1) + m) + 1)}
    (hp : inst0BinderBodyTargetEqDistinct ν m k ρ a p) :
    inst0BinderBodyTargetEqDistinct ν m k ρ a (.refl p) := by
  unfold inst0BinderBodyTargetEqDistinct at hp ⊢
  rw [inst0BinderBodyClosedLhsDistinct_refl_expand, inst0BinderBodyClosedTargetDistinct_refl_expand]
  simpa using congrArg Mettapedia.Languages.MeTTa.Pure.Core.mkRefl hp

theorem inst0BinderClosedLhsDistinct_lam_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (b : PureTm (((n + 1) + m) + 1)) :
    inst0BinderClosedLhsDistinct ν m k ρ a (.lam b)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkLam
      (inst0BinderBodyClosedLhsDistinct ν m k ρ a b) := by
  unfold inst0BinderClosedLhsDistinct inst0BinderBodyClosedLhsDistinct
  simp [quoteTmWith, subst, buildEnv, liftSubN, Nat.add_assoc, Nat.add_comm]
  rw [closeAmbient_mkLam]

theorem inst0BinderClosedTargetDistinct_lam_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (b : PureTm (((n + 1) + m) + 1)) :
    inst0BinderClosedTargetDistinct ν m k ρ a (.lam b)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkLam
      (inst0BinderBodyClosedTargetDistinct ν m k ρ a b) := by
  unfold inst0BinderClosedTargetDistinct inst0BinderBodyClosedTargetDistinct
  simp [quoteTmWith, buildEnv, Nat.add_assoc, Nat.add_comm]
  rw [closeAmbient_mkLam]
  simp [Mettapedia.Languages.MeTTa.Pure.Core.mkLam, applySubst, Nat.add_left_comm]

theorem inst0BinderClosedLhsDistinct_pi_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (A : PureTm ((n + 1) + m)) (B : PureTm (((n + 1) + m) + 1)) :
    inst0BinderClosedLhsDistinct ν m k ρ a (.pi A B)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkPi
      (inst0BinderClosedLhsDistinct ν m k ρ a A)
      (inst0BinderBodyClosedLhsDistinct ν m k ρ a B) := by
  unfold inst0BinderClosedLhsDistinct inst0BinderBodyClosedLhsDistinct
  simp [quoteTmWith, subst, buildEnv, liftSubN, Nat.add_assoc, Nat.add_comm]
  rw [closeAmbient_mkPi]

theorem inst0BinderClosedTargetDistinct_pi_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (A : PureTm ((n + 1) + m)) (B : PureTm (((n + 1) + m) + 1)) :
    inst0BinderClosedTargetDistinct ν m k ρ a (.pi A B)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkPi
      (inst0BinderClosedTargetDistinct ν m k ρ a A)
      (inst0BinderBodyClosedTargetDistinct ν m k ρ a B) := by
  unfold inst0BinderClosedTargetDistinct inst0BinderBodyClosedTargetDistinct
  simp [quoteTmWith, buildEnv, Nat.add_assoc, Nat.add_comm]
  rw [closeAmbient_mkPi]
  simp [Mettapedia.Languages.MeTTa.Pure.Core.mkPi, applySubst, Nat.add_left_comm]

theorem inst0BinderClosedLhsDistinct_sigma_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (A : PureTm ((n + 1) + m)) (B : PureTm (((n + 1) + m) + 1)) :
    inst0BinderClosedLhsDistinct ν m k ρ a (.sigma A B)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkSigma
      (inst0BinderClosedLhsDistinct ν m k ρ a A)
      (inst0BinderBodyClosedLhsDistinct ν m k ρ a B) := by
  unfold inst0BinderClosedLhsDistinct inst0BinderBodyClosedLhsDistinct
  simp [quoteTmWith, subst, buildEnv, liftSubN, Nat.add_assoc, Nat.add_comm]
  rw [closeAmbient_mkSigma]

theorem inst0BinderClosedTargetDistinct_sigma_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (A : PureTm ((n + 1) + m)) (B : PureTm (((n + 1) + m) + 1)) :
    inst0BinderClosedTargetDistinct ν m k ρ a (.sigma A B)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkSigma
      (inst0BinderClosedTargetDistinct ν m k ρ a A)
      (inst0BinderBodyClosedTargetDistinct ν m k ρ a B) := by
  unfold inst0BinderClosedTargetDistinct inst0BinderBodyClosedTargetDistinct
  simp [quoteTmWith, buildEnv, Nat.add_assoc, Nat.add_comm]
  rw [closeAmbient_mkSigma]
  simp [Mettapedia.Languages.MeTTa.Pure.Core.mkSigma, applySubst, Nat.add_left_comm]

theorem inst0BinderTargetEqDistinct_lam_of
    {ν : Nat → String} {m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    {b : PureTm (((n + 1) + m) + 1)}
    (hb : inst0BinderBodyTargetEqDistinct ν m k ρ a b) :
    inst0BinderTargetEqDistinct ν m k ρ a (.lam b) := by
  unfold inst0BinderTargetEqDistinct
  rw [inst0BinderClosedLhsDistinct_lam_expand, inst0BinderClosedTargetDistinct_lam_expand]
  simpa [inst0BinderBodyTargetEqDistinct, inst0BinderBodyClosedLhsDistinct,
    inst0BinderBodyClosedTargetDistinct] using
    congrArg Mettapedia.Languages.MeTTa.Pure.Core.mkLam hb

theorem inst0BinderTargetEqDistinct_pi_of
    {ν : Nat → String} {m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    {A : PureTm ((n + 1) + m)} {B : PureTm (((n + 1) + m) + 1)}
    (hA : inst0BinderTargetEqDistinct ν m k ρ a A)
    (hB : inst0BinderBodyTargetEqDistinct ν m k ρ a B) :
    inst0BinderTargetEqDistinct ν m k ρ a (.pi A B) := by
  unfold inst0BinderTargetEqDistinct at hA ⊢
  rw [inst0BinderClosedLhsDistinct_pi_expand, inst0BinderClosedTargetDistinct_pi_expand]
  simpa [inst0BinderBodyTargetEqDistinct, inst0BinderBodyClosedLhsDistinct,
    inst0BinderBodyClosedTargetDistinct] using
    congrArg₂ Mettapedia.Languages.MeTTa.Pure.Core.mkPi hA hB

theorem inst0BinderTargetEqDistinct_sigma_of
    {ν : Nat → String} {m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    {A : PureTm ((n + 1) + m)} {B : PureTm (((n + 1) + m) + 1)}
    (hA : inst0BinderTargetEqDistinct ν m k ρ a A)
    (hB : inst0BinderBodyTargetEqDistinct ν m k ρ a B) :
    inst0BinderTargetEqDistinct ν m k ρ a (.sigma A B) := by
  unfold inst0BinderTargetEqDistinct at hA ⊢
  rw [inst0BinderClosedLhsDistinct_sigma_expand, inst0BinderClosedTargetDistinct_sigma_expand]
  simpa [inst0BinderBodyTargetEqDistinct, inst0BinderBodyClosedLhsDistinct,
    inst0BinderBodyClosedTargetDistinct] using
    congrArg₂ Mettapedia.Languages.MeTTa.Pure.Core.mkSigma hA hB

theorem inst0BinderTargetEqDistinct_u0
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) :
    inst0BinderTargetEqDistinct ν m k ρ a .u0 := by
  unfold inst0BinderTargetEqDistinct inst0BinderClosedLhsDistinct inst0BinderClosedTargetDistinct
  simp [quoteTmWith, subst]

theorem inst0BinderTargetEqDistinct_u1
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) :
    inst0BinderTargetEqDistinct ν m k ρ a .u1 := by
  unfold inst0BinderTargetEqDistinct inst0BinderClosedLhsDistinct inst0BinderClosedTargetDistinct
  simp [quoteTmWith, subst]

theorem inst0BinderTargetEqDistinct_id_of
    {ν : Nat → String} {m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    {A a₁ b₁ : PureTm ((n + 1) + m)}
    (hA : inst0BinderTargetEqDistinct ν m k ρ a A)
    (ha₁ : inst0BinderTargetEqDistinct ν m k ρ a a₁)
    (hb₁ : inst0BinderTargetEqDistinct ν m k ρ a b₁) :
    inst0BinderTargetEqDistinct ν m k ρ a (.id A a₁ b₁) := by
  unfold inst0BinderTargetEqDistinct at hA ha₁ hb₁ ⊢
  simp [inst0BinderClosedLhsDistinct, inst0BinderClosedTargetDistinct, quoteTmWith, subst] at hA ha₁ hb₁ ⊢
  rw [hA, ha₁, hb₁]

theorem inst0BinderTargetEqDistinct_app_of
    {ν : Nat → String} {m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    {f b : PureTm ((n + 1) + m)}
    (hf : inst0BinderTargetEqDistinct ν m k ρ a f)
    (hb : inst0BinderTargetEqDistinct ν m k ρ a b) :
    inst0BinderTargetEqDistinct ν m k ρ a (.app f b) := by
  unfold inst0BinderTargetEqDistinct at hf hb ⊢
  simp [inst0BinderClosedLhsDistinct, inst0BinderClosedTargetDistinct, quoteTmWith, subst] at hf hb ⊢
  rw [hf, hb]

theorem inst0BinderTargetEqDistinct_pair_of
    {ν : Nat → String} {m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    {p q : PureTm ((n + 1) + m)}
    (hp : inst0BinderTargetEqDistinct ν m k ρ a p)
    (hq : inst0BinderTargetEqDistinct ν m k ρ a q) :
    inst0BinderTargetEqDistinct ν m k ρ a (.pair p q) := by
  unfold inst0BinderTargetEqDistinct at hp hq ⊢
  simp [inst0BinderClosedLhsDistinct, inst0BinderClosedTargetDistinct, quoteTmWith, subst] at hp hq ⊢
  rw [hp, hq]

theorem inst0BinderTargetEqDistinct_fst_of
    {ν : Nat → String} {m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    {p : PureTm ((n + 1) + m)}
    (hp : inst0BinderTargetEqDistinct ν m k ρ a p) :
    inst0BinderTargetEqDistinct ν m k ρ a (.fst p) := by
  unfold inst0BinderTargetEqDistinct at hp ⊢
  simp [inst0BinderClosedLhsDistinct, inst0BinderClosedTargetDistinct, quoteTmWith, subst] at hp ⊢
  rw [hp]

theorem inst0BinderTargetEqDistinct_snd_of
    {ν : Nat → String} {m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    {p : PureTm ((n + 1) + m)}
    (hp : inst0BinderTargetEqDistinct ν m k ρ a p) :
    inst0BinderTargetEqDistinct ν m k ρ a (.snd p) := by
  unfold inst0BinderTargetEqDistinct at hp ⊢
  simp [inst0BinderClosedLhsDistinct, inst0BinderClosedTargetDistinct, quoteTmWith, subst] at hp ⊢
  rw [hp]

theorem inst0BinderTargetEqDistinct_refl_of
    {ν : Nat → String} {m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    {p : PureTm ((n + 1) + m)}
    (hp : inst0BinderTargetEqDistinct ν m k ρ a p) :
    inst0BinderTargetEqDistinct ν m k ρ a (.refl p) := by
  unfold inst0BinderTargetEqDistinct at hp ⊢
  simp [inst0BinderClosedLhsDistinct, inst0BinderClosedTargetDistinct, quoteTmWith, subst] at hp ⊢
  rw [hp]

theorem inst0AmbientDistinctClosedLhs_lam_expand
    (ν : Nat → String) (e m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (b : PureTm (((n + 1) + (m + e)) + 1)) :
    inst0AmbientDistinctClosedLhs e ν m k ρ a (.lam b)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkLam
      (inst0AmbientDistinctClosedLhs (e + 1) ν m k ρ a (castAmbientBody b)) := by
  unfold inst0AmbientDistinctClosedLhs
  simp [quoteTmWith, subst, buildEnv, liftSubN, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    castAmbientBody, castPureTm]
  rw [closeAmbient_mkLam, closeAmbient_mkLam]

theorem inst0AmbientDistinctClosedTarget_lam_expand
    (ν : Nat → String) (e m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (b : PureTm (((n + 1) + (m + e)) + 1)) :
    inst0AmbientDistinctClosedTarget e ν m k ρ a (.lam b)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkLam
      (inst0AmbientDistinctClosedTarget (e + 1) ν m k ρ a (castAmbientBody b)) := by
  unfold inst0AmbientDistinctClosedTarget
  simp [quoteTmWith, buildEnv, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    castAmbientBody, castPureTm]
  rw [closeAmbient_mkLam, closeAmbient_mkLam]
  simp [Mettapedia.Languages.MeTTa.Pure.Core.mkLam, applySubst]

theorem inst0AmbientDistinctClosedLhs_pi_expand
    (ν : Nat → String) (e m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (A : PureTm ((n + 1) + (m + e))) (B : PureTm (((n + 1) + (m + e)) + 1)) :
    inst0AmbientDistinctClosedLhs e ν m k ρ a (.pi A B)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkPi
      (inst0AmbientDistinctClosedLhs e ν m k ρ a A)
      (inst0AmbientDistinctClosedLhs (e + 1) ν m k ρ a (castAmbientBody B)) := by
  unfold inst0AmbientDistinctClosedLhs
  simp [quoteTmWith, subst, buildEnv, liftSubN, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    castAmbientBody, castPureTm]
  rw [closeAmbient_mkPi, closeAmbient_mkPi]

theorem inst0AmbientDistinctClosedTarget_pi_expand
    (ν : Nat → String) (e m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (A : PureTm ((n + 1) + (m + e))) (B : PureTm (((n + 1) + (m + e)) + 1)) :
    inst0AmbientDistinctClosedTarget e ν m k ρ a (.pi A B)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkPi
      (inst0AmbientDistinctClosedTarget e ν m k ρ a A)
      (inst0AmbientDistinctClosedTarget (e + 1) ν m k ρ a (castAmbientBody B)) := by
  unfold inst0AmbientDistinctClosedTarget
  simp [quoteTmWith, buildEnv, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    castAmbientBody, castPureTm]
  rw [closeAmbient_mkPi, closeAmbient_mkPi]
  simp [Mettapedia.Languages.MeTTa.Pure.Core.mkPi, applySubst]

theorem inst0AmbientDistinctClosedLhs_sigma_expand
    (ν : Nat → String) (e m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (A : PureTm ((n + 1) + (m + e))) (B : PureTm (((n + 1) + (m + e)) + 1)) :
    inst0AmbientDistinctClosedLhs e ν m k ρ a (.sigma A B)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkSigma
      (inst0AmbientDistinctClosedLhs e ν m k ρ a A)
      (inst0AmbientDistinctClosedLhs (e + 1) ν m k ρ a (castAmbientBody B)) := by
  unfold inst0AmbientDistinctClosedLhs
  simp [quoteTmWith, subst, buildEnv, liftSubN, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    castAmbientBody, castPureTm]
  rw [closeAmbient_mkSigma, closeAmbient_mkSigma]

theorem inst0AmbientDistinctClosedTarget_sigma_expand
    (ν : Nat → String) (e m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (A : PureTm ((n + 1) + (m + e))) (B : PureTm (((n + 1) + (m + e)) + 1)) :
    inst0AmbientDistinctClosedTarget e ν m k ρ a (.sigma A B)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkSigma
      (inst0AmbientDistinctClosedTarget e ν m k ρ a A)
      (inst0AmbientDistinctClosedTarget (e + 1) ν m k ρ a (castAmbientBody B)) := by
  unfold inst0AmbientDistinctClosedTarget
  simp [quoteTmWith, buildEnv, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    castAmbientBody, castPureTm]
  rw [closeAmbient_mkSigma, closeAmbient_mkSigma]
  simp [Mettapedia.Languages.MeTTa.Pure.Core.mkSigma, applySubst]

theorem inst0AmbientDistinctTargetEq_lam_of
    {ν : Nat → String} {e m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    {b : PureTm (((n + 1) + (m + e)) + 1)}
    (hb : inst0AmbientDistinctTargetEq (e + 1) ν m k ρ a (castAmbientBody b)) :
    inst0AmbientDistinctTargetEq e ν m k ρ a (.lam b) := by
  unfold inst0AmbientDistinctTargetEq at hb ⊢
  rw [inst0AmbientDistinctClosedLhs_lam_expand, inst0AmbientDistinctClosedTarget_lam_expand]
  simpa using congrArg Mettapedia.Languages.MeTTa.Pure.Core.mkLam hb

theorem inst0AmbientDistinctTargetEq_pi_of
    {ν : Nat → String} {e m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    {A : PureTm ((n + 1) + (m + e))} {B : PureTm (((n + 1) + (m + e)) + 1)}
    (hA : inst0AmbientDistinctTargetEq e ν m k ρ a A)
    (hB : inst0AmbientDistinctTargetEq (e + 1) ν m k ρ a (castAmbientBody B)) :
    inst0AmbientDistinctTargetEq e ν m k ρ a (.pi A B) := by
  unfold inst0AmbientDistinctTargetEq at hA hB ⊢
  rw [inst0AmbientDistinctClosedLhs_pi_expand, inst0AmbientDistinctClosedTarget_pi_expand]
  simpa using congrArg₂ Mettapedia.Languages.MeTTa.Pure.Core.mkPi hA hB

theorem inst0AmbientDistinctTargetEq_sigma_of
    {ν : Nat → String} {e m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    {A : PureTm ((n + 1) + (m + e))} {B : PureTm (((n + 1) + (m + e)) + 1)}
    (hA : inst0AmbientDistinctTargetEq e ν m k ρ a A)
    (hB : inst0AmbientDistinctTargetEq (e + 1) ν m k ρ a (castAmbientBody B)) :
    inst0AmbientDistinctTargetEq e ν m k ρ a (.sigma A B) := by
  unfold inst0AmbientDistinctTargetEq at hA hB ⊢
  rw [inst0AmbientDistinctClosedLhs_sigma_expand, inst0AmbientDistinctClosedTarget_sigma_expand]
  simpa using congrArg₂ Mettapedia.Languages.MeTTa.Pure.Core.mkSigma hA hB

theorem inst0AmbientDistinctTargetEq_u0
    (ν : Nat → String) (e m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) :
    inst0AmbientDistinctTargetEq e ν m k ρ a .u0 := by
  unfold inst0AmbientDistinctTargetEq inst0AmbientDistinctClosedLhs inst0AmbientDistinctClosedTarget
  calc
    closeAmbient e ν k m
        (closeAmbient 0 ν (k + m) e
          (quoteTmWith ν (k + m + e) (buildEnv ν k (m + e) ρ)
            (subst (liftSubN (m + e) (subst0 a)) PureTm.u0)))
      = Mettapedia.Languages.MeTTa.Pure.Core.u0 := by
          rw [show closeAmbient 0 ν (k + m) e
                (quoteTmWith ν (k + m + e) (buildEnv ν k (m + e) ρ)
                  (subst (liftSubN (m + e) (subst0 a)) PureTm.u0))
                = Mettapedia.Languages.MeTTa.Pure.Core.u0 by
                  simpa [quoteTmWith, subst, buildEnv_succ, closeFVar,
                    Mettapedia.Languages.MeTTa.Pure.Core.u0] using
                    (closeAmbient_u0 0 ν (k + m) e)]
          simp [closeAmbient_u0]
    _ = applySubst (SubstEnv.empty.extend (ν k) (quoteTmWith ν (k + m) ρ a))
          Mettapedia.Languages.MeTTa.Pure.Core.u0 := by
          simp [Mettapedia.Languages.MeTTa.Pure.Core.u0, applySubst]
    _ = applySubst (SubstEnv.empty.extend (ν k) (quoteTmWith ν (k + m) ρ a))
          (closeAmbient e ν (k + 1) m
            (closeAmbient 0 ν (k + m + 1) e
              (quoteTmWith ν (k + m + e + 1)
                (buildEnv ν (k + 1) (m + e) (envCons (ν k) ρ)) PureTm.u0))) := by
          rw [show closeAmbient e ν (k + 1) m
                (closeAmbient 0 ν (k + m + 1) e
                  (quoteTmWith ν (k + m + e + 1)
                    (buildEnv ν (k + 1) (m + e) (envCons (ν k) ρ)) PureTm.u0))
                = Mettapedia.Languages.MeTTa.Pure.Core.u0 by
                  rw [show closeAmbient 0 ν (k + m + 1) e
                        (quoteTmWith ν (k + m + e + 1)
                          (buildEnv ν (k + 1) (m + e) (envCons (ν k) ρ)) PureTm.u0)
                        = Mettapedia.Languages.MeTTa.Pure.Core.u0 by
                  simpa [quoteTmWith, buildEnv_succ, closeFVar,
                    Mettapedia.Languages.MeTTa.Pure.Core.u0] using
                    (closeAmbient_u0 0 ν (k + m + 1) e)]
                  simp [closeAmbient_u0]]

theorem inst0AmbientDistinctTargetEq_u1
    (ν : Nat → String) (e m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) :
    inst0AmbientDistinctTargetEq e ν m k ρ a .u1 := by
  unfold inst0AmbientDistinctTargetEq inst0AmbientDistinctClosedLhs inst0AmbientDistinctClosedTarget
  calc
    closeAmbient e ν k m
        (closeAmbient 0 ν (k + m) e
          (quoteTmWith ν (k + m + e) (buildEnv ν k (m + e) ρ)
            (subst (liftSubN (m + e) (subst0 a)) PureTm.u1)))
      = Mettapedia.Languages.MeTTa.Pure.Core.u1 := by
          rw [show closeAmbient 0 ν (k + m) e
                (quoteTmWith ν (k + m + e) (buildEnv ν k (m + e) ρ)
                  (subst (liftSubN (m + e) (subst0 a)) PureTm.u1))
                = Mettapedia.Languages.MeTTa.Pure.Core.u1 by
                  simpa [quoteTmWith, subst, buildEnv_succ, closeFVar,
                    Mettapedia.Languages.MeTTa.Pure.Core.u1] using
                    (closeAmbient_u1 0 ν (k + m) e)]
          simp [closeAmbient_u1]
    _ = applySubst (SubstEnv.empty.extend (ν k) (quoteTmWith ν (k + m) ρ a))
          Mettapedia.Languages.MeTTa.Pure.Core.u1 := by
          simp [Mettapedia.Languages.MeTTa.Pure.Core.u1, applySubst]
    _ = applySubst (SubstEnv.empty.extend (ν k) (quoteTmWith ν (k + m) ρ a))
          (closeAmbient e ν (k + 1) m
            (closeAmbient 0 ν (k + m + 1) e
              (quoteTmWith ν (k + m + e + 1)
                (buildEnv ν (k + 1) (m + e) (envCons (ν k) ρ)) PureTm.u1))) := by
          rw [show closeAmbient e ν (k + 1) m
                (closeAmbient 0 ν (k + m + 1) e
                  (quoteTmWith ν (k + m + e + 1)
                    (buildEnv ν (k + 1) (m + e) (envCons (ν k) ρ)) PureTm.u1))
                = Mettapedia.Languages.MeTTa.Pure.Core.u1 by
                  rw [show closeAmbient 0 ν (k + m + 1) e
                        (quoteTmWith ν (k + m + e + 1)
                          (buildEnv ν (k + 1) (m + e) (envCons (ν k) ρ)) PureTm.u1)
                        = Mettapedia.Languages.MeTTa.Pure.Core.u1 by
                          simpa [quoteTmWith, buildEnv_succ, closeFVar,
                            Mettapedia.Languages.MeTTa.Pure.Core.u1] using
                            (closeAmbient_u1 0 ν (k + m + 1) e)]
                  simp [closeAmbient_u1]]

theorem inst0AmbientDistinctClosedLhs_app_expand
    (ν : Nat → String) (e m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (f b : PureTm ((n + 1) + (m + e))) :
    inst0AmbientDistinctClosedLhs e ν m k ρ a (.app f b)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkApp
      (inst0AmbientDistinctClosedLhs e ν m k ρ a f)
      (inst0AmbientDistinctClosedLhs e ν m k ρ a b) := by
  unfold inst0AmbientDistinctClosedLhs
  simp [quoteTmWith, subst, Nat.add_comm]

theorem inst0AmbientDistinctClosedTarget_app_expand
    (ν : Nat → String) (e m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (f b : PureTm ((n + 1) + (m + e))) :
    inst0AmbientDistinctClosedTarget e ν m k ρ a (.app f b)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkApp
      (inst0AmbientDistinctClosedTarget e ν m k ρ a f)
      (inst0AmbientDistinctClosedTarget e ν m k ρ a b) := by
  unfold inst0AmbientDistinctClosedTarget
  simp [quoteTmWith, Nat.add_assoc, Nat.add_comm]

theorem inst0AmbientDistinctTargetEq_app_of
    {ν : Nat → String} {e m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    {f b : PureTm ((n + 1) + (m + e))}
    (hf : inst0AmbientDistinctTargetEq e ν m k ρ a f)
    (hb : inst0AmbientDistinctTargetEq e ν m k ρ a b) :
    inst0AmbientDistinctTargetEq e ν m k ρ a (.app f b) := by
  unfold inst0AmbientDistinctTargetEq at hf hb ⊢
  rw [inst0AmbientDistinctClosedLhs_app_expand, inst0AmbientDistinctClosedTarget_app_expand]
  simpa using congrArg₂ Mettapedia.Languages.MeTTa.Pure.Core.mkApp hf hb

theorem inst0AmbientDistinctTargetEq_var
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ)
    (e m : Nat) (a : PureTm n) (i : Fin ((n + 1) + (m + e))) :
    inst0AmbientDistinctTargetEq e ν m k ρ a (.var i) := by
  rw [inst0AmbientDistinctTargetEq_total_iff _ _ _ _ _ _ hcompat]
  exact inst0BinderTargetEqDistinct_var hcompat (m + e) a i

theorem inst0AmbientDistinctTargetEq_id_of
    {ν : Nat → String} {e m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    (hcompat : QuoteCompat ν k ρ)
    {A a₁ b₁ : PureTm ((n + 1) + (m + e))}
    (hA : inst0AmbientDistinctTargetEq e ν m k ρ a A)
    (ha₁ : inst0AmbientDistinctTargetEq e ν m k ρ a a₁)
    (hb₁ : inst0AmbientDistinctTargetEq e ν m k ρ a b₁) :
    inst0AmbientDistinctTargetEq e ν m k ρ a (.id A a₁ b₁) := by
  rw [inst0AmbientDistinctTargetEq_total_iff _ _ _ _ _ _ hcompat] at hA ha₁ hb₁ ⊢
  exact inst0BinderTargetEqDistinct_id_of hA ha₁ hb₁

theorem inst0AmbientDistinctTargetEq_pair_of
    {ν : Nat → String} {e m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    (hcompat : QuoteCompat ν k ρ)
    {p q : PureTm ((n + 1) + (m + e))}
    (hp : inst0AmbientDistinctTargetEq e ν m k ρ a p)
    (hq : inst0AmbientDistinctTargetEq e ν m k ρ a q) :
    inst0AmbientDistinctTargetEq e ν m k ρ a (.pair p q) := by
  rw [inst0AmbientDistinctTargetEq_total_iff _ _ _ _ _ _ hcompat] at hp hq ⊢
  exact inst0BinderTargetEqDistinct_pair_of hp hq

theorem inst0AmbientDistinctTargetEq_fst_of
    {ν : Nat → String} {e m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    (hcompat : QuoteCompat ν k ρ)
    {p : PureTm ((n + 1) + (m + e))}
    (hp : inst0AmbientDistinctTargetEq e ν m k ρ a p) :
    inst0AmbientDistinctTargetEq e ν m k ρ a (.fst p) := by
  rw [inst0AmbientDistinctTargetEq_total_iff _ _ _ _ _ _ hcompat] at hp ⊢
  exact inst0BinderTargetEqDistinct_fst_of hp

theorem inst0AmbientDistinctTargetEq_snd_of
    {ν : Nat → String} {e m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    (hcompat : QuoteCompat ν k ρ)
    {p : PureTm ((n + 1) + (m + e))}
    (hp : inst0AmbientDistinctTargetEq e ν m k ρ a p) :
    inst0AmbientDistinctTargetEq e ν m k ρ a (.snd p) := by
  rw [inst0AmbientDistinctTargetEq_total_iff _ _ _ _ _ _ hcompat] at hp ⊢
  exact inst0BinderTargetEqDistinct_snd_of hp

theorem inst0AmbientDistinctTargetEq_refl_of
    {ν : Nat → String} {e m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    (hcompat : QuoteCompat ν k ρ)
    {p : PureTm ((n + 1) + (m + e))}
    (hp : inst0AmbientDistinctTargetEq e ν m k ρ a p) :
    inst0AmbientDistinctTargetEq e ν m k ρ a (.refl p) := by
  rw [inst0AmbientDistinctTargetEq_total_iff _ _ _ _ _ _ hcompat] at hp ⊢
  exact inst0BinderTargetEqDistinct_refl_of hp

theorem inst0AmbientDistinctTargetEq_all
    (ν : Nat → String) :
    ∀ {n : Nat} (e m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
      (t : PureTm ((n + 1) + (m + e))),
      QuoteCompat ν k ρ →
      inst0AmbientDistinctTargetEq e ν m k ρ a t
  | _, e, m, k, ρ, a, .var i, hcompat =>
      inst0AmbientDistinctTargetEq_var hcompat e m a i
  | _, e, m, k, ρ, a, .const c, _ =>
      by
        unfold inst0AmbientDistinctTargetEq inst0AmbientDistinctClosedLhs inst0AmbientDistinctClosedTarget
        have hInnerL :
            closeAmbient 0 ν (k + m) e (Pattern.apply (Lean.Name.toString c) []) =
              Pattern.apply (Lean.Name.toString c) [] := by
          simpa [quoteConst] using
            (closeAmbient_quoteConst (d := 0) (ν := ν) (k := k + m) (m := e) c)
        have hLeft :
            closeAmbient e ν k m
              (closeAmbient 0 ν (k + m) e (Pattern.apply (Lean.Name.toString c) [])) =
                Pattern.apply (Lean.Name.toString c) [] := by
          rw [hInnerL]
          simpa [quoteConst] using
            (closeAmbient_quoteConst (d := e) (ν := ν) (k := k) (m := m) c)
        have hInnerR0 :
            closeAmbient 0 ν (k + m + 1) e (Pattern.apply (Lean.Name.toString c) []) =
              Pattern.apply (Lean.Name.toString c) [] := by
          simpa [quoteConst] using
            (closeAmbient_quoteConst (d := 0) (ν := ν) (k := k + m + 1) (m := e) c)
        have hInnerR :
            closeAmbient e ν (k + 1) m
              (closeAmbient 0 ν (k + m + 1) e (Pattern.apply (Lean.Name.toString c) [])) =
                Pattern.apply (Lean.Name.toString c) [] := by
          rw [hInnerR0]
          simpa [quoteConst] using
            (closeAmbient_quoteConst (d := e) (ν := ν) (k := k + 1) (m := m) c)
        have hRightExpanded :
            closeAmbient e ν (k + 1) m
              (closeAmbient 0 ν (k + m + 1) e
                (quoteTmWith ν (k + m + e + 1)
                  (buildEnv ν (k + 1) (m + e) (envCons (ν k) ρ)) (.const c))) =
                quoteConst c := by
          simpa [quoteTmWith, quoteConst] using hInnerR
        calc
          closeAmbient e ν k m
              (closeAmbient 0 ν (k + m) e
                (quoteTmWith ν (k + m + e) (buildEnv ν k (m + e) ρ)
                  (subst (liftSubN (m + e) (subst0 a)) (.const c))))
              = quoteConst c := by
                exact hLeft
          _ = applySubst (SubstEnv.empty.extend (ν k) (quoteTmWith ν (k + m) ρ a))
                (quoteConst c) := by
                simp
          _ = applySubst (SubstEnv.empty.extend (ν k) (quoteTmWith ν (k + m) ρ a))
                (closeAmbient e ν (k + 1) m
                  (closeAmbient 0 ν (k + m + 1) e
                    (quoteTmWith ν (k + m + e + 1)
                      (buildEnv ν (k + 1) (m + e) (envCons (ν k) ρ)) (.const c)))) := by
                rw [hRightExpanded]
  | _, e, m, k, ρ, a, .u0, _ =>
      inst0AmbientDistinctTargetEq_u0 ν e m k ρ a
  | _, e, m, k, ρ, a, .u1, _ =>
      inst0AmbientDistinctTargetEq_u1 ν e m k ρ a
  | _, e, m, k, ρ, a, .id A a₁ b₁, hcompat =>
      inst0AmbientDistinctTargetEq_id_of hcompat
        (inst0AmbientDistinctTargetEq_all ν e m k ρ a A hcompat)
        (inst0AmbientDistinctTargetEq_all ν e m k ρ a a₁ hcompat)
        (inst0AmbientDistinctTargetEq_all ν e m k ρ a b₁ hcompat)
  | _, e, m, k, ρ, a, .app f b, hcompat =>
      inst0AmbientDistinctTargetEq_app_of
        (inst0AmbientDistinctTargetEq_all ν e m k ρ a f hcompat)
        (inst0AmbientDistinctTargetEq_all ν e m k ρ a b hcompat)
  | _, e, m, k, ρ, a, .pair p q, hcompat =>
      inst0AmbientDistinctTargetEq_pair_of hcompat
        (inst0AmbientDistinctTargetEq_all ν e m k ρ a p hcompat)
        (inst0AmbientDistinctTargetEq_all ν e m k ρ a q hcompat)
  | _, e, m, k, ρ, a, .fst p, hcompat =>
      inst0AmbientDistinctTargetEq_fst_of hcompat
        (inst0AmbientDistinctTargetEq_all ν e m k ρ a p hcompat)
  | _, e, m, k, ρ, a, .snd p, hcompat =>
      inst0AmbientDistinctTargetEq_snd_of hcompat
        (inst0AmbientDistinctTargetEq_all ν e m k ρ a p hcompat)
  | _, e, m, k, ρ, a, .refl p, hcompat =>
      inst0AmbientDistinctTargetEq_refl_of hcompat
        (inst0AmbientDistinctTargetEq_all ν e m k ρ a p hcompat)
  | _, e, m, k, ρ, a, .lam b, hcompat =>
      inst0AmbientDistinctTargetEq_lam_of
        (inst0AmbientDistinctTargetEq_all ν (e + 1) m k ρ a (castAmbientBody b) hcompat)
  | _, e, m, k, ρ, a, .pi A B, hcompat =>
      inst0AmbientDistinctTargetEq_pi_of
        (inst0AmbientDistinctTargetEq_all ν e m k ρ a A hcompat)
        (inst0AmbientDistinctTargetEq_all ν (e + 1) m k ρ a (castAmbientBody B) hcompat)
  | _, e, m, k, ρ, a, .sigma A B, hcompat =>
      inst0AmbientDistinctTargetEq_sigma_of
        (inst0AmbientDistinctTargetEq_all ν e m k ρ a A hcompat)
        (inst0AmbientDistinctTargetEq_all ν (e + 1) m k ρ a (castAmbientBody B) hcompat)
termination_by _ _ _ _ _ _ t _ => sizeOf t
decreasing_by
  all_goals
    simp [castAmbientBody, castPureTm]
    try omega

theorem inst0BinderTargetEq_lam_of
    {ν : Nat → String} {m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    {b : PureTm (((n + 1) + m) + 1)}
    (hb : inst0BinderBodyTargetEq ν m k ρ a b) :
    inst0BinderTargetEq ν m k ρ a (.lam b) := by
  unfold inst0BinderTargetEq
  rw [inst0BinderClosedLhs_lam_expand, inst0BinderClosedTarget_lam_expand]
  simpa [inst0BinderBodyTargetEq, inst0BinderBodyClosedLhs, inst0BinderBodyClosedTarget] using
    congrArg Mettapedia.Languages.MeTTa.Pure.Core.mkLam hb

theorem inst0BinderClosedLhs_pi_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (A : PureTm ((n + 1) + m)) (B : PureTm (((n + 1) + m) + 1)) :
    inst0BinderClosedLhs ν m k ρ a (.pi A B)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkPi
      (inst0BinderClosedLhs ν m k ρ a A)
      (inst0BinderBodyClosedLhs ν m k ρ a B) := by
  unfold inst0BinderClosedLhs inst0BinderBodyClosedLhs
  simp [quoteTmWith, subst, buildEnv, liftSubN, Nat.add_assoc, Nat.add_comm]
  rw [closeRange_eq_closeRangeAt_zero, closeRangeAt_mkPi]
  simp [closeRange_eq_closeRangeAt_zero]

theorem inst0BinderClosedTarget_pi_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (A : PureTm ((n + 1) + m)) (B : PureTm (((n + 1) + m) + 1)) :
    inst0BinderClosedTarget ν m k ρ a (.pi A B)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkPi
      (inst0BinderClosedTarget ν m k ρ a A)
      (inst0BinderBodyClosedTarget ν m k ρ a B) := by
  unfold inst0BinderClosedTarget inst0BinderBodyClosedTarget
  simp [quoteTmWith, buildEnv, Nat.add_assoc, Nat.add_comm]
  rw [closeRange_mkPi_shifted]
  simp [closeRange_eq_closeRangeAt_zero, Mettapedia.Languages.MeTTa.Pure.Core.mkPi, applySubst,
    Nat.add_left_comm]

theorem inst0BinderClosedLhs_sigma_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (A : PureTm ((n + 1) + m)) (B : PureTm (((n + 1) + m) + 1)) :
    inst0BinderClosedLhs ν m k ρ a (.sigma A B)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkSigma
      (inst0BinderClosedLhs ν m k ρ a A)
      (inst0BinderBodyClosedLhs ν m k ρ a B) := by
  unfold inst0BinderClosedLhs inst0BinderBodyClosedLhs
  simp [quoteTmWith, subst, buildEnv, liftSubN, Nat.add_assoc, Nat.add_comm]
  rw [closeRange_eq_closeRangeAt_zero, closeRangeAt_mkSigma]
  simp [closeRange_eq_closeRangeAt_zero]

theorem inst0BinderClosedTarget_sigma_expand
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n)
    (A : PureTm ((n + 1) + m)) (B : PureTm (((n + 1) + m) + 1)) :
    inst0BinderClosedTarget ν m k ρ a (.sigma A B)
      =
    Mettapedia.Languages.MeTTa.Pure.Core.mkSigma
      (inst0BinderClosedTarget ν m k ρ a A)
      (inst0BinderBodyClosedTarget ν m k ρ a B) := by
  unfold inst0BinderClosedTarget inst0BinderBodyClosedTarget
  simp [quoteTmWith, buildEnv, Nat.add_assoc, Nat.add_comm]
  rw [closeRange_mkSigma_shifted]
  simp [closeRange_eq_closeRangeAt_zero, Mettapedia.Languages.MeTTa.Pure.Core.mkSigma, applySubst,
    Nat.add_left_comm]

theorem inst0BinderTargetEq_pi_of
    {ν : Nat → String} {m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    {A : PureTm ((n + 1) + m)} {B : PureTm (((n + 1) + m) + 1)}
    (hA : inst0BinderTargetEq ν m k ρ a A)
    (hB : inst0BinderBodyTargetEq ν m k ρ a B) :
    inst0BinderTargetEq ν m k ρ a (.pi A B) := by
  unfold inst0BinderTargetEq at hA ⊢
  rw [inst0BinderClosedLhs_pi_expand, inst0BinderClosedTarget_pi_expand]
  simpa [inst0BinderBodyTargetEq, inst0BinderBodyClosedLhs, inst0BinderBodyClosedTarget] using
    congrArg₂ Mettapedia.Languages.MeTTa.Pure.Core.mkPi hA hB

theorem inst0BinderTargetEq_sigma_of
    {ν : Nat → String} {m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    {A : PureTm ((n + 1) + m)} {B : PureTm (((n + 1) + m) + 1)}
    (hA : inst0BinderTargetEq ν m k ρ a A)
    (hB : inst0BinderBodyTargetEq ν m k ρ a B) :
    inst0BinderTargetEq ν m k ρ a (.sigma A B) := by
  unfold inst0BinderTargetEq at hA ⊢
  rw [inst0BinderClosedLhs_sigma_expand, inst0BinderClosedTarget_sigma_expand]
  simpa [inst0BinderBodyTargetEq, inst0BinderBodyClosedLhs, inst0BinderBodyClosedTarget] using
    congrArg₂ Mettapedia.Languages.MeTTa.Pure.Core.mkSigma hA hB

theorem inst0BinderTargetEq_u0
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) :
    inst0BinderTargetEq ν m k ρ a .u0 := by
  simp [inst0BinderTargetEq, inst0BinderClosedLhs, inst0BinderClosedTarget, quoteTmWith, subst]

theorem inst0BinderTargetEq_u1
    (ν : Nat → String) (m k : Nat) (ρ : QuoteEnv n) (a : PureTm n) :
    inst0BinderTargetEq ν m k ρ a .u1 := by
  simp [inst0BinderTargetEq, inst0BinderClosedLhs, inst0BinderClosedTarget, quoteTmWith, subst]

theorem inst0BinderTargetEq_id_of
    {ν : Nat → String} {m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    {A a₁ b₁ : PureTm ((n + 1) + m)}
    (hA : inst0BinderTargetEq ν m k ρ a A)
    (ha₁ : inst0BinderTargetEq ν m k ρ a a₁)
    (hb₁ : inst0BinderTargetEq ν m k ρ a b₁) :
    inst0BinderTargetEq ν m k ρ a (.id A a₁ b₁) := by
  unfold inst0BinderTargetEq at hA ha₁ hb₁ ⊢
  simp [inst0BinderClosedLhs, inst0BinderClosedTarget, quoteTmWith, subst] at hA ha₁ hb₁ ⊢
  rw [hA, ha₁, hb₁]

theorem inst0BinderTargetEq_app_of
    {ν : Nat → String} {m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    {f b : PureTm ((n + 1) + m)}
    (hf : inst0BinderTargetEq ν m k ρ a f)
    (hb : inst0BinderTargetEq ν m k ρ a b) :
    inst0BinderTargetEq ν m k ρ a (.app f b) := by
  unfold inst0BinderTargetEq at hf hb ⊢
  simp [inst0BinderClosedLhs, inst0BinderClosedTarget, quoteTmWith, subst] at hf hb ⊢
  rw [hf, hb]

theorem inst0BinderTargetEq_pair_of
    {ν : Nat → String} {m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    {p q : PureTm ((n + 1) + m)}
    (hp : inst0BinderTargetEq ν m k ρ a p)
    (hq : inst0BinderTargetEq ν m k ρ a q) :
    inst0BinderTargetEq ν m k ρ a (.pair p q) := by
  unfold inst0BinderTargetEq at hp hq ⊢
  simp [inst0BinderClosedLhs, inst0BinderClosedTarget, quoteTmWith, subst] at hp hq ⊢
  rw [hp, hq]

theorem inst0BinderTargetEq_fst_of
    {ν : Nat → String} {m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    {p : PureTm ((n + 1) + m)}
    (hp : inst0BinderTargetEq ν m k ρ a p) :
    inst0BinderTargetEq ν m k ρ a (.fst p) := by
  unfold inst0BinderTargetEq at hp ⊢
  simp [inst0BinderClosedLhs, inst0BinderClosedTarget, quoteTmWith, subst] at hp ⊢
  rw [hp]

theorem inst0BinderTargetEq_snd_of
    {ν : Nat → String} {m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    {p : PureTm ((n + 1) + m)}
    (hp : inst0BinderTargetEq ν m k ρ a p) :
    inst0BinderTargetEq ν m k ρ a (.snd p) := by
  unfold inst0BinderTargetEq at hp ⊢
  simp [inst0BinderClosedLhs, inst0BinderClosedTarget, quoteTmWith, subst] at hp ⊢
  rw [hp]

theorem inst0BinderTargetEq_refl_of
    {ν : Nat → String} {m k : Nat} {ρ : QuoteEnv n} {a : PureTm n}
    {p : PureTm ((n + 1) + m)}
    (hp : inst0BinderTargetEq ν m k ρ a p) :
    inst0BinderTargetEq ν m k ρ a (.refl p) := by
  unfold inst0BinderTargetEq at hp ⊢
  simp [inst0BinderClosedLhs, inst0BinderClosedTarget, quoteTmWith, subst] at hp ⊢
  rw [hp]

end Mettapedia.Languages.MeTTa.PureKernel.PatternBridge.Inst0BridgeProof
