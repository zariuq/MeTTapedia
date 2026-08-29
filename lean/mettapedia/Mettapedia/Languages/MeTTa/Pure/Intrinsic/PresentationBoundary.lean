import Mettapedia.Languages.MeTTa.Pure.Intrinsic.Inst0BridgeDerived
import Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing
import Mettapedia.Languages.MeTTa.Pure.SubjectReduction

/-!
# The intrinsic/Pattern Pure presentation boundary

The intrinsic `IntrinsicPure` syntax contains global declaration constants, while
the locally nameless Pattern presentation deliberately does not.  Moreover,
the two authored typing judgments have different rule premises: Pattern Pure
records domain/codomain regularity at eliminations, while the original
`IntrinsicPure.HasType` rules omit several of those premises.

This module isolates the exact common syntax and the regular,
fragment-internal typing spine before proving any presentation
correspondence.  In particular, it does not identify the two existing
judgments by definition.
-/

namespace Mettapedia.Languages.MeTTa.Pure.Intrinsic.PresentationBoundary

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.Languages.MeTTa.Pure.Core
open Mettapedia.Languages.MeTTa.Pure.BinderOps
open Mettapedia.Languages.MeTTa.Pure.Fragment
open Mettapedia.Languages.MeTTa.Pure.Typing
open Mettapedia.Languages.MeTTa.Pure.SubjectReduction
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Syntax
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Context
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Renaming
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.Substitution
open Mettapedia.Languages.MeTTa.Pure.Intrinsic.PatternBridge

/-! ## Exact common syntax -/

/-- The declaration-free intrinsic fragment represented by `PureTmPattern`.

This is structural rather than a list of admitted constants: adding a global
declaration to `IntrinsicPure` never silently enlarges the Pattern Pure grammar.
-/
inductive ConstantFree : PureTm n → Prop where
  | var (i : Fin n) : ConstantFree (.var i)
  | u0 : ConstantFree .u0
  | u1 : ConstantFree .u1
  | pi : ConstantFree A → ConstantFree B → ConstantFree (.pi A B)
  | sigma : ConstantFree A → ConstantFree B → ConstantFree (.sigma A B)
  | id : ConstantFree A → ConstantFree a → ConstantFree b → ConstantFree (.id A a b)
  | lam : ConstantFree body → ConstantFree (.lam body)
  | app : ConstantFree f → ConstantFree a → ConstantFree (.app f a)
  | pair : ConstantFree a → ConstantFree b → ConstantFree (.pair a b)
  | fst : ConstantFree p → ConstantFree (.fst p)
  | snd : ConstantFree p → ConstantFree (.snd p)
  | refl : ConstantFree a → ConstantFree (.refl a)

/-- Renaming cannot introduce a declaration constant. -/
theorem ConstantFree.rename {t : PureTm n} (h : ConstantFree t) (ρ : Ren n m) :
    ConstantFree (rename ρ t) := by
  induction h generalizing m with
  | var i => exact .var (ρ i)
  | u0 => exact .u0
  | u1 => exact .u1
  | pi _ _ ihA ihB => exact .pi (ihA ρ) (ihB (liftRen ρ))
  | sigma _ _ ihA ihB => exact .sigma (ihA ρ) (ihB (liftRen ρ))
  | id _ _ _ ihA iha ihb => exact .id (ihA ρ) (iha ρ) (ihb ρ)
  | lam _ ih => exact .lam (ih (liftRen ρ))
  | app _ _ ihf iha => exact .app (ihf ρ) (iha ρ)
  | pair _ _ iha ihb => exact .pair (iha ρ) (ihb ρ)
  | fst _ ih => exact .fst (ih ρ)
  | snd _ ih => exact .snd (ih ρ)
  | refl _ ih => exact .refl (ih ρ)

/-- Quotation maps every declaration-free intrinsic term into Pattern Pure. -/
theorem quoteTmWith_pure {t : PureTm n} (h : ConstantFree t) (ν : Nat → String)
    (k : Nat) (ρ : QuoteEnv n) : PureTmPattern (quoteTmWith ν k ρ t) := by
  induction h generalizing k with
  | var i => exact .fvar (ρ i)
  | u0 => exact .u0
  | u1 => exact .u1
  | pi _ _ ihA ihB =>
      exact .pi (ihA k ρ)
        (pureTm_closeBVar (ν k) (ihB (k + 1) (envCons (ν k) ρ)))
  | sigma _ _ ihA ihB =>
      exact .sigma (ihA k ρ)
        (pureTm_closeBVar (ν k) (ihB (k + 1) (envCons (ν k) ρ)))
  | id _ _ _ ihA iha ihb => exact .id (ihA k ρ) (iha k ρ) (ihb k ρ)
  | lam _ ih =>
      exact .lam (pureTm_closeBVar (ν k) (ih (k + 1) (envCons (ν k) ρ)))
  | app _ _ ihf iha => exact .app (ihf k ρ) (iha k ρ)
  | pair _ _ iha ihb => exact .pair (iha k ρ) (ihb k ρ)
  | fst _ ih => exact .fst (ih k ρ)
  | snd _ ih => exact .snd (ih k ρ)
  | refl _ ih => exact .refl (ih k ρ)

/-- The legacy string quote is not an exact syntax embedding: a declaration
whose printed name is a reserved Pure constructor collides with that
constructor.  This positive witness prevents an exact-image theorem from being
claimed for `quoteTmWith` itself. -/
theorem legacy_quoteConst_u0_collision (c : DeclName)
    (hc : c.toString = "U0") : quoteConst c = u0 := by
  simp [quoteConst, u0, hc]

theorem legacy_quoteConst_u0_is_pure (c : DeclName)
    (hc : c.toString = "U0") : PureTmPattern (quoteConst c) := by
  rw [legacy_quoteConst_u0_collision c hc]
  exact .u0

/-! ### Collision-free quotation

The exact presentation square uses a tagged constant node.  This leaves the
legacy artifact quote unchanged for existing clients while supplying a
faithful syntax boundary for typing correspondence.
-/

/-- Structural unary encoding of the numeric component of a declaration name.
No pretty-printer is used at the exact syntax boundary. -/
def quoteNameNat : Nat → Pattern
  | 0 => .apply "IntrinsicPure.name.nat.zero" []
  | n + 1 => .apply "IntrinsicPure.name.nat.succ" [quoteNameNat n]

/-- Structural encoding of Lean declaration names.  String components remain
literal Pattern labels, while nesting and numeric components remain explicit
constructors. -/
def quoteDeclName : DeclName → Pattern
  | .anonymous => .apply "IntrinsicPure.name.anonymous" []
  | .str pre component =>
      .apply "IntrinsicPure.name.str" [quoteDeclName pre, .apply component []]
  | .num pre component =>
      .apply "IntrinsicPure.name.num" [quoteDeclName pre, quoteNameNat component]

def quoteTaggedConst (c : DeclName) : Pattern :=
  .apply "IntrinsicPure.const" [quoteDeclName c]

theorem quoteNameNat_injective : Function.Injective quoteNameNat := by
  intro a
  induction a with
  | zero =>
      intro b h
      cases b with
      | zero => rfl
      | succ b => simp [quoteNameNat] at h
  | succ a ih =>
      intro b h
      cases b with
      | zero => simp [quoteNameNat] at h
      | succ b =>
          simp [quoteNameNat] at h
          exact congrArg Nat.succ (ih h)

theorem quoteDeclName_injective : Function.Injective quoteDeclName := by
  intro a
  induction a with
  | anonymous =>
      intro b h
      cases b with
      | anonymous => rfl
      | str pre component => simp [quoteDeclName] at h
      | num pre component => simp [quoteDeclName] at h
  | str pre component ih =>
      intro b h
      cases b with
      | anonymous => simp [quoteDeclName] at h
      | str pre' component' =>
          simp [quoteDeclName] at h
          rcases h with ⟨hprefix, hcomponent⟩
          exact congrArg₂ Lean.Name.str (ih hprefix) hcomponent
      | num pre' component' => simp [quoteDeclName] at h
  | num pre component ih =>
      intro b h
      cases b with
      | anonymous => simp [quoteDeclName] at h
      | str pre' component' => simp [quoteDeclName] at h
      | num pre' component' =>
          simp [quoteDeclName] at h
          rcases h with ⟨hprefix, hcomponent⟩
          exact congrArg₂ Lean.Name.num (ih hprefix)
            (quoteNameNat_injective hcomponent)

theorem quoteTaggedConst_injective : Function.Injective quoteTaggedConst := by
  intro a b h
  simp [quoteTaggedConst] at h
  exact quoteDeclName_injective h

theorem lc_quoteNameNat (component : Nat) :
    lc_at 0 (quoteNameNat component) = true := by
  induction component with
  | zero => rfl
  | succ component ih => simpa [quoteNameNat, lc_at, lc_at_list] using ih

theorem lc_quoteDeclName (name : DeclName) :
    lc_at 0 (quoteDeclName name) = true := by
  induction name with
  | anonymous => rfl
  | str pre component ih => simpa [quoteDeclName, lc_at, lc_at_list] using ih
  | num pre component ih =>
      simp [quoteDeclName, lc_at, lc_at_list, ih, lc_quoteNameNat]

def quoteExactWith (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n) : PureTm n → Pattern
  | .var i => .fvar (ρ i)
  | .const c => quoteTaggedConst c
  | .u0 => u0
  | .u1 => u1
  | .pi A B =>
      let x := ν k
      mkPi (quoteExactWith ν k ρ A)
        (closeFVar 0 x (quoteExactWith ν (k + 1) (envCons x ρ) B))
  | .sigma A B =>
      let x := ν k
      mkSigma (quoteExactWith ν k ρ A)
        (closeFVar 0 x (quoteExactWith ν (k + 1) (envCons x ρ) B))
  | .id A a b =>
      mkId (quoteExactWith ν k ρ A) (quoteExactWith ν k ρ a) (quoteExactWith ν k ρ b)
  | .lam body =>
      let x := ν k
      mkLam (closeFVar 0 x (quoteExactWith ν (k + 1) (envCons x ρ) body))
  | .app f a => mkApp (quoteExactWith ν k ρ f) (quoteExactWith ν k ρ a)
  | .pair a b => mkPair (quoteExactWith ν k ρ a) (quoteExactWith ν k ρ b)
  | .fst p => mkFst (quoteExactWith ν k ρ p)
  | .snd p => mkSnd (quoteExactWith ν k ρ p)
  | .refl a => mkRefl (quoteExactWith ν k ρ a)

def isTaggedConst : Pattern → Bool
  | .apply name _ => name == "IntrinsicPure.const"
  | _ => false

theorem pure_isTaggedConst_false {p : Pattern} (h : PureTmPattern p) :
    isTaggedConst p = false := by
  induction h <;>
    simp [isTaggedConst, u0, u1, mkPi, mkSigma, mkId, mkLam, mkApp, mkPair,
      mkFst, mkSnd, mkRefl]

theorem quoteTaggedConst_not_pure (c : DeclName) :
    ¬ PureTmPattern (quoteTaggedConst c) := by
  intro h
  have hfalse := pure_isTaggedConst_false h
  simp [quoteTaggedConst, isTaggedConst] at hfalse

theorem lc_quoteExactWith (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n)
    (t : PureTm n) : lc_at 0 (quoteExactWith ν k ρ t) = true := by
  induction t generalizing k with
  | var => simp [quoteExactWith, lc_at]
  | const c =>
      simp [quoteExactWith, quoteTaggedConst, lc_at, lc_at_list,
        lc_quoteDeclName c]
  | u0 => simp [quoteExactWith, u0, lc_at, lc_at_list]
  | u1 => simp [quoteExactWith, u1, lc_at, lc_at_list]
  | pi A B ihA ihB =>
      have hA := ihA (k := k)
      have hB0 := ihB (k := k + 1) (ρ := envCons (ν k) ρ)
      have hB1 : lc_at 1 (quoteExactWith ν (k + 1) (envCons (ν k) ρ) B) = true :=
        lc_at_mono hB0 (Nat.zero_le 1)
      have hClosed := lc_at_closeFVar_of_lt (k := 1) (l := 0) (ν k)
        (quoteExactWith ν (k + 1) (envCons (ν k) ρ) B) (by omega) hB1
      simp [quoteExactWith, mkPi, lc_at, lc_at_list, hA, hClosed]
  | sigma A B ihA ihB =>
      have hA := ihA (k := k)
      have hB0 := ihB (k := k + 1) (ρ := envCons (ν k) ρ)
      have hB1 : lc_at 1 (quoteExactWith ν (k + 1) (envCons (ν k) ρ) B) = true :=
        lc_at_mono hB0 (Nat.zero_le 1)
      have hClosed := lc_at_closeFVar_of_lt (k := 1) (l := 0) (ν k)
        (quoteExactWith ν (k + 1) (envCons (ν k) ρ) B) (by omega) hB1
      simp [quoteExactWith, mkSigma, lc_at, lc_at_list, hA, hClosed]
  | id A a b ihA iha ihb =>
      simp [quoteExactWith, mkId, lc_at, lc_at_list,
        ihA (k := k), iha (k := k), ihb (k := k)]
  | lam body ih =>
      have h0 := ih (k := k + 1) (ρ := envCons (ν k) ρ)
      have h1 : lc_at 1 (quoteExactWith ν (k + 1) (envCons (ν k) ρ) body) = true :=
        lc_at_mono h0 (Nat.zero_le 1)
      have hClosed := lc_at_closeFVar_of_lt (k := 1) (l := 0) (ν k)
        (quoteExactWith ν (k + 1) (envCons (ν k) ρ) body) (by omega) h1
      simp [quoteExactWith, mkLam, lc_at, lc_at_list, hClosed]
  | app f a ihf iha =>
      simp [quoteExactWith, mkApp, lc_at, lc_at_list, ihf (k := k), iha (k := k)]
  | pair a b iha ihb =>
      simp [quoteExactWith, mkPair, lc_at, lc_at_list, iha (k := k), ihb (k := k)]
  | fst p ih => simp [quoteExactWith, mkFst, lc_at, lc_at_list, ih (k := k)]
  | snd p ih => simp [quoteExactWith, mkSnd, lc_at, lc_at_list, ih (k := k)]
  | refl a ih => simp [quoteExactWith, mkRefl, lc_at, lc_at_list, ih (k := k)]

/-- Closing a locally closed Pattern at depth zero is injective.  Reopening
both sides recovers the original Patterns. -/
theorem closeFVar_zero_injective_of_lc {x : String} {p q : Pattern}
    (hp : lc_at 0 p = true) (hq : lc_at 0 q = true)
    (h : closeFVar 0 x p = closeFVar 0 x q) : p = q := by
  have hopen := congrArg (openBVar 0 (.fvar x)) h
  simpa [openBVar_closeBVar_cancel hp, openBVar_closeBVar_cancel hq] using hopen

/-- Structural quotation is faithful whenever the free-variable environment
is injective and disjoint from the generated binder names.  In particular,
quotation does not identify distinct intrinsic terms, including beneath
binders. -/
theorem quoteExactWith_injective
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hρ : Function.Injective ρ) (hcompat : QuoteCompat ν k ρ) :
    Function.Injective (quoteExactWith ν k ρ) := by
  intro t u heq
  induction t generalizing k with
  | var i =>
      cases u <;>
        simp_all [quoteExactWith, quoteTaggedConst,
          u0, u1, mkPi, mkSigma, mkId, mkLam, mkApp, mkPair, mkFst, mkSnd, mkRefl]
      exact hρ heq
  | const c =>
      cases u <;>
        simp_all [quoteExactWith, quoteTaggedConst,
          u0, u1, mkPi, mkSigma, mkId, mkLam, mkApp, mkPair, mkFst, mkSnd, mkRefl]
      exact quoteDeclName_injective heq
  | u0 =>
      cases u <;>
        simp_all [quoteExactWith, quoteTaggedConst,
          u0, u1, mkPi, mkSigma, mkId, mkLam, mkApp, mkPair, mkFst, mkSnd, mkRefl]
  | u1 =>
      cases u <;>
        simp_all [quoteExactWith, quoteTaggedConst,
          u0, u1, mkPi, mkSigma, mkId, mkLam, mkApp, mkPair, mkFst, mkSnd, mkRefl]
  | pi A B ihA ihB =>
      cases u <;>
        simp_all [quoteExactWith, quoteTaggedConst,
          u0, u1, mkPi, mkSigma, mkId, mkLam, mkApp, mkPair, mkFst, mkSnd, mkRefl]
      rename_i A' B'
      rcases heq with ⟨hA, hB⟩
      refine ⟨ihA hρ hcompat hA, ?_⟩
      have hopened := closeFVar_zero_injective_of_lc
        (lc_quoteExactWith ν (k + 1) (envCons (ν k) ρ) B)
        (lc_quoteExactWith ν (k + 1) (envCons (ν k) ρ) B') hB
      exact ihB (envCons_injective_of_injective_of_compat hρ hcompat)
        (QuoteCompat.envCons hcompat.1 hcompat) hopened
  | sigma A B ihA ihB =>
      cases u <;>
        simp_all [quoteExactWith, quoteTaggedConst,
          u0, u1, mkPi, mkSigma, mkId, mkLam, mkApp, mkPair, mkFst, mkSnd, mkRefl]
      rename_i A' B'
      rcases heq with ⟨hA, hB⟩
      refine ⟨ihA hρ hcompat hA, ?_⟩
      have hopened := closeFVar_zero_injective_of_lc
        (lc_quoteExactWith ν (k + 1) (envCons (ν k) ρ) B)
        (lc_quoteExactWith ν (k + 1) (envCons (ν k) ρ) B') hB
      exact ihB (envCons_injective_of_injective_of_compat hρ hcompat)
        (QuoteCompat.envCons hcompat.1 hcompat) hopened
  | id A a b ihA iha ihb =>
      cases u <;>
        simp_all [quoteExactWith, quoteTaggedConst,
          u0, u1, mkPi, mkSigma, mkId, mkLam, mkApp, mkPair, mkFst, mkSnd, mkRefl]
      exact ⟨ihA hρ hcompat heq.1,
        iha hρ hcompat heq.2.1, ihb hρ hcompat heq.2.2⟩
  | lam body ih =>
      cases u <;>
        simp_all [quoteExactWith, quoteTaggedConst,
          u0, u1, mkPi, mkSigma, mkId, mkLam, mkApp, mkPair, mkFst, mkSnd, mkRefl]
      rename_i body'
      have hopened := closeFVar_zero_injective_of_lc
        (lc_quoteExactWith ν (k + 1) (envCons (ν k) ρ) body)
        (lc_quoteExactWith ν (k + 1) (envCons (ν k) ρ) body') heq
      exact ih (envCons_injective_of_injective_of_compat hρ hcompat)
        (QuoteCompat.envCons hcompat.1 hcompat) hopened
  | app f a ihf iha =>
      cases u <;>
        simp_all [quoteExactWith, quoteTaggedConst,
          u0, u1, mkPi, mkSigma, mkId, mkLam, mkApp, mkPair, mkFst, mkSnd, mkRefl]
      exact ⟨ihf hρ hcompat heq.1, iha hρ hcompat heq.2⟩
  | pair a b iha ihb =>
      cases u <;>
        simp_all [quoteExactWith, quoteTaggedConst,
          u0, u1, mkPi, mkSigma, mkId, mkLam, mkApp, mkPair, mkFst, mkSnd, mkRefl]
      exact ⟨iha hρ hcompat heq.1, ihb hρ hcompat heq.2⟩
  | fst p ih =>
      cases u <;>
        simp_all [quoteExactWith, quoteTaggedConst,
          u0, u1, mkPi, mkSigma, mkId, mkLam, mkApp, mkPair, mkFst, mkSnd, mkRefl]
      exact ih hρ hcompat heq
  | snd p ih =>
      cases u <;>
        simp_all [quoteExactWith, quoteTaggedConst,
          u0, u1, mkPi, mkSigma, mkId, mkLam, mkApp, mkPair, mkFst, mkSnd, mkRefl]
      exact ih hρ hcompat heq
  | refl a ih =>
      cases u <;>
        simp_all [quoteExactWith, quoteTaggedConst,
          u0, u1, mkPi, mkSigma, mkId, mkLam, mkApp, mkPair, mkFst, mkSnd, mkRefl]
      exact ih hρ hcompat heq

theorem quoteExactWith_pure {t : PureTm n} (h : ConstantFree t)
    (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n) :
    PureTmPattern (quoteExactWith ν k ρ t) := by
  induction h generalizing k with
  | var i => exact .fvar (ρ i)
  | u0 => exact .u0
  | u1 => exact .u1
  | pi _ _ ihA ihB =>
      exact .pi (ihA k ρ)
        (pureTm_closeBVar (ν k) (ihB (k + 1) (envCons (ν k) ρ)))
  | sigma _ _ ihA ihB =>
      exact .sigma (ihA k ρ)
        (pureTm_closeBVar (ν k) (ihB (k + 1) (envCons (ν k) ρ)))
  | id _ _ _ ihA iha ihb => exact .id (ihA k ρ) (iha k ρ) (ihb k ρ)
  | lam _ ih =>
      exact .lam (pureTm_closeBVar (ν k) (ih (k + 1) (envCons (ν k) ρ)))
  | app _ _ ihf iha => exact .app (ihf k ρ) (iha k ρ)
  | pair _ _ iha ihb => exact .pair (iha k ρ) (ihb k ρ)
  | fst _ ih => exact .fst (ih k ρ)
  | snd _ ih => exact .snd (ih k ρ)
  | refl _ ih => exact .refl (ih k ρ)

/-- On the common fragment, the collision-free quote is byte-for-byte the
existing artifact quote.  Existing clients therefore need no migration for
terms that actually belong to Pattern Pure. -/
theorem quoteExactWith_eq_quoteTmWith {t : PureTm n} (h : ConstantFree t)
    (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n) :
    quoteExactWith ν k ρ t = quoteTmWith ν k ρ t := by
  induction h generalizing k with
  | var => rfl
  | u0 => rfl
  | u1 => rfl
  | pi _ _ ihA ihB =>
      simp only [quoteExactWith, quoteTmWith]
      rw [ihA k ρ, ihB (k + 1) (envCons (ν k) ρ)]
  | sigma _ _ ihA ihB =>
      simp only [quoteExactWith, quoteTmWith]
      rw [ihA k ρ, ihB (k + 1) (envCons (ν k) ρ)]
  | id _ _ _ ihA iha ihb =>
      simp only [quoteExactWith, quoteTmWith]
      rw [ihA k ρ, iha k ρ, ihb k ρ]
  | lam _ ih =>
      simp only [quoteExactWith, quoteTmWith]
      rw [ih (k + 1) (envCons (ν k) ρ)]
  | app _ _ ihf iha =>
      simp only [quoteExactWith, quoteTmWith]
      rw [ihf k ρ, iha k ρ]
  | pair _ _ iha ihb =>
      simp only [quoteExactWith, quoteTmWith]
      rw [iha k ρ, ihb k ρ]
  | fst _ ih =>
      simp only [quoteExactWith, quoteTmWith]
      rw [ih k ρ]
  | snd _ ih =>
      simp only [quoteExactWith, quoteTmWith]
      rw [ih k ρ]
  | refl _ ih =>
      simp only [quoteExactWith, quoteTmWith]
      rw [ih k ρ]

/-- The established Pattern quote is faithful on the exact common fragment.
This is derived through the structural quotation, rather than assuming that
the legacy quotation is injective on arbitrary constant-bearing syntax. -/
theorem quoteTmWith_injective_of_constantFree
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hρ : Function.Injective ρ) (hcompat : QuoteCompat ν k ρ)
    {t u : PureTm n} (ht : ConstantFree t) (hu : ConstantFree u)
    (h : quoteTmWith ν k ρ t = quoteTmWith ν k ρ u) : t = u := by
  apply quoteExactWith_injective hρ hcompat
  rw [quoteExactWith_eq_quoteTmWith ht, quoteExactWith_eq_quoteTmWith hu]
  exact h

private theorem pure_closed_exact_body
    (x : String) (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n) (body : PureTm n)
    (hclosed : PureTmPattern (closeFVar 0 x (quoteExactWith ν k ρ body))) :
    PureTmPattern (quoteExactWith ν k ρ body) := by
  have hopen : PureTmPattern
      (openBVar 0 (.fvar x)
        (closeFVar 0 x (quoteExactWith ν k ρ body))) :=
    pureTm_openBVar_fvar x (k := 0) hclosed
  have hround :
      openBVar 0 (.fvar x)
          (closeFVar 0 x (quoteExactWith ν k ρ body)) =
        quoteExactWith ν k ρ body :=
    openBVar_closeBVar_cancel (lc_quoteExactWith ν k ρ body)
  rwa [hround] at hopen

/-- The tagged quotation has the exact constant-free fragment as its Pattern
Pure image. -/
theorem pure_quoteExactWith_iff (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n)
    (t : PureTm n) :
    PureTmPattern (quoteExactWith ν k ρ t) ↔ ConstantFree t := by
  constructor
  · intro h
    induction t generalizing k with
    | var i => exact .var i
    | const c => exact False.elim (quoteTaggedConst_not_pure c h)
    | u0 => exact .u0
    | u1 => exact .u1
    | pi A B ihA ihB =>
        have hAB := pure_pi_inv h
        have hBody := pure_closed_exact_body (ν k) ν (k + 1) (envCons (ν k) ρ) B hAB.2
        exact .pi (ihA k ρ hAB.1) (ihB (k + 1) (envCons (ν k) ρ) hBody)
    | sigma A B ihA ihB =>
        have hAB := pure_sigma_inv h
        have hBody := pure_closed_exact_body (ν k) ν (k + 1) (envCons (ν k) ρ) B hAB.2
        exact .sigma (ihA k ρ hAB.1) (ihB (k + 1) (envCons (ν k) ρ) hBody)
    | id A a b ihA iha ihb =>
        have hab := pure_id_inv h
        exact .id (ihA k ρ hab.1) (iha k ρ hab.2.1) (ihb k ρ hab.2.2)
    | lam body ih =>
        have hBody := pure_closed_exact_body (ν k) ν (k + 1) (envCons (ν k) ρ) body
          (pure_lam_inv h)
        exact .lam (ih (k + 1) (envCons (ν k) ρ) hBody)
    | app f a ihf iha =>
        have hfa := pure_app_inv h
        exact .app (ihf k ρ hfa.1) (iha k ρ hfa.2)
    | pair a b iha ihb =>
        have hab := pure_pair_inv h
        exact .pair (iha k ρ hab.1) (ihb k ρ hab.2)
    | fst p ih => exact .fst (ih k ρ (pure_fst_inv h))
    | snd p ih => exact .snd (ih k ρ (pure_snd_inv h))
    | refl a ih => exact .refl (ih k ρ (pure_refl_inv h))
  · exact fun h => quoteExactWith_pure h ν k ρ

/-! ## Context presentation -/

/-- The locally nameless association-list presentation of an intrinsic
telescope.  The most recent intrinsic variable becomes the head entry. -/
def quotePureCtx (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n) : Ctx n → PureCtx
  | .nil => []
  | .snoc Γ A =>
      let ρprev : QuoteEnv _ := fun i => ρ i.succ
      (ρ 0, quoteTmWith ν k ρprev A) :: quotePureCtx ν k ρprev Γ

@[simp] theorem quotePureCtx_nil (ν : Nat → String) (k : Nat) :
    quotePureCtx ν k emptyEnv .nil = [] := rfl

@[simp] theorem quotePureCtx_snoc (ν : Nat → String) (k : Nat)
    (ρ : QuoteEnv (n + 1)) (Γ : Ctx n) (A : PureTm n) :
    quotePureCtx ν k ρ (.snoc Γ A) =
      (ρ 0, quoteTmWith ν k (fun i => ρ i.succ) A) ::
        quotePureCtx ν k (fun i => ρ i.succ) Γ := rfl

/-- Intrinsic lookup is represented by association-list membership after
quotation. -/
theorem quote_lookup_mem (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n)
    (Γ : Ctx n) (i : Fin n) :
    (ρ i, quoteTmWith ν k ρ (lookup Γ i)) ∈ quotePureCtx ν k ρ Γ := by
  induction Γ with
  | nil => exact Fin.elim0 i
  | @snoc n Γ A ih =>
      refine Fin.cases ?_ ?_ i
      · apply List.mem_cons.mpr
        left
        apply Prod.ext
        · rfl
        · simpa [wk] using
            (quoteTmWith_rename ν (k := k) (ρdst := ρ) (ρ := wk) (t := A))
      · intro j
        have hmem := ih (ρ := fun q => ρ q.succ) j
        apply List.mem_cons.mpr
        right
        have hq :
            quoteTmWith ν k ρ (rename wk (lookup Γ j)) =
              quoteTmWith ν k (fun q => ρ q.succ) (lookup Γ j) := by
          simpa [wk] using
            (quoteTmWith_rename ν (k := k) (ρdst := ρ) (ρ := wk)
              (t := lookup Γ j))
        simp only [lookup_snoc_succ]
        rwa [hq]

/-! ### Quotation coherence across binder depths

The staged quotation proof already establishes that compatible binder-name
choices erase from the resulting locally nameless Pattern.  The lemmas below
lift that fact from terms to telescope presentations and record the freshness
facts needed by cofinite typing rules. -/

/-- Compatibility weakens when the quotation depth advances. -/
theorem QuoteCompat.mono {ν : Nat → String} {k l : Nat} {ρ : QuoteEnv n}
    (h : QuoteCompat ν k ρ) (hkl : k ≤ l) : QuoteCompat ν l ρ := by
  refine ⟨h.1, ?_⟩
  intro i j hlj
  exact h.2 i j (hkl.trans hlj)

/-- Compatible quotation is independent of the numerical binder depth. -/
theorem quoteTmWith_depth_indep {ν : Nat → String} {k l : Nat}
    {ρ : QuoteEnv n} (hcompatK : QuoteCompat ν k ρ)
    (hcompatL : QuoteCompat ν l ρ) (t : PureTm n) :
    quoteTmWith ν k ρ t = quoteTmWith ν l ρ t :=
  Inst0BridgeProof.quoteTmWith_depth_indep_staging
    ν k l ρ t hcompatK hcompatL

/-- Telescope quotation inherits term-level binder-depth independence. -/
theorem quotePureCtx_depth_indep {ν : Nat → String} {k l : Nat}
    {ρ : QuoteEnv n} (hcompatK : QuoteCompat ν k ρ)
    (hcompatL : QuoteCompat ν l ρ) (Γ : Ctx n) :
    quotePureCtx ν k ρ Γ = quotePureCtx ν l ρ Γ := by
  induction Γ with
  | nil => rfl
  | @snoc n Γ A ih =>
      let ρtail : QuoteEnv n := fun i => ρ i.succ
      have hKtail : QuoteCompat ν k ρtail := by
        refine ⟨hcompatK.1, ?_⟩
        intro i j hj
        exact hcompatK.2 i.succ j hj
      have hLtail : QuoteCompat ν l ρtail := by
        refine ⟨hcompatL.1, ?_⟩
        intro i j hj
        exact hcompatL.2 i.succ j hj
      simp only [quotePureCtx_snoc]
      rw [quoteTmWith_depth_indep hKtail hLtail A]
      rw [ih hKtail hLtail]

/-- Every name in the quoted context is supplied by its quote environment. -/
theorem quotePureCtx_ctxNames_mem_env (ν : Nat → String) (k : Nat)
    (ρ : QuoteEnv n) (Γ : Ctx n) {z : String} :
    z ∈ ctxNames (quotePureCtx ν k ρ Γ) → ∃ i : Fin n, ρ i = z := by
  induction Γ with
  | nil => simp [quotePureCtx, ctxNames]
  | @snoc n Γ A ih =>
      intro hz
      simp only [quotePureCtx_snoc, ctxNames_cons, List.mem_cons] at hz
      rcases hz with hz | hz
      · exact ⟨0, hz.symm⟩
      · rcases ih (ρ := fun i => ρ i.succ) hz with ⟨i, hi⟩
        exact ⟨i.succ, hi⟩

/-- The current canonical binder name is absent from a compatible quoted
context. -/
theorem quotePureCtx_current_not_mem_ctxNames
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ) (Γ : Ctx n) :
    ν k ∉ ctxNames (quotePureCtx ν k ρ Γ) := by
  intro hmem
  rcases quotePureCtx_ctxNames_mem_env ν k ρ Γ hmem with ⟨i, hi⟩
  exact hcompat.2 i k (by omega) hi

/-- The current canonical binder name is fresh in every type stored in a
compatible quoted context. -/
theorem quotePureCtx_current_fresh
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ) (Γ : Ctx n) :
    ctxFresh (ν k) (quotePureCtx ν k ρ Γ) := by
  induction Γ with
  | nil =>
      intro y T hmem
      simp [quotePureCtx] at hmem
  | @snoc n Γ A ih =>
      let ρtail : QuoteEnv n := fun i => ρ i.succ
      have htail : QuoteCompat ν k ρtail := by
        refine ⟨hcompat.1, ?_⟩
        intro i j hj
        exact hcompat.2 i.succ j hj
      intro y T hmem
      rw [quotePureCtx_snoc] at hmem
      rcases List.mem_cons.mp hmem with hhead | hrest
      · cases hhead
        exact isFresh_quoteTmWith_future htail A (j := k) (by omega)
      · exact ih htail y T hrest

/-- Every intrinsic telescope entry must be declaration-free for the context
to live in the Pattern Pure presentation. -/
def ConstantFreeCtx : Ctx n → Prop
  | .nil => True
  | .snoc Γ A => ConstantFreeCtx Γ ∧ ConstantFree A

theorem ConstantFreeCtx.lookup {Γ : Ctx n} (hΓ : ConstantFreeCtx Γ) (i : Fin n) :
    ConstantFree (lookup Γ i) := by
  induction Γ with
  | nil => exact Fin.elim0 i
  | @snoc n Γ A ih =>
      rcases hΓ with ⟨hΓ, hA⟩
      refine Fin.cases ?_ ?_ i
      · exact hA.rename wk
      · intro j
        exact (ih hΓ j).rename wk

/-! `inst0` is substitution, not application.  These lemmas keep the syntax
boundary proof honest without conflating those operations. -/

theorem ConstantFree.subst {t : PureTm n} {σ : Sub n m} (ht : ConstantFree t)
    (hσ : ∀ i, ConstantFree (σ i)) : ConstantFree (subst σ t) := by
  induction ht generalizing m with
  | var i => exact hσ i
  | u0 => exact .u0
  | u1 => exact .u1
  | pi _ _ ihA ihB =>
      exact .pi (ihA hσ) (ihB (fun i => Fin.cases (.var 0) (fun j => (hσ j).rename wk) i))
  | sigma _ _ ihA ihB =>
      exact .sigma (ihA hσ) (ihB (fun i => Fin.cases (.var 0) (fun j => (hσ j).rename wk) i))
  | id _ _ _ ihA iha ihb => exact .id (ihA hσ) (iha hσ) (ihb hσ)
  | lam _ ih => exact .lam (ih (fun i => Fin.cases (.var 0) (fun j => (hσ j).rename wk) i))
  | app _ _ ihf iha => exact .app (ihf hσ) (iha hσ)
  | pair _ _ iha ihb => exact .pair (iha hσ) (ihb hσ)
  | fst _ ih => exact .fst (ih hσ)
  | snd _ ih => exact .snd (ih hσ)
  | refl _ ih => exact .refl (ih hσ)

theorem ConstantFree.inst0 {a : PureTm n} {B : PureTm (n + 1)}
    (ha : ConstantFree a) (hB : ConstantFree B) :
    ConstantFree (inst0 a B) := by
  exact hB.subst (fun i => Fin.cases ha (fun j => .var j) i)

/-! ## The regular intensional typing spine -/

/-- One intrinsic reduction step whose source and target both remain in the
exact Pattern Pure fragment. -/
def ConstantFreeRed (t u : PureTm n) : Prop :=
  Mettapedia.Languages.MeTTa.Pure.Intrinsic.Reduction.Red t u ∧
    ConstantFree t ∧ ConstantFree u

/-- Definitional equality internal to the exact common fragment.

Every constructor carries enough evidence to keep the whole proof object in
the fragment, including reflexivity.  Merely applying `Relation.EqvGen` to a
restricted edge relation would make reflexivity available for arbitrary
constant-bearing terms. -/
inductive ConstantFreeConv : PureTm n → PureTm n → Prop where
  | rel {t u : PureTm n} : ConstantFreeRed t u → ConstantFreeConv t u
  | refl (t : PureTm n) : ConstantFree t → ConstantFreeConv t t
  | symm {t u : PureTm n} : ConstantFreeConv t u → ConstantFreeConv u t
  | trans {t u v : PureTm n} :
      ConstantFreeConv t u → ConstantFreeConv u v → ConstantFreeConv t v

/-- Fragment-internal conversion forgets to the permissive authored
conversion relation. -/
theorem ConstantFreeConv.toConv {t u : PureTm n} (h : ConstantFreeConv t u) :
    Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.Conv t u := by
  induction h with
  | rel hred => exact .rel _ _ hred.1
  | refl x _ => exact .refl x
  | symm hxy ih => exact .symm _ _ ih
  | trans hxy hyz ihxy ihyz => exact .trans _ _ _ ihxy ihyz

/-- Both endpoints of a fragment-internal conversion remain in the common
syntax.  This is stronger than endpoint-only filtering of a raw conversion:
the induction also certifies every intermediate term carried by the proof
object. -/
theorem ConstantFreeConv.constantFree_both {t u : PureTm n}
    (h : ConstantFreeConv t u) : ConstantFree t ∧ ConstantFree u := by
  induction h with
  | rel hred => exact hred.2
  | refl _ ht => exact ⟨ht, ht⟩
  | symm _ ih => exact ih.symm
  | trans _ _ ihxy ihyz => exact ⟨ihxy.1, ihyz.2⟩

/-- A concrete raw conversion path can leave the common fragment even when
its endpoints are pure.  This witnesses a proof-fibre mismatch; it does not
claim the endpoint propositions differ. -/
def rawConstantDetour (c : DeclName) : PureTm 0 :=
  .app (.lam .u0) (.const c)

theorem rawConstantDetour_not_constantFree (c : DeclName) :
    ¬ ConstantFree (rawConstantDetour c) := by
  intro h
  cases h with
  | app hlam hconst => cases hconst

theorem rawConstantDetour_reduces (c : DeclName) :
    Mettapedia.Languages.MeTTa.Pure.Intrinsic.Reduction.Red
      (rawConstantDetour c) .u0 := by
  simpa [rawConstantDetour, inst0, subst, subst0] using
    (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Reduction.Red.betaPi
      (.u0 : PureTm 1) (.const c : PureTm 0))

theorem raw_conversion_has_impure_detour (c : DeclName) :
    ∃ middle : PureTm 0,
      Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.Conv .u0 middle ∧
      Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.Conv middle .u0 ∧
      ¬ ConstantFree middle := by
  refine ⟨rawConstantDetour c, ?_, ?_, rawConstantDetour_not_constantFree c⟩
  · exact Relation.EqvGen.symm _ _
      (Relation.EqvGen.rel _ _ (rawConstantDetour_reduces c))
  · exact Relation.EqvGen.rel _ _ (rawConstantDetour_reduces c)

/-- The impure intermediate term cannot occur as an endpoint of the
fragment-internal conversion relation.  Together with
`raw_conversion_has_impure_detour`, this separates raw endpoint equality from
the exact conversion proof fibre used by the presentation bridge. -/
theorem rawConstantDetour_not_fragment_endpoint (c : DeclName) :
    ¬ ConstantFreeConv (.u0 : PureTm 0) (rawConstantDetour c) := by
  intro h
  exact rawConstantDetour_not_constantFree c h.constantFree_both.2

/-- The regular intrinsic spine selected by explicit presuppositions.

Unlike the older `IntrinsicPure.HasType`, every rule which consumes a dependent
codomain carries its well-formedness derivation.  This is the premise structure
already enforced by `PureHasType`.  Conversion is retained as intensional
equality, but its target must itself be a type (or the distinguished top sort).
The latter premise is deliberately stronger than the authored Pattern rule;
the forthcoming presentation square must derive it from context regularity
rather than assume the two judgments coincide.
-/
inductive RegularHasType : Ctx n → PureTm n → PureTm n → Prop where
  | u0_type (Γ : Ctx n) : RegularHasType Γ .u0 .u1
  | var {Γ : Ctx n} (i : Fin n) : RegularHasType Γ (.var i) (lookup Γ i)
  | pi_form {Γ : Ctx n} {A : PureTm n} {B : PureTm (n + 1)} :
      RegularHasType Γ A .u1 →
      RegularHasType (.snoc Γ A) B .u1 →
      RegularHasType Γ (.pi A B) .u1
  | sigma_form {Γ : Ctx n} {A : PureTm n} {B : PureTm (n + 1)} :
      RegularHasType Γ A .u1 →
      RegularHasType (.snoc Γ A) B .u1 →
      RegularHasType Γ (.sigma A B) .u1
  | lam_intro {Γ : Ctx n} {A : PureTm n} {body B : PureTm (n + 1)} :
      RegularHasType Γ A .u1 →
      RegularHasType (.snoc Γ A) B .u1 →
      RegularHasType (.snoc Γ A) body B →
      RegularHasType Γ (.lam body) (.pi A B)
  | app_elim {Γ : Ctx n} {f a A : PureTm n} {B : PureTm (n + 1)} :
      RegularHasType Γ A .u1 →
      RegularHasType Γ f (.pi A B) →
      RegularHasType Γ a A →
      RegularHasType (.snoc Γ A) B .u1 →
      RegularHasType Γ (.app f a) (inst0 a B)
  | pair_intro {Γ : Ctx n} {a b A : PureTm n} {B : PureTm (n + 1)} :
      RegularHasType Γ A .u1 →
      RegularHasType Γ a A →
      RegularHasType Γ b (inst0 a B) →
      RegularHasType (.snoc Γ A) B .u1 →
      RegularHasType Γ (.pair a b) (.sigma A B)
  | fst_elim {Γ : Ctx n} {p A : PureTm n} {B : PureTm (n + 1)} :
      RegularHasType Γ A .u1 →
      RegularHasType Γ p (.sigma A B) →
      RegularHasType (.snoc Γ A) B .u1 →
      RegularHasType Γ (.fst p) A
  | snd_elim {Γ : Ctx n} {p A : PureTm n} {B : PureTm (n + 1)} :
      RegularHasType Γ A .u1 →
      RegularHasType Γ p (.sigma A B) →
      RegularHasType (.snoc Γ A) B .u1 →
      RegularHasType Γ (.snd p) (inst0 (.fst p) B)
  | id_form {Γ : Ctx n} {A a b : PureTm n} :
      RegularHasType Γ A .u1 →
      RegularHasType Γ a A →
      RegularHasType Γ b A →
      RegularHasType Γ (.id A a b) .u1
  | refl_intro {Γ : Ctx n} {a A : PureTm n} :
      RegularHasType Γ A .u1 →
      RegularHasType Γ a A →
      RegularHasType Γ (.refl a) (.id A a a)
  /-- Conversion into an ordinary type.  The target-formation premise is the
  presupposition omitted by the two older authored conversion rules. -/
  | conv_type {Γ : Ctx n} {t A B : PureTm n} :
      RegularHasType Γ t A →
      RegularHasType Γ B .u1 →
      ConstantFreeConv A B →
      RegularHasType Γ t B
  /-- Conversion into the top sort is separated because `U1` has no type in
  this two-universe fragment. -/
  | conv_sort {Γ : Ctx n} {t A : PureTm n} :
      RegularHasType Γ t A →
      ConstantFreeConv A .u1 →
      RegularHasType Γ t .u1

/-- Forgetting the regularity witnesses recovers an authored intrinsic typing
derivation. -/
theorem RegularHasType.toHasType (h : RegularHasType Γ t A) :
    Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.HasType Γ t A := by
  induction h with
  | u0_type Γ => exact .u0_type Γ
  | var i => exact .var i
  | pi_form _ _ ihA ihB => exact .pi_form ihA ihB
  | sigma_form _ _ ihA ihB => exact .sigma_form ihA ihB
  | lam_intro _ _ _ ihA ihB ihBody => exact .lam_intro ihBody
  | app_elim _ _ _ _ ihA ihf iha ihB => exact .app_elim ihf iha
  | pair_intro _ _ _ _ ihA iha ihb ihB => exact .pair_intro iha ihb
  | fst_elim _ _ _ ihA ihp ihB => exact .fst_elim ihp
  | snd_elim _ _ _ ihA ihp ihB => exact .snd_elim ihp
  | id_form _ _ _ ihA iha ihb => exact .id_form ihA iha ihb
  | refl_intro _ _ ihA iha => exact .refl_intro iha
  | conv_type ht hB hconv iht ihB => exact .conv iht hconv.toConv
  | conv_sort ht hconv iht => exact .conv iht hconv.toConv

/-- In a declaration-free context, the whole regular typing derivation stays
inside the exact common syntax. -/
theorem RegularHasType.constantFree_both (h : RegularHasType Γ t A)
    (hΓ : ConstantFreeCtx Γ) : ConstantFree t ∧ ConstantFree A := by
  induction h with
  | u0_type => exact ⟨.u0, .u1⟩
  | var i => exact ⟨.var i, hΓ.lookup i⟩
  | pi_form hA hB ihA ihB =>
      have pA := ihA hΓ
      have pB := ihB ⟨hΓ, pA.1⟩
      exact ⟨.pi pA.1 pB.1, .u1⟩
  | sigma_form hA hB ihA ihB =>
      have pA := ihA hΓ
      have pB := ihB ⟨hΓ, pA.1⟩
      exact ⟨.sigma pA.1 pB.1, .u1⟩
  | lam_intro hA hB hBody ihA ihB ihBody =>
      have pA := ihA hΓ
      have pB := ihB ⟨hΓ, pA.1⟩
      have pBody := ihBody ⟨hΓ, pA.1⟩
      exact ⟨.lam pBody.1, .pi pA.1 pB.1⟩
  | app_elim hA hf ha hB ihA ihf iha ihB =>
      have pA := ihA hΓ
      have pf := ihf hΓ
      have pa := iha hΓ
      have pB := ihB ⟨hΓ, pA.1⟩
      exact ⟨.app pf.1 pa.1, ConstantFree.inst0 pa.1 pB.1⟩
  | pair_intro hA ha hb hB ihA iha ihb ihB =>
      have pA := ihA hΓ
      have pa := iha hΓ
      have pb := ihb hΓ
      have pB := ihB ⟨hΓ, pA.1⟩
      exact ⟨.pair pa.1 pb.1, .sigma pA.1 pB.1⟩
  | fst_elim hA hp hB ihA ihp ihB =>
      have pp := ihp hΓ
      cases pp.2 with
      | sigma hA hCod => exact ⟨.fst pp.1, hA⟩
  | snd_elim hA hp hB ihA ihp ihB =>
      have pA := ihA hΓ
      have pp := ihp hΓ
      cases pp.2 with
      | sigma hA hCod =>
          have pB := ihB ⟨hΓ, pA.1⟩
          exact ⟨.snd pp.1, ConstantFree.inst0 (.fst pp.1) pB.1⟩
  | id_form hA ha hb ihA iha ihb =>
      have pA := ihA hΓ
      have pa := iha hΓ
      have pb := ihb hΓ
      exact ⟨.id pA.1 pa.1 pb.1, .u1⟩
  | refl_intro hA ha ihA iha =>
      have pA := ihA hΓ
      have pa := iha hΓ
      exact ⟨.refl pa.1, .id pA.1 pa.1 pa.1⟩
  | conv_type ht hB hconv iht ihB =>
      have pt := iht hΓ
      have pB := ihB hΓ
      exact ⟨pt.1, pB.1⟩
  | conv_sort ht hconv iht =>
      have pt := iht hΓ
      exact ⟨pt.1, .u1⟩

/-! ### Context formation and the actual judgment boundary

`Ctx` remains useful raw syntax.  A kernel context is a telescope together
with a derivation that every extension is a type in the preceding context.
This blocks malformed assumptions before variable lookup can turn them into
apparently typed terms. -/

/-- Presupposition-closed context formation for the regular spine. -/
inductive RegularCtx : {n : Nat} → Ctx n → Prop where
  | nil : RegularCtx (.nil : Ctx 0)
  | snoc {Γ : Ctx n} {A : PureTm n} :
      RegularCtx Γ →
      RegularHasType Γ A .u1 →
      RegularCtx (.snoc Γ A)

/-- Every type stored in a regular context belongs to the exact common syntax.
The result follows from the context-formation derivations, rather than being
an independent side condition. -/
theorem RegularCtx.constantFreeCtx {Γ : Ctx n} (hΓ : RegularCtx Γ) :
    ConstantFreeCtx Γ := by
  induction hΓ with
  | nil => trivial
  | snoc hΓ hA ih =>
      exact ⟨ih, (hA.constantFree_both ih).1⟩

/-- Quotation faithfully represents regular intrinsic contexts.  Types in a
regular context are declaration-free, so the legacy context serializer agrees
with the injective structural quotation on every entry. -/
theorem quotePureCtx_injective
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hρ : Function.Injective ρ) (hcompat : QuoteCompat ν k ρ)
    {Γ Δ : Ctx n} (hΓ : RegularCtx Γ) (hΔ : RegularCtx Δ)
    (h : quotePureCtx ν k ρ Γ = quotePureCtx ν k ρ Δ) : Γ = Δ := by
  induction hΓ with
  | nil =>
      cases hΔ
      rfl
  | @snoc n Γ A hΓ hA ih =>
      cases hΔ with
      | @snoc _ Δ B hΔ hB =>
          let ρtail : QuoteEnv n := fun i => ρ i.succ
          have hρtail : Function.Injective ρtail := by
            intro i j hij
            exact Fin.succ_inj.mp (hρ hij)
          have hcompatTail : QuoteCompat ν k ρtail := by
            refine ⟨hcompat.1, ?_⟩
            intro i j hj
            exact hcompat.2 i.succ j hj
          have hparts := List.cons.inj h
          have htypes : quoteTmWith ν k ρtail A = quoteTmWith ν k ρtail B :=
            congrArg Prod.snd hparts.1
          have hcfΓ := RegularCtx.constantFreeCtx hΓ
          have hcfΔ := RegularCtx.constantFreeCtx hΔ
          have hAB := quoteTmWith_injective_of_constantFree hρtail hcompatTail
            (hA.constantFree_both hcfΓ).1 (hB.constantFree_both hcfΔ).1 htypes
          have hΓΔ := ih hρtail hcompatTail hΔ hparts.2
          exact congrArg₂ Ctx.snoc hΓΔ hAB

/-- A kernel judgment carries context formation, rather than accepting an
arbitrary raw telescope by convention. -/
structure RegularJudgment (Γ : Ctx n) (t A : PureTm n) : Prop where
  context : RegularCtx Γ
  typing : RegularHasType Γ t A

/-- Forgetting presupposition evidence yields the original permissive
intrinsic judgment. -/
theorem RegularJudgment.toHasType (h : RegularJudgment Γ t A) :
    Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.HasType Γ t A :=
  h.typing.toHasType

/-! ### Least rule closure, not a greatest fixpoint

The finite proof objects generated by the rules form an inductive least
closure.  Calling this a greatest fixpoint would incorrectly admit cyclic or
infinite derivations.  Calling it a coreflection additionally requires a
category of presentations and an adjunction; no such claim is made here. -/

/-- A universe-polymorphic intrinsic typing relation on the shared syntax. -/
abbrev TypingRelation :=
  {n : Nat} → Ctx n → PureTm n → PureTm n → Prop

/-- Pointwise inclusion between intrinsic typing relations. -/
def TypingRelation.LE (R S : TypingRelation) : Prop :=
  ∀ {n : Nat} {Γ : Ctx n} {t A : PureTm n}, R Γ t A → S Γ t A

/-- Closure under exactly the presupposition-complete regular rules. -/
structure RegularRuleModel (R : TypingRelation) where
  u0_type : ∀ {n : Nat} (Γ : Ctx n), R Γ .u0 .u1
  var : ∀ {n : Nat} {Γ : Ctx n} (i : Fin n), R Γ (.var i) (lookup Γ i)
  pi_form : ∀ {n : Nat} {Γ : Ctx n} {A : PureTm n} {B : PureTm (n + 1)},
    R Γ A .u1 → R (.snoc Γ A) B .u1 → R Γ (.pi A B) .u1
  sigma_form : ∀ {n : Nat} {Γ : Ctx n} {A : PureTm n} {B : PureTm (n + 1)},
    R Γ A .u1 → R (.snoc Γ A) B .u1 → R Γ (.sigma A B) .u1
  lam_intro : ∀ {n : Nat} {Γ : Ctx n} {A : PureTm n}
      {body B : PureTm (n + 1)},
    R Γ A .u1 → R (.snoc Γ A) B .u1 → R (.snoc Γ A) body B →
      R Γ (.lam body) (.pi A B)
  app_elim : ∀ {n : Nat} {Γ : Ctx n} {f a A : PureTm n}
      {B : PureTm (n + 1)},
    R Γ A .u1 → R Γ f (.pi A B) → R Γ a A → R (.snoc Γ A) B .u1 →
      R Γ (.app f a) (inst0 a B)
  pair_intro : ∀ {n : Nat} {Γ : Ctx n} {a b A : PureTm n}
      {B : PureTm (n + 1)},
    R Γ A .u1 → R Γ a A → R Γ b (inst0 a B) →
      R (.snoc Γ A) B .u1 →
      R Γ (.pair a b) (.sigma A B)
  fst_elim : ∀ {n : Nat} {Γ : Ctx n} {p A : PureTm n}
      {B : PureTm (n + 1)},
    R Γ A .u1 → R Γ p (.sigma A B) → R (.snoc Γ A) B .u1 →
      R Γ (.fst p) A
  snd_elim : ∀ {n : Nat} {Γ : Ctx n} {p A : PureTm n}
      {B : PureTm (n + 1)},
    R Γ A .u1 → R Γ p (.sigma A B) → R (.snoc Γ A) B .u1 →
      R Γ (.snd p) (inst0 (.fst p) B)
  id_form : ∀ {n : Nat} {Γ : Ctx n} {A a b : PureTm n},
    R Γ A .u1 → R Γ a A → R Γ b A → R Γ (.id A a b) .u1
  refl_intro : ∀ {n : Nat} {Γ : Ctx n} {a A : PureTm n},
    R Γ A .u1 → R Γ a A → R Γ (.refl a) (.id A a a)
  conv_type : ∀ {n : Nat} {Γ : Ctx n} {t A B : PureTm n},
    R Γ t A → R Γ B .u1 →
      ConstantFreeConv A B → R Γ t B
  conv_sort : ∀ {n : Nat} {Γ : Ctx n} {t A : PureTm n},
    R Γ t A →
      ConstantFreeConv A .u1 → R Γ t .u1

/-- The regular judgment is contained in every relation closed under its
rules.  This is its precise least-closure/initial-algebra property. -/
theorem RegularHasType.least {R : TypingRelation} (model : RegularRuleModel R) :
    TypingRelation.LE (fun Γ t A => RegularHasType Γ t A) R := by
  intro n Γ t A derivation
  induction derivation with
  | u0_type Γ => exact model.u0_type Γ
  | var i => exact model.var i
  | pi_form hA hB ihA ihB => exact model.pi_form ihA ihB
  | sigma_form hA hB ihA ihB => exact model.sigma_form ihA ihB
  | lam_intro hA hB hBody ihA ihB ihBody =>
      exact model.lam_intro ihA ihB ihBody
  | app_elim hA hf ha hB ihA ihf iha ihB =>
      exact model.app_elim ihA ihf iha ihB
  | pair_intro hA ha hb hB ihA iha ihb ihB =>
      exact model.pair_intro ihA iha ihb ihB
  | fst_elim hA hp hB ihA ihp ihB => exact model.fst_elim ihA ihp ihB
  | snd_elim hA hp hB ihA ihp ihB => exact model.snd_elim ihA ihp ihB
  | id_form hA ha hb ihA iha ihb => exact model.id_form ihA iha ihb
  | refl_intro hA ha ihA iha => exact model.refl_intro ihA iha
  | conv_type ht hB hconv iht ihB => exact model.conv_type iht ihB hconv
  | conv_sort ht hconv iht => exact model.conv_sort iht hconv

/-! ## Positive and negative typing witnesses -/

/-- The regular spine contains the ordinary identity function. -/
theorem regular_identity :
    RegularHasType (.nil : Ctx 0) (.lam (.var 0)) (.pi .u0 .u0) := by
  exact .lam_intro (.u0_type .nil) (.u0_type _) (.var 0)

/-- The original raw judgment permits a lambda over `U1`, even though `U1`
has no type in this two-universe kernel. -/
theorem raw_allows_untyped_lambda_domain :
    Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.HasType (.nil : Ctx 0)
      (.lam (.var 0)) (.pi .u1 .u1) := by
  apply Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.HasType.lam_intro
  exact Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.HasType.var 0

theorem RegularHasType.subject_ne_u1 (h : RegularHasType Γ t A) : t ≠ .u1 := by
  induction h <;> simp_all

theorem no_regular_u1_term {Γ : Ctx n} {A : PureTm n}
    (h : RegularHasType Γ .u1 A) : False :=
  h.subject_ne_u1 rfl

/-- A Pi whose domain is the untyped top sort cannot itself be assigned any
type by the regular rules.  Conversion cannot conceal the missing premise:
its source derivation is structurally smaller, and conversion into an
ordinary target separately requires target formation. -/
theorem RegularHasType.subject_ne_pi_u1_domain
    (h : RegularHasType Γ t A) : t ≠ (.pi .u1 .u1) := by
  induction h with
  | pi_form hDom hCod ihDom ihCod =>
      intro equal
      cases equal
      exact hDom.subject_ne_u1 rfl
  | conv_type ht hB hconv iht ihB => exact iht
  | conv_sort ht hconv iht => exact iht
  | u0_type => simp
  | var => simp
  | sigma_form => simp
  | lam_intro => simp
  | app_elim => simp
  | pair_intro => simp
  | fst_elim => simp
  | snd_elim => simp
  | id_form => simp
  | refl_intro => simp

theorem no_regular_pi_u1_domain {Γ : Ctx n} {A : PureTm n}
    (h : RegularHasType Γ (.pi .u1 .u1) A) : False :=
  h.subject_ne_pi_u1_domain rfl

/-- A lambda whose body is the untyped top sort cannot be assigned a type by
the regular rules. -/
theorem RegularHasType.subject_ne_lam_u1
    (h : RegularHasType Γ t A) : t ≠ (.lam .u1) := by
  induction h with
  | lam_intro hDom hCod hBody ihDom ihCod ihBody =>
      intro equal
      cases equal
      exact hBody.subject_ne_u1 rfl
  | conv_type ht hB hconv iht ihB => exact iht
  | conv_sort ht hconv iht => exact iht
  | u0_type => simp
  | var => simp
  | pi_form => simp
  | sigma_form => simp
  | app_elim => simp
  | pair_intro => simp
  | fst_elim => simp
  | snd_elim => simp
  | id_form => simp
  | refl_intro => simp

/-- Consequently the beta-redex whose function is that malformed lambda
cannot itself be assigned a type by the regular rules. -/
theorem RegularHasType.subject_ne_untyped_beta_redex
    (h : RegularHasType Γ t A) :
    t ≠ (.app (.lam .u1) .u0) := by
  induction h with
  | app_elim hA hf ha hB ihA ihf iha ihB =>
      intro equal
      cases equal
      exact hf.subject_ne_lam_u1 rfl
  | conv_type ht hB hconv iht ihB => exact iht
  | conv_sort ht hconv iht => exact iht
  | u0_type => simp
  | var => simp
  | pi_form => simp
  | sigma_form => simp
  | lam_intro => simp
  | pair_intro => simp
  | fst_elim => simp
  | snd_elim => simp
  | id_form => simp
  | refl_intro => simp

/-- An exact common-fragment term which is definitionally equal to `U1`, but
is not itself a well-formed type. -/
def untypedBetaType : PureTm 0 :=
  .app (.lam .u1) .u0

theorem untypedBetaType_not_formed :
    ¬ RegularHasType (.nil : Ctx 0) untypedBetaType .u1 := by
  intro h
  exact h.subject_ne_untyped_beta_redex rfl

/-- The regular kernel cannot type `U0` at the unformed beta-redex type. -/
theorem regular_rejects_conversion_to_unformed_type :
    ¬ RegularHasType (.nil : Ctx 0) .u0 untypedBetaType := by
  intro h
  cases h with
  | conv_type ht hB hconv => exact untypedBetaType_not_formed hB

/-- The same ill-formed-domain derivation is rejected by the regular spine. -/
theorem regular_rejects_untyped_lambda_domain :
    ¬ RegularHasType (.nil : Ctx 0) (.lam (.var 0)) (.pi .u1 .u1) := by
  intro h
  cases h with
  | lam_intro hA hB hBody => exact no_regular_u1_term hA
  | conv_type ht hB hconv => exact no_regular_pi_u1_domain hB

/-! ### Specification ablations

Each presupposition is separated by a positive inhabitant and a negative
witness.  This makes the choice of spine auditable rather than editorial. -/

/-- The smallest nonempty regular context. -/
theorem regularCtx_u0 : RegularCtx (.snoc .nil .u0) :=
  .snoc .nil (.u0_type .nil)

/-- The raw context syntax admits the top sort as an assumption. -/
def rawTopSortContext : Ctx 1 :=
  .snoc .nil .u1

/-- Raw variable typing consumes that malformed assumption without checking
its presupposition. -/
theorem raw_types_variable_in_top_sort_context :
    Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.HasType
      rawTopSortContext (.var 0) .u1 := by
  simpa [rawTopSortContext, rename] using
    (Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.HasType.var
      (Γ := rawTopSortContext) (i := (0 : Fin 1)))

/-- Context formation rejects the same raw telescope. -/
theorem rawTopSortContext_not_regular : ¬ RegularCtx rawTopSortContext := by
  intro regular
  cases regular with
  | snoc hnil hTop => exact no_regular_u1_term hTop

/-- Consequently the malformed variable fact cannot cross the actual kernel
judgment boundary even though the underlying raw typing proposition holds. -/
theorem no_regular_judgment_in_top_sort_context :
    ¬ RegularJudgment rawTopSortContext (.var 0) .u1 := by
  intro judgment
  exact rawTopSortContext_not_regular judgment.context

/-- Positive nondegeneracy witness at the full judgment boundary. -/
theorem regular_identity_judgment :
    RegularJudgment (.nil : Ctx 0) (.lam (.var 0)) (.pi .u0 .u0) :=
  ⟨.nil, regular_identity⟩

/-- The permissive authored relation is a model of every regular rule after
presupposition evidence is forgotten. -/
def rawRegularRuleModel : RegularRuleModel
    (fun Γ t A =>
      Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.HasType Γ t A) where
  u0_type := fun Γ => .u0_type Γ
  var := fun i => .var i
  pi_form := fun hA hB => .pi_form hA hB
  sigma_form := fun hA hB => .sigma_form hA hB
  lam_intro := fun _hA _hB hBody => .lam_intro hBody
  app_elim := fun _hA hf ha _hB => .app_elim hf ha
  pair_intro := fun _hA ha hb _hB => .pair_intro ha hb
  fst_elim := fun _hA hp _hB => .fst_elim hp
  snd_elim := fun _hA hp _hB => .snd_elim hp
  id_form := fun hA ha hb => .id_form hA ha hb
  refl_intro := fun _hA ha => .refl_intro ha
  conv_type := fun ht _hB hconv => .conv ht hconv.toConv
  conv_sort := fun ht hconv => .conv ht hconv.toConv

/-- The forgetful inclusion follows from least rule closure, independently of
the hand-written structural proof above. -/
theorem regular_le_raw : TypingRelation.LE
    (fun Γ t A => RegularHasType Γ t A)
    (fun Γ t A =>
      Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.HasType Γ t A) :=
  RegularHasType.least rawRegularRuleModel

/-- The inclusion is strict: raw typing contains a concrete derivation that
the presupposition-closed relation rejects. -/
theorem raw_not_le_regular : ¬ TypingRelation.LE
    (fun Γ t A =>
      Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.HasType Γ t A)
    (fun Γ t A => RegularHasType Γ t A) := by
  intro inclusion
  exact regular_rejects_untyped_lambda_domain
    (inclusion raw_allows_untyped_lambda_domain)

/-- Exact ablation result for rule presuppositions: the regular relation is a
proper subrelation of the permissive authored relation. -/
theorem regular_strictly_below_raw :
    TypingRelation.LE
        (fun Γ t A => RegularHasType Γ t A)
        (fun Γ t A =>
          Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.HasType Γ t A) ∧
      ¬ TypingRelation.LE
        (fun Γ t A =>
          Mettapedia.Languages.MeTTa.Pure.Intrinsic.Typing.HasType Γ t A)
        (fun Γ t A => RegularHasType Γ t A) :=
  ⟨regular_le_raw, raw_not_le_regular⟩

end Mettapedia.Languages.MeTTa.Pure.Intrinsic.PresentationBoundary
