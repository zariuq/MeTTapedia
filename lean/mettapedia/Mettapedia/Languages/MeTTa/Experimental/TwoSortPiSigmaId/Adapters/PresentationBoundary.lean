import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.PermissiveComparison
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.Inst0BridgeDerived
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular.Typing
import Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.SubjectReduction

/-!
# The intrinsic/Pattern two-sort presentation boundary

The intrinsic `TwoSortPiSigmaId` syntax contains global declaration constants, while
the locally nameless Pattern presentation deliberately does not.  Moreover,
the two authored typing judgments have different rule premises: Pattern two-sort
records domain/codomain regularity at eliminations, while the original
`TwoSortPiSigmaId.HasType` rules omit several of those premises.

The regular typing spine is defined independently in
`TypeTheory.Calculi.TwoSortPiSigmaId.Regular.Typing`. This adapter supplies its
Pattern quotation boundary and comparisons with the permissive intrinsic
judgment. In particular, it does not identify the two typing judgments.
-/

namespace Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Core
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.BinderOps
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Fragment
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.Typing
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Pattern.SubjectReduction
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Context
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution
open Mettapedia.Languages.MeTTa.Experimental.TwoSortPiSigmaId.Adapters.PatternBridge

/-! ## Quotation of declaration-free syntax -/

/-- Quotation maps every declaration-free intrinsic term into Pattern two-sort. -/
theorem quoteTmWith_twoSort {t : ScopedTerm n} (h : ConstantFree t) (ν : Nat → String)
    (k : Nat) (ρ : QuoteEnv n) : TwoSortTermPattern (quoteTmWith ν k ρ t) := by
  induction h generalizing k with
  | var i => exact .fvar (ρ i)
  | u0 => exact .u0
  | u1 => exact .u1
  | pi _ _ ihA ihB =>
      exact .pi (ihA k ρ)
        (twoSortTm_closeBVar (ν k) (ihB (k + 1) (envCons (ν k) ρ)))
  | sigma _ _ ihA ihB =>
      exact .sigma (ihA k ρ)
        (twoSortTm_closeBVar (ν k) (ihB (k + 1) (envCons (ν k) ρ)))
  | id _ _ _ ihA iha ihb => exact .id (ihA k ρ) (iha k ρ) (ihb k ρ)
  | lam _ ih =>
      exact .lam (twoSortTm_closeBVar (ν k) (ih (k + 1) (envCons (ν k) ρ)))
  | app _ _ ihf iha => exact .app (ihf k ρ) (iha k ρ)
  | pair _ _ iha ihb => exact .pair (iha k ρ) (ihb k ρ)
  | fst _ ih => exact .fst (ih k ρ)
  | snd _ ih => exact .snd (ih k ρ)
  | refl _ ih => exact .refl (ih k ρ)

/-- The legacy string quote is not an exact syntax embedding: a declaration
whose printed name is a reserved two-sort constructor collides with that
constructor.  This positive witness prevents an exact-image theorem from being
claimed for `quoteTmWith` itself. -/
theorem legacy_quoteConst_u0_collision (c : DeclName)
    (hc : c.toString = "U0") : quoteConst c = u0 := by
  simp [quoteConst, u0, hc]

theorem legacy_quoteConst_u0_is_twoSort (c : DeclName)
    (hc : c.toString = "U0") : TwoSortTermPattern (quoteConst c) := by
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
  | 0 => .apply "TwoSortPiSigmaId.name.nat.zero" []
  | n + 1 => .apply "TwoSortPiSigmaId.name.nat.succ" [quoteNameNat n]

/-- Structural encoding of Lean declaration names.  String components remain
literal Pattern labels, while nesting and numeric components remain explicit
constructors. -/
def quoteDeclName : DeclName → Pattern
  | .anonymous => .apply "TwoSortPiSigmaId.name.anonymous" []
  | .str pre component =>
      .apply "TwoSortPiSigmaId.name.str" [quoteDeclName pre, .apply component []]
  | .num pre component =>
      .apply "TwoSortPiSigmaId.name.num" [quoteDeclName pre, quoteNameNat component]

def quoteTaggedConst (c : DeclName) : Pattern :=
  .apply "TwoSortPiSigmaId.const" [quoteDeclName c]

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

def quoteExactWith (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n) : ScopedTerm n → Pattern
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
  | .apply name _ => name == "TwoSortPiSigmaId.const"
  | _ => false

theorem twoSort_isTaggedConst_false {p : Pattern} (h : TwoSortTermPattern p) :
    isTaggedConst p = false := by
  induction h <;>
    simp [isTaggedConst, u0, u1, mkPi, mkSigma, mkId, mkLam, mkApp, mkPair,
      mkFst, mkSnd, mkRefl]

theorem quoteTaggedConst_not_twoSort (c : DeclName) :
    ¬ TwoSortTermPattern (quoteTaggedConst c) := by
  intro h
  have hfalse := twoSort_isTaggedConst_false h
  simp [quoteTaggedConst, isTaggedConst] at hfalse

theorem lc_quoteExactWith (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n)
    (t : ScopedTerm n) : lc_at 0 (quoteExactWith ν k ρ t) = true := by
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

theorem quoteExactWith_twoSort {t : ScopedTerm n} (h : ConstantFree t)
    (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n) :
    TwoSortTermPattern (quoteExactWith ν k ρ t) := by
  induction h generalizing k with
  | var i => exact .fvar (ρ i)
  | u0 => exact .u0
  | u1 => exact .u1
  | pi _ _ ihA ihB =>
      exact .pi (ihA k ρ)
        (twoSortTm_closeBVar (ν k) (ihB (k + 1) (envCons (ν k) ρ)))
  | sigma _ _ ihA ihB =>
      exact .sigma (ihA k ρ)
        (twoSortTm_closeBVar (ν k) (ihB (k + 1) (envCons (ν k) ρ)))
  | id _ _ _ ihA iha ihb => exact .id (ihA k ρ) (iha k ρ) (ihb k ρ)
  | lam _ ih =>
      exact .lam (twoSortTm_closeBVar (ν k) (ih (k + 1) (envCons (ν k) ρ)))
  | app _ _ ihf iha => exact .app (ihf k ρ) (iha k ρ)
  | pair _ _ iha ihb => exact .pair (iha k ρ) (ihb k ρ)
  | fst _ ih => exact .fst (ih k ρ)
  | snd _ ih => exact .snd (ih k ρ)
  | refl _ ih => exact .refl (ih k ρ)

/-- On the common fragment, the collision-free quote is byte-for-byte the
existing artifact quote.  Existing clients therefore need no migration for
terms that actually belong to Pattern two-sort. -/
theorem quoteExactWith_eq_quoteTmWith {t : ScopedTerm n} (h : ConstantFree t)
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
    {t u : ScopedTerm n} (ht : ConstantFree t) (hu : ConstantFree u)
    (h : quoteTmWith ν k ρ t = quoteTmWith ν k ρ u) : t = u := by
  apply quoteExactWith_injective hρ hcompat
  rw [quoteExactWith_eq_quoteTmWith ht, quoteExactWith_eq_quoteTmWith hu]
  exact h

private theorem twoSort_closed_exact_body
    (x : String) (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n) (body : ScopedTerm n)
    (hclosed : TwoSortTermPattern (closeFVar 0 x (quoteExactWith ν k ρ body))) :
    TwoSortTermPattern (quoteExactWith ν k ρ body) := by
  have hopen : TwoSortTermPattern
      (openBVar 0 (.fvar x)
        (closeFVar 0 x (quoteExactWith ν k ρ body))) :=
    twoSortTm_openBVar_fvar x (k := 0) hclosed
  have hround :
      openBVar 0 (.fvar x)
          (closeFVar 0 x (quoteExactWith ν k ρ body)) =
        quoteExactWith ν k ρ body :=
    openBVar_closeBVar_cancel (lc_quoteExactWith ν k ρ body)
  rwa [hround] at hopen

/-- The tagged quotation has the exact constant-free fragment as its Pattern
two-sort image. -/
theorem twoSort_quoteExactWith_iff (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n)
    (t : ScopedTerm n) :
    TwoSortTermPattern (quoteExactWith ν k ρ t) ↔ ConstantFree t := by
  constructor
  · intro h
    induction t generalizing k with
    | var i => exact .var i
    | const c => exact False.elim (quoteTaggedConst_not_twoSort c h)
    | u0 => exact .u0
    | u1 => exact .u1
    | pi A B ihA ihB =>
        have hAB := twoSort_pi_inv h
        have hBody := twoSort_closed_exact_body (ν k) ν (k + 1) (envCons (ν k) ρ) B hAB.2
        exact .pi (ihA k ρ hAB.1) (ihB (k + 1) (envCons (ν k) ρ) hBody)
    | sigma A B ihA ihB =>
        have hAB := twoSort_sigma_inv h
        have hBody := twoSort_closed_exact_body (ν k) ν (k + 1) (envCons (ν k) ρ) B hAB.2
        exact .sigma (ihA k ρ hAB.1) (ihB (k + 1) (envCons (ν k) ρ) hBody)
    | id A a b ihA iha ihb =>
        have hab := twoSort_id_inv h
        exact .id (ihA k ρ hab.1) (iha k ρ hab.2.1) (ihb k ρ hab.2.2)
    | lam body ih =>
        have hBody := twoSort_closed_exact_body (ν k) ν (k + 1) (envCons (ν k) ρ) body
          (twoSort_lam_inv h)
        exact .lam (ih (k + 1) (envCons (ν k) ρ) hBody)
    | app f a ihf iha =>
        have hfa := twoSort_app_inv h
        exact .app (ihf k ρ hfa.1) (iha k ρ hfa.2)
    | pair a b iha ihb =>
        have hab := twoSort_pair_inv h
        exact .pair (iha k ρ hab.1) (ihb k ρ hab.2)
    | fst p ih => exact .fst (ih k ρ (twoSort_fst_inv h))
    | snd p ih => exact .snd (ih k ρ (twoSort_snd_inv h))
    | refl a ih => exact .refl (ih k ρ (twoSort_refl_inv h))
  · exact fun h => quoteExactWith_twoSort h ν k ρ

/-! ## Context presentation -/

/-- The locally nameless association-list presentation of an intrinsic
telescope.  The most recent intrinsic variable becomes the head entry. -/
def quoteTwoSortCtx (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n) : Ctx n → TwoSortCtx
  | .nil => []
  | .snoc Γ A =>
      let ρprev : QuoteEnv _ := fun i => ρ i.succ
      (ρ 0, quoteTmWith ν k ρprev A) :: quoteTwoSortCtx ν k ρprev Γ

@[simp] theorem quoteTwoSortCtx_nil (ν : Nat → String) (k : Nat) :
    quoteTwoSortCtx ν k emptyEnv .nil = [] := rfl

@[simp] theorem quoteTwoSortCtx_snoc (ν : Nat → String) (k : Nat)
    (ρ : QuoteEnv (n + 1)) (Γ : Ctx n) (A : ScopedTerm n) :
    quoteTwoSortCtx ν k ρ (.snoc Γ A) =
      (ρ 0, quoteTmWith ν k (fun i => ρ i.succ) A) ::
        quoteTwoSortCtx ν k (fun i => ρ i.succ) Γ := rfl

/-- Intrinsic lookup is represented by association-list membership after
quotation. -/
theorem quote_lookup_mem (ν : Nat → String) (k : Nat) (ρ : QuoteEnv n)
    (Γ : Ctx n) (i : Fin n) :
    (ρ i, quoteTmWith ν k ρ (lookup Γ i)) ∈ quoteTwoSortCtx ν k ρ Γ := by
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
    (hcompatL : QuoteCompat ν l ρ) (t : ScopedTerm n) :
    quoteTmWith ν k ρ t = quoteTmWith ν l ρ t :=
  Inst0BridgeProof.quoteTmWith_depth_indep_staging
    ν k l ρ t hcompatK hcompatL

/-- Telescope quotation inherits term-level binder-depth independence. -/
theorem quoteTwoSortCtx_depth_indep {ν : Nat → String} {k l : Nat}
    {ρ : QuoteEnv n} (hcompatK : QuoteCompat ν k ρ)
    (hcompatL : QuoteCompat ν l ρ) (Γ : Ctx n) :
    quoteTwoSortCtx ν k ρ Γ = quoteTwoSortCtx ν l ρ Γ := by
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
      simp only [quoteTwoSortCtx_snoc]
      rw [quoteTmWith_depth_indep hKtail hLtail A]
      rw [ih hKtail hLtail]

/-- Every name in the quoted context is supplied by its quote environment. -/
theorem quoteTwoSortCtx_ctxNames_mem_env (ν : Nat → String) (k : Nat)
    (ρ : QuoteEnv n) (Γ : Ctx n) {z : String} :
    z ∈ ctxNames (quoteTwoSortCtx ν k ρ Γ) → ∃ i : Fin n, ρ i = z := by
  induction Γ with
  | nil => simp [quoteTwoSortCtx, ctxNames]
  | @snoc n Γ A ih =>
      intro hz
      simp only [quoteTwoSortCtx_snoc, ctxNames_cons, List.mem_cons] at hz
      rcases hz with hz | hz
      · exact ⟨0, hz.symm⟩
      · rcases ih (ρ := fun i => ρ i.succ) hz with ⟨i, hi⟩
        exact ⟨i.succ, hi⟩

/-- The current canonical binder name is absent from a compatible quoted
context. -/
theorem quoteTwoSortCtx_current_not_mem_ctxNames
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ) (Γ : Ctx n) :
    ν k ∉ ctxNames (quoteTwoSortCtx ν k ρ Γ) := by
  intro hmem
  rcases quoteTwoSortCtx_ctxNames_mem_env ν k ρ Γ hmem with ⟨i, hi⟩
  exact hcompat.2 i k (by omega) hi

/-- The current canonical binder name is fresh in every type stored in a
compatible quoted context. -/
theorem quoteTwoSortCtx_current_fresh
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hcompat : QuoteCompat ν k ρ) (Γ : Ctx n) :
    ctxFresh (ν k) (quoteTwoSortCtx ν k ρ Γ) := by
  induction Γ with
  | nil =>
      intro y T hmem
      simp [quoteTwoSortCtx] at hmem
  | @snoc n Γ A ih =>
      let ρtail : QuoteEnv n := fun i => ρ i.succ
      have htail : QuoteCompat ν k ρtail := by
        refine ⟨hcompat.1, ?_⟩
        intro i j hj
        exact hcompat.2 i.succ j hj
      intro y T hmem
      rw [quoteTwoSortCtx_snoc] at hmem
      rcases List.mem_cons.mp hmem with hhead | hrest
      · cases hhead
        exact isFresh_quoteTmWith_future htail A (j := k) (by omega)
      · exact ih htail y T hrest

/-- A concrete raw conversion path can leave the common fragment even when
its endpoints lie in the two-sort fragment. This witnesses a proof-fibre mismatch; it does not
claim the endpoint propositions differ. -/
def rawConstantDetour (c : DeclName) : ScopedTerm 0 :=
  .app (.lam .u0) (.const c)

theorem rawConstantDetour_not_constantFree (c : DeclName) :
    ¬ ConstantFree (rawConstantDetour c) := by
  intro h
  cases h with
  | app hlam hconst => cases hconst

theorem rawConstantDetour_reduces (c : DeclName) :
    Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Reduction.Red
      (rawConstantDetour c) .u0 := by
  simpa [rawConstantDetour, inst0, subst, subst0] using
    (Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Reduction.Red.betaPi
      (.u0 : ScopedTerm 1) (.const c : ScopedTerm 0))

theorem raw_conversion_has_imtwoSort_detour (c : DeclName) :
    ∃ middle : ScopedTerm 0,
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.Conv .u0 middle ∧
      Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing.Conv middle .u0 ∧
      ¬ ConstantFree middle := by
  refine ⟨rawConstantDetour c, ?_, ?_, rawConstantDetour_not_constantFree c⟩
  · exact Relation.EqvGen.symm _ _
      (Relation.EqvGen.rel _ _ (rawConstantDetour_reduces c))
  · exact Relation.EqvGen.rel _ _ (rawConstantDetour_reduces c)

/-- The imtwoSort intermediate term cannot occur as an endpoint of the
fragment-internal conversion relation.  Together with
`raw_conversion_has_imtwoSort_detour`, this separates raw endpoint equality from
the exact conversion proof fibre used by the presentation bridge. -/
theorem rawConstantDetour_not_fragment_endpoint (c : DeclName) :
    ¬ ConstantFreeConv (.u0 : ScopedTerm 0) (rawConstantDetour c) := by
  intro h
  exact rawConstantDetour_not_constantFree c h.constantFree_both.2

/-- Quotation faithfully represents regular intrinsic contexts.  Types in a
regular context are declaration-free, so the legacy context serializer agrees
with the injective structural quotation on every entry. -/
theorem quoteTwoSortCtx_injective
    {ν : Nat → String} {k : Nat} {ρ : QuoteEnv n}
    (hρ : Function.Injective ρ) (hcompat : QuoteCompat ν k ρ)
    {Γ Δ : Ctx n} (hΓ : RegularCtx Γ) (hΔ : RegularCtx Δ)
    (h : quoteTwoSortCtx ν k ρ Γ = quoteTwoSortCtx ν k ρ Δ) : Γ = Δ := by
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


end Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Regular
