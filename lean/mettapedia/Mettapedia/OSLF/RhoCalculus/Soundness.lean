import Mettapedia.OSLF.RhoCalculus.Types
import Mettapedia.OSLF.RhoCalculus.Reduction
import Mettapedia.OSLF.MeTTaIL.Substitution
import Mettapedia.CategoryTheory.Topos.InternalLanguage
import Mathlib.Data.Fintype.EquivFin

/-!
# Type Soundness for ρ-Calculus (Locally Nameless)

This file formalizes the key soundness theorem from OSLF:
type preservation under substitution (substitutability).

Uses locally nameless representation: bound variables are de Bruijn indices,
free variables are named strings. The `HasType.input` rule uses cofinite
quantification following Aydemir et al. (POPL 2008).

## The Substitutability Theorem

If Γ, x:σ ⊢ p : τ and Γ ⊢ q : σ then Γ ⊢ p[q/x] : τ

## References

- Meredith & Stay, "Operational Semantics in Logical Form" Theorem 1
- Williams & Stay, "Native Type Theory" (ACT 2021)
- Aydemir et al., "Engineering Formal Metatheory" (POPL 2008)
-/

namespace Mettapedia.OSLF.RhoCalculus.Soundness

open Mettapedia.OSLF.RhoCalculus
open Mettapedia.OSLF.RhoCalculus.Reduction
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.CategoryTheory.LambdaTheories

-- Modal operators from operational semantics
local notation "possibly" => possiblyProp
local notation "rely" => relyProp

/-! ## Typing Contexts -/

/-- A native type is a pair of sort and predicate -/
structure NativeType where
  /-- The sort (Proc or Name) -/
  sort : String
  /-- The predicate (truth value in fiber) -/
  predicate : ProcPred
  /-- Sort must be valid -/
  sort_valid : sort ∈ ["Proc", "Name"]

/-- A typing context maps variable names to native types -/
def TypingContext := List (String × NativeType)

namespace TypingContext

/-- Empty context -/
def empty : TypingContext := []

/-- Extend context with a binding -/
def extend (Γ : TypingContext) (x : String) (τ : NativeType) : TypingContext :=
  (x, τ) :: Γ

/-- Look up a variable's type -/
def lookup (Γ : TypingContext) (x : String) : Option NativeType :=
  match Γ.find? (fun p => p.1 == x) with
  | some (_, τ) => some τ
  | none => none

/-- Check if a variable is bound -/
def isBound (Γ : TypingContext) (x : String) : Bool :=
  (Γ.find? (fun p => p.1 == x)).isSome

end TypingContext

/-! ## Fresh String -/

/-- There exists a string not in any given finite list. -/
private theorem exists_fresh (L : List String) : ∃ z : String, z ∉ L := by
  have h := Infinite.exists_notMem_finset (α := String) L.toFinset
  obtain ⟨z, hz⟩ := h
  exact ⟨z, fun hmem => hz (List.mem_toFinset.mpr hmem)⟩

/-! ## Type Judgments (Locally Nameless)

The `input` rule uses **cofinite quantification**: there exists a finite set L
of "bad" names, and for any z not in L, the body types after opening with z.
-/

/-- Type judgment: Γ ⊢ p : τ -/
inductive HasType : TypingContext → Pattern → NativeType → Prop where
  /-- Free variable rule: Γ ⊢ x : τ when Γ(x) = τ -/
  | fvar {Γ : TypingContext} {x : String} {τ : NativeType} :
      Γ.lookup x = some τ → HasType Γ (.fvar x) τ

  /-- Nil process: Γ ⊢ 0 : (Proc, ⊤) -/
  | nil {Γ : TypingContext} :
      HasType Γ (.apply "PZero" []) ⟨"Proc", fun _ => True, by simp⟩

  /-- Quote: Γ ⊢ p : (Proc, φ) → Γ ⊢ @p : (Name, ◇φ) -/
  | quote {Γ : TypingContext} {p : Pattern} {φ : ProcPred} :
      HasType Γ p ⟨"Proc", φ, by simp⟩ →
      HasType Γ (.apply "NQuote" [p]) ⟨"Name", possibly φ, by simp⟩

  /-- Drop: Γ ⊢ n : (Name, α) → Γ ⊢ *n : (Proc, ⧫α) -/
  | drop {Γ : TypingContext} {n : Pattern} {α : NamePred} :
      HasType Γ n ⟨"Name", α, by simp⟩ →
      HasType Γ (.apply "PDrop" [n]) ⟨"Proc", rely α, by simp⟩

  /-- Output: Γ ⊢ n : (Name, α), Γ ⊢ q : (Proc, φ) → Γ ⊢ n!(q) : (Proc, ⊤) -/
  | output {Γ : TypingContext} {n q : Pattern} {α : NamePred} {φ : ProcPred} :
      HasType Γ n ⟨"Name", α, by simp⟩ →
      HasType Γ q ⟨"Proc", φ, by simp⟩ →
      HasType Γ (.apply "POutput" [n, q]) ⟨"Proc", fun _ => True, by simp⟩

  /-- Input (cofinite): for all z outside a finite set L,
      opening the body with z gives a well-typed process. -/
  | input {Γ : TypingContext} {n : Pattern} {p : Pattern}
          {α : NamePred} {φ : ProcPred} (L : List String) :
      HasType Γ n ⟨"Name", α, by simp⟩ →
      (∀ z, z ∉ L →
        HasType (Γ.extend z ⟨"Name", α, by simp⟩) (openBVar 0 (.fvar z) p) ⟨"Proc", φ, by simp⟩) →
      HasType Γ (.apply "PInput" [n, .lambda p]) ⟨"Proc", fun _ => True, by simp⟩

  /-- Parallel: all elements must be well-typed processes -/
  | par {Γ : TypingContext} {ps : List Pattern} :
      (∀ p ∈ ps, HasType Γ p ⟨"Proc", fun _ => True, by simp⟩) →
      HasType Γ (.collection .hashBag ps none) ⟨"Proc", fun _ => True, by simp⟩

notation:40 Γ " ⊢ " p " : " τ => HasType Γ p τ

/-! ## Context Infrastructure -/

theorem lookup_extend_neq {Γ : TypingContext} {x y : String} {σ : NativeType}
    (hne : x ≠ y) : (Γ.extend x σ).lookup y = Γ.lookup y := by
  unfold TypingContext.extend TypingContext.lookup
  simp only [List.find?]
  have : (x == y) = false := beq_eq_false_iff_ne.mpr hne
  simp only [this]

theorem lookup_extend_eq {Γ : TypingContext} {x : String} {σ : NativeType} :
    (Γ.extend x σ).lookup x = some σ := by
  unfold TypingContext.extend TypingContext.lookup
  simp only [List.find?, beq_self_eq_true]

def TypingContext.LookupEquiv (Γ Γ' : TypingContext) : Prop :=
  ∀ x, Γ.lookup x = Γ'.lookup x

theorem TypingContext.LookupEquiv.refl (Γ : TypingContext) : Γ.LookupEquiv Γ :=
  fun _ => rfl

theorem TypingContext.LookupEquiv.symm {Γ Γ' : TypingContext} (h : Γ.LookupEquiv Γ') :
    Γ'.LookupEquiv Γ := fun x => (h x).symm

theorem TypingContext.LookupEquiv.trans {Γ₁ Γ₂ Γ₃ : TypingContext}
    (h₁₂ : Γ₁.LookupEquiv Γ₂) (h₂₃ : Γ₂.LookupEquiv Γ₃) : Γ₁.LookupEquiv Γ₃ :=
  fun x => (h₁₂ x).trans (h₂₃ x)

theorem TypingContext.LookupEquiv.extend {Γ Γ' : TypingContext} (h : Γ.LookupEquiv Γ')
    (x : String) (τ : NativeType) : (Γ.extend x τ).LookupEquiv (Γ'.extend x τ) := by
  intro z
  unfold TypingContext.extend TypingContext.lookup
  by_cases hzx : z = x
  · have hxz : (x == z) = true := beq_iff_eq.mpr hzx.symm
    simp only [List.find?, hxz]
  · have hne : (x == z) = false := beq_eq_false_iff_ne.mpr (Ne.symm hzx)
    simp only [List.find?, hne]
    exact h z

theorem HasType_context_equiv {Γ Γ' : TypingContext} {p : Pattern} {τ : NativeType}
    (hequiv : Γ.LookupEquiv Γ') (htype : Γ ⊢ p : τ) : Γ' ⊢ p : τ := by
  induction htype generalizing Γ' with
  | fvar hlookup =>
    apply HasType.fvar
    rw [← hequiv _]
    exact hlookup
  | nil => exact HasType.nil
  | quote _ ih => exact HasType.quote (ih hequiv)
  | drop _ ih => exact HasType.drop (ih hequiv)
  | output _ _ ih1 ih2 => exact HasType.output (ih1 hequiv) (ih2 hequiv)
  | @input _ n p' α φ L _ _ ih_n ih_body =>
    exact HasType.input L (ih_n hequiv) (fun z hz => ih_body z hz (hequiv.extend z _))
  | @par _ ps hps ih =>
    exact HasType.par (fun p hp => ih p hp hequiv)

theorem TypingContext.LookupEquiv.permute {Γ : TypingContext} {x y : String} {σ τ : NativeType}
    (hne : x ≠ y) : ((Γ.extend x σ).extend y τ).LookupEquiv ((Γ.extend y τ).extend x σ) := by
  intro z
  unfold TypingContext.extend TypingContext.lookup
  by_cases hzy : z = y
  · have hyz : (y == z) = true := beq_iff_eq.mpr hzy.symm
    have hxz : (x == z) = false := by rw [hzy]; exact beq_eq_false_iff_ne.mpr hne
    simp only [List.find?, hyz, hxz]
  · by_cases hzx : z = x
    · have hyz : (y == z) = false := beq_eq_false_iff_ne.mpr (Ne.symm hzy)
      have hxz : (x == z) = true := beq_iff_eq.mpr hzx.symm
      simp only [List.find?, hyz, hxz]
    · have hyz : (y == z) = false := beq_eq_false_iff_ne.mpr (Ne.symm hzy)
      have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr (Ne.symm hzx)
      simp only [List.find?, hyz, hxz]

theorem TypingContext.LookupEquiv.shadow {Γ : TypingContext} {x : String} {σ τ : NativeType} :
    ((Γ.extend x σ).extend x τ).LookupEquiv (Γ.extend x τ) := by
  intro z
  unfold TypingContext.extend TypingContext.lookup
  by_cases hzx : z = x
  · have hxz : (x == z) = true := beq_iff_eq.mpr hzx.symm
    simp only [List.find?, hxz]
  · have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr (Ne.symm hzx)
    simp only [List.find?, hxz]

/-! ## Freshness Helpers -/

theorem isFresh_apply_singleton {x : String} {c : String} {p : Pattern}
    (h : isFresh x (.apply c [p])) : isFresh x p := by
  simp only [isFresh, freeVars, List.flatMap_cons, List.flatMap_nil, List.append_nil] at h ⊢
  exact h

theorem isFresh_apply_pair {x : String} {c : String} {p q : Pattern}
    (h : isFresh x (.apply c [p, q])) : isFresh x p ∧ isFresh x q := by
  simp only [isFresh, freeVars, List.flatMap_cons, List.flatMap_nil,
             List.append_nil, List.contains_append, Bool.not_or,
             Bool.and_eq_true] at h
  simp only [isFresh]
  exact h

private theorem list_mem_of_contains {x : String} {L : List String}
    (h : L.contains x = true) : x ∈ L := by
  simp only [List.contains_iff_exists_mem_beq] at h
  obtain ⟨z, hz, hzx⟩ := h
  rwa [show z = x from (beq_iff_eq.mp hzx).symm] at hz

private theorem contains_of_list_mem {x : String} {L : List String}
    (h : x ∈ L) : L.contains x = true := by
  simp only [List.contains_iff_exists_mem_beq]
  exact ⟨x, h, beq_self_eq_true x⟩

theorem freeVars_openBVar_subset {k : Nat} {u : Pattern} {p : Pattern} {x : String}
    (hx : x ∈ freeVars (openBVar k u p)) : x ∈ freeVars p ∨ x ∈ freeVars u := by
  induction p using Pattern.inductionOn generalizing k with
  | hbvar n =>
    simp only [openBVar] at hx
    split at hx
    · exact Or.inr hx
    · simp only [freeVars] at hx; cases hx
  | hfvar name =>
    simp only [openBVar, freeVars] at hx ⊢
    exact Or.inl hx
  | happly c args ih =>
    simp only [openBVar, freeVars, List.mem_flatMap] at hx ⊢
    obtain ⟨mapped, hmapped, hx_in⟩ := hx
    rw [List.mem_map] at hmapped
    obtain ⟨a, ha, rfl⟩ := hmapped
    cases ih a ha hx_in with
    | inl h => exact Or.inl ⟨a, ha, h⟩
    | inr h => exact Or.inr h
  | hlambda body ih =>
    simp only [openBVar, freeVars] at hx ⊢
    exact ih hx
  | hmultiLambda n body ih =>
    simp only [openBVar, freeVars] at hx ⊢
    exact ih hx
  | hsubst body repl ihb ihr =>
    simp only [openBVar, freeVars, List.mem_append] at hx ⊢
    cases hx with
    | inl h =>
      cases ihb h with
      | inl h' => exact Or.inl (Or.inl h')
      | inr h' => exact Or.inr h'
    | inr h =>
      cases ihr h with
      | inl h' => exact Or.inl (Or.inr h')
      | inr h' => exact Or.inr h'
  | hcollection ct elems rest ih =>
    simp only [openBVar, freeVars, List.mem_flatMap] at hx ⊢
    obtain ⟨mapped, hmapped, hx_in⟩ := hx
    rw [List.mem_map] at hmapped
    obtain ⟨a, ha, rfl⟩ := hmapped
    cases ih a ha hx_in with
    | inl h => exact Or.inl ⟨a, ha, h⟩
    | inr h => exact Or.inr h

theorem isFresh_openBVar {x z : String} {p : Pattern} {k : Nat}
    (hfresh : isFresh x p = true) (hxz : x ≠ z) :
    isFresh x (openBVar k (.fvar z) p) = true := by
  simp only [isFresh, Bool.not_eq_true'] at hfresh ⊢
  rw [Bool.eq_false_iff] at hfresh ⊢
  intro habs
  have hx_mem := list_mem_of_contains habs
  cases freeVars_openBVar_subset hx_mem with
  | inl h => exact hfresh (contains_of_list_mem h)
  | inr h =>
    simp only [freeVars, List.mem_singleton] at h
    exact hxz h

/-! ## Weakening -/

theorem weakening {Γ : TypingContext} {p : Pattern} {τ : NativeType}
    {x : String} {σ : NativeType} :
    (Γ ⊢ p : τ) → isFresh x p → (Γ.extend x σ ⊢ p : τ) := by
  intro htype hfresh
  induction htype with
  | @fvar _ y _ hlookup =>
    apply HasType.fvar
    have hne : x ≠ y := isFresh_fvar_neq hfresh
    rw [lookup_extend_neq hne]
    exact hlookup
  | nil => exact HasType.nil
  | quote _ ih =>
    exact HasType.quote (ih (isFresh_apply_singleton hfresh))
  | drop _ ih =>
    exact HasType.drop (ih (isFresh_apply_singleton hfresh))
  | output _ _ ih1 ih2 =>
    have ⟨h1, h2⟩ := isFresh_apply_pair hfresh
    exact HasType.output (ih1 h1) (ih2 h2)
  | @input _ n p' α φ L hn hbody ih_n ih_body =>
    have ⟨hfresh_n, hfresh_lam⟩ := isFresh_apply_pair hfresh
    rw [isFresh_lambda_iff] at hfresh_lam
    refine @HasType.input _ _ _ α φ (x :: L) (ih_n hfresh_n) (fun z hz => ?_)
    simp only [List.mem_cons, not_or] at hz
    obtain ⟨hzx, hzL⟩ := hz
    by_cases hxx' : x = z
    · subst hxx'; exact absurd rfl hzx
    · have hfresh_opened : isFresh x (openBVar 0 (.fvar z) p') = true :=
        isFresh_openBVar hfresh_lam hxx'
      have hp' := ih_body z hzL hfresh_opened
      exact HasType_context_equiv (TypingContext.LookupEquiv.permute (Ne.symm hxx')) hp'
  | @par _ ps hps ih =>
    have hfresh_all : ∀ p ∈ ps, isFresh x p := by
      intro p hp
      exact isFresh_collection_mem hfresh hp
    exact HasType.par (fun p hp => ih p hp (hfresh_all p hp))

/-! ## Well-typed patterns have no explicit substitution -/

theorem HasType.noExplicitSubst {Γ : TypingContext} {p : Pattern} {τ : NativeType}
    (h : Γ ⊢ p : τ) : Mettapedia.OSLF.MeTTaIL.Substitution.noExplicitSubst p := by
  induction h with
  | fvar _ => rfl
  | nil => rfl
  | quote _ ih =>
    show allNoExplicitSubst [_] = true
    simp only [allNoExplicitSubst, ih, Bool.true_and]
  | drop _ ih =>
    show allNoExplicitSubst [_] = true
    simp only [allNoExplicitSubst, ih, Bool.true_and]
  | output _ _ ih1 ih2 =>
    show allNoExplicitSubst [_, _] = true
    simp only [allNoExplicitSubst, ih1, ih2, Bool.and_self]
  | @input _ n p' α φ L _ hbody ih_n ih_body =>
    show allNoExplicitSubst [_, .lambda _] = true
    simp only [allNoExplicitSubst, Mettapedia.OSLF.MeTTaIL.Substitution.noExplicitSubst,
               ih_n, Bool.true_and, Bool.and_true]
    obtain ⟨z, hz⟩ := exists_fresh L
    exact noExplicitSubst_of_openBVar (ih_body z hz)
  | @par _ ps hps ih =>
    show allNoExplicitSubst ps = true
    have hall : ∀ p ∈ ps, Mettapedia.OSLF.MeTTaIL.Substitution.noExplicitSubst p = true := ih
    clear ih hps
    induction ps with
    | nil => rfl
    | cons p ps' ih_ps =>
      simp only [allNoExplicitSubst]
      have hp := hall p (by simp)
      rw [hp]
      simp only [Bool.true_and]
      exact ih_ps (fun q hq => hall q (by simp; right; exact hq))

/-! ## Substitution Preserves Types -/

/-- Substitution preserves types.

    Uses the LookupEquiv generalization to handle the input case where
    extending the context produces a different list order. -/
theorem substitution_preserves_type
    {Γ : TypingContext} {p : Pattern} {τ : NativeType}
    (hptype : Γ ⊢ p : τ)
    {Γ₀ : TypingContext} {x : String} {q : Pattern} {σ : NativeType}
    (hctx : Γ.LookupEquiv (Γ₀.extend x σ))
    (hqtype : Γ₀ ⊢ q : σ)
    (hnes_q : Mettapedia.OSLF.MeTTaIL.Substitution.noExplicitSubst q = true)
    (hlc_q : lc q = true) :
    Γ₀ ⊢ applySubst (SubstEnv.extend SubstEnv.empty x q) p : τ := by
  induction hptype generalizing Γ₀ x q σ with
  | @fvar _ y _ hlookup =>
    simp only [applySubst]
    by_cases hxy : x = y
    · -- Substituting: x = y
      subst hxy
      simp only [SubstEnv.find_extend_empty_eq]
      -- hlookup : Γ✝.lookup x = some τ
      -- hctx x : Γ✝.lookup x = (Γ₀.extend x σ).lookup x
      -- lookup_extend_eq : (Γ₀.extend x σ).lookup x = some σ
      have h1 := hctx x
      rw [hlookup, lookup_extend_eq] at h1
      have hτσ := Option.some.inj h1
      subst hτσ; exact hqtype
    · -- Not substituting
      simp only [SubstEnv.find_extend_empty_ne hxy]
      apply HasType.fvar
      have hlookup' := hlookup
      rw [hctx y, lookup_extend_neq hxy] at hlookup'
      exact hlookup'
  | nil =>
    simp only [applySubst, List.map_nil]
    exact HasType.nil
  | @quote _ p' φ _ ih =>
    simp only [applySubst, List.map_cons, List.map_nil]
    exact HasType.quote (ih hctx hqtype hnes_q hlc_q)
  | @drop _ n' α _ ih =>
    simp only [applySubst, List.map_cons, List.map_nil]
    exact HasType.drop (ih hctx hqtype hnes_q hlc_q)
  | @output _ n' q' α φ _ _ ih_n ih_q =>
    simp only [applySubst, List.map_cons, List.map_nil]
    exact HasType.output (ih_n hctx hqtype hnes_q hlc_q) (ih_q hctx hqtype hnes_q hlc_q)
  | @input Γ_c n' p_body α φ L hn hbody ih_n ih_body =>
    simp only [applySubst, List.map_cons, List.map_nil]
    refine @HasType.input _ _ _ α φ (L ++ freeVars q ++ [x] ++ freeVars p_body)
      (ih_n hctx hqtype hnes_q hlc_q) ?_
    intro z hz
    simp only [List.mem_append, List.mem_singleton, not_or] at hz
    obtain ⟨⟨⟨hzL, hzq⟩, hzx⟩, hzp⟩ := hz
    -- z ∉ L, z ∉ freeVars q, z ≠ x (as ¬(z = x)), z ∉ freeVars p_body
    -- Convert ¬(z = x) to Ne forms
    have hzx_ne : z ≠ x := hzx
    have hxz_ne : x ≠ z := Ne.symm hzx_ne
    -- Step 1: Context equivalence for IH
    have hctx' : (Γ_c.extend z ⟨"Name", α, by simp⟩).LookupEquiv
                 ((Γ₀.extend z ⟨"Name", α, by simp⟩).extend x σ) :=
      (hctx.extend z ⟨"Name", α, by simp⟩).trans (TypingContext.LookupEquiv.permute hxz_ne)
    -- Step 2: Weaken q-typing to extended context
    have hfresh_z_q : isFresh z q = true := by
      simp only [isFresh, Bool.not_eq_true']
      rw [Bool.eq_false_iff]
      intro hmem; exact hzq (list_mem_of_contains hmem)
    have hqtype' : Γ₀.extend z ⟨"Name", α, by simp⟩ ⊢ q : σ := weakening hqtype hfresh_z_q
    -- Step 3: Get noExplicitSubst p_body
    have hnes_pbody : Mettapedia.OSLF.MeTTaIL.Substitution.noExplicitSubst p_body = true :=
      noExplicitSubst_of_openBVar (HasType.noExplicitSubst (hbody z hzL))
    -- Step 4: Apply IH
    have hIH := ih_body z hzL hctx' hqtype' hnes_q hlc_q
    -- Step 5: Use commutation to rewrite
    rw [applySubst_openBVar_comm hzx_ne (by exact hlc_q) hnes_pbody] at hIH
    exact hIH
  | @par _ ps _ ih =>
    simp only [applySubst]
    refine HasType.par (fun p' hp' => ?_)
    rw [List.mem_map] at hp'
    obtain ⟨p, hp, rfl⟩ := hp'
    exact ih p hp hctx hqtype hnes_q hlc_q

/-! ## The Substitutability Theorem -/

/-- **Substitutability Theorem** (OSLF Theorem 1)

    If Γ,x:σ ⊢ p : τ and Γ ⊢ q : σ (with q subst-free and locally closed),
    then Γ ⊢ p[q/x] : τ. -/
theorem substitutability
    {Γ : TypingContext} {p : Pattern} {U : NativeType}
    {x : String} {q : Pattern} {τₓ : NativeType}
    (hptype : Γ.extend x τₓ ⊢ p : U)
    (hqtype : Γ ⊢ q : τₓ)
    (hnes_q : Mettapedia.OSLF.MeTTaIL.Substitution.noExplicitSubst q = true)
    (hlc_q : lc q = true) :
    Γ ⊢ applySubst (SubstEnv.extend SubstEnv.empty x q) p : U :=
  substitution_preserves_type hptype (TypingContext.LookupEquiv.refl _) hqtype hnes_q hlc_q

/-! ## COMM Rule Preserves Types -/

/-- COMM rule preserves types.

    The COMM rule `{n!(q) | for(<-n){p} | ...rest} ~~> {commSubst p q | ...rest}`
    preserves the body's type. In locally nameless, `commSubst p q = openBVar 0 (NQuote q) p`.

    We take the body typing directly via cofinite quantification:
    for all z outside L, the opened body types in the extended context.
    Using `subst_intro`, we convert this to a direct opening with NQuote(q).
-/
theorem comm_preserves_type
    {Γ : TypingContext} {p_body : Pattern} {q : Pattern}
    {φ : ProcPred}
    {L : List String}
    (hbody : ∀ z, z ∉ L →
      HasType (Γ.extend z ⟨"Name", possibly (fun _ => True), by simp⟩)
        (openBVar 0 (.fvar z) p_body) ⟨"Proc", φ, by simp⟩)
    (hq : HasType Γ q ⟨"Proc", fun _ => True, by simp⟩)
    (hlc_q : lc q = true) :
    HasType Γ (commSubst p_body q) ⟨"Proc", φ, by simp⟩ := by
  -- commSubst p_body q = openBVar 0 (NQuote q) p_body
  unfold commSubst
  -- Pick z ∉ L ++ freeVars (NQuote q) ++ freeVars p_body
  have ⟨z, hz⟩ := exists_fresh (L ++ freeVars (.apply "NQuote" [q]) ++ freeVars p_body)
  simp only [List.mem_append, not_or] at hz
  obtain ⟨⟨hzL, hzNQ⟩, hzp⟩ := hz
  -- z is fresh in p_body
  have hfresh_z_pbody : isFresh z p_body = true := by
    simp only [isFresh, Bool.not_eq_true']
    rw [Bool.eq_false_iff]
    intro hmem; exact hzp (list_mem_of_contains hmem)
  -- noExplicitSubst p_body (from the body typing)
  have hnes : Mettapedia.OSLF.MeTTaIL.Substitution.noExplicitSubst p_body = true :=
    noExplicitSubst_of_openBVar (HasType.noExplicitSubst (hbody z hzL))
  -- By subst_intro: applySubst [(z, NQuote q)] (openBVar 0 (.fvar z) p_body) = openBVar 0 (NQuote q) p_body
  have hsubst_eq : applySubst (SubstEnv.extend SubstEnv.empty z (.apply "NQuote" [q]))
      (openBVar 0 (.fvar z) p_body) = openBVar 0 (.apply "NQuote" [q]) p_body :=
    subst_intro hfresh_z_pbody hnes
  -- From hbody z hzL: (Γ.extend z α) ⊢ openBVar 0 (.fvar z) p_body : (Proc, φ)
  -- Apply substitutability with x := z, q := NQuote q, σ := (Name, α)
  -- Γ₀ := Γ, so context is Γ.extend z α = Γ₀.extend z α
  -- NQuote q : (Name, ◇⊤) = (Name, possibly (fun _ => True))
  have hquote : HasType Γ (.apply "NQuote" [q]) ⟨"Name", possibly (fun _ => True), by simp⟩ :=
    HasType.quote hq
  have hnes_nquote : Mettapedia.OSLF.MeTTaIL.Substitution.noExplicitSubst (.apply "NQuote" [q]) = true := by
    show allNoExplicitSubst [q] = true
    simp only [allNoExplicitSubst, HasType.noExplicitSubst hq, Bool.true_and]
  have hlc_nquote : lc (.apply "NQuote" [q]) = true := by
    simp only [lc, lc_at, lc_at_list, Bool.and_true]
    exact hlc_q
  -- Apply substitutability: Γ.extend z (Name, ◇⊤) ⊢ openBVar 0 (.fvar z) p_body : (Proc, φ)
  -- with NQuote q : (Name, ◇⊤) gives:
  -- Γ ⊢ applySubst [(z, NQuote q)] (openBVar 0 (.fvar z) p_body) : (Proc, φ)
  have hresult := substitutability (hbody z hzL) hquote hnes_nquote hlc_nquote
  rw [hsubst_eq] at hresult
  exact hresult

/-! ## Progress Theorem -/

/-- Syntactic inertness check for elements (recursive) -/
def isInertElement : Pattern → Bool
  | .apply "PZero" [] => true
  | .apply "POutput" _ => true
  | .apply "PInput" _ => true
  | .apply "NQuote" _ => true
  | .collection .hashBag ps none => isInertElementList ps
  | _ => false
where
  isInertElementList : List Pattern → Bool
    | [] => true
    | p :: ps => isInertElement p && isInertElementList ps

/-- Syntactic inertness check for top-level patterns -/
def isInertSyntax : Pattern → Bool
  | .apply "PZero" [] => true
  | .apply "POutput" _ => true
  | .apply "PInput" _ => true
  | .apply "NQuote" _ => true
  | .collection .hashBag ps none => isInertElement.isInertElementList ps
  | _ => false

theorem isInertElementList_eq_all (ps : List Pattern) :
    isInertElement.isInertElementList ps = ps.all isInertElement := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [isInertElement.isInertElementList, List.all_cons, ih]

theorem isInertElement_collection (ps : List Pattern) :
    isInertElement (.collection .hashBag ps none) = isInertElement.isInertElementList ps := rfl

theorem isInertElement_par_iff (ps : List Pattern) :
    isInertElement (.collection .hashBag ps none) = ps.all isInertElement := by
  rw [isInertElement_collection, isInertElementList_eq_all]

/-- In empty context, all Names are quotes. -/
theorem empty_context_name_is_quote {n : Pattern} {α : NamePred} :
    (TypingContext.empty ⊢ n : ⟨"Name", α, by simp⟩) →
    ∃ p, n = .apply "NQuote" [p] := by
  intro h
  generalize hτ : (⟨"Name", α, by simp⟩ : NativeType) = τ at h
  cases h with
  | fvar hlookup =>
    simp [TypingContext.empty, TypingContext.lookup] at hlookup
  | quote hp =>
    exact ⟨_, rfl⟩
  | nil => simp [NativeType.mk.injEq] at hτ
  | drop _ => simp [NativeType.mk.injEq] at hτ
  | output _ _ => simp [NativeType.mk.injEq] at hτ
  | input _ _ => simp [NativeType.mk.injEq] at hτ
  | par _ => simp [NativeType.mk.injEq] at hτ

theorem List.exists_split_of_mem' {α : Type*} {x : α} {xs : List α} (h : x ∈ xs) :
    ∃ before after, xs = before ++ [x] ++ after := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
    cases h with
    | head => exact ⟨[], ys, rfl⟩
    | tail _ hy =>
      obtain ⟨before, after, heq⟩ := ih hy
      exact ⟨y :: before, after, by simp [heq]⟩

/-- A non-inert element in empty context reduces. -/
theorem non_inert_proc_reduces {p : Pattern} {φ : ProcPred}
    (htype : TypingContext.empty ⊢ p : ⟨"Proc", φ, by simp⟩)
    (hnotval : isInertElement p = false) :
    ∃ q, Nonempty (p ⇝ q) := by
  generalize hp : sizeOf p = n
  induction n using Nat.strong_induction_on generalizing p φ with
  | _ n ih =>
    generalize hτ : (⟨"Proc", φ, by simp⟩ : NativeType) = τ at htype
    cases htype with
    | fvar hlookup =>
      simp [TypingContext.empty, TypingContext.lookup] at hlookup
    | nil =>
      simp [isInertElement] at hnotval
    | quote _ =>
      simp [NativeType.mk.injEq] at hτ
    | drop hn =>
      obtain ⟨q, rfl⟩ := empty_context_name_is_quote hn
      exact ⟨q, ⟨Reduces.drop⟩⟩
    | output _ _ =>
      simp [isInertElement] at hnotval
    | input _ _ =>
      simp [isInertElement] at hnotval
    | @par _ ps hall =>
      rw [isInertElement_par_iff] at hnotval
      have hnotval' : ¬ ps.all isInertElement = true := by simp [hnotval]
      simp only [List.all_eq_true] at hnotval'
      push_neg at hnotval'
      obtain ⟨elem, helem, helemnotval⟩ := hnotval'
      have hmem := List.sizeOf_lt_of_mem helem
      have hsz : sizeOf elem < n := by
        have h1 : sizeOf ps ≤ sizeOf (Pattern.collection CollType.hashBag ps (none : Option String)) := by
          simp only [Pattern.collection.sizeOf_spec]
          omega
        rw [hp] at h1
        omega
      have helem_typed := hall elem helem
      have helemnotval' : isInertElement elem = false := by
        cases h : isInertElement elem
        · rfl
        · exact absurd h helemnotval
      have hreduces := ih (sizeOf elem) hsz helem_typed helemnotval' rfl
      obtain ⟨q, hred⟩ := hreduces
      obtain ⟨before, after, hps⟩ := List.exists_split_of_mem' helem
      use .collection .hashBag (before ++ [q] ++ after) none
      rw [hps]
      exact ⟨Reduces.par_any hred.some⟩

/-- Syntactic progress for Proc-sorted types -/
theorem progress_proc {p : Pattern} {φ : ProcPred} :
    (TypingContext.empty ⊢ p : ⟨"Proc", φ, by simp⟩) →
    isInertSyntax p ∨ ∃ q, Nonempty (p ⇝ q) := by
  intro h
  generalize hτ : (⟨"Proc", φ, by simp⟩ : NativeType) = τ at h
  cases h with
  | fvar hlookup =>
    simp [TypingContext.empty, TypingContext.lookup] at hlookup
  | nil =>
    left; rfl
  | quote _ =>
    simp [NativeType.mk.injEq] at hτ
  | drop hn =>
    right
    obtain ⟨q, rfl⟩ := empty_context_name_is_quote hn
    exact ⟨q, ⟨Reduces.drop⟩⟩
  | output _ _ =>
    left; rfl
  | input _ _ =>
    left; rfl
  | @par _ ps hall =>
    by_cases hval : isInertElement.isInertElementList ps
    · left
      simp only [isInertSyntax]
      exact hval
    · right
      rw [isInertElementList_eq_all] at hval
      have hval' : ¬ ps.all isInertElement = true := by simp [hval]
      simp only [List.all_eq_true] at hval'
      push_neg at hval'
      obtain ⟨elem, helem, hnotval⟩ := hval'
      have htyped := hall elem helem
      have hnotval' : isInertElement elem = false := by
        cases h : isInertElement elem
        · rfl
        · exact absurd h hnotval
      obtain ⟨q, hred⟩ := non_inert_proc_reduces htyped hnotval'
      obtain ⟨before, after, hps⟩ := List.exists_split_of_mem' helem
      use .collection .hashBag (before ++ [q] ++ after) none
      rw [hps]
      exact ⟨Reduces.par_any hred.some⟩

/-- Syntactic progress (general) -/
theorem progress {p : Pattern} {τ : NativeType} :
    (TypingContext.empty ⊢ p : τ) →
    isInertSyntax p ∨ ∃ q, Nonempty (p ⇝ q) := by
  intro h
  by_cases hsort : τ.sort = "Proc"
  · obtain ⟨sort, pred, valid⟩ := τ
    simp only at hsort
    subst hsort
    exact progress_proc h
  · left
    obtain ⟨sort, pred, valid⟩ := τ
    rcases valid with _ | ⟨_, _ | ⟨_, h'⟩⟩
    · exact absurd rfl hsort
    · obtain ⟨q, rfl⟩ := empty_context_name_is_quote h
      rfl
    · nomatch h'

/-! ## Summary

This file establishes the type soundness of OSLF:

1. **NativeType**: Sort x Predicate pairs
2. **TypingContext**: Variable -> NativeType maps
3. **HasType**: Type judgment (locally nameless, cofinite input)
4. **LookupEquiv**: Context equivalence (reflexive, symmetric, transitive)
5. **weakening**: Fresh variable extension preserves typing
6. **HasType.noExplicitSubst**: Well-typed patterns have no .subst nodes
7. **substitution_preserves_type**: Substitution preserves types (LookupEquiv formulation)
8. **substitutability**: Main theorem (standard formulation)
9. **comm_preserves_type**: COMM rule soundness (partial -- see note)
10. **isInertSyntax**: Syntactic approximation of normal forms
11. **non_inert_proc_reduces**: Non-inert implies reduces
12. **progress_proc** / **progress**: Syntactic progress

**Note on comm_preserves_type**: The body predicate φ is existentially
determined by the input derivation, so the theorem requires access to the
derivation structure. This is captured via `cases hp` in the proof.
-/

end Mettapedia.OSLF.RhoCalculus.Soundness
