import Mettapedia.OSLF.RhoCalculus.Types
import Mettapedia.OSLF.RhoCalculus.Reduction
import Mettapedia.OSLF.MeTTaIL.Substitution
import Mettapedia.CategoryTheory.Topos.InternalLanguage

/-!
# Type Soundness for ρ-Calculus

This file formalizes the key soundness theorem from OSLF:
type preservation under substitution (substitutability).

## The Substitutability Theorem

If Γ ⊢ p : U and Γ ⊢ q : τₓ then Γ ⊢ p[q/x] : U

This says that substitution preserves types: if a process p has type U,
and we substitute a well-typed term q for variable x, the result still
has type U.

## Why This Matters

The substitutability theorem is the **key correctness property** of OSLF:
- It validates the rely-possibly formula construction
- It shows that native types are preserved under computation
- It connects operational semantics to the type system

## References

- Meredith & Stay, "Operational Semantics in Logical Form" Theorem 1
- Williams & Stay, "Native Type Theory" (ACT 2021)
-/

namespace Mettapedia.OSLF.RhoCalculus.Soundness

open Mettapedia.OSLF.RhoCalculus
open Mettapedia.OSLF.RhoCalculus.Reduction
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.CategoryTheory.LambdaTheories

/-! ## Typing Contexts

A typing context Γ assigns types to variables. In the OSLF framework,
a "type" is a pair (sort, predicate) where:
- sort ∈ {Proc, Name}
- predicate is a truth value in the fiber
-/

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

/-! ## Type Judgments

We define when a pattern has a given type in a context.
This is the judgment Γ ⊢ p : τ.
-/

/-- Type judgment: Γ ⊢ p : τ -/
inductive HasType : TypingContext → Pattern → NativeType → Prop where
  /-- Variable rule: Γ, x:τ, Γ' ⊢ x : τ -/
  | var {Γ : TypingContext} {x : String} {τ : NativeType} :
      Γ.lookup x = some τ → HasType Γ (.var x) τ

  /-- Nil process: Γ ⊢ 0 : (Proc, ⊤) -/
  | nil {Γ : TypingContext} :
      HasType Γ (.apply "PZero" []) ⟨"Proc", ⊤, by simp⟩

  /-- Quote: Γ ⊢ p : (Proc, φ) → Γ ⊢ @p : (Name, ◇φ) -/
  | quote {Γ : TypingContext} {p : Pattern} {φ : ProcPred} :
      HasType Γ p ⟨"Proc", φ, by simp⟩ →
      HasType Γ (.apply "NQuote" [p]) ⟨"Name", possibly φ, by simp⟩

  /-- Drop: Γ ⊢ n : (Name, α) → Γ ⊢ *n : (Proc, ⧫α) -/
  | drop {Γ : TypingContext} {n : Pattern} {α : NamePred} :
      HasType Γ n ⟨"Name", α, by simp⟩ →
      HasType Γ (.apply "PDrop" [n]) ⟨"Proc", rely α, by simp⟩

  /-- Output: Γ ⊢ n : (Name, α), Γ ⊢ q : (Proc, φ) → Γ ⊢ n!(q) : (Proc, ...) -/
  | output {Γ : TypingContext} {n q : Pattern} {α : NamePred} {φ : ProcPred} :
      HasType Γ n ⟨"Name", α, by simp⟩ →
      HasType Γ q ⟨"Proc", φ, by simp⟩ →
      HasType Γ (.apply "POutput" [n, q]) ⟨"Proc", ⊤, by simp⟩

  /-- Input: Γ ⊢ n : (Name, α), Γ,x:(Name,α) ⊢ p : (Proc, φ) → Γ ⊢ for(x<-n){p} : (Proc, ...) -/
  | input {Γ : TypingContext} {n : Pattern} {x : String} {p : Pattern}
          {α : NamePred} {φ : ProcPred} :
      HasType Γ n ⟨"Name", α, by simp⟩ →
      HasType (Γ.extend x ⟨"Name", α, by simp⟩) p ⟨"Proc", φ, by simp⟩ →
      HasType Γ (.apply "PInput" [n, .lambda x p]) ⟨"Proc", ⊤, by simp⟩

  /-- Parallel: all elements must be well-typed processes -/
  | par {Γ : TypingContext} {ps : List Pattern} :
      (∀ p ∈ ps, HasType Γ p ⟨"Proc", ⊤, by simp⟩) →
      HasType Γ (.collection .hashBag ps none) ⟨"Proc", ⊤, by simp⟩

notation:40 Γ " ⊢ " p " : " τ => HasType Γ p τ

/-! ## Substitution Lemma

The key lemma: substitution preserves types.
-/

/-- Helper: isFresh on var implies inequality -/
theorem isFresh_var_neq {x y : String} (h : isFresh x (.var y)) : x ≠ y := by
  unfold isFresh freeVars at h
  simp only [List.contains_cons, List.contains_nil, Bool.or_false,
             Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h
  exact fun heq => h heq

/-- Helper: lookup in extended context when variable differs -/
theorem lookup_extend_neq {Γ : TypingContext} {x y : String} {σ : NativeType}
    (hne : x ≠ y) : (Γ.extend x σ).lookup y = Γ.lookup y := by
  unfold TypingContext.extend TypingContext.lookup
  simp only [List.find?]
  have : (x == y) = false := beq_eq_false_iff_ne.mpr hne
  simp only [this]

/-- Two contexts are lookup-equivalent if they give the same result for all lookups -/
def TypingContext.LookupEquiv (Γ Γ' : TypingContext) : Prop :=
  ∀ x, Γ.lookup x = Γ'.lookup x

/-- LookupEquiv is reflexive -/
theorem TypingContext.LookupEquiv.refl (Γ : TypingContext) : Γ.LookupEquiv Γ :=
  fun _ => rfl

/-- LookupEquiv is symmetric -/
theorem TypingContext.LookupEquiv.symm {Γ Γ' : TypingContext} (h : Γ.LookupEquiv Γ') :
    Γ'.LookupEquiv Γ := fun x => (h x).symm

/-- Extending lookup-equivalent contexts preserves equivalence -/
theorem TypingContext.LookupEquiv.extend {Γ Γ' : TypingContext} (h : Γ.LookupEquiv Γ')
    (x : String) (τ : NativeType) : (Γ.extend x τ).LookupEquiv (Γ'.extend x τ) := by
  intro z
  unfold TypingContext.extend TypingContext.lookup
  by_cases hzx : z = x
  · -- z = x: both find τ immediately
    -- The predicate in find? is (fun p => p.1 == z), so we need (x == z) = true
    have hxz : (x == z) = true := beq_iff_eq.mpr hzx.symm
    simp only [List.find?, hxz]
  · -- z ≠ x: fall through to original contexts
    have hne : (x == z) = false := beq_eq_false_iff_ne.mpr (Ne.symm hzx)
    simp only [List.find?, hne]
    exact h z

/-- **Context equivalence for HasType**: If Γ and Γ' have the same lookups, typing is preserved.

    This is the key lemma that justifies treating contexts extensionally.
    It requires induction on the typing derivation because the `input` rule
    structurally extends the context.
-/
theorem HasType_context_equiv {Γ Γ' : TypingContext} {p : Pattern} {τ : NativeType}
    (hequiv : Γ.LookupEquiv Γ') (htype : Γ ⊢ p : τ) : Γ' ⊢ p : τ := by
  induction htype generalizing Γ' with
  | var hlookup =>
    apply HasType.var
    rw [← hequiv _]
    exact hlookup
  | nil => exact HasType.nil
  | quote _ ih => exact HasType.quote (ih hequiv)
  | drop _ ih => exact HasType.drop (ih hequiv)
  | output _ _ ih1 ih2 => exact HasType.output (ih1 hequiv) (ih2 hequiv)
  | @input _ n x p' α φ _ _ ih_n ih_p =>
    apply HasType.input (ih_n hequiv)
    exact ih_p (hequiv.extend x _)
  | @par _ ps hps ih =>
    exact HasType.par (fun p hp => ih p hp hequiv)

/-- Permuted extensions are lookup-equivalent -/
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

/-- Inner binding shadows outer: (Γ.extend x σ).extend x τ ≃ Γ.extend x τ for lookups -/
theorem TypingContext.LookupEquiv.shadow {Γ : TypingContext} {x : String} {σ τ : NativeType} :
    ((Γ.extend x σ).extend x τ).LookupEquiv (Γ.extend x τ) := by
  intro z
  unfold TypingContext.extend TypingContext.lookup
  by_cases hzx : z = x
  · have hxz : (x == z) = true := beq_iff_eq.mpr hzx.symm
    simp only [List.find?, hxz]
  · have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr (Ne.symm hzx)
    simp only [List.find?, hxz]

/-- Lookup in permuted context: when x ≠ y, lookup z is the same regardless of extension order -/
theorem lookup_permute {Γ : TypingContext} {x y : String} {σ τ : NativeType} {z : String}
    (hne : x ≠ y) : ((Γ.extend x σ).extend y τ).lookup z = ((Γ.extend y τ).extend x σ).lookup z := by
  unfold TypingContext.extend TypingContext.lookup
  by_cases hzy : z = y
  · -- z = y: first finds (y,τ) immediately, second finds after skipping (x,σ)
    have hyz : (y == z) = true := beq_iff_eq.mpr hzy.symm
    have hxz : (x == z) = false := by rw [hzy]; exact beq_eq_false_iff_ne.mpr hne
    simp only [List.find?, hyz, hxz]
  · by_cases hzx : z = x
    · -- z = x: first finds (x,σ) after skipping (y,τ), second finds immediately
      have hyz : (y == z) = false := beq_eq_false_iff_ne.mpr (Ne.symm hzy)
      have hxz : (x == z) = true := beq_iff_eq.mpr hzx.symm
      simp only [List.find?, hyz, hxz]
    · -- z ≠ x, z ≠ y: both find the same value in Γ
      have hyz : (y == z) = false := beq_eq_false_iff_ne.mpr (Ne.symm hzy)
      have hxz : (x == z) = false := beq_eq_false_iff_ne.mpr (Ne.symm hzx)
      simp only [List.find?, hyz, hxz]

/-- Helper: if x ∈ L and x ≠ y then x ∈ L.filter (· != y) -/
theorem mem_filter_of_mem_neq {x y : String} {L : List String}
    (hmem : x ∈ L) (hne : x ≠ y) : x ∈ L.filter (· != y) := by
  simp only [List.mem_filter]
  constructor
  · exact hmem
  · exact bne_iff_ne.mpr hne

/-- Helper: contains implies elem -/
theorem elem_of_contains {x : String} {L : List String}
    (h : L.contains x = true) : x ∈ L := by
  simp only [List.contains_iff_exists_mem_beq] at h
  obtain ⟨z, hz_mem, hz_eq⟩ := h
  -- hz_eq : (x == z) = true, need z = x
  have : x = z := beq_iff_eq.mp hz_eq
  rw [this]
  exact hz_mem

/-- Helper: elem implies contains -/
theorem contains_of_elem {x : String} {L : List String}
    (h : x ∈ L) : L.contains x = true := by
  simp only [List.contains_iff_exists_mem_beq]
  exact ⟨x, h, beq_self_eq_true x⟩

/-- Helper: if x ∉ L.filter (· != y) and x ≠ y, then x ∉ L -/
theorem not_contains_of_filter_neq {x y : String} {L : List String}
    (h : !(L.filter (· != y)).contains x) (hne : x ≠ y) : !L.contains x := by
  -- Contraposition: if x ∈ L then x ∈ filtered list (contradiction with h)
  -- h : !(...).contains x = true means (...).contains x = false
  rw [Bool.not_eq_true'] at h ⊢
  -- Goal: L.contains x = false
  by_contra habs
  -- habs : ¬(L.contains x = false)
  -- Bool has decidable equality, so ¬(b = false) → b = true
  have habs' : L.contains x = true := by
    cases hb : L.contains x
    · exact (habs hb).elim
    · rfl
  have hxL := elem_of_contains habs'
  have hxFiltered := mem_filter_of_mem_neq hxL hne
  have hcontains := contains_of_elem hxFiltered
  rw [h] at hcontains
  exact Bool.false_ne_true hcontains

/-- Freshness for lambda: x fresh in (lambda y p) means x = y or x fresh in p -/
theorem isFresh_lambda {x y : String} {p : Pattern}
    (h : isFresh x (.lambda y p)) : x = y ∨ isFresh x p := by
  unfold isFresh freeVars at h
  by_cases hxy : x = y
  · exact Or.inl hxy
  · right
    unfold isFresh
    exact not_contains_of_filter_neq h hxy

/-- Freshness for single-argument apply -/
theorem isFresh_apply_singleton {x : String} {c : String} {p : Pattern}
    (h : isFresh x (.apply c [p])) : isFresh x p := by
  simp only [isFresh, freeVars, List.flatMap_cons, List.flatMap_nil, List.append_nil] at h ⊢
  exact h

/-- Freshness for two-argument apply -/
theorem isFresh_apply_pair {x : String} {c : String} {p q : Pattern}
    (h : isFresh x (.apply c [p, q])) : isFresh x p ∧ isFresh x q := by
  simp only [isFresh, freeVars, List.flatMap_cons, List.flatMap_nil,
             List.append_nil, List.contains_append, Bool.not_or,
             Bool.and_eq_true] at h
  simp only [isFresh]
  exact h

/-- Weakening: if Γ ⊢ p : τ and x ∉ FV(p), then Γ,x:σ ⊢ p : τ -/
theorem weakening {Γ : TypingContext} {p : Pattern} {τ : NativeType}
    {x : String} {σ : NativeType} :
    (Γ ⊢ p : τ) → isFresh x p → (Γ.extend x σ ⊢ p : τ) := by
  intro htype hfresh
  induction htype with
  | @var _ y _ hlookup =>
    apply HasType.var
    -- x is fresh in (var y) means x ≠ y, so lookup unchanged
    have hne : x ≠ y := isFresh_var_neq hfresh
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
  | @input _ n x' p' α φ hn hp ih_n ih_p =>
    -- Input case: x fresh in (PInput [n, lambda x' p'])
    -- Need: Γ.extend x σ ⊢ PInput [n, lambda x' p'] : ⟨"Proc", ⊤, ...⟩
    have ⟨hfresh_n, hfresh_lam⟩ := isFresh_apply_pair hfresh
    refine @HasType.input _ n x' p' α φ (ih_n hfresh_n) ?_
    -- Goal: (Γ.extend x σ).extend x' α ⊢ p' : ⟨"Proc", φ, ...⟩
    -- Have hp : (Γ.extend x' α) ⊢ p' : ⟨"Proc", φ, ...⟩
    -- Have ih_p : isFresh x p' → ((Γ.extend x' α).extend x σ ⊢ p' : ...)
    have hcases := isFresh_lambda hfresh_lam
    cases hcases with
    | inl heq =>
      -- x = x': inner binding shadows outer
      subst heq
      -- Goal: (Γ.extend x σ).extend x α ⊢ p' : ...
      -- hp : (Γ.extend x α) ⊢ p' : ...
      -- These contexts are lookup-equivalent by shadow lemma
      exact HasType_context_equiv TypingContext.LookupEquiv.shadow.symm hp
    | inr hfresh_p =>
      -- x ≠ x': use ih_p and permutation
      -- First, we need x ≠ x' explicitly for permutation
      -- From the case split: we're in inr, so isFresh_lambda gave us isFresh x p'
      -- but not directly x ≠ x'. We can derive it:
      -- If x = x', then isFresh_lambda would return Or.inl (since it checks by_cases first)
      -- So being in Or.inr means x ≠ x' in the proof of isFresh_lambda
      -- But we need to derive this fact here...
      -- Alternative: check directly from hfresh_lam
      by_cases hxx' : x = x'
      · -- Contradiction: if x = x', we should be in the inl case
        -- But actually both cases can be reached if both hold
        -- Use the shadow lemma here too
        subst hxx'
        exact HasType_context_equiv (TypingContext.LookupEquiv.shadow.symm) hp
      · -- x ≠ x': apply ih_p then permute
        have hp' := ih_p hfresh_p
        -- hp' : (Γ.extend x' α).extend x σ ⊢ p' : ...
        -- Goal: (Γ.extend x σ).extend x' α ⊢ p' : ...
        -- Use permutation equivalence (note: need Ne.symm to get x' ≠ x)
        exact HasType_context_equiv (TypingContext.LookupEquiv.permute (Ne.symm hxx')) hp'
  | @par _ ps hps ih =>
    -- For each element p ∈ ps, we have isFresh x p (from hfresh on the collection)
    -- and ih gives us: isFresh x p → HasType (Γ.extend x σ) p ...
    -- But wait, hfresh is about the whole collection, not individual elements
    -- We need: isFresh x (.collection .hashBag ps none) → ∀ p ∈ ps, isFresh x p
    -- This follows from the definition of freeVars on collections
    have hfresh_all : ∀ p ∈ ps, isFresh x p := by
      intro p hp
      unfold isFresh at hfresh ⊢
      unfold freeVars at hfresh
      rw [Bool.not_eq_true'] at hfresh ⊢
      -- hfresh : (ps.flatMap freeVars).contains x = false
      -- Goal: (freeVars p).contains x = false
      by_contra habs
      push_neg at habs
      -- habs : (freeVars p).contains x ≠ false
      cases hb : (freeVars p).contains x with
      | false => exact habs hb
      | true =>
        have hmem := elem_of_contains hb
        have helem : x ∈ ps.flatMap freeVars := List.mem_flatMap.mpr ⟨p, hp, hmem⟩
        have hcontains := contains_of_elem helem
        -- hfresh and hcontains contradict
        rw [hfresh] at hcontains
        exact Bool.false_ne_true hcontains
    exact HasType.par (fun p hp => ih p hp (hfresh_all p hp))

/-- Well-typed patterns have no explicit substitution nodes.

    This is because our typing rules (var, nil, quote, drop, output, input)
    never introduce or type a `.subst` pattern constructor.

    Note: The `par` case requires strengthening the typing rule to include
    hypotheses about the well-typedness of collection elements.
-/
theorem HasType.noExplicitSubst {Γ : TypingContext} {p : Pattern} {τ : NativeType}
    (h : Γ ⊢ p : τ) : noExplicitSubst p := by
  induction h with
  | var _ => rfl
  | nil => rfl
  | quote _ ih =>
    -- quote n : noExplicitSubst (.apply "NQuote" [n]) = allNoExplicitSubst [n]
    show allNoExplicitSubst [_] = true
    simp only [allNoExplicitSubst, ih, Bool.true_and]
  | drop _ ih =>
    -- drop n : noExplicitSubst (.apply "PDrop" [n]) = allNoExplicitSubst [n]
    show allNoExplicitSubst [_] = true
    simp only [allNoExplicitSubst, ih, Bool.true_and]
  | output _ _ ih1 ih2 =>
    -- output n q : noExplicitSubst (.apply "POutput" [n, q])
    show allNoExplicitSubst [_, _] = true
    simp only [allNoExplicitSubst, ih1, ih2, Bool.and_self]
  | input _ _ ih_n ih_p =>
    -- input n p : noExplicitSubst (.apply "PInput" [n, .lambda x p])
    show allNoExplicitSubst [_, .lambda _ _] = true
    simp only [allNoExplicitSubst, Mettapedia.OSLF.MeTTaIL.Substitution.noExplicitSubst,
               ih_n, ih_p, Bool.and_self]
  | @par _ ps hps ih =>
    -- Now that par requires all elements well-typed, we can use the IH
    show allNoExplicitSubst ps = true
    -- ih : ∀ p ∈ ps, noExplicitSubst p = true
    -- (ih is the induction hypothesis for the elements)
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

/-- Get bound variables of a pattern (variables bound by lambdas) -/
def boundVars : Pattern → List String
  | .var _ => []
  | .apply _ args => args.flatMap boundVars
  | .lambda x body => x :: boundVars body
  | .multiLambda xs body => xs ++ boundVars body
  | .subst body _ repl => boundVars body ++ boundVars repl
  | .collection _ elems _ => elems.flatMap boundVars
termination_by p => sizeOf p

/-- All bound variables in p are fresh in q (Barendregt convention) -/
def boundFresh (p q : Pattern) : Prop :=
  ∀ y ∈ boundVars p, isFresh y q

/-- Substitution preserves types

    The proof uses well-founded recursion on pattern size.
    We assume the Barendregt convention: bound variables in p are fresh in q.
    This ensures that going under a binder doesn't cause capture issues.
-/
theorem substitution_preserves_type
    {Γ : TypingContext} {p : Pattern} {τ : NativeType}
    {x : String} {q : Pattern} {σ : NativeType}
    (hptype : Γ.extend x σ ⊢ p : τ)
    (hqtype : Γ ⊢ q : σ)
    (hfresh : boundFresh p q) :
    Γ ⊢ applySubst (SubstEnv.extend SubstEnv.empty x q) p : τ := by
  -- Case split on the typing derivation
  cases hptype with
  | @var _ y _ hlookup =>
    -- p = .var y
    simp only [applySubst, SubstEnv.extend, SubstEnv.empty, SubstEnv.find, List.find?]
    by_cases hxy : x = y
    · -- Substituting: x = y
      simp only [beq_iff_eq.mpr hxy]
      have hτσ : τ = σ := by
        unfold TypingContext.extend TypingContext.lookup at hlookup
        have hyx : (x == y) = true := beq_iff_eq.mpr hxy
        simp only [List.find?, hyx] at hlookup
        exact (Option.some_injective _ hlookup).symm
      subst hτσ
      exact hqtype
    · -- Not substituting: x ≠ y
      simp only [beq_eq_false_iff_ne.mpr hxy]
      apply HasType.var
      rw [← lookup_extend_neq hxy]
      exact hlookup
  | nil =>
    simp only [applySubst, List.map_nil]
    exact HasType.nil
  | @quote _ p' φ hp' =>
    simp only [applySubst, List.map_cons, List.map_nil]
    have hfresh' : boundFresh p' q := fun y hy => hfresh y (by
      simp only [boundVars, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hy ⊢
      exact hy)
    exact HasType.quote (substitution_preserves_type hp' hqtype hfresh')
  | @drop _ n' α hn' =>
    simp only [applySubst, List.map_cons, List.map_nil]
    have hfresh' : boundFresh n' q := fun y hy => hfresh y (by
      simp only [boundVars, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hy ⊢
      exact hy)
    exact HasType.drop (substitution_preserves_type hn' hqtype hfresh')
  | @output _ n' q' α φ hn' hq' =>
    simp only [applySubst, List.map_cons, List.map_nil]
    have hfresh_n : boundFresh n' q := fun y hy => hfresh y (by
      simp only [boundVars, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hy ⊢
      exact List.mem_append_left _ hy)
    have hfresh_q : boundFresh q' q := fun y hy => hfresh y (by
      simp only [boundVars, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hy ⊢
      exact List.mem_append_right _ hy)
    exact HasType.output (substitution_preserves_type hn' hqtype hfresh_n)
                         (substitution_preserves_type hq' hqtype hfresh_q)
  | @input _ n' x' p' α φ hn' hp' =>
    simp only [applySubst, List.map_cons, List.map_nil]
    -- hp' : (Γ.extend x σ).extend x' α ⊢ p' : ⟨"Proc", φ, ...⟩
    -- Need: Γ.extend x' α ⊢ applySubst (env.filter (·.1 != x')) p' : ⟨"Proc", φ, ...⟩
    -- First, prove freshness for n'
    have hfresh_n : boundFresh n' q := fun y hy => hfresh y (by
      simp only [boundVars, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hy ⊢
      exact List.mem_append_left _ hy)
    refine @HasType.input Γ _ x' _ α φ (substitution_preserves_type hn' hqtype hfresh_n) ?_
    -- The substitution filters out x' from the environment
    by_cases hxx' : x = x'
    · -- x = x': the substitution is filtered out entirely
      subst hxx'
      have hfilter : (SubstEnv.extend SubstEnv.empty x q).filter (fun p => p.1 != x) = SubstEnv.empty := by
        simp only [SubstEnv.extend, SubstEnv.empty, List.filter]
        have : (x != x) = false := by simp only [bne_self_eq_false]
        simp only [this]
      rw [hfilter]
      -- hp' : (Γ.extend x σ).extend x α ⊢ p' : ⟨"Proc", φ, ...⟩
      -- By shadow: ((Γ.extend x σ).extend x α).LookupEquiv (Γ.extend x α)
      have hp'_shadow := HasType_context_equiv TypingContext.LookupEquiv.shadow hp'
      -- hp'_shadow : Γ.extend x α ⊢ p' : ⟨"Proc", φ, ...⟩
      -- Well-typed patterns have no explicit subst nodes
      have hnosubst := HasType.noExplicitSubst hp'_shadow
      -- By subst_empty: applySubst [] p' = p'
      rw [subst_empty p' hnosubst]
      exact hp'_shadow
    · -- x ≠ x': apply IH with permuted context
      have hp'_permuted : (Γ.extend x' ⟨"Name", α, by simp⟩).extend x σ ⊢ p' : ⟨"Proc", φ, by simp⟩ :=
        HasType_context_equiv (TypingContext.LookupEquiv.permute hxx') hp'
      have hfilter_eq : (SubstEnv.extend SubstEnv.empty x q).filter (fun p => p.1 != x') =
                        SubstEnv.extend SubstEnv.empty x q := by
        simp only [SubstEnv.extend, SubstEnv.empty, List.filter]
        have : (x != x') = true := bne_iff_ne.mpr hxx'
        simp only [this]
      rw [hfilter_eq]
      -- x' is bound in the lambda, so by Barendregt (hfresh), x' is fresh in q
      -- boundVars (.apply "PInput" [n', .lambda x' p']) includes x' from the lambda
      have hx'_bound : x' ∈ boundVars (.apply "PInput" [n', .lambda x' p']) := by
        simp only [boundVars, List.flatMap_cons, List.flatMap_nil, List.append_nil,
                   List.mem_append, List.mem_cons, true_or, or_true]
      have hx'_fresh : isFresh x' q := hfresh x' hx'_bound
      -- Use weakening to get hqtype in the extended context
      have hqtype' : Γ.extend x' ⟨"Name", α, by simp⟩ ⊢ q : σ := weakening hqtype hx'_fresh
      -- Freshness for p'
      have hfresh_p' : boundFresh p' q := fun y hy => hfresh y (by
        simp only [boundVars, List.flatMap_cons, List.flatMap_nil, List.append_nil,
                   List.mem_append, List.mem_cons]
        right; right; exact hy)
      exact substitution_preserves_type hp'_permuted hqtype' hfresh_p'
  | @par _ ps hps =>
    simp only [applySubst]
    -- Need to show: Γ ⊢ .collection .hashBag (ps.map (applySubst env)) none : ⊤
    -- Using par rule, need: ∀ p' ∈ ps.map (applySubst env), HasType Γ p' ⊤
    refine HasType.par (fun p' hp' => ?_)
    -- p' ∈ ps.map (applySubst env), so p' = applySubst env p for some p ∈ ps
    rw [List.mem_map] at hp'
    obtain ⟨p, hp, rfl⟩ := hp'
    -- hps p hp : (Γ.extend x σ) ⊢ p : ⊤
    -- Need to show boundFresh p q for the recursive call
    have hfresh_p : boundFresh p q := fun y hy => hfresh y (by
      simp only [boundVars, List.flatMap] at hy ⊢
      exact List.mem_flatMap.mpr ⟨p, hp, hy⟩)
    exact substitution_preserves_type (hps p hp) hqtype hfresh_p
termination_by sizeOf p

/-! ## The Substitutability Theorem

This is Theorem 1 from OSLF: substitution preserves native types.
-/

/-- **Substitutability Theorem** (OSLF Theorem 1)

    If Γ ⊢ p : U and Γ ⊢ q : τₓ where x : τₓ is bound in p,
    and the bound variables of p are fresh in q (Barendregt convention),
    then Γ ⊢ p[q/x] : U.

    This is the key soundness theorem: native types are preserved
    under substitution, which validates the OSLF type system.
-/
theorem substitutability
    {Γ : TypingContext} {p : Pattern} {U : NativeType}
    {x : String} {q : Pattern} {τₓ : NativeType}
    (hptype : Γ.extend x τₓ ⊢ p : U)
    (hqtype : Γ ⊢ q : τₓ)
    (hfresh : boundFresh p q) :
    Γ ⊢ applySubst (SubstEnv.extend SubstEnv.empty x q) p : U :=
  substitution_preserves_type hptype hqtype hfresh

/-! ## Corollaries -/

/-- COMM rule preserves types

    The key observation: the substituted term `@q` has type `(Name, ◇⊤) = (Name, ⊤)`
    (since `possibly` is currently defined as identity). For the types to match,
    we need `α = ⊤`. In the full OSLF, this constraint comes from channel types.
-/
theorem comm_preserves_type
    {Γ : TypingContext} {n : Pattern} {p : Pattern} {q : Pattern}
    {x : String} {φ : ProcPred}
    (_hn : HasType Γ n ⟨"Name", ⊤, by simp⟩)
    (hp : HasType (Γ.extend x ⟨"Name", ⊤, by simp⟩) p ⟨"Proc", φ, by simp⟩)
    (hq : HasType Γ q ⟨"Proc", ⊤, by simp⟩)
    (hfresh : boundFresh p (.apply "NQuote" [q])) :
    HasType Γ (commSubst p x q) ⟨"Proc", φ, by simp⟩ := by
  -- commSubst p x q = applySubst [(x, NQuote q)] p
  unfold commSubst
  -- @q has type (Name, ◇⊤) = (Name, ⊤) since possibly = identity
  have hquote : HasType Γ (.apply "NQuote" [q]) ⟨"Name", possibly ⊤, by simp⟩ := HasType.quote hq
  -- Since possibly = identity, possibly ⊤ = ⊤
  have hposs_top : possibly (⊤ : ProcPred) = ⊤ := by unfold possibly; rfl
  rw [hposs_top] at hquote
  -- Now apply substitutability
  exact substitution_preserves_type hp hquote hfresh

/-! ## Progress Theorem

A well-typed process either reduces or is a value.
-/

/-- Check if a pattern is a value element (recursive).
    This is the main definition; `isValue` delegates to it for parallel bags. -/
def isValueElement : Pattern → Bool
  | .apply "PZero" [] => true
  | .apply "POutput" _ => true
  | .apply "PInput" _ => true
  | .apply "NQuote" _ => true
  | .collection .hashBag ps none => isValueElementList ps
  | _ => false
where
  /-- Check if all elements in a list are value elements -/
  isValueElementList : List Pattern → Bool
    | [] => true
    | p :: ps => isValueElement p && isValueElementList ps

/-- A process is a value (normal form) if it cannot reduce without external interaction.

    Values in ρ-calculus are:
    - `0` (nil process)
    - `n!(q)` (standalone output, blocked waiting for receiver)
    - `for(x<-n){p}` (standalone input, blocked waiting for sender)
    - `@p` (quoted process, a name value)
    - `{ P | Q | ... }` where all elements are value elements

    Note: A parallel bag with matching output/input channels CAN reduce via COMM,
    but we still call it a "value" here since `isValue ∨ reduces` holds either way. -/
def isValue : Pattern → Bool
  | .apply "PZero" [] => true
  | .apply "POutput" _ => true  -- Standalone output, blocked
  | .apply "PInput" _ => true   -- Standalone input, blocked
  | .apply "NQuote" _ => true   -- Quote is a Name value
  | .collection .hashBag ps none => isValueElement.isValueElementList ps
  | _ => false

/-- isValueElementList is equivalent to List.all isValueElement -/
theorem isValueElementList_eq_all (ps : List Pattern) :
    isValueElement.isValueElementList ps = ps.all isValueElement := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [isValueElement.isValueElementList, List.all_cons, ih]

/-- isValueElement for collections -/
theorem isValueElement_collection (ps : List Pattern) :
    isValueElement (.collection .hashBag ps none) = isValueElement.isValueElementList ps := rfl

/-- isValueElement of nested parallel matches recursive check -/
theorem isValueElement_par_iff (ps : List Pattern) :
    isValueElement (.collection .hashBag ps none) = ps.all isValueElement := by
  rw [isValueElement_collection, isValueElementList_eq_all]

/-- In empty context, all Names are quotes.

    Proof: By the typing rules, a term of sort "Name" can only be:
    - A variable (but empty context has none)
    - A quote @p (the only constructor producing Name sort)
-/
theorem empty_context_name_is_quote {n : Pattern} {α : NamePred} :
    (TypingContext.empty ⊢ n : ⟨"Name", α, by simp⟩) →
    ∃ p, n = .apply "NQuote" [p] := by
  intro h
  -- By the structure of HasType, only `var` and `quote` produce Name sort
  -- All other constructors (nil, drop, output, input, par) produce Proc sort
  generalize hτ : (⟨"Name", α, by simp⟩ : NativeType) = τ at h
  cases h with
  | var hlookup =>
    -- Variable case: empty context has no bindings
    simp [TypingContext.empty, TypingContext.lookup] at hlookup
  | quote hp =>
    -- Quote case: n = NQuote [p]
    exact ⟨_, rfl⟩
  | nil => simp [NativeType.mk.injEq] at hτ
  | drop _ => simp [NativeType.mk.injEq] at hτ
  | output _ _ => simp [NativeType.mk.injEq] at hτ
  | input _ _ => simp [NativeType.mk.injEq] at hτ
  | par _ => simp [NativeType.mk.injEq] at hτ

/-- Helper: split a list at an element -/
theorem List.exists_split_of_mem {α : Type*} {x : α} {xs : List α} (h : x ∈ xs) :
    ∃ before after, xs = before ++ [x] ++ after := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
    cases h with
    | head => exact ⟨[], ys, rfl⟩
    | tail _ hy =>
      obtain ⟨before, after, heq⟩ := ih hy
      exact ⟨y :: before, after, by simp [heq]⟩

/-- A non-value element in empty context reduces.

    This key lemma uses well-founded induction on pattern size to handle
    arbitrarily nested parallel compositions. If a well-typed closed Proc-sorted
    term is not a value element, it must contain a PDrop somewhere that can reduce. -/
theorem non_value_proc_reduces {p : Pattern} {φ : ProcPred}
    (htype : TypingContext.empty ⊢ p : ⟨"Proc", φ, by simp⟩)
    (hnotval : isValueElement p = false) :
    ∃ q, p ⇝ q := by
  -- Well-founded induction on sizeOf p
  generalize hp : sizeOf p = n
  induction n using Nat.strong_induction_on generalizing p φ with
  | _ n ih =>
    generalize hτ : (⟨"Proc", φ, by simp⟩ : NativeType) = τ at htype
    cases htype with
    | var hlookup =>
      simp [TypingContext.empty, TypingContext.lookup] at hlookup
    | nil =>
      simp [isValueElement] at hnotval
    | quote _ =>
      simp [NativeType.mk.injEq] at hτ
    | drop hn =>
      -- PDrop reduces via DROP rule
      obtain ⟨q, rfl⟩ := empty_context_name_is_quote hn
      exact ⟨q, Reduces.drop⟩
    | output _ _ =>
      simp [isValueElement] at hnotval
    | input _ _ =>
      simp [isValueElement] at hnotval
    | @par _ ps hall =>
      -- isValueElement (.collection .hashBag ps none) = ps.all isValueElement
      rw [isValueElement_par_iff] at hnotval
      -- hnotval : ps.all isValueElement = false
      -- Extract witness: some element is not a value
      have hnotval' : ¬ ps.all isValueElement = true := by simp [hnotval]
      simp only [List.all_eq_true] at hnotval'
      push_neg at hnotval'
      obtain ⟨elem, helem, helemnotval⟩ := hnotval'
      -- elem has sizeOf < sizeOf p (list membership property)
      have hmem := List.sizeOf_lt_of_mem helem
      -- sizeOf elem < sizeOf ps < sizeOf (Pattern.collection .hashBag ps none) = n
      have hsz : sizeOf elem < n := by
        have h1 : sizeOf ps ≤ sizeOf (Pattern.collection CollType.hashBag ps (none : Option String)) := by
          simp only [Pattern.collection.sizeOf_spec]
          omega
        rw [hp] at h1
        omega
      -- elem is typed with Proc sort
      have helem_typed := hall elem helem
      -- Apply induction hypothesis
      have helemnotval' : isValueElement elem = false := by
        cases h : isValueElement elem
        · rfl
        · exact absurd h helemnotval
      have hreduces := ih (sizeOf elem) hsz helem_typed helemnotval' rfl
      obtain ⟨q, hred⟩ := hreduces
      -- Lift reduction to parallel composition
      obtain ⟨before, after, hps⟩ := List.exists_split_of_mem helem
      use .collection .hashBag (before ++ [q] ++ after) none
      rw [hps]
      exact Reduces.par_any hred

/-- Progress for Proc-sorted types: a well-typed closed process either reduces or is a value.

    Key observation: For well-typed closed Procs, `isValueElement p = false` implies
    p is either PDrop (which reduces) or a parallel collection with a non-value sub-element.
-/
theorem progress_proc {p : Pattern} {φ : ProcPred} :
    (TypingContext.empty ⊢ p : ⟨"Proc", φ, by simp⟩) →
    isValue p ∨ ∃ q, p ⇝ q := by
  intro h
  generalize hτ : (⟨"Proc", φ, by simp⟩ : NativeType) = τ at h
  cases h with
  | var hlookup =>
    simp [TypingContext.empty, TypingContext.lookup] at hlookup
  | nil =>
    left; rfl
  | quote _ =>
    simp [NativeType.mk.injEq] at hτ
  | drop hn =>
    right
    obtain ⟨q, rfl⟩ := empty_context_name_is_quote hn
    exact ⟨q, Reduces.drop⟩
  | output _ _ =>
    left; rfl
  | input _ _ =>
    left; rfl
  | @par _ ps hall =>
    -- Use isValueElementList for the parallel check
    by_cases hval : isValueElement.isValueElementList ps
    · left
      simp only [isValue]
      exact hval
    · -- Some element fails isValueElement
      right
      rw [isValueElementList_eq_all] at hval
      have hval' : ¬ ps.all isValueElement = true := by simp [hval]
      simp only [List.all_eq_true] at hval'
      push_neg at hval'
      obtain ⟨elem, helem, hnotval⟩ := hval'
      -- elem is a non-value element, so it reduces by the well-founded lemma
      have htyped := hall elem helem
      have hnotval' : isValueElement elem = false := by
        cases h : isValueElement elem
        · rfl
        · exact absurd h hnotval
      obtain ⟨q, hred⟩ := non_value_proc_reduces htyped hnotval'
      -- Lift the reduction to the parallel composition
      obtain ⟨before, after, hps⟩ := List.exists_split_of_mem helem
      use .collection .hashBag (before ++ [q] ++ after) none
      rw [hps]
      exact Reduces.par_any hred

/-- Progress (general): a well-typed closed term either reduces or is a value. -/
theorem progress {p : Pattern} {τ : NativeType} :
    (TypingContext.empty ⊢ p : τ) →
    isValue p ∨ ∃ q, p ⇝ q := by
  intro h
  by_cases hsort : τ.sort = "Proc"
  · -- Proc sort: use progress_proc
    -- Rewrite τ to have explicit "Proc" sort
    obtain ⟨sort, pred, valid⟩ := τ
    simp only at hsort
    subst hsort
    exact progress_proc h
  · -- Name sort: quotes are values (no reduction rule applies)
    left
    -- τ.sort ≠ "Proc", so τ.sort = "Name" (by sort_valid)
    obtain ⟨sort, pred, valid⟩ := τ
    -- sort_valid says sort ∈ ["Proc", "Name"], and sort ≠ "Proc", so sort = "Name"
    rcases valid with _ | ⟨_, _ | ⟨_, h'⟩⟩
    · -- sort = "Proc", contradicts hsort
      exact absurd rfl hsort
    · -- sort = "Name"
      obtain ⟨q, rfl⟩ := empty_context_name_is_quote h
      rfl
    · -- sort ∈ [], contradiction
      nomatch h'

/-! ## Summary

This file establishes the type soundness of OSLF:

1. ✅ **NativeType**: Sort × Predicate pairs
2. ✅ **TypingContext**: Variable → NativeType maps
3. ✅ **HasType**: Type judgment Γ ⊢ p : τ
4. ✅ **LookupEquiv**: Context equivalence (same lookup ⇒ same typing)
5. ✅ **weakening**: If Γ ⊢ p : τ and x ∉ FV(p), then Γ,x:σ ⊢ p : τ
6. ✅ **substitutability**: Main theorem with Barendregt convention (boundFresh hypothesis)
7. ✅ **comm_preserves_type**: COMM rule soundness
8. ✅ **progress**: Trivially satisfied (placeholder reduction relation)

**Key theorems proven:**
- `substitution_preserves_type`: Uses well-founded recursion on `sizeOf p`
  - var case: direct lookup or substitution
  - nil/par cases: trivial
  - quote/drop/output cases: recursive with freshness propagation
  - input case: context permutation + weakening for binder handling
- `comm_preserves_type`: Applies substitutability with `@q : (Name, ⊤)` for `x : (Name, ⊤)`

**Proven helper lemmas:**
- `isFresh_var_neq`: Variable freshness implies inequality
- `lookup_extend_neq`: Lookup unchanged when extending with different var
- `LookupEquiv.refl`, `.symm`, `.extend`: Context equivalence is an equivalence
- `LookupEquiv.permute`: Permuted extensions are equivalent (x ≠ y)
- `LookupEquiv.shadow`: Inner binding shadows outer ((Γ,x:σ),x:τ ≃ Γ,x:τ)
- `HasType_context_equiv`: Typing respects lookup equivalence
- `mem_filter_of_mem_neq`, `not_contains_of_filter_neq`: Filter lemmas
- `isFresh_lambda`, `isFresh_apply_*`: Freshness decomposition

**All theorems in this file are fully proven (no sorries).**

The `par` typing rule was strengthened to require all elements be well-typed processes,
which enabled proving `HasType.noExplicitSubst` for the par case.

**Connection to Internal Language:**
The HasType judgment corresponds to comprehension in the topos.
When we write Γ ⊢ p : (Proc, φ), we're saying p is in the
comprehension { p : Proc | φ(p) = ⊤ }. The substitutability theorem
says this comprehension is preserved under substitution.
-/

end Mettapedia.OSLF.RhoCalculus.Soundness
