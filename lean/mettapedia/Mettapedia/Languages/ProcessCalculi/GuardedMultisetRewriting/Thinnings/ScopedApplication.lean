import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.ContextualMatching
import Mettapedia.GSLT.LanguageDef.ScopedABTApplication
import Mettapedia.TypeTheory.ScopeDependencies

/-!
# One scoped application action and inferred dependency interfaces

The generic simultaneous operation acts on the same binding trees as the
existing thinned store. Its order-preserving case is exactly the old thinning
action. Finite sets of permitted variables compile to actual bit-vector
thinnings, connecting the scope-map factorization to this representation.

A term's syntactic support is read from its reference. Closing it under a
supplied finite context-dependency graph computes a permitted interface that
the existing contextual-hole matcher accepts. Explicit closed bounds and the
inferred minimum are compared by the same inclusion law. No annotation is
required from an ordinary program, and no logical promotion theorem is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
namespace ScopedApplication

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Thin

variable {Head : Type} {n k : ℕ}

theorem lift_selection (d : ℕ) (θ : Thin) :
    SortedSignatureIndexedABT.Term.liftRenaming (List.replicate d ())
        (fun _ : Unit => sel θ) = fun _ => sel (keepN d θ) := by
  funext sort i
  cases sort
  simp [SortedSignatureIndexedABT.Term.liftRenaming,
    SortedSignatureIndexedABT.Term.binderCount, SortedSignatureIndexedABT.Term.liftIndex,
    sel_keepN]

mutual

theorem encode_rename (θ : Thin) (t : Term Head) :
    SingleSort.encode (rename θ t) =
      SortedSignatureIndexedABT.Term.parallelRename (fun _ : Unit => sel θ) (SingleSort.encode t) := by
  cases t with
  | idx i => rfl
  | node h fs => exact congrArg (SortedSignatureIndexedABT.Term.node h) (encode_renameFields θ fs)

theorem encode_renameFields (θ : Thin) (fs : Fields Head) :
    SingleSort.encodeFields (renameFields θ fs) =
      SortedSignatureIndexedABT.Term.Fields.parallelRename (fun _ : Unit => sel θ)
        (SingleSort.encodeFields fs) := by
  cases fs with
  | nil => rfl
  | cons d t rest =>
      simp only [renameFields_cons, SingleSort.encodeFields,
        SortedSignatureIndexedABT.Term.Fields.parallelRename, lift_selection]
      rw [encode_rename, encode_renameFields]

end

/-- The general operation and the thinned store share their ordered action. -/
theorem renameMany_selection (θ : Thin) (t : Term Head) :
    Term.renameMany (sel θ) t = rename θ t := by
  apply SingleSort.encode_injective
  rw [Term.encode_renameMany, encode_rename]

def mask (allowed : Finset (Fin n)) : Thin :=
  List.ofFn fun i : Fin n => decide (i ∈ allowed)

@[simp] theorem mask_length (allowed : Finset (Fin n)) : (mask allowed).length = n := by
  simp [mask]

theorem bit_eq_get (θ : Thin) (i : ℕ) : bit θ i = θ[i]?.getD false := by
  induction θ generalizing i with
  | nil => simp
  | cons b θ ih => cases i <;> simp [ih]

@[simp] theorem mask_bit (allowed : Finset (Fin n)) (i : Fin n) :
    bit (mask allowed) i.val = decide (i ∈ allowed) := by
  simp [bit_eq_get, mask, i.isLt]

theorem ones_ofFn (predicate : Fin n → Bool) :
    ones (List.ofFn predicate) = (Finset.univ.filter fun i => predicate i = true).card := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.card_eq_sum_ones, Finset.sum_filter, Fin.sum_univ_succ]
      rw [List.ofFn_succ]
      have tail := ih (fun i => predicate i.succ)
      rw [Finset.card_eq_sum_ones, Finset.sum_filter] at tail
      cases first : predicate 0
      · simpa only [first, ones_false, Bool.false_eq_true, ↓reduceIte, zero_add] using tail
      · simp only [ones_true, ↓reduceIte]
        omega

@[simp] theorem mask_ones (allowed : Finset (Fin n)) : ones (mask allowed) = allowed.card := by
  simp [mask, ones_ofFn]

def selection (allowed : Finset (Fin n)) (count : allowed.card = k) (i : Fin k) : Fin n :=
  ⟨sel (mask allowed) i.val, by
    have inside : i.val < ones (mask allowed) := by simp [count]
    simpa using (bit_sel inside).2⟩

theorem selection_mem (allowed : Finset (Fin n)) (count : allowed.card = k) (i : Fin k) :
    selection allowed count i ∈ allowed := by
  have inside : i.val < ones (mask allowed) := by simp [count]
  have selected := (bit_sel inside).1
  have eq := mask_bit allowed (selection allowed count i)
  change bit (mask allowed) (sel (mask allowed) i.val) = _ at eq
  rw [selected] at eq
  exact of_decide_eq_true eq.symm

theorem selection_strictMono (allowed : Finset (Fin n)) (count : allowed.card = k) :
    StrictMono (selection allowed count) := by
  intro i j smaller
  exact sel_lt_sel (mask allowed) smaller

theorem selection_eq_ordered (allowed : Finset (Fin n)) (count : allowed.card = k) :
    selection allowed count = allowed.orderEmbOfFin count :=
  Finset.orderEmbOfFin_unique count (selection_mem allowed count) (selection_strictMono allowed count)

/-- Every injective finite argument map has a factorization using an actual
bit-vector thinning and a permutation of the argument slots. -/
theorem finite_injection_factor (f : Fin k → Fin n) (injective : Function.Injective f) (i : Fin k) :
    f i = selection (Mettapedia.TypeTheory.ScopeMapFactorization.support f)
      (Mettapedia.TypeTheory.ScopeMapFactorization.card_support f injective)
      (Mettapedia.TypeTheory.ScopeMapFactorization.permutationIndex f injective i) := by
  rw [selection_eq_ordered]
  exact Mettapedia.TypeTheory.ScopeMapFactorization.factor f injective i

def used (width : ℕ) (reference : Ref) : Finset (Fin width) :=
  Finset.univ.filter fun i => bit reference.thin i.val = true

@[simp] theorem mem_used (width : ℕ) (reference : Ref) (i : Fin width) :
    i ∈ used width reference ↔ bit reference.thin i.val = true := by simp [used]

theorem support_inclusion_iff (reference : Ref) (within : reference.thin.length ≤ n)
    (allowed : Finset (Fin n)) :
    Sub reference.thin (mask allowed) ↔ used n reference ⊆ allowed := by
  constructor
  · intro included i present
    have kept := included i.val ((mem_used _ _ _).mp present)
    simpa using kept
  · intro included i present
    have inside : i < n := by
      by_contra outside
      have absent := bit_of_length_le (θ := reference.thin)
        (within.trans (Nat.le_of_not_gt outside))
      rw [absent] at present
      cases present
    have accepted := included ((mem_used n reference ⟨i, inside⟩).mpr present)
    exact (mask_bit allowed ⟨i, inside⟩).trans (by simpa using accepted)

def inferredMask (deps : Mettapedia.TypeTheory.ScopeDependencies.Dependencies n) (reference : Ref) : Thin :=
  mask (Mettapedia.TypeTheory.ScopeDependencies.infer deps (used n reference))

theorem inferred_mask_accepts (deps : Mettapedia.TypeTheory.ScopeDependencies.Dependencies n)
    (reference : Ref) (within : reference.thin.length ≤ n) :
    (ContextualMatching.restrictRef (inferredMask deps reference) reference).isSome = true := by
  have included := (support_inclusion_iff reference within _).mpr
    (Mettapedia.TypeTheory.ScopeDependencies.infer_contains deps (used n reference))
  simp [inferredMask, ContextualMatching.restrictRef,
    (ContextualMatching.subCheck_iff _ _).mpr included]

theorem explicit_iff_inferred (deps : Mettapedia.TypeTheory.ScopeDependencies.Dependencies n)
    (reference : Ref) (within : reference.thin.length ≤ n) (allowed : Finset (Fin n))
    (closed : Mettapedia.TypeTheory.ScopeDependencies.Closed deps allowed) :
    ContextualMatching.subCheck reference.thin (mask allowed) = true ↔
      Mettapedia.TypeTheory.ScopeDependencies.infer deps (used n reference) ⊆ allowed := by
  rw [ContextualMatching.subCheck_iff, support_inclusion_iff reference within,
    Mettapedia.TypeTheory.ScopeDependencies.explicit_iff_inferred deps closed]

theorem all_available_variables_are_an_admissible_interface (reference : Ref)
    (within : reference.thin.length ≤ n) :
    ContextualMatching.subCheck reference.thin (mask (Finset.univ : Finset (Fin n))) = true := by
  rw [ContextualMatching.subCheck_iff, support_inclusion_iff reference within]
  exact Finset.subset_univ _

/-- The first support boundary survives append-only growth of its immutable
term store. This is not a claim about arbitrary mutations of theory or worlds. -/
theorem solution_prefix {store larger : Store Head} (canonical : Canonical store)
    (growth : store <+: larger) {source body : Ref} (valid : CanonRef store source)
    {allowed : Thin} (solution : ContextualMatching.Solution store allowed source body) :
    ContextualMatching.Solution larger allowed source body := by
  refine ⟨solution.1.prefix growth, solution.2.1, ?_⟩
  rw [unfold_prefix canonical.topo growth solution.1.valid,
    unfold_prefix canonical.topo growth valid.valid]
  exact solution.2.2

end ScopedApplication
end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
