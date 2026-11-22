import Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings.Operations

/-!
# Matching one contextual metavariable on the existing shared store

A contextual hole declares an ordered subscope of the scope at its occurrence.
Its assignment is a term in that smaller scope. Matching pulls a reference back
through the declared thinning; placing the assignment back reconstructs the
original term. Both operations reuse the existing nodes and references.

`restrictRef_exact` compares the executable support check and pullback with a
semantic solution relation on unfolded binding trees. It includes scope bounds,
refusal of escaping variables, uniqueness and ambient-renaming stability.

This is the order-preserving contextual-hole operation, not a complete Miller
pattern matcher or unification modulo beta/eta. A thinning cannot reverse two
parameters. Arbitrary ordered parameter spines need additional substitution or
permutation structure; no surface notation is selected here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
namespace ContextualMatching

open Mettapedia.GSLT.LanguageDef.SignatureIndexedABT
open Thin

variable {Head : Type}

/-- Finite executable support inclusion; variables beyond the declared mask
are forbidden, rather than inherited from `sel`'s total extension. -/
def subCheck (used allowed : Thin) : Bool :=
  (List.range used.length).all fun i =>
    decide (bit used i = true → bit allowed i = true)

theorem subCheck_iff (used allowed : Thin) :
    subCheck used allowed = true ↔ Sub used allowed := by
  simp only [subCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq]
  constructor
  · intro checked i usedHere
    have inside : i < used.length := by
      by_contra outside
      have absent := bit_of_length_le (θ := used) (Nat.le_of_not_gt outside)
      rw [absent] at usedHere
      cases usedHere
    exact checked i inside usedHere
  · intro included i _ usedHere
    exact included i usedHere

theorem cut_length_le (count : ℕ) (scope : Thin) :
    (cut count scope).length ≤ scope.length := by
  induction scope generalizing count with
  | nil => cases count <;> simp
  | cons b scope ih =>
      cases count with
      | zero => simp
      | succ count =>
          cases b <;> simp only [cut_succ_false, cut_succ_true, List.length_cons]
          · exact Nat.succ_le_succ (ih (count + 1))
          · exact Nat.succ_le_succ (ih count)

/-- Re-express the source's support in the hole's own scope. No node is
visited or allocated; the source node identity is retained. -/
def projectRef (allowed : Thin) (source : Ref) : Ref :=
  ⟨cut (ones source.thin) (pull allowed source.thin), source.id⟩

def restrictRef (allowed : Thin) (source : Ref) : Option Ref :=
  if subCheck source.thin allowed then some (projectRef allowed source) else none

/-- A semantic solution has the declared finite scope, and its placement
denotes exactly the source tree. -/
def Solution (store : Store Head) (allowed : Thin) (source body : Ref) : Prop :=
  CanonRef store body ∧ body.thin.length ≤ ones allowed ∧
    rename allowed (unfold store body) = unfold store source

theorem projectRef_solution {store : Store Head} (canonical : Canonical store)
    {source : Ref} (valid : CanonRef store source) (allowed : Thin)
    (included : Sub source.thin allowed) :
    Solution store allowed source (projectRef allowed source) := by
  have counts := ones_pull included
  have enough : ones source.thin ≤ ones (pull allowed source.thin) := by omega
  have relevant := CTerm.relevant_toTree _ _ (valid.placed.ok canonical)
  refine ⟨⟨valid.valid, trimmed_cut enough, ?_⟩, ?_, ?_⟩
  · simp only [projectRef]
    rw [ones_cut enough]
    exact valid.ones_eq
  · exact (cut_length_le _ _).trans (le_of_eq (length_pull _ _))
  · simp only [unfold_eq, projectRef]
    rw [rename_comp]
    apply rename_congr_relevant relevant
    intro j below
    simp only [sel_comp]
    rw [sel_cut _ below]
    exact sel_pull included below

theorem solution_includes_support {store : Store Head} (canonical : Canonical store)
    {source body : Ref} (valid : CanonRef store source) {allowed : Thin}
    (solution : Solution store allowed source body) : Sub source.thin allowed := by
  rcases solution with ⟨bodyValid, bodyScope, placed⟩
  intro i usedHere
  have freeSource : freeAt (unfold store source) i = true := by
    rw [freeAt_unfold canonical valid]
    exact usedHere
  rw [← placed] at freeSource
  obtain ⟨j, freeBody, position⟩ := (freeAt_rename allowed (unfold store body) i).mp freeSource
  have kept : bit body.thin j = true := by
    rw [← freeAt_unfold canonical bodyValid]
    exact freeBody
  have bodyInside : j < body.thin.length := by
    by_contra outside
    have absent := bit_of_length_le (θ := body.thin) (Nat.le_of_not_gt outside)
    rw [absent] at kept
    cases kept
  have declared := (bit_sel (θ := allowed) (lt_of_lt_of_le bodyInside bodyScope)).1
  simpa only [position] using declared

theorem solution_unique {store : Store Head} (canonical : Canonical store)
    {allowed : Thin} {source first second : Ref}
    (left : Solution store allowed source first)
    (right : Solution store allowed source second) : first = second := by
  have trees : unfold store first = unfold store second :=
    rename_injective allowed _ _ (left.2.2.trans right.2.2.symm)
  exact (unfold_eq_iff canonical left.1 right.1).mp trees

/-- Exact contextual-hole matching on canonical shared references. Scope
inclusion is checked, and no new store or term representation is introduced. -/
theorem restrictRef_exact {store : Store Head} (canonical : Canonical store)
    {source : Ref} (valid : CanonRef store source) (allowed : Thin) (body : Ref) :
    restrictRef allowed source = some body ↔ Solution store allowed source body := by
  constructor
  · intro matched
    unfold restrictRef at matched
    split at matched
    · have included := (subCheck_iff _ _).mp (by assumption)
      have same : projectRef allowed source = body := Option.some.inj matched
      rw [← same]
      exact projectRef_solution canonical valid allowed included
    · cases matched
  · intro solution
    have included := solution_includes_support canonical valid solution
    have constructed := projectRef_solution canonical valid allowed included
    have same := solution_unique canonical constructed solution
    simp only [restrictRef, (subCheck_iff _ _).mpr included, ↓reduceIte, same]

theorem restrictRef_refuses_iff {store : Store Head} (canonical : Canonical store)
    {source : Ref} (valid : CanonRef store source) (allowed : Thin) :
    restrictRef allowed source = none ↔ ¬∃ body, Solution store allowed source body := by
  constructor
  · intro refused ⟨body, solution⟩
    have found := (restrictRef_exact canonical valid allowed body).mpr solution
    rw [refused] at found
    cases found
  · intro absent
    cases result : restrictRef allowed source with
    | none => rfl
    | some body =>
      exact False.elim (absent ⟨body, (restrictRef_exact canonical valid allowed body).mp result⟩)

/-- Placing an accepted assignment back gives the same canonical source
reference, not only an equal printed tree. -/
theorem restrictRef_place_back {store : Store Head} (canonical : Canonical store)
    {source body : Ref} (valid : CanonRef store source) {allowed : Thin}
    (matched : restrictRef allowed source = some body) :
    weakenRef allowed body = source := by
  have solution := (restrictRef_exact canonical valid allowed body).mp matched
  obtain ⟨placedValid, placed⟩ := weakenRef_spec canonical solution.1.placed allowed
  exact (unfold_eq_iff canonical placedValid valid).mp (placed.trans solution.2.2)

/-- Move a declared finite scope through an ambient order-preserving
renaming, retaining exactly its declared parameters. -/
def scopeImage (ambient allowed : Thin) : Thin :=
  cut (ones allowed) (comp allowed ambient)

theorem scopeImage_ones (ambient allowed : Thin) :
    ones (scopeImage ambient allowed) = ones allowed :=
  ones_cut (ones_le_ones_comp allowed ambient)

theorem solution_weaken {store : Store Head} (canonical : Canonical store)
    {source body : Ref} (valid : CanonRef store source) {allowed : Thin}
    (solution : Solution store allowed source body) (ambient : Thin) :
    Solution store (scopeImage ambient allowed) (weakenRef ambient source) body := by
  refine ⟨solution.1, ?_, ?_⟩
  · simpa only [scopeImage_ones] using solution.2.1
  · rw [(weakenRef_spec canonical valid.placed ambient).2, ← solution.2.2, rename_comp]
    apply rename_congr
    intro j free
    have kept : bit body.thin j = true := by
      rw [← freeAt_unfold canonical solution.1]
      exact free
    have inside : j < body.thin.length := by
      by_contra outside
      have absent := bit_of_length_le (θ := body.thin) (Nat.le_of_not_gt outside)
      rw [absent] at kept
      cases kept
    exact sel_cut _ (lt_of_lt_of_le inside solution.2.1)

theorem restrictRef_weaken {store : Store Head} (canonical : Canonical store)
    {source body : Ref} (valid : CanonRef store source) {allowed : Thin}
    (matched : restrictRef allowed source = some body) (ambient : Thin) :
    restrictRef (scopeImage ambient allowed) (weakenRef ambient source) = some body := by
  apply (restrictRef_exact canonical (weakenRef_spec canonical valid.placed ambient).1 _ _).mpr
  exact solution_weaken canonical valid
    ((restrictRef_exact canonical valid allowed body).mp matched) ambient

/-- A mask is an ordered embedding. It cannot also stand for a permutation
that exchanges two parameters. -/
theorem thinning_cannot_swap : ¬∃ scope : Thin, sel scope 0 = 1 ∧ sel scope 1 = 0 := by
  rintro ⟨scope, first, second⟩
  have increasing := sel_lt_sel scope (show 0 < 1 by decide)
  rw [first, second] at increasing
  omega

namespace Controls

def bound : Ref := ⟨[true], 0⟩

theorem unlisted_enclosing_variable_refused : restrictRef [] bound = none := by decide

theorem listed_enclosing_variable_accepted :
    restrictRef [true] bound = some bound := by decide

theorem skip_middle_variable :
    restrictRef [true, false, true] ⟨[false, false, true], 0⟩ =
      some ⟨[false, true], 0⟩ := by decide

theorem forbidden_middle_variable_refused :
    restrictRef [true, false, true] ⟨[false, true], 0⟩ = none := by decide

def identityTree : Term ℕ := .node 1 (.cons 1 (.idx 0) .nil)
def escapingTree : Term ℕ := .node 1 (.cons 1 (.idx 1) .nil)

theorem internal_binder_is_not_an_outer_dependency :
    (restrictRef [] (encodeR [] identityTree).2).isSome = true := by decide

theorem enclosing_variable_beneath_an_internal_binder_refused :
    restrictRef [] (encodeR [] escapingTree).2 = none := by decide

theorem substitution_does_not_capture :
    Term.instantiateAt 0 (.idx 0) escapingTree = escapingTree ∧
      Term.instantiateAt 0 (.idx 0) escapingTree ≠ identityTree := by decide

theorem same_support_does_not_determine_parameter_order :
    ([0, 1] : List ℕ).toFinset = [1, 0].toFinset ∧
      ([0, 1] : List ℕ) ≠ [1, 0] := by decide

end Controls

end ContextualMatching
end Mettapedia.Languages.ProcessCalculi.GuardedMultisetRewriting.Thinnings
