import Mathlib.Data.List.Infix
import Mathlib.Logic.Function.Basic

/-!
# Sequence patterns: associative matching

A sequence pattern lists, in order, literal elements, element variables (each
standing for exactly one element) and sequence variables (each standing for a
finite sequence, possibly empty). Matching a pattern against a list solves an
equation in the free monoid whose right side is ground.

* **Matching is finitary.** `matchFrom` enumerates finitely many partial
  assignments of the pattern's variables. Every total assignment that agrees
  with one of them is a matcher (`matchFrom_sound`), and every matcher agrees
  with one of them (`matchFrom_complete`); together, `matches_iff`. A
  repeated variable is an equality constraint, never two captures
  (`Controls.repeated_sequence`).
* **Why matching and not unification.** With variables on both sides the
  same equations are infinitary: `x a = a x` has the solutions `x ↦ aⁿ` and no
  finite complete set of unifiers
  (`Collections.Unification.plotkin_infinitary`). The fragment an explicit
  facility can expose with complete finite answer sets is therefore matching
  against a subject whose variables, if any, are held rigid: take the element
  type to be the subject's atoms and variables together, and the same
  matcher applies. Tail rests on both sides are the other unitary fragment:
  they are the cons view of lists, solved by syntactic unification
  (`Logic.Unification.ListSplice.Encoding.solve`).
* Two sequence variables split a list at every point, so the answer sets can
  be large (`Controls.two_sequence_variables`): a pattern with `k` sequence
  variables has at most `(n + 1) ^ k` matchers against a list of length `n`.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.Collections.SequencePatterns

universe u v w

variable {A : Type u} {E : Type v} {X : Type w}

/-- One position of a sequence pattern. -/
inductive Item (A : Type u) (E : Type v) (X : Type w) where
  /-- This element. -/
  | lit (a : A)
  /-- An element variable: exactly one element. -/
  | elem (y : E)
  /-- A sequence variable: any finite sequence, possibly empty. -/
  | seq (x : X)
  deriving DecidableEq, Repr

/-- A total assignment of the variables. -/
structure Assignment (A : Type u) (E : Type v) (X : Type w) where
  elem : E → A
  seq : X → List A

/-- The list a pattern denotes under an assignment. -/
def instantiate (σ : Assignment A E X) : List (Item A E X) → List A
  | [] => []
  | .lit a :: pattern => a :: instantiate σ pattern
  | .elem y :: pattern => σ.elem y :: instantiate σ pattern
  | .seq x :: pattern => σ.seq x ++ instantiate σ pattern

/-- An assignment of some of the variables. -/
structure Partial (A : Type u) (E : Type v) (X : Type w) where
  elem : E → Option A
  seq : X → Option (List A)

/-- Nothing assigned. -/
def Partial.empty : Partial A E X := ⟨fun _ => none, fun _ => none⟩

/-- A total assignment agrees with a partial one where the latter is defined. -/
def Agrees (ρ : Partial A E X) (σ : Assignment A E X) : Prop :=
  (∀ y a, ρ.elem y = some a → σ.elem y = a) ∧ (∀ x u, ρ.seq x = some u → σ.seq x = u)

/-- `ρ'` keeps every assignment of `ρ`. -/
def Refines (ρ ρ' : Partial A E X) : Prop :=
  (∀ y a, ρ.elem y = some a → ρ'.elem y = some a) ∧
    (∀ x u, ρ.seq x = some u → ρ'.seq x = some u)

theorem Refines.refl (ρ : Partial A E X) : Refines ρ ρ := ⟨fun _ _ h => h, fun _ _ h => h⟩

theorem Refines.trans {ρ ρ' ρ'' : Partial A E X} (first : Refines ρ ρ')
    (second : Refines ρ' ρ'') : Refines ρ ρ'' :=
  ⟨fun y a h => second.1 y a (first.1 y a h), fun x u h => second.2 x u (first.2 x u h)⟩

theorem Agrees.of_refines {ρ ρ' : Partial A E X} {σ : Assignment A E X} (refines : Refines ρ ρ')
    (agrees : Agrees ρ' σ) : Agrees ρ σ :=
  ⟨fun y a h => agrees.1 y a (refines.1 y a h), fun x u h => agrees.2 x u (refines.2 x u h)⟩

@[simp] theorem agrees_empty (σ : Assignment A E X) : Agrees Partial.empty σ :=
  ⟨fun _ _ h => (by simp [Partial.empty] at h), fun _ _ h => (by simp [Partial.empty] at h)⟩

/-- Assign an element variable. -/
def Partial.setElem [DecidableEq E] (ρ : Partial A E X) (y : E) (a : A) : Partial A E X :=
  ⟨Function.update ρ.elem y (some a), ρ.seq⟩

/-- Assign a sequence variable. -/
def Partial.setSeq [DecidableEq X] (ρ : Partial A E X) (x : X) (u : List A) : Partial A E X :=
  ⟨ρ.elem, Function.update ρ.seq x (some u)⟩

theorem refines_setElem [DecidableEq E] {ρ : Partial A E X} {y : E} (fresh : ρ.elem y = none) (a : A) :
    Refines ρ (ρ.setElem y a) := by
  refine ⟨fun z b h => ?_, fun _ _ h => h⟩
  have : z ≠ y := by rintro rfl; rw [fresh] at h; cases h
  simpa [Partial.setElem, Function.update_of_ne this] using h

theorem refines_setSeq [DecidableEq X] {ρ : Partial A E X} {x : X} (fresh : ρ.seq x = none) (u : List A) :
    Refines ρ (ρ.setSeq x u) := by
  refine ⟨fun _ _ h => h, fun z v h => ?_⟩
  have : z ≠ x := by rintro rfl; rw [fresh] at h; cases h
  simpa [Partial.setSeq, Function.update_of_ne this] using h

theorem agrees_setElem [DecidableEq E] {ρ : Partial A E X} {σ : Assignment A E X} (agrees : Agrees ρ σ) (y : E) :
    Agrees (ρ.setElem y (σ.elem y)) σ := by
  refine ⟨fun z b h => ?_, agrees.2⟩
  by_cases same : z = y
  · subst same
    simp only [Partial.setElem, Function.update_self, Option.some.injEq] at h
    exact h
  · exact agrees.1 z b (by simpa [Partial.setElem, Function.update_of_ne same] using h)

theorem agrees_setSeq [DecidableEq X] {ρ : Partial A E X} {σ : Assignment A E X} (agrees : Agrees ρ σ) (x : X) :
    Agrees (ρ.setSeq x (σ.seq x)) σ := by
  refine ⟨agrees.1, fun z v h => ?_⟩
  by_cases same : z = x
  · subst same
    simp only [Partial.setSeq, Function.update_self, Option.some.injEq] at h
    exact h
  · exact agrees.2 z v (by simpa [Partial.setSeq, Function.update_of_ne same] using h)

variable [DecidableEq A] [DecidableEq E] [DecidableEq X]

/-- The matcher: from a partial assignment, every way to extend it so that
the pattern denotes the list. A bound variable is checked; an unbound
element variable takes the next element; an unbound sequence variable tries
every prefix. -/
def matchFrom : List (Item A E X) → List A → Partial A E X → List (Partial A E X)
  | [], [], ρ => [ρ]
  | [], _ :: _, _ => []
  | .lit _ :: _, [], _ => []
  | .lit a :: pattern, b :: rest, ρ => if a = b then matchFrom pattern rest ρ else []
  | .elem _ :: _, [], _ => []
  | .elem y :: pattern, b :: rest, ρ =>
      match ρ.elem y with
      | some c => if c = b then matchFrom pattern rest ρ else []
      | none => matchFrom pattern rest (ρ.setElem y b)
  | .seq x :: pattern, subject, ρ =>
      match ρ.seq x with
      | some u => if u <+: subject then matchFrom pattern (subject.drop u.length) ρ else []
      | none => (List.range (subject.length + 1)).flatMap fun k =>
          matchFrom pattern (subject.drop k) (ρ.setSeq x (subject.take k))

/-- **Soundness.** Each partial assignment found refines the start, and every
total assignment that agrees with it makes the pattern denote the list. -/
theorem matchFrom_sound :
    ∀ (pattern : List (Item A E X)) (subject : List A) (ρ ρ' : Partial A E X),
      ρ' ∈ matchFrom pattern subject ρ →
        Refines ρ ρ' ∧ ∀ σ, Agrees ρ' σ → instantiate σ pattern = subject
  | [], [], ρ, ρ', found => by
      simp only [matchFrom, List.mem_singleton] at found
      subst found
      exact ⟨Refines.refl _, fun _ _ => rfl⟩
  | [], _ :: _, _, _, found => by simp [matchFrom] at found
  | .lit _ :: _, [], _, _, found => by simp [matchFrom] at found
  | .lit a :: pattern, b :: rest, ρ, ρ', found => by
      simp only [matchFrom] at found
      split_ifs at found with same
      · subst same
        obtain ⟨refines, denotes⟩ := matchFrom_sound pattern rest ρ ρ' found
        exact ⟨refines, fun σ agrees => by simp [instantiate, denotes σ agrees]⟩
      · simp at found
  | .elem _ :: _, [], _, _, found => by simp [matchFrom] at found
  | .elem y :: pattern, b :: rest, ρ, ρ', found => by
      simp only [matchFrom] at found
      split at found
      · rename_i c bound
        split_ifs at found with same
        · subst same
          obtain ⟨refines, denotes⟩ := matchFrom_sound pattern rest ρ ρ' found
          refine ⟨refines, fun σ agrees => ?_⟩
          rw [instantiate, denotes σ agrees, agrees.1 y c (refines.1 y c bound)]
        · simp at found
      · rename_i fresh
        obtain ⟨refines, denotes⟩ := matchFrom_sound pattern rest _ ρ' found
        refine ⟨(refines_setElem fresh b).trans refines, fun σ agrees => ?_⟩
        have assigned : σ.elem y = b :=
          agrees.1 y b (refines.1 y b (by simp [Partial.setElem]))
        rw [instantiate, denotes σ agrees, assigned]
  | .seq x :: pattern, subject, ρ, ρ', found => by
      simp only [matchFrom] at found
      split at found
      · rename_i u bound
        split_ifs at found with isPrefix
        · obtain ⟨refines, denotes⟩ := matchFrom_sound pattern _ ρ ρ' found
          refine ⟨refines, fun σ agrees => ?_⟩
          rw [instantiate, denotes σ agrees, agrees.2 x u (refines.2 x u bound)]
          obtain ⟨tail, rfl⟩ := isPrefix
          simp
        · simp at found
      · rename_i fresh
        obtain ⟨k, -, inner⟩ := List.mem_flatMap.mp found
        obtain ⟨refines, denotes⟩ := matchFrom_sound pattern _ _ ρ' inner
        refine ⟨(refines_setSeq fresh _).trans refines, fun σ agrees => ?_⟩
        have assigned : σ.seq x = subject.take k :=
          agrees.2 x _ (refines.2 x _ (by simp [Partial.setSeq]))
        rw [instantiate, denotes σ agrees, assigned, List.take_append_drop]

/-- **Completeness.** Every total assignment that agrees with the start and
makes the pattern denote the list agrees with one of the partial assignments
found. -/
theorem matchFrom_complete :
    ∀ (pattern : List (Item A E X)) (subject : List A) (ρ : Partial A E X)
      (σ : Assignment A E X), Agrees ρ σ → instantiate σ pattern = subject →
        ∃ ρ' ∈ matchFrom pattern subject ρ, Agrees ρ' σ
  | [], subject, ρ, σ, agrees, denotes => by
      subst denotes
      exact ⟨ρ, by simp [instantiate, matchFrom], agrees⟩
  | .lit a :: pattern, subject, ρ, σ, agrees, denotes => by
      subst denotes
      obtain ⟨ρ', found, agrees'⟩ := matchFrom_complete pattern _ ρ σ agrees rfl
      exact ⟨ρ', by simpa [instantiate, matchFrom] using found, agrees'⟩
  | .elem y :: pattern, subject, ρ, σ, agrees, denotes => by
      subst denotes
      cases bound : ρ.elem y with
      | some c =>
          have same : σ.elem y = c := agrees.1 y c bound
          obtain ⟨ρ', found, agrees'⟩ := matchFrom_complete pattern _ ρ σ agrees rfl
          refine ⟨ρ', ?_, agrees'⟩
          simp only [instantiate, matchFrom, bound, same, if_true]
          exact found
      | none =>
          obtain ⟨ρ', found, agrees'⟩ :=
            matchFrom_complete pattern _ (ρ.setElem y (σ.elem y)) σ (agrees_setElem agrees y) rfl
          refine ⟨ρ', ?_, agrees'⟩
          simp only [instantiate, matchFrom, bound]
          exact found
  | .seq x :: pattern, subject, ρ, σ, agrees, denotes => by
      subst denotes
      cases bound : ρ.seq x with
      | some u =>
          have same : σ.seq x = u := agrees.2 x u bound
          obtain ⟨ρ', found, agrees'⟩ := matchFrom_complete pattern _ ρ σ agrees rfl
          refine ⟨ρ', ?_, agrees'⟩
          simp only [instantiate, matchFrom, bound, same, List.prefix_append, if_true,
            List.drop_left]
          exact found
      | none =>
          obtain ⟨ρ', found, agrees'⟩ :=
            matchFrom_complete pattern _ (ρ.setSeq x (σ.seq x)) σ (agrees_setSeq agrees x) rfl
          refine ⟨ρ', ?_, agrees'⟩
          simp only [instantiate, matchFrom, bound]
          refine List.mem_flatMap.mpr ⟨(σ.seq x).length, ?_, ?_⟩
          · simp only [List.mem_range, List.length_append]
            omega
          · simpa only [List.drop_left, List.take_left] using found

/-- **Matching is finitary.** The matchers of a pattern against a list are
exactly the total assignments that agree with one of the finitely many
partial assignments `matchFrom` finds. -/
theorem matches_iff (pattern : List (Item A E X)) (subject : List A) (σ : Assignment A E X) :
    instantiate σ pattern = subject ↔
      ∃ ρ ∈ matchFrom pattern subject Partial.empty, Agrees ρ σ := by
  constructor
  · exact matchFrom_complete pattern subject _ σ (agrees_empty σ)
  · rintro ⟨ρ, found, agrees⟩
    exact (matchFrom_sound pattern subject _ ρ found).2 σ agrees

/-! ## Controls -/

namespace Controls

/-- `[$xs 1 $ys]` against `[2 1 3 1]`: two matchers, one per occurrence of `1`. -/
theorem split_at_each_occurrence :
    ((matchFrom [.seq 0, .lit 1, .seq 1] [2, 1, 3, 1] (Partial.empty : Partial ℕ ℕ ℕ)).map
      fun ρ => (ρ.seq 0, ρ.seq 1)) = [(some [2], some [3, 1]), (some [2, 1, 3], some [])] := by
  decide

/-- A repeated sequence variable is an equality: `[$xs $xs]` matches
`[1 2 1 2]` once, with `$xs = [1 2]`, and `[1 2 1]` not at all. -/
theorem repeated_sequence :
    ((matchFrom [.seq 0, .seq 0] [1, 2, 1, 2] (Partial.empty : Partial ℕ ℕ ℕ)).map
        fun ρ => ρ.seq 0) = [some [1, 2]] ∧
      matchFrom [.seq 0, .seq 0] [1, 2, 1] (Partial.empty : Partial ℕ ℕ ℕ) = [] := by
  decide

/-- An element variable takes exactly one element; a sequence variable any
number: `[$h $*t]` against `[]` has no matcher, against `[1 2]` one. -/
theorem element_and_sequence :
    matchFrom [.elem 0, .seq 0] [] (Partial.empty : Partial ℕ ℕ ℕ) = [] ∧
      ((matchFrom [.elem 0, .seq 0] [1, 2] (Partial.empty : Partial ℕ ℕ ℕ)).map
        fun ρ => (ρ.elem 0, ρ.seq 0)) = [(some 1, some [2])] := by
  decide

/-- Two sequence variables split a list of length three at four points. -/
theorem two_sequence_variables :
    (matchFrom [.seq 0, .seq 1] [5, 6, 7] (Partial.empty : Partial ℕ ℕ ℕ)).length = 4 := by
  decide

end Controls

end Mettapedia.Algebra.Collections.SequencePatterns
