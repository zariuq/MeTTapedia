import Mathlib.Data.Multiset.MapFold
import Mathlib.Logic.Equiv.Bool

/-!
# Selection, symmetry, and the scope of commitment

An unordered answer bag supplies no distinguished occurrence. A deterministic
selector that returns an answer on every nonempty bag cannot respect even all
Boolean renamings. The two-element Boolean bag and negation give the obstruction.
This also rules out a natural deterministic selector for the nonempty finite-bag
functor: naturality would in particular respect this permutation.

The relation "the chosen value is a member" does respect equivalences, and an
ordered traversal has a natural head operation. Thus an any-witness specification
is compatible with a scheduler-supplied traversal; it need not prescribe a
canonical winner for the unordered bag.

The final control checks the substitution law for a unary algebraic operation.
Truncating a computation before sequencing differs from truncating after it.
This is a concrete law failure, not an inference merely from the absence of a
monad morphism. These are finite pure controls; effects and resource consumption
require their own state semantics.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.EquivariantSelection

universe u v

/-- The permitted values of an any-witness observation. Multiplicity is retained
in the source bag, although this particular relation observes only membership. -/
def Admissible {A : Type u} (answers : Multiset A) (value : A) : Prop :=
  value ∈ answers

theorem admissible_map_equiv {A : Type u} {B : Type v} (e : A ≃ B)
    (answers : Multiset A) (value : A) :
    Admissible (answers.map e) (e value) ↔ Admissible answers value := by
  constructor
  · intro h
    obtain ⟨other, member, same⟩ := Multiset.mem_map.mp h
    exact e.injective same ▸ member
  · intro h
    exact Multiset.mem_map.mpr ⟨value, h, rfl⟩

/-- The unordered candidate bag is unchanged by exchanging its two values. -/
def booleanPair : Multiset Bool := {false, true}

theorem booleanPair_nonempty : booleanPair ≠ 0 := by
  intro equal
  have cards := congrArg Multiset.card equal
  simp [booleanPair] at cards

theorem booleanPair_swap : booleanPair.map Equiv.boolNot = booleanPair := by
  change (true ::ₘ false ::ₘ 0) = (false ::ₘ true ::ₘ 0)
  exact Multiset.cons_swap true false 0

/-- Even totality and equivariance alone are incompatible; no additional
assumption that the result is a member is needed for the Boolean witness. -/
theorem no_equivariant_selector (select : Multiset Bool → Option Bool)
    (total : ∀ answers, answers ≠ 0 → (select answers).isSome = true)
    (equivariant : ∀ (e : Equiv.Perm Bool) answers,
      select (answers.map e) = (select answers).map e) : False := by
  have same := equivariant Equiv.boolNot booleanPair
  rw [booleanPair_swap] at same
  have existsAnswer := total booleanPair booleanPair_nonempty
  cases chosen : select booleanPair with
  | none => simp [chosen] at existsAnswer
  | some value =>
      cases value <;> simp [chosen, Equiv.boolNot] at same

/-- Supplying an order changes the interface: head selection does respect all
maps of payloads, without requiring any order on those payloads themselves. -/
theorem head_map {A : Type u} {B : Type v} (f : A → B) (answers : List A) :
    (answers.map f).head? = answers.head?.map f := by
  cases answers <;> rfl

/-- Both candidates remain legal under the unordered any-witness contract. -/
theorem both_values_admissible :
    Admissible booleanPair false ∧ Admissible booleanPair true := by
  unfold Admissible booleanPair
  decide

/-- Hard left-pruning cannot retain distinct committed computations after
quotienting choice by commutativity. The search scope must retain control
structure that the completed bag observation forgets. -/
theorem commutative_pruning_collapses_commits {C : Type u}
    (choice : C → C → C) (commit : C → C)
    (commutes : ∀ left right, choice left right = choice right left)
    (prunes : ∀ chosen other, choice (commit chosen) other = commit chosen)
    (first second : C) : commit first = commit second := by
  calc
    commit first = choice (commit first) (commit second) := (prunes first _).symm
    _ = choice (commit second) (commit first) := commutes _ _
    _ = commit second := prunes second _

/-- In particular these laws cannot describe a commitment that preserves the
distinction between two Boolean results. -/
theorem no_commutative_distinct_commit {C : Type u}
    (choice : C → C → C) (commit : C → C) (result : Bool → C)
    (commutes : ∀ left right, choice left right = choice right left)
    (prunes : ∀ chosen other, choice (commit chosen) other = commit chosen)
    (distinct : commit (result false) ≠ commit (result true)) : False := by
  exact distinct
    (commutative_pruning_collapses_commits choice commit commutes prunes _ _)

/-- Ordinary bag union preserves both answer occurrences rather than applying
the left-pruning law. This is the positive bag behavior the scope must retain
outside a committed region. -/
theorem bag_union_retains_both :
    ([false] : Multiset Bool) + [true] = booleanPair ∧
      ([false] : Multiset Bool) + [true] ≠ [false] := by
  constructor
  · rfl
  · intro equal
    have cards := congrArg Multiset.card equal
    simp at cards

/-- A particular finite traversal's once operation. This does not prescribe
that traversal as the MeTTa language's semantic answer order. -/
def once {A : Type u} (answers : List A) : List A := answers.take 1

/-- The first candidate fails its continuation; the second candidate succeeds. -/
def acceptTrue : Bool → List Nat
  | false => []
  | true => [7]

theorem once_before_bind_loses_answer :
    (once [false, true]).flatMap acceptTrue = [] ∧
      once ([false, true].flatMap acceptTrue) = [7] := by decide

/-- The unary operation does not commute with substitution into returned
values, the relevant algebraicity law in this list interpretation. -/
theorem once_not_algebraic :
    ¬ (∀ (answers : List Bool) (next : Bool → List Nat),
      (once answers).flatMap next = once (answers.flatMap next)) := by
  intro commutes
  have impossible := commutes [false, true] acceptTrue
  have left := once_before_bind_loses_answer.1
  have right := once_before_bind_loses_answer.2
  rw [left, right] at impossible
  cases impossible

end Mettapedia.Machines.Cursor.EquivariantSelection
