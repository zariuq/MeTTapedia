import Mettapedia.Algebra.SupportSeparatedDecomposition

/-!
# One-pass decisions for separated inventory scopes

The procedure traverses an actual occurrence list once, classifying every
occurrence and retaining both complete multiset components. Its earned
filter readout makes the procedure independent of list permutation, so it
descends to the multiset quotient. Independently supplied scope tests decide
the existential composite predicate under the proved support discipline.
The account counts classifier queries; it does not price predicate evaluation
or provide funding authority.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.SupportSeparatedDecomposition

universe u

variable {Name : Type u}

@[ext] structure CountedParts (Name : Type u) where
  first : Multiset Name
  second : Multiset Name
  queries : Nat

/-- One classifier query is issued for each encountered occurrence. -/
def partitionList (classify : Name → Bool) : List Name → CountedParts Name
  | [] => ⟨0, 0, 0⟩
  | name :: rest =>
      let tail := partitionList classify rest
      if classify name then
        ⟨name ::ₘ tail.first, tail.second, tail.queries + 1⟩
      else
        ⟨tail.first, name ::ₘ tail.second, tail.queries + 1⟩

/-- The independently defined filters recover all occurrences and the
actual recursion makes exactly one classifier query per occurrence. -/
theorem partitionList_readout (classify : Name → Bool) (values : List Name) :
    (partitionList classify values).first = leftPart classify (values : Multiset Name) ∧
    (partitionList classify values).second = rightPart classify (values : Multiset Name) ∧
    (partitionList classify values).queries = values.length := by
  induction values with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons name rest induction =>
      rcases induction with ⟨first, second, queries⟩
      cases classified : classify name <;>
        simp [partitionList, classified, first, second, queries, leftPart, rightPart]

theorem partitionList_permutation (classify : Name → Bool)
    {first second : List Name} (permuted : first.Perm second) :
    partitionList classify first = partitionList classify second := by
  have same : (first : Multiset Name) = second := Multiset.coe_eq_coe.mpr permuted
  obtain ⟨firstRead, secondRead, queryRead⟩ := partitionList_readout classify first
  obtain ⟨firstRead', secondRead', queryRead'⟩ := partitionList_readout classify second
  apply CountedParts.ext
  · exact firstRead.trans ((congrArg (leftPart classify) same).trans firstRead'.symm)
  · exact secondRead.trans ((congrArg (rightPart classify) same).trans secondRead'.symm)
  · exact queryRead.trans (permuted.length_eq.trans queryRead'.symm)

/-- The procedure descends to actual unordered occurrence inventories. -/
def partitionInventory (classify : Name → Bool) (inventory : Multiset Name) :
    CountedParts Name :=
  Quotient.lift (partitionList classify)
    (fun _ _ permuted => partitionList_permutation classify permuted) inventory

theorem partitionInventory_readout (classify : Name → Bool) (inventory : Multiset Name) :
    (partitionInventory classify inventory).first = leftPart classify inventory ∧
    (partitionInventory classify inventory).second = rightPart classify inventory ∧
    (partitionInventory classify inventory).queries = inventory.card := by
  refine Quotient.inductionOn inventory ?_
  intro values
  exact partitionList_readout classify values

theorem partitionInventory_complete (classify : Name → Bool) (inventory : Multiset Name) :
    (partitionInventory classify inventory).first +
      (partitionInventory classify inventory).second = inventory := by
  obtain ⟨first, second, _⟩ := partitionInventory_readout classify inventory
  rw [first, second]
  exact parts_add classify inventory

/-- Independent executable scope tests are applied to the computed halves. -/
def decideComposite (classify : Name → Bool)
    (leftTest rightTest : Multiset Name → Bool) (inventory : Multiset Name) : Bool :=
  let parts := partitionInventory classify inventory
  leftTest parts.first && rightTest parts.second

theorem decideComposite_iff {classify : Name → Bool}
    {left right : Multiset Name → Prop}
    (first : LeftSupported classify left) (second : RightSupported classify right)
    (leftTest rightTest : Multiset Name → Bool)
    (leftReadout : ∀ inventory, leftTest inventory = true ↔ left inventory)
    (rightReadout : ∀ inventory, rightTest inventory = true ↔ right inventory)
    (inventory : Multiset Name) :
    decideComposite classify leftTest rightTest inventory = true ↔
      Composite left right inventory := by
  obtain ⟨firstRead, secondRead, _⟩ := partitionInventory_readout classify inventory
  simp only [decideComposite, Bool.and_eq_true, firstRead, secondRead,
    leftReadout, rightReadout]
  exact (composite_iff_parts first second inventory).symm

end Mettapedia.Algebra.SupportSeparatedDecomposition
