import Mettapedia.OSLF.Framework.GSLTTypeSynthesis
import Mathlib.Order.CompleteBooleanAlgebra

/-!
# Keys, the partition discipline and classification

A rule's left-hand side is a predicate on terms, the redexes of the rule. A key
refines it: a predicate that implies it. The refinements of a left-hand side,
ordered by implication, form a complete Boolean algebra, the refinement
lattice of the rule.

A family of keys is a **partition** of the rule when the keys are pairwise
exclusive and together exhaust the left-hand side. Exactly then every redex has
one key: classification is a total, single-valued function on the redexes.
Without exhaustiveness some redex has no key; without exclusivity some redex has
two.

Classification reads the redex as a term. It is well defined on equation classes
when every key is invariant under the equations; a key that reads the shape of a
representative need not be.

A pairwise exclusive family becomes a partition by adjoining the rest of the
left-hand side as one more key.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Weighting

open Mettapedia.GSLT
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis (EquationInvariant)

universe uTerm uKey

variable {Term : Type uTerm} {Key : Type uKey}

/-- The refinements of a left-hand side: predicates implying it. Ordered by
implication they form the refinement lattice of the rule. -/
def Refines (lhs φ : Term → Prop) : Prop := φ ≤ lhs

/-- The refinement lattice of a left-hand side is the interval below it in the
complete Boolean algebra of predicates. -/
theorem refines_iff_mem_Iic (lhs φ : Term → Prop) : Refines lhs φ ↔ φ ∈ Set.Iic lhs :=
  Iff.rfl

/-- **The partition discipline**: every key refines the left-hand side, two
different keys never hold of one redex, and every redex has a key. -/
structure Partition (lhs : Term → Prop) (keys : Key → Term → Prop) : Prop where
  refines : ∀ key, Refines lhs (keys key)
  exclusive : ∀ {key key' : Key} {redex : Term}, keys key redex → keys key' redex → key = key'
  exhaustive : ∀ {redex : Term}, lhs redex → ∃ key, keys key redex

namespace Partition

variable {lhs : Term → Prop} {keys : Key → Term → Prop}

/-- **Classification**: the key of a redex. -/
noncomputable def classify (partition : Partition lhs keys) (redex : {redex // lhs redex}) : Key :=
  Classical.choose (partition.exhaustive redex.property)

theorem classify_holds (partition : Partition lhs keys) (redex : {redex // lhs redex}) :
    keys (partition.classify redex) redex.val :=
  Classical.choose_spec (partition.exhaustive redex.property)

/-- **Classification is single valued**: the key of a redex is the only key that
holds of it. -/
theorem classify_eq_iff (partition : Partition lhs keys) (redex : {redex // lhs redex})
    (key : Key) : partition.classify redex = key ↔ keys key redex.val :=
  ⟨fun same => same ▸ partition.classify_holds redex,
    fun holds => partition.exclusive (partition.classify_holds redex) holds⟩

/-- **A partition is exactly a classification.** Every function that picks a
holding key for each redex is the classification. -/
theorem classify_unique (partition : Partition lhs keys)
    (pick : {redex // lhs redex} → Key) (picks : ∀ redex, keys (pick redex) redex.val) :
    pick = partition.classify :=
  funext fun redex => ((partition.classify_eq_iff redex _).mpr (picks redex)).symm

/-- A classification function makes its key predicates a partition. -/
theorem of_classify (classifyBy : {redex // lhs redex} → Key) :
    Partition lhs (fun key redex => ∃ isRedex : lhs redex, classifyBy ⟨redex, isRedex⟩ = key) where
  refines _ _ holds := holds.1
  exclusive := by
    rintro key key' redex ⟨isRedex, rfl⟩ ⟨isRedex', rfl⟩
    rfl
  exhaustive isRedex := ⟨_, isRedex, rfl⟩

/-- **Classification is well defined on equation classes when the keys are
invariant under the equations.** -/
theorem classify_eq_of_equiv (S : GSLT.{uTerm}) {keys : Key → S.Term → Prop}
    {lhs : S.Term → Prop} (partition : Partition lhs keys)
    (invariant : ∀ key, EquationInvariant S (keys key))
    {first second : {redex // lhs redex}} (equal : S.Equiv first.val second.val) :
    partition.classify first = partition.classify second :=
  ((partition.classify_eq_iff second _).mpr
    ((invariant _ equal).mp (partition.classify_holds first))).symm

/-- **Conversely, a classification that is well defined on equation classes has
invariant keys** on the redexes. -/
theorem keys_invariant_of_classify (S : GSLT.{uTerm}) {keys : Key → S.Term → Prop}
    {lhs : S.Term → Prop} (partition : Partition lhs keys)
    (classes : ∀ {first second : {redex // lhs redex}}, S.Equiv first.val second.val →
      partition.classify first = partition.classify second)
    (key : Key) {first second : {redex // lhs redex}} (equal : S.Equiv first.val second.val) :
    keys key first.val ↔ keys key second.val := by
  rw [← partition.classify_eq_iff, ← partition.classify_eq_iff, classes equal]

end Partition

/-! ## Completing an exclusive family -/

/-- The key that holds of the rest of the left-hand side: the redexes no listed
key covers. -/
def completeKeys (lhs : Term → Prop) (keys : Key → Term → Prop) : Option Key → Term → Prop
  | some key, redex => keys key redex
  | none, redex => lhs redex ∧ ∀ key, ¬ keys key redex

/-- **Completing a partition is cheap.** A family of refinements that are
pairwise exclusive becomes a partition by adjoining the rest of the left-hand
side as one more key. -/
theorem complete_partition {lhs : Term → Prop} {keys : Key → Term → Prop}
    (refines : ∀ key, Refines lhs (keys key))
    (exclusive : ∀ {key key' : Key} {redex : Term}, keys key redex → keys key' redex →
      key = key') :
    Partition lhs (completeKeys lhs keys) where
  refines
    | some key => refines key
    | none => fun _ holds => holds.1
  exclusive := by
    rintro (_ | key) (_ | key') redex holds holds'
    · rfl
    · exact absurd holds' (holds.2 key')
    · exact absurd holds (holds'.2 key)
    · exact congrArg some (exclusive holds holds')
  exhaustive := by
    intro redex isRedex
    by_cases covered : ∃ key, keys key redex
    · obtain ⟨key, holds⟩ := covered
      exact ⟨some key, holds⟩
    · exact ⟨none, isRedex, fun key holds => covered ⟨key, holds⟩⟩

/-! ## Controls -/

namespace KeyControls

/-- Keys on natural numbers below three: "zero", "one". -/
def smallKeys : Bool → ℕ → Prop
  | false, n => n = 0
  | true, n => n = 1

def belowThree (n : ℕ) : Prop := n < 3

/-- Without exhaustiveness some redex has no key: two is below three and has
neither key. -/
theorem not_exhaustive : ¬ ∀ {n : ℕ}, belowThree n → ∃ key, smallKeys key n := by
  intro exhaustive
  obtain ⟨key, holds⟩ := exhaustive (n := 2) (by decide : 2 < 3)
  cases key <;> simp [smallKeys] at holds

/-- Without exclusivity some redex has two keys. -/
def overlappingKeys : Bool → ℕ → Prop
  | false, n => n ≤ 1
  | true, n => 1 ≤ n

theorem not_exclusive :
    overlappingKeys false 1 ∧ overlappingKeys true 1 ∧ (false : Bool) ≠ true :=
  ⟨show (1 : ℕ) ≤ 1 from le_refl 1, show (1 : ℕ) ≤ 1 from le_refl 1, Bool.false_ne_true⟩

/-- Completing the small keys gives a partition of the numbers below three. -/
theorem completed : Partition belowThree (completeKeys belowThree smallKeys) :=
  complete_partition
    (fun key n holds => by cases key <;> simp_all [smallKeys, belowThree])
    (fun {key key' n} holds holds' => by
      cases key <;> cases key' <;> simp_all [smallKeys])

end KeyControls


/-! ## What a positive language cannot state -/

/-- Formulas built from atoms with truth and conjunction only: what a target
specification with finite limits supplies. -/
inductive PositiveFormula (Atom : Type uKey) where
  | top : PositiveFormula Atom
  | atom : Atom → PositiveFormula Atom
  | and : PositiveFormula Atom → PositiveFormula Atom → PositiveFormula Atom

namespace PositiveFormula

variable {Atom : Type uKey}

/-- Truth of a positive formula under a valuation of the atoms. -/
def holds (valuation : Atom → Prop) : PositiveFormula Atom → Prop
  | top => True
  | atom a => valuation a
  | and φ ψ => holds valuation φ ∧ holds valuation ψ

/-- Every positive formula holds when every atom does. -/
theorem holds_all_true : ∀ φ : PositiveFormula Atom, φ.holds (fun _ => True)
  | top => trivial
  | atom _ => trivial
  | and φ ψ => ⟨holds_all_true φ, holds_all_true ψ⟩

/-- **A positive language cannot state exclusivity.** No positive formula holds
exactly when two atoms do not both hold: positive formulas hold when every atom
does, and there exclusivity fails. So the partition discipline, stated inside
the language, needs negation. -/
theorem exclusivity_not_positive (a b : Atom) :
    ¬ ∃ φ : PositiveFormula Atom, ∀ valuation, φ.holds valuation ↔ ¬ (valuation a ∧ valuation b) :=
  fun ⟨φ, states⟩ => (states fun _ => True).mp (holds_all_true φ) ⟨trivial, trivial⟩

end PositiveFormula

end Mettapedia.GSLT.Weighting
