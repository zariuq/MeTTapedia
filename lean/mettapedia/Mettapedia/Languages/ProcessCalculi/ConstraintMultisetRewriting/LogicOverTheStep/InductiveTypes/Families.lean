import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.InductiveTypes.Lists

/-!
# An indexed family on the step: vectors, on closed rows

Vectors are rows `vecRow n l` at the handle `vec`, made by `vnil` at index `zeroE` and by `vcons`,
which reads `natRow x` and `vecRow n l` and makes `vecRow (succE n) (consE x l)`; with the number
constructors they read (`vecFamilyRules`).

* **What the region holds** (`vecFamily_generated_iff`): the rows of the numerals and the rows
  `vecRow (numeral ks.length) (listE ks)`. **The intrinsic family is the extrinsic one on closed
  rows** (`vecRow_generated_iff_extrinsic`): a vector row is generated exactly when its list is a
  generated list of numbers and its index is the numeral of that list's length. **The fibre over an
  index** (`vec_fibre`): the generated rows at index `n` are the lists of numerals whose length has
  numeral `n`; over an index that is not a numeral, such as `junkE`, there are none (`no_junk_index`),
  and a list sits at no other index than its length (`wrong_index_not_generated`).
* **One derivation per row** (`Derivation`, `derivation_unique`): derivations as data are unique for
  rules in which a conclusion determines its premises (`SyntaxDirected`), as the vector rules are
  (`vecFamily_syntaxDirected`); every generated vector row has exactly one derivation
  (`vecRow_one_derivation`). **Control** (`twoWays_two_derivations`): with two rules making one row,
  that row has two different derivations.

Against the extrinsic typed syntax of the model, whose elements are pairs of an untyped expression and
a typing proof: its two defects do not appear here. An element at a variable index is an open term,
and rows on the step are closed: every generated row's index is a closed numeral, the computed one.
Two typing proofs of one expression are two elements there; here a row carries no proof, its
membership is a proposition about the row, and its derivation is unique.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.InductiveTypes

open WhenTypesApply.ThatsAll
open NamesOnTheStep NamesOnTheStep.IssuingControls

namespace Families

/-- The constructors of vectors, with those of the numbers they read. -/
def vecFamilyRules : Set (List Expr × Expr) := natRules ∪ vecRules

theorem mem_vecRules {ps : List Expr} {r : Expr} :
    (ps, r) ∈ vecRules ↔ (ps = [] ∧ r = vecRow zeroE nilE) ∨
      ∃ x n l, ps = [natRow x, vecRow n l] ∧ r = vecRow (succE n) (consE x l) := by
  simp [vecRules]

theorem vnil_mem : (([] : List Expr), vecRow zeroE nilE) ∈ vecFamilyRules :=
  Or.inr (mem_vecRules.mpr (Or.inl ⟨rfl, rfl⟩))

theorem vcons_mem (x n l : Expr) :
    ([natRow x, vecRow n l], vecRow (succE n) (consE x l)) ∈ vecFamilyRules :=
  Or.inr (mem_vecRules.mpr (Or.inr ⟨x, n, l, rfl, rfl⟩))

theorem natRow_ne_vecRow (x n l : Expr) : natRow x ≠ vecRow n l := by
  simp [natRow, vecRow]

theorem vecRow_injective {n l n' l' : Expr} (same : vecRow n l = vecRow n' l') : n = n' ∧ l = l' := by
  simp only [vecRow, Expr.app.injEq, true_and] at same
  exact same

/-- Rows of numerals, and rows of lists of numerals at the numeral of their length. -/
def IsVecRow (r : Expr) : Prop :=
  (∃ k, r = natRow (numeral k)) ∨ ∃ ks : List ℕ, r = vecRow (numeral ks.length) (listE ks)

theorem isVecRow_ruleClosed : RuleClosed vecFamilyRules IsVecRow := by
  intro ps r declared premises
  rcases declared with declared | declared
  · rcases Numbers.mem_natRules.mp declared with ⟨rfl, rfl⟩ | ⟨x, rfl, rfl⟩
    · exact Or.inl ⟨0, rfl⟩
    · rcases premises _ (List.mem_singleton_self _) with ⟨k, same⟩ | ⟨ks, same⟩
      · exact Or.inl ⟨k + 1, by rw [natRow_injective same]; rfl⟩
      · exact absurd same (natRow_ne_vecRow _ _ _)
  · rcases mem_vecRules.mp declared with ⟨rfl, rfl⟩ | ⟨x, n, l, rfl, rfl⟩
    · exact Or.inr ⟨[], rfl⟩
    · rcases premises (natRow x) (List.mem_cons_self ..) with ⟨k, sameX⟩ | ⟨ks, sameX⟩
      · rcases premises (vecRow n l) (List.mem_cons_of_mem _ (List.mem_cons_self ..)) with
          ⟨j, sameV⟩ | ⟨ks, sameV⟩
        · exact absurd sameV.symm (natRow_ne_vecRow _ _ _)
        · obtain ⟨rfl, rfl⟩ := vecRow_injective sameV
          refine Or.inr ⟨k :: ks, ?_⟩
          rw [natRow_injective sameX]
          rfl
      · exact absurd sameX (natRow_ne_vecRow _ _ _)

theorem vecRow_generated {r : Expr} (row : IsVecRow r) : Generated vecFamilyRules ∅ r := by
  rcases row with ⟨k, rfl⟩ | ⟨ks, rfl⟩
  · exact WhenTypesApply.TwoKinds.generated_mono natRules ∅ Set.subset_union_left le_rfl
      (Numbers.numeral_generated k)
  · induction ks with
    | nil => exact Generated.rule vnil_mem fun _ member => absurd member List.not_mem_nil
    | cons k ks ih =>
        refine Generated.rule (vcons_mem (numeral k) (numeral ks.length) (listE ks))
          fun p member => ?_
        rcases List.mem_cons.mp member with rfl | member
        · exact WhenTypesApply.TwoKinds.generated_mono natRules ∅ Set.subset_union_left le_rfl
            (Numbers.numeral_generated k)
        · rw [List.mem_singleton.mp member]
          exact ih

/-- **The generated rows of the family.** -/
theorem vecFamily_generated_iff {r : Expr} : Generated vecFamilyRules ∅ r ↔ IsVecRow r :=
  ⟨generated_induction isVecRow_ruleClosed, vecRow_generated⟩

/-- **The intrinsic family is the extrinsic one on closed rows**: a vector row is generated exactly
when its list is a generated list of numbers and its index is the numeral of the list's length. -/
theorem vecRow_generated_iff_extrinsic (n l : Expr) :
    Generated vecFamilyRules ∅ (vecRow n l) ↔
      Generated Lists.listRules ∅ (lstRow l) ∧ ∃ ks : List ℕ, l = listE ks ∧ n = numeral ks.length := by
  rw [vecFamily_generated_iff, Lists.listRules_generated_iff]
  constructor
  · rintro (⟨k, same⟩ | ⟨ks, same⟩)
    · exact absurd same.symm (natRow_ne_vecRow _ _ _)
    · obtain ⟨rfl, rfl⟩ := vecRow_injective same
      exact ⟨Or.inr ⟨ks, rfl⟩, ks, rfl, rfl⟩
  · rintro ⟨-, ks, rfl, rfl⟩
    exact Or.inr ⟨ks, rfl⟩

/-- **The fibre over an index**: the generated rows at index `n` are the lists of numerals whose length
has numeral `n`. -/
theorem vec_fibre (n : Expr) :
    {l | Generated vecFamilyRules ∅ (vecRow n l)} = {l | ∃ ks : List ℕ, l = listE ks ∧ n = numeral ks.length} := by
  ext l
  simp only [Set.mem_ofPred_eq, vecRow_generated_iff_extrinsic]
  constructor
  · exact fun found => found.2
  · rintro ⟨ks, rfl, rfl⟩
    exact ⟨Lists.listRow_generated (Or.inr ⟨ks, rfl⟩), ks, rfl, rfl⟩

/-- **No row at an index that is not a numeral.** -/
theorem no_junk_index (l : Expr) : ¬ Generated vecFamilyRules ∅ (vecRow junkE l) := by
  rw [vecRow_generated_iff_extrinsic]
  rintro ⟨-, ks, -, same⟩
  exact Numbers.numeral_ne_junk _ same.symm

/-- **A list sits at no other index than its length**: the empty list is not a vector of length one. -/
theorem wrong_index_not_generated : ¬ Generated vecFamilyRules ∅ (vecRow (numeral 1) nilE) := by
  rw [vecRow_generated_iff_extrinsic]
  rintro ⟨-, ks, same, index⟩
  cases ks with
  | nil => exact absurd (numeral_injective index) (by decide)
  | cons k ks => simp [listE, consE, nilE] at same

/-! ## Derivations as data -/

/-- **A derivation**: a declared rule and derivations of its premises. -/
inductive Derivation (rules : Set (List Expr × Expr)) : Expr → Type
  | rule {ps : List Expr} {r : Expr} : (ps, r) ∈ rules →
      ((p : Expr) → p ∈ ps → Derivation rules p) → Derivation rules r

/-- The premises of a derivation's last rule. -/
def Derivation.premises {rules : Set (List Expr × Expr)} {r : Expr} : Derivation rules r → List Expr
  | .rule (ps := ps) _ _ => ps

/-- **Generation is the existence of a derivation.** -/
theorem generated_iff_nonempty (rules : Set (List Expr × Expr)) (r : Expr) :
    Generated rules ∅ r ↔ Nonempty (Derivation rules r) := by
  constructor
  · intro generated
    induction generated with
    | base inside => exact absurd inside (Set.notMem_empty _)
    | rule declared _ ih =>
        exact ⟨.rule declared fun p member => Classical.choice (ih p member)⟩
  · rintro ⟨d⟩
    induction d with
    | rule declared _ ih => exact Generated.rule declared ih

/-- **A conclusion determines its premises.** -/
def SyntaxDirected (rules : Set (List Expr × Expr)) : Prop :=
  ∀ ps ps' r, (ps, r) ∈ rules → (ps', r) ∈ rules → ps = ps'

/-- **One derivation per row** for rules in which a conclusion determines its premises. -/
theorem derivation_unique {rules : Set (List Expr × Expr)} (directed : SyntaxDirected rules)
    {r : Expr} (d : Derivation rules r) : ∀ d' : Derivation rules r, d = d' := by
  induction d with
  | @rule ps r declared subs ih =>
      intro d'
      cases d' with
      | @rule ps' _ declared' subs' =>
          obtain rfl := directed ps ps' r declared declared'
          have same : subs = subs' := funext fun p => funext fun member => ih p member (subs' p member)
          subst same
          rfl

/-- The vector rules are syntax-directed. -/
theorem vecFamily_syntaxDirected : SyntaxDirected vecFamilyRules := by
  intro ps ps' r first second
  rcases first with first | first <;> rcases second with second | second
  · exact Numbers.natRules_syntaxDirected first second
  · rcases Numbers.mem_natRules.mp first with ⟨_, rfl⟩ | ⟨x, _, rfl⟩ <;>
      rcases mem_vecRules.mp second with ⟨_, same⟩ | ⟨y, n, l, _, same⟩ <;>
      exact absurd same (natRow_ne_vecRow _ _ _)
  · rcases Numbers.mem_natRules.mp second with ⟨_, rfl⟩ | ⟨x, _, rfl⟩ <;>
      rcases mem_vecRules.mp first with ⟨_, same⟩ | ⟨y, n, l, _, same⟩ <;>
      exact absurd same (natRow_ne_vecRow _ _ _)
  · rcases mem_vecRules.mp first with ⟨rfl, rfl⟩ | ⟨x, n, l, rfl, rfl⟩ <;>
      rcases mem_vecRules.mp second with ⟨rfl, same⟩ | ⟨y, m, k, rfl, same⟩
    · rfl
    · simp [vecRow, consE, nilE] at same
    · simp [vecRow, consE, nilE] at same
    · obtain ⟨first, second⟩ := vecRow_injective same
      obtain ⟨rfl, rfl⟩ := Lists.consE_injective second
      rw [succE_injective first]

/-- **Every generated vector row has exactly one derivation.** -/
theorem vecRow_one_derivation (ks : List ℕ) :
    Nonempty (Derivation vecFamilyRules (vecRow (numeral ks.length) (listE ks))) ∧
      ∀ d d' : Derivation vecFamilyRules (vecRow (numeral ks.length) (listE ks)), d = d' :=
  ⟨(generated_iff_nonempty _ _).mp (vecRow_generated (Or.inr ⟨ks, rfl⟩)),
    fun d => derivation_unique vecFamily_syntaxDirected d⟩

/-- Two rules making one row. -/
def twoWays : Set (List Expr × Expr) := {([], zeroE), ([nilE], zeroE), ([], nilE)}

/-- **Control: with two rules making one row, the row has two different derivations.** -/
theorem twoWays_two_derivations :
    ∃ d d' : Derivation twoWays zeroE, d ≠ d' := by
  have direct : (([] : List Expr), zeroE) ∈ twoWays := Or.inl rfl
  have through : ([nilE], zeroE) ∈ twoWays := Or.inr (Or.inl rfl)
  have base : (([] : List Expr), nilE) ∈ twoWays := Or.inr (Or.inr rfl)
  let leaf : Derivation twoWays nilE := .rule base fun _ member => absurd member List.not_mem_nil
  refine ⟨.rule direct fun _ member => absurd member List.not_mem_nil,
    .rule through fun p member => (List.mem_singleton.mp member) ▸ leaf, fun same => ?_⟩
  have := congrArg Derivation.premises same
  simp [Derivation.premises] at this

end Families

#print axioms Families.vecFamily_generated_iff
#print axioms Families.vecRow_generated_iff_extrinsic
#print axioms Families.vec_fibre
#print axioms Families.no_junk_index
#print axioms Families.wrong_index_not_generated
#print axioms Families.generated_iff_nonempty
#print axioms Families.derivation_unique
#print axioms Families.vecFamily_syntaxDirected
#print axioms Families.vecRow_one_derivation
#print axioms Families.twoWays_two_derivations

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.InductiveTypes
