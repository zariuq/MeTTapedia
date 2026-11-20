import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Untagged

/-!
# Deciding which rows are codes

Whether a row is the code of a rule of the fragment is decided by a finite computation over the row:
read the row back as a rule (`decode`), check that the rule is in the fragment, and code it again
(`isCode`). The procedure is a structural recursion over the row and the rule it reads.

* **Reading a code back** (`decode`): the nine parts of the row, each list's entries read back from
  quotation; the tells are the pairs of the fourth and fifth parts, the checks are the kinds of the
  eighth part on the terms of the sixth and seventh. Reading the code of a rule of the fragment gives
  the rule back (`decode_ruleCode`).
* **The decision** (`isCode_iff`): `isCode t` holds exactly when `t` is the code of a rule of the
  fragment. The rule is then unique (`eq_decode_of_code`, from `ruleCode_injective`).
* **Tagging is decided row by row** (`tagged_iff`, `taggedCheck_iff`): for a fragment closed under what
  its rules make and decided by a test, a store is tagged exactly when each present row is a data row
  or reads back as a rule of the fragment whose code it is.

**Examples.** The codes of the two example rules are codes, and the example store is tagged
(`second_isCode`, `start_taggedCheck`). Refused: a data row; the row the interpreter reads at the
untagged store (its take entry is an unknown, not a quotation: `openedCode_not_code`), so that store is
not tagged (`loose_not_tagged`); a code-shaped row whose none check carries a second term; one whose
tells have one side missing; one with a tenth part; and the code of a rule that drops
(`dropRule_not_code`): quotation keeps the `drop`, and the rule read back is outside the fragment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Decoding

open Expr
open Examples (fragmentCheck fragment_of_check DataFragment)

/-! ## Reading a code back -/

/-- The entries of a cell list; reading stops at the first row that is not a cell. -/
def entries : Expr → List Expr
  | cell a rest => a :: entries rest
  | _ => []

theorem entries_lst : ∀ l : List Expr, entries (lst l) = l
  | [] => rfl
  | a :: l => by
      show a :: entries (lst l) = a :: l
      rw [entries_lst l]

/-- What a row holds under its tag. -/
def untag : Expr → Expr
  | cell _ body => body
  | t => t

/-- Part `k` of a row read as a code: the entries of its `k`-th list, read back from quotation. -/
def partOf (t : Expr) (k : ℕ) : List Expr :=
  (entries ((entries (untag t)).getD k nil)).map unquote

/-- A check kind read back from its constant. Anything else reads as an equation; the comparison in
`isCode` then refuses the row. -/
def kindOfTerm : Expr → Kind
  | sym 21 => .predicate .none
  | sym 23 => .predicate .any
  | cell (sym 22) (sym n) => .count n
  | _ => .equal

theorem kindOfTerm_term (k : Kind) : kindOfTerm k.term = k := by
  rcases k with _ | ⟨_ | _⟩ | _ <;> rfl

theorem kindOf_check (k : Kind) (a b : Expr) : kindOf (k.check a b) = k := by
  rcases k with _ | ⟨_ | _⟩ | _ <;> rfl

/-- Checks from their kinds and their two terms, in order. -/
def checksOf : List Kind → List Expr → List Expr → List (Check Expr)
  | k :: ks, a :: as, b :: bs => k.check a b :: checksOf ks as bs
  | _, _, _ => []

theorem checksOf_parts : ∀ cs : List (Check Expr),
    checksOf (cs.map kindOf) (cs.map Check.pattern) (cs.map guardRight) = cs
  | [] => rfl
  | c :: cs => by
      simp only [List.map_cons, checksOf, check_rebuild, checksOf_parts cs]

/-- **The rule a row reads as**: takes, reads, tells, checks, made rows and collect patterns, from the
nine parts. -/
def decode (t : Expr) : Rule Tm :=
  ⟨PUnit.unit, ⟨partOf t 0, partOf t 1, (partOf t 3).zip (partOf t 4),
    checksOf ((partOf t 7).map kindOfTerm) (partOf t 5) (partOf t 6), partOf t 2⟩, partOf t 8⟩

theorem partOf_ruleCode {r : Rule Tm} (frag : Fragment r) {k : ℕ} (hk : k < 9) :
    partOf (ruleCode r) k = partsAt r k := by
  have body : untag (ruleCode r) = lst ((List.range 9).map fun k => lst ((partsAt r k).map quote)) := rfl
  unfold partOf
  rw [body, entries_lst, getD_of_lt _ _ (by simpa using hk)]
  simp only [List.getElem_map, List.getElem_range]
  rw [entries_lst, List.map_map]
  calc (partsAt r k).map (unquote ∘ quote) = (partsAt r k).map id :=
        List.map_congr_left fun p inside => unquote_quote (partsAt_dropFree frag inside)
    _ = partsAt r k := List.map_id _

/-- **Reading the code of a rule of the fragment gives the rule back.** -/
theorem decode_ruleCode {r : Rule Tm} (frag : Fragment r) : decode (ruleCode r) = r := by
  have part := fun (k : ℕ) (hk : k < 9) => partOf_ruleCode frag hk
  unfold decode
  rw [part 0 (by decide), part 1 (by decide), part 2 (by decide), part 3 (by decide),
    part 4 (by decide), part 5 (by decide), part 6 (by decide), part 7 (by decide),
    part 8 (by decide)]
  have tells : (r.body.tell.map Prod.fst).zip (r.body.tell.map Prod.snd) = r.body.tell := by
    rw [← List.unzip_fst, ← List.unzip_snd, List.zip_unzip]
  have kinds : (r.body.checks.map fun c => (kindOf c).term).map kindOfTerm = r.body.checks.map kindOf := by
    rw [List.map_map]
    exact List.map_congr_left fun c _ => kindOfTerm_term (kindOf c)
  show (⟨PUnit.unit, ⟨r.body.take, r.body.read, (r.body.tell.map Prod.fst).zip (r.body.tell.map Prod.snd),
    checksOf ((r.body.checks.map fun c => (kindOf c).term).map kindOfTerm) (r.body.checks.map Check.pattern)
      (r.body.checks.map guardRight), r.body.produce⟩, r.collect⟩ : Rule Tm) = r
  rw [tells, kinds, checksOf_parts]

/-! ## The decision -/

theorem check_of_fragment {r : Rule Tm} (frag : Fragment r) : fragmentCheck r = true := by
  simp only [fragmentCheck, Bool.and_eq_true, List.all_eq_true]
  exact ⟨⟨⟨⟨⟨frag.take, frag.read⟩, fun e inside => by simpa using frag.tell e inside⟩, frag.check⟩,
    frag.produce⟩, frag.collect⟩

/-- **Whether a row is the code of a rule of the fragment**: read it back as a rule, check that the
rule is in the fragment, and compare its code with the row. -/
def isCode (t : Expr) : Bool := fragmentCheck (decode t) && decide (ruleCode (decode t) = t)

/-- **The procedure decides the codes of the fragment's rules.** -/
theorem isCode_iff (t : Expr) : isCode t = true ↔ ∃ r, Fragment r ∧ ruleCode r = t := by
  constructor
  · intro checked
    simp only [isCode, Bool.and_eq_true, decide_eq_true_eq] at checked
    exact ⟨decode t, fragment_of_check checked.1, checked.2⟩
  · rintro ⟨r, frag, rfl⟩
    simp only [isCode, Bool.and_eq_true, decide_eq_true_eq, decode_ruleCode frag]
    exact ⟨check_of_fragment frag, trivial⟩

/-- **The rule of a code is the rule it reads as**: the only rule with that code. -/
theorem eq_decode_of_code {r : Rule Tm} (frag : Fragment r) {t : Expr} (same : ruleCode r = t) :
    decode t = r := by
  rw [← same, decode_ruleCode frag]

/-! ## Tagging, decided -/

/-- Whether a row is a data row. -/
def isObj : Expr → Bool
  | cell (sym 1) _ => true
  | _ => false

theorem isObj_iff (t : Expr) : isObj t = true ↔ ∃ u, t = obj u := by
  constructor
  · intro checked
    unfold isObj at checked
    split at checked
    · exact ⟨_, rfl⟩
    · exact absurd checked Bool.false_ne_true
  · rintro ⟨u, rfl⟩
    rfl

/-- **Tagging is decided row by row**: for a fragment closed under what its rules make, decided by a
test `inF`, a store is tagged exactly when each present row is a data row, or reads back as a rule that
passes the test and whose code it is. -/
theorem tagged_iff {F : Set (Rule Tm)} (closed : ClosedFragment F) (inF : Rule Tm → Bool)
    (decides : ∀ r, inF r = true ↔ r ∈ F) (s : State Tm ℕ) :
    Tagged F s ↔ ∀ o ∈ s.present,
      isObj (s.label o) = true ∨ (isCode (s.label o) = true ∧ inF (decode (s.label o)) = true) := by
  constructor
  · intro tagged o present
    rcases tagged o present with ⟨t, data⟩ | ⟨r, hr, coded⟩
    · exact Or.inl ((isObj_iff _).mpr ⟨t, data⟩)
    · refine Or.inr ⟨(isCode_iff _).mpr ⟨r, closed.fragment r hr, coded.symm⟩, ?_⟩
      rw [eq_decode_of_code (closed.fragment r hr) coded.symm]
      exact (decides r).mpr hr
  · intro checked o present
    rcases checked o present with data | ⟨coded, passes⟩
    · exact Or.inl ((isObj_iff _).mp data)
    · obtain ⟨r, frag, same⟩ := (isCode_iff _).mp coded
      rw [eq_decode_of_code frag same] at passes
      exact Or.inr ⟨r, (decides r).mp passes, same.symm⟩

/-- **The check of a store**, a finite computation over its present rows. -/
def taggedCheck (inF : Rule Tm → Bool) (s : State Tm ℕ) : Bool :=
  decide (∀ o ∈ s.present,
    isObj (s.label o) = true ∨ (isCode (s.label o) = true ∧ inF (decode (s.label o)) = true))

theorem taggedCheck_iff {F : Set (Rule Tm)} (closed : ClosedFragment F) (inF : Rule Tm → Bool)
    (decides : ∀ r, inF r = true ↔ r ∈ F) (s : State Tm ℕ) :
    taggedCheck inF s = true ↔ Tagged F s := by
  rw [tagged_iff closed inF decides s, taggedCheck, decide_eq_true_eq]

/-! ## Examples -/

/-- The test of the data fragment: the fragment, and every made row a data row. -/
def dataCheck (r : Rule Tm) : Bool := fragmentCheck r && r.body.produce.all isObj

theorem dataCheck_iff (r : Rule Tm) : dataCheck r = true ↔ r ∈ DataFragment := by
  simp only [dataCheck, Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨checked, made⟩
    exact ⟨fragment_of_check checked, fun m inside => (isObj_iff m).mp (made m inside)⟩
  · rintro ⟨frag, made⟩
    exact ⟨check_of_fragment frag, fun m inside => (isObj_iff m).mpr (made m inside)⟩

theorem second_isCode : isCode (ruleCode Examples.second) = true := by decide

theorem first_isCode : isCode (ruleCode Examples.first) = true :=
  (isCode_iff _).mpr ⟨Examples.first, Examples.first_mem.1, rfl⟩

/-- The example store holding two codes and two data rows is tagged, by the computation. -/
theorem start_taggedCheck : taggedCheck dataCheck Examples.start = true := by decide

theorem start_tagged : Tagged DataFragment Examples.start :=
  (taggedCheck_iff Examples.dataFragment_closed dataCheck dataCheck_iff _).mp start_taggedCheck

theorem obj_not_code : isCode (obj Examples.five) = false := by decide

/-- **The row the interpreter reads at the untagged store is not a code**: its take entry is an
unknown, where a code has a quotation. -/
theorem openedCode_not_code : isCode Untagged.openedCode = false := by decide

/-- **The untagged store is not tagged**, by the computation: its row `0` is an unknown. -/
theorem loose_not_tagged : ¬ Tagged DataFragment Untagged.loose := by
  rw [← taggedCheck_iff Examples.dataFragment_closed dataCheck dataCheck_iff]
  decide

/-- A code-shaped row whose none check carries a second term. -/
def noneWithRight : Expr :=
  code (lst [nil, nil, nil, nil, nil, lst [Examples.five], lst [Examples.five], lst [(Kind.predicate .none).term], nil])

theorem noneWithRight_not_code : isCode noneWithRight = false := by decide

/-- A code-shaped row with a tell whose right side is missing. -/
def tellHalf : Expr := code (lst [nil, nil, nil, lst [Examples.five], nil, nil, nil, nil, nil])

theorem tellHalf_not_code : isCode tellHalf = false := by decide

/-- A code-shaped row with a tenth part. -/
def tenParts : Expr := code (lst [nil, nil, nil, nil, nil, nil, nil, nil, nil, nil])

theorem tenParts_not_code : isCode tenParts = false := by decide

/-- A rule that drops (outside the fragment). -/
def dropRule : Rule Tm := ⟨PUnit.unit, ⟨[drop (var 0) (var 1)], [], [], [], []⟩, []⟩

/-- **The code of a rule outside the fragment is not a code of the fragment.** -/
theorem dropRule_not_code : isCode (ruleCode dropRule) = false := by decide

/-- The nine empty parts are the code of the rule with no patterns at all. -/
theorem empty_isCode : isCode (code (lst [nil, nil, nil, nil, nil, nil, nil, nil, nil])) = true := by decide

#print axioms decode_ruleCode
#print axioms isCode_iff
#print axioms eq_decode_of_code
#print axioms tagged_iff
#print axioms taggedCheck_iff
#print axioms start_tagged
#print axioms loose_not_tagged
#print axioms openedCode_not_code
#print axioms dropRule_not_code

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RulesAsRows.Decoding
