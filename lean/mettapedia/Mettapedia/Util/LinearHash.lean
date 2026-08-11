import Mathlib.Data.List.Nodup
import Std.Data.HashSet.Lemmas

/-!
# Linear hash-indexed list predicates

This module supplies executable hash-indexed realizations of list properties
whose simple logical specifications use linear membership scans.  Theorems in
this file connect the realizations to ordinary `List` predicates; callers can
therefore retain small structural specifications without paying their
quadratic cost in compiled code.
-/

namespace Mettapedia.Util.LinearHash

private def eraseDupsFastAux {alpha : Type} [BEq alpha] [Hashable alpha]
    (seen : Std.HashSet alpha) : List alpha -> List alpha -> List alpha
  | [], reversed => reversed.reverse
  | value :: values, reversed =>
      if seen.contains value then
        eraseDupsFastAux seen values reversed
      else
        eraseDupsFastAux (seen.insert value) values (value :: reversed)

/-- Hash-indexed stable duplicate removal.  It retains the first occurrence
of each value, exactly like `List.eraseDups`. -/
def eraseDupsFast {alpha : Type} [BEq alpha] [Hashable alpha]
    (values : List alpha) : List alpha :=
  eraseDupsFastAux {} values []

private theorem eraseDupsFastAux_eq
    {alpha : Type} [BEq alpha] [Hashable alpha]
    [LawfulBEq alpha] [LawfulHashable alpha]
    (seenSet : Std.HashSet alpha) (remaining reversed : List alpha)
    (sameMembers : forall value, value ∈ seenSet <-> value ∈ reversed) :
    eraseDupsFastAux seenSet remaining reversed =
      List.eraseDupsBy.loop (fun left right => left == right)
        remaining reversed := by
  induction remaining generalizing seenSet reversed with
  | nil => rfl
  | cons value remaining inductionHypothesis =>
      have containsEqual :
          seenSet.contains value = reversed.contains value := by
        apply Bool.eq_iff_iff.mpr
        rw [Std.HashSet.contains_iff_mem, List.contains_iff_mem]
        exact sameMembers value
      have nextMembers : forall candidate,
          candidate ∈ seenSet.insert value <-> candidate ∈ value :: reversed := by
        intro candidate
        constructor
        · intro inserted
          rcases Std.HashSet.mem_insert.mp inserted with equal | oldMember
          · exact List.mem_cons.mpr
              (Or.inl (LawfulBEq.eq_of_beq equal).symm)
          · exact List.mem_cons.mpr
              (Or.inr ((sameMembers candidate).mp oldMember))
        · intro member
          rcases List.mem_cons.mp member with equal | oldMember
          · subst candidate
            exact Std.HashSet.mem_insert_self
          · exact Std.HashSet.mem_insert.mpr
              (Or.inr ((sameMembers candidate).mpr oldMember))
      unfold eraseDupsFastAux List.eraseDupsBy.loop
      rw [List.any_beq, ← containsEqual]
      cases observed : seenSet.contains value with
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact inductionHypothesis (seenSet := seenSet.insert value)
            (reversed := value :: reversed) nextMembers
      | true =>
          simp only [↓reduceIte]
          exact inductionHypothesis (seenSet := seenSet)
            (reversed := reversed) sameMembers

/-- The hash-indexed implementation is exactly the standard stable
duplicate-removal specification. -/
theorem eraseDupsFast_eq
    {alpha : Type} [BEq alpha] [Hashable alpha]
    [LawfulBEq alpha] [LawfulHashable alpha]
    (values : List alpha) :
    eraseDupsFast values = values.eraseDups := by
  simpa [eraseDupsFast, List.eraseDups, List.eraseDupsBy] using
    eraseDupsFastAux_eq (alpha := alpha) ({} : Std.HashSet alpha) values []
      (by simp)

private theorem eraseDups_sublist
    {alpha : Type} [BEq alpha] [LawfulBEq alpha] :
    forall values : List alpha, values.eraseDups.Sublist values
  | [] => by simp
  | value :: values => by
      rw [List.eraseDups_cons]
      exact List.Sublist.cons_cons value
        ((eraseDups_sublist
            (values.filter fun other => !other == value)).trans
          List.filter_sublist)
  termination_by values => values.length
  decreasing_by
    have shorter :=
      List.length_filter_le (fun other => !other == value) values
    simp only [List.length_cons]
    omega

private theorem nodup_eraseDups
    {alpha : Type} [BEq alpha] [LawfulBEq alpha] :
    forall values : List alpha, values.eraseDups.Nodup
  | [] => by simp
  | value :: values => by
      rw [List.eraseDups_cons]
      refine List.nodup_cons.mpr
        ⟨?_, nodup_eraseDups
          (values.filter fun other => !other == value)⟩
      intro member
      rw [List.mem_eraseDups, List.mem_filter] at member
      simp at member
  termination_by values => values.length
  decreasing_by
    have shorter :=
      List.length_filter_le (fun other => !other == value) values
    simp only [List.length_cons]
    omega

private theorem eraseDups_of_nodup
    {alpha : Type} [BEq alpha] [LawfulBEq alpha] :
    forall {values : List alpha}, values.Nodup -> values.eraseDups = values
  | [], _ => by simp
  | value :: values, nodup => by
      rw [List.eraseDups_cons]
      obtain ⟨absent, tailNodup⟩ := List.nodup_cons.mp nodup
      have filterAll :
          (values.filter fun other => !other == value) = values := by
        rw [List.filter_eq_self]
        intro other member
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true,
          beq_eq_false_iff_ne, ne_eq]
        intro equal
        exact absent (equal ▸ member)
      rw [filterAll, eraseDups_of_nodup tailNodup]
  termination_by values => values.length
  decreasing_by
    simp only [List.length_cons]
    omega

/-- The conventional executable length test for duplicate freedom is exactly
`List.Nodup`. -/
theorem eraseDupsLength_eq_true_iff_nodup
    {alpha : Type} [BEq alpha] [LawfulBEq alpha]
    (values : List alpha) :
    (values.eraseDups.length == values.length) = true <-> values.Nodup := by
  constructor
  · intro lengths
    have equal : values.eraseDups = values :=
      (eraseDups_sublist values).eq_of_length (by simpa using lengths)
    exact equal ▸ nodup_eraseDups values
  · intro nodup
    simp [eraseDups_of_nodup nodup]

/-- Scan the remaining values while retaining the values already observed.
With a lawful hash function this performs one expected-constant-time lookup
and insertion per list element. -/
def allDistinctFrom {alpha : Type} [BEq alpha] [Hashable alpha]
    (seen : Std.HashSet alpha) : List alpha -> Bool
  | [] => true
  | value :: values =>
      if seen.contains value then
        false
      else
        allDistinctFrom (seen.insert value) values

/-- Hash-indexed duplicate-freedom test. -/
def allDistinct {alpha : Type} [BEq alpha] [Hashable alpha]
    (values : List alpha) : Bool :=
  allDistinctFrom {} values

/-- Every value in `left` is absent from `right`, using one hash index for
the right-hand collection. -/
def allAbsent {alpha : Type} [BEq alpha] [Hashable alpha]
    (left right : List alpha) : Bool :=
  let rightSet : Std.HashSet alpha := .ofList right
  left.all fun value => !rightSet.contains value

/-- Hash-indexed disjointness has exactly the conventional list-membership
result. -/
theorem allAbsent_eq
    {alpha : Type} [BEq alpha] [Hashable alpha]
    [LawfulBEq alpha] [LawfulHashable alpha]
    (left right : List alpha) :
    allAbsent left right =
      left.all (fun value => !(right.contains value)) := by
  simp only [allAbsent, Std.HashSet.contains_ofList]

theorem allDistinctFrom_eq_true_iff
    {alpha : Type} [BEq alpha] [Hashable alpha]
    [LawfulBEq alpha] [LawfulHashable alpha]
    (seen : Std.HashSet alpha) (values : List alpha) :
    allDistinctFrom seen values = true <->
      values.Nodup /\ forall value, value ∈ values -> value ∉ seen := by
  induction values generalizing seen with
  | nil => simp [allDistinctFrom]
  | cons value values inductionHypothesis =>
      by_cases observed : seen.contains value = true
      · have member : value ∈ seen :=
          Std.HashSet.mem_iff_contains.mpr observed
        simp [allDistinctFrom, observed, member]
      · have absent : value ∉ seen := by
          intro member
          exact observed (Std.HashSet.mem_iff_contains.mp member)
        have unobserved : seen.contains value = false := by
          cases equality : seen.contains value with
          | false => rfl
          | true => exact (observed equality).elim
        rw [allDistinctFrom]
        simp only [unobserved, Bool.false_eq_true, ↓reduceIte]
        rw [inductionHypothesis (seen := seen.insert value)]
        constructor
        · rintro ⟨tailNodup, tailFresh⟩
          have valueAbsent : value ∉ values := by
            intro valueMember
            exact (tailFresh value valueMember)
              Std.HashSet.mem_insert_self
          refine ⟨List.nodup_cons.mpr ⟨valueAbsent, tailNodup⟩, ?_⟩
          intro candidate candidateMember
          rcases List.mem_cons.mp candidateMember with rfl | tailMember
          · exact absent
          · intro candidateSeen
            exact (tailFresh candidate tailMember)
              (Std.HashSet.mem_insert.mpr (Or.inr candidateSeen))
        · rintro ⟨allNodup, allFresh⟩
          have split := List.nodup_cons.mp allNodup
          refine ⟨split.2, ?_⟩
          intro candidate candidateMember inserted
          rcases Std.HashSet.mem_insert.mp inserted with equal | oldMember
          · exact split.1 ((LawfulBEq.eq_of_beq equal).symm ▸ candidateMember)
          · exact (allFresh candidate (List.mem_cons_of_mem value candidateMember))
              oldMember

theorem allDistinct_eq_true_iff
    {alpha : Type} [BEq alpha] [Hashable alpha]
    [LawfulBEq alpha] [LawfulHashable alpha]
    (values : List alpha) :
    allDistinct values = true <-> values.Nodup := by
  rw [allDistinct, allDistinctFrom_eq_true_iff]
  simp

/-- The hash-indexed test and the conventional `eraseDups` length test have
identical Boolean results. -/
theorem allDistinct_eq_eraseDupsLength
    {alpha : Type} [BEq alpha] [Hashable alpha]
    [LawfulBEq alpha] [LawfulHashable alpha]
    (values : List alpha) :
    allDistinct values =
      (values.eraseDups.length == values.length) := by
  apply Bool.eq_iff_iff.mpr
  rw [allDistinct_eq_true_iff,
    eraseDupsLength_eq_true_iff_nodup]

theorem allDistinct_accepts_distinct_canary :
    allDistinct ["alpha", "beta", "gamma"] = true := by
  rw [allDistinct_eq_eraseDupsLength]
  decide

theorem allDistinct_rejects_duplicate_canary :
    allDistinct ["alpha", "beta", "alpha"] = false := by
  rw [allDistinct_eq_eraseDupsLength]
  decide

theorem eraseDupsFast_preserves_first_occurrence_canary :
    eraseDupsFast ["beta", "alpha", "beta", "gamma", "alpha"] =
      ["beta", "alpha", "gamma"] := by
  rw [eraseDupsFast_eq]
  decide

end Mettapedia.Util.LinearHash
