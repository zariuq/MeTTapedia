import Mettapedia.GSLT.Parsing.PlainBnfLexicalScalarSemantics
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Interval
import Mathlib.Data.List.Range

/-!
# Inhabitation of plain-BNF lexical classes

A declaration names a class; that fact alone does not establish that the
class accepts any scalar. In particular, an empty exclusion list denotes
the whole Unicode scalar carrier, whereas exclusion of that entire carrier
denotes the empty class.

The independent meaning below is existence of an accepted scalar. For a
valid, duplicate-free scalar inventory, a linear list-length test decides
this meaning exactly. The finite interval representation is used only in
the cardinality proof: the executable checker never enumerates Unicode.
Neither declaration admission nor graph productivity is redefined here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.PlainBnfLexicalInhabitation

open ParserProfileSemantics PlainBnfLexicalScalarSemantics

/-- Semantic inhabitation uses the existing lexical acceptance relation. -/
def InhabitedClass (kind : LexicalClassKind) : Prop :=
  ∃ scalar, kind.accepts scalar = true

/-- A proof-only finite description of the existing Unicode scalar carrier. -/
def scalarCarrier : Finset Nat :=
  Finset.range 55296 ∪ Finset.Ico 57344 1114112

theorem mem_scalarCarrier (scalar : Nat) :
    scalar ∈ scalarCarrier ↔ isUnicodeScalar scalar = true := by
  simp only [scalarCarrier, Finset.mem_union, Finset.mem_range, Finset.mem_Ico,
    isUnicodeScalar, decide_eq_true_eq]
  omega

theorem scalarCarrier_card : scalarCarrier.card = 1112064 := by
  have disjoint : Disjoint (Finset.range 55296) (Finset.Ico 57344 1114112) := by
    rw [Finset.disjoint_left]
    intro n low high
    simp only [Finset.mem_range, Finset.mem_Ico] at low high
    omega
  rw [scalarCarrier, Finset.card_union_of_disjoint disjoint]
  simp

/-- These hypotheses are weaker than strictly increasing scalar admission;
an empty list is permitted and has different meanings for points/except. -/
def InventoryValid (scalars : List Nat) : Prop :=
  scalars.Nodup ∧ ∀ scalar ∈ scalars, isUnicodeScalar scalar = true

def ClassInventoryValid : LexicalClassKind → Prop
  | .points scalars | .except scalars => InventoryValid scalars

theorem scalarListWellFormed_of_sorted (scalars : List Nat)
    (nonempty : scalars ≠ []) (sorted : scalars.Pairwise (· < ·))
    (valid : ∀ scalar ∈ scalars, isUnicodeScalar scalar = true) :
    ScalarListWellFormed (scalars.map Int.ofNat) := by
  induction scalars with
  | nil => exact False.elim (nonempty rfl)
  | cons first tail ih =>
    cases tail with
    | nil =>
      simpa [ScalarListWellFormed, isUnicodeScalarInt_nat] using valid first (by simp)
    | cons next rest =>
      rw [List.pairwise_cons] at sorted
      change isUnicodeScalarInt (Int.ofNat first) = true ∧
        Int.ofNat first < Int.ofNat next ∧
        ScalarListWellFormed ((next :: rest).map Int.ofNat)
      refine ⟨?_, ?_, ih (by simp) sorted.2 (fun scalar member => valid scalar (by simp [member]))⟩
      · simpa only [Int.ofNat_eq_natCast, isUnicodeScalarInt_nat] using valid first (by simp)
      · simpa only [Int.ofNat_eq_natCast, Int.ofNat_lt] using sorted.1 next (by simp)

theorem sorted_and_valid_of_scalarListWellFormed (scalars : List Nat)
    (wellFormed : ScalarListWellFormed (scalars.map Int.ofNat)) :
    scalars.Pairwise (· < ·) ∧
      ∀ scalar ∈ scalars, isUnicodeScalar scalar = true := by
  induction scalars with
  | nil => exact False.elim wellFormed
  | cons first tail ih =>
    cases tail with
    | nil =>
      have valid : isUnicodeScalar first = true := by
        simpa [ScalarListWellFormed, isUnicodeScalarInt_nat] using wellFormed
      simp [valid]
    | cons next rest =>
      change isUnicodeScalarInt (Int.ofNat first) = true ∧
        Int.ofNat first < Int.ofNat next ∧
        ScalarListWellFormed ((next :: rest).map Int.ofNat) at wellFormed
      have tailFacts := ih wellFormed.2.2
      have firstValid : isUnicodeScalar first = true := by
        simpa only [Int.ofNat_eq_natCast, isUnicodeScalarInt_nat] using wellFormed.1
      have firstLess : first < next := by
        simpa only [Int.ofNat_eq_natCast, Int.ofNat_lt] using wellFormed.2.1
      constructor
      · rw [List.pairwise_cons]
        refine ⟨?_, tailFacts.1⟩
        intro scalar member
        rcases List.mem_cons.mp member with rfl | later
        · exact firstLess
        · exact Nat.lt_trans firstLess ((List.pairwise_cons.mp tailFacts.1).1 scalar later)
      · intro scalar member
        rcases List.mem_cons.mp member with rfl | later
        · exact firstValid
        · exact tailFacts.2 scalar later

/-- Existing strictly increasing scalar admission supplies every hypothesis
needed by the linear inhabitation check. Empty exclusions may instead supply
the trivial valid empty inventory directly. -/
theorem inventoryValid_of_scalarListWellFormed (scalars : List Nat)
    (wellFormed : ScalarListWellFormed (scalars.map Int.ofNat)) :
    InventoryValid scalars := by
  obtain ⟨sorted, valid⟩ := sorted_and_valid_of_scalarListWellFormed scalars wellFormed
  exact ⟨sorted.imp Nat.ne_of_lt, valid⟩

theorem empty_inventory_valid : InventoryValid [] := by simp [InventoryValid]

theorem points_inhabited_iff {scalars : List Nat}
    (valid : ∀ scalar ∈ scalars, isUnicodeScalar scalar = true) :
    InhabitedClass (.points scalars) ↔ scalars ≠ [] := by
  constructor
  · rintro ⟨scalar, accepted⟩ empty
    simp [LexicalClassKind.accepts, empty] at accepted
  · intro nonempty
    obtain ⟨scalar, member⟩ := List.exists_mem_of_ne_nil scalars nonempty
    exact ⟨scalar, by simp [LexicalClassKind.accepts, valid scalar member, member]⟩

theorem except_inhabited_iff {excluded : List Nat}
    (valid : InventoryValid excluded) :
    InhabitedClass (.except excluded) ↔ excluded.length < 1112064 := by
  have included : excluded.toFinset ⊆ scalarCarrier := by
    intro scalar member
    exact (mem_scalarCarrier scalar).mpr (valid.2 scalar (List.mem_toFinset.mp member))
  have count : excluded.toFinset.card = excluded.length := List.toFinset_card_of_nodup valid.1
  constructor
  · rintro ⟨scalar, accepted⟩
    have accepted' : isUnicodeScalar scalar = true ∧ scalar ∉ excluded := by
      simpa [LexicalClassKind.accepts] using accepted
    have proper : excluded.toFinset ⊂ scalarCarrier := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨included, ?_⟩
      intro equal
      have member : scalar ∈ excluded.toFinset := by
        rw [equal]
        exact (mem_scalarCarrier scalar).mpr accepted'.1
      exact accepted'.2 (List.mem_toFinset.mp member)
    simpa [count, scalarCarrier_card] using Finset.card_lt_card proper
  · intro shorter
    have countLt : excluded.toFinset.card < scalarCarrier.card := by
      simpa [count, scalarCarrier_card] using shorter
    obtain ⟨scalar, member, absent⟩ := Finset.exists_mem_notMem_of_card_lt_card countLt
    exact ⟨scalar, by
      have accepted := (mem_scalarCarrier scalar).mp member
      have notExcluded : scalar ∉ excluded := by simpa using absent
      simp [LexicalClassKind.accepts, accepted, notExcluded]⟩

/-- A linear structural decision on already qualified inventories. The
validity premise is proved separately, never inferred from this result. -/
def checkInhabited : LexicalClassKind → Bool
  | .points scalars => !scalars.isEmpty
  | .except excluded => decide (excluded.length < 1112064)

theorem checkInhabited_iff (kind : LexicalClassKind)
    (valid : ClassInventoryValid kind) :
    checkInhabited kind = true ↔ InhabitedClass kind := by
  cases kind with
  | points scalars =>
    rw [points_inhabited_iff valid.2]
    simp [checkInhabited]
  | except excluded =>
    rw [except_inhabited_iff valid]
    simp [checkInhabited]

/-- Search for a missing valid scalar strictly after an excluded scalar.
This is the ordered scan used by the authored graph analysis: it tests gaps
without constructing output integers and skips exactly the surrogate hole. -/
def gapAfter (previous : Nat) : List Nat → Bool
  | [] => decide (previous < 1114111)
  | next :: rest =>
    if previous = 55295 ∧ next = 57344 then gapAfter next rest
    else if previous + 1 < next then true else gapAfter next rest

def exceptGapCheck : List Nat → Bool
  | [] => true
  | first :: rest => if first = 0 then gapAfter first rest else true

def checkInhabitedByGaps : LexicalClassKind → Bool
  | .points scalars => !scalars.isEmpty
  | .except excluded => exceptGapCheck excluded

private def MissingAbove (previous : Nat) (excluded : List Nat) : Prop :=
  ∃ scalar, isUnicodeScalar scalar = true ∧ previous < scalar ∧ scalar ∉ excluded

private theorem missingAbove_no_gap (previous next : Nat) (rest : List Nat)
    (ordered : previous < next)
    (noGap : ∀ scalar, isUnicodeScalar scalar = true →
      previous < scalar → scalar < next → False) :
    MissingAbove previous (next :: rest) ↔ MissingAbove next rest := by
  constructor
  · rintro ⟨scalar, valid, above, absent⟩
    have different : scalar ≠ next := by intro equal; exact absent (by simp [equal])
    have afterNext : next < scalar := by
      by_contra notAfter
      exact noGap scalar valid above (by omega)
    exact ⟨scalar, valid, afterNext, fun member => absent (by simp [member])⟩
  · rintro ⟨scalar, valid, above, absent⟩
    exact ⟨scalar, valid, by omega, by
      intro member
      rcases List.mem_cons.mp member with equal | member
      · omega
      · exact absent member⟩

private theorem missingAbove_of_gap (previous next : Nat) (rest : List Nat)
    (previousValid : isUnicodeScalar previous = true)
    (nextValid : isUnicodeScalar next = true)
    (sorted : (next :: rest).Pairwise (· < ·))
    (gap : previous + 1 < next)
    (notHole : ¬ (previous = 55295 ∧ next = 57344)) :
    MissingAbove previous (next :: rest) := by
  have previousBounds := of_decide_eq_true previousValid
  have nextBounds := of_decide_eq_true nextValid
  have absent (scalar : Nat) (below : scalar < next) : scalar ∉ next :: rest := by
    intro member
    rcases List.mem_cons.mp member with equal | later
    · omega
    · have laterBound := (List.pairwise_cons.mp sorted).1 scalar later
      omega
  by_cases edge : previous = 55295
  · refine ⟨57344, by decide, by omega, absent 57344 (by omega)⟩
  · refine ⟨previous + 1, ?_, by omega, absent _ gap⟩
    simp only [isUnicodeScalar, decide_eq_true_eq]
    omega

theorem gapAfter_iff (previous : Nat) (excluded : List Nat)
    (previousValid : isUnicodeScalar previous = true)
    (valid : ∀ scalar ∈ excluded, isUnicodeScalar scalar = true)
    (sorted : (previous :: excluded).Pairwise (· < ·)) :
    gapAfter previous excluded = true ↔
      ∃ scalar, isUnicodeScalar scalar = true ∧ previous < scalar ∧ scalar ∉ excluded := by
  induction excluded generalizing previous with
  | nil =>
    simp only [gapAfter, decide_eq_true_eq]
    constructor
    · intro beforeEnd
      exact ⟨1114111, by decide, beforeEnd, by simp⟩
    · rintro ⟨scalar, scalarValid, afterPrevious, _⟩
      have bounds := of_decide_eq_true scalarValid
      omega
  | cons next rest ih =>
    have nextValid := valid next (by simp)
    have tailValid : ∀ scalar ∈ rest, isUnicodeScalar scalar = true :=
      fun scalar member => valid scalar (by simp [member])
    have sortedParts := List.pairwise_cons.mp sorted
    have ordered := sortedParts.1 next (by simp)
    have recursive := ih next nextValid tailValid sortedParts.2
    change gapAfter previous (next :: rest) = true ↔ MissingAbove previous (next :: rest)
    by_cases hole : previous = 55295 ∧ next = 57344
    · simp only [gapAfter, if_pos hole]
      rw [recursive]
      exact (missingAbove_no_gap previous next rest ordered (by
        intro scalar scalarValid afterPrevious beforeNext
        have bounds := of_decide_eq_true scalarValid
        omega)).symm
    · by_cases gap : previous + 1 < next
      · simp only [gapAfter, if_neg hole, if_pos gap, true_iff]
        exact missingAbove_of_gap previous next rest previousValid nextValid sortedParts.2 gap hole
      · simp only [gapAfter, if_neg hole, if_neg gap]
        rw [recursive]
        exact (missingAbove_no_gap previous next rest ordered (by
          intro scalar _ afterPrevious beforeNext
          omega)).symm

theorem exceptGapCheck_iff (excluded : List Nat)
    (valid : ∀ scalar ∈ excluded, isUnicodeScalar scalar = true)
    (sorted : excluded.Pairwise (· < ·)) :
    exceptGapCheck excluded = true ↔ InhabitedClass (.except excluded) := by
  cases excluded with
  | nil =>
    constructor
    · intro _; exact ⟨0, by decide⟩
    · intro _; rfl
  | cons first rest =>
    by_cases zero : first = 0
    · simp only [exceptGapCheck, if_pos zero]
      rw [gapAfter_iff first rest (valid first (by simp))
        (fun scalar member => valid scalar (by simp [member])) sorted]
      constructor
      · rintro ⟨scalar, scalarValid, above, absent⟩
        exact ⟨scalar, by simp [LexicalClassKind.accepts, scalarValid,
          show scalar ≠ first by omega, absent]⟩
      · rintro ⟨scalar, accepted⟩
        have facts : isUnicodeScalar scalar = true ∧ scalar ∉ first :: rest := by
          simpa [LexicalClassKind.accepts] using accepted
        have notFirst : scalar ≠ first := by intro eq; exact facts.2 (by simp [eq])
        exact ⟨scalar, facts.1, by omega, fun member => facts.2 (by simp [member])⟩
    · simp only [exceptGapCheck, if_neg zero, true_iff]
      have absent : 0 ∉ first :: rest := by
        intro member
        rcases List.mem_cons.mp member with equal | later
        · omega
        · have positive := (List.pairwise_cons.mp sorted).1 0 later
          omega
      exact ⟨0, by simp [LexicalClassKind.accepts, absent, isUnicodeScalar]⟩

theorem checkInhabitedByGaps_iff (kind : LexicalClassKind)
    (valid : ClassInventoryValid kind)
    (sorted : match kind with
      | .points scalars | .except scalars => scalars.Pairwise (· < ·)) :
    checkInhabitedByGaps kind = true ↔ InhabitedClass kind := by
  cases kind with
  | points scalars =>
    rw [points_inhabited_iff valid.2]
    simp [checkInhabitedByGaps]
  | except excluded => exact exceptGapCheck_iff excluded valid.2 sorted

theorem gap_check_agrees_with_cardinality (kind : LexicalClassKind)
    (valid : ClassInventoryValid kind)
    (sorted : match kind with
      | .points scalars | .except scalars => scalars.Pairwise (· < ·)) :
    checkInhabitedByGaps kind = checkInhabited kind := by
  apply Bool.eq_iff_iff.mpr
  exact (checkInhabitedByGaps_iff kind valid sorted).trans (checkInhabited_iff kind valid).symm

theorem empty_exclusion_accepts_exactly_unicode (scalar : Nat) :
    LexicalClassKind.accepts (.except []) scalar = isUnicodeScalar scalar := by
  simp [LexicalClassKind.accepts]

theorem empty_exclusion_is_inhabited : InhabitedClass (.except []) :=
  ⟨0, by decide⟩

theorem empty_positive_class_is_uninhabited : ¬ InhabitedClass (.points []) := by
  rintro ⟨scalar, accepted⟩
  simp [LexicalClassKind.accepts] at accepted

theorem singleton_exclusion_is_inhabited : InhabitedClass (.except [0]) :=
  ⟨1, by decide⟩

theorem invalid_positive_scalar_is_not_productive : ¬ InhabitedClass (.points [55296]) := by
  rintro ⟨scalar, accepted⟩
  simp only [LexicalClassKind.accepts, Bool.and_eq_true, List.contains_iff_mem,
    List.mem_cons, List.not_mem_nil, or_false] at accepted
  obtain ⟨valid, rfl⟩ := accepted
  contradiction

/-- A symbolic counterexample inventory: every Unicode scalar, in increasing
order. Proofs use range/filter laws rather than reducing a million-element
list or imposing a resource-dependent admission restriction. -/
def allScalars : List Nat := (List.range 1114112).filter isUnicodeScalar

theorem mem_allScalars (scalar : Nat) :
    scalar ∈ allScalars ↔ isUnicodeScalar scalar = true := by
  simp only [allScalars, List.mem_filter, List.mem_range]
  constructor
  · exact And.right
  · intro valid
    have bounds := of_decide_eq_true valid
    exact ⟨by omega, valid⟩

theorem allScalars_sorted : allScalars.Pairwise (· < ·) :=
  List.pairwise_lt_range.filter isUnicodeScalar

theorem allScalars_valid : InventoryValid allScalars :=
  ⟨allScalars_sorted.imp Nat.ne_of_lt,
    fun scalar member => (mem_allScalars scalar).mp member⟩

theorem allScalars_nonempty : allScalars ≠ [] := by
  have zero : 0 ∈ allScalars := (mem_allScalars 0).mpr (by decide)
  intro empty
  rw [empty] at zero
  contradiction

theorem allScalars_scalarListWellFormed :
    ScalarListWellFormed (allScalars.map Int.ofNat) := by
  generalize equation : allScalars = scalars
  exact scalarListWellFormed_of_sorted scalars
    (equation ▸ allScalars_nonempty) (equation ▸ allScalars_sorted)
    (equation ▸ allScalars_valid.2)

theorem excluding_allScalars_accepts_nothing (scalar : Nat) :
    LexicalClassKind.accepts (.except allScalars) scalar = false := by
  by_cases valid : isUnicodeScalar scalar = true
  · have member := (mem_allScalars scalar).mpr valid
    simp [LexicalClassKind.accepts, valid, member]
  · have invalid : isUnicodeScalar scalar = false := Bool.eq_false_iff.mpr valid
    simp [LexicalClassKind.accepts, invalid]

theorem excluding_allScalars_is_uninhabited : ¬ InhabitedClass (.except allScalars) := by
  rintro ⟨scalar, accepted⟩
  rw [excluding_allScalars_accepts_nothing] at accepted
  contradiction

theorem full_exclusion_check_is_false : checkInhabited (.except allScalars) = false := by
  apply Bool.eq_false_iff.mpr
  intro checked
  exact excluding_allScalars_is_uninhabited
    ((checkInhabited_iff (.except allScalars) allScalars_valid).mp checked)

theorem full_exclusion_gap_check_is_false : exceptGapCheck allScalars = false := by
  apply Bool.eq_false_iff.mpr
  intro checked
  exact excluding_allScalars_is_uninhabited
    ((exceptGapCheck_iff allScalars allScalars_valid.2 allScalars_sorted).mp checked)

/-- Nonempty, strictly ordered, valid exclusions can still denote no
terminal at all. Declaration presence cannot justify productivity. -/
theorem well_formed_exclusion_can_be_uninhabited :
    ∃ excluded : List Nat,
      ScalarListWellFormed (excluded.map Int.ofNat) ∧
      ¬ InhabitedClass (.except excluded) := by
  generalize equation : allScalars = excluded
  refine ⟨excluded, ?_, equation ▸ excluding_allScalars_is_uninhabited⟩
  exact scalarListWellFormed_of_sorted excluded
    (equation ▸ allScalars_nonempty) (equation ▸ allScalars_sorted)
    (equation ▸ allScalars_valid.2)

theorem surrogate_hole_is_not_a_scalar_gap :
    55295 + 1 < (57344 : Nat) ∧
      ¬ ∃ scalar, isUnicodeScalar scalar = true ∧ 55295 < scalar ∧ scalar < 57344 := by
  refine ⟨by decide, ?_⟩
  rintro ⟨scalar, valid, low, high⟩
  have bounds := of_decide_eq_true valid
  omega

theorem gap_scan_endpoint_and_interior_controls :
    exceptGapCheck [] = true ∧ exceptGapCheck [1] = true ∧
      exceptGapCheck [0] = true ∧ gapAfter 1114109 [1114111] = true ∧
      gapAfter 1114110 [1114111] = false ∧ gapAfter 55295 [57345] = true := by
  decide

/-- The length optimization is unsound without duplicate-free inventory:
repeating one excluded scalar does not exclude the other scalars. -/
theorem cardinality_check_needs_duplicate_freedom :
    checkInhabited (.except (List.replicate 1112064 0)) = false ∧
      InhabitedClass (.except (List.replicate 1112064 0)) := by
  generalize equation : 1112064 = count
  constructor
  · simp only [checkInhabited, List.length_replicate, decide_eq_false_iff_not]
    omega
  · refine ⟨1, ?_⟩
    simp [LexicalClassKind.accepts, isUnicodeScalar]

#print axioms scalarCarrier_card
#print axioms checkInhabited_iff
#print axioms inventoryValid_of_scalarListWellFormed
#print axioms allScalars_scalarListWellFormed
#print axioms excluding_allScalars_is_uninhabited
#print axioms checkInhabitedByGaps_iff
#print axioms full_exclusion_gap_check_is_false

end Mettapedia.GSLT.Parsing.PlainBnfLexicalInhabitation
