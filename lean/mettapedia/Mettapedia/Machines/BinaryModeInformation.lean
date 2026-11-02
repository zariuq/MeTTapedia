import Mettapedia.Machines.SortedRunMode
import Mathlib.Data.Int.Basic

/-!
# The continuation-minimal summary for two-label mode

For labels `false < true`, additions observe only the signed vote margin and
whether the input was empty. Equal summaries give equal answers after every
future addition; conversely every unequal summary has a distinguishing suffix.
The integer margin is unbounded: a fixed number of fields is not a bounded
number of bits. Deletions require information this quotient intentionally loses.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ModeAggregation.BinaryInformation

def vote (label : Bool) : Int := if label then 1 else -1
def margin (labels : List Bool) : Int := (labels.map vote).sum

structure Summary where
  margin : Int
  occupied : Bool
  deriving DecidableEq

def summarize (labels : List Bool) : Summary := ⟨margin labels, !labels.isEmpty⟩
def combine (left right : Summary) : Summary :=
  ⟨left.margin + right.margin, left.occupied || right.occupied⟩

def read (summary : Summary) : Option Bool :=
  if summary.occupied then some (decide (0 < summary.margin)) else none

def Valid (summary : Summary) : Prop := summary.occupied = false → summary.margin = 0

theorem summarize_valid (labels : List Bool) : Valid (summarize labels) := by
  cases labels <;> simp [Valid, summarize, margin]

theorem combine_valid (left right : Summary) (hl : Valid left) (hr : Valid right) : Valid (combine left right) := by
  intro empty
  have flags : left.occupied = false ∧ right.occupied = false := by simpa [combine] using empty
  simp [combine, hl flags.1, hr flags.2]

/-- The count-based specification is independent of the margin summary. -/
def answer (labels : List Bool) : Option Bool :=
  if labels = [] then none else some (decide (labels.count false < labels.count true))

theorem margin_counts (labels : List Bool) :
    margin labels = (labels.count true : Int) - (labels.count false : Int) := by
  induction labels with
  | nil => simp [margin]
  | cons label rest ih =>
    cases label <;> simp [margin, vote] at ih ⊢ <;> omega

theorem summarize_append (left right : List Bool) :
    summarize (left ++ right) = combine (summarize left) (summarize right) := by
  cases left <;> simp [summarize, combine, margin, Int.add_assoc]

theorem combine_assoc (a b c : Summary) : combine (combine a b) c = combine a (combine b c) := by
  simp [combine, Int.add_assoc, Bool.or_assoc]

theorem combine_comm (a b : Summary) : combine a b = combine b a := by
  simp [combine, Int.add_comm, Bool.or_comm]

theorem combine_empty (a : Summary) : combine (summarize []) a = a := by
  cases a
  simp [combine, summarize, margin]

theorem read_exact (labels : List Bool) : read (summarize labels) = answer labels := by
  have counts := margin_counts labels
  cases labels with
  | nil => simp [read, summarize, answer]
  | cons label rest =>
    have inequality : 0 < margin (label :: rest) ↔
        (label :: rest).count false < (label :: rest).count true := by omega
    simp [read, summarize, answer, inequality]

theorem answer_present (labels : List Bool) : (answer labels).isSome = !labels.isEmpty := by
  cases labels <;> simp [answer]

/-- Every integer margin has a nonempty realization. The neutral pair makes
zero and negative margins usable as distinguishing future contexts too. -/
def realize (difference : Int) : List Bool :=
  List.replicate difference.toNat true ++ List.replicate (-difference).toNat false ++ [false, true]

theorem realize_margin (difference : Int) : margin (realize difference) = difference := by
  simp [margin, realize, vote, List.sum_append, List.map_replicate, List.sum_replicate]
  omega

theorem realize_occupied (difference : Int) : (summarize (realize difference)).occupied = true := by
  simp [summarize, realize]

theorem valid_iff_realizable (summary : Summary) : Valid summary ↔ ∃ labels, summarize labels = summary := by
  constructor
  · intro valid
    cases occupied : summary.occupied with
    | false =>
      refine ⟨[], ?_⟩
      exact congrArg₂ Summary.mk (show margin [] = summary.margin by simpa [margin] using (valid occupied).symm)
        occupied.symm
    | true =>
      refine ⟨realize summary.margin, ?_⟩
      exact congrArg₂ Summary.mk (realize_margin summary.margin)
        ((realize_occupied summary.margin).trans occupied.symm)
  · rintro ⟨labels, rfl⟩
    exact summarize_valid labels

theorem answer_append_realize (labels : List Bool) (difference : Int) :
    answer (labels ++ realize difference) = some (decide (0 < margin labels + difference)) := by
  rw [← read_exact, summarize_append]
  dsimp only [read, combine]
  rw [realize_occupied]
  simp only [Bool.or_true, ↓reduceIte, summarize]
  simp only [realize_margin]

def SameFuture (left right : List Bool) : Prop :=
  ∀ suffix, answer (left ++ suffix) = answer (right ++ suffix)

theorem sameFuture_margin {left right : List Bool} (same : SameFuture left right) : margin left = margin right := by
  have notLess : ¬ margin left < margin right := by
    intro less
    have observe := same (realize (-margin left))
    rw [answer_append_realize, answer_append_realize] at observe
    have positive : 0 < margin right + -margin left := by omega
    simp [positive] at observe
  have notGreater : ¬ margin right < margin left := by
    intro greater
    have observe := same (realize (-margin right))
    rw [answer_append_realize, answer_append_realize] at observe
    have positive : 0 < margin left + -margin right := by omega
    simp [positive] at observe
  omega

theorem sameFuture_iff_summary (left right : List Bool) :
    SameFuture left right ↔ summarize left = summarize right := by
  constructor
  · intro same
    have balance := sameFuture_margin same
    have present := congrArg Option.isSome (same [])
    simp only [List.append_nil, answer_present] at present
    exact congrArg₂ Summary.mk balance present
  · intro same suffix
    rw [← read_exact, ← read_exact, summarize_append, summarize_append, same]

/-- Every summary that can answer all additions must distinguish at least
these classes. No particular representation or merge operation is assumed. -/
theorem every_future_summary_refines {Code : Type} (encode : List Bool → Code)
    (decode : Code → List Bool → Option Bool)
    (correct : ∀ labels suffix, decode (encode labels) suffix = answer (labels ++ suffix))
    {left right : List Bool} (same : encode left = encode right) : summarize left = summarize right := by
  apply (sameFuture_iff_summary left right).mp
  intro suffix
  rw [← correct, ← correct, same]

theorem no_finite_future_summary (Code : Type) [Fintype Code] :
    ¬ ∃ (encode : List Bool → Code) (decode : Code → List Bool → Option Bool),
      ∀ labels suffix, decode (encode labels) suffix = answer (labels ++ suffix) := by
  rintro ⟨encode, decode, correct⟩
  have injective : Function.Injective (fun i : Fin (Fintype.card Code + 1) => encode (realize i.val)) := by
    intro a b same
    have summary := every_future_summary_refines encode decode correct same
    have balance := congrArg Summary.margin summary
    simp only [summarize, realize_margin] at balance
    exact Fin.ext (by omega)
  have impossible := Fintype.card_le_of_injective _ injective
  simp only [Fintype.card_fin] at impossible
  omega

/-! ## Joining the two-label quotient to the source mode interface -/

def labelNat (label : Bool) : Nat := if label then 1 else 0

theorem labelNat_injective : Function.Injective labelNat := by
  intro a b same
  cases a <;> cases b <;> simp_all [labelNat]

theorem labelNat_count (labels : List Bool) (label : Bool) :
    (labels.map labelNat).count (labelNat label) = labels.count label :=
  List.count_map_of_injective labels labelNat labelNat_injective label

theorem binary_mode_exact (labels : List Bool) :
    mode (labels.map labelNat) = (answer labels).map labelNat := by
  by_cases empty : labels = []
  · subst labels; rfl
  · by_cases more : labels.count false < labels.count true
    · simp only [answer, empty, ↓reduceIte, more, decide_true, Option.map_some]
      apply (mode_spec _ _).mpr
      have present : true ∈ labels := List.count_pos_iff.mp (by omega)
      refine ⟨List.mem_map.mpr ⟨true, present, rfl⟩, ?_⟩
      intro other member
      obtain ⟨bit, _, rfl⟩ := List.mem_map.mp member
      rw [labelNat_count, labelNat_count]
      cases bit <;> simp [labelNat]
      omega
    · simp only [answer, empty, ↓reduceIte, more, decide_false, Option.map_some]
      apply (mode_spec _ _).mpr
      have present : false ∈ labels := by
        by_contra absent
        have zero := List.count_eq_zero.mpr absent
        have noTrue : true ∉ labels := List.count_eq_zero.mp (by omega)
        apply empty
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro bit member
        cases bit
        · exact absent member
        · exact noTrue member
      refine ⟨List.mem_map.mpr ⟨false, present, rfl⟩, ?_⟩
      intro other member
      obtain ⟨bit, _, rfl⟩ := List.mem_map.mp member
      rw [labelNat_count, labelNat_count]
      cases bit <;> simp [labelNat]
      omega

theorem binary_sorted_source (labels : List Bool) :
    SortedRun.sourceMode ((labels.map labelNat).mergeSort (· ≤ ·)) =
      (read (summarize labels)).map labelNat := by
  rw [SortedRun.sorted_source_is_histogram_readout, sparse_readout_exact, binary_mode_exact, read_exact]

/-- If an enclosing observer fixes the empty default to the smaller label,
the occupancy bit itself becomes unnecessary. -/
theorem default_false_exact (labels : List Bool) :
    (answer labels).getD false = decide (0 < margin labels) := by
  rw [← read_exact]
  cases labels <;> simp [read, summarize, margin]

theorem sameFuture_default_false (left right : List Bool) :
    (∀ suffix, (answer (left ++ suffix)).getD false = (answer (right ++ suffix)).getD false) ↔
      margin left = margin right := by
  constructor
  · intro same
    have notLess : ¬ margin left < margin right := by
      intro less
      have observe := same (realize (-margin left))
      rw [answer_append_realize, answer_append_realize] at observe
      have positive : 0 < margin right + -margin left := by omega
      simp [positive] at observe
    have notGreater : ¬ margin right < margin left := by
      intro greater
      have observe := same (realize (-margin right))
      rw [answer_append_realize, answer_append_realize] at observe
      have positive : 0 < margin left + -margin right := by omega
      simp [positive] at observe
    omega
  · intro same suffix
    rw [default_false_exact, default_false_exact]
    have add (xs ys : List Bool) : margin (xs ++ ys) = margin xs + margin ys := by simp [margin]
    simp only [add, same]

namespace Controls

theorem common_votes_can_be_forgotten :
    summarize [false, true] = summarize [false, false, true, true] := by decide

theorem total_vote_count_is_not_recoverable :
    ¬ ∃ recover : Summary → Nat, ∀ labels, recover (summarize labels) = labels.length := by
  rintro ⟨recover, correct⟩
  have short := correct [false, true]
  have long := correct [false, false, true, true]
  rw [common_votes_can_be_forgotten] at short
  simp only [List.length_cons, List.length_nil] at short long
  omega

theorem empty_is_not_balanced_nonempty :
    margin [] = margin [false, true] ∧ answer [] ≠ answer [false, true] := by decide

theorem deletion_distinguishes :
    summarize [false, true] = summarize [false, false, true, true] ∧
    answer (([false, true].erase false).erase true) ≠
      answer (([false, false, true, true].erase false).erase true) := by decide

theorem fallback_changes_required_information :
    (answer []).getD false = (answer [false, true]).getD false ∧
    (answer []).getD true ≠ (answer [false, true]).getD true := by decide

end Controls
end Mettapedia.Machines.ModeAggregation.BinaryInformation
