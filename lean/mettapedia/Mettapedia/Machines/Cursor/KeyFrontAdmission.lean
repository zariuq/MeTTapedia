import Mettapedia.Machines.Cursor.KeyFrontTerms

/-!
# Bounded front metadata without bounded source terms

Closing delimiters do not consume a preorder node position. The bounded
front construction retains at most the requested number of actual nodes.
First-variable counters can therefore omit empty early bands while a late
counter causes front truncation. Both are index decisions, not restrictions
on term depth, variable names, or the language's unification relation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Cursor.KeyFrontAdmission

open KeyFrontRanges KeyFrontCompleteness

def nodes (key : Key) : Nat :=
  (key.filter (fun token => kind token != 0)).length

theorem nodes_append (left right : Key) : nodes (left ++ right) = nodes left + nodes right := by
  simp [nodes]

def takeNodes : Nat → Key → Key
  | 0, _ => []
  | _ + 1, [] => []
  | budget + 1, token :: later =>
      token :: takeNodes (if kind token = 0 then budget + 1 else budget) later

theorem takeNodes_prefix (budget : Nat) (key : Key) : takeNodes budget key <+: key := by
  induction key generalizing budget with
  | nil => cases budget <;> simp [takeNodes]
  | cons token later ih =>
      cases budget with
      | zero => simp [takeNodes]
      | succ budget =>
          obtain ⟨rest, equation⟩ := ih (if kind token = 0 then budget + 1 else budget)
          exact ⟨rest, by simpa only [takeNodes, List.cons_append] using congrArg (token :: ·) equation⟩

theorem takeNodes_bound (budget : Nat) (key : Key) : nodes (takeNodes budget key) ≤ budget := by
  induction key generalizing budget with
  | nil => cases budget <;> simp [takeNodes, nodes]
  | cons token later ih =>
      cases budget with
      | zero => simp [takeNodes, nodes]
      | succ budget =>
          by_cases closing : kind token = 0
          · simpa [takeNodes, closing, nodes] using ih (budget + 1)
          · simpa [takeNodes, closing, nodes] using Nat.succ_le_succ (ih budget)

theorem front_append_variable (stem : Key) (name : Nat) (later : Key)
    (rigidStem : ∀ token ∈ stem, kind token ≠ 1) :
    front (stem ++ varToken name :: later) = stem := by
  induction stem with
  | nil => simp [front, varToken, kind]
  | cons token stem ih =>
      have first := rigidStem token (by simp)
      have remaining := ih (fun item member => rigidStem item (by simp [member]))
      simpa only [List.cons_append, front, first, ↓reduceIte] using congrArg (token :: ·) remaining

def firstNode (row : Key) : Option Nat :=
  if front row = row then none else some (nodes (front row))

theorem firstNode_band (stem row : Key) (rigidStem : ∀ token ∈ stem, kind token ≠ 1)
    (band : Band stem row) : firstNode row = some (nodes stem) := by
  obtain ⟨name, later, rfl⟩ := band
  have frontEq := front_append_variable stem name later rigidStem
  have different : stem ≠ stem ++ varToken name :: later := by
    intro equal
    have lengths := congrArg List.length equal
    simp only [List.length_append, List.length_cons] at lengths
    omega
  simp [firstNode, frontEq, different]

def earlyCount (rows : List Key) (position : Nat) : Nat :=
  (rows.filter (fun row => firstNode row = some position)).length

def lateCount (limit : Nat) (rows : List Key) : Nat :=
  (rows.filter (fun row => match firstNode row with
    | none => false
    | some position => decide (limit ≤ position))).length

theorem earlyCount_nonzero (rows : List Key) (position : Nat) :
    earlyCount rows position ≠ 0 ↔ ∃ row ∈ rows, firstNode row = some position := by
  simp [earlyCount, List.filter_eq_nil_iff]

theorem earlyCount_add (rows : List Key) (row : Key) (position : Nat) :
    earlyCount (rows ++ [row]) position =
      earlyCount rows position + if firstNode row = some position then 1 else 0 := by
  by_cases selected : firstNode row = some position <;> simp [earlyCount, selected]

theorem no_late_member (limit : Nat) (rows : List Key) (row : Key) (position : Nat)
    (absent : lateCount limit rows = 0) (member : row ∈ rows)
    (first : firstNode row = some position) : position < limit := by
  have noneLate : ∀ item ∈ rows, ¬ (match firstNode item with
      | none => false
      | some node => decide (limit ≤ node)) = true := by
    simpa [lateCount, List.filter_eq_nil_iff] using absent
  have outside := noneLate row member
  simp only [first, decide_eq_true_eq, not_le] at outside
  exact outside

/-- On a stored occurrence, a zero count can safely omit that band; positive
global counts alone do not assert that the query's particular band is nonempty. -/
theorem candidate_band_has_count (query row stem before : Key) (token : Token)
    (later : Key) (rows : List Key) (member : row ∈ rows)
    (queryFront : stem <+: front query) (decomposition : stem = before ++ token :: later)
    (band : Band before row) : earlyCount rows (nodes before) ≠ 0 := by
  apply (earlyCount_nonzero rows _).mpr
  refine ⟨row, member, firstNode_band before row ?_ band⟩
  intro item inBefore
  have inStem : item ∈ stem := by rw [decomposition]; simp [inBefore]
  exact front_rigid query item (queryFront.subset inStem)

theorem candidate_band_before_limit (stem before : Key) (token : Token) (later : Key)
    (decomposition : stem = before ++ token :: later) (ground : 1 < kind token)
    (limit : Nat) (bounded : nodes stem ≤ limit) : nodes before < limit := by
  have nonzero : kind token ≠ 0 := by omega
  have positive : (kind token != 0) = true := by simp [nonzero]
  rw [decomposition, nodes_append] at bounded
  have length : nodes (token :: later) = 1 + nodes later := by simp [nodes, positive, Nat.add_comm]
  rw [length] at bounded
  omega

def selectedFront (limit : Nat) (rows : List Key) (raw : Key) : Key :=
  if lateCount limit rows = 0 then raw else takeNodes limit raw

theorem selectedFront_prefix (limit : Nat) (rows : List Key) (raw : Key) :
    selectedFront limit rows raw <+: raw := by
  unfold selectedFront
  split
  · exact List.prefix_refl _
  · exact takeNodes_prefix limit raw

/-- The chosen front is complete, and every needed variable band is counted
among the bounded early positions. This applies to every stored occurrence. -/
theorem selected_front_complete (limit : Nat) (rows : List Key)
    (queryEnvironment rowEnvironment : Nat → Key) (query row raw : Key)
    (justified : raw <+: front query)
    (proper : Proper rowEnvironment) (member : row ∈ rows)
    (common : expand queryEnvironment query = expand rowEnvironment row) :
    selectedFront limit rows raw <+: row ∨
      ∃ before token later, selectedFront limit rows raw = before ++ token :: later ∧
        1 < kind token ∧ Band before row ∧ nodes before < limit ∧
        earlyCount rows (nodes before) ≠ 0 := by
  have chosen := (selectedFront_prefix limit rows raw).trans justified
  rcases common_instance_candidate queryEnvironment rowEnvironment query row _ proper chosen common with
    direct | ⟨before, token, later, decomposition, ground, band⟩
  · exact Or.inl direct
  · have counted := candidate_band_has_count query row _ before token later rows
      member chosen decomposition band
    have ordinal : nodes before < limit := by
      by_cases late : lateCount limit rows = 0
      · have first : firstNode row = some (nodes before) := by
          apply firstNode_band before row ?_ band
          intro item inBefore
          exact front_rigid query item (chosen.subset (by rw [decomposition]; simp [inBefore]))
        exact no_late_member limit rows row (nodes before) late member first
      · apply candidate_band_before_limit _ before token later decomposition ground limit
        simpa only [selectedFront, late, ↓reduceIte] using takeNodes_bound limit raw
    exact Or.inr ⟨before, token, later, decomposition, ground, band, ordinal, counted⟩

theorem nodes_prefix_monotone (left right : Key) (stem : left <+: right) :
    nodes left ≤ nodes right := by
  obtain ⟨later, rfl⟩ := stem
  rw [nodes_append]
  omega

/-- Ordering the actual preorder node ordinals also orders the token bands;
closing delimiters cannot introduce a second band at one node. -/
theorem earlier_band_precedes_later (whole beforeLeft beforeRight left right : Key)
    (leftToken : Token) (leftLater : Key)
    (decomposition : whole = beforeLeft ++ leftToken :: leftLater)
    (rightStem : beforeRight <+: whole)
    (earlier : nodes beforeLeft < nodes beforeRight) (rigidLeft : 1 < kind leftToken)
    (leftBand : Band beforeLeft left) (rightBand : Band beforeRight right) : left < right := by
  have leftStem : beforeLeft <+: whole := ⟨leftToken :: leftLater, decomposition.symm⟩
  have leftBefore : beforeLeft <+: beforeRight := by
    rcases List.prefix_or_prefix_of_prefix leftStem rightStem with forward | backward
    · exact forward
    · have noEarlier := nodes_prefix_monotone beforeRight beforeLeft backward
      omega
  have longer : beforeLeft.length < beforeRight.length := by
    have ordered := leftBefore.length_le
    by_contra sameLength
    have same : beforeLeft = beforeRight :=
      leftBefore.eq_of_length (by omega)
    rw [same] at earlier
    omega
  have throughNode : beforeLeft ++ [leftToken] <+: whole :=
    ⟨leftLater, by simp [decomposition, List.append_assoc]⟩
  have inside : beforeLeft ++ [leftToken] <+: beforeRight :=
    List.prefix_of_prefix_length_le throughNode rightStem (by simp; omega)
  obtain ⟨middle, equation⟩ := inside
  obtain ⟨leftName, leftRest, rfl⟩ := leftBand
  obtain ⟨rightName, rightRest, rfl⟩ := rightBand
  rw [← equation]
  simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using
    band_before_extension beforeLeft leftToken rigidLeft leftName leftRest
      (middle ++ varToken rightName :: rightRest)

theorem band_precedes_full_front (whole before left right : Key) (token : Token) (later : Key)
    (decomposition : whole = before ++ token :: later) (rigidNode : 1 < kind token)
    (band : Band before left) (full : whole <+: right) : left < right := by
  obtain ⟨name, leftRest, rfl⟩ := band
  obtain ⟨rightRest, rfl⟩ := full
  rw [decomposition]
  simpa only [List.append_assoc, List.cons_append] using
    band_before_extension before token rigidNode name leftRest (later ++ rightRest)

end Mettapedia.Machines.Cursor.KeyFrontAdmission
