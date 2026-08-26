import Mettapedia.Computability.KolmogorovComplexity.KraftChaitinEffective

/-!
# Saturating online Kraft--Chaitin streams

The ordinary stream theorem assumes a Kraft budget for every condition and
therefore proves that every request is allocated.  This file records the
complementary total construction: allocation failures are retained as
rejected requests, while every successfully assigned code remains globally
prefix-free within its condition.

This distinction is useful when a condition carries a proposed numerical
bound.  The request stream is safe for every proposal; a separate
condition-local budget theorem proves that all requests are accepted when the
proposal has the intended value.
-/

namespace KolmogorovComplexity

open scoped Classical

namespace KraftChaitin

/-! ## Structural safety without a global budget -/

/-- The part of the allocator invariant needed for prefix-freeness. -/
structure StructuralStateInv (state : State) : Prop where
  allocated_pf : state.allocated.Pairwise Incomp
  frontier_pf : state.frontier.Pairwise Incomp
  cross : ∀ allocated ∈ state.allocated, ∀ free ∈ state.frontier,
    Incomp allocated free

theorem structuralStateInv_initial :
    StructuralStateInv ⟨[], [[]]⟩ := by
  constructor <;> simp

/-- Removing one free prefix preserves structural safety. -/
theorem StructuralStateInv.of_cons
    {allocated : List BinString} {pfx : BinString}
    {frontier : List BinString}
    (h : StructuralStateInv ⟨allocated, pfx :: frontier⟩) :
    StructuralStateInv ⟨allocated, frontier⟩ := by
  have hFrontier : (pfx :: frontier).Pairwise Incomp := h.frontier_pf
  rw [List.pairwise_cons] at hFrontier
  exact ⟨h.allocated_pf, hFrontier.2,
    fun allocated hAllocated free hFree =>
      h.cross allocated hAllocated free (List.mem_cons_of_mem _ hFree)⟩

/-- Every successful allocation preserves structural safety, independently
of whether the complete request stream satisfies a Kraft budget. -/
theorem allocStep_preserves_structural {requestedLength : Nat} :
    ∀ (frontier allocated : List BinString) (code : BinString)
      (frontier' : List BinString),
      StructuralStateInv ⟨allocated, frontier⟩ →
      allocStep frontier requestedLength = some (code, frontier') →
      StructuralStateInv ⟨code :: allocated, frontier'⟩ := by
  intro frontier
  induction frontier with
  | nil =>
      intro allocated code frontier' _ hStep
      simp [allocStep] at hStep
  | cons pfx frontier ih =>
      intro allocated code frontier' hState hStep
      by_cases hFits : pfx.length ≤ requestedLength
      · simp only [allocStep, if_pos hFits, Option.some.injEq,
          Prod.mk.injEq] at hStep
        obtain ⟨hCode, hFrontier⟩ := hStep
        subst code
        subst frontier'
        have hTail := hState.of_cons
        have hPrefixCode : pfx <+:
            pfx ++ List.replicate (requestedLength - pfx.length) false :=
          ⟨List.replicate (requestedLength - pfx.length) false, rfl⟩
        have hFree : (pfx :: frontier).Pairwise Incomp :=
          hState.frontier_pf
        rw [List.pairwise_cons] at hFree
        refine ⟨?_, ?_, ?_⟩
        · rw [List.pairwise_cons]
          refine ⟨?_, hState.allocated_pf⟩
          intro old hOld
          exact ((hState.cross old hOld pfx List.mem_cons_self).of_prefix_right
            hPrefixCode).symm
        · rw [List.pairwise_append]
          refine ⟨siblingsOf_pairwise _ _, hTail.frontier_pf, ?_⟩
          intro sibling hSibling free hFreeMem
          exact (hFree.1 free hFreeMem).of_prefix_left
            (siblingsOf_extends hSibling)
        · intro assigned hAssigned free hFreeMem
          rcases List.mem_cons.mp hAssigned with rfl | hAssigned
          · rcases List.mem_append.mp hFreeMem with hSibling | hFreeMem
            · rcases siblingsOf_mem.mp hSibling with ⟨index, hIndex, rfl⟩
              exact (incomp_marker_zeros hIndex).symm
            · exact (hFree.1 free hFreeMem).of_prefix_left hPrefixCode
          · rcases List.mem_append.mp hFreeMem with hSibling | hFreeMem
            · exact (hState.cross assigned hAssigned pfx List.mem_cons_self).of_prefix_right
                (siblingsOf_extends hSibling)
            · exact hTail.cross assigned hAssigned free hFreeMem
      · simp only [allocStep, if_neg hFits] at hStep
        cases hRecursive : allocStep frontier requestedLength with
        | none =>
            rw [hRecursive] at hStep
            simp at hStep
        | some result =>
            obtain ⟨recursiveCode, recursiveFrontier⟩ := result
            rw [hRecursive] at hStep
            simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hStep
            obtain ⟨hCode, hFrontier⟩ := hStep
            subst code
            subst frontier'
            have hNew := ih allocated recursiveCode recursiveFrontier
              hState.of_cons hRecursive
            have hFree : (pfx :: frontier).Pairwise Incomp :=
              hState.frontier_pf
            rw [List.pairwise_cons] at hFree
            refine ⟨hNew.allocated_pf, ?_, ?_⟩
            · rw [List.pairwise_cons]
              refine ⟨?_, hNew.frontier_pf⟩
              intro free hFreeMem
              rcases allocStep_mem_extends hRecursive hFreeMem with
                hOld | ⟨oldPrefix, hOldPrefix, hExtends, _hLength⟩
              · exact hFree.1 free hOld
              · exact (hFree.1 oldPrefix hOldPrefix).of_prefix_right hExtends
            · intro assigned hAssigned free hFreeMem
              rcases List.mem_cons.mp hAssigned with hAssignedCode | hAssigned
              · subst assigned
                rcases List.mem_cons.mp hFreeMem with hFreePfx | hFreeMem
                · subst free
                  obtain ⟨oldPrefix, hOldPrefix, hExtends, _hLength⟩ :=
                    allocStep_code_extends hRecursive
                  exact ((hFree.1 oldPrefix hOldPrefix).of_prefix_right
                    hExtends).symm
                · exact hNew.cross recursiveCode List.mem_cons_self free hFreeMem
              · rcases List.mem_cons.mp hFreeMem with hFreePfx | hFreeMem
                · subst free
                  exact hState.cross assigned hAssigned pfx List.mem_cons_self
                · exact hNew.cross assigned
                    (List.mem_cons_of_mem _ hAssigned) free hFreeMem

/-- Every finite state of the failure-saturating stream is structurally safe. -/
theorem streamState_structural {Value : Type*}
    (requests : BinString → Nat → Request Value)
    (condition : BinString) (count : Nat) :
    StructuralStateInv (streamState requests condition count) := by
  induction count with
  | zero => exact structuralStateInv_initial
  | succ count ih =>
      simp only [streamState, advance]
      cases hStep : allocStep (streamState requests condition count).frontier
          (requests condition count).requestedLength with
      | none => simpa [hStep] using ih
      | some result =>
          obtain ⟨code, frontier'⟩ := result
          simpa [hStep] using
            (allocStep_preserves_structural
              (streamState requests condition count).frontier
              (streamState requests condition count).allocated code frontier'
              ih hStep)

/-- Codes allocated at distinct steps are prefix-incomparable even when some
requests in the stream are rejected. -/
theorem streamCode_incomp_of_lt_saturated {Value : Type*}
    {requests : BinString → Nat → Request Value} {condition : BinString}
    {first later : Nat} {firstCode laterCode : BinString}
    (hIndex : first < later)
    (hFirst : streamCode requests condition first = some firstCode)
    (hLater : streamCode requests condition later = some laterCode) :
    Incomp firstCode laterCode := by
  have hFirstNext := streamCode_mem_next hFirst
  have hFirstLater :
      firstCode ∈ (streamState requests condition later).allocated :=
    mem_streamState_allocated_of_le (by omega) hFirstNext
  have hLedger := streamState_allocated_succ_of_streamCode hLater
  have hPairwise :=
    (streamState_structural requests condition (later + 1)).allocated_pf
  rw [hLedger, List.pairwise_cons] at hPairwise
  exact (hPairwise.1 firstCode hFirstLater).symm

theorem streamCode_index_injective_saturated {Value : Type*}
    {requests : BinString → Nat → Request Value} {condition : BinString}
    {first later : Nat} {code : BinString}
    (hFirst : streamCode requests condition first = some code)
    (hLater : streamCode requests condition later = some code) :
    first = later := by
  rcases Nat.lt_trichotomy first later with hlt | heq | hgt
  · have hIncomp := streamCode_incomp_of_lt_saturated hlt hFirst hLater
    exact False.elim (hIncomp.1 List.prefix_rfl)
  · exact heq
  · have hIncomp := streamCode_incomp_of_lt_saturated hgt hLater hFirst
    exact False.elim (hIncomp.1 List.prefix_rfl)

theorem assignedCodes_incomp_saturated {Value : Type*}
    {requests : BinString → Nat → Request Value}
    {condition left right : BinString}
    (hLeft : Assigned requests condition left)
    (hRight : Assigned requests condition right) (hNe : left ≠ right) :
    Incomp left right := by
  obtain ⟨leftIndex, hLeftCode⟩ := hLeft
  obtain ⟨rightIndex, hRightCode⟩ := hRight
  rcases Nat.lt_trichotomy leftIndex rightIndex with hlt | heq | hgt
  · exact streamCode_incomp_of_lt_saturated hlt hLeftCode hRightCode
  · subst rightIndex
    have hEq : left = right :=
      Option.some.inj (hLeftCode.symm.trans hRightCode)
    exact absurd hEq hNe
  · exact (streamCode_incomp_of_lt_saturated hgt hRightCode hLeftCode).symm

/-! ## The saturated machine and operational readback -/

/-- A prefix machine that keeps every successful online assignment and
silently rejects requests made after the relevant frontier is exhausted. -/
noncomputable def saturatedKcMachine
    (requests : BinString → Nat → Request BinString) :
    ConditionalPrefixFreeMachine where
  compute := kcCompute requests
  prefix_free := by
    intro condition left right hPrefix hNe hLeftHalts
    by_cases hRight : Assigned requests condition right
    · have hLeft : Assigned requests condition left := by
        by_contra hNot
        simp [kcCompute, hNot] at hLeftHalts
      have hIncomp := assignedCodes_incomp_saturated hLeft hRight hNe
      exact False.elim (hIncomp.1 hPrefix)
    · simp [kcCompute, hRight]

theorem kcSearchAlgorithm_mem_iff_saturated
    {requests : BinString → Nat → Request BinString}
    {program condition output : BinString} :
    output ∈ kcSearchAlgorithm requests program condition ↔
      ∃ index, streamCode requests condition index = some program ∧
        (requests condition index).value = output := by
  constructor
  · intro hOutput
    obtain ⟨index, hStep⟩ := Nat.rfindOpt_spec hOutput
    exact ⟨index, (kcSearchStep_eq_some_iff.mp hStep).1,
      (kcSearchStep_eq_some_iff.mp hStep).2⟩
  · rintro ⟨index, hCode, hValue⟩
    have hStep : kcSearchStep requests program condition index = some output :=
      kcSearchStep_eq_some_iff.mpr ⟨hCode, hValue⟩
    have hDom : (kcSearchAlgorithm requests program condition).Dom :=
      Nat.rfindOpt_dom.mpr ⟨index, output, by simpa using hStep⟩
    let found := (kcSearchAlgorithm requests program condition).get hDom
    have hFoundMem : found ∈ kcSearchAlgorithm requests program condition :=
      Part.get_mem hDom
    obtain ⟨foundIndex, hFoundStep⟩ := Nat.rfindOpt_spec hFoundMem
    have hFoundCode := (kcSearchStep_eq_some_iff.mp hFoundStep).1
    have hFoundValue := (kcSearchStep_eq_some_iff.mp hFoundStep).2
    have hIndex : foundIndex = index :=
      streamCode_index_injective_saturated hFoundCode hCode
    have hFoundEq : found = output := by
      subst foundIndex
      exact hFoundValue.symm.trans hValue
    simpa [hFoundEq] using hFoundMem

theorem kcCompute_part_eq_search_saturated
    {requests : BinString → Nat → Request BinString}
    (program condition : BinString) :
    Part.ofOption (kcCompute requests program condition) =
      kcSearchAlgorithm requests program condition := by
  apply Part.ext
  intro output
  rw [kcSearchAlgorithm_mem_iff_saturated]
  by_cases hAssigned : Assigned requests condition program
  · have hFound := Nat.find_spec hAssigned
    constructor
    · intro hOutput
      have hValue : (requests condition (Nat.find hAssigned)).value = output := by
        have hValue' : output =
            (requests condition (Nat.find hAssigned)).value := by
          simpa [kcCompute, hAssigned] using hOutput
        exact hValue'.symm
      exact ⟨Nat.find hAssigned, hFound, hValue⟩
    · rintro ⟨index, hCode, hValue⟩
      have hIndex : Nat.find hAssigned = index :=
        streamCode_index_injective_saturated hFound hCode
      subst index
      simpa [kcCompute, hAssigned] using hValue.symm
  · constructor
    · simp [kcCompute, hAssigned]
    · rintro ⟨index, hCode, _hValue⟩
      exact (hAssigned ⟨index, hCode⟩).elim

/-- Every effective request stream induces an effective saturated prefix
machine; no global Kraft premise is required for safety. -/
theorem saturatedKcMachine_effective
    {requests : BinString → Nat → Request BinString}
    (effective : EffectiveRequestStream requests) :
    Partrec₂ fun program condition =>
      Part.ofOption ((saturatedKcMachine requests).compute program condition) := by
  unfold Partrec₂
  have hSearch : Partrec fun input : BinString × BinString =>
      kcSearchAlgorithm requests input.1 input.2 :=
    Partrec.rfindOpt (kcSearchStep_primrec effective).to_comp
  apply hSearch.of_eq
  intro input
  simpa [saturatedKcMachine] using
    (kcCompute_part_eq_search_saturated
      (requests := requests) input.1 input.2).symm

/-! ## Condition-local acceptance -/

/-- Kraft safety for one condition slice. -/
def KraftBudgetAt {Value : Type*}
    (requests : BinString → Nat → Request Value) (condition : BinString) : Prop :=
  ∀ count L,
    (∀ n ∈ requestedLengthsUpTo requests condition count, n ≤ L) →
    ((requestedLengthsUpTo requests condition count).map
      (fun n => 2 ^ (L - n))).sum ≤ 2 ^ L

theorem streamState_spec_at {Value : Type*}
    {requests : BinString → Nat → Request Value} {condition : BinString}
    (budget : KraftBudgetAt requests condition) (count L : Nat)
    (hL : ∀ n ∈ requestedLengthsUpTo requests condition count, n ≤ L) :
    StateInv L (streamState requests condition count) (2 ^ L) ∧
      (streamState requests condition count).allocated.map List.length =
        requestedLengthsUpTo requests condition count := by
  induction count with
  | zero => exact ⟨stateInv_initial L, rfl⟩
  | succ count ih =>
      have hPrevious : ∀ n ∈ requestedLengthsUpTo requests condition count,
          n ≤ L := by
        intro n hn
        exact hL n (List.mem_cons_of_mem _ hn)
      have hNext : (requests condition count).requestedLength ≤ L :=
        hL _ List.mem_cons_self
      obtain ⟨hInvariant, hLengths⟩ := ih hPrevious
      have hMass := allocatedMass_eq_requestedMass L hLengths
      have hWhole := budget (count + 1) L hL
      simp only [requestedLengthsUpTo, List.map_cons, List.sum_cons] at hWhole
      have hRoom :
          ((streamState requests condition count).allocated.map
              (fun code => 2 ^ (L - code.length))).sum +
            2 ^ (L - (requests condition count).requestedLength) ≤ 2 ^ L := by
        rw [hMass]
        omega
      obtain ⟨code, frontier', hStep⟩ :=
        allocStep_success hNext hInvariant hRoom
      have hPreserved := allocStep_preserves hNext
        (streamState requests condition count).frontier
        (streamState requests condition count).allocated code frontier' (2 ^ L)
        hInvariant hStep
      obtain ⟨_prefix, _hMem, _hExtends, hCodeLength⟩ :=
        allocStep_code_extends hStep
      constructor
      · simpa [streamState, advance, hStep] using hPreserved
      · simp only [streamState, advance, hStep, requestedLengthsUpTo,
          List.map_cons]
        rw [hCodeLength, hLengths]

theorem streamAllocStep_success_at {Value : Type*}
    {requests : BinString → Nat → Request Value} {condition : BinString}
    (budget : KraftBudgetAt requests condition) (index : Nat) :
    ∃ code frontier',
      allocStep (streamState requests condition index).frontier
        (requests condition index).requestedLength = some (code, frontier') := by
  let level := requestLevel requests condition (index + 1)
  have hAll : ∀ n ∈ requestedLengthsUpTo requests condition (index + 1),
      n ≤ level := by
    intro n hn
    exact requestedLength_le_requestLevel hn
  have hPrevious :
      ∀ n ∈ requestedLengthsUpTo requests condition index, n ≤ level := by
    intro n hn
    exact hAll n (List.mem_cons_of_mem _ hn)
  have hNext : (requests condition index).requestedLength ≤ level :=
    hAll _ List.mem_cons_self
  obtain ⟨hInvariant, hLengths⟩ :=
    streamState_spec_at budget index level hPrevious
  have hMass := allocatedMass_eq_requestedMass level hLengths
  have hWhole := budget (index + 1) level hAll
  simp only [requestedLengthsUpTo, List.map_cons, List.sum_cons] at hWhole
  apply allocStep_success hNext hInvariant
  rw [hMass]
  omega

theorem streamCode_exists_length_at {Value : Type*}
    {requests : BinString → Nat → Request Value} {condition : BinString}
    (budget : KraftBudgetAt requests condition) (index : Nat) :
    ∃ code, streamCode requests condition index = some code ∧
      code.length = (requests condition index).requestedLength := by
  obtain ⟨code, frontier', hStep⟩ :=
    streamAllocStep_success_at budget index
  refine ⟨code, ?_, ?_⟩
  · simp [streamCode, hStep]
  · obtain ⟨_prefix, _hMem, _hExtends, hLength⟩ :=
      allocStep_code_extends hStep
    exact hLength

/-- A request is realized by the saturated machine whenever its condition
slice has enough Kraft capacity for the complete prefix ending at that
request.  A full local budget gives this for every index. -/
theorem saturatedKcMachine_realizes_request_at
    {requests : BinString → Nat → Request BinString} {condition : BinString}
    (budget : KraftBudgetAt requests condition) (index : Nat) :
    ∃ code, code.length = (requests condition index).requestedLength ∧
      (saturatedKcMachine requests).compute code condition =
        some (requests condition index).value := by
  obtain ⟨code, hCode, hLength⟩ :=
    streamCode_exists_length_at budget index
  have hAssigned : Assigned requests condition code := ⟨index, hCode⟩
  have hFound := Nat.find_spec hAssigned
  have hIndex : Nat.find hAssigned = index :=
    streamCode_index_injective_saturated hFound hCode
  refine ⟨code, hLength, ?_⟩
  simp only [saturatedKcMachine, kcCompute, dif_pos hAssigned]
  rw [hIndex]

/-! ## Controls -/

/-- Positive control: the first one-bit request is assigned. -/
example : streamCode effectiveOverfullRequests [] 0 = some [false] := rfl

/-- Negative control: after both one-bit codewords are consumed, the third
one-bit request is rejected without compromising the machine. -/
example : streamCode effectiveOverfullRequests [] 2 = none := by decide

#print axioms allocStep_preserves_structural
#print axioms streamState_structural
#print axioms saturatedKcMachine_effective
#print axioms saturatedKcMachine_realizes_request_at

end KraftChaitin

end KolmogorovComplexity
