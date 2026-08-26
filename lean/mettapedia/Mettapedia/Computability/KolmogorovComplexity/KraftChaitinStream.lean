import Mettapedia.Computability.KolmogorovComplexity.KraftChaitin

/-!
# Online Kraft–Chaitin request streams

`KraftChaitin.lean` proves one-step allocation and exact finite-capacity
conservation.  This file iterates that allocator over a condition-indexed
request stream and packages the resulting code assignment as a conditional
prefix-free machine.

The budget is stated for every finite request prefix at a common denominator
level `L`.  This keeps the construction entirely in `Nat`: a request of length
`n` has integer mass `2^(L-n)`.  The principal result,
`kcMachine_complexity_le_requestedLength`, realizes every request with a
program of exactly its requested length.

The stream construction is classical only when it reads back the output
associated with an assigned code using `Nat.find`.  Allocation and every
finite invariant are executable definitions.
-/

namespace KolmogorovComplexity

open scoped Classical

namespace KraftChaitin

/-- One coding request: an output value and its desired codeword length. -/
structure Request (Value : Type*) where
  value : Value
  requestedLength : Nat

/-- Requested lengths, newest first, after the first `count` requests.  This
order agrees with the allocator's newest-first codeword ledger. -/
def requestedLengthsUpTo {Value : Type*}
    (requests : BinString → Nat → Request Value) (condition : BinString) :
    Nat → List Nat
  | 0 => []
  | count + 1 =>
      (requests condition count).requestedLength ::
        requestedLengthsUpTo requests condition count

/-- Every request before `count` occurs in the finite length ledger. -/
theorem requestedLength_mem_requestedLengthsUpTo {Value : Type*}
    {requests : BinString → Nat → Request Value} {condition : BinString}
    {index count : Nat} (hIndex : index < count) :
    (requests condition index).requestedLength ∈
      requestedLengthsUpTo requests condition count := by
  induction count with
  | zero => omega
  | succ count ih =>
      by_cases hLast : index = count
      · subst index
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih (by omega))

/-- Summing the newest-first length ledger is the same as summing the request
indices in their ordinary order. -/
theorem sum_map_requestedLengthsUpTo_eq_sum_range {Value : Type*}
    (requests : BinString → Nat → Request Value) (condition : BinString)
    (count : Nat) (weight : Nat → Nat) :
    ((requestedLengthsUpTo requests condition count).map weight).sum =
      ∑ index ∈ Finset.range count,
        weight (requests condition index).requestedLength := by
  induction count with
  | zero => simp [requestedLengthsUpTo]
  | succ count ih =>
      simp only [requestedLengthsUpTo, List.map_cons, List.sum_cons,
        Finset.sum_range_succ]
      rw [ih]
      omega

/-- Every finite prefix of a request stream satisfies the binary Kraft bound,
written at any common denominator level bounding its requested lengths. -/
def KraftBudget {Value : Type*}
    (requests : BinString → Nat → Request Value) : Prop :=
  ∀ condition count L,
    (∀ n ∈ requestedLengthsUpTo requests condition count, n ≤ L) →
    ((requestedLengthsUpTo requests condition count).map
      (fun n => 2 ^ (L - n))).sum ≤ 2 ^ L

/-- Advance an allocator state by one length request.  The failure branch is
kept total; `streamState_spec` proves that it is unreachable under
`KraftBudget`. -/
def advance (state : State) (requestedLength : Nat) : State :=
  match allocStep state.frontier requestedLength with
  | none => state
  | some (code, frontier') => ⟨code :: state.allocated, frontier'⟩

/-- Allocator state after a finite request prefix. -/
def streamState {Value : Type*}
    (requests : BinString → Nat → Request Value) (condition : BinString) :
    Nat → State
  | 0 => ⟨[], [[]]⟩
  | count + 1 =>
      advance (streamState requests condition count)
        (requests condition count).requestedLength

/-- The codeword assigned to request `index`, if allocation succeeds. -/
def streamCode {Value : Type*}
    (requests : BinString → Nat → Request Value)
    (condition : BinString) (index : Nat) : Option BinString :=
  match allocStep (streamState requests condition index).frontier
      (requests condition index).requestedLength with
  | none => none
  | some (code, _frontier') => some code

/-- Re-express codeword mass through the ledger of their lengths. -/
theorem allocatedMass_eq_requestedMass {allocated : List BinString}
    {lengths : List Nat} (L : Nat)
    (hlengths : allocated.map List.length = lengths) :
    (allocated.map fun code => 2 ^ (L - code.length)).sum =
      (lengths.map fun n => 2 ^ (L - n)).sum := by
  calc
    (allocated.map fun code => 2 ^ (L - code.length)).sum =
        ((allocated.map List.length).map fun n => 2 ^ (L - n)).sum := by
          simp only [List.map_map]
          rfl
    _ = (lengths.map fun n => 2 ^ (L - n)).sum := by rw [hlengths]

/-- The iterated allocator preserves its exact finite-capacity invariant, and
its allocated ledger has exactly the requested lengths in matching order. -/
theorem streamState_spec {Value : Type*}
    {requests : BinString → Nat → Request Value}
    (budget : KraftBudget requests) (condition : BinString) (count L : Nat)
    (hL : ∀ n ∈ requestedLengthsUpTo requests condition count, n ≤ L) :
    StateInv L (streamState requests condition count) (2 ^ L) ∧
      (streamState requests condition count).allocated.map List.length =
        requestedLengthsUpTo requests condition count := by
  induction count with
  | zero =>
      exact ⟨stateInv_initial L, rfl⟩
  | succ count ih =>
      have hprevious : ∀ n ∈ requestedLengthsUpTo requests condition count,
          n ≤ L := by
        intro n hn
        exact hL n (List.mem_cons_of_mem _ hn)
      have hnext : (requests condition count).requestedLength ≤ L :=
        hL _ List.mem_cons_self
      obtain ⟨hinvariant, hlengths⟩ := ih hprevious
      have hmass :
          ((streamState requests condition count).allocated.map
            (fun code => 2 ^ (L - code.length))).sum =
          ((requestedLengthsUpTo requests condition count).map
            (fun n => 2 ^ (L - n))).sum :=
        allocatedMass_eq_requestedMass L hlengths
      have hwhole := budget condition (count + 1) L hL
      simp only [requestedLengthsUpTo, List.map_cons, List.sum_cons] at hwhole
      have hroom :
          ((streamState requests condition count).allocated.map
              (fun code => 2 ^ (L - code.length))).sum +
            2 ^ (L - (requests condition count).requestedLength) ≤ 2 ^ L := by
        rw [hmass]
        omega
      obtain ⟨code, frontier', hstep⟩ :=
        allocStep_success hnext hinvariant hroom
      have hpreserved := allocStep_preserves hnext
        (streamState requests condition count).frontier
        (streamState requests condition count).allocated code frontier' (2 ^ L)
        hinvariant hstep
      obtain ⟨_prefix, _hmem, _hextends, hcodeLength⟩ :=
        allocStep_code_extends hstep
      constructor
      · simpa [streamState, advance, hstep] using hpreserved
      · simp only [streamState, advance, hstep, requestedLengthsUpTo,
          List.map_cons]
        rw [hcodeLength, hlengths]

/-- A list member is bounded by the list's maximum fold. -/
theorem le_foldr_max_of_mem {n : Nat} {lengths : List Nat}
    (hn : n ∈ lengths) : n ≤ lengths.foldr max 0 :=
  List.le_max_of_le' 0 hn le_rfl

/-- A finite request prefix always has a finite common denominator level. -/
def requestLevel {Value : Type*}
    (requests : BinString → Nat → Request Value)
    (condition : BinString) (count : Nat) : Nat :=
  (requestedLengthsUpTo requests condition count).foldr max 0

theorem requestedLength_le_requestLevel {Value : Type*}
    {requests : BinString → Nat → Request Value}
    {condition : BinString} {count n : Nat}
    (hn : n ∈ requestedLengthsUpTo requests condition count) :
    n ≤ requestLevel requests condition count :=
  le_foldr_max_of_mem hn

/-- Under the stream budget, the one-step allocator never reaches its failure
branch. -/
theorem streamAllocStep_success {Value : Type*}
    {requests : BinString → Nat → Request Value}
    (budget : KraftBudget requests) (condition : BinString) (index : Nat) :
    ∃ code frontier',
      allocStep (streamState requests condition index).frontier
        (requests condition index).requestedLength = some (code, frontier') := by
  let L := requestLevel requests condition (index + 1)
  have hAll : ∀ n ∈ requestedLengthsUpTo requests condition (index + 1),
      n ≤ L := by
    intro n hn
    exact requestedLength_le_requestLevel hn
  have hprevious :
      ∀ n ∈ requestedLengthsUpTo requests condition index, n ≤ L := by
    intro n hn
    exact hAll n (List.mem_cons_of_mem _ hn)
  have hnext : (requests condition index).requestedLength ≤ L :=
    hAll _ List.mem_cons_self
  obtain ⟨hinvariant, hlengths⟩ :=
    streamState_spec budget condition index L hprevious
  have hmass :
      ((streamState requests condition index).allocated.map
        (fun code => 2 ^ (L - code.length))).sum =
      ((requestedLengthsUpTo requests condition index).map
        (fun n => 2 ^ (L - n))).sum :=
    allocatedMass_eq_requestedMass L hlengths
  have hwhole := budget condition (index + 1) L hAll
  simp only [requestedLengthsUpTo, List.map_cons, List.sum_cons] at hwhole
  apply allocStep_success hnext hinvariant
  rw [hmass]
  omega

/-- Every request receives a codeword of exactly its requested length. -/
theorem streamCode_exists_length {Value : Type*}
    {requests : BinString → Nat → Request Value}
    (budget : KraftBudget requests) (condition : BinString) (index : Nat) :
    ∃ code, streamCode requests condition index = some code ∧
      code.length = (requests condition index).requestedLength := by
  obtain ⟨code, frontier', hstep⟩ :=
    streamAllocStep_success budget condition index
  refine ⟨code, ?_, ?_⟩
  · simp [streamCode, hstep]
  · obtain ⟨_prefix, _hmem, _hextends, hlength⟩ :=
      allocStep_code_extends hstep
    exact hlength

/-! ## Global prefix-freeness of the stream assignment -/

/-- A code returned at a step is the new head of the next state's allocated
ledger. -/
theorem streamState_allocated_succ_of_streamCode {Value : Type*}
    {requests : BinString → Nat → Request Value}
    {condition : BinString} {index : Nat} {code : BinString}
    (hcode : streamCode requests condition index = some code) :
    (streamState requests condition (index + 1)).allocated =
      code :: (streamState requests condition index).allocated := by
  unfold streamCode at hcode
  cases hstep : allocStep (streamState requests condition index).frontier
      (requests condition index).requestedLength with
  | none => simp [hstep] at hcode
  | some result =>
      obtain ⟨assigned, frontier'⟩ := result
      simp only [hstep, Option.some.injEq] at hcode
      subst assigned
      simp [streamState, advance, hstep]

/-- Allocated codewords persist in the next state. -/
theorem mem_streamState_allocated_succ {Value : Type*}
    {requests : BinString → Nat → Request Value}
    {condition : BinString} {index : Nat} {code : BinString}
    (hcode : code ∈ (streamState requests condition index).allocated) :
    code ∈ (streamState requests condition (index + 1)).allocated := by
  simp only [streamState, advance]
  cases hstep : allocStep (streamState requests condition index).frontier
      (requests condition index).requestedLength with
  | none => simpa [hstep] using hcode
  | some result =>
      obtain ⟨assigned, frontier'⟩ := result
      simp [hcode]

/-- Allocated codewords persist through every later stream state. -/
theorem mem_streamState_allocated_of_le {Value : Type*}
    {requests : BinString → Nat → Request Value}
    {condition : BinString} {first later : Nat} {code : BinString}
    (hindex : first ≤ later)
    (hcode : code ∈ (streamState requests condition first).allocated) :
    code ∈ (streamState requests condition later).allocated := by
  induction later generalizing first with
  | zero =>
      have hfirst : first = 0 := by omega
      simpa [hfirst] using hcode
  | succ later ih =>
      by_cases hlast : first = later + 1
      · simpa [hlast] using hcode
      · have hprevious : first ≤ later := by omega
        exact mem_streamState_allocated_succ (ih hprevious hcode)

/-- A returned code occurs in the allocated ledger immediately after its
request. -/
theorem streamCode_mem_next {Value : Type*}
    {requests : BinString → Nat → Request Value}
    {condition : BinString} {index : Nat} {code : BinString}
    (hcode : streamCode requests condition index = some code) :
    code ∈ (streamState requests condition (index + 1)).allocated := by
  rw [streamState_allocated_succ_of_streamCode hcode]
  exact List.mem_cons_self

/-- Codes allocated at distinct chronological steps are prefix-incomparable. -/
theorem streamCode_incomp_of_lt {Value : Type*}
    {requests : BinString → Nat → Request Value}
    (budget : KraftBudget requests) {condition : BinString}
    {first later : Nat} {firstCode laterCode : BinString}
    (hindex : first < later)
    (hfirst : streamCode requests condition first = some firstCode)
    (hlater : streamCode requests condition later = some laterCode) :
    Incomp firstCode laterCode := by
  have hfirstNext := streamCode_mem_next hfirst
  have hfirstLater :
      firstCode ∈ (streamState requests condition later).allocated :=
    mem_streamState_allocated_of_le (by omega) hfirstNext
  let L := requestLevel requests condition (later + 1)
  have hAll : ∀ n ∈ requestedLengthsUpTo requests condition (later + 1),
      n ≤ L := by
    intro n hn
    exact requestedLength_le_requestLevel hn
  have hinvariant := (streamState_spec budget condition (later + 1) L hAll).1
  have hledger := streamState_allocated_succ_of_streamCode hlater
  have hpairwise := hinvariant.allocated_pf
  rw [hledger, List.pairwise_cons] at hpairwise
  exact (hpairwise.1 firstCode hfirstLater).symm

/-- The stream assignment is injective in its request index. -/
theorem streamCode_index_injective {Value : Type*}
    {requests : BinString → Nat → Request Value}
    (budget : KraftBudget requests) {condition : BinString}
    {first later : Nat} {code : BinString}
    (hfirst : streamCode requests condition first = some code)
    (hlater : streamCode requests condition later = some code) :
    first = later := by
  rcases Nat.lt_trichotomy first later with hlt | heq | hgt
  · have hinc := streamCode_incomp_of_lt budget hlt hfirst hlater
    exact False.elim (hinc.1 List.prefix_rfl)
  · exact heq
  · have hinc := streamCode_incomp_of_lt budget hgt hlater hfirst
    exact False.elim (hinc.1 List.prefix_rfl)

/-- A codeword has been assigned somewhere in the request stream for this
condition. -/
def Assigned {Value : Type*}
    (requests : BinString → Nat → Request Value)
    (condition code : BinString) : Prop :=
  ∃ index, streamCode requests condition index = some code

/-- Distinct assigned codes are prefix-incomparable. -/
theorem assignedCodes_incomp {Value : Type*}
    {requests : BinString → Nat → Request Value}
    (budget : KraftBudget requests) {condition left right : BinString}
    (hleft : Assigned requests condition left)
    (hright : Assigned requests condition right) (hne : left ≠ right) :
    Incomp left right := by
  obtain ⟨leftIndex, hleftCode⟩ := hleft
  obtain ⟨rightIndex, hrightCode⟩ := hright
  rcases Nat.lt_trichotomy leftIndex rightIndex with hlt | heq | hgt
  · exact streamCode_incomp_of_lt budget hlt hleftCode hrightCode
  · subst rightIndex
    have : left = right := Option.some.inj (hleftCode.symm.trans hrightCode)
    exact absurd this hne
  · exact (streamCode_incomp_of_lt budget hgt hrightCode hleftCode).symm

/-! ## The induced conditional prefix machine -/

/-- Read the output belonging to an assigned code.  Injectivity of
`streamCode` makes the chosen witness index unique. -/
noncomputable def kcCompute
    (requests : BinString → Nat → Request BinString)
    (program condition : BinString) : Option BinString :=
  if h : Assigned requests condition program then
    some (requests condition (Nat.find h)).value
  else none

/-- The conditional prefix-free machine induced by a budgeted online request
stream. -/
noncomputable def kcMachine
    (requests : BinString → Nat → Request BinString)
    (budget : KraftBudget requests) : ConditionalPrefixFreeMachine where
  compute := kcCompute requests
  prefix_free := by
    intro condition left right hprefix hne hleftHalts
    by_cases hright : Assigned requests condition right
    · have hleft : Assigned requests condition left := by
        by_contra hnot
        simp [kcCompute, hnot] at hleftHalts
      have hinc := assignedCodes_incomp budget hleft hright hne
      exact False.elim (hinc.1 hprefix)
    · simp [kcCompute, hright]

/-- The machine evaluates each assigned code to the value of its originating
request, at exactly the assigned length. -/
theorem kcMachine_realizes_request
    {requests : BinString → Nat → Request BinString}
    (budget : KraftBudget requests) (condition : BinString) (index : Nat) :
    ∃ code, code.length = (requests condition index).requestedLength ∧
      (kcMachine requests budget).compute code condition =
        some (requests condition index).value := by
  obtain ⟨code, hcode, hlength⟩ :=
    streamCode_exists_length budget condition index
  have hassigned : Assigned requests condition code := ⟨index, hcode⟩
  have hfound := Nat.find_spec hassigned
  have hindex : Nat.find hassigned = index :=
    streamCode_index_injective budget hfound hcode
  refine ⟨code, hlength, ?_⟩
  simp only [kcMachine, kcCompute, dif_pos hassigned]
  rw [hindex]

/-- Kraft–Chaitin complexity theorem: every budgeted request is realized by a
conditional prefix program no longer than its requested length. -/
theorem kcMachine_complexity_le_requestedLength
    {requests : BinString → Nat → Request BinString}
    (budget : KraftBudget requests) (condition : BinString) (index : Nat) :
    Kc[kcMachine requests budget]((requests condition index).value | condition) ≤
      (requests condition index).requestedLength := by
  obtain ⟨code, hlength, hcompute⟩ :=
    kcMachine_realizes_request budget condition index
  rw [← hlength]
  exact conditionalComplexity_le_program_length
    (kcMachine requests budget) condition (requests condition index).value code hcompute

/-! ## Effective readback boundary -/

/-- One total search step: accept an index exactly when its assigned code is
the queried program, then return that request's value. -/
def kcSearchStep
    (requests : BinString → Nat → Request BinString)
    (program condition : BinString) (index : Nat) : Option BinString :=
  match streamCode requests condition index with
  | none => none
  | some code =>
      if code = program then some (requests condition index).value else none

theorem kcSearchStep_eq_some_iff
    {requests : BinString → Nat → Request BinString}
    {program condition output : BinString} {index : Nat} :
    kcSearchStep requests program condition index = some output ↔
      streamCode requests condition index = some program ∧
        (requests condition index).value = output := by
  unfold kcSearchStep
  cases hcode : streamCode requests condition index with
  | none => simp
  | some code =>
      by_cases hmatch : code = program
      · subst code
        simp
      · simp [hmatch]

/-- Partial readback by unbounded search for the request index assigned to a
program.  Unlike `kcCompute`, this exposes an operational search whose
computability can be proved from a concrete request enumerator. -/
noncomputable def kcSearchAlgorithm
    (requests : BinString → Nat → Request BinString)
    (program condition : BinString) : Part BinString :=
  Nat.rfindOpt (kcSearchStep requests program condition)

/-- Search readback returns exactly the value belonging to an assigned code. -/
theorem kcSearchAlgorithm_mem_iff
    {requests : BinString → Nat → Request BinString}
    (budget : KraftBudget requests)
    {program condition output : BinString} :
    output ∈ kcSearchAlgorithm requests program condition ↔
      ∃ index, streamCode requests condition index = some program ∧
        (requests condition index).value = output := by
  constructor
  · intro houtput
    obtain ⟨index, hstep⟩ := Nat.rfindOpt_spec houtput
    exact ⟨index, (kcSearchStep_eq_some_iff.mp hstep).1,
      (kcSearchStep_eq_some_iff.mp hstep).2⟩
  · rintro ⟨index, hcode, hvalue⟩
    have hstep : kcSearchStep requests program condition index = some output :=
      kcSearchStep_eq_some_iff.mpr ⟨hcode, hvalue⟩
    have hdom : (kcSearchAlgorithm requests program condition).Dom :=
      Nat.rfindOpt_dom.mpr ⟨index, output, by simpa using hstep⟩
    let found := (kcSearchAlgorithm requests program condition).get hdom
    have hfoundMem : found ∈ kcSearchAlgorithm requests program condition :=
      Part.get_mem hdom
    obtain ⟨foundIndex, hfoundStep⟩ := Nat.rfindOpt_spec hfoundMem
    have hfoundCode := (kcSearchStep_eq_some_iff.mp hfoundStep).1
    have hfoundValue := (kcSearchStep_eq_some_iff.mp hfoundStep).2
    have hindex : foundIndex = index :=
      streamCode_index_injective budget hfoundCode hcode
    have hfoundEq : found = output := by
      subst foundIndex
      exact hfoundValue.symm.trans hvalue
    simpa [hfoundEq] using hfoundMem

/-- The classical Option readback and the operational unbounded search denote
the same partial function. -/
theorem kcCompute_part_eq_search
    {requests : BinString → Nat → Request BinString}
    (budget : KraftBudget requests) (program condition : BinString) :
    Part.ofOption (kcCompute requests program condition) =
      kcSearchAlgorithm requests program condition := by
  apply Part.ext
  intro output
  rw [kcSearchAlgorithm_mem_iff budget]
  by_cases hassigned : Assigned requests condition program
  · have hfound := Nat.find_spec hassigned
    constructor
    · intro houtput
      have hvalue : (requests condition (Nat.find hassigned)).value = output := by
        have hvalue' : output =
            (requests condition (Nat.find hassigned)).value := by
          simpa [kcCompute, hassigned] using houtput
        exact hvalue'.symm
      exact ⟨Nat.find hassigned, hfound, hvalue⟩
    · rintro ⟨index, hcode, hvalue⟩
      have hindex : Nat.find hassigned = index :=
        streamCode_index_injective budget hfound hcode
      subst index
      simpa [kcCompute, hassigned] using hvalue.symm
  · constructor
    · simp [kcCompute, hassigned]
    · rintro ⟨index, hcode, _hvalue⟩
      exact (hassigned ⟨index, hcode⟩).elim

/-- The only remaining effectivity obligation for a concrete request stream is
that one bounded search step is computable.  Under that obligation, the
induced Kraft–Chaitin prefix machine is a partial-recursive two-input
algorithm. -/
theorem kcMachine_effective_of_searchStep
    {requests : BinString → Nat → Request BinString}
    (budget : KraftBudget requests)
    (hSearchStep : Computable₂ fun input : BinString × BinString => fun index =>
      kcSearchStep requests input.1 input.2 index) :
    Partrec₂ fun program condition =>
      Part.ofOption ((kcMachine requests budget).compute program condition) := by
  unfold Partrec₂
  have hSearch : Partrec fun input : BinString × BinString =>
      kcSearchAlgorithm requests input.1 input.2 :=
    Partrec.rfindOpt hSearchStep
  apply hSearch.of_eq
  intro input
  simpa [kcMachine] using
    (kcCompute_part_eq_search budget input.1 input.2).symm

/-! ## Positive and negative controls -/

/-- A nontrivial infinite request family with lengths `1, 2, 3, ...`.  Its
Kraft mass is the geometric series `1/2 + 1/4 + ...`. -/
def geometricRequests (_condition : BinString) (index : Nat) : Request BinString where
  value := binaryBits index
  requestedLength := index + 1

/-- Exact common-denominator mass of the first `count` geometric requests. -/
theorem geometricRequests_mass (condition : BinString) (count L : Nat)
    (hcount : count ≤ L) :
    ((requestedLengthsUpTo geometricRequests condition count).map
      (fun n => 2 ^ (L - n))).sum = 2 ^ L - 2 ^ (L - count) := by
  induction count with
  | zero => simp [requestedLengthsUpTo]
  | succ count ih =>
      simp only [requestedLengthsUpTo, geometricRequests, List.map_cons, List.sum_cons]
      rw [ih (by omega)]
      have hdouble :
          2 ^ (L - count) =
            2 ^ (L - (count + 1)) + 2 ^ (L - (count + 1)) := by
        have hexponent : L - count = L - (count + 1) + 1 := by omega
        rw [hexponent, pow_succ]
        ring
      have hsmall : 2 ^ (L - count) ≤ 2 ^ L :=
        Nat.pow_le_pow_right (by omega) (by omega)
      set A := 2 ^ (L - (count + 1)) with _hA
      set B := 2 ^ (L - count) with _hB
      set C := 2 ^ L with _hC
      clear_value A B C
      omega

/-- The geometric request family satisfies the online Kraft budget for every
condition and finite prefix. -/
theorem geometricRequests_kraftBudget : KraftBudget geometricRequests := by
  intro condition count L hlengths
  have hcount : count ≤ L := by
    cases count with
    | zero => omega
    | succ count =>
        exact hlengths (count + 1) (by
          simp [requestedLengthsUpTo, geometricRequests])
  rw [geometricRequests_mass condition count L hcount]
  exact Nat.sub_le _ _

/-- Positive control: the stream machine realizes the infinite geometric
family with `index + 1`-bit conditional programs. -/
theorem geometricRequests_complexity_bound (condition : BinString) (index : Nat) :
    Kc[kcMachine geometricRequests geometricRequests_kraftBudget](binaryBits index | condition) ≤
      index + 1 := by
  simpa [geometricRequests] using
    kcMachine_complexity_le_requestedLength
      geometricRequests_kraftBudget condition index

/-- A deliberately overfull request family: every request asks for a one-bit
codeword. -/
def constantOneRequests (_condition : BinString) (index : Nat) : Request BinString where
  value := binaryBits index
  requestedLength := 1

/-- Negative control: three distinct one-bit requests exceed binary Kraft
capacity, so the universal stream budget correctly rejects this family. -/
theorem constantOneRequests_not_kraftBudget : ¬ KraftBudget constantOneRequests := by
  intro budget
  have h := budget [] 3 1 (by
    norm_num [requestedLengthsUpTo, constantOneRequests])
  norm_num [requestedLengthsUpTo, constantOneRequests] at h

#print axioms streamState_spec
#print axioms streamCode_incomp_of_lt
#print axioms kcMachine_complexity_le_requestedLength
#print axioms kcMachine_effective_of_searchStep
#print axioms geometricRequests_complexity_bound
#print axioms constantOneRequests_not_kraftBudget

end KraftChaitin

end KolmogorovComplexity
