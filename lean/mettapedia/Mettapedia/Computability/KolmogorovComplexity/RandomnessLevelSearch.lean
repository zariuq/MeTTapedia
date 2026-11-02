import Mettapedia.Computability.KolmogorovComplexity.FeatureRandomness

/-!
# Stable effective enumeration of finite randomness-test levels

A bounded stage dovetails approximation time, a fixed-length source index
and evaluator fuel. Newly discovered strings are appended exactly once.
Published indices never change when an earlier-in-lexicographic-order string
is discovered later. The decoder searches for its fixed index, not for the
final sorted level set, whose completion is generally undecidable.
-/

set_option autoImplicit false

namespace KolmogorovComplexity.FeatureTheory.Randomness

open Mettapedia.UniversalAI.TimeBoundedAIXI
open FiniteBitStrings
open scoped Classical

def encodedApproximation (approximation : Nat → BinString → Nat) : Nat →. Nat :=
  fun input => (Part.ofOption (Encodable.decode (α := Nat × BinString) input)).map
    (fun fields => approximation fields.1 fields.2)

theorem exists_approximation_code {approximation : Nat → BinString → Nat}
    (effective : Computable₂ approximation) :
    ∃ code : Nat.Partrec.Code, Nat.Partrec.Code.eval code = encodedApproximation approximation :=
  Nat.Partrec.Code.exists_code.mp (by
    change Nat.Partrec (fun input =>
      (Part.ofOption (Encodable.decode (α := Nat × BinString) input)).bind
        (fun fields => (Part.some (approximation fields.1 fields.2)).map Encodable.encode)) at effective
    exact effective.of_eq (fun input => by
      cases decoded : Encodable.decode (α := Nat × BinString) input <;> simp [encodedApproximation, decoded]))

theorem lower_approximation_le {value : BinString → Nat} {approximation : Nat → BinString → Nat}
    (monotone : ∀ source, Monotone (fun stage => approximation stage source))
    (settles : ∀ source, ∃ settled, ∀ stage, settled ≤ stage → approximation stage source = value source)
    (stage : Nat) (source : BinString) : approximation stage source ≤ value source := by
  obtain ⟨settled, stable⟩ := settles source
  have bound := monotone source (le_max_left stage settled)
  change approximation stage source ≤ approximation (max stage settled) source at bound
  rw [stable (max stage settled) (le_max_right _ _)] at bound
  exact bound

abbrev LevelInput := Nat × Nat

def levelCandidate (code : Nat.Partrec.Code) (input : LevelInput) (rank : Nat) : Option BinString :=
  ((bitstringsOfLength input.1)[rank.unpair.2.unpair.1]?).bind fun source =>
    (Nat.Partrec.Code.evaln rank.unpair.2.unpair.2 code (Encodable.encode (rank.unpair.1, source))).bind fun value =>
      if input.2 ≤ value then some source else none

theorem levelCandidate_primrec (code : Nat.Partrec.Code) : Primrec₂ (levelCandidate code) := by
  have rank : Primrec fun input : LevelInput × Nat => input.2 := Primrec.snd
  have stage : Primrec fun input : LevelInput × Nat => input.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp rank)
  have tail : Primrec fun input : LevelInput × Nat => input.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp rank)
  have index : Primrec fun input : LevelInput × Nat => input.2.unpair.2.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp tail)
  have fuel : Primrec fun input : LevelInput × Nat => input.2.unpair.2.unpair.2 :=
    Primrec.snd.comp (Primrec.unpair.comp tail)
  have selected : Primrec fun input : LevelInput × Nat =>
      (bitstringsOfLength input.1.1)[input.2.unpair.2.unpair.1]? :=
    Primrec.list_getElem?.comp (bitstringsOfLength_primrec.comp (Primrec.fst.comp Primrec.fst)) index
  have evaluation : Primrec fun input : (LevelInput × Nat) × BinString =>
      Nat.Partrec.Code.evaln input.1.2.unpair.2.unpair.2 code (Encodable.encode (input.1.2.unpair.1, input.2)) :=
    Nat.Partrec.Code.primrec_evaln.comp
      (((fuel.comp Primrec.fst).pair (Primrec.const code)).pair
        (Primrec.encode.comp ((stage.comp Primrec.fst).pair Primrec.snd)))
  have publish : Primrec₂ fun (input : (LevelInput × Nat) × BinString) (value : Nat) =>
      if input.1.1.2 ≤ value then some input.2 else none :=
    (Primrec.ite
      (Primrec.nat_le.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd)
      (Primrec.option_some.comp (Primrec.snd.comp Primrec.fst)) (Primrec.const none)).to₂
  exact (Primrec.option_bind selected (Primrec.option_bind evaluation publish).to₂).to₂

theorem levelCandidate_sound {value : BinString → Nat} {approximation : Nat → BinString → Nat}
    {code : Nat.Partrec.Code} (codeSpec : Nat.Partrec.Code.eval code = encodedApproximation approximation)
    (below : ∀ stage source, approximation stage source ≤ value source)
    {input : LevelInput} {rank : Nat} {source : BinString}
    (found : levelCandidate code input rank = some source) : source ∈ level value input.1 input.2 := by
  unfold levelCandidate at found
  obtain ⟨selected, selectedAt, computed⟩ := Option.bind_eq_some_iff.mp found
  obtain ⟨amount, evaluated, checked⟩ := Option.bind_eq_some_iff.mp computed
  split_ifs at checked with high
  · cases Option.some.inj checked
    have member : source ∈ bitstringsOfLength input.1 := List.mem_of_getElem? selectedAt
    have runs := Nat.Partrec.Code.evaln_sound (show amount ∈
      Nat.Partrec.Code.evaln rank.unpair.2.unpair.2 code (Encodable.encode (rank.unpair.1, source)) from
        by simpa only [Option.mem_def] using evaluated)
    rw [codeSpec] at runs
    have actual : amount = approximation rank.unpair.1 source := by simpa [encodedApproximation] using runs
    exact (mem_level _ _ _ _).mpr ⟨length_eq_of_mem_bitstringsOfLength member, by
      rw [actual] at high
      exact high.trans (below _ _)⟩

theorem levelCandidate_complete {value : BinString → Nat} {approximation : Nat → BinString → Nat}
    {code : Nat.Partrec.Code} (codeSpec : Nat.Partrec.Code.eval code = encodedApproximation approximation)
    (settles : ∀ source, ∃ settled, ∀ stage, settled ≤ stage → approximation stage source = value source)
    {input : LevelInput} {source : BinString} (member : source ∈ level value input.1 input.2) :
    ∃ rank, levelCandidate code input rank = some source := by
  obtain ⟨sameLength, high⟩ := (mem_level _ _ _ _).mp member
  obtain ⟨stage, stable⟩ := settles source
  have actual : approximation stage source = value source := stable stage le_rfl
  have runs : value source ∈ Nat.Partrec.Code.eval code (Encodable.encode (stage, source)) := by
    rw [codeSpec]
    simp [encodedApproximation, actual]
  obtain ⟨fuel, computes⟩ := Nat.Partrec.Code.evaln_complete.mp runs
  have sourceMember : source ∈ bitstringsOfLength input.1 := sameLength ▸ mem_bitstringsOfLength_self source
  let index := (bitstringsOfLength input.1).idxOf source
  have selected : (bitstringsOfLength input.1)[index]? = some source := by
    exact List.getElem?_eq_some_iff.mpr ⟨List.idxOf_lt_length_of_mem sourceMember,
      List.getElem_idxOf (List.idxOf_lt_length_of_mem sourceMember)⟩
  refine ⟨Nat.pair stage (Nat.pair index fuel), ?_⟩
  simp only [levelCandidate, Nat.unpair_pair, selected, Option.bind_some, Option.mem_def.mp computes, if_pos high]

def appendNew (previous : List BinString) : Option BinString → List BinString
  | none => previous
  | some source => if source ∈ previous then previous else previous ++ [source]

theorem appendNew_primrec : Primrec₂ appendNew := by
  have membership : PrimrecRel fun (rows : List BinString) (source : BinString) => source ∈ rows := by
    simpa using PrimrecRel.exists_mem_list (show PrimrecRel (fun first second : BinString => first = second) from Primrec.eq)
  have fresh : Primrec₂ fun (input : List BinString × Option BinString) (source : BinString) =>
      if source ∈ input.1 then input.1 else input.1 ++ [source] :=
    (Primrec.ite
      (membership.comp (Primrec.fst.comp Primrec.fst) Primrec.snd)
      (Primrec.fst.comp Primrec.fst)
      (Primrec.list_append.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.list_cons.comp Primrec.snd (Primrec.const [])))).to₂
  exact (Primrec.option_casesOn Primrec.snd Primrec.fst fresh).to₂.of_eq
    (fun previous candidate => by cases candidate <;> rfl)

theorem appendNew_prefix (previous : List BinString) (candidate : Option BinString) : previous <+: appendNew previous candidate := by
  cases candidate with
  | none => exact ⟨[], by simp [appendNew]⟩
  | some source =>
      by_cases present : source ∈ previous
      · exact ⟨[], by simp [appendNew, present]⟩
      · exact ⟨[source], by simp [appendNew, present]⟩

theorem mem_appendNew (previous : List BinString) (candidate : Option BinString) (source : BinString) :
    source ∈ appendNew previous candidate ↔ source ∈ previous ∨ candidate = some source := by
  cases candidate with
  | none => simp [appendNew]
  | some item =>
      by_cases present : item ∈ previous
      · simp only [appendNew, if_pos present, Option.some.injEq]
        constructor
        · exact Or.inl
        · rintro (member | rfl)
          · exact member
          · exact present
      · simp [appendNew, present, eq_comm]

theorem appendNew_nodup (previous : List BinString) (unique : previous.Nodup) (candidate : Option BinString) :
    (appendNew previous candidate).Nodup := by
  cases candidate with
  | none => exact unique
  | some source =>
      by_cases present : source ∈ previous
      · simpa only [appendNew, if_pos present] using unique
      · simp only [appendNew, if_neg present, List.nodup_append, unique, List.nodup_singleton, true_and]
        intro item member other otherMember same
        have otherEq : other = source := List.mem_singleton.mp otherMember
        rw [otherEq] at same
        exact present (same ▸ member)

def discovered (code : Nat.Partrec.Code) (input : LevelInput) : Nat → List BinString
  | 0 => []
  | stage + 1 => appendNew (discovered code input stage) (levelCandidate code input stage)

theorem discovered_primrec (code : Nat.Partrec.Code) : Primrec₂ (discovered code) := by
  have step : Primrec₂ fun (input : LevelInput) (state : Nat × List BinString) =>
      appendNew state.2 (levelCandidate code input state.1) :=
    (appendNew_primrec.comp (Primrec.snd.comp Primrec.snd)
      ((levelCandidate_primrec code).comp Primrec.fst (Primrec.fst.comp Primrec.snd))).to₂
  exact (Primrec.nat_rec (Primrec.const []) step).of_eq (by
    intro input stage
    induction stage with
    | zero => rfl
    | succ stage ih => simp [discovered, ih])

theorem discovered_nodup (code : Nat.Partrec.Code) (input : LevelInput) (stage : Nat) :
    (discovered code input stage).Nodup := by
  induction stage with
  | zero => simp [discovered]
  | succ stage ih => exact appendNew_nodup _ ih _

theorem discovered_prefix (code : Nat.Partrec.Code) (input : LevelInput) {before after : Nat} (later : before ≤ after) :
    discovered code input before <+: discovered code input after := by
  induction later with
  | refl => exact ⟨[], by simp⟩
  | @step after _ ih => exact ih.trans (appendNew_prefix _ _)

theorem discovered_get_mono (code : Nat.Partrec.Code) (input : LevelInput) {before after index : Nat} {source : BinString}
    (later : before ≤ after) (found : (discovered code input before)[index]? = some source) :
    (discovered code input after)[index]? = some source := by
  obtain ⟨suffix, same⟩ := discovered_prefix code input later
  rw [← same, List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).choose]
  exact found

theorem discovered_sound {value : BinString → Nat} {approximation : Nat → BinString → Nat}
    {code : Nat.Partrec.Code} (codeSpec : Nat.Partrec.Code.eval code = encodedApproximation approximation)
    (below : ∀ stage source, approximation stage source ≤ value source)
    (input : LevelInput) (stage : Nat) :
    ∀ source ∈ discovered code input stage, source ∈ level value input.1 input.2 := by
  induction stage with
  | zero => simp [discovered]
  | succ stage ih =>
      intro source member
      rcases (mem_appendNew _ _ _).mp member with earlier | current
      · exact ih source earlier
      · exact levelCandidate_sound codeSpec below current

theorem discovered_complete {value : BinString → Nat} {approximation : Nat → BinString → Nat}
    {code : Nat.Partrec.Code} (codeSpec : Nat.Partrec.Code.eval code = encodedApproximation approximation)
    (settles : ∀ source, ∃ settled, ∀ stage, settled ≤ stage → approximation stage source = value source)
    {input : LevelInput} {source : BinString} (member : source ∈ level value input.1 input.2) :
    ∃ stage, source ∈ discovered code input stage := by
  obtain ⟨rank, found⟩ := levelCandidate_complete codeSpec settles member
  exact ⟨rank + 1, (mem_appendNew _ _ _).mpr (Or.inr found)⟩

def decodeLevel (code : Nat.Partrec.Code) (threshold : Nat) (residual : BinString) : Part BinString :=
  Nat.rfindOpt fun stage => (discovered code (threshold + residual.length, threshold) stage)[fixedRank residual]?

theorem decodeLevel_partrec (code : Nat.Partrec.Code) : Partrec₂ (decodeLevel code) := by
  have observed : Primrec₂ fun (input : Nat × BinString) (stage : Nat) =>
      (discovered code (input.1 + input.2.length, input.1) stage)[fixedRank input.2]? := by
    have parameters : Primrec fun input : (Nat × BinString) × Nat => (input.1.1 + input.1.2.length, input.1.1) :=
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.list_length.comp (Primrec.snd.comp Primrec.fst))).pair (Primrec.fst.comp Primrec.fst)
    exact (Primrec.list_getElem?.comp
      ((discovered_primrec code).comp parameters Primrec.snd)
      (fixedRank_primrec.comp (Primrec.snd.comp Primrec.fst))).to₂
  exact Partrec.rfindOpt observed.to_comp

theorem decodeLevel_of_get (code : Nat.Partrec.Code) (threshold : Nat) (residual source : BinString) (stage : Nat)
    (found : (discovered code (threshold + residual.length, threshold) stage)[fixedRank residual]? = some source) :
    source ∈ decodeLevel code threshold residual := by
  exact (Nat.rfindOpt_mono (fun {_source _before _after} later selected =>
    Option.mem_def.mpr (discovered_get_mono code _ later (Option.mem_def.mp selected)))).mpr
      ⟨stage, Option.mem_def.mpr found⟩

theorem decodeLevel_complete {value : BinString → Nat} {approximation : Nat → BinString → Nat}
    {code : Nat.Partrec.Code} (codeSpec : Nat.Partrec.Code.eval code = encodedApproximation approximation)
    (below : ∀ stage source, approximation stage source ≤ value source)
    (settles : ∀ source, ∃ settled, ∀ stage, settled ≤ stage → approximation stage source = value source)
    (test : UniformTest value) (source : BinString) (threshold : Nat) (high : threshold ≤ value source) :
    ∃ residual : BinString, residual.length = source.length - threshold ∧ source ∈ decodeLevel code threshold residual := by
  let input : LevelInput := (source.length, threshold)
  have member : source ∈ level value input.1 input.2 := (mem_level _ _ _ _).mpr ⟨rfl, high⟩
  obtain ⟨stage, seen⟩ := discovered_complete codeSpec settles member
  let index := (discovered code input stage).idxOf source
  have inBounds : index < (discovered code input stage).length := List.idxOf_lt_length_of_mem seen
  have count : (discovered code input stage).length ≤ (level value source.length threshold).card := by
    rw [← List.toFinset_card_of_nodup (discovered_nodup code input stage)]
    exact Finset.card_le_card (by
      intro item present
      exact discovered_sound codeSpec below input stage item (List.mem_toFinset.mp present))
  have small : index < 2 ^ (source.length - threshold) := inBounds.trans_le (count.trans (test.unscaled_bound _ _))
  obtain ⟨residual, width, sameIndex⟩ := fixedRank_surjective (source.length - threshold) index small
  have sourceLength := test.length_ge_of_high source threshold high
  have sameLength : threshold + residual.length = source.length := by omega
  refine ⟨residual, width, ?_⟩
  apply decodeLevel_of_get code threshold residual source stage
  simpa only [sameLength, sameIndex, input] using
    (List.getElem?_eq_some_iff.mpr ⟨inBounds, List.getElem_idxOf inBounds⟩ :
      (discovered code input stage)[index]? = some source)

def levelResidualAt (code : Nat.Partrec.Code) (input : Nat × BinString) (stage : Nat) : Option BinString :=
  let words := discovered code (input.2.length, input.1) stage
  if input.2 ∈ words then (bitstringsOfLength (input.2.length - input.1))[words.idxOf input.2]? else none

theorem levelResidualAt_primrec (code : Nat.Partrec.Code) : Primrec₂ (levelResidualAt code) := by
  have source : Primrec fun input : (Nat × BinString) × Nat => input.1.2 := Primrec.snd.comp Primrec.fst
  have threshold : Primrec fun input : (Nat × BinString) × Nat => input.1.1 := Primrec.fst.comp Primrec.fst
  have words : Primrec fun input : (Nat × BinString) × Nat => discovered code (input.1.2.length, input.1.1) input.2 :=
    (discovered_primrec code).comp ((Primrec.list_length.comp source).pair threshold) Primrec.snd
  have membership : PrimrecRel fun (rows : List BinString) (source : BinString) => source ∈ rows := by
    simpa using PrimrecRel.exists_mem_list (show PrimrecRel (fun first second : BinString => first = second) from Primrec.eq)
  have output : Primrec fun input : (Nat × BinString) × Nat =>
      (bitstringsOfLength (input.1.2.length - input.1.1))[(discovered code (input.1.2.length, input.1.1) input.2).idxOf input.1.2]? :=
    Primrec.list_getElem?.comp
      (bitstringsOfLength_primrec.comp (Primrec.nat_sub.comp (Primrec.list_length.comp source) threshold))
      (wordIndex_primrec.comp source words)
  exact (Primrec.ite (membership.comp words source) output (Primrec.const none)).to₂

def encodeLevel (code : Nat.Partrec.Code) (threshold : Nat) (source : BinString) : Part BinString :=
  Nat.rfindOpt fun stage => levelResidualAt code (threshold, source) stage

theorem encodeLevel_partrec (code : Nat.Partrec.Code) : Partrec₂ (encodeLevel code) :=
  Partrec.rfindOpt (levelResidualAt_primrec code).to_comp

theorem encodeLevel_sound (code : Nat.Partrec.Code) (threshold : Nat) (source residual : BinString)
    (withinLength : threshold ≤ source.length) (produces : residual ∈ encodeLevel code threshold source) :
    residual.length = source.length - threshold ∧ source ∈ decodeLevel code threshold residual := by
  obtain ⟨stage, found⟩ := Nat.rfindOpt_spec produces
  have found' := Option.mem_def.mp found
  unfold levelResidualAt at found'
  dsimp only at found'
  split_ifs at found' with present
  · obtain ⟨width, sameIndex⟩ := fixedRank_of_get found'
    refine ⟨width, ?_⟩
    apply decodeLevel_of_get code threshold residual source stage
    have sum : threshold + residual.length = source.length := by omega
    rw [sum, sameIndex]
    exact List.getElem?_eq_some_iff.mpr ⟨List.idxOf_lt_length_of_mem present,
      List.getElem_idxOf (List.idxOf_lt_length_of_mem present)⟩

theorem encodeLevel_complete {value : BinString → Nat} {approximation : Nat → BinString → Nat}
    {code : Nat.Partrec.Code} (codeSpec : Nat.Partrec.Code.eval code = encodedApproximation approximation)
    (below : ∀ stage source, approximation stage source ≤ value source)
    (settles : ∀ source, ∃ settled, ∀ stage, settled ≤ stage → approximation stage source = value source)
    (test : UniformTest value) (source : BinString) (threshold : Nat) (high : threshold ≤ value source) :
    ∃ residual, residual ∈ encodeLevel code threshold source := by
  let input : LevelInput := (source.length, threshold)
  have member : source ∈ level value input.1 input.2 := (mem_level _ _ _ _).mpr ⟨rfl, high⟩
  obtain ⟨stage, seen⟩ := discovered_complete codeSpec settles member
  have count : (discovered code input stage).length ≤ (level value source.length threshold).card := by
    rw [← List.toFinset_card_of_nodup (discovered_nodup code input stage)]
    exact Finset.card_le_card (by
      intro item present
      exact discovered_sound codeSpec below input stage item (List.mem_toFinset.mp present))
  have index : (discovered code input stage).idxOf source < (bitstringsOfLength (source.length - threshold)).length := by
    rw [bitstringsOfLength_length]
    exact (List.idxOf_lt_length_of_mem seen).trans_le (count.trans (test.unscaled_bound _ _))
  let residual := (bitstringsOfLength (source.length - threshold))[(discovered code input stage).idxOf source]
  apply Part.dom_iff_mem.mp
  apply Nat.rfindOpt_dom.mpr
  refine ⟨stage, residual, ?_⟩
  have output : levelResidualAt code (threshold, source) stage = some residual := by
    simp only [levelResidualAt, input, if_pos seen]
    exact List.getElem?_eq_some_iff.mpr ⟨index, rfl⟩
  exact Option.mem_def.mpr output

end KolmogorovComplexity.FeatureTheory.Randomness
