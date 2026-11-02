import Mettapedia.Computability.KolmogorovComplexity.FeatureSchemeCodec
import Mettapedia.Computability.KolmogorovComplexity.FeatureResidualSearch
import Mettapedia.Computability.KolmogorovComplexity.FeatureRationalScheme
import Mettapedia.Algorithms.Compression.FairSearch

/-!
# Global effective search over competing autoencoder compositions

Franz, Antonenko and Soletskyi, "A theory of incremental compression",
Information Sciences 547 (2021), Section 4, doi:10.1016/j.ins.2020.08.035.

Every residual retains an enumerator of all descriptive/feature program pairs.
Trials use the shared effective conditional interpreter, retain an extracted
residual while testing reconstruction, and spawn another enumerator only after
both computations and strict shortening have succeeded. Failed and indefinitely
running trials coexist with later trials and deeper searches.

The operational scheduler is the proved eight-turn cost/age queue. This module
does not identify that policy with the paper's dyadic phases. In particular,
`Code.evaln` is a bounded evaluator stage, not a count of Turing-machine steps;
no paper running-time bound follows from the stage count below.
-/

set_option autoImplicit false

namespace KolmogorovComplexity.FeatureTheory.GlobalSearch

open Mettapedia.Algorithms.Compression

def evaluate (code : Nat.Partrec.Code) (program condition : BinString) (stage : Nat) : Option BinString :=
  (Nat.Partrec.Code.evaln stage code (Encodable.encode (program, condition))).bind Encodable.decode

theorem evaluate_mono (code : Nat.Partrec.Code) (program condition : BinString)
    {first second : Nat} (later : first ≤ second) {output : BinString}
    (found : evaluate code program condition first = some output) :
    evaluate code program condition second = some output := by
  unfold evaluate at found ⊢
  obtain ⟨raw, computed, decoded⟩ := Option.bind_eq_some_iff.mp found
  have persists := Nat.Partrec.Code.evaln_mono later (show raw ∈
    Nat.Partrec.Code.evaln first code (Encodable.encode (program, condition)) from computed)
  rw [show Nat.Partrec.Code.evaln second code (Encodable.encode (program, condition)) = some raw from persists]
  exact decoded

theorem evaluate_sound {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U)
    {program condition output : BinString} {stage : Nat}
    (found : evaluate code program condition stage = some output) : output ∈ U program condition := by
  unfold evaluate at found
  obtain ⟨raw, computed, decoded⟩ := Option.bind_eq_some_iff.mp found
  have runs := Nat.Partrec.Code.evaln_sound (show raw ∈
    Nat.Partrec.Code.evaln stage code (Encodable.encode (program, condition)) from computed)
  rw [codeSpec] at runs
  have mapped : raw ∈ (U program condition).map Encodable.encode := by
    simpa [encodedConditionalAlgorithm] using runs
  obtain ⟨value, computes, same⟩ := (Part.mem_map_iff Encodable.encode).mp mapped
  have equal : value = output := by
    simpa only [← same, Encodable.encodek, Option.some.injEq] using decoded
  simpa only [equal] using computes

theorem evaluate_complete {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U)
    {program condition output : BinString} (runs : output ∈ U program condition) :
    ∃ stage, evaluate code program condition stage = some output := by
  have computed : Encodable.encode output ∈ Nat.Partrec.Code.eval code (Encodable.encode (program, condition)) := by
    rw [codeSpec]
    simpa [encodedConditionalAlgorithm] using Part.mem_map Encodable.encode runs
  obtain ⟨stage, bounded⟩ := Nat.Partrec.Code.evaln_complete.mp computed
  refine ⟨stage, ?_⟩
  simp only [evaluate, show Nat.Partrec.Code.evaln stage code (Encodable.encode (program, condition)) =
    some (Encodable.encode output) from bounded, Option.bind_some, Encodable.encodek]

structure Frame where
  residual : BinString
  features : List BinString
  deriving DecidableEq, Repr

def Frame.root (source : BinString) : Frame := ⟨source, []⟩

def Frame.extend (frame : Frame) (feature residual : BinString) : Frame :=
  ⟨residual, frame.features ++ [feature]⟩

def Frame.description (frame : Frame) : BinString := schemeDescription frame.features frame.residual

def Frame.Valid (U : ConditionalAlgorithm) (source : BinString) (frame : Frame) : Prop :=
  source ∈ runStoredFeatures U (frame.features.reverse, frame.residual) ∧
    (frame.features.map List.length).sum + frame.residual.length + frame.features.length ≤ source.length

theorem root_valid (U : ConditionalAlgorithm) (source : BinString) : (Frame.root source).Valid U source := by
  exact ⟨runStoredFeatures_nil U source, by simp [Frame.root]⟩

theorem extend_valid {U : ConditionalAlgorithm} {source : BinString} {frame : Frame}
    (valid : frame.Valid U source) {feature residual : BinString}
    (reconstructs : frame.residual ∈ U feature residual)
    (shorter : feature.length + residual.length < frame.residual.length) :
    (frame.extend feature residual).Valid U source := by
  constructor
  · simpa [Frame.extend] using runStoredFeatures_cons reconstructs valid.1
  · have before := valid.2
    simp only [Frame.extend, List.map_append, List.map_singleton, List.sum_append,
      List.sum_singleton, List.length_append, List.length_singleton]
    omega

theorem valid_description {U : ConditionalAlgorithm} {source : BinString} {frame : Frame}
    (valid : frame.Valid U source) : source ∈ schemeInterpreter U frame.description [] :=
  (schemeInterpreter_encode_iff U frame.features frame.residual [] source).mpr valid.1

theorem valid_depth {U : ConditionalAlgorithm} {source : BinString} {frame : Frame}
    (valid : frame.Valid U source) : frame.features.length ≤ source.length := by
  have bounded := valid.2
  omega

inductive Node where
  | enumerate (frame : Frame) (rank : Nat)
  | extract (frame : Frame) (descriptive feature : BinString) (stage : Nat)
  | rebuild (frame : Frame) (descriptive feature residual : BinString) (stage : Nat)
  | found (frame : Frame) (descriptive feature residual : BinString)
  deriving DecidableEq, Repr

def successors (code : Nat.Partrec.Code) : Node → List Node
  | .enumerate frame rank =>
      .enumerate frame (rank + 1) ::
        ((Encodable.decode (α := BinString × BinString) rank).map
          fun pair => Node.extract frame pair.1 pair.2 0).toList
  | .extract frame descriptive feature stage =>
      match evaluate code descriptive frame.residual stage with
      | none => [.extract frame descriptive feature (stage + 1)]
      | some residual =>
          if feature.length + residual.length < frame.residual.length then
            [.rebuild frame descriptive feature residual 0] else []
  | .rebuild frame descriptive feature residual stage =>
      match evaluate code feature residual stage with
      | none => [.rebuild frame descriptive feature residual (stage + 1)]
      | some output => if output = frame.residual then [.found frame descriptive feature residual] else []
  | .found frame _descriptive feature residual => [.enumerate (frame.extend feature residual) 0]

def emit : Node → Option Frame
  | .found frame _descriptive feature residual => some (frame.extend feature residual)
  | _ => none

def priority : Node → Nat
  | .enumerate frame rank => frame.features.length + rank
  | .extract frame descriptive feature _stage
  | .rebuild frame descriptive feature _residual _stage
  | .found frame descriptive feature _residual =>
      frame.features.length + descriptive.length + feature.length

def Legal (U : ConditionalAlgorithm) (source : BinString) : Node → Prop
  | .enumerate frame _rank | .extract frame _descriptive _feature _stage => frame.Valid U source
  | .rebuild frame descriptive feature residual _stage =>
      frame.Valid U source ∧ residual ∈ U descriptive frame.residual ∧
        feature.length + residual.length < frame.residual.length
  | .found frame descriptive feature residual =>
      frame.Valid U source ∧ residual ∈ U descriptive frame.residual ∧
        frame.residual ∈ U feature residual ∧ feature.length + residual.length < frame.residual.length

theorem successor_legal {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U)
    {source : BinString} {node next : Node} (legal : Legal U source node)
    (member : next ∈ successors code node) : Legal U source next := by
  cases node with
  | enumerate frame rank =>
      cases decoded : Encodable.decode (α := BinString × BinString) rank with
      | none =>
          simp [successors, decoded] at member
          subst next
          exact legal
      | some pair =>
          simp [successors, decoded] at member
          rcases member with rfl | rfl <;> exact legal
  | extract frame descriptive feature stage =>
      cases result : evaluate code descriptive frame.residual stage with
      | none => simp only [successors, result, List.mem_singleton] at member; subst next; exact legal
      | some residual =>
          by_cases shorter : feature.length + residual.length < frame.residual.length
          · simp only [successors, result, if_pos shorter, List.mem_singleton] at member
            subst next
            exact ⟨legal, evaluate_sound codeSpec result, shorter⟩
          · simp [successors, result, shorter] at member
  | rebuild frame descriptive feature residual stage =>
      cases result : evaluate code feature residual stage with
      | none => simp only [successors, result, List.mem_singleton] at member; subst next; exact legal
      | some output =>
          by_cases same : output = frame.residual
          · simp only [successors, result, if_pos same, List.mem_singleton] at member
            subst next
            exact ⟨legal.1, legal.2.1, same ▸ evaluate_sound codeSpec result, legal.2.2⟩
          · simp [successors, result, same] at member
  | found frame descriptive feature residual =>
      simp only [successors, List.mem_singleton] at member
      subst next
      exact extend_valid legal.1 legal.2.2.1 legal.2.2.2

abbrev Reaches (code : Nat.Partrec.Code) :=
  Relation.ReflTransGen (fun node next => next ∈ successors code node)

theorem reaches_legal {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U)
    {source : BinString} {node next : Node} (legal : Legal U source node)
    (path : Reaches code node next) : Legal U source next := by
  induction path with
  | refl => exact legal
  | tail _ member ih => exact successor_legal codeSpec ih member

theorem emitted_description_sound {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U)
    (source : BinString) {node : Node} (path : Reaches code (.enumerate (.root source) 0) node)
    {frame : Frame} (emitted : emit node = some frame) :
    source ∈ schemeInterpreter U frame.description [] := by
  have rootLegal : Legal U source (.enumerate (.root source) 0) := root_valid U source
  have legal := reaches_legal codeSpec rootLegal path
  cases node with
  | enumerate => simp [emit] at emitted
  | extract => simp [emit] at emitted
  | rebuild => simp [emit] at emitted
  | found previous descriptive feature residual =>
      cases Option.some.inj emitted
      exact valid_description (extend_valid legal.1 legal.2.2.1 legal.2.2.2)

theorem enumerate_reaches (code : Nat.Partrec.Code) (frame : Frame) (rank : Nat) :
    Reaches code (.enumerate frame 0) (.enumerate frame rank) := by
  induction rank with
  | zero => exact .refl
  | succ rank ih => exact ih.tail (by simp [successors])

theorem enumerate_reaches_pair (code : Nat.Partrec.Code) (frame : Frame)
    (descriptive feature : BinString) :
    Reaches code (.enumerate frame 0) (.extract frame descriptive feature 0) := by
  exact (enumerate_reaches code frame (Encodable.encode (descriptive, feature))).tail
    (by simp [successors])

theorem extract_reaches_result (code : Nat.Partrec.Code) (frame : Frame)
    (descriptive feature residual : BinString) (stage extra : Nat)
    (found : evaluate code descriptive frame.residual (stage + extra) = some residual)
    (shorter : feature.length + residual.length < frame.residual.length) :
    Reaches code (.extract frame descriptive feature stage) (.rebuild frame descriptive feature residual 0) := by
  induction extra generalizing stage with
  | zero =>
      have current : evaluate code descriptive frame.residual stage = some residual := by simpa using found
      exact .single (by simp [successors, current, shorter])
  | succ extra ih =>
      cases current : evaluate code descriptive frame.residual stage with
      | none =>
          have first : Reaches code (.extract frame descriptive feature stage)
              (.extract frame descriptive feature (stage + 1)) := .single (by simp [successors, current])
          exact first.trans (ih (stage + 1) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using found))
      | some earlier =>
          have persists := evaluate_mono code descriptive frame.residual (Nat.le_add_right stage (extra + 1)) current
          have equal := Option.some.inj (persists.symm.trans found)
          subst earlier
          exact .single (by simp [successors, current, shorter])

theorem rebuild_reaches_result (code : Nat.Partrec.Code) (frame : Frame)
    (descriptive feature residual : BinString) (stage extra : Nat)
    (found : evaluate code feature residual (stage + extra) = some frame.residual) :
    Reaches code (.rebuild frame descriptive feature residual stage) (.found frame descriptive feature residual) := by
  induction extra generalizing stage with
  | zero =>
      have current : evaluate code feature residual stage = some frame.residual := by simpa using found
      exact .single (by simp [successors, current])
  | succ extra ih =>
      cases current : evaluate code feature residual stage with
      | none =>
          have first : Reaches code (.rebuild frame descriptive feature residual stage)
              (.rebuild frame descriptive feature residual (stage + 1)) := .single (by simp [successors, current])
          exact first.trans (ih (stage + 1) (by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using found))
      | some earlier =>
          have persists := evaluate_mono code feature residual (Nat.le_add_right stage (extra + 1)) current
          have equal := Option.some.inj (persists.symm.trans found)
          subst earlier
          exact .single (by simp [successors, current])

theorem step_reaches_emission {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U)
    (frame : Frame) (step : CompressionStep U frame.residual) :
    Reaches code (.enumerate frame 0)
      (.found frame step.descriptiveProgram step.featureProgram step.residual) := by
  obtain ⟨mapStage, mapFound⟩ := evaluate_complete codeSpec step.extracts
  obtain ⟨featureStage, featureFound⟩ := evaluate_complete codeSpec step.reconstructs
  exact (enumerate_reaches_pair code frame step.descriptiveProgram step.featureProgram).trans
    ((extract_reaches_result code frame step.descriptiveProgram step.featureProgram step.residual
      0 mapStage (by simpa using mapFound) step.compresses).trans
        (rebuild_reaches_result code frame step.descriptiveProgram step.featureProgram step.residual
          0 featureStage (by simpa using featureFound)))

theorem step_reaches_child {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U)
    (frame : Frame) (step : CompressionStep U frame.residual) :
    Reaches code (.enumerate frame 0) (.enumerate (frame.extend step.featureProgram step.residual) 0) :=
  (step_reaches_emission codeSpec frame step).tail (by simp [successors])

theorem bChain_reaches_child {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U)
    {factor : ℝ} {source final : BinString} {features : List BinString}
    (chain : BChain U factor source features final) (accumulated : List BinString) :
    Reaches code (.enumerate ⟨source, accumulated⟩ 0) (.enumerate ⟨final, accumulated ++ features⟩ 0) := by
  induction chain generalizing accumulated with
  | nil source => simpa using (Relation.ReflTransGen.refl (a := Node.enumerate ⟨source, accumulated⟩ 0))
  | @cons source residual final feature descriptive features extracts reconstructs smaller _ _ ih =>
      let step : CompressionStep U source := ⟨feature, descriptive, residual, extracts, reconstructs, smaller⟩
      have first := step_reaches_child codeSpec ⟨source, accumulated⟩ step
      have later := ih (accumulated ++ [feature])
      simpa [step, Frame.extend, List.append_assoc] using first.trans later

theorem bChain_reaches_emission {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U)
    {factor : ℝ} {source final : BinString} {features : List BinString}
    (chain : BChain U factor source features final) (nonempty : features ≠ []) (accumulated : List BinString) :
    ∃ node, Reaches code (.enumerate ⟨source, accumulated⟩ 0) node ∧
      emit node = some ⟨final, accumulated ++ features⟩ := by
  induction chain generalizing accumulated with
  | nil source => exact (nonempty rfl).elim
  | @cons source residual final feature descriptive features extracts reconstructs smaller _ later ih =>
      let step : CompressionStep U source := ⟨feature, descriptive, residual, extracts, reconstructs, smaller⟩
      cases features with
      | nil =>
          cases later
          exact ⟨_, step_reaches_emission codeSpec ⟨source, accumulated⟩ step, rfl⟩
      | cons next rest =>
          obtain ⟨node, reached, emitted⟩ := ih (by simp) (accumulated ++ [feature])
          refine ⟨node, (step_reaches_child codeSpec ⟨source, accumulated⟩ step).trans reached, ?_⟩
          simpa [List.append_assoc] using emitted

def initial (source : BinString) : FairQueue.Queue Node :=
  FairQueue.initial [.enumerate (.root source) 0]

def observedFrames (code : Nat.Partrec.Code) (fuel : Nat) (queue : FairQueue.Queue Node) : List Frame :=
  ((FairQueue.run priority (successors code) fuel queue).1).filterMap (fun entry => emit entry.value)

theorem observedFrames_origin (code : Nat.Partrec.Code) (fuel : Nat) (queue : FairQueue.Queue Node)
    (frame : Frame) : frame ∈ observedFrames code fuel queue ↔
      ∃ entry ∈ (FairQueue.run priority (successors code) fuel queue).1, emit entry.value = some frame := by
  simp [observedFrames, List.mem_filterMap]

theorem observedFrames_add (code : Nat.Partrec.Code) (first second : Nat) (queue : FairQueue.Queue Node) :
    observedFrames code (first + second) queue = observedFrames code first queue ++
      observedFrames code second (FairQueue.run priority (successors code) first queue).2 := by
  simp [observedFrames, FairQueue.run_add]

theorem legal_emission {U : ConditionalAlgorithm} {source : BinString} {node : Node}
    (legal : Legal U source node) {frame : Frame} (emitted : emit node = some frame) :
    frame.Valid U source := by
  cases node with
  | enumerate => simp [emit] at emitted
  | extract => simp [emit] at emitted
  | rebuild => simp [emit] at emitted
  | found previous descriptive feature residual =>
      cases Option.some.inj emitted
      exact extend_valid legal.1 legal.2.2.1 legal.2.2.2

theorem observed_frame_valid {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U)
    (source : BinString) (fuel : Nat) {frame : Frame}
    (emitted : frame ∈ observedFrames code fuel (initial source)) : frame.Valid U source := by
  have rootLegal : Legal U source (.enumerate (.root source) 0) := root_valid U source
  have pending : ∀ node ∈ (initial source).pending.map FairQueue.Entry.value, Legal U source node := by
    simpa [initial, FairQueue.initial, FairQueue.numbered] using rootLegal
  have serviced := (FairQueue.run_preserves_invariant priority (successors code) (Legal U source)
    (fun _ legal _ member => successor_legal codeSpec legal member) fuel (initial source) pending).1
  obtain ⟨entry, present, published⟩ := (observedFrames_origin code fuel (initial source) frame).mp emitted
  exact legal_emission (serviced _ (List.mem_map.mpr ⟨entry, present, rfl⟩)) published

theorem every_observation_reconstructs {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U)
    (source : BinString) (fuel : Nat) {frame : Frame}
    (emitted : frame ∈ observedFrames code fuel (initial source)) :
    source ∈ schemeInterpreter U frame.description [] ∧ frame.features.length ≤ source.length := by
  have valid := observed_frame_valid codeSpec source fuel emitted
  exact ⟨valid_description valid, valid_depth valid⟩

theorem bChain_eventually_observed {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U)
    {factor : ℝ} {source final : BinString} {features : List BinString}
    (chain : BChain U factor source features final) (nonempty : features ≠ []) :
    ∃ fuel, (⟨final, features⟩ : Frame) ∈ observedFrames code fuel (initial source) := by
  obtain ⟨node, reachable, emits⟩ := bChain_reaches_emission codeSpec chain nonempty []
  obtain ⟨fuel, serviced⟩ := FairQueue.services_reachable priority (successors code) (initial source)
    (FairQueue.initial_valid _) (by simp [initial, FairQueue.initial, FairQueue.numbered, Frame.root]) reachable
  obtain ⟨entry, present, same⟩ := List.mem_map.mp serviced
  refine ⟨fuel, (observedFrames_origin code fuel (initial source) _).mpr ⟨entry, present, ?_⟩⟩
  simpa only [same, List.nil_append] using emits

/-- One fixed encoded interpreter works for all sources, factors and finite
valid chains. No shortest-feature oracle is used by the operational search. -/
theorem exists_global_search (U : ConditionalAlgorithm) (effective : Partrec₂ U) :
    ∃ code : Nat.Partrec.Code, Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U ∧
      ∀ factor source final features, BChain U factor source features final → features ≠ [] →
        ∃ fuel, (⟨final, features⟩ : Frame) ∈ observedFrames code fuel (initial source) := by
  obtain ⟨code, codeSpec⟩ := exists_conditional_algorithm_code effective
  exact ⟨code, codeSpec, fun _ _ _ _ chain nonempty => bChain_eventually_observed codeSpec chain nonempty⟩

theorem rational_scheme_eventually_observed {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U)
    {numerator denominator cutoff : Nat} {source final : BinString} {features : List BinString}
    (scheme : RationalScheme U numerator denominator cutoff source features final) (nonempty : features ≠ []) :
    ∃ fuel, (⟨final, features⟩ : Frame) ∈ observedFrames code fuel (initial source) :=
  bChain_eventually_observed codeSpec scheme.toBChain nonempty

def HasEnumerator (queue : FairQueue.Queue Node) : Prop :=
  ∃ frame rank, Node.enumerate frame rank ∈ queue.pending.map FairQueue.Entry.value

theorem after_has_enumerator (code : Nat.Partrec.Code) (queue : FairQueue.Queue Node)
    (live : HasEnumerator queue) {selected : FairQueue.Entry Node} {remaining : List (FairQueue.Entry Node)}
    (popped : FairQueue.pop priority queue = some (selected, remaining)) :
    HasEnumerator (FairQueue.after (successors code) queue selected remaining) := by
  obtain ⟨frame, rank, member⟩ := live
  have moved := ((FairQueue.pop_perm priority queue popped).map FairQueue.Entry.value).mem_iff.mpr member
  simp only [List.map_cons, List.mem_cons] at moved
  rcases moved with same | pending
  · refine ⟨frame, rank + 1, ?_⟩
    simp only [FairQueue.after, List.map_append, FairQueue.numbered_values, List.mem_append]
    exact Or.inr (by rw [← same]; simp [successors])
  · exact ⟨frame, rank, by
      simp only [FairQueue.after, List.map_append, FairQueue.numbered_values, List.mem_append]
      exact Or.inl pending⟩

theorem run_has_enumerator (code : Nat.Partrec.Code) (fuel : Nat) (queue : FairQueue.Queue Node)
    (live : HasEnumerator queue) : HasEnumerator (FairQueue.run priority (successors code) fuel queue).2 := by
  induction fuel generalizing queue with
  | zero => exact live
  | succ fuel ih =>
      cases popped : FairQueue.pop priority queue with
      | none => simpa [FairQueue.run, FairQueue.tick, popped] using live
      | some choice =>
          obtain ⟨selected, remaining⟩ := choice
          simpa [FairQueue.run, FairQueue.tick, popped] using
            ih _ (after_has_enumerator code queue live popped)

/-- A finite stage budget does not decide exhaustion of this unbounded
enumeration, even when the source has no compressive feature. -/
theorem global_search_never_exhausted (code : Nat.Partrec.Code) (fuel : Nat) (source : BinString) :
    (FairQueue.run priority (successors code) fuel (initial source)).2.pending ≠ [] := by
  have live : HasEnumerator (initial source) := ⟨.root source, 0,
    by simp [initial, FairQueue.initial, FairQueue.numbered]⟩
  obtain ⟨frame, rank, present⟩ := run_has_enumerator code fuel (initial source) live
  intro empty
  simp [empty] at present

/-- A greedy slice retains its local search until the first successful
publication, then commits to that residual and resets only the local search.
It uses the same cost/age policy, not the paper's dyadic allocation. -/
structure GreedyState where
  current : Frame
  queue : FairQueue.Queue Node

def greedyInitial (source : BinString) : GreedyState := ⟨.root source, initial source⟩

def greedyTick (code : Nat.Partrec.Code) (state : GreedyState) : GreedyState :=
  match FairQueue.tick priority (successors code) state.queue with
  | none => state
  | some (selected, remaining) =>
      match emit selected.value with
      | none => ⟨state.current, remaining⟩
      | some child => ⟨child, FairQueue.initial [.enumerate child 0]⟩

def greedyRun (code : Nat.Partrec.Code) : Nat → GreedyState → GreedyState
  | 0, state => state
  | count + 1, state => greedyRun code count (greedyTick code state)

def GreedyState.Valid (U : ConditionalAlgorithm) (source : BinString) (state : GreedyState) : Prop :=
  state.current.Valid U source ∧ ∀ node ∈ state.queue.pending.map FairQueue.Entry.value, Legal U source node

theorem greedy_tick_has_enumerator (code : Nat.Partrec.Code) (state : GreedyState)
    (live : HasEnumerator state.queue) : HasEnumerator (greedyTick code state).queue := by
  cases popped : FairQueue.pop priority state.queue with
  | none => simpa [greedyTick, FairQueue.tick, popped] using live
  | some choice =>
      obtain ⟨selected, remaining⟩ := choice
      cases emitted : emit selected.value with
      | none =>
          simpa [greedyTick, FairQueue.tick, popped, emitted] using
            after_has_enumerator code state.queue live popped
      | some child =>
          refine ⟨child, 0, ?_⟩
          simp [greedyTick, FairQueue.tick, popped, emitted, FairQueue.initial, FairQueue.numbered]

theorem greedy_run_has_enumerator (code : Nat.Partrec.Code) (count : Nat) (state : GreedyState)
    (live : HasEnumerator state.queue) : HasEnumerator (greedyRun code count state).queue := by
  induction count generalizing state with
  | zero => exact live
  | succ count ih => exact ih _ (greedy_tick_has_enumerator code state live)

theorem greedy_search_never_exhausted (code : Nat.Partrec.Code) (count : Nat) (source : BinString) :
    (greedyRun code count (greedyInitial source)).queue.pending ≠ [] := by
  have live : HasEnumerator (greedyInitial source).queue := ⟨.root source, 0,
    by simp [greedyInitial, initial, FairQueue.initial, FairQueue.numbered]⟩
  obtain ⟨frame, rank, present⟩ := greedy_run_has_enumerator code count (greedyInitial source) live
  intro empty
  simp [empty] at present

theorem greedy_initial_valid (U : ConditionalAlgorithm) (source : BinString) :
    (greedyInitial source).Valid U source := by
  constructor
  · exact root_valid U source
  · simpa [greedyInitial, initial, FairQueue.initial, FairQueue.numbered] using
      (show Legal U source (.enumerate (.root source) 0) from root_valid U source)

theorem greedy_tick_valid {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U)
    {source : BinString} {state : GreedyState} (valid : state.Valid U source) :
    (greedyTick code state).Valid U source := by
  cases popped : FairQueue.pop priority state.queue with
  | none => simpa [greedyTick, FairQueue.tick, popped] using valid
  | some choice =>
      obtain ⟨selected, remaining⟩ := choice
      have selectedLegal := valid.2 selected.value (List.mem_map.mpr ⟨selected,
        (FairQueue.pop_perm priority state.queue popped).mem_iff.mp (List.mem_cons_self ..), rfl⟩)
      have afterLegal := (FairQueue.run_preserves_invariant priority (successors code) (Legal U source)
        (fun _ legal _ member => successor_legal codeSpec legal member) 1 state.queue valid.2).2
      cases emitted : emit selected.value with
      | none =>
          constructor
          · simpa [greedyTick, FairQueue.tick, popped, emitted] using valid.1
          · simpa [greedyTick, FairQueue.run, FairQueue.tick, popped, emitted] using afterLegal
      | some child =>
          have childValid := legal_emission selectedLegal emitted
          constructor
          · simpa [greedyTick, FairQueue.tick, popped, emitted] using childValid
          · simpa [greedyTick, FairQueue.tick, popped, emitted, FairQueue.initial, FairQueue.numbered] using
              (show Legal U source (.enumerate child 0) from childValid)

theorem greedy_run_valid {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U)
    {source : BinString} (count : Nat) (state : GreedyState) (valid : state.Valid U source) :
    (greedyRun code count state).Valid U source := by
  induction count generalizing state with
  | zero => exact valid
  | succ count ih => exact ih _ (greedy_tick_valid codeSpec valid)

theorem greedy_run_add (code : Nat.Partrec.Code) (first second : Nat) (state : GreedyState) :
    greedyRun code (first + second) state = greedyRun code second (greedyRun code first state) := by
  induction first generalizing state with
  | zero => simp [greedyRun]
  | succ first ih => simpa only [Nat.succ_add, greedyRun] using ih (greedyTick code state)

theorem greedy_budget_reconstructs {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U)
    (source : BinString) (count : Nat) :
    let frame := (greedyRun code count (greedyInitial source)).current
    source ∈ schemeInterpreter U frame.description [] ∧ frame.features.length ≤ source.length := by
  have valid := (greedy_run_valid codeSpec count (greedyInitial source) (greedy_initial_valid U source)).1
  exact ⟨valid_description valid, valid_depth valid⟩

theorem emission_nonempty {node : Node} {frame : Frame} (emitted : emit node = some frame) :
    frame.features ≠ [] := by
  cases node with
  | enumerate => simp [emit] at emitted
  | extract => simp [emit] at emitted
  | rebuild => simp [emit] at emitted
  | found previous descriptive feature residual =>
      cases Option.some.inj emitted
      simp [Frame.extend]

/-- Before its first publication, the greedy machine services precisely the
same local queue as the global machine. A finite nonempty observation prefix
therefore forces an actual greedy commitment, not just a reachable branch. -/
theorem greedy_commits_of_observation (code : Nat.Partrec.Code) (fuel : Nat)
    (state : GreedyState) (observed : observedFrames code fuel state.queue ≠ []) :
    ∃ count, 0 < count ∧ count ≤ fuel ∧
      (greedyRun code count state).current.features ≠ [] := by
  induction fuel generalizing state with
  | zero => simp [observedFrames, FairQueue.run] at observed
  | succ fuel ih =>
      cases ticked : FairQueue.tick priority (successors code) state.queue with
      | none => simp [observedFrames, FairQueue.run, ticked] at observed
      | some choice =>
          obtain ⟨selected, remaining⟩ := choice
          cases emitted : emit selected.value with
          | some child =>
              refine ⟨1, by omega, by omega, ?_⟩
              simpa [greedyRun, greedyTick, ticked, emitted] using emission_nonempty emitted
          | none =>
              have later : observedFrames code fuel remaining ≠ [] := by
                simpa [observedFrames, FairQueue.run, ticked, emitted] using observed
              obtain ⟨count, positive, bounded, committed⟩ := ih ⟨state.current, remaining⟩ later
              refine ⟨count + 1, by omega, by omega, ?_⟩
              simpa [greedyRun, greedyTick, ticked, emitted] using committed

/-- A nonempty valid compression chain guarantees a finite first greedy
commitment, even though competing trials can diverge forever. This does not
claim that greedy search selects that chain or an ideal shortest feature. -/
theorem greedy_eventually_commits {U : ConditionalAlgorithm} {code : Nat.Partrec.Code}
    (codeSpec : Nat.Partrec.Code.eval code = encodedConditionalAlgorithm U)
    {factor : ℝ} {source final : BinString} {features : List BinString}
    (chain : BChain U factor source features final) (nonempty : features ≠ []) :
    ∃ count, 0 < count ∧ (greedyRun code count (greedyInitial source)).current.features ≠ [] := by
  obtain ⟨fuel, emitted⟩ := bChain_eventually_observed codeSpec chain nonempty
  have observed : observedFrames code fuel (greedyInitial source).queue ≠ [] := by
    intro empty
    simp only [greedyInitial] at empty
    rw [empty] at emitted
    simp at emitted
  obtain ⟨count, positive, _bounded, committed⟩ :=
    greedy_commits_of_observation code fuel (greedyInitial source) observed
  exact ⟨count, positive, committed⟩

#print axioms evaluate_mono
#print axioms evaluate_sound
#print axioms evaluate_complete
#print axioms root_valid
#print axioms extend_valid
#print axioms valid_description
#print axioms valid_depth
#print axioms successor_legal
#print axioms reaches_legal
#print axioms emitted_description_sound
#print axioms enumerate_reaches
#print axioms enumerate_reaches_pair
#print axioms extract_reaches_result
#print axioms rebuild_reaches_result
#print axioms step_reaches_emission
#print axioms step_reaches_child
#print axioms bChain_reaches_child
#print axioms bChain_reaches_emission
#print axioms observedFrames_origin
#print axioms observedFrames_add
#print axioms legal_emission
#print axioms observed_frame_valid
#print axioms every_observation_reconstructs
#print axioms bChain_eventually_observed
#print axioms exists_global_search
#print axioms rational_scheme_eventually_observed
#print axioms after_has_enumerator
#print axioms run_has_enumerator
#print axioms global_search_never_exhausted
#print axioms greedy_tick_has_enumerator
#print axioms greedy_run_has_enumerator
#print axioms greedy_search_never_exhausted
#print axioms greedy_initial_valid
#print axioms greedy_tick_valid
#print axioms greedy_run_valid
#print axioms greedy_run_add
#print axioms greedy_budget_reconstructs
#print axioms emission_nonempty
#print axioms greedy_commits_of_observation
#print axioms greedy_eventually_commits

end KolmogorovComplexity.FeatureTheory.GlobalSearch
