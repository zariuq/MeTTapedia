import Mettapedia.Languages.ProcessCalculi.PiCalculus.Synchronous
import Mettapedia.Languages.ProcessCalculi.PiCalculus.AuthoredStepReflection

/-!
# Reflecting synchronous π's rule firings

The occurrence specification of synchronous π's three rules (`PiSyncRawStep`): an input and an output on its channel
followed by a process, at two occurrences of a bag, leave the reception beside the process that followed the output; a
step inside a bag; a step under a restriction. The authored rules fire exactly these steps (`piSync_step_iff_raw`). A
replicated process takes part through its unfolding, a law, not a rule.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.Synchronous

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Interaction

theorem piSyncCalc_rewrites : piSyncCalc.rewrites =
    [piSyncCommRewrite, piParCongRewrite, piResCongRewrite] :=
  rfl

private theorem listener_match_iff (listener : String) (target : Pattern) (bindings : Bindings) :
    MatchRel (.apply listener [.fvar "x", .lambda none (.fvar "body")]) target bindings ↔
      ∃ channel binder body, target = .apply listener [channel, .lambda binder body] ∧
        bindings = [("body", body), ("x", channel)] := by
  constructor
  · intro matched
    cases matched with
    | apply args _ =>
      cases args with
      | cons channelMatch tail merged =>
        cases channelMatch
        cases tail with
        | cons bodyMatch last mergedBody =>
          cases bodyMatch with
          | lambda bodyMatch =>
            cases bodyMatch
            cases last
            simp only [mergeBindings] at mergedBody
            cases mergedBody
            simp only [mergeBindings] at merged
            cases merged
            exact ⟨_, _, _, rfl, rfl⟩
  · rintro ⟨channel, binder, body, rfl, rfl⟩
    exact .apply (.cons .fvar (.cons (.lambda .fvar) .nil rfl) rfl) rfl

private theorem output_match_iff (target : Pattern) (bindings : Bindings) :
    MatchRel (.apply "PiOutK" [.fvar "x", .fvar "z", .fvar "k"]) target bindings ↔
      ∃ channel datum continuation, target = .apply "PiOutK" [channel, datum, continuation] ∧
        bindings = [("z", datum), ("k", continuation), ("x", channel)] := by
  constructor
  · intro matched
    cases matched with
    | apply args _ =>
      cases args with
      | cons channelMatch tail merged =>
        cases channelMatch
        cases tail with
        | cons datumMatch tail' mergedDatum =>
          cases datumMatch
          cases tail' with
          | cons continuationMatch last mergedContinuation =>
            cases continuationMatch
            cases last
            simp only [mergeBindings] at mergedContinuation
            cases mergedContinuation
            simp only [mergeBindings] at mergedDatum
            cases mergedDatum
            simp only [mergeBindings] at merged
            cases merged
            exact ⟨_, _, _, rfl, rfl⟩
  · rintro ⟨channel, datum, continuation, rfl, rfl⟩
    exact .apply (.cons .fvar (.cons .fvar (.cons .fvar .nil rfl) rfl) rfl) rfl

private theorem exchange_match_inv (listener : String) {source : Pattern} {bindings : Bindings}
    (matched : MatchRel
      (.collection .hashBag [.apply listener [.fvar "x", .lambda none (.fvar "body")],
        .apply "PiOutK" [.fvar "x", .fvar "z", .fvar "k"]] (some "rest")) source bindings) :
    ∃ (elements : List Pattern) (tail : Option String)
      (i : Nat) (hi : i < elements.length)
      (j : Nat) (hj : j < (elements.eraseIdx i).length)
      (channel : Pattern) (binder : Option String) (body datum continuation : Pattern),
      source = .collection .hashBag elements tail ∧
      elements[i] = .apply listener [channel, .lambda binder body] ∧
      (elements.eraseIdx i)[j] = .apply "PiOutK" [channel, datum, continuation] ∧
      bindings = piSyncMatchedBindings channel body datum continuation ((elements.eraseIdx i).eraseIdx j) := by
  cases matched with
  | collection _ bag =>
    cases bag with
    | cons i hi first remaining mergeFirst =>
      obtain ⟨channel, binder, body, firstShape, firstBindings⟩ :=
        (listener_match_iff listener _ _).mp first
      subst firstBindings
      cases remaining with
      | cons j hj second last mergeRest =>
        obtain ⟨otherChannel, datum, continuation, secondShape, secondBindings⟩ :=
          (output_match_iff _ _).mp second
        subst secondBindings
        cases last
        simp only [mergeBindings] at mergeRest
        cases mergeRest
        simp only [mergeBindings, List.foldlM_cons, List.foldlM_nil,
          List.find?_cons, List.find?_nil] at mergeFirst
        simp at mergeFirst
        obtain ⟨rfl, rfl⟩ := mergeFirst
        exact ⟨_, _, i, hi, j, hj, _, binder, body, datum, continuation,
          rfl, firstShape, secondShape, rfl⟩

/-- The concrete captures are accepted by the matcher, at any two occurrences. -/
theorem piSyncExchange_selected_match (listener : String)
    {elements : List Pattern} {tail : Option String}
    (i : Nat) (hi : i < elements.length)
    (j : Nat) (hj : j < (elements.eraseIdx i).length)
    (channel : Pattern) (binder : Option String) (body datum continuation : Pattern)
    (input : elements[i] = .apply listener [channel, .lambda binder body])
    (output : (elements.eraseIdx i)[j] = .apply "PiOutK" [channel, datum, continuation]) :
    piSyncMatchedBindings channel body datum continuation ((elements.eraseIdx i).eraseIdx j) ∈
      matchPattern (.collection .hashBag
        [.apply listener [.fvar "x", .lambda none (.fvar "body")],
          .apply "PiOutK" [.fvar "x", .fvar "z", .fvar "k"]] (some "rest"))
        (.collection .hashBag elements tail) := by
  apply matchPattern_iff_matchRel.mpr
  apply MatchRel.collection (by decide)
  apply MatchBagRel.cons i hi
  · exact (listener_match_iff _ _ _).mpr ⟨channel, binder, body, input, rfl⟩
  · apply MatchBagRel.cons j hj
    · exact (output_match_iff _ _).mpr ⟨channel, datum, continuation, output, rfl⟩
    · exact .nilRest
    · rfl
  · simp [piSyncMatchedBindings, mergeBindings]

/-- Binding application substitutes the carried name into the listener's body and releases the continuation. -/
theorem piSyncComm_apply_exact (channel body datum continuation : Pattern) (rest : List Pattern) :
    applyBindingsForRule piSyncCalc piSyncCommRewrite (piSyncMatchedBindings channel body datum continuation rest) =
      .collection .hashBag (instantiateBVar datum body :: continuation :: rest) none := by
  rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide +kernel)]
  simp [piSyncCommRewrite, piSyncMatchedBindings, applyBindings]

theorem piSyncParCong_apply_exact (source target : Pattern) (rest : List Pattern) :
    applyBindingsForRule piSyncCalc piParCongRewrite
      [("T", target), ("rest", .collection .hashBag rest none), ("S", source)] =
      .collection .hashBag (target :: rest) none :=
  piParCong_apply_exact source target rest

theorem piSyncResCong_apply_exact (source target : Pattern) :
    applyBindingsForRule piSyncCalc piResCongRewrite [("T", target), ("S", source)] =
      .apply "PiNu" [.lambda none target] :=
  piResCong_apply_exact source target

/-- **The occurrence specification of synchronous π's rules.** Display metadata and open collection tails are
visible only at the raw matcher boundary. -/
inductive PiSyncRawStep : Pattern → Pattern → Prop where
  | comm {elements : List Pattern} {tail : Option String}
      (i : Nat) (hi : i < elements.length)
      (j : Nat) (hj : j < (elements.eraseIdx i).length)
      (channel : Pattern) (binder : Option String) (body datum continuation : Pattern)
      (input : elements[i] = .apply "PiInp" [channel, .lambda binder body])
      (output : (elements.eraseIdx i)[j] = .apply "PiOutK" [channel, datum, continuation]) :
      PiSyncRawStep (.collection .hashBag elements tail)
        (.collection .hashBag
          (instantiateBVar datum body :: continuation :: (elements.eraseIdx i).eraseIdx j) none)
  | par {elements : List Pattern} {tail : Option String}
      (i : Nat) (hi : i < elements.length) {target : Pattern}
      (inner : PiSyncRawStep elements[i] target) :
      PiSyncRawStep (.collection .hashBag elements tail)
        (.collection .hashBag (target :: elements.eraseIdx i) none)
  | res (binder : Option String) {source target : Pattern}
      (inner : PiSyncRawStep source target) :
      PiSyncRawStep (.apply "PiNu" [.lambda binder source])
        (.apply "PiNu" [.lambda none target])

private theorem par_match_inv {source : Pattern} {bindings : Bindings}
    (matched : MatchRel (.collection .hashBag [.fvar "S"] (some "rest")) source bindings) :
    ∃ (elements : List Pattern) (tail : Option String) (i : Nat) (hi : i < elements.length),
      source = .collection .hashBag elements tail ∧
      bindings = [("rest", .collection .hashBag (elements.eraseIdx i) none), ("S", elements[i])] := by
  cases matched with
  | collection _ bag =>
    cases bag with
    | cons i hi first remaining merged =>
      cases first
      cases remaining
      simp [mergeBindings] at merged
      cases merged
      exact ⟨_, _, i, hi, rfl, rfl⟩

private theorem restriction_match_inv {source : Pattern} {bindings : Bindings}
    (matched : MatchRel (.apply "PiNu" [.lambda none (.fvar "S")]) source bindings) :
    ∃ binder body, source = .apply "PiNu" [.lambda binder body] ∧ bindings = [("S", body)] := by
  cases matched with
  | apply args _ =>
    cases args with
    | cons bodyMatch last merged =>
      cases bodyMatch with
      | lambda bodyMatch =>
        cases bodyMatch
        cases last
        simp [mergeBindings] at merged
        cases merged
        exact ⟨_, _, rfl, rfl⟩

private theorem piSyncRawStep_of_stepAt {fuel : Nat} {source target : Pattern}
    (step : StepAt (engineBasePremises RelationEnv.empty) piSyncCalc fuel source target) :
    PiSyncRawStep source target := by
  induction fuel using Nat.strong_induction_on generalizing source target with
  | h fuel ih =>
    cases step with
    | @rule innerFuel source target rule initial final member matching premises result =>
      rw [piSyncCalc_rewrites] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rw [matchPatternForRule_eq_syntactic] at matching
      have matchRel := matchPattern_iff_matchRel.mp matching
      rcases member with rfl | rfl | rfl
      · change MatchRel (.collection .hashBag
          [.apply "PiInp" [.fvar "x", .lambda none (.fvar "body")],
            .apply "PiOutK" [.fvar "x", .fvar "z", .fvar "k"]] (some "rest")) source initial at matchRel
        obtain ⟨elements, tail, i, hi, j, hj, channel, binder, body, datum, continuation,
          rfl, atInput, atOutput, rfl⟩ := exchange_match_inv "PiInp" matchRel
        change PremisesAt _ _ _ _ [] _ at premises
        cases premises
        rw [piSyncComm_apply_exact] at result
        cases result
        exact .comm i hi j hj channel binder body datum continuation atInput atOutput
      · change MatchRel (.collection .hashBag [.fvar "S"] (some "rest")) source initial at matchRel
        obtain ⟨elements, tail, i, hi, rfl, rfl⟩ := par_match_inv matchRel
        change PremisesAt _ _ _ _ [.congruence (.fvar "S") (.fvar "T")] _ at premises
        cases premises with
        | cons premise last =>
          cases last
          cases premise with
          | @congruence _ _ premiseBindings _ _ _ candidate inner matched merged =>
            have bindingsEq : premiseBindings = [("T", candidate)] := by
              simpa [matchPattern] using matched
            subst premiseBindings
            have finalEq : final = [("T", candidate),
                ("rest", .collection .hashBag (elements.eraseIdx i) none), ("S", elements[i])] := by
              simpa [mergeBindings] using merged.symm
            subst final
            rw [piSyncParCong_apply_exact] at result
            cases result
            exact .par i hi (ih innerFuel (by omega) (by simpa [applyBindings] using inner))
      · change MatchRel (.apply "PiNu" [.lambda none (.fvar "S")]) source initial at matchRel
        obtain ⟨binder, body, rfl, rfl⟩ := restriction_match_inv matchRel
        change PremisesAt _ _ _ _ [.congruence (.fvar "S") (.fvar "T")] _ at premises
        cases premises with
        | cons premise last =>
          cases last
          cases premise with
          | @congruence _ _ premiseBindings _ _ _ candidate inner matched merged =>
            have bindingsEq : premiseBindings = [("T", candidate)] := by
              simpa [matchPattern] using matched
            subst premiseBindings
            have finalEq : final = [("T", candidate), ("S", body)] := by
              simpa [mergeBindings] using merged.symm
            subst final
            rw [piSyncResCong_apply_exact] at result
            cases result
            exact .res binder (ih innerFuel (by omega) (by simpa [applyBindings] using inner))

/-- Every authored firing is a step of the occurrence specification. -/
theorem piSyncRawStep_of_step {source target : Pattern}
    (step : Step (engineBasePremises RelationEnv.empty) piSyncCalc source target) :
    PiSyncRawStep source target := by
  obtain ⟨fuel, bounded⟩ := step
  exact piSyncRawStep_of_stepAt bounded

/-- The occurrence specification is executable by the authored rules. -/
theorem step_of_piSyncRawStep {source target : Pattern} (step : PiSyncRawStep source target) :
    Step (engineBasePremises RelationEnv.empty) piSyncCalc source target := by
  induction step with
  | comm i hi j hj channel binder body datum continuation input output =>
    refine ⟨1, .rule (rule := piSyncCommRewrite) ?_ ?_ (.nil _)
      (piSyncComm_apply_exact channel body datum continuation _)⟩
    · rw [piSyncCalc_rewrites]; simp
    · rw [matchPatternForRule_eq_syntactic]
      exact piSyncExchange_selected_match "PiInp" i hi j hj channel binder body datum continuation input output
  | @par elements tail i hi target _ ih =>
    obtain ⟨fuel, inner⟩ := ih
    refine ⟨fuel + 1, .rule (rule := piParCongRewrite)
      (initialBindings := [("rest", .collection .hashBag (elements.eraseIdx i) none), ("S", elements[i])])
      (finalBindings := [("T", target), ("rest", .collection .hashBag (elements.eraseIdx i) none),
        ("S", elements[i])]) ?_ ?_ ?_ (piSyncParCong_apply_exact _ _ _)⟩
    · rw [piSyncCalc_rewrites]; simp
    · rw [matchPatternForRule_eq_syntactic]
      exact matchPattern_iff_matchRel.mpr
        (.collection (by decide) (.cons i hi .fvar .nilRest rfl))
    · apply PremisesAt.cons
      · apply PremiseAt.congruence (premiseBindings := [("T", target)]) (candidate := target)
        · simpa [applyBindings] using inner
        · simp [matchPattern]
        · rfl
      · exact .nil _
  | @res binder source target _ ih =>
    obtain ⟨fuel, inner⟩ := ih
    refine ⟨fuel + 1, .rule (rule := piResCongRewrite)
      (initialBindings := [("S", source)]) (finalBindings := [("T", target), ("S", source)])
      ?_ ?_ ?_ (piSyncResCong_apply_exact source target)⟩
    · rw [piSyncCalc_rewrites]; simp
    · rw [matchPatternForRule_eq_syntactic]
      exact matchPattern_iff_matchRel.mpr (.apply (.cons (.lambda .fvar) .nil rfl) rfl)
    · apply PremisesAt.cons
      · apply PremiseAt.congruence (premiseBindings := [("T", target)]) (candidate := target)
        · simpa [applyBindings] using inner
        · simp [matchPattern]
        · rfl
      · exact .nil _

/-- **Exact two-sided adequacy** of synchronous π's authored rules. -/
theorem piSync_step_iff_raw (source target : Pattern) :
    Step (engineBasePremises RelationEnv.empty) piSyncCalc source target ↔ PiSyncRawStep source target :=
  ⟨piSyncRawStep_of_step, step_of_piSyncRawStep⟩

end Mettapedia.Languages.ProcessCalculi.PiCalculus.Synchronous
