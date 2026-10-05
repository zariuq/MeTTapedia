import Mettapedia.Languages.ProcessCalculi.PiCalculus.AuthoredCommunication

/-!
# Reflecting actual pi rule firings

The independent reduction specification selects occurrences in a parallel bag,
performs binder elimination, and descends through the two active contexts.
Occurrence indices distinguish equal messages. The comparison retains the
endpoint supplied by the authored execution, rather than finding another run.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Interaction

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
    MatchRel (.apply "PiOut" [.fvar "x", .fvar "z"]) target bindings ↔
      ∃ channel datum, target = .apply "PiOut" [channel, datum] ∧
        bindings = [("z", datum), ("x", channel)] := by
  constructor
  · intro matched
    cases matched with
    | apply args _ =>
      cases args with
      | cons channelMatch tail merged =>
        cases channelMatch
        cases tail with
        | cons datumMatch last mergedDatum =>
          cases datumMatch
          cases last
          simp only [mergeBindings] at mergedDatum
          cases mergedDatum
          simp only [mergeBindings] at merged
          cases merged
          exact ⟨_, _, rfl, rfl⟩
  · rintro ⟨channel, datum, rfl, rfl⟩
    exact .apply (.cons .fvar (.cons .fvar .nil rfl) rfl) rfl

private theorem exchange_match_inv (listener : String) {source : Pattern} {bindings : Bindings}
    (matched : MatchRel
      (.collection .hashBag [.apply listener [.fvar "x", .lambda none (.fvar "body")],
        .apply "PiOut" [.fvar "x", .fvar "z"]] (some "rest")) source bindings) :
    ∃ (elements : List Pattern) (tail : Option String)
      (i : Nat) (hi : i < elements.length)
      (j : Nat) (hj : j < (elements.eraseIdx i).length)
      (channel : Pattern) (binder : Option String) (body datum : Pattern),
      source = .collection .hashBag elements tail ∧
      elements[i] = .apply listener [channel, .lambda binder body] ∧
      (elements.eraseIdx i)[j] = .apply "PiOut" [channel, datum] ∧
      bindings = piCommMatchedBindings channel body datum ((elements.eraseIdx i).eraseIdx j) := by
  cases matched with
  | collection _ bag =>
    cases bag with
    | cons i hi first remaining mergeFirst =>
      obtain ⟨channel, binder, body, firstShape, firstBindings⟩ :=
        (listener_match_iff listener _ _).mp first
      subst firstBindings
      cases remaining with
      | cons j hj second last mergeRest =>
        obtain ⟨otherChannel, datum, secondShape, secondBindings⟩ :=
          (output_match_iff _ _).mp second
        subst secondBindings
        cases last
        simp only [mergeBindings] at mergeRest
        cases mergeRest
        simp only [mergeBindings, List.foldlM_cons, List.foldlM_nil,
          List.find?_cons, List.find?_nil] at mergeFirst
        simp at mergeFirst
        obtain ⟨rfl, rfl⟩ := mergeFirst
        exact ⟨_, _, i, hi, j, hj, _, binder, body, datum,
          rfl, firstShape, secondShape, rfl⟩

/-- An occurrence-based specification of the four internal rules. Display
metadata and open collection tails are visible only at the raw matcher
boundary; the atomic object fragment below excludes both. -/
inductive PiRawStep : Pattern → Pattern → Prop where
  | comm {elements : List Pattern} {tail : Option String}
      (i : Nat) (hi : i < elements.length)
      (j : Nat) (hj : j < (elements.eraseIdx i).length)
      (channel : Pattern) (binder : Option String) (body datum : Pattern)
      (input : elements[i] = .apply "PiInp" [channel, .lambda binder body])
      (output : (elements.eraseIdx i)[j] = .apply "PiOut" [channel, datum]) :
      PiRawStep (.collection .hashBag elements tail)
        (.collection .hashBag
          (instantiateBVar datum body :: (elements.eraseIdx i).eraseIdx j) none)
  | repComm {elements : List Pattern} {tail : Option String}
      (i : Nat) (hi : i < elements.length)
      (j : Nat) (hj : j < (elements.eraseIdx i).length)
      (channel : Pattern) (binder : Option String) (body datum : Pattern)
      (input : elements[i] = .apply "PiRep" [channel, .lambda binder body])
      (output : (elements.eraseIdx i)[j] = .apply "PiOut" [channel, datum]) :
      PiRawStep (.collection .hashBag elements tail)
        (.collection .hashBag
          ([instantiateBVar datum body, .apply "PiRep" [channel, .lambda none body]] ++
            (elements.eraseIdx i).eraseIdx j) none)
  | par {elements : List Pattern} {tail : Option String}
      (i : Nat) (hi : i < elements.length) {target : Pattern}
      (inner : PiRawStep elements[i] target) :
      PiRawStep (.collection .hashBag elements tail)
        (.collection .hashBag (target :: elements.eraseIdx i) none)
  | res (binder : Option String) {source target : Pattern}
      (inner : PiRawStep source target) :
      PiRawStep (.apply "PiNu" [.lambda binder source])
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

private theorem piRawStep_of_stepAt {fuel : Nat} {source target : Pattern}
    (step : StepAt (engineBasePremises RelationEnv.empty) piCalc fuel source target) :
    PiRawStep source target := by
  induction fuel using Nat.strong_induction_on generalizing source target with
  | h fuel ih =>
    cases step with
    | @rule innerFuel source target rule initial final member matching premises result =>
      rw [piCalc_rewrites] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rw [matchPatternForRule_eq_syntactic] at matching
      have matchRel := matchPattern_iff_matchRel.mp matching
      rcases member with rfl | rfl | rfl | rfl
      · change MatchRel (.collection .hashBag
          [.apply "PiInp" [.fvar "x", .lambda none (.fvar "body")],
            .apply "PiOut" [.fvar "x", .fvar "z"]] (some "rest")) source initial at matchRel
        obtain ⟨elements, tail, i, hi, j, hj, channel, binder, body, datum,
          rfl, atInput, atOutput, rfl⟩ := exchange_match_inv "PiInp" matchRel
        change PremisesAt _ _ _ _ [] _ at premises
        cases premises
        rw [piComm_apply_exact] at result
        cases result
        exact .comm i hi j hj channel binder body datum atInput atOutput
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
            rw [piParCong_apply_exact] at result
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
            rw [piResCong_apply_exact] at result
            cases result
            exact .res binder (ih innerFuel (by omega) (by simpa [applyBindings] using inner))
      · change MatchRel (.collection .hashBag
          [.apply "PiRep" [.fvar "x", .lambda none (.fvar "body")],
            .apply "PiOut" [.fvar "x", .fvar "z"]] (some "rest")) source initial at matchRel
        obtain ⟨elements, tail, i, hi, j, hj, channel, binder, body, datum,
          rfl, atInput, atOutput, rfl⟩ := exchange_match_inv "PiRep" matchRel
        change PremisesAt _ _ _ _ [] _ at premises
        cases premises
        rw [piRepComm_apply_exact] at result
        cases result
        exact .repComm i hi j hj channel binder body datum atInput atOutput

/-- Every supplied authored endpoint has a reduction derivation in the
independent occurrence specification. -/
theorem piRawStep_of_step {source target : Pattern}
    (step : Step (engineBasePremises RelationEnv.empty) piCalc source target) :
    PiRawStep source target := by
  obtain ⟨fuel, bounded⟩ := step
  exact piRawStep_of_stepAt bounded

/-- Actual matching at two distinct bag occurrences, including non-leading
receivers and equal messages at different positions. -/
theorem piExchange_selected_match (listener : String)
    {elements : List Pattern} {tail : Option String}
    (i : Nat) (hi : i < elements.length)
    (j : Nat) (hj : j < (elements.eraseIdx i).length)
    (channel : Pattern) (binder : Option String) (body datum : Pattern)
    (input : elements[i] = .apply listener [channel, .lambda binder body])
    (output : (elements.eraseIdx i)[j] = .apply "PiOut" [channel, datum]) :
    piCommMatchedBindings channel body datum ((elements.eraseIdx i).eraseIdx j) ∈
      matchPattern (.collection .hashBag
        [.apply listener [.fvar "x", .lambda none (.fvar "body")],
          .apply "PiOut" [.fvar "x", .fvar "z"]] (some "rest"))
        (.collection .hashBag elements tail) := by
  apply matchPattern_iff_matchRel.mpr
  apply MatchRel.collection (by decide)
  apply MatchBagRel.cons i hi
  · exact (listener_match_iff _ _ _).mpr ⟨channel, binder, body, input, rfl⟩
  · apply MatchBagRel.cons j hj
    · exact (output_match_iff _ _).mpr ⟨channel, datum, output, rfl⟩
    · exact .nilRest
    · rfl
  · simp [piCommMatchedBindings, mergeBindings]

/-- The occurrence specification is executable by the actual authored rules. -/
theorem step_of_piRawStep {source target : Pattern} (step : PiRawStep source target) :
    Step (engineBasePremises RelationEnv.empty) piCalc source target := by
  induction step with
  | comm i hi j hj channel binder body datum input output =>
    refine ⟨1, .rule (rule := piCommRewrite) ?_ ?_ (.nil _)
      (piComm_apply_exact channel body datum _)⟩
    · rw [piCalc_rewrites]; simp
    · rw [matchPatternForRule_eq_syntactic]
      exact piExchange_selected_match "PiInp" i hi j hj channel binder body datum input output
  | repComm i hi j hj channel binder body datum input output =>
    refine ⟨1, .rule (rule := piRepCommRewrite) ?_ ?_ (.nil _)
      (piRepComm_apply_exact channel body datum _)⟩
    · rw [piCalc_rewrites]; simp
    · rw [matchPatternForRule_eq_syntactic]
      exact piExchange_selected_match "PiRep" i hi j hj channel binder body datum input output
  | @par elements tail i hi target _ ih =>
    obtain ⟨fuel, inner⟩ := ih
    refine ⟨fuel + 1, .rule (rule := piParCongRewrite)
      (initialBindings := [("rest", .collection .hashBag (elements.eraseIdx i) none), ("S", elements[i])])
      (finalBindings := [("T", target), ("rest", .collection .hashBag (elements.eraseIdx i) none),
        ("S", elements[i])]) ?_ ?_ ?_ (piParCong_apply_exact _ _ _)⟩
    · rw [piCalc_rewrites]; simp
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
      ?_ ?_ ?_ (piResCong_apply_exact source target)⟩
    · rw [piCalc_rewrites]; simp
    · rw [matchPatternForRule_eq_syntactic]
      exact matchPattern_iff_matchRel.mpr (.apply (.cons (.lambda .fvar) .nil rfl) rfl)
    · apply PremisesAt.cons
      · apply PremiseAt.congruence (premiseBindings := [("T", target)]) (candidate := target)
        · simpa [applyBindings] using inner
        · simp [matchPattern]
        · rfl
      · exact .nil _

/-- Exact two-sided adequacy for internal execution, before static saturation. -/
theorem pi_step_iff_raw (source target : Pattern) :
    Step (engineBasePremises RelationEnv.empty) piCalc source target ↔ PiRawStep source target :=
  ⟨piRawStep_of_step, step_of_piRawStep⟩

/-- Both comparisons retain the endpoint of the supplied finite execution. -/
theorem pi_path_iff_raw (source target : Pattern) :
    Relation.ReflTransGen (Step (engineBasePremises RelationEnv.empty) piCalc) source target ↔
      Relation.ReflTransGen PiRawStep source target := by
  constructor
  · intro path
    exact Relation.ReflTransGen.mono (fun _ _ firing => piRawStep_of_step firing) source target path
  · intro path
    exact Relation.ReflTransGen.mono (fun _ _ firing => step_of_piRawStep firing) source target path

end Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
