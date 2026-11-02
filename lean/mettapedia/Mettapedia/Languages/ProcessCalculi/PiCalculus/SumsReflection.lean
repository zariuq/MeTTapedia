import Mettapedia.Languages.ProcessCalculi.PiCalculus.Sums

/-!
# The rule firing of the π-calculus with sums, by occurrence

An independent specification of the rules of the π-calculus with sums (`PiSumRawStep`), by occurrence index:

- a communication selects two sums among the components of a parallel composition, an input among the summands of
  the first and an output on the same channel among the summands of the second; the input's body receives the
  output's datum beside the output's continuation, and the other summands of the two sums are discarded;
- a silent step selects a silent summand of a sum and leaves its continuation, the other summands discarded;
- a step happens inside a parallel composition and under a restriction.

The authored rules fire exactly as the specification says (`step_iff_raw`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.Sums

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (instantiateBVar)
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Interaction

/-- **The firing of the π-calculus with sums, by occurrence.** -/
inductive PiSumRawStep : Pattern → Pattern → Prop where
  /-- `[x(y).P + M] | [x⟨z⟩.K + N] | R ⟶ P[z/y] | K | R` -/
  | comm {elements : List Pattern} {tail : Option String}
      (i : ℕ) (hi : i < elements.length) (j : ℕ) (hj : j < (elements.eraseIdx i).length)
      {guards guards' : List Pattern} {sumTail sumTail' : Option String}
      (k : ℕ) (hk : k < guards.length) (l : ℕ) (hl : l < guards'.length)
      (channel : Pattern) (binder : Option String) (body datum continuation : Pattern)
      (first : elements[i] = .apply "PiSum" [.collection .hashBag guards sumTail])
      (second : (elements.eraseIdx i)[j] = .apply "PiSum" [.collection .hashBag guards' sumTail'])
      (receiving : guards[k] = .apply "PiRecv" [channel, .lambda binder body])
      (sending : guards'[l] = .apply "PiSend" [channel, datum, continuation]) :
      PiSumRawStep (.collection .hashBag elements tail)
        (.collection .hashBag (instantiateBVar datum body :: continuation :: (elements.eraseIdx i).eraseIdx j) none)
  /-- `τ.K + M ⟶ K` -/
  | tau {guards : List Pattern} {sumTail : Option String} (k : ℕ) (hk : k < guards.length) (continuation : Pattern)
      (silent : guards[k] = .apply "PiTau" [continuation]) :
      PiSumRawStep (.apply "PiSum" [.collection .hashBag guards sumTail]) continuation
  /-- A step inside a parallel composition. -/
  | par {elements : List Pattern} {tail : Option String} (i : ℕ) (hi : i < elements.length) {target : Pattern}
      (inner : PiSumRawStep elements[i] target) :
      PiSumRawStep (.collection .hashBag elements tail) (.collection .hashBag (target :: elements.eraseIdx i) none)
  /-- A step under a restriction. -/
  | res (binder : Option String) {source target : Pattern} (inner : PiSumRawStep source target) :
      PiSumRawStep (.apply "PiNu" [.lambda binder source]) (.apply "PiNu" [.lambda none target])

/-! ## Matching the rules -/

/-- The bindings of a communication. -/
def commBindings (channel body datum continuation : Pattern) (others others' rest : List Pattern) : Bindings :=
  [("k", continuation), ("z", datum), ("n", .collection .hashBag others' none), ("rest", .collection .hashBag rest none),
    ("m", .collection .hashBag others none), ("body", body), ("x", channel)]

/-- The bindings of a silent step. -/
def tauBindings (continuation : Pattern) (others : List Pattern) : Bindings :=
  [("m", .collection .hashBag others none), ("k", continuation)]

private theorem recv_match_iff (target : Pattern) (bindings : Bindings) :
    MatchRel (.apply "PiRecv" [.fvar "x", .lambda none (.fvar "body")]) target bindings ↔
      ∃ channel binder body, target = .apply "PiRecv" [channel, .lambda binder body] ∧
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

private theorem send_match_iff (target : Pattern) (bindings : Bindings) :
    MatchRel (.apply "PiSend" [.fvar "x", .fvar "z", .fvar "k"]) target bindings ↔
      ∃ channel datum continuation, target = .apply "PiSend" [channel, datum, continuation] ∧
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

private theorem unary_match_iff (label var : String) (target : Pattern) (bindings : Bindings) :
    MatchRel (.apply label [.fvar var]) target bindings ↔
      ∃ argument, target = .apply label [argument] ∧ bindings = [(var, argument)] := by
  constructor
  · intro matched
    cases matched with
    | apply args _ =>
      cases args with
      | cons argumentMatch last merged =>
        cases argumentMatch
        cases last
        simp [mergeBindings] at merged
        subst merged
        exact ⟨_, rfl, rfl⟩
  · rintro ⟨argument, rfl, rfl⟩
    exact .apply (.cons .fvar .nil rfl) rfl

private theorem recvSum_match_iff (target : Pattern) (bindings : Bindings) :
    MatchRel (.apply "PiSum" [.collection .hashBag [.apply "PiRecv" [.fvar "x", .lambda none (.fvar "body")]]
        (some "m")]) target bindings ↔
      ∃ (guards : List Pattern) (sumTail : Option String) (k : ℕ) (hk : k < guards.length) (channel : Pattern)
        (binder : Option String) (body : Pattern),
        target = .apply "PiSum" [.collection .hashBag guards sumTail] ∧
          guards[k] = .apply "PiRecv" [channel, .lambda binder body] ∧
          bindings = [("m", .collection .hashBag (guards.eraseIdx k) none), ("body", body), ("x", channel)] := by
  constructor
  · intro matched
    cases matched with
    | apply args _ =>
      cases args with
      | cons sumMatch last merged =>
        cases last
        cases sumMatch with
        | collection _ bag =>
          cases bag with
          | cons k hk first remaining mergedFirst =>
            obtain ⟨channel, binder, body, atGuard, rfl⟩ := (recv_match_iff _ _).mp first
            cases remaining
            simp [mergeBindings, List.find?] at mergedFirst
            subst mergedFirst
            simp [mergeBindings] at merged
            subst merged
            exact ⟨_, _, k, hk, channel, binder, body, rfl, atGuard, rfl⟩
  · rintro ⟨guards, sumTail, k, hk, channel, binder, body, rfl, atGuard, rfl⟩
    have guardMatch : MatchRel (.apply "PiRecv" [.fvar "x", .lambda none (.fvar "body")]) guards[k]
        [("body", body), ("x", channel)] := by
      rw [atGuard]
      exact (recv_match_iff _ _).mpr ⟨channel, binder, body, rfl, rfl⟩
    exact .apply (.cons (.collection (by decide)
      (MatchBagRel.cons (bs := [("m", .collection .hashBag (guards.eraseIdx k) none), ("body", body),
          ("x", channel)]) k hk guardMatch .nilRest (by simp [mergeBindings, List.find?]))) .nil
      (by simp [mergeBindings])) rfl

private theorem sendSum_match_iff (target : Pattern) (bindings : Bindings) :
    MatchRel (.apply "PiSum" [.collection .hashBag [.apply "PiSend" [.fvar "x", .fvar "z", .fvar "k"]] (some "n")])
        target bindings ↔
      ∃ (guards : List Pattern) (sumTail : Option String) (l : ℕ) (hl : l < guards.length)
        (channel datum continuation : Pattern),
        target = .apply "PiSum" [.collection .hashBag guards sumTail] ∧
          guards[l] = .apply "PiSend" [channel, datum, continuation] ∧
          bindings = [("n", .collection .hashBag (guards.eraseIdx l) none), ("z", datum), ("k", continuation),
            ("x", channel)] := by
  constructor
  · intro matched
    cases matched with
    | apply args _ =>
      cases args with
      | cons sumMatch last merged =>
        cases last
        cases sumMatch with
        | collection _ bag =>
          cases bag with
          | cons l hl first remaining mergedFirst =>
            obtain ⟨channel, datum, continuation, atGuard, rfl⟩ := (send_match_iff _ _).mp first
            cases remaining
            simp [mergeBindings, List.find?] at mergedFirst
            subst mergedFirst
            simp [mergeBindings] at merged
            subst merged
            exact ⟨_, _, l, hl, channel, datum, continuation, rfl, atGuard, rfl⟩
  · rintro ⟨guards, sumTail, l, hl, channel, datum, continuation, rfl, atGuard, rfl⟩
    have guardMatch : MatchRel (.apply "PiSend" [.fvar "x", .fvar "z", .fvar "k"]) guards[l]
        [("z", datum), ("k", continuation), ("x", channel)] := by
      rw [atGuard]
      exact (send_match_iff _ _).mpr ⟨channel, datum, continuation, rfl, rfl⟩
    exact .apply (.cons (.collection (by decide)
      (MatchBagRel.cons (bs := [("n", .collection .hashBag (guards.eraseIdx l) none), ("z", datum),
          ("k", continuation), ("x", channel)]) l hl guardMatch .nilRest (by simp [mergeBindings, List.find?]))) .nil
      (by simp [mergeBindings])) rfl

private theorem comm_match_iff (source : Pattern) (bindings : Bindings) :
    MatchRel piSumCommRewrite.left source bindings ↔
      ∃ (elements : List Pattern) (tail : Option String) (i : ℕ) (hi : i < elements.length) (j : ℕ)
        (hj : j < (elements.eraseIdx i).length) (guards guards' : List Pattern) (sumTail sumTail' : Option String)
        (k : ℕ) (hk : k < guards.length) (l : ℕ) (hl : l < guards'.length) (channel : Pattern)
        (binder : Option String) (body datum continuation : Pattern),
        source = .collection .hashBag elements tail ∧
          elements[i] = .apply "PiSum" [.collection .hashBag guards sumTail] ∧
          (elements.eraseIdx i)[j] = .apply "PiSum" [.collection .hashBag guards' sumTail'] ∧
          guards[k] = .apply "PiRecv" [channel, .lambda binder body] ∧
          guards'[l] = .apply "PiSend" [channel, datum, continuation] ∧
          bindings = commBindings channel body datum continuation (guards.eraseIdx k) (guards'.eraseIdx l)
            ((elements.eraseIdx i).eraseIdx j) := by
  constructor
  · intro matched
    simp only [piSumCommRewrite] at matched
    cases matched with
    | collection _ bag =>
      cases bag with
      | cons i hi first remaining mergedFirst =>
        obtain ⟨guards, sumTail, k, hk, channel, binder, body, atFirst, atInput, rfl⟩ :=
          (recvSum_match_iff _ _).mp first
        cases remaining with
        | cons j hj second last mergedSecond =>
          obtain ⟨guards', sumTail', l, hl, channel', datum, continuation, atSecond, atOutput, rfl⟩ :=
            (sendSum_match_iff _ _).mp second
          cases last
          simp [mergeBindings, List.find?] at mergedSecond
          subst mergedSecond
          simp [mergeBindings, List.find?] at mergedFirst
          obtain ⟨rfl, rfl⟩ := mergedFirst
          exact ⟨_, _, i, hi, j, hj, guards, guards', sumTail, sumTail', k, hk, l, hl, channel, binder, body, datum,
            continuation, rfl, atFirst, atSecond, atInput, atOutput, rfl⟩
  · rintro ⟨elements, tail, i, hi, j, hj, guards, guards', sumTail, sumTail', k, hk, l, hl, channel, binder, body,
      datum, continuation, rfl, atFirst, atSecond, atInput, atOutput, rfl⟩
    have firstMatch := (recvSum_match_iff _ _).mpr ⟨guards, sumTail, k, hk, channel, binder, body, rfl, atInput, rfl⟩
    have secondMatch := (sendSum_match_iff _ _).mpr
      ⟨guards', sumTail', l, hl, channel, datum, continuation, rfl, atOutput, rfl⟩
    rw [← atFirst] at firstMatch
    rw [← atSecond] at secondMatch
    exact .collection (by decide) (.cons i hi firstMatch
      (MatchBagRel.cons (bs := [("rest", .collection .hashBag ((elements.eraseIdx i).eraseIdx j) none),
          ("n", .collection .hashBag (guards'.eraseIdx l) none), ("z", datum), ("k", continuation),
          ("x", channel)]) j hj secondMatch .nilRest (by simp [mergeBindings, List.find?]))
      (by simp [mergeBindings, List.find?, commBindings]))

private theorem tau_match_iff (source : Pattern) (bindings : Bindings) :
    MatchRel piSumTauRewrite.left source bindings ↔
      ∃ (guards : List Pattern) (sumTail : Option String) (k : ℕ) (hk : k < guards.length) (continuation : Pattern),
        source = .apply "PiSum" [.collection .hashBag guards sumTail] ∧ guards[k] = .apply "PiTau" [continuation] ∧
          bindings = tauBindings continuation (guards.eraseIdx k) := by
  constructor
  · intro matched
    simp only [piSumTauRewrite] at matched
    cases matched with
    | apply args _ =>
      cases args with
      | cons sumMatch last merged =>
        cases last
        cases sumMatch with
        | collection _ bag =>
          cases bag with
          | cons k hk first remaining mergedFirst =>
            obtain ⟨continuation, atSilent, rfl⟩ := (unary_match_iff "PiTau" "k" _ _).mp first
            cases remaining
            simp [mergeBindings, List.find?] at mergedFirst
            subst mergedFirst
            simp [mergeBindings] at merged
            subst merged
            exact ⟨_, _, k, hk, continuation, rfl, atSilent, rfl⟩
  · rintro ⟨guards, sumTail, k, hk, continuation, rfl, atSilent, rfl⟩
    have silentMatch := (unary_match_iff "PiTau" "k" _ _).mpr ⟨continuation, rfl, rfl⟩
    rw [← atSilent] at silentMatch
    exact .apply (.cons (.collection (by decide)
      (MatchBagRel.cons (bs := [("m", .collection .hashBag (guards.eraseIdx k) none), ("k", continuation)]) k hk
        silentMatch .nilRest (by simp [mergeBindings, List.find?]))) .nil (by simp [mergeBindings, tauBindings])) rfl

private theorem par_match_inv {source : Pattern} {bindings : Bindings}
    (matched : MatchRel (.collection .hashBag [.fvar "S"] (some "rest")) source bindings) :
    ∃ (elements : List Pattern) (tail : Option String) (i : ℕ) (hi : i < elements.length),
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

/-! ## What the rules leave -/

theorem comm_apply_exact (channel body datum continuation : Pattern) (others others' rest : List Pattern) :
    applyBindingsForRule piSumCalc piSumCommRewrite
        (commBindings channel body datum continuation others others' rest) =
      .collection .hashBag (instantiateBVar datum body :: continuation :: rest) none := by
  rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide +kernel)]
  simp [piSumCommRewrite, commBindings, applyBindings]

theorem tau_apply_exact (continuation : Pattern) (others : List Pattern) :
    applyBindingsForRule piSumCalc piSumTauRewrite (tauBindings continuation others) = continuation := by
  rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide +kernel)]
  simp [piSumTauRewrite, tauBindings, applyBindings]

theorem parCong_apply_exact (source target : Pattern) (rest : List Pattern) :
    applyBindingsForRule piSumCalc piParCongRewrite
      [("T", target), ("rest", .collection .hashBag rest none), ("S", source)] =
      .collection .hashBag (target :: rest) none := by
  rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide +kernel)]
  simp [piParCongRewrite, piCalc, applyBindings]

theorem resCong_apply_exact (source target : Pattern) :
    applyBindingsForRule piSumCalc piResCongRewrite [("T", target), ("S", source)] =
      .apply "PiNu" [.lambda none target] := by
  rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide +kernel)]
  simp [piResCongRewrite, piCalc, applyBindings]

/-! ## Adequacy -/

private theorem raw_of_stepAt {fuel : ℕ} {source target : Pattern}
    (step : StepAt (engineBasePremises RelationEnv.empty) piSumCalc fuel source target) :
    PiSumRawStep source target := by
  induction fuel using Nat.strong_induction_on generalizing source target with
  | h fuel ih =>
    cases step with
    | @rule innerFuel source target rule initial final member matching premises result =>
      rw [piSumCalc_rewrites] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rw [matchPatternForRule_eq_syntactic] at matching
      have matchRel := matchPattern_iff_matchRel.mp matching
      rcases member with rfl | rfl | rfl | rfl
      · obtain ⟨elements, tail, i, hi, j, hj, guards, guards', sumTail, sumTail', k, hk, l, hl, channel, binder, body,
          datum, continuation, rfl, atFirst, atSecond, atInput, atOutput, rfl⟩ := (comm_match_iff _ _).mp matchRel
        change PremisesAt _ _ _ _ [] _ at premises
        cases premises
        rw [comm_apply_exact] at result
        cases result
        exact .comm i hi j hj k hk l hl channel binder body datum continuation atFirst atSecond atInput atOutput
      · obtain ⟨guards, sumTail, k, hk, continuation, rfl, atSilent, rfl⟩ := (tau_match_iff _ _).mp matchRel
        change PremisesAt _ _ _ _ [] _ at premises
        cases premises
        rw [tau_apply_exact] at result
        subst result
        exact .tau k hk _ atSilent
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
            rw [parCong_apply_exact] at result
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
            rw [resCong_apply_exact] at result
            cases result
            exact .res binder (ih innerFuel (by omega) (by simpa [applyBindings] using inner))

/-- **Every firing of the authored rules is a firing of the specification.** -/
theorem raw_of_step {source target : Pattern}
    (step : Step (engineBasePremises RelationEnv.empty) piSumCalc source target) : PiSumRawStep source target := by
  obtain ⟨fuel, bounded⟩ := step
  exact raw_of_stepAt bounded

/-- **Every firing of the specification is a firing of the authored rules.** -/
theorem step_of_raw {source target : Pattern} (step : PiSumRawStep source target) :
    Step (engineBasePremises RelationEnv.empty) piSumCalc source target := by
  induction step with
  | @comm elements tail i hi j hj guards guards' sumTail sumTail' k hk l hl channel binder body datum continuation
      first second receiving sending =>
    refine ⟨1, .rule (rule := piSumCommRewrite) (by rw [piSumCalc_rewrites]; simp) ?_ (.nil _)
      (comm_apply_exact channel body datum continuation (guards.eraseIdx k) (guards'.eraseIdx l)
        ((elements.eraseIdx i).eraseIdx j))⟩
    rw [matchPatternForRule_eq_syntactic]
    exact matchPattern_iff_matchRel.mpr ((comm_match_iff _ _).mpr
      ⟨_, _, i, hi, j, hj, _, _, _, _, k, hk, l, hl, channel, binder, body, datum, continuation, rfl, first, second,
        receiving, sending, rfl⟩)
  | @tau guards sumTail k hk continuation silent =>
    refine ⟨1, .rule (rule := piSumTauRewrite) (by rw [piSumCalc_rewrites]; simp) ?_ (.nil _)
      (tau_apply_exact continuation (guards.eraseIdx k))⟩
    rw [matchPatternForRule_eq_syntactic]
    exact matchPattern_iff_matchRel.mpr ((tau_match_iff _ _).mpr ⟨_, _, k, hk, continuation, rfl, silent, rfl⟩)
  | @par elements tail i hi target _ ih =>
    obtain ⟨fuel, inner⟩ := ih
    refine ⟨fuel + 1, .rule (rule := piParCongRewrite)
      (initialBindings := [("rest", .collection .hashBag (elements.eraseIdx i) none), ("S", elements[i])])
      (finalBindings := [("T", target), ("rest", .collection .hashBag (elements.eraseIdx i) none),
        ("S", elements[i])]) ?_ ?_ ?_ (parCong_apply_exact _ _ _)⟩
    · rw [piSumCalc_rewrites]; simp
    · rw [matchPatternForRule_eq_syntactic]
      exact matchPattern_iff_matchRel.mpr (.collection (by decide) (.cons i hi .fvar .nilRest rfl))
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
      ?_ ?_ ?_ (resCong_apply_exact source target)⟩
    · rw [piSumCalc_rewrites]; simp
    · rw [matchPatternForRule_eq_syntactic]
      exact matchPattern_iff_matchRel.mpr (.apply (.cons (.lambda .fvar) .nil rfl) rfl)
    · apply PremisesAt.cons
      · apply PremiseAt.congruence (premiseBindings := [("T", target)]) (candidate := target)
        · simpa [applyBindings] using inner
        · simp [matchPattern]
        · rfl
      · exact .nil _

/-- **The authored rules fire exactly as the specification says.** -/
theorem step_iff_raw (source target : Pattern) :
    Step (engineBasePremises RelationEnv.empty) piSumCalc source target ↔ PiSumRawStep source target :=
  ⟨raw_of_step, step_of_raw⟩

end Mettapedia.Languages.ProcessCalculi.PiCalculus.Sums
