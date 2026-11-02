import Mettapedia.Languages.ProcessCalculi.CCS.LanguageDef
import Mettapedia.Languages.ProcessCalculi.Ambient.MobileAmbientsReflection

/-!
# The rule firing of CCS, by occurrence

An independent specification of CCS's rules (`CCSRawStep`), by occurrence index:

- a reaction selects two sums among the components of a parallel composition, an action among the summands of the
  first and the co-action on the same name among the summands of the second, and releases both continuations into
  the composition, the other summands of the two sums discarded;
- a silent step selects a silent summand of a sum and leaves its continuation, the other summands discarded;
- a step happens inside a parallel composition and under a restriction.

The authored rules fire exactly as the specification says (`step_iff_raw`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.CCS

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.Languages.ProcessCalculi.Ambient.Mobile (binary_match_iff)

/-- **The firing of CCS, by occurrence.** -/
inductive CCSRawStep : Pattern → Pattern → Prop where
  /-- `(a.P + M) | (~a.Q + N) | R ⟶ P | Q | R` -/
  | react {elements : List Pattern} {tail : Option String}
      (i : ℕ) (hi : i < elements.length) (j : ℕ) (hj : j < (elements.eraseIdx i).length)
      {guards guards' : List Pattern} {sumTail sumTail' : Option String}
      (k : ℕ) (hk : k < guards.length) (l : ℕ) (hl : l < guards'.length)
      (name continuation continuation' : Pattern)
      (first : elements[i] = .apply "CSum" [.collection .hashBag guards sumTail])
      (second : (elements.eraseIdx i)[j] = .apply "CSum" [.collection .hashBag guards' sumTail'])
      (acting : guards[k] = .apply "CAct" [name, continuation])
      (coacting : guards'[l] = .apply "CCoAct" [name, continuation']) :
      CCSRawStep (.collection .hashBag elements tail)
        (.collection .hashBag (continuation :: continuation' :: (elements.eraseIdx i).eraseIdx j) none)
  /-- `τ.P + M ⟶ P` -/
  | tau {guards : List Pattern} {sumTail : Option String} (k : ℕ) (hk : k < guards.length) (continuation : Pattern)
      (silent : guards[k] = .apply "CTau" [continuation]) :
      CCSRawStep (.apply "CSum" [.collection .hashBag guards sumTail]) continuation
  /-- A step inside a parallel composition. -/
  | par {elements : List Pattern} {tail : Option String} (i : ℕ) (hi : i < elements.length) {target : Pattern}
      (inner : CCSRawStep elements[i] target) :
      CCSRawStep (.collection .hashBag elements tail) (.collection .hashBag (target :: elements.eraseIdx i) none)
  /-- A step under a restriction. -/
  | res (binder : Option String) {source target : Pattern} (inner : CCSRawStep source target) :
      CCSRawStep (.apply "CNu" [.lambda binder source]) (.apply "CNu" [.lambda none target])

/-! ## Matching the rules -/

/-- The bindings of a reaction. -/
def reactBindings (name continuation continuation' : Pattern) (others others' rest : List Pattern) : Bindings :=
  [("q", continuation'), ("n", .collection .hashBag others' none), ("rest", .collection .hashBag rest none),
    ("m", .collection .hashBag others none), ("p", continuation), ("a", name)]

/-- The bindings of a silent step. -/
def tauBindings (continuation : Pattern) (others : List Pattern) : Bindings :=
  [("m", .collection .hashBag others none), ("p", continuation)]

theorem sum_match_iff (guard nameVar continuationVar othersVar : String)
    (distinct : nameVar ≠ continuationVar) (fresh : othersVar ≠ continuationVar ∧ othersVar ≠ nameVar)
    (target : Pattern) (bindings : Bindings) :
    MatchRel (.apply "CSum" [.collection .hashBag [.apply guard [.fvar nameVar, .fvar continuationVar]]
        (some othersVar)]) target bindings ↔
      ∃ (guards : List Pattern) (sumTail : Option String) (k : ℕ) (hk : k < guards.length) (name continuation : Pattern),
        target = .apply "CSum" [.collection .hashBag guards sumTail] ∧ guards[k] = .apply guard [name, continuation] ∧
          bindings = [(othersVar, .collection .hashBag (guards.eraseIdx k) none), (continuationVar, continuation),
            (nameVar, name)] := by
  have continuationFresh : (continuationVar == othersVar) = false := by
    simpa [beq_eq_false_iff_ne] using fresh.1.symm
  have nameFresh : (nameVar == othersVar) = false := by
    simpa [beq_eq_false_iff_ne] using fresh.2.symm
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
            obtain ⟨name, continuation, atGuard, rfl⟩ :=
              (binary_match_iff guard nameVar continuationVar distinct _ _).mp first
            cases remaining
            simp [mergeBindings, List.find?, continuationFresh, nameFresh] at mergedFirst
            subst mergedFirst
            simp [mergeBindings] at merged
            subst merged
            exact ⟨_, _, k, hk, name, continuation, rfl, atGuard, rfl⟩
  · rintro ⟨guards, sumTail, k, hk, name, continuation, rfl, atGuard, rfl⟩
    have guardMatch : MatchRel (.apply guard [.fvar nameVar, .fvar continuationVar]) guards[k]
        [(continuationVar, continuation), (nameVar, name)] := by
      rw [atGuard]
      exact (binary_match_iff guard nameVar continuationVar distinct _ _).mpr ⟨name, continuation, rfl, rfl⟩
    exact .apply (.cons (.collection (by decide)
      (MatchBagRel.cons (bs := [(othersVar, .collection .hashBag (guards.eraseIdx k) none),
          (continuationVar, continuation), (nameVar, name)]) k hk guardMatch .nilRest
        (by simp [mergeBindings, List.find?, continuationFresh, nameFresh]))) .nil (by simp [mergeBindings])) rfl

theorem react_match_iff (source : Pattern) (bindings : Bindings) :
    MatchRel ccsReactRewrite.left source bindings ↔
      ∃ (elements : List Pattern) (tail : Option String) (i : ℕ) (hi : i < elements.length) (j : ℕ)
        (hj : j < (elements.eraseIdx i).length) (guards guards' : List Pattern) (sumTail sumTail' : Option String)
        (k : ℕ) (hk : k < guards.length) (l : ℕ) (hl : l < guards'.length) (name continuation continuation' : Pattern),
        source = .collection .hashBag elements tail ∧
          elements[i] = .apply "CSum" [.collection .hashBag guards sumTail] ∧
          (elements.eraseIdx i)[j] = .apply "CSum" [.collection .hashBag guards' sumTail'] ∧
          guards[k] = .apply "CAct" [name, continuation] ∧ guards'[l] = .apply "CCoAct" [name, continuation'] ∧
          bindings = reactBindings name continuation continuation' (guards.eraseIdx k) (guards'.eraseIdx l)
            ((elements.eraseIdx i).eraseIdx j) := by
  constructor
  · intro matched
    simp only [ccsReactRewrite] at matched
    cases matched with
    | collection _ bag =>
      cases bag with
      | cons i hi first remaining mergedFirst =>
        obtain ⟨guards, sumTail, k, hk, name, continuation, atFirst, atAction, rfl⟩ :=
          (sum_match_iff "CAct" "a" "p" "m" (by decide) (by decide) _ _).mp first
        cases remaining with
        | cons j hj second last mergedSecond =>
          obtain ⟨guards', sumTail', l, hl, name', continuation', atSecond, atCoaction, rfl⟩ :=
            (sum_match_iff "CCoAct" "a" "q" "n" (by decide) (by decide) _ _).mp second
          cases last
          simp [mergeBindings, List.find?] at mergedSecond
          subst mergedSecond
          simp [mergeBindings, List.find?] at mergedFirst
          obtain ⟨rfl, rfl⟩ := mergedFirst
          exact ⟨_, _, i, hi, j, hj, guards, guards', sumTail, sumTail', k, hk, l, hl, name, continuation,
            continuation', rfl, atFirst, atSecond, atAction, atCoaction, rfl⟩
  · rintro ⟨elements, tail, i, hi, j, hj, guards, guards', sumTail, sumTail', k, hk, l, hl, name, continuation,
      continuation', rfl, atFirst, atSecond, atAction, atCoaction, rfl⟩
    have firstMatch := (sum_match_iff "CAct" "a" "p" "m" (by decide) (by decide) _ _).mpr
      ⟨guards, sumTail, k, hk, name, continuation, rfl, atAction, rfl⟩
    have secondMatch := (sum_match_iff "CCoAct" "a" "q" "n" (by decide) (by decide) _ _).mpr
      ⟨guards', sumTail', l, hl, name, continuation', rfl, atCoaction, rfl⟩
    rw [← atFirst] at firstMatch
    rw [← atSecond] at secondMatch
    exact .collection (by decide) (.cons i hi firstMatch
      (MatchBagRel.cons (bs := [("rest", .collection .hashBag ((elements.eraseIdx i).eraseIdx j) none),
          ("n", .collection .hashBag (guards'.eraseIdx l) none), ("q", continuation'), ("a", name)]) j hj secondMatch
        .nilRest (by simp [mergeBindings, List.find?])) (by simp [mergeBindings, List.find?, reactBindings]))

theorem unary_match_iff (label var : String) (target : Pattern) (bindings : Bindings) :
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

theorem tau_match_iff (source : Pattern) (bindings : Bindings) :
    MatchRel ccsTauRewrite.left source bindings ↔
      ∃ (guards : List Pattern) (sumTail : Option String) (k : ℕ) (hk : k < guards.length) (continuation : Pattern),
        source = .apply "CSum" [.collection .hashBag guards sumTail] ∧ guards[k] = .apply "CTau" [continuation] ∧
          bindings = tauBindings continuation (guards.eraseIdx k) := by
  constructor
  · intro matched
    simp only [ccsTauRewrite] at matched
    cases matched with
    | apply args _ =>
      cases args with
      | cons sumMatch last merged =>
        cases last
        cases sumMatch with
        | collection _ bag =>
          cases bag with
          | cons k hk first remaining mergedFirst =>
            obtain ⟨continuation, atSilent, rfl⟩ := (unary_match_iff "CTau" "p" _ _).mp first
            cases remaining
            simp [mergeBindings, List.find?] at mergedFirst
            subst mergedFirst
            simp [mergeBindings] at merged
            subst merged
            exact ⟨_, _, k, hk, continuation, rfl, atSilent, rfl⟩
  · rintro ⟨guards, sumTail, k, hk, continuation, rfl, atSilent, rfl⟩
    have silentMatch := (unary_match_iff "CTau" "p" _ _).mpr ⟨continuation, rfl, rfl⟩
    rw [← atSilent] at silentMatch
    exact .apply (.cons (.collection (by decide)
      (MatchBagRel.cons (bs := [("m", .collection .hashBag (guards.eraseIdx k) none), ("p", continuation)]) k hk
        silentMatch .nilRest (by simp [mergeBindings, List.find?]))) .nil (by simp [mergeBindings, tauBindings])) rfl

theorem par_match_inv {source : Pattern} {bindings : Bindings}
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

theorem restriction_match_inv {source : Pattern} {bindings : Bindings}
    (matched : MatchRel (.apply "CNu" [.lambda none (.fvar "S")]) source bindings) :
    ∃ binder body, source = .apply "CNu" [.lambda binder body] ∧ bindings = [("S", body)] := by
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

theorem react_apply_exact {language : LanguageDef} (name continuation continuation' : Pattern) (others others' rest : List Pattern) :
    applyBindingsForRule language ccsReactRewrite
        (reactBindings name continuation continuation' others others' rest) =
      .collection .hashBag (continuation :: continuation' :: rest) none := by
  rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide +kernel)]
  simp [ccsReactRewrite, reactBindings, applyBindings]

theorem tau_apply_exact {language : LanguageDef} (continuation : Pattern) (others : List Pattern) :
    applyBindingsForRule language ccsTauRewrite (tauBindings continuation others) = continuation := by
  rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide +kernel)]
  simp [ccsTauRewrite, tauBindings, applyBindings]

theorem parCong_apply_exact {language : LanguageDef} (source target : Pattern) (rest : List Pattern) :
    applyBindingsForRule language ccsParCongRewrite
      [("T", target), ("rest", .collection .hashBag rest none), ("S", source)] =
      .collection .hashBag (target :: rest) none := by
  rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide +kernel)]
  simp [ccsParCongRewrite, applyBindings]

theorem resCong_apply_exact {language : LanguageDef} (source target : Pattern) :
    applyBindingsForRule language ccsResCongRewrite [("T", target), ("S", source)] =
      .apply "CNu" [.lambda none target] := by
  rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide +kernel)]
  simp [ccsResCongRewrite, applyBindings]

/-! ## Adequacy -/

section Adequacy

variable {language : LanguageDef}
  (rewritesIs : language.rewrites = [ccsReactRewrite, ccsTauRewrite, ccsParCongRewrite, ccsResCongRewrite])

include rewritesIs in

private theorem raw_of_stepAt_of {fuel : ℕ} {source target : Pattern}
    (step : StepAt (engineBasePremises RelationEnv.empty) language fuel source target) :
    CCSRawStep source target := by
  induction fuel using Nat.strong_induction_on generalizing source target with
  | h fuel ih =>
    cases step with
    | @rule innerFuel source target rule initial final member matching premises result =>
      rw [rewritesIs] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rw [matchPatternForRule_eq_syntactic] at matching
      have matchRel := matchPattern_iff_matchRel.mp matching
      rcases member with rfl | rfl | rfl | rfl
      · obtain ⟨elements, tail, i, hi, j, hj, guards, guards', sumTail, sumTail', k, hk, l, hl, name, continuation,
          continuation', rfl, atFirst, atSecond, atAction, atCoaction, rfl⟩ := (react_match_iff _ _).mp matchRel
        change PremisesAt _ _ _ _ [] _ at premises
        cases premises
        rw [react_apply_exact] at result
        cases result
        exact .react i hi j hj k hk l hl name continuation continuation' atFirst atSecond atAction atCoaction
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
      · change MatchRel (.apply "CNu" [.lambda none (.fvar "S")]) source initial at matchRel
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

include rewritesIs in
/-- **Every firing of the authored rules is a firing of the specification.** -/
theorem raw_of_step_of {source target : Pattern}
    (step : Step (engineBasePremises RelationEnv.empty) language source target) : CCSRawStep source target := by
  obtain ⟨fuel, bounded⟩ := step
  exact raw_of_stepAt_of rewritesIs bounded

include rewritesIs in
/-- **Every firing of the specification is a firing of the authored rules.** -/
theorem step_of_raw_of {source target : Pattern} (step : CCSRawStep source target) :
    Step (engineBasePremises RelationEnv.empty) language source target := by
  induction step with
  | @react elements tail i hi j hj guards guards' sumTail sumTail' k hk l hl name continuation continuation' first
      second acting coacting =>
    refine ⟨1, .rule (rule := ccsReactRewrite) (by rw [rewritesIs]; simp) ?_ (.nil _)
      (react_apply_exact name continuation continuation' (guards.eraseIdx k) (guards'.eraseIdx l)
        ((elements.eraseIdx i).eraseIdx j))⟩
    rw [matchPatternForRule_eq_syntactic]
    exact matchPattern_iff_matchRel.mpr ((react_match_iff _ _).mpr
      ⟨_, _, i, hi, j, hj, _, _, _, _, k, hk, l, hl, name, continuation, continuation', rfl, first, second, acting,
        coacting, rfl⟩)
  | @tau guards sumTail k hk continuation silent =>
    refine ⟨1, .rule (rule := ccsTauRewrite) (by rw [rewritesIs]; simp) ?_ (.nil _)
      (tau_apply_exact continuation (guards.eraseIdx k))⟩
    rw [matchPatternForRule_eq_syntactic]
    exact matchPattern_iff_matchRel.mpr ((tau_match_iff _ _).mpr ⟨_, _, k, hk, continuation, rfl, silent, rfl⟩)
  | @par elements tail i hi target _ ih =>
    obtain ⟨fuel, inner⟩ := ih
    refine ⟨fuel + 1, .rule (rule := ccsParCongRewrite)
      (initialBindings := [("rest", .collection .hashBag (elements.eraseIdx i) none), ("S", elements[i])])
      (finalBindings := [("T", target), ("rest", .collection .hashBag (elements.eraseIdx i) none),
        ("S", elements[i])]) ?_ ?_ ?_ (parCong_apply_exact _ _ _)⟩
    · rw [rewritesIs]; simp
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
    refine ⟨fuel + 1, .rule (rule := ccsResCongRewrite)
      (initialBindings := [("S", source)]) (finalBindings := [("T", target), ("S", source)])
      ?_ ?_ ?_ (resCong_apply_exact source target)⟩
    · rw [rewritesIs]; simp
    · rw [matchPatternForRule_eq_syntactic]
      exact matchPattern_iff_matchRel.mpr (.apply (.cons (.lambda .fvar) .nil rfl) rfl)
    · apply PremisesAt.cons
      · apply PremiseAt.congruence (premiseBindings := [("T", target)]) (candidate := target)
        · simpa [applyBindings] using inner
        · simp [matchPattern]
        · rfl
      · exact .nil _

include rewritesIs in
/-- **The authored rules fire exactly as the specification says**, in any language with CCS's rules. -/
theorem step_iff_raw_of (source target : Pattern) :
    Step (engineBasePremises RelationEnv.empty) language source target ↔ CCSRawStep source target :=
  ⟨raw_of_step_of rewritesIs, step_of_raw_of rewritesIs⟩

end Adequacy

/-- **The authored rules of CCS fire exactly as the specification says.** -/
theorem step_iff_raw (source target : Pattern) :
    Step (engineBasePremises RelationEnv.empty) ccsCalc source target ↔ CCSRawStep source target :=
  step_iff_raw_of ccsCalc_rewrites source target

theorem raw_of_step {source target : Pattern}
    (step : Step (engineBasePremises RelationEnv.empty) ccsCalc source target) : CCSRawStep source target :=
  raw_of_step_of ccsCalc_rewrites step

theorem step_of_raw {source target : Pattern} (step : CCSRawStep source target) :
    Step (engineBasePremises RelationEnv.empty) ccsCalc source target :=
  step_of_raw_of ccsCalc_rewrites step


end Mettapedia.Languages.ProcessCalculi.CCS
