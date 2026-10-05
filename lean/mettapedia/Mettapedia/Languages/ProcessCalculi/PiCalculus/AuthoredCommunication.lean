import Mettapedia.Languages.ProcessCalculi.PiCalculus.BindingAgreement
import Mettapedia.Languages.ProcessCalculi.PiCalculus.Interaction
import Mettapedia.OSLF.MeTTaIL.MatchSpec

/-!
# Authored pi communication and named substitution

The matcher and binding applier of the authored communication rule return
exactly the substituted continuation and the untouched parallel residue.
The comparison uses the general named-to-locally-nameless binding laws,
including colliding and shadowing binders.
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

/-- Captures selected by the authored input/output match. -/
def piCommMatchedBindings (channel body datum : Pattern) (rest : List Pattern) : Bindings :=
  [("z", datum), ("rest", .collection .hashBag rest none), ("body", body), ("x", channel)]

private theorem exchange_matchRel (listener : String) (channel body datum : Pattern) (rest : List Pattern) :
    MatchRel
      (.collection .hashBag [
        .apply listener [.fvar "x", .lambda none (.fvar "body")],
        .apply "PiOut" [.fvar "x", .fvar "z"]] (some "rest"))
      (.collection .hashBag
        ([.apply listener [channel, .lambda none body], .apply "PiOut" [channel, datum]] ++ rest) none)
      (piCommMatchedBindings channel body datum rest) := by
  apply MatchRel.collection (by decide)
  apply MatchBagRel.cons 0 (by simp)
  · apply MatchRel.apply
    · apply MatchArgsRel.cons MatchRel.fvar
      · apply MatchArgsRel.cons
        · exact MatchRel.lambda MatchRel.fvar
        · exact MatchArgsRel.nil
        · rfl
      · rfl
    · rfl
  · apply MatchBagRel.cons 0 (by simp)
    · apply MatchRel.apply
      · apply MatchArgsRel.cons MatchRel.fvar
        · exact MatchArgsRel.cons MatchRel.fvar MatchArgsRel.nil rfl
        · rfl
      · rfl
    · exact MatchBagRel.nilRest
    · rfl
  · simp [piCommMatchedBindings, mergeBindings]



/-- The concrete COMM captures are accepted by the actual rule matcher. -/
theorem piComm_match_exact (channel body datum : Pattern) (rest : List Pattern) :
    piCommMatchedBindings channel body datum rest ∈ matchPatternForRule piCalc piCommRewrite
      (.collection .hashBag
        ([.apply "PiInp" [channel, .lambda none body], .apply "PiOut" [channel, datum]] ++ rest) none) := by
  rw [matchPatternForRule_eq_syntactic]
  exact matchPattern_iff_matchRel.mpr (exchange_matchRel "PiInp" channel body datum rest)

/-- Binding application consumes the input binder and preserves the residue. -/
theorem piComm_apply_exact (channel body datum : Pattern) (rest : List Pattern) :
    applyBindingsForRule piCalc piCommRewrite (piCommMatchedBindings channel body datum rest) =
      .collection .hashBag (instantiateBVar datum body :: rest) none := by
  rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide +kernel)]
  simp [piCommRewrite, piCalc, piCommMatchedBindings, applyBindings]

/-- One authored COMM firing, with no interpreter unfolding of its body. -/
theorem piComm_step (channel body datum : Pattern) (rest : List Pattern) :
    Step (engineBasePremises RelationEnv.empty) piCalc
      (.collection .hashBag
        ([.apply "PiInp" [channel, .lambda none body], .apply "PiOut" [channel, datum]] ++ rest) none)
      (.collection .hashBag (instantiateBVar datum body :: rest) none) := by
  exact ⟨1, .rule (rule := piCommRewrite) (by rw [piCalc_rewrites]; exact List.mem_cons_self)
    (piComm_match_exact channel body datum rest) (.nil _)
    (piComm_apply_exact channel body datum rest)⟩

/-- Every named COMM instance produces the exact capture-avoiding reduct. -/
theorem piComm_named_step (channel bound datum : Name) (P : Process) (rest : List Pattern) :
    Step (engineBasePremises RelationEnv.empty) piCalc
      (.collection .hashBag
        ([piToPattern (.input channel bound P), piToPattern (.output channel datum)] ++ rest) none)
      (.collection .hashBag (piToPattern (P.substitute bound datum) :: rest) none) := by
  rw [← piToPattern_instantiate_substitute]
  exact piComm_step (.fvar channel) (closeFVar 0 bound (piToPattern P)) (.fvar datum) rest

/-- The restriction schema captures the body in its existing binder context. -/
theorem piResCong_match_exact (body : Pattern) :
    [("S", body)] ∈ matchPatternForRule piCalc piResCongRewrite
      (.apply "PiNu" [.lambda none body]) := by
  rw [matchPatternForRule_eq_syntactic]
  apply matchPattern_iff_matchRel.mpr
  exact .apply (.cons (.lambda .fvar) .nil rfl) rfl

/-- A premise result is returned under the same restriction binder. -/
theorem piResCong_apply_exact (source target : Pattern) :
    applyBindingsForRule piCalc piResCongRewrite [("T", target), ("S", source)] =
      .apply "PiNu" [.lambda none target] := by
  rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide +kernel)]
  simp [piResCongRewrite, piCalc, applyBindings]

/-- Every bounded body step lifts through one authored restriction context. -/
theorem piResCong_stepAt {fuel : Nat} {source target : Pattern}
    (step : StepAt (engineBasePremises RelationEnv.empty) piCalc fuel source target) :
    StepAt (engineBasePremises RelationEnv.empty) piCalc (fuel + 1)
      (.apply "PiNu" [.lambda none source])
      (.apply "PiNu" [.lambda none target]) := by
  apply StepAt.rule (rule := piResCongRewrite)
    (initialBindings := [("S", source)])
    (finalBindings := [("T", target), ("S", source)])
  · rw [piCalc_rewrites]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · exact piResCong_match_exact source
  · apply PremisesAt.cons (middle := [("T", target), ("S", source)])
    · apply PremiseAt.congruence
        (premiseBindings := [("T", target)]) (candidate := target)
      · simpa [applyBindings] using step
      · simp [matchPattern]
      · simp [mergeBindings]
    · exact .nil _
  · exact piResCong_apply_exact source target

/-- Restriction preserves the least authored step relation. -/
theorem piResCong_step {source target : Pattern}
    (step : Step (engineBasePremises RelationEnv.empty) piCalc source target) :
    Step (engineBasePremises RelationEnv.empty) piCalc
      (.apply "PiNu" [.lambda none source])
      (.apply "PiNu" [.lambda none target]) := by
  obtain ⟨fuel, step⟩ := step
  exact ⟨fuel + 1, piResCong_stepAt step⟩


/-- Every actual restricted step reflects to its actual body endpoint. -/
theorem piResCong_step_iff (source target : Pattern) :
    Step (engineBasePremises RelationEnv.empty) piCalc
      (.apply "PiNu" [.lambda none source])
      (.apply "PiNu" [.lambda none target]) ↔
    Step (engineBasePremises RelationEnv.empty) piCalc source target := by
  constructor
  · rintro ⟨fuel, step⟩
    cases step with
    | @rule fuel _ _ rule initial final member matching premises result =>
      rw [piCalc_rewrites] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · rw [matchPatternForRule_eq_syntactic] at matching
        simp [piCommRewrite, piCalc, matchPattern] at matching
      · rw [matchPatternForRule_eq_syntactic] at matching
        simp [piParCongRewrite, piCalc, matchPattern] at matching
      · rw [matchPatternForRule_eq_syntactic] at matching
        have initialEq : initial = [("S", source)] := by
          simpa [piResCongRewrite, piCalc, matchPattern, matchArgs, mergeBindings] using matching
        subst initial
        change PremisesAt _ _ _ _ [.congruence (.fvar "S") (.fvar "T")] _ at premises
        cases premises with
        | cons premise tail =>
          cases tail
          cases premise with
          | @congruence _ _ premiseBindings _ _ _ candidate inner matched merged =>
            have bindingsEq : premiseBindings = [("T", candidate)] := by
              simpa [matchPattern] using matched
            subst premiseBindings
            have finalEq : final = [("T", candidate), ("S", source)] := by
              simpa [mergeBindings] using merged.symm
            subst final
            rw [piResCong_apply_exact] at result
            have endpoint : candidate = target := by simpa using result
            subst candidate
            exact ⟨fuel, by simpa [applyBindings] using inner⟩
      · rw [matchPatternForRule_eq_syntactic] at matching
        simp [piRepCommRewrite, piCalc, matchPattern] at matching
  · exact piResCong_step


/-- A guarded server and one message have the same captures as an ordinary input. -/
theorem piRepComm_match_exact (channel body datum : Pattern) (rest : List Pattern) :
    piCommMatchedBindings channel body datum rest ∈ matchPatternForRule piCalc piRepCommRewrite
      (.collection .hashBag
        ([.apply "PiRep" [channel, .lambda none body], .apply "PiOut" [channel, datum]] ++ rest) none) := by
  rw [matchPatternForRule_eq_syntactic]
  exact matchPattern_iff_matchRel.mpr (exchange_matchRel "PiRep" channel body datum rest)

/-- A server firing substitutes only its released body and retains the original server. -/
theorem piRepComm_apply_exact (channel body datum : Pattern) (rest : List Pattern) :
    applyBindingsForRule piCalc piRepCommRewrite (piCommMatchedBindings channel body datum rest) =
      .collection .hashBag
        ([instantiateBVar datum body, .apply "PiRep" [channel, .lambda none body]] ++ rest) none := by
  rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide +kernel)]
  simp [piRepCommRewrite, piCalc, piCommMatchedBindings, applyBindings]

/-- The authored guarded-server firing preserves the parallel residue. -/
theorem piRepComm_step (channel body datum : Pattern) (rest : List Pattern) :
    Step (engineBasePremises RelationEnv.empty) piCalc
      (.collection .hashBag
        ([.apply "PiRep" [channel, .lambda none body], .apply "PiOut" [channel, datum]] ++ rest) none)
      (.collection .hashBag
        ([instantiateBVar datum body, .apply "PiRep" [channel, .lambda none body]] ++ rest) none) := by
  exact ⟨1, .rule (rule := piRepCommRewrite)
    (by rw [piCalc_rewrites]; simp)
    (piRepComm_match_exact channel body datum rest) (.nil _)
    (piRepComm_apply_exact channel body datum rest)⟩

/-- Capture-avoiding named server communication has the exact authored endpoint. -/
theorem piRepComm_named_step (channel bound datum : Name) (P : Process) (rest : List Pattern) :
    Step (engineBasePremises RelationEnv.empty) piCalc
      (.collection .hashBag
        ([piToPattern (.replicate channel bound P), piToPattern (.output channel datum)] ++ rest) none)
      (.collection .hashBag
        ([piToPattern (P.substitute bound datum), piToPattern (.replicate channel bound P)] ++ rest) none) := by
  rw [← piToPattern_instantiate_substitute]
  exact piRepComm_step (.fvar channel) (closeFVar 0 bound (piToPattern P)) (.fvar datum) rest

theorem piParCong_match_exact (source : Pattern) (rest : List Pattern) :
    [("rest", .collection .hashBag rest none), ("S", source)] ∈
      matchPatternForRule piCalc piParCongRewrite (.collection .hashBag (source :: rest) none) := by
  rw [matchPatternForRule_eq_syntactic]
  exact matchPattern_iff_matchRel.mpr
    (.collection (by decide) (.cons 0 (by simp) .fvar .nilRest rfl))

theorem piParCong_apply_exact (source target : Pattern) (rest : List Pattern) :
    applyBindingsForRule piCalc piParCongRewrite
      [("T", target), ("rest", .collection .hashBag rest none), ("S", source)] =
      .collection .hashBag (target :: rest) none := by
  rw [applyBindingsForRule_eq_applyBindings _ _ _ (by decide +kernel)]
  simp [piParCongRewrite, piCalc, applyBindings]

theorem piParCong_step {source target : Pattern} (rest : List Pattern)
    (step : Step (engineBasePremises RelationEnv.empty) piCalc source target) :
    Step (engineBasePremises RelationEnv.empty) piCalc
      (.collection .hashBag (source :: rest) none)
      (.collection .hashBag (target :: rest) none) := by
  obtain ⟨fuel, step⟩ := step
  refine ⟨fuel + 1, .rule (rule := piParCongRewrite)
    (initialBindings := [("rest", .collection .hashBag rest none), ("S", source)])
    (finalBindings := [("T", target), ("rest", .collection .hashBag rest none), ("S", source)])
    ?_ (piParCong_match_exact source rest) ?_ (piParCong_apply_exact source target rest)⟩
  · rw [piCalc_rewrites]; simp
  · apply PremisesAt.cons (middle := [("T", target), ("rest", .collection .hashBag rest none), ("S", source)])
    · apply PremiseAt.congruence (premiseBindings := [("T", target)]) (candidate := target)
      · simpa [applyBindings] using step
      · simp [matchPattern]
      · simp [mergeBindings]
    · exact .nil _


end Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
