import Mettapedia.Languages.ProcessCalculi.PiCalculus.AuthoredStepReflection
import Mettapedia.OSLF.MeTTaIL.ContextualStepFuel

/-!
# A complete finite internal frontier for authored pi

Only parallel components and restriction bodies are active contexts. Their
finite nesting gives a computable source-dependent bound for the existing
contextual executor. At this bound the executor returns every internal
successor and invents none. The membership theorem does not count derivations;
the executor's list is retained without deduplication. This is an internal
frontier; equation saturation is not enumerated by this list.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Interaction

mutual
  /-- One unit for a possible root firing, plus the deepest active context. -/
  def piContextDepth : Pattern → Nat
    | .apply "PiNu" [.lambda _ body] => piContextDepth body + 1
    | .collection .hashBag elements _ => piContextDepthList elements + 1
    | _ => 1

  def piContextDepthList : List Pattern → Nat
    | [] => 0
    | first :: rest => max (piContextDepth first) (piContextDepthList rest)
end

theorem piContextDepthList_member {elements : List Pattern} {element : Pattern}
    (member : element ∈ elements) : piContextDepth element ≤ piContextDepthList elements := by
  induction elements with
  | nil => cases member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | present
    · exact Nat.le_max_left _ _
    · exact (ih present).trans (Nat.le_max_right _ _)

/-- Every occurrence reduction is executed at the bound computed from its source. -/
theorem PiRawStep.bounded {source target : Pattern} (firing : PiRawStep source target) :
    StepAt (engineBasePremises RelationEnv.empty) piCalc (piContextDepth source) source target := by
  induction firing with
  | @comm elements tail i hi j hj channel binder body datum input output =>
    have root : StepAt (engineBasePremises RelationEnv.empty) piCalc 1
        (.collection .hashBag elements tail)
        (.collection .hashBag
          (instantiateBVar datum body :: (elements.eraseIdx i).eraseIdx j) none) := by
      apply StepAt.rule (rule := piCommRewrite)
        (initialBindings := piCommMatchedBindings channel body datum ((elements.eraseIdx i).eraseIdx j))
        (finalBindings := piCommMatchedBindings channel body datum ((elements.eraseIdx i).eraseIdx j))
      · rw [piCalc_rewrites]; simp
      · rw [matchPatternForRule_eq_syntactic]
        exact piExchange_selected_match "PiInp" i hi j hj channel binder body datum input output
      · exact .nil _
      · exact piComm_apply_exact channel body datum _
    exact root.mono_fuel (by change 1 ≤ piContextDepthList elements + 1; omega)
  | @repComm elements tail i hi j hj channel binder body datum input output =>
    have root : StepAt (engineBasePremises RelationEnv.empty) piCalc 1
        (.collection .hashBag elements tail)
        (.collection .hashBag
          ([instantiateBVar datum body, .apply "PiRep" [channel, .lambda none body]] ++
            (elements.eraseIdx i).eraseIdx j) none) := by
      apply StepAt.rule (rule := piRepCommRewrite)
        (initialBindings := piCommMatchedBindings channel body datum ((elements.eraseIdx i).eraseIdx j))
        (finalBindings := piCommMatchedBindings channel body datum ((elements.eraseIdx i).eraseIdx j))
      · rw [piCalc_rewrites]; simp
      · rw [matchPatternForRule_eq_syntactic]
        exact piExchange_selected_match "PiRep" i hi j hj channel binder body datum input output
      · exact .nil _
      · exact piRepComm_apply_exact channel body datum _
    exact root.mono_fuel (by change 1 ≤ piContextDepthList elements + 1; omega)
  | @par elements tail i hi target _ ih =>
    have inner := ih.mono_fuel (piContextDepthList_member (List.getElem_mem hi))
    change StepAt _ _ (piContextDepthList elements + 1) _ _
    apply StepAt.rule (rule := piParCongRewrite)
      (initialBindings := [("rest", .collection .hashBag (elements.eraseIdx i) none), ("S", elements[i])])
      (finalBindings := [("T", target), ("rest", .collection .hashBag (elements.eraseIdx i) none),
        ("S", elements[i])])
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
    · exact piParCong_apply_exact _ _ _
  | @res binder source target _ ih =>
    change StepAt _ _ (piContextDepth source + 1) _ _
    apply StepAt.rule (rule := piResCongRewrite)
      (initialBindings := [("S", source)]) (finalBindings := [("T", target), ("S", source)])
    · rw [piCalc_rewrites]; simp
    · rw [matchPatternForRule_eq_syntactic]
      exact matchPattern_iff_matchRel.mpr (.apply (.cons (.lambda .fvar) .nil rfl) rfl)
    · apply PremisesAt.cons
      · apply PremiseAt.congruence (premiseBindings := [("T", target)]) (candidate := target)
        · simpa [applyBindings] using ih
        · simp [matchPattern]
        · rfl
      · exact .nil _
    · exact piResCong_apply_exact source target

/-- Exhaustiveness and soundness concern the unbounded authored relation. -/
theorem pi_complete_frontier_iff_step (source target : Pattern) :
    target ∈ piCalcReducts (piContextDepth source) source ↔
      Step (engineBasePremises RelationEnv.empty) piCalc source target := by
  constructor
  · intro member
    exact ⟨_, mem_rewriteAt_iff_stepAt.mp member⟩
  · intro firing
    exact mem_rewriteAt_iff_stepAt.mpr (piRawStep_of_step firing).bounded

def decideInternalStep (source target : Pattern) :
    Decidable (Step (engineBasePremises RelationEnv.empty) piCalc source target) :=
  decidable_of_iff (target ∈ piCalcReducts (piContextDepth source) source)
    (pi_complete_frontier_iff_step source target)

end Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance
