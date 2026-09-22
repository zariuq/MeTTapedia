import Mettapedia.OSLF.Framework.WMCalculusEncoding

/-!
# WM calculus: contextual steps on terms and on patterns

`WMContextStep` is the least relation on sorted WM terms containing the root
`WMStep` and closed under every argument position of `Revise`, `Extract` and
`Combine`.  On encoded terms it coincides with one step of the authored
contextual presentation `wmExtVertexLanguageDefWithCong wmExtVertexMinimal`:
the five core rules plus one `Premise.congruence` rule per argument position
(`wmContextStep_iff`, `wmContextStepStar_iff`).  Completeness inverts a
bounded contextual derivation by induction on its depth: a core rule is a
root `WMStep` (`wmStep_complete`), a congruence rule exposes a derivation one
level shallower for the argument it rewrites.

`WMTermCongruence` names the sort-indexed relations closed under every
constructor position; each one containing the root steps contains every
contextual step (`WMTermCongruence.holds_of_contextStep`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.WMCalculusContextEncoding

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.LangMorphism
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef
open Mettapedia.OSLF.Framework.WMCalculusOSLFBridge
open Mettapedia.OSLF.Framework.WMCalculusEncoding
open Mettapedia.OSLF.Framework.WMCalculusContextClosure

/-! ## Authored binary congruence rules -/

/-- A rule `c(X, Y) ⇒ c(X', Y)` whose only premise is `X ⇒ X'`. -/
structure LeftCongruenceShape (rule : RewriteRule) (c X Y X' : String) : Prop where
  left : rule.left = .apply c [.fvar X, .fvar Y]
  premises : rule.premises = [.congruence (.fvar X) (.fvar X')]
  right : rule.right = .apply c [.fvar X', .fvar Y]
  aligned : ruleDepthAligned rule = true
  distinct : X ≠ Y
  fresh_left : X' ≠ X
  fresh_right : X' ≠ Y

/-- A rule `c(X, Y) ⇒ c(X, Y')` whose only premise is `Y ⇒ Y'`. -/
structure RightCongruenceShape (rule : RewriteRule) (c X Y Y' : String) : Prop where
  left : rule.left = .apply c [.fvar X, .fvar Y]
  premises : rule.premises = [.congruence (.fvar Y) (.fvar Y')]
  right : rule.right = .apply c [.fvar X, .fvar Y']
  aligned : ruleDepthAligned rule = true
  distinct : X ≠ Y
  fresh_left : Y' ≠ X
  fresh_right : Y' ≠ Y

theorem mem_matchPattern_binary {c X Y : String} (distinct : X ≠ Y)
    {term : Pattern} {bindings : Bindings} :
    bindings ∈ matchPattern (.apply c [.fvar X, .fvar Y]) term ↔
      ∃ first second, term = .apply c [first, second] ∧
        bindings = [(Y, second), (X, first)] := by
  constructor
  · intro member
    cases term with
    | apply c' arguments =>
        rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, rest⟩⟩⟩ <;>
          simp [matchPattern, matchArgs, mergeBindings, distinct] at member
        obtain ⟨rfl, rfl⟩ := member
        exact ⟨first, second, rfl, rfl⟩
    | _ => simp [matchPattern] at member
  · rintro ⟨first, second, rfl, rfl⟩
    simp [matchPattern, matchArgs, mergeBindings, distinct]

variable {base : BasePremiseEvaluator} {lang : LanguageDef} {rule : RewriteRule}

/-- A left congruence rule lifts a step of the first argument. -/
theorem LeftCongruenceShape.step {c X Y X' : String}
    (shape : LeftCongruenceShape rule c X Y X') (member : rule ∈ lang.rewrites)
    {first first' : Pattern} (second : Pattern) (step : Step base lang first first') :
    Step base lang (.apply c [first, second]) (.apply c [first', second]) := by
  refine step_of_single_congruence_rule
    (initialBindings := [(Y, second), (X, first)])
    (finalBindings := [(X', first'), (Y, second), (X, first)])
    (premiseBindings := [(X', first')])
    (premiseSource := .fvar X) (premiseTarget := .fvar X') (candidate := first')
    member ?_ shape.premises ?_ ?_ ?_ ?_
  · rw [matchPatternForRule_eq_syntactic, shape.left]
    exact (mem_matchPattern_binary shape.distinct).mpr ⟨_, _, rfl, rfl⟩
  · simpa [applyBindings, shape.distinct.symm] using step
  · simp [matchPattern]
  · simp [mergeBindings, shape.fresh_left.symm, shape.fresh_right.symm]
  · rw [applyBindingsForRule_eq_applyBindings _ _ _ shape.aligned, shape.right]
    simp [applyBindings, shape.fresh_right]

/-- A right congruence rule lifts a step of the second argument. -/
theorem RightCongruenceShape.step {c X Y Y' : String}
    (shape : RightCongruenceShape rule c X Y Y') (member : rule ∈ lang.rewrites)
    (first : Pattern) {second second' : Pattern} (step : Step base lang second second') :
    Step base lang (.apply c [first, second]) (.apply c [first, second']) := by
  refine step_of_single_congruence_rule
    (initialBindings := [(Y, second), (X, first)])
    (finalBindings := [(Y', second'), (Y, second), (X, first)])
    (premiseBindings := [(Y', second')])
    (premiseSource := .fvar Y) (premiseTarget := .fvar Y') (candidate := second')
    member ?_ shape.premises ?_ ?_ ?_ ?_
  · rw [matchPatternForRule_eq_syntactic, shape.left]
    exact (mem_matchPattern_binary shape.distinct).mpr ⟨_, _, rfl, rfl⟩
  · simpa [applyBindings] using step
  · simp [matchPattern]
  · simp [mergeBindings, shape.fresh_left.symm, shape.fresh_right.symm]
  · rw [applyBindingsForRule_eq_applyBindings _ _ _ shape.aligned, shape.right]
    simp [applyBindings, shape.fresh_left, shape.distinct.symm]

/-- Inversion of one application of a left congruence rule. -/
theorem LeftCongruenceShape.inversion {c X Y X' : String}
    (shape : LeftCongruenceShape rule c X Y X') {fuel : Nat}
    {source target : Pattern} {initial final : Bindings}
    (matched : initial ∈ matchPatternForRule lang rule source)
    (premises : PremisesAt base lang fuel initial rule.premises final)
    (targetEq : applyBindingsForRule lang rule final = target) :
    ∃ first second first', source = .apply c [first, second] ∧
      StepAt base lang fuel first first' ∧ target = .apply c [first', second] := by
  rw [matchPatternForRule_eq_syntactic, shape.left,
    mem_matchPattern_binary shape.distinct] at matched
  obtain ⟨first, second, rfl, rfl⟩ := matched
  rw [shape.premises] at premises
  cases premises with
  | cons head tail =>
      cases tail
      cases head with
      | congruence recursive premiseMatched merged =>
          simp [matchPattern] at premiseMatched
          subst premiseMatched
          simp [mergeBindings, shape.fresh_left.symm, shape.fresh_right.symm] at merged
          subst merged
          rw [applyBindingsForRule_eq_applyBindings _ _ _ shape.aligned, shape.right]
            at targetEq
          simp [applyBindings, shape.fresh_right] at targetEq
          refine ⟨first, second, _, rfl, ?_, targetEq.symm⟩
          simpa [applyBindings, shape.distinct.symm] using recursive

/-- Inversion of one application of a right congruence rule. -/
theorem RightCongruenceShape.inversion {c X Y Y' : String}
    (shape : RightCongruenceShape rule c X Y Y') {fuel : Nat}
    {source target : Pattern} {initial final : Bindings}
    (matched : initial ∈ matchPatternForRule lang rule source)
    (premises : PremisesAt base lang fuel initial rule.premises final)
    (targetEq : applyBindingsForRule lang rule final = target) :
    ∃ first second second', source = .apply c [first, second] ∧
      StepAt base lang fuel second second' ∧ target = .apply c [first, second'] := by
  rw [matchPatternForRule_eq_syntactic, shape.left,
    mem_matchPattern_binary shape.distinct] at matched
  obtain ⟨first, second, rfl, rfl⟩ := matched
  rw [shape.premises] at premises
  cases premises with
  | cons head tail =>
      cases tail
      cases head with
      | congruence recursive premiseMatched merged =>
          simp [matchPattern] at premiseMatched
          subst premiseMatched
          simp [mergeBindings, shape.fresh_left.symm, shape.fresh_right.symm] at merged
          subst merged
          rw [applyBindingsForRule_eq_applyBindings _ _ _ shape.aligned, shape.right]
            at targetEq
          simp [applyBindings, shape.fresh_left, shape.distinct.symm] at targetEq
          refine ⟨first, second, _, rfl, ?_, targetEq.symm⟩
          simpa [applyBindings] using recursive

theorem ruleReviseCongLeft_shape :
    LeftCongruenceShape ruleReviseCongLeft "Revise" "W1" "W2" "W1p" :=
  ⟨rfl, rfl, rfl, by decide +kernel, by decide, by decide, by decide⟩

theorem ruleReviseCongRight_shape :
    RightCongruenceShape ruleReviseCongRight "Revise" "W1" "W2" "W2p" :=
  ⟨rfl, rfl, rfl, by decide +kernel, by decide, by decide, by decide⟩

theorem ruleExtractCongLeft_shape :
    LeftCongruenceShape ruleExtractCongLeft "Extract" "W" "q" "Wp" :=
  ⟨rfl, rfl, rfl, by decide +kernel, by decide, by decide, by decide⟩

theorem ruleExtractCongRight_shape :
    RightCongruenceShape ruleExtractCongRight "Extract" "W" "q" "qp" :=
  ⟨rfl, rfl, rfl, by decide +kernel, by decide, by decide, by decide⟩

theorem ruleCombineCongLeft_shape :
    LeftCongruenceShape ruleCombineCongLeft "Combine" "e1" "e2" "e1p" :=
  ⟨rfl, rfl, rfl, by decide +kernel, by decide, by decide, by decide⟩

theorem ruleCombineCongRight_shape :
    RightCongruenceShape ruleCombineCongRight "Combine" "e1" "e2" "e2p" :=
  ⟨rfl, rfl, rfl, by decide +kernel, by decide, by decide, by decide⟩

/-! ## The contextual presentation at the minimal vertex -/

theorem minimalVertexWithCong_rewrites :
    (wmExtVertexLanguageDefWithCong wmExtVertexMinimal).rewrites =
      coreRules ++ coreCongruenceRules :=
  rfl

theorem minimalVertexWithCong_isEquationFree :
    (wmExtVertexLanguageDefWithCong wmExtVertexMinimal).isEquationFree = true :=
  rfl

theorem coreRules_premises_nil : ∀ rule ∈ coreRules, rule.premises = [] := by
  simp [coreRules, ruleEvidenceAdd, ruleRevisionComm, ruleRevisionAssoc,
    ruleCombineComm, ruleCombineZero]

theorem coreCongruenceRule_mem_minimalVertexWithCong {rule : RewriteRule} (member : rule ∈ coreCongruenceRules) :
    rule ∈ (wmExtVertexLanguageDefWithCong wmExtVertexMinimal).rewrites := by
  rw [minimalVertexWithCong_rewrites]
  exact List.mem_append_right _ member

/-- An application of a core rule, in any language, is a `wmCoreLanguageDef`
step. -/
theorem coreLangReduces_of_coreRule {lang : LanguageDef} {fuel : Nat}
    {rule : RewriteRule} {source target : Pattern} {initial final : Bindings}
    (core : rule ∈ coreRules)
    (matched : initial ∈ matchPatternForRule lang rule source)
    (premises : PremisesAt (engineBasePremises RelationEnv.empty) lang fuel
      initial rule.premises final)
    (targetEq : applyBindingsForRule lang rule final = target) :
    langReduces wmCoreLanguageDef source target := by
  have noPremises := coreRules_premises_nil rule core
  rw [noPremises] at premises
  cases premises
  refine ⟨1, .rule core matched ?_ targetEq⟩
  rw [noPremises]
  exact .nil _

/-! ## Contextual steps on terms -/

/-- One WM step at any depth: a root `WMStep`, or a step in one argument
position of `Revise`, `Extract` or `Combine`. -/
inductive WMContextStep : {s : WMSort} → WMTerm s → WMTerm s → Prop where
  | root {s : WMSort} {source target : WMTerm s} :
      WMStep source target → WMContextStep source target
  | revise_left {first first' : WMTerm .state} (second : WMTerm .state) :
      WMContextStep first first' →
        WMContextStep (.revise first second) (.revise first' second)
  | revise_right (first : WMTerm .state) {second second' : WMTerm .state} :
      WMContextStep second second' →
        WMContextStep (.revise first second) (.revise first second')
  | extract_left {world world' : WMTerm .state} (query : WMTerm .query) :
      WMContextStep world world' →
        WMContextStep (.extract world query) (.extract world' query)
  | extract_right (world : WMTerm .state) {query query' : WMTerm .query} :
      WMContextStep query query' →
        WMContextStep (.extract world query) (.extract world query')
  | combine_left {first first' : WMTerm .evidence} (second : WMTerm .evidence) :
      WMContextStep first first' →
        WMContextStep (.combine first second) (.combine first' second)
  | combine_right (first : WMTerm .evidence) {second second' : WMTerm .evidence} :
      WMContextStep second second' →
        WMContextStep (.combine first second) (.combine first second')

/-- Reflexive-transitive closure of `WMContextStep`. -/
def WMContextStepStar {s : WMSort} (source target : WMTerm s) : Prop :=
  Relation.ReflTransGen (fun first second => WMContextStep first second) source target

/-- A sort-indexed relation on WM terms closed under every constructor in
every argument position. -/
structure WMTermCongruence (relation : ∀ {s : WMSort}, WMTerm s → WMTerm s → Prop) :
    Prop where
  revise_left : ∀ {first first' : WMTerm .state} (second : WMTerm .state),
    relation first first' → relation (.revise first second) (.revise first' second)
  revise_right : ∀ (first : WMTerm .state) {second second' : WMTerm .state},
    relation second second' → relation (.revise first second) (.revise first second')
  extract_left : ∀ {world world' : WMTerm .state} (query : WMTerm .query),
    relation world world' → relation (.extract world query) (.extract world' query)
  extract_right : ∀ (world : WMTerm .state) {query query' : WMTerm .query},
    relation query query' → relation (.extract world query) (.extract world query')
  combine_left : ∀ {first first' : WMTerm .evidence} (second : WMTerm .evidence),
    relation first first' → relation (.combine first second) (.combine first' second)
  combine_right : ∀ (first : WMTerm .evidence) {second second' : WMTerm .evidence},
    relation second second' → relation (.combine first second) (.combine first second')

/-- A congruence that contains every root `WMStep` contains every contextual
step. -/
theorem WMTermCongruence.holds_of_contextStep
    {relation : ∀ {s : WMSort}, WMTerm s → WMTerm s → Prop}
    (congruence : WMTermCongruence relation)
    (root : ∀ {s : WMSort} {source target : WMTerm s},
      WMStep source target → relation source target)
    {s : WMSort} {source target : WMTerm s} (step : WMContextStep source target) :
    relation source target := by
  induction step with
  | root step => exact root step
  | revise_left second _ inner => exact congruence.revise_left second inner
  | revise_right first _ inner => exact congruence.revise_right first inner
  | extract_left query _ inner => exact congruence.extract_left query inner
  | extract_right world _ inner => exact congruence.extract_right world inner
  | combine_left second _ inner => exact congruence.combine_left second inner
  | combine_right first _ inner => exact congruence.combine_right first inner

/-- Soundness: every contextual term step is one step of the authored
contextual presentation. -/
theorem wmContextStep_sound {s : WMSort} {source target : WMTerm s}
    (step : WMContextStep source target) :
    langReduces (wmExtVertexLanguageDefWithCong wmExtVertexMinimal)
      (encodeWM source) (encodeWM target) := by
  induction step with
  | root step =>
      refine Step.mono_rules (fun rule member => ?_) (wmStep_sound _ _ step)
      rw [minimalVertexWithCong_rewrites]
      exact List.mem_append_left _ member
  | revise_left second _ inner =>
      exact ruleReviseCongLeft_shape.step
        (coreCongruenceRule_mem_minimalVertexWithCong (by simp [coreCongruenceRules])) (encodeWM second) inner
  | revise_right first _ inner =>
      exact ruleReviseCongRight_shape.step
        (coreCongruenceRule_mem_minimalVertexWithCong (by simp [coreCongruenceRules])) (encodeWM first) inner
  | extract_left query _ inner =>
      exact ruleExtractCongLeft_shape.step
        (coreCongruenceRule_mem_minimalVertexWithCong (by simp [coreCongruenceRules])) (encodeWM query) inner
  | extract_right world _ inner =>
      exact ruleExtractCongRight_shape.step
        (coreCongruenceRule_mem_minimalVertexWithCong (by simp [coreCongruenceRules])) (encodeWM world) inner
  | combine_left second _ inner =>
      exact ruleCombineCongLeft_shape.step
        (coreCongruenceRule_mem_minimalVertexWithCong (by simp [coreCongruenceRules])) (encodeWM second) inner
  | combine_right first _ inner =>
      exact ruleCombineCongRight_shape.step
        (coreCongruenceRule_mem_minimalVertexWithCong (by simp [coreCongruenceRules])) (encodeWM first) inner

/-- Completeness at a fixed contextual depth. -/
theorem wmContextStep_complete_at : ∀ (fuel : Nat) {s : WMSort} (source : WMTerm s)
    {target : Pattern},
    StepAt (engineBasePremises RelationEnv.empty)
        (wmExtVertexLanguageDefWithCong wmExtVertexMinimal) fuel (encodeWM source) target →
      ∃ reduct : WMTerm s, WMContextStep source reduct ∧ encodeWM reduct = target
  | 0, _, _, _, step => by cases step
  | fuel + 1, _, source, target, step => by
      cases step with
      | rule member matched premises targetEq =>
          rw [minimalVertexWithCong_rewrites, List.mem_append] at member
          rcases member with core | congruence
          · obtain ⟨reduct, rootStep, encoded⟩ := wmStep_complete source target
              (coreLangReduces_of_coreRule core matched premises targetEq)
            exact ⟨reduct, .root rootStep, encoded⟩
          · simp only [coreCongruenceRules, List.mem_cons, List.not_mem_nil, or_false]
              at congruence
            rcases congruence with rfl | rfl | rfl | rfl | rfl | rfl
            · obtain ⟨first, second, first', sourceEq, inner, rfl⟩ :=
                ruleReviseCongLeft_shape.inversion matched premises targetEq
              cases source with
              | revise a b =>
                  simp only [encodeWM, pRevise, Pattern.apply.injEq, List.cons.injEq,
                    and_true, true_and] at sourceEq
                  obtain ⟨rfl, rfl⟩ := sourceEq
                  obtain ⟨a', aStep, rfl⟩ := wmContextStep_complete_at fuel a inner
                  exact ⟨.revise a' b, .revise_left b aStep, rfl⟩
              | _ => simp [encodeWM, pExtract, pCombine, pEvidenceZero] at sourceEq
            · obtain ⟨first, second, second', sourceEq, inner, rfl⟩ :=
                ruleReviseCongRight_shape.inversion matched premises targetEq
              cases source with
              | revise a b =>
                  simp only [encodeWM, pRevise, Pattern.apply.injEq, List.cons.injEq,
                    and_true, true_and] at sourceEq
                  obtain ⟨rfl, rfl⟩ := sourceEq
                  obtain ⟨b', bStep, rfl⟩ := wmContextStep_complete_at fuel b inner
                  exact ⟨.revise a b', .revise_right a bStep, rfl⟩
              | _ => simp [encodeWM, pExtract, pCombine, pEvidenceZero] at sourceEq
            · obtain ⟨first, second, first', sourceEq, inner, rfl⟩ :=
                ruleExtractCongLeft_shape.inversion matched premises targetEq
              cases source with
              | extract w q =>
                  simp only [encodeWM, pExtract, Pattern.apply.injEq, List.cons.injEq,
                    and_true, true_and] at sourceEq
                  obtain ⟨rfl, rfl⟩ := sourceEq
                  obtain ⟨w', wStep, rfl⟩ := wmContextStep_complete_at fuel w inner
                  exact ⟨.extract w' q, .extract_left q wStep, rfl⟩
              | _ => simp [encodeWM, pRevise, pCombine, pEvidenceZero] at sourceEq
            · obtain ⟨first, second, second', sourceEq, inner, rfl⟩ :=
                ruleExtractCongRight_shape.inversion matched premises targetEq
              cases source with
              | extract w q =>
                  simp only [encodeWM, pExtract, Pattern.apply.injEq, List.cons.injEq,
                    and_true, true_and] at sourceEq
                  obtain ⟨rfl, rfl⟩ := sourceEq
                  obtain ⟨q', qStep, rfl⟩ := wmContextStep_complete_at fuel q inner
                  exact ⟨.extract w q', .extract_right w qStep, rfl⟩
              | _ => simp [encodeWM, pRevise, pCombine, pEvidenceZero] at sourceEq
            · obtain ⟨first, second, first', sourceEq, inner, rfl⟩ :=
                ruleCombineCongLeft_shape.inversion matched premises targetEq
              cases source with
              | combine a b =>
                  simp only [encodeWM, pCombine, Pattern.apply.injEq, List.cons.injEq,
                    and_true, true_and] at sourceEq
                  obtain ⟨rfl, rfl⟩ := sourceEq
                  obtain ⟨a', aStep, rfl⟩ := wmContextStep_complete_at fuel a inner
                  exact ⟨.combine a' b, .combine_left b aStep, rfl⟩
              | _ => simp [encodeWM, pRevise, pExtract, pEvidenceZero] at sourceEq
            · obtain ⟨first, second, second', sourceEq, inner, rfl⟩ :=
                ruleCombineCongRight_shape.inversion matched premises targetEq
              cases source with
              | combine a b =>
                  simp only [encodeWM, pCombine, Pattern.apply.injEq, List.cons.injEq,
                    and_true, true_and] at sourceEq
                  obtain ⟨rfl, rfl⟩ := sourceEq
                  obtain ⟨b', bStep, rfl⟩ := wmContextStep_complete_at fuel b inner
                  exact ⟨.combine a b', .combine_right a bStep, rfl⟩
              | _ => simp [encodeWM, pRevise, pExtract, pEvidenceZero] at sourceEq

/-- Completeness: every step of the authored contextual presentation from an
encoded term is the encoding of a contextual term step. -/
theorem wmContextStep_complete {s : WMSort} (source : WMTerm s) {target : Pattern}
    (step : langReduces (wmExtVertexLanguageDefWithCong wmExtVertexMinimal)
      (encodeWM source) target) :
    ∃ reduct : WMTerm s, WMContextStep source reduct ∧ encodeWM reduct = target :=
  let ⟨fuel, bounded⟩ := step
  wmContextStep_complete_at fuel source bounded

/-- One contextual step on the image of `encodeWM`: exactly the semantic step
of the contextual presentation, i.e. the step of its `langGSLT`. -/
theorem wmContextStep_iff {s : WMSort} (source target : WMTerm s) :
    WMContextStep source target ↔
      langSemanticReduces (wmExtVertexLanguageDefWithCong wmExtVertexMinimal)
        (encodeWM source) (encodeWM target) := by
  rw [langSemanticReduces_iff_langReduces_of_equation_free
    minimalVertexWithCong_isEquationFree]
  constructor
  · exact wmContextStep_sound
  · intro step
    obtain ⟨reduct, contextStep, encoded⟩ := wmContextStep_complete source step
    rwa [encodeWM_injective encoded] at contextStep

theorem wmContextStepStar_sound {s : WMSort} {source target : WMTerm s}
    (steps : WMContextStepStar source target) :
    LangReducesStar (wmExtVertexLanguageDefWithCong wmExtVertexMinimal)
      (encodeWM source) (encodeWM target) := by
  induction steps with
  | refl => exact .refl _
  | tail _ last previous =>
      exact previous.trans (LangReducesStar.single
        (langReduces_to_semantic _ (wmContextStep_sound last)))

/-- Every multi-step reduct of an encoded term under the contextual
presentation is the encoding of a `WMContextStepStar` reduct. -/
theorem wmContextStepStar_complete {s : WMSort} (source : WMTerm s) {target : Pattern}
    (steps : LangReducesStar (wmExtVertexLanguageDefWithCong wmExtVertexMinimal)
      (encodeWM source) target) :
    ∃ reduct : WMTerm s, WMContextStepStar source reduct ∧ encodeWM reduct = target := by
  generalize encoded : encodeWM source = start at steps
  induction steps generalizing source with
  | refl => exact ⟨source, .refl, encoded⟩
  | step first _ inductionHypothesis =>
      subst encoded
      obtain ⟨middle, firstStep, rfl⟩ := wmContextStep_complete source
        ((langSemanticReduces_iff_langReduces_of_equation_free
          minimalVertexWithCong_isEquationFree _ _).mp first)
      obtain ⟨reduct, rest, encodedReduct⟩ := inductionHypothesis middle rfl
      exact ⟨reduct, Relation.ReflTransGen.head firstStep rest, encodedReduct⟩

theorem wmContextStepStar_iff {s : WMSort} (source target : WMTerm s) :
    WMContextStepStar source target ↔
      LangReducesStar (wmExtVertexLanguageDefWithCong wmExtVertexMinimal)
        (encodeWM source) (encodeWM target) := by
  constructor
  · exact wmContextStepStar_sound
  · intro steps
    obtain ⟨reduct, contextSteps, encoded⟩ := wmContextStepStar_complete source steps
    rwa [encodeWM_injective encoded] at contextSteps

#print axioms mem_matchPattern_binary
#print axioms LeftCongruenceShape.step
#print axioms RightCongruenceShape.step
#print axioms LeftCongruenceShape.inversion
#print axioms RightCongruenceShape.inversion
#print axioms coreLangReduces_of_coreRule
#print axioms WMTermCongruence.holds_of_contextStep
#print axioms wmContextStep_sound
#print axioms wmContextStep_complete
#print axioms wmContextStep_iff
#print axioms wmContextStepStar_complete
#print axioms wmContextStepStar_iff

end Mettapedia.OSLF.Framework.WMCalculusContextEncoding
