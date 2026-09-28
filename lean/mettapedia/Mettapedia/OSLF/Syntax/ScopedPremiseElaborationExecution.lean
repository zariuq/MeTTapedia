import Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise
import Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution

/-!
# Executable meaning of an elaborated root step premise

The surface congruence premise omits its endpoint sort. When the authored
grammar determines that sort uniquely, elaboration produces an explicitly
scoped root step. This module compares that result with the proof-relevant
scoped executor, including its ordered occurrence index and assignment.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedPremiseElaborationExecution

open Mettapedia.GSLT.LanguageDef.CanonicalScopedPremise
open Mettapedia.GSLT.LanguageDef.TypedScopedStepPremise
open Mettapedia.GSLT.LanguageDef.WellSorted (FreeTypeContext)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching (Assignment)

/-- A successfully elaborated surface root step has exactly the same
proof-relevant one-premise results as its canonical scoped representation.
Both sides retain the oracle occurrence number and completed assignment. -/
theorem premiseResults_compiled_congruence
    {Evidence : Type} (oracle : StepOracle Evidence)
    (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (ambient : List TypeExpr)
    (rule : RewriteRule) (spec : RuleBindingSpec) (index : Nat)
    (source target : Pattern) (payload : ScopedStepPremise)
    (assignment : Assignment)
    (compiled : compile? language free ambient (.congruence source target) =
      some (.step payload)) :
    premiseResults oracle relEnv language rule spec ambient.length index
        (.scopedStep payload) assignment =
      premiseResults oracle relEnv language rule spec ambient.length index
        (.congruence source target) assignment := by
  obtain ⟨resultType, payloadEq, typed⟩ :=
    compile_congruence_typed compiled
  subst payload
  have wellScoped := HasType.isWellScopedAt typed
  change (if (ScopedStepPremise.root resultType source target).isWellScopedAt
      ambient.length then
      stepResults oracle rule spec ambient.length index 0 source target
        assignment else []) =
    stepResults oracle rule spec ambient.length index 0 source target
      assignment
  rw [wellScoped]
  rfl

/-- The same comparison holds for a complete singleton premise run. Its
history still consists of the selected occurrence at the author's index. -/
theorem runPremises_compiled_singleton
    {Evidence : Type} (oracle : StepOracle Evidence)
    (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (ambient : List TypeExpr)
    (rule : RewriteRule) (spec : RuleBindingSpec) (index : Nat)
    (source target : Pattern) (payload : ScopedStepPremise)
    (assignment : Assignment)
    (compiled : compile? language free ambient (.congruence source target) =
      some (.step payload)) :
    runPremises oracle relEnv language rule spec ambient.length index
        [.scopedStep payload] assignment =
      runPremises oracle relEnv language rule spec ambient.length index
        [.congruence source target] assignment := by
  simp only [runPremises,
    premiseResults_compiled_congruence oracle relEnv language free ambient
      rule spec index source target payload assignment compiled]

/-- Collection quantification currently has no result in the scoped
executor, regardless of its body. This is an explicit boundary of the
comparison, not an assertion that the quantified premise is valid. -/
theorem premiseResults_forAll
    {Evidence : Type} (oracle : StepOracle Evidence)
    (relEnv : RelationEnv) (language : LanguageDef)
    (rule : RewriteRule) (spec : RuleBindingSpec) (ambient index : Nat)
    (collection parameter : String) (body : Premise)
    (assignment : Assignment) :
    premiseResults oracle relEnv language rule spec ambient index
      (.forAll collection parameter body) assignment = [] := by
  change rootResults relEnv language spec ambient index
    (.forAll collection parameter body) assignment = []
  unfold rootResults
  by_cases hasOccurrence : hasOccurrenceAt spec index = true
  · simp [hasOccurrence]
  · have absent : hasOccurrenceAt spec index = false :=
      Bool.eq_false_iff.mpr hasOccurrence
    simp only [absent, Bool.false_eq_true, if_false]
    cases Mettapedia.OSLF.MeTTaIL.ScopedRuleMatching.projectRoot?
      ambient assignment with
    | none => rfl
    | some root =>
        simp [Mettapedia.OSLF.MeTTaIL.Engine.premiseStepWithEnv]

/-- Successful checked elaboration preserves the exact proof-relevant result
list of the current scoped executor. In particular, root-step inference does
not change selected oracle ordinals or binding assignments. -/
theorem premiseResults_compile
    {Evidence : Type} (oracle : StepOracle Evidence)
    (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (ambient : List TypeExpr)
    (rule : RewriteRule) (spec : RuleBindingSpec) (index : Nat)
    (premise : Premise) (canonical : CanonicalPremise)
    (assignment : Assignment)
    (compiled : compile? language free ambient premise = some canonical) :
    premiseResults oracle relEnv language rule spec ambient.length index
        canonical.toAuthored assignment =
      premiseResults oracle relEnv language rule spec ambient.length index
        premise assignment := by
  cases premise with
  | freshness condition =>
      simp only [compile?, Option.some.injEq] at compiled
      subst canonical
      rfl
  | congruence source target =>
      cases inferred : inferRootSort? language free ambient source target with
      | none => simp [compile?, inferred] at compiled
      | some resultType =>
          simp [compile?, inferred] at compiled
          subst canonical
          exact premiseResults_compiled_congruence oracle relEnv language
            free ambient rule spec index source target
            (ScopedStepPremise.root resultType source target) assignment
            (by simp [compile?, inferred])
  | scopedStep step =>
      cases checked : Mettapedia.GSLT.LanguageDef.TypedScopedStepPremise.check
          language free ambient step with
      | false => simp [compile?, checked] at compiled
      | true =>
          simp [compile?, checked] at compiled
          subst canonical
          rfl
  | relationQuery relation arguments =>
      simp only [compile?, Option.some.injEq] at compiled
      subst canonical
      rfl
  | forAll collection parameter body =>
      have canonicalForAll : ∃ nested,
          canonical = .forAll collection parameter nested := by
        cases hcollection : free collection with
        | none => simp [compile?, hcollection] at compiled
        | some ty =>
            cases ty with
            | base _ => simp [compile?, hcollection] at compiled
            | arrow _ _ => simp [compile?, hcollection] at compiled
            | multiBinder _ => simp [compile?, hcollection] at compiled
            | collection kind elementType =>
                cases hbody : compile? language
                    (fun name => if name = parameter then some elementType
                      else free name) ambient body with
                | none => simp [compile?, hcollection, hbody] at compiled
                | some nested =>
                    simp [compile?, hcollection, hbody] at compiled
                    cases compiled
                    exact ⟨nested, rfl⟩
      obtain ⟨nested, equal⟩ := canonicalForAll
      subst canonical
      simp only [CanonicalPremise.toAuthored]
      rw [premiseResults_forAll, premiseResults_forAll]

/-- Elaborating a complete ordered premise list preserves the exact list of
completed assignments and premise-event histories at every initial index.
This covers repeated root occurrences and mixed step/relation premises; the
currently unsupported quantified case stays empty on both sides. -/
theorem runPremises_compileList
    {Evidence : Type} (oracle : StepOracle Evidence)
    (relEnv : RelationEnv) (language : LanguageDef)
    (free : FreeTypeContext) (ambient : List TypeExpr)
    (rule : RewriteRule) (spec : RuleBindingSpec) (index : Nat)
    (premises : List Premise) (canonical : List CanonicalPremise)
    (assignment : Assignment)
    (compiled : compileList? language free ambient premises =
      some canonical) :
    runPremises oracle relEnv language rule spec ambient.length index
        (canonical.map CanonicalPremise.toAuthored) assignment =
      runPremises oracle relEnv language rule spec ambient.length index
        premises assignment := by
  induction premises generalizing canonical assignment index with
  | nil =>
      simp only [compileList?, Option.some.injEq] at compiled
      subst canonical
      rfl
  | cons premise rest inductionHypothesis =>
      cases first : compile? language free ambient premise with
      | none => simp [compileList?, first] at compiled
      | some canonicalFirst =>
          cases later : compileList? language free ambient rest with
          | none => simp [compileList?, first, later] at compiled
          | some canonicalRest =>
              simp [compileList?, first, later] at compiled
              subst canonical
              simp only [List.map_cons, runPremises]
              rw [premiseResults_compile oracle relEnv language free ambient
                rule spec index premise canonicalFirst assignment first]
              congr 1
              funext entry
              cases entry with
              | mk event completed =>
                  congr 1
                  exact inductionHypothesis (index := index + 1)
                    (assignment := completed) (canonical := canonicalRest)
                    later

/-- The rule-level elaborator is the same ordered premise interpreter used
by the bounded authored executor. The comparison ranges over an actual rule
declaration, rather than an independently supplied premise list. -/
theorem runPremises_compileRule
    {Evidence : Type} (oracle : StepOracle Evidence)
    (relEnv : RelationEnv) (language : LanguageDef)
    (rule : RewriteRule) (spec : RuleBindingSpec)
    (index : Nat) (canonical : List CanonicalPremise)
    (assignment : Assignment)
    (compiled : compileRulePremises? language rule = some canonical) :
    runPremises oracle relEnv language rule spec 0 index
        (canonical.map CanonicalPremise.toAuthored) assignment =
      runPremises oracle relEnv language rule spec 0 index
        rule.premises assignment := by
  have compiledList :
      compileList? language (freeFromRuleContext rule.typeContext) []
        rule.premises = some canonical := by
    unfold compileRulePremises? at compiled
    split at compiled
    · exact compiled
    · contradiction
  exact runPremises_compileList oracle relEnv language
    (freeFromRuleContext rule.typeContext) [] rule spec index
    rule.premises canonical assignment compiledList

private def sortedRhoParCong : RewriteRule :=
  { rhoParCongRewrite with
    typeContext :=
      [("S", .base "Proc"), ("T", .base "Proc"),
       ("rest", .collection .hashBag (.base "Proc"))] }

private theorem rhoParCong_compiles :
    compile? rhoCalc (freeFromRuleContext sortedRhoParCong.typeContext) []
        (.congruence (.fvar "S") (.fvar "T")) =
      some (.step (ScopedStepPremise.root (.base "Proc")
        (.fvar "S") (.fvar "T"))) := by
  decide

/-- The actual sorted rho parallel-congruence premise can be executed
through its canonical explicit root form with identical selected events and
assignments, for every step oracle and binding specification. -/
theorem rhoParCong_root_execution_agrees
    {Evidence : Type} (oracle : StepOracle Evidence)
    (relEnv : RelationEnv) (spec : RuleBindingSpec)
    (assignment : Assignment) :
    runPremises oracle relEnv rhoCalc sortedRhoParCong spec 0 0
        [.scopedStep (ScopedStepPremise.root (.base "Proc")
          (.fvar "S") (.fvar "T"))] assignment =
      runPremises oracle relEnv rhoCalc sortedRhoParCong spec 0 0
        [.congruence (.fvar "S") (.fvar "T")] assignment := by
  exact runPremises_compiled_singleton oracle relEnv rhoCalc
    (freeFromRuleContext sortedRhoParCong.typeContext) []
    sortedRhoParCong spec 0 (.fvar "S") (.fvar "T")
    (ScopedStepPremise.root (.base "Proc") (.fvar "S") (.fvar "T"))
    assignment rhoParCong_compiles

/-- The unsorted shipped rho declaration cannot infer an endpoint sort for
its two free premise variables. It therefore has no silent canonicalization. -/
theorem rhoParCong_unsorted_rejected :
    compileRulePremises? rhoCalc rhoParCongRewrite = none := by
  decide

end Mettapedia.OSLF.Binding.ScopedPremiseElaborationExecution
