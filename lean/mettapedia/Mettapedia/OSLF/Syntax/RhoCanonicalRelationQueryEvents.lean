import Mettapedia.OSLF.Syntax.CanonicalRelationQueryEvents
import Mettapedia.OSLF.Syntax.CanonicalRelationQueryTranslations
import Mettapedia.OSLF.Syntax.RhoAuthoredDropProfile

/-!
# Relation-event controls in the authored rho profile

The built-in equality table deliberately contains two rows for an equal
concrete pair. Both rows produce the same empty assignment, but they remain
separate query events. An unequal concrete pair has no event.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoCanonicalRelationQueryEvents

open Mettapedia.OSLF.Binding.CanonicalConditionalRuleFrames
open Mettapedia.OSLF.Binding.CanonicalRelationQueryEvents
open Mettapedia.OSLF.Binding.CanonicalRelationQueryTranslations
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.RhoSchema.Authored
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.Match (Bindings)

private def atomA : Pattern := .apply "a" []
private def atomB : Pattern := .apply "b" []

/-- The actual relation interpreter emits two equal results from its two
equal rows. The list is intentional: its multiplicity is observable. -/
theorem equal_pair_has_two_results :
    relationQueryStep RelationEnv.empty rhoCalcWithDrop [] "eq"
      [atomA, atomA] = [[], []] := by
  decide +kernel

/-- The computable event list has the same two results, but identifies their
distinct source rows by positions zero and one. -/
theorem equal_pair_recorded_positions :
    (recordedEvents RelationEnv.empty rhoCalcWithDrop [] "eq"
      [atomA, atomA]).map RecordedEvent.tuplePosition = [0, 1] := by
  decide +kernel

private def firstEvent : Event RelationEnv.empty rhoCalcWithDrop []
    "eq" [atomA, atomA] [] where
  tuple := [atomA, atomA]
  selectedTuple := ⟨⟨0, by decide +kernel⟩, by decide +kernel⟩
  extension := []
  selectedMatch := ⟨⟨0, by decide +kernel⟩, by decide +kernel⟩
  merge := by decide +kernel

private def secondEvent : Event RelationEnv.empty rhoCalcWithDrop []
    "eq" [atomA, atomA] [] where
  tuple := [atomA, atomA]
  selectedTuple := ⟨⟨1, by decide +kernel⟩, by decide +kernel⟩
  extension := []
  selectedMatch := ⟨⟨0, by decide +kernel⟩, by decide +kernel⟩
  merge := by decide +kernel

/-- The same endpoint assignment still carries two distinct events. -/
theorem equal_pair_events_distinct : firstEvent ≠ secondEvent := by
  apply distinct_tuple_positions
  decide +kernel

/-- Adding external tuples leaves both existing built-in equality events
distinct. This is an authored instance of faithful table translation. -/
private def augmentedEnv : RelationEnv where
  tuples := fun _ _ => [[atomB]]

theorem equal_pair_events_survive_environment_extension :
    mapEvent (TableMap.emptyTo augmentedEnv) firstEvent ≠
      mapEvent (TableMap.emptyTo augmentedEnv) secondEvent := by
  apply mapEvent_distinct_tuple_positions
    (TableMap.emptyTo augmentedEnv)
    (TableMap.emptyTo_faithful augmentedEnv)
  decide +kernel

/-- The existing environment preorder forgets row multiplicity. -/
private def duplicateEnv : RelationEnv where
  tuples := fun _ _ => [[atomA], [atomA]]

private def singletonEnv : RelationEnv where
  tuples := fun _ _ => [[atomA]]

theorem duplicate_rows_le_single_row : duplicateEnv ≤ singletonEnv := by
  intro relation arguments tuple membership
  simpa [duplicateEnv, singletonEnv] using membership

/-- Despite that preorder inclusion, no occurrence-faithful translation can
send the two duplicated external rows into the one-row table. -/
theorem duplicate_rows_cannot_translate_faithfully :
    ¬ ∃ translation : TableMap duplicateEnv singletonEnv,
      translation.Faithful := by
  rintro ⟨translation, faithful⟩
  let firstPosition : Fin
      (relationTuples duplicateEnv rhoCalcWithDrop [] "lookup" []).length :=
    ⟨0, by decide +kernel⟩
  let secondPosition : Fin
      (relationTuples duplicateEnv rhoCalcWithDrop [] "lookup" []).length :=
    ⟨1, by decide +kernel⟩
  have sameImage :
      translation.onTuple rhoCalcWithDrop [] "lookup" [] firstPosition =
        translation.onTuple rhoCalcWithDrop [] "lookup" []
          secondPosition := by
    apply Fin.ext
    have targetLength :
        (relationTuples singletonEnv rhoCalcWithDrop [] "lookup" []).length =
          1 := by decide +kernel
    have firstBound :=
      (translation.onTuple rhoCalcWithDrop [] "lookup" [] firstPosition).2
    have secondBound :=
      (translation.onTuple rhoCalcWithDrop [] "lookup" [] secondPosition).2
    omega
  have samePosition := faithful rhoCalcWithDrop [] "lookup" [] sameImage
  have distinct : firstPosition ≠ secondPosition := by decide +kernel
  exact distinct samePosition

/-- A diagnostic authored rho profile makes the Drop step conditional on a
real equality relation query. The two built-in equality rows then yield two
separate firings of the same source rule. -/
def guardedDrop : RewriteRule :=
  { rhoDropRewrite with
    name := "GuardedDrop"
    premises := [.relationQuery "eq" [.fvar "P", .fvar "P"]] }

def rhoCalcWithGuardedDrop : LanguageDef :=
  { rhoCalc with rewrites := rhoCalc.rewrites ++ [guardedDrop] }

def guardedEqualityModes : RelationModeTable :=
  [{ relation := "eq", args := [.input, .input] }]

def guardedEqualitySignatures : List LogicRelationDecl :=
  [{ name := "eq", argTypes := [TypeExpr.proc, TypeExpr.proc] }]

theorem guardedRho_valid : rhoCalcWithGuardedDrop.validate = [] := by
  simp [LanguageDef.validate, rhoCalcWithGuardedDrop, rhoCalc,
    guardedDrop, rhoDropRewrite, rhoCommRewrite, rhoParCongRewrite,
    LanguageDef.duplicateErrors, LanguageDef.duplicateErrorsAux,
    LanguageDef.validateEquation, LanguageDef.validateRewrite,
    LanguageDef.validatePatternConstructors, LanguageDef.validateRulePatterns,
    LanguageDef.typeNames, TypeDecl.plain, TypeExpr.baseType,
    TypeExpr.proc, TypeExpr.name, TypeExpr.funType, TypeExpr.bag,
    TermParam.bodyName, TermParam.binderNames, TermParam.typeExpr,
    LanguageDef.patternFvarNames, LanguageDef.patternBinderNames,
    LanguageDef.premiseProducedFvarNames, LanguageDef.premisePatterns,
    LanguageDef.premiseFvarNames, LanguageDef.premiseForAllParams,
    Pattern.constructorRefs, Pattern.constructorRefsList,
    Pattern.freeFvarNames, Pattern.isWellScoped, Pattern.isWellScopedAt,
    Pattern.isWellScopedListAt]
  all_goals decide +kernel

private theorem guardedRho_flow :
    rhoCalcWithGuardedDrop.executionFlowErrors guardedEqualityModes = [] := by
  apply LanguageDef.executionFlowErrors_append_binaryInputGuard
    rhoCalc guardedEqualityModes guardedDrop "eq" (.fvar "P") (.fvar "P")
  · exact rhoCalc_executionFlowErrors_any_modes guardedEqualityModes
  · rfl
  · rfl
  · intro name member
    simpa [guardedDrop, rhoDropRewrite, Pattern.freeFvarNames] using member
  · intro name member
    simpa [guardedDrop, rhoDropRewrite, Pattern.freeFvarNames] using member
  · intro name member
    simpa [guardedDrop, rhoDropRewrite, Pattern.freeFvarNames] using member

/-- The guarded rho profile passes the actual structural, signature, and
ordered-flow execution-admission gates. -/
theorem guardedRho_execution_admitted :
    rhoCalcWithGuardedDrop.executionAdmissionErrors
      guardedEqualityModes guardedEqualitySignatures = [] := by
  apply LanguageDef.executionAdmissionErrors_eq_nil_of_single_mode
    rhoCalcWithGuardedDrop
    { relation := "eq", args := [.input, .input] }
    { name := "eq", argTypes := [TypeExpr.proc, TypeExpr.proc] }
  · rfl
  · rfl
  · exact guardedRho_valid
  · exact guardedRho_flow

theorem guardedDrop_has_two_firings :
    rewriteAt (engineBasePremises RelationEnv.empty)
      rhoCalcWithGuardedDrop 1 dropQuotedZero = [zero, zero] := by
  decide +kernel

/-- The guarded conditional rule inhabits the actual canonical rule tree,
not only the flat relation-query evaluator. -/
theorem guardedDrop_has_tree :
    Nonempty ((authoredPresentation
      (engineBasePremises RelationEnv.empty) rhoCalcWithGuardedDrop).Derivation ()
        (1, dropQuotedZero, zero)) := by
  apply (mem_rewriteAt_iff_derivation
    (engineBasePremises RelationEnv.empty) rhoCalcWithGuardedDrop
    1 dropQuotedZero zero).mp
  rw [guardedDrop_has_two_firings]
  simp

private def guardedAssignment : Bindings := [("P", zero)]

private theorem guardedQueryResults :
    engineBasePremises RelationEnv.empty rhoCalcWithGuardedDrop
      guardedAssignment
      (.relationQuery "eq" [.fvar "P", .fvar "P"]) =
        [guardedAssignment, guardedAssignment] := by
  decide +kernel

private def guardedQueryWitness (position : Fin 2) :
    ListedWitness
      (engineBasePremises RelationEnv.empty rhoCalcWithGuardedDrop
        guardedAssignment
        (.relationQuery "eq" [.fvar "P", .fvar "P"]))
      guardedAssignment where
  position := ⟨position.val, by simpa [guardedQueryResults] using position.2⟩
  represents := by
    fin_cases position <;> decide +kernel

/-- One source-rule constructor for each selected equality-row occurrence.
The two choices have the same initial and final assignments. -/
def guardedDropFrame (position : Fin 2) :
    RuleFrame (engineBasePremises RelationEnv.empty)
      rhoCalcWithGuardedDrop dropQuotedZero zero where
  rule := guardedDrop
  declared := ⟨⟨2, by decide +kernel⟩, rfl⟩
  initial := guardedAssignment
  matched := ⟨⟨0, by decide +kernel⟩, by decide +kernel⟩
  final := guardedAssignment
  premises := .cons (.relationQuery (guardedQueryWitness position))
    (.nil guardedAssignment)
  result := by decide +kernel

private def firstQueryIndex {lang : LanguageDef} {initial final : Bindings}
    {premises : List Premise}
    (frames : PremiseFrames (engineBasePremises RelationEnv.empty) lang
      initial premises final) : Option Nat :=
  match frames with
  | .nil _ => none
  | .cons first _ =>
    match first with
    | .relationQuery witness => some witness.position.val
    | _ => none

/-- Identical guarded outputs arise from distinct source-rule constructors. -/
theorem guardedDropFrames_distinct :
    guardedDropFrame ⟨0, by decide⟩ ≠
      guardedDropFrame ⟨1, by decide⟩ := by
  intro equal
  have sameIndex := congrArg (fun frame => firstQueryIndex frame.premises)
    equal
  simp [firstQueryIndex, guardedDropFrame, guardedQueryWitness] at sameIndex

/-- The two constructors inhabit the actual free rule model as separate
firing histories at the same source and target. -/
def guardedDropTree (position : Fin 2) :
    (authoredPresentation (engineBasePremises RelationEnv.empty)
      rhoCalcWithGuardedDrop).Derivation ()
        (1, dropQuotedZero, zero) := by
  refine .roll (guardedDropFrame position) (fun child => ?_)
  have noChildren :
      (authoredPresentation (engineBasePremises RelationEnv.empty)
        rhoCalcWithGuardedDrop).premises () (1, dropQuotedZero, zero)
        (guardedDropFrame position) = [] := rfl
  change Fin ((authoredPresentation (engineBasePremises RelationEnv.empty)
    rhoCalcWithGuardedDrop).premises () (1, dropQuotedZero, zero)
    (guardedDropFrame position)).length at child
  rw [noChildren] at child
  exact Fin.elim0 child

theorem guardedDropTrees_distinct :
    guardedDropTree ⟨0, by decide⟩ ≠
      guardedDropTree ⟨1, by decide⟩ := by
  intro equal
  have shapeEq := congrArg
    (fun tree => (Mettapedia.TypeTheory.IndexedPolynomial.Fix.out
      (authoredPresentation (engineBasePremises RelationEnv.empty)
        rhoCalcWithGuardedDrop).polynomial tree).1) equal
  exact guardedDropFrames_distinct shapeEq

/-- A faithful table extension preserves the actual guarded firing at the
same contextual depth. -/
theorem guardedDrop_survives_environment_extension :
    zero ∈ rewriteAt (engineBasePremises augmentedEnv)
      rhoCalcWithGuardedDrop 1 dropQuotedZero := by
  apply rewriteAt_mono_tableMap
    (TableMap.emptyTo augmentedEnv) rhoCalcWithGuardedDrop 1
    dropQuotedZero zero
  rw [guardedDrop_has_two_firings]
  simp

/-- A mismatched pair is rejected by the same actual query interpreter. -/
theorem unequal_pair_has_no_event :
    ¬ Nonempty (Event RelationEnv.empty rhoCalcWithDrop []
      "eq" [atomA, atomB] []) := by
  intro event
  have emitted := result_iff_event.mpr event
  have none : relationQueryStep RelationEnv.empty rhoCalcWithDrop []
      "eq" [atomA, atomB] = [] := by
    decide +kernel
  rw [none] at emitted
  exact List.not_mem_nil emitted

#print axioms equal_pair_has_two_results
#print axioms equal_pair_recorded_positions
#print axioms equal_pair_events_distinct
#print axioms equal_pair_events_survive_environment_extension
#print axioms duplicate_rows_le_single_row
#print axioms duplicate_rows_cannot_translate_faithfully
#print axioms guardedDrop_has_two_firings
#print axioms guardedRho_valid
#print axioms guardedRho_execution_admitted
#print axioms guardedDrop_has_tree
#print axioms guardedDropTrees_distinct
#print axioms guardedDrop_survives_environment_extension
#print axioms unequal_pair_has_no_event

end Mettapedia.OSLF.Binding.RhoCanonicalRelationQueryEvents
