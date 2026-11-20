import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NumberedSourceDeclarations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NumberedSourceInputControls

/-!
# Numbered declaration controls

The first control uses the literal initial truth-definition rows and raw
event. Its input equation has VAR T and its claimed result has CONST T.
The later type declaration is explicitly auxiliary: its existence theorem
is earned by the actual REFL call on the captured identity term. Both type
outputs are independently represented by numbered source rows.

Corrupted-metadata controls distinguish registered soundness from a faithful
source-conclusion interpretation. They assert no new original trace or prod
reception and use no separately supplied theorem or admission oracle.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceDeclarationsControls

open Lean Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open ProofExecution DefinitionAdapters SignatureFormation ExportReplay NumberedSourceDeclarations

private theorem option_eq_some_of_same {A : Type} (same : A → A → Bool)
    (sound : ∀ first second, same first second = true → first = second)
    (actual : Option A) (expected : A)
    (checked : actual.map (fun value => same value expected) = some true) : actual = some expected := by
  cases actual with
  | none => cases checked
  | some value =>
      have equal := sound value expected (Option.some.inj checked)
      cases equal
      rfl

def claim (id conclusion : Nat) : Json := Json.mkObj
  [("id",toJson id),("hypotheses",.arr #[]),("conclusion",toJson conclusion)]

def rawTruth : Json := Json.mkObj
  [("rule",.str "DEFINITION"),("event",.num 0),("payload",.arr #[.num 8]),
    ("parents",.arr #[]),("outputs",.arr #[claim 0 11])]

def originalInput : SourceDAGReceive.Input :=
  ⟨NumberedSourceInputControls.typeBodies.toArray ++ #[
      .arr #[.str "op",.str "fun",.arr #[.num 0,.num 1]]],
    NumberedSourceInputControls.termBodies.toArray ++ #[
      .arr #[.str "var",.str "T",.num 0],
      .arr #[.str "const",.str "=",.num 4],
      .arr #[.str "app",.num 6,.num 5],
      .arr #[.str "app",.num 7,.num 4],
      .arr #[.str "const",.str "T",.num 0],
      .arr #[.str "app",.num 6,.num 9],
      .arr #[.str "app",.num 10,.num 4]], #[rawTruth]⟩

def initial : Reading := SourceDAGReceive.start originalInput

theorem input_equation_has_variable_lhs :
    NumberedSourceProofs.sourceTerm? initial 8 = some
      (.app (.app (.const Const.equality (Ty.equality Ty.bool)) (.var (.global "T") Ty.bool))
        StandardTheoryInterpretation.Source.truthBody) := by
  apply option_eq_some_of_same SourceTerm.same (fun first second checked =>
    (SourceTerm.same_eq_true_iff first second).mp checked)
  decide +kernel

theorem output_requires_new_symbols : NumberedSourceProofs.sourceTerm? initial 11 = none := by decide +kernel

theorem truth_prepared_available : (prepare? initial rawTruth).isSome = true := by decide +kernel
theorem truth_received_available : (receive? initial rawTruth).isSome = true := by decide +kernel

def afterTruth : Reading := (receive? initial rawTruth).get truth_received_available

theorem truth_actual_receive : receive? initial rawTruth = some afterTruth :=
  (Option.some_get truth_received_available).symm

theorem actual_truth_output :
    afterTruth.registered.registered.cache[0]? =
      some StandardTheoryInterpretation.Source.truthResult.output.definitionTheorem := by decide +kernel

theorem actual_truth_constant :
    List.lookup "T" afterTruth.symbols.constants =
      some StandardTheoryInterpretation.Source.truthResult.output.constant := by
  apply option_eq_some_of_same Const.same (fun first second checked =>
    (Const.same_eq_true_iff first second).mp checked)
  decide +kernel

theorem truth_counts_and_identity :
    afterTruth.registered.registered.cache.size = 1 ∧ afterTruth.registered.receipts.size = 1 ∧
      afterTruth.registered.addresses[0]? = some 0 ∧ afterTruth.refusalChecks = 0 := by decide +kernel

theorem truth_registry_extension_checked :
    NumberedSourceRegistry.preserves? initial.symbols afterTruth.symbols = true := by decide +kernel

def shadowedInitial : Reading :=
  { initial with symbols := { initial.symbols with constants := ("T",Const.equality) :: initial.symbols.constants } }

theorem shadowed_truth_available : (receive? shadowedInitial rawTruth).isSome = true := by decide +kernel
def shadowedAfter : Reading := (receive? shadowedInitial rawTruth).get shadowed_truth_available

/-- Successful kernel admission does not by itself certify an independently
corrupted registry's old visible lookups. This is not an honest-trace claim. -/
theorem admission_is_not_a_registry_extension_licence :
    shadowedInitial.registered = initial.registered ∧
      NumberedSourceRegistry.preserves? shadowedInitial.symbols shadowedAfter.symbols = false := by
  constructor
  · rfl
  · decide +kernel

theorem variable_input_differs_from_constant_output :
    (do
      let input ← NumberedSourceProofs.canonical? initial 8
      let output ← NumberedSourceProofs.canonical? afterTruth 11
      pure (input.same output)) = some false := by decide +kernel

theorem wrong_variable_claim_refused :
    (receive? initial (Json.mkObj
      [("rule",.str "DEFINITION"),("event",.num 0),("payload",.arr #[.num 8]),
        ("parents",.arr #[]),("outputs",.arr #[claim 0 8])])).isNone = true := by decide +kernel

theorem nonvariable_lhs_refused :
    (prepare? initial (Json.mkObj
      [("rule",.str "DEFINITION"),("event",.num 0),("payload",.arr #[.num 4]),
        ("parents",.arr #[]),("outputs",.arr #[claim 0 11])])).isNone = true := by decide +kernel

def looseAnnotations : Reading := SourceDAGReceive.start
  { originalInput with terms := originalInput.terms.set! 5 (.arr #[.str "var",.str "T",.num 1]) }

/-- The raw recipe admits the body, rather than imposing a new check on
the input equation's ignored variable annotation. -/
theorem raw_lhs_annotation_is_not_an_admission_guard :
    (NumberedSourceProofs.canonical? looseAnnotations 8).isNone = true ∧
      (receive? looseAnnotations rawTruth).isSome = true := by decide +kernel

def rawReflexivity : Json := Json.mkObj
  [("rule",.str "REFL"),("event",.num 1),("payload",.arr #[.num 1]),
    ("parents",.arr #[]),("outputs",.arr #[claim 1 4])]

def rawType : Json := Json.mkObj
  [("rule",.str "TYPE_DEFINITION"),("event",.num 1000),
    ("payload",.arr #[.str "NumberedFixture",.str "ABS_NumberedFixture",.str "REP_NumberedFixture"]),
    ("parents",.arr #[.num 1]),("outputs",.arr #[claim 9001 19,claim 9002 27])]

def fixtureInput : SourceDAGReceive.Input :=
  { originalInput with
    types := originalInput.types ++ #[
      .arr #[.str "op",.str "NumberedFixture",.arr #[]],
      .arr #[.str "op",.str "fun",.arr #[.num 1,.num 5]],
      .arr #[.str "op",.str "fun",.arr #[.num 5,.num 1]],
      .arr #[.str "op",.str "fun",.arr #[.num 5,.num 0]],
      .arr #[.str "op",.str "fun",.arr #[.num 5,.num 8]]]
    terms := originalInput.terms ++ #[
      .arr #[.str "var",.str "a",.num 5],
      .arr #[.str "const",.str "ABS_NumberedFixture",.num 6],
      .arr #[.str "const",.str "REP_NumberedFixture",.num 7],
      .arr #[.str "const",.str "=",.num 9],
      .arr #[.str "app",.num 14,.num 12],
      .arr #[.str "app",.num 13,.num 16],
      .arr #[.str "app",.num 15,.num 17],
      .arr #[.str "app",.num 18,.num 12],
      .arr #[.str "var",.str "r",.num 1],
      .arr #[.str "app",.num 3,.num 20],
      .arr #[.str "app",.num 6,.num 21],
      .arr #[.str "app",.num 13,.num 20],
      .arr #[.str "app",.num 14,.num 23],
      .arr #[.str "app",.num 2,.num 24],
      .arr #[.str "app",.num 25,.num 20],
      .arr #[.str "app",.num 22,.num 26]]
    events := #[rawTruth,rawReflexivity,rawType] }

def fixtureInitial : Reading := SourceDAGReceive.start fixtureInput

theorem fixture_truth_available : (receive? fixtureInitial rawTruth).isSome = true := by decide +kernel
def fixtureTruth : Reading := (receive? fixtureInitial rawTruth).get fixture_truth_available

theorem witness_available : (NumberedSourceProofs.receive? fixtureTruth rawReflexivity).isSome = true := by decide +kernel
def beforeType : Reading := (NumberedSourceProofs.receive? fixtureTruth rawReflexivity).get witness_available

theorem fixture_truth_coherent : ConclusionsChecked fixtureTruth :=
  receive_preserves_conclusions fixtureInitial fixtureTruth rawTruth
    (NumberedSourceMetadata.empty_conclusions_checked fixtureInitial.registered)
    (Option.some_get fixture_truth_available).symm

theorem before_type_coherent : ConclusionsChecked beforeType :=
  NumberedSourceProofMetadata.receive_preserves_conclusions fixtureTruth beforeType rawReflexivity
    fixture_truth_coherent (Option.some_get witness_available).symm

theorem actual_existence_parent :
    beforeType.registered.addresses[1]? = some 1 ∧
      beforeType.sourceConclusions[1]? = some StandardTheoryInterpretation.Source.truthBody := by
  constructor
  · decide +kernel
  · apply option_eq_some_of_same SourceTerm.same (fun first second checked =>
      (SourceTerm.same_eq_true_iff first second).mp checked)
    decide +kernel

theorem type_prepared_available : (prepare? beforeType rawType).isSome = true := by decide +kernel
def typePrepared : Prepared beforeType rawType := (prepare? beforeType rawType).get type_prepared_available

theorem type_data_available : typePrepared.admission.typeData?.isSome = true := by decide +kernel
def actualTypeData : TypeAdmission beforeType := typePrepared.admission.typeData?.get type_data_available

theorem actual_named_predicate_and_witness :
    actualTypeData.predicate.check = some actualTypeData.result.core.predicate ∧
      actualTypeData.sourceWitness.check = some actualTypeData.result.core.witness :=
  actualTypeData.source_checks before_type_coherent

theorem type_received_available : (receive? beforeType rawType).isSome = true := by decide +kernel
def afterType : Reading := (receive? beforeType rawType).get type_received_available

theorem type_actual_receive : receive? beforeType rawType = some afterType :=
  (Option.some_get type_received_available).symm

theorem after_type_coherent : ConclusionsChecked afterType :=
  receive_preserves_conclusions beforeType afterType rawType before_type_coherent type_actual_receive

theorem both_outputs_and_same_parent :
    typePrepared.event.sourceIds = [9001,9002] ∧ typePrepared.event.sourceParents = [1] ∧
      typePrepared.event.command.parents = [1] ∧
      typePrepared.event.command.origin = ("indexed-hol-source-export",1000) := by decide +kernel

theorem type_counts_and_refusals :
    beforeType.registered.registered.cache.size = 2 ∧ afterType.registered.registered.cache.size = 4 ∧
      afterType.registered.receipts.size = 3 ∧
      afterType.registered.addresses[9001]? = some 2 ∧
      afterType.registered.addresses[9002]? = some 3 ∧ afterType.refusalChecks = 3 := by decide +kernel

theorem type_registry_extension_checked :
    NumberedSourceRegistry.preserves? beforeType.symbols afterType.symbols = true := by decide +kernel

theorem ordered_output_claims :
    (afterType.registered.registered.cache[2]?).map (fun fact => fact.sequent) =
      (NumberedSourceProofs.claim? afterType (claim 9001 19)).map (·.sequent) ∧
    (afterType.registered.registered.cache[3]?).map (fun fact => fact.sequent) =
      (NumberedSourceProofs.claim? afterType (claim 9002 27)).map (·.sequent) := by decide +kernel

theorem repeated_type_refused : (receive? afterType rawType).isNone = true := by decide +kernel

theorem swapped_type_claims_refused :
    (receive? beforeType (Json.mkObj
      [("rule",.str "TYPE_DEFINITION"),("event",.num 1000),
        ("payload",.arr #[.str "NumberedFixture",.str "ABS_NumberedFixture",.str "REP_NumberedFixture"]),
        ("parents",.arr #[.num 1]),("outputs",.arr #[claim 9002 27,claim 9001 19])])).isNone = true := by decide +kernel

theorem duplicate_output_ids_refused :
    (receive? beforeType (Json.mkObj
      [("rule",.str "TYPE_DEFINITION"),("event",.num 1000),
        ("payload",.arr #[.str "NumberedFixture",.str "ABS_NumberedFixture",.str "REP_NumberedFixture"]),
        ("parents",.arr #[.num 1]),("outputs",.arr #[claim 9001 19,claim 9001 27])])).isNone = true := by decide +kernel

def badSource : SourceTerm :=
  .app (.app (.const Const.equality (Ty.equality (Ty.function Ty.bool Ty.bool)))
    (.abs (.global "p") Ty.bool (.var (.global "p") Ty.bool)))
    (.var (.global "different_witness") (Ty.function Ty.bool Ty.bool))

def corruptedMetadata : Reading :=
  { beforeType with sourceConclusions := beforeType.sourceConclusions.insert 1 badSource }

/-- History constrains the actual registered state, not independent named
source metadata. Admission still uses the real cached existence theorem. -/
theorem history_does_not_certify_source_metadata :
    corruptedMetadata.registered = beforeType.registered ∧
      (receive? corruptedMetadata rawType).isSome = true ∧
      badSource.check ≠ (beforeType.registered.registered.cache[1]?).map (fun fact => fact.sequent.concl) := by
  refine ⟨rfl,?_,?_⟩ <;> decide +kernel

theorem corrupted_metadata_not_checked : ¬ ConclusionsChecked corruptedMetadata := by
  intro coherent
  have stored : corruptedMetadata.sourceConclusions[1]? = some badSource := by simp [corruptedMetadata]
  obtain ⟨position,fact,addressAt,factAt,checked⟩ := coherent 1 badSource stored
  have actualAddress : corruptedMetadata.registered.addresses[1]? = some 1 := by decide +kernel
  have positionEq := Option.some.inj (addressAt.symm.trans actualAddress)
  subst position
  change beforeType.registered.registered.cache[1]? = some fact at factAt
  apply history_does_not_certify_source_metadata.2.2
  rw [factAt]
  exact checked

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NumberedSourceDeclarationsControls
