import Mettapedia.GSLT.LanguageDef.C0PureNTT
import Mettapedia.OSLF.MeTTaIL.RelationQueryAdmission

/-!
# Constructive transition admission for C0-pure

These lemmas turn explicit relation-environment rows into authored C0
transitions.  They are parameterized by opaque programs, stores, labels, and
values, so downstream compiler proofs do not unfold a generated program while
proving generic matcher and premise plumbing.
-/

namespace Mettapedia.GSLT.LanguageDef.C0PureTransitionAdmission

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution
open Mettapedia.OSLF.MeTTaIL.RelationQueryAdmission
open Mettapedia.GSLT.LanguageDef.C0PureNTT

def consumedBindings
    (program pc store fuel receipt nextFuel : Pattern) : Bindings :=
  ("nextFuel", nextFuel) ::
    runMatchBindings program pc store fuel receipt

def callFetchedBindings
    (program pc store fuel receipt nextFuel external
      ifValue ifLanguageFault ifEngineFault ifResourceFault : Pattern) :
    Bindings :=
  ("external", external) ::
  ("ifLanguageFault", ifLanguageFault) ::
  ("ifResourceFault", ifResourceFault) ::
  ("ifEngineFault", ifEngineFault) ::
  ("ifValue", ifValue) ::
    consumedBindings program pc store fuel receipt nextFuel

def callValueBindings
    (program pc store fuel receipt nextFuel external
      ifValue ifLanguageFault ifEngineFault ifResourceFault nextStore : Pattern) :
    Bindings :=
  ("nextStore", nextStore) ::
    callFetchedBindings program pc store fuel receipt nextFuel external
      ifValue ifLanguageFault ifEngineFault ifResourceFault

/-! ## Exact substitution boundary for the common running configuration -/

@[simp] theorem applyBindings_run_program
    (program pc store fuel receipt : Pattern) :
    applyBindings (runMatchBindings program pc store fuel receipt)
        (v "program") = program := by
  simp [runMatchBindings, v, applyBindings]

@[simp] theorem applyBindings_run_pc
    (program pc store fuel receipt : Pattern) :
    applyBindings (runMatchBindings program pc store fuel receipt)
        (v "pc") = pc := by
  simp [runMatchBindings, v, applyBindings]

@[simp] theorem applyBindings_run_store
    (program pc store fuel receipt : Pattern) :
    applyBindings (runMatchBindings program pc store fuel receipt)
        (v "store") = store := by
  simp [runMatchBindings, v, applyBindings]

@[simp] theorem applyBindings_run_fuel
    (program pc store fuel receipt : Pattern) :
    applyBindings (runMatchBindings program pc store fuel receipt)
        (v "fuel") = fuel := by
  simp [runMatchBindings, v, applyBindings]

@[simp] theorem applyBindings_run_unbound
    (program pc store fuel receipt : Pattern) :
    applyBindings (runMatchBindings program pc store fuel receipt)
        (v "nextFuel") = v "nextFuel" := by
  simp [runMatchBindings, v, applyBindings]

theorem match_consume_fuel
    (program pc store fuel receipt nextFuel : Pattern) :
    [("nextFuel", nextFuel)] ∈
      matchRelationArgs
        (runMatchBindings program pc store fuel receipt)
        [v "fuel", v "nextFuel"] [fuel, nextFuel] := by
  let start := runMatchBindings program pc store fuel receipt
  let extension : Bindings := [("nextFuel", nextFuel)]
  have fuelFound : start.lookup "fuel" = some fuel := by
    simp [start, runMatchBindings, Bindings.lookup]
  have nextFuelMissing : start.lookup "nextFuel" = none := by
    simp [start, runMatchBindings, Bindings.lookup]
  have first := matchRelationArgument_bound_self fuelFound
  have second := matchRelationArgument_unbound
    (value := nextFuel) nextFuelMissing
  have merged : mergeBindings start extension =
      some (consumedBindings program pc store fuel receipt nextFuel) := by
    simp [start, extension, consumedBindings, runMatchBindings, mergeBindings]
  have tail : extension ∈
      matchRelationArgs start [v "nextFuel"] [nextFuel] := by
    exact matchRelationArgs_cons second merged
      (matchRelationArgs_nil _)
      (by simp [extension, mergeBindings])
  exact matchRelationArgs_cons first (by simp [start, mergeBindings]) tail
    (by simp [extension, mergeBindings])

theorem merge_consume_fuel
    (program pc store fuel receipt nextFuel : Pattern) :
    mergeBindings (runMatchBindings program pc store fuel receipt)
        [("nextFuel", nextFuel)] =
      some (consumedBindings program pc store fuel receipt nextFuel) := by
  simp [consumedBindings, runMatchBindings, mergeBindings]

theorem match_fetch_call_instruction
    (program pc store fuel receipt nextFuel external
      ifValue ifLanguageFault ifEngineFault ifResourceFault : Pattern) :
    callInstructionBindings external ifValue ifLanguageFault
        ifEngineFault ifResourceFault ∈
      matchRelationArgs
        (consumedBindings program pc store fuel receipt nextFuel)
        [v "program", v "pc",
          a "c0:call-binary"
            [v "external", v "ifValue", v "ifLanguageFault",
             v "ifEngineFault", v "ifResourceFault"]]
        [program, pc,
          a "c0:call-binary"
            [external, ifValue, ifLanguageFault, ifEngineFault,
             ifResourceFault]] := by
  let seed := consumedBindings program pc store fuel receipt nextFuel
  let extension := callInstructionBindings external ifValue
    ifLanguageFault ifEngineFault ifResourceFault
  let instructionSchema :=
    a "c0:call-binary"
      [v "external", v "ifValue", v "ifLanguageFault",
       v "ifEngineFault", v "ifResourceFault"]
  let instruction :=
    a "c0:call-binary"
      [external, ifValue, ifLanguageFault, ifEngineFault,
       ifResourceFault]
  have applied : applyBindings seed instructionSchema = instructionSchema := by
    simp [seed, instructionSchema, consumedBindings, runMatchBindings,
      a, v, applyBindings]
  have instructionMatched :
      extension ∈ matchRelationArgument seed instructionSchema instruction := by
    have exactMatch : extension ∈ matchPattern instructionSchema instruction := by
      rw [show matchPattern instructionSchema instruction = [extension] by
        simpa [extension, instructionSchema, instruction] using
          match_call_instruction external ifValue ifLanguageFault
            ifEngineFault ifResourceFault]
      simp
    change extension ∈
      matchPattern (applyBindings seed instructionSchema) instruction
    rw [applied]
    exact exactMatch
  have merged : mergeBindings seed extension =
      some (callFetchedBindings program pc store fuel receipt nextFuel
        external ifValue ifLanguageFault ifEngineFault ifResourceFault) := by
    simp [seed, extension, consumedBindings, callFetchedBindings,
      runMatchBindings, callInstructionBindings, mergeBindings]
  have instructionTail :
      extension ∈ matchRelationArgs seed [instructionSchema] [instruction] :=
    matchRelationArgs_single instructionMatched merged
  have pcFound : seed.lookup "pc" = some pc := by
    simp [seed, consumedBindings, runMatchBindings, Bindings.lookup]
  have pcTail : extension.reverse ∈
      matchRelationArgs seed [v "pc", instructionSchema]
        [pc, instruction] :=
    matchRelationArgs_bound_cons pcFound instructionTail (by
      simp [extension, callInstructionBindings, mergeBindings])
  have programFound : seed.lookup "program" = some program := by
    simp [seed, consumedBindings, runMatchBindings, Bindings.lookup]
  exact matchRelationArgs_bound_cons programFound pcTail (by
    simp [extension, callInstructionBindings, mergeBindings])

theorem merge_fetch_call_instruction
    (program pc store fuel receipt nextFuel external
      ifValue ifLanguageFault ifEngineFault ifResourceFault : Pattern) :
    mergeBindings
        (consumedBindings program pc store fuel receipt nextFuel)
        (callInstructionBindings external ifValue ifLanguageFault
          ifEngineFault ifResourceFault) =
      some (callFetchedBindings program pc store fuel receipt nextFuel
        external ifValue ifLanguageFault ifEngineFault ifResourceFault) := by
  simp [consumedBindings, callFetchedBindings, runMatchBindings,
    callInstructionBindings, mergeBindings]

theorem match_call_external_value
    (program pc store fuel receipt nextFuel external
      ifValue ifLanguageFault ifEngineFault ifResourceFault nextStore : Pattern) :
    [("nextStore", nextStore)] ∈
      matchRelationArgs
        (callFetchedBindings program pc store fuel receipt nextFuel
          external ifValue ifLanguageFault ifEngineFault ifResourceFault)
        [v "program", v "external", v "store",
          a "c0:external-value" [v "nextStore"]]
        [program, external, store,
          a "c0:external-value" [nextStore]] := by
  let seed := callFetchedBindings program pc store fuel receipt nextFuel
    external ifValue ifLanguageFault ifEngineFault ifResourceFault
  let extension : Bindings := [("nextStore", nextStore)]
  let outcomeSchema := a "c0:external-value" [v "nextStore"]
  let outcome := a "c0:external-value" [nextStore]
  have applied : applyBindings seed outcomeSchema = outcomeSchema := by
    simp [seed, outcomeSchema, callFetchedBindings, consumedBindings,
      runMatchBindings, a, v, applyBindings]
  have outcomeMatched :
      extension ∈ matchRelationArgument seed outcomeSchema outcome := by
    have exactMatch : extension ∈ matchPattern outcomeSchema outcome := by
      rw [show matchPattern outcomeSchema outcome = [extension] by
        simpa [extension, outcomeSchema, outcome] using
          match_external_value nextStore]
      simp
    change extension ∈ matchPattern (applyBindings seed outcomeSchema) outcome
    rw [applied]
    exact exactMatch
  have merged : mergeBindings seed extension =
      some (callValueBindings program pc store fuel receipt nextFuel
        external ifValue ifLanguageFault ifEngineFault ifResourceFault
        nextStore) := by
    simp [seed, extension, callValueBindings, callFetchedBindings,
      consumedBindings, runMatchBindings, mergeBindings]
  have outcomeTail : extension ∈
      matchRelationArgs seed [outcomeSchema] [outcome] :=
    matchRelationArgs_single outcomeMatched merged
  have storeFound : seed.lookup "store" = some store := by
    simp [seed, callFetchedBindings, consumedBindings, runMatchBindings,
      Bindings.lookup]
  have storeTail : extension ∈
      matchRelationArgs seed [v "store", outcomeSchema] [store, outcome] :=
    matchRelationArgs_bound_cons storeFound outcomeTail (by
      simp [extension, mergeBindings])
  have externalFound : seed.lookup "external" = some external := by
    simp [seed, callFetchedBindings, consumedBindings, runMatchBindings,
      Bindings.lookup]
  have externalTail : extension ∈
      matchRelationArgs seed [v "external", v "store", outcomeSchema]
        [external, store, outcome] :=
    matchRelationArgs_bound_cons externalFound storeTail (by
      simp [extension, mergeBindings])
  have programFound : seed.lookup "program" = some program := by
    simp [seed, callFetchedBindings, consumedBindings, runMatchBindings,
      Bindings.lookup]
  exact matchRelationArgs_bound_cons programFound externalTail (by
    simp [extension, mergeBindings])

theorem merge_call_external_value
    (program pc store fuel receipt nextFuel external
      ifValue ifLanguageFault ifEngineFault ifResourceFault nextStore : Pattern) :
    mergeBindings
        (callFetchedBindings program pc store fuel receipt nextFuel
          external ifValue ifLanguageFault ifEngineFault ifResourceFault)
        [("nextStore", nextStore)] =
      some (callValueBindings program pc store fuel receipt nextFuel
        external ifValue ifLanguageFault ifEngineFault ifResourceFault
        nextStore) := by
  simp [callValueBindings, callFetchedBindings, consumedBindings,
    runMatchBindings, mergeBindings]

/-! ## Zero-branch premise fibres -/

def branchFetchedBindings
    (program pc store fuel receipt nextFuel slot ifZero ifNonzero : Pattern) :
    Bindings :=
  ("slot", slot) :: ("ifNonzero", ifNonzero) :: ("ifZero", ifZero) ::
    consumedBindings program pc store fuel receipt nextFuel

def branchReadBindings
    (program pc store fuel receipt nextFuel slot ifZero ifNonzero value : Pattern) :
    Bindings :=
  ("value", value) ::
    branchFetchedBindings program pc store fuel receipt nextFuel
      slot ifZero ifNonzero

theorem match_fetch_branch_instruction
    (program pc store fuel receipt nextFuel slot ifZero ifNonzero : Pattern) :
    branchInstructionBindings slot ifZero ifNonzero ∈
      matchRelationArgs
        (consumedBindings program pc store fuel receipt nextFuel)
        [v "program", v "pc",
          a "c0:branch-zero" [v "slot", v "ifZero", v "ifNonzero"]]
        [program, pc, a "c0:branch-zero" [slot, ifZero, ifNonzero]] := by
  let seed := consumedBindings program pc store fuel receipt nextFuel
  let extension := branchInstructionBindings slot ifZero ifNonzero
  let instructionSchema :=
    a "c0:branch-zero" [v "slot", v "ifZero", v "ifNonzero"]
  let instruction := a "c0:branch-zero" [slot, ifZero, ifNonzero]
  have applied : applyBindings seed instructionSchema = instructionSchema := by
    simp [seed, instructionSchema, consumedBindings, runMatchBindings,
      a, v, applyBindings]
  have instructionMatched :
      extension ∈ matchRelationArgument seed instructionSchema instruction := by
    have exactMatch : extension ∈ matchPattern instructionSchema instruction := by
      rw [show matchPattern instructionSchema instruction = [extension] by
        simpa [extension, instructionSchema, instruction] using
          match_branch_instruction slot ifZero ifNonzero]
      simp
    change extension ∈
      matchPattern (applyBindings seed instructionSchema) instruction
    rw [applied]
    exact exactMatch
  have merged : mergeBindings seed extension =
      some (branchFetchedBindings program pc store fuel receipt nextFuel
        slot ifZero ifNonzero) := by
    simp [seed, extension, branchFetchedBindings, consumedBindings,
      runMatchBindings, branchInstructionBindings, mergeBindings]
  have instructionTail :
      extension ∈ matchRelationArgs seed [instructionSchema] [instruction] :=
    matchRelationArgs_single instructionMatched merged
  have pcFound : seed.lookup "pc" = some pc := by
    simp [seed, consumedBindings, runMatchBindings, Bindings.lookup]
  have pcTail : extension.reverse ∈
      matchRelationArgs seed [v "pc", instructionSchema]
        [pc, instruction] :=
    matchRelationArgs_bound_cons pcFound instructionTail (by
      simp [extension, branchInstructionBindings, mergeBindings])
  have programFound : seed.lookup "program" = some program := by
    simp [seed, consumedBindings, runMatchBindings, Bindings.lookup]
  exact matchRelationArgs_bound_cons programFound pcTail (by
    simp [extension, branchInstructionBindings, mergeBindings])

theorem merge_fetch_branch_instruction
    (program pc store fuel receipt nextFuel slot ifZero ifNonzero : Pattern) :
    mergeBindings
        (consumedBindings program pc store fuel receipt nextFuel)
        (branchInstructionBindings slot ifZero ifNonzero) =
      some (branchFetchedBindings program pc store fuel receipt nextFuel
        slot ifZero ifNonzero) := by
  simp [branchFetchedBindings, consumedBindings, runMatchBindings,
    branchInstructionBindings, mergeBindings]

theorem match_read_branch_slot
    (program pc store fuel receipt nextFuel slot ifZero ifNonzero value : Pattern) :
    [("value", value)] ∈
      matchRelationArgs
        (branchFetchedBindings program pc store fuel receipt nextFuel
          slot ifZero ifNonzero)
        [v "store", v "slot", v "value"] [store, slot, value] := by
  let seed := branchFetchedBindings program pc store fuel receipt nextFuel
    slot ifZero ifNonzero
  let extension : Bindings := [("value", value)]
  have valueMissing : seed.lookup "value" = none := by
    simp [seed, branchFetchedBindings, consumedBindings, runMatchBindings,
      Bindings.lookup]
  have valueMatched := matchRelationArgument_unbound
    (value := value) valueMissing
  have merged : mergeBindings seed extension =
      some (branchReadBindings program pc store fuel receipt nextFuel
        slot ifZero ifNonzero value) := by
    simp [seed, extension, branchReadBindings, branchFetchedBindings,
      consumedBindings, runMatchBindings, mergeBindings]
  have valueTail : extension ∈
      matchRelationArgs seed [v "value"] [value] :=
    matchRelationArgs_single valueMatched merged
  have slotFound : seed.lookup "slot" = some slot := by
    simp [seed, branchFetchedBindings, consumedBindings, runMatchBindings,
      Bindings.lookup]
  have slotTail : extension ∈
      matchRelationArgs seed [v "slot", v "value"] [slot, value] :=
    matchRelationArgs_bound_cons slotFound valueTail (by
      simp [extension, mergeBindings])
  have storeFound : seed.lookup "store" = some store := by
    simp [seed, branchFetchedBindings, consumedBindings, runMatchBindings,
      Bindings.lookup]
  exact matchRelationArgs_bound_cons storeFound slotTail (by
    simp [extension, mergeBindings])

theorem merge_read_branch_slot
    (program pc store fuel receipt nextFuel slot ifZero ifNonzero value : Pattern) :
    mergeBindings
        (branchFetchedBindings program pc store fuel receipt nextFuel
          slot ifZero ifNonzero)
        [("value", value)] =
      some (branchReadBindings program pc store fuel receipt nextFuel
        slot ifZero ifNonzero value) := by
  simp [branchReadBindings, branchFetchedBindings, consumedBindings,
    runMatchBindings, mergeBindings]

theorem match_bound_value_test
    (bindings : Bindings) (value : Pattern)
    (found : bindings.lookup "value" = some value) :
    [] ∈ matchRelationArgs bindings [v "value"] [value] := by
  exact matchRelationArgs_bound_cons found (matchRelationArgs_nil bindings)
    (by simp [mergeBindings])

/-- A generic authored branch edge.  The caller supplies the selected named
rule and its concrete right-hand instantiation, keeping zero and nonzero
selection explicit rather than hidden in an implementation dispatcher. -/
theorem branchTransition_mem_rewriteAt
    (relationEnv : RelationEnv) (rule : RewriteRule)
    (test : String)
    (program pc store fuel receipt nextFuel slot ifZero ifNonzero value
      target : Pattern)
    (ruleMember : rule ∈ c0Pure.rewrites)
    (rulePremises : rule.premises = [
      query "C0ConsumeFuel" [v "fuel", v "nextFuel"],
      fetch (a "c0:branch-zero" [v "slot", v "ifZero", v "ifNonzero"]),
      query "C0ReadSlot" [v "store", v "slot", v "value"],
      query test [v "value"]])
    (ruleLeft : rule.left =
      run (v "program") (v "pc") (v "store") (v "fuel") (v "receipt"))
    (ruleTarget :
      applyBindingsForRule c0Pure rule
        (branchReadBindings program pc store fuel receipt nextFuel
          slot ifZero ifNonzero value) =
        run program target store nextFuel (stepReceipt pc receipt))
    (consumeRow :
      [fuel, nextFuel] ∈ relationEnv.tuples "C0ConsumeFuel"
        ([v "fuel", v "nextFuel"].map
          (applyBindings
            (runMatchBindings program pc store fuel receipt))))
    (fetchRow :
      [program, pc, a "c0:branch-zero" [slot, ifZero, ifNonzero]] ∈
        relationEnv.tuples "C0FetchInstruction"
          ([v "program", v "pc",
            a "c0:branch-zero" [v "slot", v "ifZero", v "ifNonzero"]].map
            (applyBindings
              (consumedBindings program pc store fuel receipt nextFuel))))
    (readRow :
      [store, slot, value] ∈ relationEnv.tuples "C0ReadSlot"
        ([v "store", v "slot", v "value"].map
          (applyBindings
            (branchFetchedBindings program pc store fuel receipt nextFuel
              slot ifZero ifNonzero))))
    (testRow :
      [value] ∈ relationEnv.tuples test
        ([v "value"].map
          (applyBindings
            (branchReadBindings program pc store fuel receipt nextFuel
              slot ifZero ifNonzero value)))) :
    run program target store nextFuel (stepReceipt pc receipt) ∈
      rewriteAt (engineBasePremises relationEnv) c0Pure 1
        (run program pc store fuel receipt) := by
  let start := runMatchBindings program pc store fuel receipt
  let afterFuel := consumedBindings program pc store fuel receipt nextFuel
  let afterFetch := branchFetchedBindings program pc store fuel receipt
    nextFuel slot ifZero ifNonzero
  let final := branchReadBindings program pc store fuel receipt nextFuel
    slot ifZero ifNonzero value
  have consumePremise :
      afterFuel ∈ premiseStepWithEnv relationEnv c0Pure start
        (query "C0ConsumeFuel" [v "fuel", v "nextFuel"]) := by
    apply premiseStepWithEnv_relationQuery_of_env_tuple
      (tuple := [fuel, nextFuel])
      (extension := [("nextFuel", nextFuel)])
    · exact consumeRow
    · simpa [start] using
        match_consume_fuel program pc store fuel receipt nextFuel
    · simpa [start, afterFuel] using
        merge_consume_fuel program pc store fuel receipt nextFuel
  have fetchPremise :
      afterFetch ∈ premiseStepWithEnv relationEnv c0Pure afterFuel
        (fetch (a "c0:branch-zero"
          [v "slot", v "ifZero", v "ifNonzero"])) := by
    apply premiseStepWithEnv_relationQuery_of_env_tuple
      (tuple := [program, pc,
        a "c0:branch-zero" [slot, ifZero, ifNonzero]])
      (extension := branchInstructionBindings slot ifZero ifNonzero)
    · exact fetchRow
    · simpa [afterFuel] using
        match_fetch_branch_instruction program pc store fuel receipt nextFuel
          slot ifZero ifNonzero
    · simpa [afterFuel, afterFetch] using
        merge_fetch_branch_instruction program pc store fuel receipt nextFuel
          slot ifZero ifNonzero
  have readPremise :
      final ∈ premiseStepWithEnv relationEnv c0Pure afterFetch
        (query "C0ReadSlot" [v "store", v "slot", v "value"]) := by
    apply premiseStepWithEnv_relationQuery_of_env_tuple
      (tuple := [store, slot, value])
      (extension := [("value", value)])
    · exact readRow
    · simpa [afterFetch] using
        match_read_branch_slot program pc store fuel receipt nextFuel
          slot ifZero ifNonzero value
    · simpa [afterFetch, final] using
        merge_read_branch_slot program pc store fuel receipt nextFuel
          slot ifZero ifNonzero value
  have testPremise :
      final ∈ premiseStepWithEnv relationEnv c0Pure final
        (query test [v "value"]) := by
    apply premiseStepWithEnv_relationQuery_of_env_tuple
      (tuple := [value]) (extension := [])
    · exact testRow
    · apply match_bound_value_test
      simp [final, branchReadBindings, Bindings.lookup]
    · simp [mergeBindings]
  have premiseEvidence :
      PremisesAt (engineBasePremises relationEnv) c0Pure 0 start
        rule.premises final := by
    rw [rulePremises]
    exact .cons (.relationQuery (by
        simpa [engineBasePremises, query] using consumePremise))
      (.cons (.relationQuery (by
          simpa [engineBasePremises, fetch, query] using fetchPremise))
        (.cons (.relationQuery (by
            simpa [engineBasePremises, query] using readPremise))
          (.cons (.relationQuery (by
              simpa [engineBasePremises, query] using testPremise))
            (.nil final))))
  apply mem_rewriteAt_iff_stepAt.mpr
  exact .rule ruleMember
    (by rw [match_run_transition rule ruleLeft]; simp [start])
    premiseEvidence ruleTarget

/-! ## Terminal value and decline edges -/

def returnFetchedBindings
    (program pc store fuel receipt nextFuel slot : Pattern) : Bindings :=
  ("slot", slot) ::
    consumedBindings program pc store fuel receipt nextFuel

def returnReadBindings
    (program pc store fuel receipt nextFuel slot value : Pattern) : Bindings :=
  ("value", value) ::
    returnFetchedBindings program pc store fuel receipt nextFuel slot

theorem match_fetch_return_value
    (program pc store fuel receipt nextFuel slot : Pattern) :
    [("slot", slot)] ∈
      matchRelationArgs
        (consumedBindings program pc store fuel receipt nextFuel)
        [v "program", v "pc", a "c0:return-value" [v "slot"]]
        [program, pc, a "c0:return-value" [slot]] := by
  let seed := consumedBindings program pc store fuel receipt nextFuel
  let extension : Bindings := [("slot", slot)]
  let instructionSchema := a "c0:return-value" [v "slot"]
  let instruction := a "c0:return-value" [slot]
  have applied : applyBindings seed instructionSchema = instructionSchema := by
    simp [seed, instructionSchema, consumedBindings, runMatchBindings,
      a, v, applyBindings]
  have instructionMatched :
      extension ∈ matchRelationArgument seed instructionSchema instruction := by
    have exactMatch : extension ∈ matchPattern instructionSchema instruction := by
      rw [show matchPattern instructionSchema instruction = [extension] by
        simpa [extension, instructionSchema, instruction] using
          match_return_value slot]
      simp
    change extension ∈
      matchPattern (applyBindings seed instructionSchema) instruction
    rw [applied]
    exact exactMatch
  have merged : mergeBindings seed extension =
      some (returnFetchedBindings program pc store fuel receipt nextFuel slot) := by
    simp [seed, extension, returnFetchedBindings, consumedBindings,
      runMatchBindings, mergeBindings]
  have instructionTail : extension ∈
      matchRelationArgs seed [instructionSchema] [instruction] :=
    matchRelationArgs_single instructionMatched merged
  have pcFound : seed.lookup "pc" = some pc := by
    simp [seed, consumedBindings, runMatchBindings, Bindings.lookup]
  have pcTail : extension ∈
      matchRelationArgs seed [v "pc", instructionSchema]
        [pc, instruction] :=
    matchRelationArgs_bound_cons pcFound instructionTail (by
      simp [extension, mergeBindings])
  have programFound : seed.lookup "program" = some program := by
    simp [seed, consumedBindings, runMatchBindings, Bindings.lookup]
  exact matchRelationArgs_bound_cons programFound pcTail (by
    simp [extension, mergeBindings])

theorem merge_fetch_return_value
    (program pc store fuel receipt nextFuel slot : Pattern) :
    mergeBindings (consumedBindings program pc store fuel receipt nextFuel)
        [("slot", slot)] =
      some (returnFetchedBindings program pc store fuel receipt nextFuel slot) := by
  simp [returnFetchedBindings, consumedBindings, runMatchBindings,
    mergeBindings]

theorem match_read_return_slot
    (program pc store fuel receipt nextFuel slot value : Pattern) :
    [("value", value)] ∈
      matchRelationArgs
        (returnFetchedBindings program pc store fuel receipt nextFuel slot)
        [v "store", v "slot", v "value"] [store, slot, value] := by
  let seed := returnFetchedBindings program pc store fuel receipt nextFuel slot
  let extension : Bindings := [("value", value)]
  have valueMissing : seed.lookup "value" = none := by
    simp [seed, returnFetchedBindings, consumedBindings, runMatchBindings,
      Bindings.lookup]
  have valueMatched := matchRelationArgument_unbound
    (value := value) valueMissing
  have merged : mergeBindings seed extension =
      some (returnReadBindings program pc store fuel receipt nextFuel
        slot value) := by
    simp [seed, extension, returnReadBindings, returnFetchedBindings,
      consumedBindings, runMatchBindings, mergeBindings]
  have valueTail : extension ∈
      matchRelationArgs seed [v "value"] [value] :=
    matchRelationArgs_single valueMatched merged
  have slotFound : seed.lookup "slot" = some slot := by
    simp [seed, returnFetchedBindings, consumedBindings, runMatchBindings,
      Bindings.lookup]
  have slotTail : extension ∈
      matchRelationArgs seed [v "slot", v "value"] [slot, value] :=
    matchRelationArgs_bound_cons slotFound valueTail (by
      simp [extension, mergeBindings])
  have storeFound : seed.lookup "store" = some store := by
    simp [seed, returnFetchedBindings, consumedBindings, runMatchBindings,
      Bindings.lookup]
  exact matchRelationArgs_bound_cons storeFound slotTail (by
    simp [extension, mergeBindings])

theorem merge_read_return_slot
    (program pc store fuel receipt nextFuel slot value : Pattern) :
    mergeBindings
        (returnFetchedBindings program pc store fuel receipt nextFuel slot)
        [("value", value)] =
      some (returnReadBindings program pc store fuel receipt nextFuel
        slot value) := by
  simp [returnReadBindings, returnFetchedBindings, consumedBindings,
    runMatchBindings, mergeBindings]

theorem returnValueTransition_mem_rewriteAt
    (relationEnv : RelationEnv)
    (program pc store fuel receipt nextFuel slot value : Pattern)
    (consumeRow :
      [fuel, nextFuel] ∈ relationEnv.tuples "C0ConsumeFuel"
        ([v "fuel", v "nextFuel"].map
          (applyBindings
            (runMatchBindings program pc store fuel receipt))))
    (fetchRow :
      [program, pc, a "c0:return-value" [slot]] ∈
        relationEnv.tuples "C0FetchInstruction"
          ([v "program", v "pc", a "c0:return-value" [v "slot"]].map
            (applyBindings
              (consumedBindings program pc store fuel receipt nextFuel))))
    (readRow :
      [store, slot, value] ∈ relationEnv.tuples "C0ReadSlot"
        ([v "store", v "slot", v "value"].map
          (applyBindings
            (returnFetchedBindings program pc store fuel receipt nextFuel
              slot)))) :
    halted (a "c0:outcome-value" [value]) (stepReceipt pc receipt) ∈
      rewriteAt (engineBasePremises relationEnv) c0Pure 1
        (run program pc store fuel receipt) := by
  let start := runMatchBindings program pc store fuel receipt
  let afterFuel := consumedBindings program pc store fuel receipt nextFuel
  let afterFetch := returnFetchedBindings program pc store fuel receipt
    nextFuel slot
  let final := returnReadBindings program pc store fuel receipt nextFuel
    slot value
  have consumePremise :
      afterFuel ∈ premiseStepWithEnv relationEnv c0Pure start
        (query "C0ConsumeFuel" [v "fuel", v "nextFuel"]) := by
    apply premiseStepWithEnv_relationQuery_of_env_tuple
      (tuple := [fuel, nextFuel])
      (extension := [("nextFuel", nextFuel)])
    · exact consumeRow
    · simpa [start] using
        match_consume_fuel program pc store fuel receipt nextFuel
    · simpa [start, afterFuel] using
        merge_consume_fuel program pc store fuel receipt nextFuel
  have fetchPremise :
      afterFetch ∈ premiseStepWithEnv relationEnv c0Pure afterFuel
        (fetch (a "c0:return-value" [v "slot"])) := by
    apply premiseStepWithEnv_relationQuery_of_env_tuple
      (tuple := [program, pc, a "c0:return-value" [slot]])
      (extension := [("slot", slot)])
    · exact fetchRow
    · simpa [afterFuel] using
        match_fetch_return_value program pc store fuel receipt nextFuel slot
    · simpa [afterFuel, afterFetch] using
        merge_fetch_return_value program pc store fuel receipt nextFuel slot
  have readPremise :
      final ∈ premiseStepWithEnv relationEnv c0Pure afterFetch
        (query "C0ReadSlot" [v "store", v "slot", v "value"]) := by
    apply premiseStepWithEnv_relationQuery_of_env_tuple
      (tuple := [store, slot, value])
      (extension := [("value", value)])
    · exact readRow
    · simpa [afterFetch] using
        match_read_return_slot program pc store fuel receipt nextFuel slot value
    · simpa [afterFetch, final] using
        merge_read_return_slot program pc store fuel receipt nextFuel slot value
  have premiseEvidence :
      PremisesAt (engineBasePremises relationEnv) c0Pure 0 start
        returnValueTransition.premises final := by
    simp only [returnValueTransition]
    exact .cons (.relationQuery (by
        simpa [engineBasePremises, consumeFuel, query] using consumePremise))
      (.cons (.relationQuery (by
          simpa [engineBasePremises, fetch, query] using fetchPremise))
        (.cons (.relationQuery (by
            simpa [engineBasePremises, query] using readPremise))
          (.nil final)))
  apply mem_rewriteAt_iff_stepAt.mpr
  refine .rule ?_ ?_ premiseEvidence ?_
  · simp [c0Pure, c0PureTransitions]
  · rw [match_run_transition returnValueTransition rfl]
    simp [start]
  · simp [returnValueTransition, applyBindingsForRule_eq_syntactic,
      final, returnReadBindings, returnFetchedBindings, consumedBindings,
      runMatchBindings, applyBindings, halted, stepReceipt, run, a, v]

theorem match_fetch_return_declined
    (program pc store fuel receipt nextFuel : Pattern) :
    [] ∈ matchRelationArgs
      (consumedBindings program pc store fuel receipt nextFuel)
      [v "program", v "pc", a "c0:return-declined"]
      [program, pc, a "c0:return-declined"] := by
  let seed := consumedBindings program pc store fuel receipt nextFuel
  let instruction := a "c0:return-declined"
  have instructionMatched :
      [] ∈ matchRelationArgument seed instruction instruction := by
    change [] ∈ matchPattern (applyBindings seed instruction) instruction
    simp [instruction, a, applyBindings, matchPattern, matchArgs]
  have instructionTail : [] ∈
      matchRelationArgs seed [instruction] [instruction] :=
    matchRelationArgs_single (extended := seed) instructionMatched
      (by simp [mergeBindings])
  have pcFound : seed.lookup "pc" = some pc := by
    simp [seed, consumedBindings, runMatchBindings, Bindings.lookup]
  have pcTail : [] ∈
      matchRelationArgs seed [v "pc", instruction] [pc, instruction] :=
    matchRelationArgs_bound_cons pcFound instructionTail (by
      simp [mergeBindings])
  have programFound : seed.lookup "program" = some program := by
    simp [seed, consumedBindings, runMatchBindings, Bindings.lookup]
  exact matchRelationArgs_bound_cons programFound pcTail (by
    simp [mergeBindings])

theorem returnDeclinedTransition_mem_rewriteAt
    (relationEnv : RelationEnv)
    (program pc store fuel receipt nextFuel : Pattern)
    (consumeRow :
      [fuel, nextFuel] ∈ relationEnv.tuples "C0ConsumeFuel"
        ([v "fuel", v "nextFuel"].map
          (applyBindings
            (runMatchBindings program pc store fuel receipt))))
    (fetchRow :
      [program, pc, a "c0:return-declined"] ∈
        relationEnv.tuples "C0FetchInstruction"
          ([v "program", v "pc", a "c0:return-declined"].map
            (applyBindings
              (consumedBindings program pc store fuel receipt nextFuel)))) :
    halted (a "c0:outcome-declined") (stepReceipt pc receipt) ∈
      rewriteAt (engineBasePremises relationEnv) c0Pure 1
        (run program pc store fuel receipt) := by
  let start := runMatchBindings program pc store fuel receipt
  let final := consumedBindings program pc store fuel receipt nextFuel
  have consumePremise :
      final ∈ premiseStepWithEnv relationEnv c0Pure start
        (query "C0ConsumeFuel" [v "fuel", v "nextFuel"]) := by
    apply premiseStepWithEnv_relationQuery_of_env_tuple
      (tuple := [fuel, nextFuel])
      (extension := [("nextFuel", nextFuel)])
    · exact consumeRow
    · simpa [start] using
        match_consume_fuel program pc store fuel receipt nextFuel
    · simpa [start, final] using
        merge_consume_fuel program pc store fuel receipt nextFuel
  have fetchPremise :
      final ∈ premiseStepWithEnv relationEnv c0Pure final
        (fetch (a "c0:return-declined")) := by
    apply premiseStepWithEnv_relationQuery_of_env_tuple
      (tuple := [program, pc, a "c0:return-declined"])
      (extension := [])
    · exact fetchRow
    · simpa [final] using
        match_fetch_return_declined program pc store fuel receipt nextFuel
    · simp [mergeBindings]
  have premiseEvidence :
      PremisesAt (engineBasePremises relationEnv) c0Pure 0 start
        returnDeclinedTransition.premises final := by
    simp only [returnDeclinedTransition]
    exact .cons (.relationQuery (by
        simpa [engineBasePremises, consumeFuel, query] using consumePremise))
      (.cons (.relationQuery (by
          simpa [engineBasePremises, fetch, query] using fetchPremise))
        (.nil final))
  apply mem_rewriteAt_iff_stepAt.mpr
  refine .rule ?_ ?_ premiseEvidence ?_
  · simp [c0Pure, c0PureTransitions]
  · rw [match_run_transition returnDeclinedTransition rfl]
    simp [start]
  · simp [returnDeclinedTransition, applyBindingsForRule_eq_syntactic,
      final, consumedBindings, runMatchBindings, applyBindings,
      halted, stepReceipt, run, a, v]

/-- Exact result of the authored `c0:call-value` edge from three declared
external rows: fuel consumption, instruction fetch, and external return. -/
theorem callValueTransition_mem_rewriteAt
    (relationEnv : RelationEnv)
    (program pc store fuel receipt nextFuel external
      ifValue ifLanguageFault ifEngineFault ifResourceFault nextStore : Pattern)
    (consumeRow :
      [fuel, nextFuel] ∈ relationEnv.tuples "C0ConsumeFuel"
        ([v "fuel", v "nextFuel"].map
          (applyBindings
            (runMatchBindings program pc store fuel receipt))))
    (fetchRow :
      [program, pc,
        a "c0:call-binary"
          [external, ifValue, ifLanguageFault, ifEngineFault,
           ifResourceFault]] ∈
        relationEnv.tuples "C0FetchInstruction"
          ([v "program", v "pc",
            a "c0:call-binary"
              [v "external", v "ifValue", v "ifLanguageFault",
               v "ifEngineFault", v "ifResourceFault"]].map
            (applyBindings
              (consumedBindings program pc store fuel receipt nextFuel))))
    (callRow :
      [program, external, store, a "c0:external-value" [nextStore]] ∈
        relationEnv.tuples "C0CallBinaryExternal"
          ([v "program", v "external", v "store",
            a "c0:external-value" [v "nextStore"]].map
            (applyBindings
              (callFetchedBindings program pc store fuel receipt nextFuel
                external ifValue ifLanguageFault ifEngineFault
                ifResourceFault)))) :
    run program ifValue nextStore nextFuel
        (externalReceipt external (a "c0:external-value" [nextStore])
          pc receipt) ∈
      rewriteAt (engineBasePremises relationEnv) c0Pure 1
        (run program pc store fuel receipt) := by
  let start := runMatchBindings program pc store fuel receipt
  let afterFuel := consumedBindings program pc store fuel receipt nextFuel
  let afterFetch := callFetchedBindings program pc store fuel receipt nextFuel
    external ifValue ifLanguageFault ifEngineFault ifResourceFault
  let final := callValueBindings program pc store fuel receipt nextFuel
    external ifValue ifLanguageFault ifEngineFault ifResourceFault nextStore

  have consumePremise :
      afterFuel ∈ premiseStepWithEnv relationEnv c0Pure start
        (query "C0ConsumeFuel" [v "fuel", v "nextFuel"]) := by
    apply premiseStepWithEnv_relationQuery_of_env_tuple
      (tuple := [fuel, nextFuel])
      (extension := [("nextFuel", nextFuel)])
    · exact consumeRow
    · simpa [start] using
        match_consume_fuel program pc store fuel receipt nextFuel
    · simpa [start, afterFuel] using
        merge_consume_fuel program pc store fuel receipt nextFuel

  have fetchPremise :
      afterFetch ∈ premiseStepWithEnv relationEnv c0Pure afterFuel
        (fetch (a "c0:call-binary"
          [v "external", v "ifValue", v "ifLanguageFault",
           v "ifEngineFault", v "ifResourceFault"])) := by
    apply premiseStepWithEnv_relationQuery_of_env_tuple
      (tuple := [program, pc,
        a "c0:call-binary"
          [external, ifValue, ifLanguageFault, ifEngineFault,
           ifResourceFault]])
      (extension := callInstructionBindings external ifValue
        ifLanguageFault ifEngineFault ifResourceFault)
    · exact fetchRow
    · simpa [afterFuel] using
        match_fetch_call_instruction program pc store fuel receipt nextFuel
          external ifValue ifLanguageFault ifEngineFault ifResourceFault
    · simpa [afterFuel, afterFetch] using
        merge_fetch_call_instruction program pc store fuel receipt nextFuel
          external ifValue ifLanguageFault ifEngineFault ifResourceFault

  have callPremise :
      final ∈ premiseStepWithEnv relationEnv c0Pure afterFetch
        (query "C0CallBinaryExternal"
          [v "program", v "external", v "store",
           a "c0:external-value" [v "nextStore"]]) := by
    apply premiseStepWithEnv_relationQuery_of_env_tuple
      (tuple := [program, external, store,
        a "c0:external-value" [nextStore]])
      (extension := [("nextStore", nextStore)])
    · exact callRow
    · simpa [afterFetch] using
        match_call_external_value program pc store fuel receipt nextFuel
          external ifValue ifLanguageFault ifEngineFault ifResourceFault
          nextStore
    · simpa [afterFetch, final] using
        merge_call_external_value program pc store fuel receipt nextFuel
          external ifValue ifLanguageFault ifEngineFault ifResourceFault
          nextStore

  have premiseEvidence :
      PremisesAt (engineBasePremises relationEnv) c0Pure 0 start
        callValueTransition.premises final := by
    simp only [callValueTransition, callRule]
    exact .cons (.relationQuery (by
        simpa [engineBasePremises, query] using consumePremise))
      (.cons (.relationQuery (by
          simpa [engineBasePremises, fetch, query] using fetchPremise))
        (.cons (.relationQuery (by
            simpa [engineBasePremises, query] using callPremise))
          (.nil final)))

  apply mem_rewriteAt_iff_stepAt.mpr
  refine .rule ?_ ?_ premiseEvidence ?_
  · simp [c0Pure, c0PureTransitions]
  · rw [match_run_transition callValueTransition rfl]
    simp [start]
  · simp [callValueTransition, callRule, applyBindingsForRule_eq_syntactic,
      final, callValueBindings, callFetchedBindings, consumedBindings,
      runMatchBindings, applyBindings, externalReceipt,
      stepReceipt, run, a, v]

end Mettapedia.GSLT.LanguageDef.C0PureTransitionAdmission
