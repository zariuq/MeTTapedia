import Mettapedia.Languages.MeTTa.HE.LeaTTaEvaluatorBindingObservation

/-!
# Expected-application output binding retention counterexample

The selected expected-aware application worker starts from a public
applicability binding.  Before repair #26, its intermediate and final
projections retained only variables occurring in the argument list, so a
public assignment visible solely through the expected type was seeded
correctly and then forgotten by an otherwise successful application.

The witness below is deliberately below the recursive evaluator: a quoted,
closed argument avoids every unrelated evaluation concern, and a reducer
emits one closed result.  The repaired worker retains the seed support while
still discarding an unrelated private binding produced downstream.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaExpectedApplicationBindingRetentionCounterexample

open Metta
open Metta.Minimal
open Mettapedia.Languages.MeTTa.HE.LeaTTaEvaluatorBindingObservation

private def selected : SelectedFunctionType :=
  { functionType := .expr [.sym "->", .sym "Atom"]
    argumentTypes := []
    returnType := .sym "Atom"
    typeBindings := [] }

private def unusedExpectedEvaluator
    (state : St) (bindings : Metta.Bindings) (atom _expected : Metta.Atom) :
    List (Metta.Atom × Metta.Bindings) × St :=
  ([(atom, bindings)], state)

private def emitA
    (state : St) (_application : Metta.Atom) :
    List (Metta.Atom × Metta.Bindings) × St :=
  ([(.sym "A", [])], state)

private def emitAWithPrivate
    (state : St) (_application : Metta.Atom) :
    List (Metta.Atom × Metta.Bindings) × St :=
  ([(.sym "A", [.val "private#26" (.sym "C")])], state)

def expectedOnlySeed : Metta.Bindings :=
  [.val "t" (.sym "B")]

private theorem retentionScope_eq :
    expectedApplicationRetentionScope expectedOnlySeed [] = ["t"] := by
  simp [expectedApplicationRetentionScope, expectedOnlySeed,
    Metta.Bindings.vars, Metta.Atom.vars, List.eraseDups_cons]

private theorem restrict_expectedOnlySeed :
    restrictBnd ["t"] expectedOnlySeed = expectedOnlySeed := by
  change restrictBnd ["t"]
      ([.val "t" (.sym "B")] : Metta.Bindings) =
    [.val "t" (.sym "B")]
  have resolvePublic :
      resolveAtom ([.val "t" (.sym "B")] : Metta.Bindings) 2
        (.var "t") = .sym "B" := by
    have instantiatePublic :
        instantiate ([.val "t" (.sym "B")] : Metta.Bindings)
          (.var "t") = .sym "B" :=
      instantiate_singleton_val_var_of_not_mem "t" (.sym "B") (by
        simp [Metta.Atom.vars])
    have instantiateClosed :
        instantiate ([.val "t" (.sym "B")] : Metta.Bindings)
          (.sym "B") = .sym "B" :=
      instantiate_of_closed _ _ (by simp [Metta.Atom.vars])
    have changes : ((.sym "B" : Metta.Atom) == .var "t") = false := rfl
    have stable : ((.sym "B" : Metta.Atom) == .sym "B") = true := rfl
    simp [resolveAtom, instantiatePublic, instantiateClosed, changes, stable]
  simp [restrictBnd, restrictBndRaw, resolvePublic,
    Metta.Bindings.merge, Metta.Bindings.mergeOne,
    Metta.Bindings.addVarBinding, Metta.Bindings.classValues,
    Metta.Bindings.eqClassOrdered, Metta.Bindings.eqVarsInOrder,
    Metta.Bindings.lookupVal, Metta.Bindings.addValRaw,
    Metta.Bindings.removeVal]

private theorem merge_expectedOnlySeed_empty :
    Metta.Bindings.merge expectedOnlySeed [] = [expectedOnlySeed] := by
  rfl

private theorem merge_expectedOnlySeed_private :
    Metta.Bindings.merge expectedOnlySeed
        [.val "private#26" (.sym "C")] =
      [[.val "private#26" (.sym "C"), .val "t" (.sym "B")]] := by
  rfl

private theorem restrict_expectedOnlySeed_private :
    restrictBnd ["t"]
        [.val "private#26" (.sym "C"), .val "t" (.sym "B")] =
      expectedOnlySeed := by
  change restrictBnd ["t"]
      ([.val "private#26" (.sym "C"), .val "t" (.sym "B")] :
        Metta.Bindings) = [.val "t" (.sym "B")]
  have resolvePublic :
      resolveAtom
          ([.val "private#26" (.sym "C"), .val "t" (.sym "B")] :
            Metta.Bindings)
          3 (.var "t") = .sym "B" := by
    have closed :
        Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.ClosedValueBindings
          ([.val "private#26" (.sym "C"), .val "t" (.sym "B")] :
            Metta.Bindings) := by
      exact .val (by simp [Metta.Atom.vars])
        (.val (by simp [Metta.Atom.vars]) .nil)
    have lookup :
        Metta.Bindings.resolve
            ([.val "private#26" (.sym "C"), .val "t" (.sym "B")] :
              Metta.Bindings)
            "t" = some (.sym "B") := by
      rw [Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.ClosedValueBindings.resolve_eq_lookupVal
        closed]
      rfl
    have instantiatePublic :
        instantiate
            ([.val "private#26" (.sym "C"), .val "t" (.sym "B")] :
              Metta.Bindings)
            (.var "t") = .sym "B" := by
      simp [instantiate, Metta.Bindings.resolveAtom, lookup]
    have instantiateClosed :
        instantiate
            ([.val "private#26" (.sym "C"), .val "t" (.sym "B")] :
              Metta.Bindings)
            (.sym "B") = .sym "B" :=
      instantiate_of_closed _ _ (by simp [Metta.Atom.vars])
    have changes : ((.sym "B" : Metta.Atom) == .var "t") = false := rfl
    have stable : ((.sym "B" : Metta.Atom) == .sym "B") = true := rfl
    simp [resolveAtom, instantiatePublic, instantiateClosed, changes, stable]
  simp [restrictBnd, restrictBndRaw, resolvePublic,
    Metta.Bindings.merge, Metta.Bindings.mergeOne,
    Metta.Bindings.addVarBinding, Metta.Bindings.classValues,
    Metta.Bindings.eqClassOrdered, Metta.Bindings.eqVarsInOrder,
    Metta.Bindings.lookupVal, Metta.Bindings.addValRaw,
    Metta.Bindings.removeVal]

/-- Positive repair canary: even though the nullary call contributes no
argument variables, its successful result retains the expected-only public
seed assignment. -/
theorem expectedApplicationFrom_retains_expectedOnly_seed :
    evaluateExpectedApplicationFrom unusedExpectedEvaluator emitA
      expectedOnlySeed St.init "f" [] selected =
        ([(.sym "A", expectedOnlySeed)], St.init) := by
  have notSentinel : ((.sym "A" : Metta.Atom) == .sym "NotReducible") = false := rfl
  have notApplication :
      ((.sym "A" : Metta.Atom) == .expr [.sym "f"]) = false := rfl
  have atomReturn : ((.sym "Atom" : Metta.Atom) == .sym "Atom") = true := rfl
  simp [evaluateExpectedApplicationFrom, retentionScope_eq, selected, emitA,
    restrict_expectedOnlySeed, returnsAtom, notReducibleA, instantiate_nil,
    notSentinel, notApplication, atomReturn]

/-- The retained result now extends the binding theory from which the worker
started. -/
theorem expectedApplicationFrom_expectedOnly_seed_extends :
    LeaBindingTheoryExtends expectedOnlySeed expectedOnlySeed :=
  LeaBindingTheoryExtends.refl _

/-- Negative no-leak canary: a downstream private assignment outside both the
seed and argument support is still discarded. -/
theorem expectedApplicationFrom_discards_unrelated_private :
    evaluateExpectedApplicationFrom unusedExpectedEvaluator emitAWithPrivate
      expectedOnlySeed St.init "f" [] selected =
        ([(.sym "A", expectedOnlySeed)], St.init) := by
  have notSentinel : ((.sym "A" : Metta.Atom) == .sym "NotReducible") = false := rfl
  have notApplication :
      ((.sym "A" : Metta.Atom) == .expr [.sym "f"]) = false := rfl
  have atomReturn : ((.sym "Atom" : Metta.Atom) == .sym "Atom") = true := rfl
  simp [evaluateExpectedApplicationFrom, retentionScope_eq, selected,
    emitAWithPrivate, merge_expectedOnlySeed_private,
    restrict_expectedOnlySeed_private, returnsAtom, notReducibleA,
    instantiate_nil, notSentinel, notApplication, atomReturn]

private def expectedOnlyNested : Metta.Atom :=
  .expr [.sym "metta", .expr [.sym "f"], .var "t", .sym "&self"]

private def expectedOnlyTemplate : Metta.Atom :=
  .expr [.sym ":", .var "res", .var "t"]

private def expectedOnlyContinuation : Stack :=
  [{ atom := .expr [.sym "chain", expectedOnlyNested, .var "res",
        expectedOnlyTemplate]
     ret := .chain
     vars := chainFrameVars [] expectedOnlyNested expectedOnlyTemplate }]

private theorem expectedOnlyContinuation_vars :
    varsCopy expectedOnlyContinuation = ["t"] := by
  simp [expectedOnlyContinuation, varsCopy, chainFrameVars,
    expectedOnlyNested, expectedOnlyTemplate, Metta.Atom.vars]
  rw [List.eraseDups_cons]
  simp

private theorem expectedOnlyRetentionScope :
    embeddedMettaRetentionScope expectedOnlyContinuation (.var "t") =
      ["t"] := by
  rw [embeddedMettaRetentionScope, expectedOnlyContinuation_vars]
  simp [Metta.Atom.vars]

private theorem merge_empty_expectedOnlySeed :
    Metta.Bindings.merge [] expectedOnlySeed = [expectedOnlySeed] := by
  rfl

/-- Full embedded-operation boundary canary: `chain` records the expected
variable as live, and `metta` reconciles the worker's public assignment into
the continuation binding. -/
theorem embeddedMetta_retains_live_expected_assignment :
    retainEmbeddedMettaResults expectedOnlyContinuation [] (.var "t")
        [(.sym "A", expectedOnlySeed)] =
      [finItem expectedOnlyContinuation (.sym "A") expectedOnlySeed] := by
  unfold retainEmbeddedMettaResults
  rw [expectedOnlyRetentionScope]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [restrict_expectedOnlySeed, merge_empty_expectedOnlySeed]
  rfl

private def letLocalContinuation : Stack :=
  [{ atom := .expr [.sym "return", .var "result"]
     vars := ["typecode", "mvar"] }]

private def letLocalBindings : Metta.Bindings :=
  [.val "mvar" (.sym "Q"), .val "typecode" (.sym "wff")]

/-- Negative hygiene canary: variables produced inside a `%Undefined%`
evaluation are not return-gate assignments, even when equal spellings occur
in the continuation scope. -/
theorem embeddedMetta_discards_nonexpected_let_locals :
    retainEmbeddedMettaResults letLocalContinuation expectedOnlySeed
        (.sym "%Undefined%") [(.sym "Q", letLocalBindings)] =
      [finItem letLocalContinuation (.sym "Q") expectedOnlySeed] := by
  simp [retainEmbeddedMettaResults, embeddedMettaRetentionScope,
    letLocalContinuation, letLocalBindings, Metta.Atom.vars,
    restrictBnd, restrictBndRaw, Metta.Bindings.merge]

/-- The cast freshener protects the complete continuation scope, not merely
the expected variables whose assignments will later be retained. -/
theorem embeddedMetta_cast_protects_complete_continuation :
    embeddedMettaCastProtectedScope expectedOnlyContinuation = ["t"] := by
  simpa [embeddedMettaCastProtectedScope] using expectedOnlyContinuation_vars

/-- Positive C02 canary: a successful non-expression cast returns its public
expected-type assignment to the continuation. -/
theorem embeddedMetta_cast_success_retains_expected_assignment :
    finishEmbeddedMettaCast expectedOnlyContinuation [] (.sym "A")
        (.var "t") (.inr expectedOnlySeed) =
      [finItem expectedOnlyContinuation (.sym "A") expectedOnlySeed] := by
  simpa [finishEmbeddedMettaCast] using
    embeddedMetta_retains_live_expected_assignment

/-- Negative hygiene canary: even when a cast output also carries a private
assignment, only the live expected variable reaches the continuation. -/
theorem embeddedMetta_cast_success_discards_private_assignment :
    finishEmbeddedMettaCast expectedOnlyContinuation [] (.sym "A")
        (.var "t")
        (.inr [.val "private#26" (.sym "C"), .val "t" (.sym "B")]) =
      [finItem expectedOnlyContinuation (.sym "A") expectedOnlySeed] := by
  simp [finishEmbeddedMettaCast, retainEmbeddedMettaResults,
    expectedOnlyRetentionScope, restrict_expectedOnlySeed_private,
    merge_empty_expectedOnlySeed]

/-- A rejected cast retains the incoming binding on every ordered diagnostic;
failure cannot manufacture or discard a caller solution. -/
theorem embeddedMetta_cast_failure_retains_incoming :
    finishEmbeddedMettaCast expectedOnlyContinuation expectedOnlySeed
        (.sym "A") (.sym "B") (.inl [.sym "C"]) =
      [finItem expectedOnlyContinuation
        (badTypeAtom (.sym "A") (.sym "B") (.sym "C"))
        expectedOnlySeed] := by
  rfl

end Mettapedia.Languages.MeTTa.HE.LeaTTaExpectedApplicationBindingRetentionCounterexample
