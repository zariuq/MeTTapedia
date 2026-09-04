import Mettapedia.Languages.MeTTa.HE.LeaTTaExpectedBindingThreadingCounterexample
import Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge

namespace Scratch.Repair19Canary

open Metta Metta.Minimal

private theorem visibleScope_eq :
    expectedApplicationVisibleScope
      (.expr [.sym "f", .var "t"]) (.var "t") = ["t"] := by
  unfold expectedApplicationVisibleScope
  simp only [Metta.Atom.vars, List.map, List.flatten, List.append]
  change ["t", "t"].eraseDups = ["t"]
  rw [List.eraseDups_cons]
  simp

private theorem resolve_public :
    resolveAtom ([.val "t" (.sym "B")] : Bindings) 2 (.var "t") =
      .sym "B" := by
  have hinst :
      instantiate ([.val "t" (.sym "B")] : Bindings) (.var "t") =
        .sym "B" :=
    instantiate_singleton_val_var_of_not_mem "t" (.sym "B") (by
      simp [Atom.vars])
  have hfixed :
      instantiate ([.val "t" (.sym "B")] : Bindings) (.sym "B") =
        .sym "B" :=
    instantiate_of_closed _ _ (by simp [Atom.vars])
  have hneq : ((.sym "B" : Atom) == .var "t") = false := by rfl
  have hself : ((.sym "B" : Atom) == .sym "B") = true := by rfl
  simp [resolveAtom, hinst, hfixed, hneq, hself]

private theorem restrict_public :
    restrictBnd ["t"] ([.val "t" (.sym "B")] : Bindings) =
      [.val "t" (.sym "B")] := by
  have hneq : ((.sym "B" : Atom) == .var "t") = false := by rfl
  simp [restrictBnd, resolve_public, hneq]

private theorem merge_public :
    Bindings.merge [] ([.val "t" (.sym "B")] : Bindings) =
      [[.val "t" (.sym "B")]] := by
  simp [Bindings.merge, Bindings.mergeOne, Bindings.addVarBinding,
    Bindings.classValues, Bindings.eqClassOrdered, Bindings.eqVarsInOrder,
    Bindings.lookupVal, Bindings.addValRaw, Bindings.removeVal]

example :
    selectedApplicationInitialBindings []
      (.expr [.sym "f", .var "t"]) (.var "t")
      { functionType := .expr [.sym "->", .sym "Atom", .sym "B"]
        argumentTypes := [.sym "Atom"]
        returnType := .sym "B"
        typeBindings := [.val "t" (.sym "B")] } =
      [[.val "t" (.sym "B")]] := by
  rw [selectedApplicationInitialBindings, selectedApplicationVisibleBindings,
    visibleScope_eq, restrict_public, merge_public]

private def selectedWithPrivate : SelectedFunctionType :=
  { functionType := .expr [.sym "->", .sym "Atom", .sym "B"]
    argumentTypes := [.sym "Atom"]
    returnType := .sym "B"
    typeBindings :=
      [.val "private#19" (.sym "A"), .val "t" (.sym "B")] }

private theorem resolve_public_with_private :
    resolveAtom selectedWithPrivate.typeBindings 3 (.var "t") = .sym "B" := by
  have hclosed :
      Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.ClosedValueBindings
        selectedWithPrivate.typeBindings := by
    exact .val (by simp [Atom.vars]) (.val (by simp [Atom.vars]) .nil)
  have hresolve : Bindings.resolve selectedWithPrivate.typeBindings "t" =
      some (.sym "B") := by
    rw [Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.ClosedValueBindings.resolve_eq_lookupVal
      hclosed]
    rfl
  have hinst : instantiate selectedWithPrivate.typeBindings (.var "t") =
      .sym "B" := by
    simp [instantiate, Bindings.resolveAtom, hresolve]
  have hfixed : instantiate selectedWithPrivate.typeBindings (.sym "B") =
      .sym "B" := instantiate_of_closed _ _ (by simp [Atom.vars])
  have hneq : ((.sym "B" : Atom) == .var "t") = false := by rfl
  have hself : ((.sym "B" : Atom) == .sym "B") = true := by rfl
  simp [resolveAtom, hinst, hfixed, hneq, hself]

private theorem restrict_public_with_private :
    restrictBnd ["t"] selectedWithPrivate.typeBindings =
      [.val "t" (.sym "B")] := by
  change
    restrictBnd ["t"]
      ([.val "private#19" (.sym "A"), .val "t" (.sym "B")] : Bindings) =
        [.val "t" (.sym "B")]
  have hresolve :
      resolveAtom
          ([.val "private#19" (.sym "A"), .val "t" (.sym "B")] : Bindings)
          3 (.var "t") = .sym "B" := by
    simpa [selectedWithPrivate] using resolve_public_with_private
  have hneq : ((.sym "B" : Atom) == .var "t") = false := by rfl
  simp [restrictBnd, hresolve, hneq]

example :
    .val "private#19" (.sym "A") ∉
      (selectedApplicationInitialBindings []
        (.expr [.sym "f", .var "t"]) (.var "t")
        selectedWithPrivate).flatten := by
  rw [selectedApplicationInitialBindings, selectedApplicationVisibleBindings,
    visibleScope_eq, restrict_public_with_private, merge_public]
  simp

end Scratch.Repair19Canary

#print axioms Mettapedia.Languages.MeTTa.HE.LeaTTaExpectedBindingThreadingCounterexample.selected_public_binding_is_not_seeded_into_evaluation
#print axioms Mettapedia.Languages.MeTTa.HE.LeaTTaExpectedBindingThreadingCounterexample.selected_public_binding_is_seeded_into_expected_application
#print axioms Mettapedia.Languages.MeTTa.HE.LeaTTaExpectedBindingThreadingCounterexample.selected_private_binding_does_not_leak_into_expected_application
#print axioms Mettapedia.Languages.MeTTa.HE.LeaTTaExpectedBindingThreadingCounterexample.ground_expected_application_seed_is_neutral
#print axioms Mettapedia.Languages.MeTTa.HE.LeaTTaExpectedBindingThreadingCounterexample.expected_return_gate_binds_public_variable
#print axioms Mettapedia.Languages.MeTTa.HE.LeaTTaExpectedBindingThreadingCounterexample.expected_binding_cannot_be_private
