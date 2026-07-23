import Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
import MettaHyperonFull.Proofs.BindingLaws

/-!
# Cyclic reduced-type accumulator counterexample

Each leaf match below is individually loop-free.  Threading the two matches
through `matchReducedList`, however, constructs a mutually recursive type
binding and returns it without applying the public matcher's whole-result loop
filter.  The named spec R2 relation rejects the same constraint system because
it has no finite-tree model.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaTypeLoopCounterexample

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore
open Spec.Type.RuntimeRefinement

private def firstTypeBinding : Metta.Bindings :=
  [.val "x" (.expr [.sym "f", .var "y"])]

mutual

/-- Pre-repair reduced-type matching, retained only to pin the behavior that
made the cross-child cycle reachable. -/
private def legacyMatchReduced
    (bindings : Metta.Bindings) (expected actual : Metta.Atom) :
    Option Metta.Bindings :=
  if expected == .sym "%Undefined%" || actual == .sym "%Undefined%" then
    some bindings
  else match expected, actual with
    | .expr expecteds, .expr actuals =>
        legacyMatchReducedList bindings expecteds actuals
    | _, _ =>
        ((Metta.matchAtoms expected actual).flatMap
          (Metta.Bindings.merge bindings)).head?

/-- Pre-repair list companion of `legacyMatchReduced`. -/
private def legacyMatchReducedList (bindings : Metta.Bindings) :
    List Metta.Atom → List Metta.Atom → Option Metta.Bindings
  | [], [] => some bindings
  | expected :: expecteds, actual :: actuals =>
      match legacyMatchReduced bindings expected actual with
      | some next => legacyMatchReducedList next expecteds actuals
      | none => none
  | _, _ => none

end

/-- The two individually occurs-clean child equations accepted by reduced
type matching. -/
def cyclicTypeExpected : List Metta.Atom :=
  [.var "x", .var "y"]

def cyclicTypeActual : List Metta.Atom :=
  [.expr [.sym "f", .var "y"],
    .expr [.sym "f", .var "x"]]

/-- Negative legacy witness: pre-repair reduced-type list matching returned
the cyclic whole binding instead of rejecting it. -/
theorem legacyMatchReducedList_accepts_cyclic_type_binding :
    legacyMatchReducedList [] cyclicTypeExpected cyclicTypeActual =
      some Metta.crossChildCycleBindings := by
  have hxLoop : Metta.Bindings.hasLoop
      [.val "x" (.expr [.sym "f", .var "y"])] = false :=
    Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _
      (by simp [Metta.Atom.vars])
  have hxOccurs : Metta.Subst.occurs "x"
      (.expr [.sym "f", .var "y"]) = false := by
    simp [Metta.Subst.occurs]
  have hxMatch : Metta.matchAtoms (.var "x")
      (.expr [.sym "f", .var "y"]) =
        [[.val "x" (.expr [.sym "f", .var "y"])]] := by
    simp only [Metta.matchAtoms, Metta.matchAtomsWith, hxOccurs,
      Bool.false_eq_true, if_false]
    simp [hxLoop]
  have hxUndefined :
      ((.var "x" : Metta.Atom) == .sym "%Undefined%") = false := by
    rfl
  have hfxUndefined :
      ((.expr [.sym "f", .var "y"] : Metta.Atom) ==
        .sym "%Undefined%") = false := by
    rfl
  have hxValues : Metta.Bindings.classValues [] "x" = [] := by
    rfl
  have hfirst : legacyMatchReduced [] (.var "x")
      (.expr [.sym "f", .var "y"]) = some firstTypeBinding := by
    simp [legacyMatchReduced, hxUndefined, hfxUndefined, hxMatch,
      Metta.Bindings.merge, Metta.Bindings.mergeOne,
      Metta.Bindings.addVarBinding, hxValues, Metta.Bindings.addValRaw,
      Metta.Bindings.removeVal, firstTypeBinding]
  have hyLoop : Metta.Bindings.hasLoop
      [.val "y" (.expr [.sym "f", .var "x"])] = false :=
    Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _
      (by simp [Metta.Atom.vars])
  have hyOccurs : Metta.Subst.occurs "y"
      (.expr [.sym "f", .var "x"]) = false := by
    simp [Metta.Subst.occurs]
  have hyMatch : Metta.matchAtoms (.var "y")
      (.expr [.sym "f", .var "x"]) =
        [[.val "y" (.expr [.sym "f", .var "x"])]] := by
    simp only [Metta.matchAtoms, Metta.matchAtomsWith, hyOccurs,
      Bool.false_eq_true, if_false]
    simp [hyLoop]
  have hyUndefined :
      ((.var "y" : Metta.Atom) == .sym "%Undefined%") = false := by
    rfl
  have hfyUndefined :
      ((.expr [.sym "f", .var "x"] : Metta.Atom) ==
        .sym "%Undefined%") = false := by
    rfl
  have hsecond : legacyMatchReduced firstTypeBinding (.var "y")
      (.expr [.sym "f", .var "x"]) =
        some Metta.crossChildCycleBindings := by
    simp [legacyMatchReduced, hyUndefined, hfyUndefined, hyMatch,
      Metta.Bindings.merge, Metta.Bindings.mergeOne,
      Metta.Bindings.addVarBinding, Metta.Bindings.addValRaw,
      Metta.Bindings.removeVal, firstTypeBinding,
      Metta.crossChildCycleBindings]
  simp [cyclicTypeExpected, cyclicTypeActual,
    legacyMatchReducedList, hfirst, hsecond]

/-- The returned binding is semantically cyclic. -/
theorem accepted_type_binding_hasLoop :
    Metta.crossChildCycleBindings.hasLoop = true :=
  Metta.crossChildCycleBindings_hasLoop

/-- Positive repair witness: filtering the complete merged accumulator before
candidate selection rejects the cross-child cycle. -/
theorem repaired_matchReducedList_rejects_cyclic_type_binding :
    Metta.Minimal.matchReducedList [] cyclicTypeExpected cyclicTypeActual =
      none := by
  have hxLoop : Metta.Bindings.hasLoop
      [.val "x" (.expr [.sym "f", .var "y"])] = false :=
    Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _
      (by simp [Metta.Atom.vars])
  have hxOccurs : Metta.Subst.occurs "x"
      (.expr [.sym "f", .var "y"]) = false := by
    simp [Metta.Subst.occurs]
  have hxMatch : Metta.matchAtoms (.var "x")
      (.expr [.sym "f", .var "y"]) =
        [[.val "x" (.expr [.sym "f", .var "y"])]] := by
    simp only [Metta.matchAtoms, Metta.matchAtomsWith, hxOccurs,
      Bool.false_eq_true, if_false]
    simp [hxLoop]
  have hxUndefined :
      ((.var "x" : Metta.Atom) == .sym "%Undefined%") = false := by
    rfl
  have hfxUndefined :
      ((.expr [.sym "f", .var "y"] : Metta.Atom) ==
        .sym "%Undefined%") = false := by
    rfl
  have hxValues : Metta.Bindings.classValues [] "x" = [] := by
    rfl
  have hfirst : Metta.Minimal.matchReduced [] (.var "x")
      (.expr [.sym "f", .var "y"]) = some firstTypeBinding := by
    simp [Metta.Minimal.matchReduced, hxUndefined, hfxUndefined, hxMatch,
      Metta.Bindings.merge, Metta.Bindings.mergeOne,
      Metta.Bindings.addVarBinding, hxValues, Metta.Bindings.addValRaw,
      Metta.Bindings.removeVal, firstTypeBinding, hxLoop]
  have hyLoop : Metta.Bindings.hasLoop
      [.val "y" (.expr [.sym "f", .var "x"])] = false :=
    Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _
      (by simp [Metta.Atom.vars])
  have hyOccurs : Metta.Subst.occurs "y"
      (.expr [.sym "f", .var "x"]) = false := by
    simp [Metta.Subst.occurs]
  have hyMatch : Metta.matchAtoms (.var "y")
      (.expr [.sym "f", .var "x"]) =
        [[.val "y" (.expr [.sym "f", .var "x"])]] := by
    simp only [Metta.matchAtoms, Metta.matchAtomsWith, hyOccurs,
      Bool.false_eq_true, if_false]
    simp [hyLoop]
  have hyUndefined :
      ((.var "y" : Metta.Atom) == .sym "%Undefined%") = false := by
    rfl
  have hfyUndefined :
      ((.expr [.sym "f", .var "x"] : Metta.Atom) ==
        .sym "%Undefined%") = false := by
    rfl
  have hmergedLoop : Metta.Bindings.hasLoop
      [.val "y" (.expr [.sym "f", .var "x"]),
        .val "x" (.expr [.sym "f", .var "y"])] = true := by
    change Metta.crossChildCycleBindings.hasLoop = true
    exact Metta.crossChildCycleBindings_hasLoop
  have hsecond : Metta.Minimal.matchReduced firstTypeBinding (.var "y")
      (.expr [.sym "f", .var "x"]) = none := by
    simp [Metta.Minimal.matchReduced, hyUndefined, hfyUndefined, hyMatch,
      Metta.Bindings.merge, Metta.Bindings.mergeOne,
      Metta.Bindings.addVarBinding, Metta.Bindings.addValRaw,
      Metta.Bindings.removeVal, firstTypeBinding, hmergedLoop]
  simp [cyclicTypeExpected, cyclicTypeActual,
    Metta.Minimal.matchReducedList, hfirst, hsecond]

/-- specification counterpart of `cyclicTypeExpected`. -/
def specCyclicTypeExpected : Atom :=
  .expression [.var "x", .var "y"]

/-- specification counterpart of `cyclicTypeActual`. -/
def specCyclicTypeActual : Atom :=
  .expression [
    .expression [.symbol "f", .var "y"],
    .expression [.symbol "f", .var "x"]]

/-- Semantic witness: no output binding can present the R2 solution theory of
the cyclic equations, because finite HE atoms cannot contain themselves. -/
theorem no_spec_r2_model_for_cyclic_type_constraints :
    ¬∃ output,
      R2ReducedTypeMatchRel specCyclicTypeExpected specCyclicTypeActual
        Bindings.empty output := by
  rintro ⟨output, hmatch⟩
  obtain ⟨valuation, hmodel⟩ := hmatch.satisfiable
  have hconsistent := (hmatch.solutions valuation).mp hmodel |>.2
  simp only [specCyclicTypeExpected, specCyclicTypeActual,
    ReducedTypeConsistent, ReducedTypeListConsistent] at hconsistent
  rcases hconsistent with ⟨hx, hy, _⟩
  simp [applyTypeValuation] at hx hy
  rw [hy] at hx
  have hsize := congrArg sizeOf hx
  simp at hsize
  omega

end Mettapedia.Languages.MeTTa.HE.LeaTTaTypeLoopCounterexample
