import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ApplicationEquivariance
import MettaHyperonFull.Minimal.Interpreter
import MettaHyperonFull.Proofs.Substitution

/-!
# Pre-instantiated argument-type counterexample

This witness distinguishes a literal `Atom` parameter from a type variable
that an earlier argument has bound to `Atom`.  The published argument scan
matches each raw formal under the threaded presentation.  The retired runtime
path instead instantiated a later formal before testing the gradual-top
syntax, so the bound value was exposed as a wildcard and an incompatible
second argument was accepted.

The module permanently records the retired capability and its repaired
replacement.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaArgumentTypeSelectionCounterexample

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.Spec.Type
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Exact
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ApplicationEquivariance
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

private def firstActualType : Metta.Atom :=
  .expr [.sym "P", .sym "Atom"]

private def argumentEnv : Metta.Minimal.MinEnv :=
  Metta.Minimal.MinEnv.ofAtomsGT [
    .expr [.sym ":", .sym "argument-a", firstActualType],
    .expr [.sym ":", .sym "argument-b", .sym "B"]] []

private theorem first_argument_match : Metta.Minimal.matchType []
    (.expr [.sym "P", .var "t"])
    (.expr [.sym "P", .sym "Atom"]) =
      some [.val "t" (.sym "Atom")] := by
  have hloop : Metta.Bindings.hasLoop
      ([.val "t" (.sym "Atom")] : Metta.Bindings) = false := by
    simpa using Metta.Bindings.hasLoop_singleton_val_of_not_mem
      "t" (.sym "Atom") (by simp [Metta.Atom.vars])
  simp [Metta.Minimal.matchType, Metta.Minimal.matchReduced,
    Metta.Minimal.matchReducedList, Metta.matchAtoms,
    Metta.matchAtomsWith, Metta.Bindings.merge,
    Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
    Metta.Bindings.addValRaw, Metta.Bindings.removeVal,
    Metta.Atom.beq, BEq.beq, hloop]

private theorem second_instantiated_argument_match :
    Metta.Minimal.matchType [.val "t" (.sym "Atom")]
      (.sym "Atom") (.sym "B") =
        some [.val "t" (.sym "Atom")] := by
  rfl

private def preinstantiatedArgumentGate
    (bindings : Metta.Bindings) (formal actual : Metta.Atom) :
    Option Metta.Bindings :=
  Metta.Minimal.matchType bindings
    (Metta.instantiate bindings formal) actual

/-- The retired eager-instantiation step exposes a later formal `$t`, already
bound to literal `Atom`, as a new gradual wildcard and accepts `B`. -/
theorem preinstantiated_argument_exposes_bound_atom_wildcard :
    preinstantiatedArgumentGate [.val "t" (.sym "Atom")]
      (.var "t") (.sym "B") =
        some [.val "t" (.sym "Atom")] := by
  rw [preinstantiatedArgumentGate,
    Metta.instantiate_singleton_val_var_of_not_mem
      "t" (.sym "Atom") (by simp [Metta.Atom.vars])]
  exact second_instantiated_argument_match

/-- Repaired runtime behaviour: the second argument is checked against raw
formal `$t` under the threaded binding `t = Atom`, so incompatible `B` is
rejected.  The instantiated `Atom` appears only in the diagnostic. -/
theorem repaired_argument_scan_rejects_bound_atom :
    Metta.Minimal.typeCheckArgsOutcome argumentEnv
      Metta.Minimal.World.empty
      [.expr [.sym "P", .var "t"], .var "t"] 0 []
      [.sym "argument-a", .sym "argument-b"] =
        .failure 2 (.sym "Atom") (.sym "B") := by
  have hprepA : Metta.Minimal.typePrep Metta.Minimal.World.empty
      (.sym "argument-a") = .sym "argument-a" := by
    simp [Metta.Minimal.typePrep, Metta.Minimal.subTokens.eq_1,
      Metta.Minimal.wrapStates.eq_3, Metta.Minimal.World.empty]
  have hprepB : Metta.Minimal.typePrep Metta.Minimal.World.empty
      (.sym "argument-b") = .sym "argument-b" := by
    simp [Metta.Minimal.typePrep, Metta.Minimal.subTokens.eq_1,
      Metta.Minimal.wrapStates.eq_3, Metta.Minimal.World.empty]
  have ha : Metta.Minimal.getTypes argumentEnv (.sym "argument-a") =
      [firstActualType] := by
    rw [Metta.Minimal.getTypes.eq_8]
    simp [argumentEnv, firstActualType, Metta.Minimal.MinEnv.ofAtomsGT,
      Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity]
  have hb : Metta.Minimal.getTypes argumentEnv (.sym "argument-b") =
      [.sym "B"] := by
    rw [Metta.Minimal.getTypes.eq_8]
    simp [argumentEnv, firstActualType, Metta.Minimal.MinEnv.ofAtomsGT,
      Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity]
  have hinstantiate : Metta.instantiate [.val "t" (.sym "Atom")]
      (.var "t") = .sym "Atom" := by
    exact Metta.instantiate_singleton_val_var_of_not_mem
      "t" (.sym "Atom") (by simp [Metta.Atom.vars])
  have hresolve : Metta.Bindings.resolveAtom
      [.val "t" (.sym "Atom")] (.var "t") = .sym "Atom" := by
    simpa [Metta.instantiate] using hinstantiate
  have hreject : Metta.Minimal.matchType
      [.val "t" (.sym "Atom")] (.var "t") (.sym "B") = none := by
    simp [Metta.Minimal.matchType, Metta.Minimal.matchReduced,
      Metta.matchAtoms, Metta.matchAtomsWith, Metta.Bindings.merge,
      Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
      Metta.Bindings.addValRaw, Metta.Bindings.removeVal,
      Metta.Bindings.unifyValues, Metta.Unify.unifyRounds,
      Metta.Unify.decomposeAll, Metta.Unify.decomposeEq,
      Metta.Atom.size, Metta.Atom.beq, BEq.beq]
  simp [Metta.Minimal.typeCheckArgsOutcome,
    Metta.Minimal.typeCheckArgsDetailedOutcome,
    Metta.Minimal.typeCheckArgsDetailedOutcomeScoped,
    Metta.Minimal.applicationTypeInferenceScope,
    Metta.Minimal.scanActualTypes,
    hprepA, hprepB, ha, hb, firstActualType,
    Metta.Minimal.freshenTypeCandidate,
    Metta.Minimal.renameAllVars, Metta.instantiate,
    first_argument_match, hresolve, hreject]

/-- The executable-independent presentation scan rejects the same arguments.
Its first constraint forces `t = Atom`, whereas its second constraint requires
that same `t` to agree with `B`; no valuation satisfies both. -/
theorem raw_argument_scan_rejects_bound_atom :
    ¬∃ output,
      PresentationArgumentListMatchRel
        [.expression [.symbol "P", .var "t"], .var "t"]
        [.expression [.symbol "P", .symbol "Atom"], .symbol "B"]
        [] output := by
  intro success
  have model := (presentationArgumentList_exists_iff
    [.expression [.symbol "P", .var "t"], .var "t"]
    [.expression [.symbol "P", .symbol "Atom"], .symbol "B"]).mp success
  rcases model with ⟨valuation, consistency⟩
  cases consistency with
  | cons firstConsistency secondConstraints =>
      cases secondConstraints with
      | cons secondConsistency tailConsistency =>
          simp [CorePlusR2TypeConsistent, ReducedTypeConsistent,
            ReducedTypeListConsistent, applyTypeValuation,
            Atom.undefinedType, Atom.atomType] at firstConsistency secondConsistency
          rw [firstConsistency] at secondConsistency
          simp at secondConsistency

end Mettapedia.Languages.MeTTa.HE.LeaTTaArgumentTypeSelectionCounterexample
