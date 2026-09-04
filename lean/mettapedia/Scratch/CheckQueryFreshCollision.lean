import Mettapedia.Languages.MeTTa.HE.Conformance

open Metta
open Metta.Minimal

def collisionIncoming : Bindings :=
  [BindingRel.val "x#0" (.sym "b")]

def collisionPattern : Atom :=
  .expr [.sym "f", .var "x"]

def collisionQuery : Atom :=
  .expr [.sym "f", .sym "a"]

theorem freshCollision :
    (freshenRule 0 collisionPattern (.var "x")).1 =
      .expr [.sym "f", .var "x#0"] := by
  have hzero : Nat.repr 0 = "0" := by decide
  simp [collisionPattern, freshenRule, Metta.Atom.vars,
    Subst.apply, Subst.lookup, hzero]

theorem collisionMatch :
    matchAtoms (freshenRule 0 collisionPattern (.var "x")).1 collisionQuery =
      [[BindingRel.val "x#0" (.sym "a")]] := by
  rw [freshCollision]
  have hclass : Bindings.classValues ([] : Bindings) "x#0" = [] := by
    simp [Bindings.classValues, Bindings.lookupVal]
  have hadd :
      Bindings.addVarBinding [] "x#0" (.sym "a") =
        [[BindingRel.val "x#0" (.sym "a")]] := by
    simpa [Bindings.addValRaw, Bindings.removeVal] using
      (Bindings.addVarBinding_fresh hclass (by intro name h; cases h))
  have hraw :
      matchAtomsWith none
          (.expr [.sym "f", .var "x#0"])
          collisionQuery =
        [[BindingRel.val "x#0" (.sym "a")]] := by
    simp only [collisionQuery, matchAtomsWith]
    unfold matchAll
    simp [matchAtomsWith, Bindings.merge]
    unfold matchAll
    simp [matchAtomsWith, Bindings.merge]
    unfold matchAll
    have hloop :
        Bindings.hasLoop [BindingRel.val "x#0" (.sym "a")] = false :=
      Bindings.hasLoop_singleton_val_of_not_mem _ _ (by
        simp [Metta.Atom.vars])
    simp [hloop, Bindings.mergeOne, hadd]
  rw [matchAtoms, hraw]
  simp [Bindings.hasLoop_singleton_val_of_not_mem,
    Metta.Atom.vars]

theorem collisionMerge :
    Bindings.merge collisionIncoming
      [BindingRel.val "x#0" (.sym "a")] = [] := by
  have hvalues :
      Bindings.classValues collisionIncoming "x#0" = [.sym "b"] := by
    simp [collisionIncoming, Bindings.classValues,
      Bindings.eqClassOrdered, Bindings.eqVarsInOrder,
      Bindings.lookupVal]
  have hunify :
      Bindings.unifyValues ([.sym "b"] ++ [.sym "a"]) = none := by
    simp [Bindings.unifyValues, Unify.unifyRounds,
      Unify.decomposeAll, Unify.decomposeEq, Metta.Atom.size]
  have hadd :
      Bindings.addVarBinding collisionIncoming "x#0" (.sym "a") = [] :=
    Bindings.addVarBinding_conflict
      (by intro name h; cases h) hvalues (by simp) hunify
  simpa [Bindings.merge, Bindings.mergeOne] using hadd

theorem collisionCandidateContributesNoItem :
    Mettapedia.Languages.MeTTa.HE.LeaTTaBridge.queryOpItemsOfRule
        [] collisionQuery collisionIncoming 0
        (collisionPattern, .var "x") = [] := by
  simp [Mettapedia.Languages.MeTTa.HE.LeaTTaBridge.queryOpItemsOfRule,
    collisionMatch, collisionMerge]

theorem collisionIncomingProducedAtCounterZero :
    unifyOp [] (.sym "b") (.var "x#0") (.sym "ok") (.sym "fallback") [] =
      [finItem [] (.sym "ok") collisionIncoming] := by
  have hmatch :
      matchAtoms (.sym "b") (.var "x#0") =
        [[BindingRel.val "x#0" (.sym "b")]] := by
    simp [matchAtoms, matchAtomsWith,
      Bindings.hasLoop_singleton_val_of_not_mem, Metta.Atom.vars]
  have hmerge :
      Bindings.merge [] [BindingRel.val "x#0" (.sym "b")] =
        [[BindingRel.val "x#0" (.sym "b")]] := by
    simp [Bindings.merge, Bindings.mergeOne,
      Bindings.addVarBinding_fresh, Bindings.classValues,
      Bindings.lookupVal, Bindings.addValRaw, Bindings.removeVal]
  have hloop :
      Bindings.hasLoop [BindingRel.val "x#0" (.sym "b")] = false :=
    Bindings.hasLoop_singleton_val_of_not_mem _ _ (by
      simp [Metta.Atom.vars])
  simp [unifyOp, hmatch, hmerge, hloop, collisionIncoming,
    instantiate, Bindings.resolveAtom]
