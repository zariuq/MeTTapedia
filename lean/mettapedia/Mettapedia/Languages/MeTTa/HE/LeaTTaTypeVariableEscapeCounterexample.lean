import Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement
import MettaHyperonFull.Minimal.Interpreter
import MettaHyperonFull.Proofs.BindingLaws
import MettaHyperonFull.Proofs.CaptureAvoidingFreshening
import MettaHyperonFull.Proofs.Substitution
import Std.Data.HashMap.Lemmas

/-!
# Capture-avoiding application-type variables

The pre-repair type service represented private annotation variables by their
source spelling.  Independent annotations could therefore capture one
another during a nested application inference.  The repaired service gives
each consumed type candidate a fresh spelling while preserving unresolved
polymorphism as a variable.

The legacy witnesses remain local to this module so the capability change is
kernel checked.  The final semantic witness also delimits any independent R1
package semantics: package-local satisfiability is too permissive for exact
candidate-set reasoning, because an unresolved variable has models of every
shape while the runtime retains one definite variable presentation.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaTypeVariableEscapeCounterexample

/-- The application-type lookup used before type candidates received private
fresh variable identities.  It is retained only for negative canaries. -/
private def legacyGetTypes (env : Metta.Minimal.MinEnv) :
    Metta.Atom → List Metta.Atom
  | .gnd (.int _) => [.sym "Number"]
  | .gnd (.float _) => [.sym "Number"]
  | .gnd (.str _) => [.sym "String"]
  | .gnd (.bool _) => [.sym "Bool"]
  | .gnd (.external typeName _) => [.sym typeName]
  | .gnd _ => [.sym "Grounded"]
  | .var _ => [.sym "%Undefined%"]
  | .sym name =>
      match env.types.getD name [] with
      | [] => [.sym "%Undefined%"]
      | types => types
  | .expr [.sym "StateValue", value] =>
      [.expr [.sym "StateMonad",
        ((legacyGetTypes env value).head?).getD (.sym "%Undefined%")]]
  | .expr (operator :: arguments) =>
      match env.exprTypes.filter
          (fun pair => pair.1 == .expr (operator :: arguments)) with
      | direct :: directs => (direct :: directs).map (·.2)
      | [] =>
          let argumentTypes := arguments.map fun argument =>
            ((legacyGetTypes env argument).head?).getD (.sym "%Undefined%")
          match (legacyGetTypes env operator).filterMap fun type =>
              match type with
              | .expr (.sym "->" :: types) =>
                  let returnType :=
                    (types.getLast?).getD (.sym "%Undefined%")
                  match Metta.Minimal.matchApplicationTypeArguments []
                      types.dropLast argumentTypes with
                  | some bindings =>
                      some (Metta.instantiate bindings returnType)
                  | none => none
              | _ => none with
          | [] => [.sym "%Undefined%"]
          | results => results
  | .expr [] => [.sym "%Undefined%"]

private def escapeEnv : Metta.Minimal.MinEnv :=
  Metta.Minimal.MinEnv.ofAtomsGT [
    .expr [.sym ":", .sym "k", .expr [.sym "->", .var "t"]],
    .expr [.sym ":", .sym "a", .sym "A"]] []

private def nullaryK : Metta.Atom :=
  .expr [.sym "k"]

private def applyNullaryK : Metta.Atom :=
  .expr [nullaryK, .sym "a"]

/-- A nullary arrow whose return variable is not constrained by an argument
emits that variable, rather than choosing one of its possible valuations. -/
theorem unresolved_return_variable_is_emitted :
    legacyGetTypes escapeEnv nullaryK = [.var "t"] := by
  simp [escapeEnv, nullaryK, legacyGetTypes,
    Metta.Minimal.MinEnv.ofAtomsGT, Std.HashMap.getD_insert,
    Std.HashMap.getD_emptyWithCapacity,
    Metta.Minimal.matchApplicationTypeArguments, Metta.instantiate_nil]

/-- The escaped variable is not treated as an arbitrary function skeleton by
the next application-inference step.  Since its syntax is not an arrow, the
runtime emits the gradual fallback. -/
theorem escaped_variable_is_not_an_arrow_candidate :
    legacyGetTypes escapeEnv applyNullaryK =
      [.sym "%Undefined%"] := by
  simp [escapeEnv, applyNullaryK, nullaryK, legacyGetTypes,
    Metta.Minimal.MinEnv.ofAtomsGT, Std.HashMap.getD_insert,
    Std.HashMap.getD_emptyWithCapacity,
    Metta.Minimal.matchApplicationTypeArguments, Metta.instantiate_nil]

/-- In contrast, package-local existential provenance for an unconstrained
raw variable admits an arrow-shaped valuation.  This is why satisfiability
alone cannot characterize the runtime candidate presentation. -/
theorem empty_theory_variable_has_arrow_valuation :
    ∃ valuation : String → Mettapedia.Languages.MeTTa.OSLFCore.Atom,
      Spec.Type.RuntimeRefinement.RuntimeTypeTheory.empty.Holds valuation ∧
        Spec.Type.RuntimeRefinement.applyTypeValuation valuation (.var "t") =
          .expression [.symbol "->", .symbol "A", .symbol "B"] := by
  refine ⟨fun name => if name = "t" then
      .expression [.symbol "->", .symbol "A", .symbol "B"]
    else .var name, trivial, ?_⟩
  simp [Spec.Type.RuntimeRefinement.applyTypeValuation]

private def collisionEnv : Metta.Minimal.MinEnv :=
  Metta.Minimal.MinEnv.ofAtomsGT [
    .expr [.sym ":", .sym "g",
      .expr [.sym "->", .var "t", .sym "A", .sym "R"]],
    .expr [.sym ":", .sym "b", .sym "B"],
    .expr [.sym ":", .sym "k", .expr [.sym "->", .var "t"]]] []

private def hygienicEnv : Metta.Minimal.MinEnv :=
  Metta.Minimal.MinEnv.ofAtomsGT [
    .expr [.sym ":", .sym "g",
      .expr [.sym "->", .var "t", .sym "A", .sym "R"]],
    .expr [.sym ":", .sym "b", .sym "B"],
    .expr [.sym ":", .sym "k", .expr [.sym "->", .var "u"]]] []

private def capturedApplication : Metta.Atom :=
  .expr [.sym "g", .sym "b", .expr [.sym "k"]]

private def collisionInnerAvoid : List Metta.VarName :=
  Metta.Minimal.typeInferenceAvoid collisionEnv (.expr [.sym "k"])
    [.expr [.sym "->", .var "t"]]

private def collisionInnerT : Metta.VarName :=
  Metta.Minimal.captureAvoidingName collisionInnerAvoid 0 "t"

private def collisionOuterAvoid : List Metta.VarName :=
  Metta.Minimal.typeInferenceAvoid collisionEnv capturedApplication
    [.expr [.sym "->", .var "t", .sym "A", .sym "R"],
      .sym "B", .var collisionInnerT]

private def collisionOuterArgumentT : Metta.VarName :=
  Metta.Minimal.captureAvoidingName collisionOuterAvoid 1 collisionInnerT

private def collisionFunctionAvoid : List Metta.VarName :=
  collisionOuterAvoid ++ [collisionOuterArgumentT]

private def collisionOuterFunctionT : Metta.VarName :=
  Metta.Minimal.captureAvoidingName collisionFunctionAvoid 2 "t"

private theorem first_argument_binds_t :
    Metta.Minimal.matchType [] (.var "t") (.sym "B") =
      some [.val "t" (.sym "B")] := by
  have hloop : Metta.Bindings.hasLoop [.val "t" (.sym "B")] = false :=
    Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _
      (by simp [Metta.Atom.vars])
  have hmatch : Metta.matchAtoms (.var "t") (.sym "B") =
      [[.val "t" (.sym "B")]] := by
    simp [Metta.matchAtoms, Metta.matchAtomsWith, Metta.Subst.occurs,
      hloop]
  have hmerge : Metta.Bindings.merge [] [.val "t" (.sym "B")] =
      [[.val "t" (.sym "B")]] := by
    simp [Metta.Bindings.merge, Metta.Bindings.mergeOne,
      Metta.Bindings.addVarBinding_fresh, Metta.Bindings.classValues,
      Metta.Bindings.lookupVal, Metta.Bindings.addValRaw,
      Metta.Bindings.removeVal]
  simp [Metta.Minimal.matchType, Metta.Minimal.matchReduced,
    Metta.Atom.beq, BEq.beq, hmatch, hmerge, hloop]

private theorem second_argument_collides :
    Metta.Minimal.matchType [.val "t" (.sym "B")]
      (.sym "A") (.var "t") = none := by
  have hloop : Metta.Bindings.hasLoop [.val "t" (.sym "A")] = false :=
    Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _
      (by simp [Metta.Atom.vars])
  have hmatch : Metta.matchAtoms (.sym "A") (.var "t") =
      [[.val "t" (.sym "A")]] := by
    simp [Metta.matchAtoms, Metta.matchAtomsWith, Metta.Subst.occurs,
      hloop]
  have hvalues :
      Metta.Bindings.classValues [.val "t" (.sym "B")] "t" =
        [.sym "B"] := by
    simp
  have hunify :
      Metta.Bindings.unifyValues ([.sym "B"] ++ [.sym "A"]) = none := by
    simp [Metta.Bindings.unifyValues, Metta.Unify.unifyRounds,
      Metta.Unify.decomposeAll, Metta.Unify.decomposeEq, Metta.Atom.size]
  have hadd : Metta.Bindings.addVarBinding [.val "t" (.sym "B")]
      "t" (.sym "A") = [] :=
    Metta.Bindings.addVarBinding_conflict
      (by intro name h; cases h) hvalues (by simp) hunify
  have hmerge : Metta.Bindings.merge [.val "t" (.sym "B")]
      [.val "t" (.sym "A")] = [] := by
    simpa [Metta.Bindings.merge, Metta.Bindings.mergeOne] using hadd
  simp [Metta.Minimal.matchType, Metta.Minimal.matchReduced,
    Metta.Atom.beq, BEq.beq, hmatch, hmerge]

private theorem second_argument_fresh_u :
    Metta.Minimal.matchType [.val "t" (.sym "B")]
      (.sym "A") (.var "u") =
        some [.val "u" (.sym "A"), .val "t" (.sym "B")] := by
  have hcandidateLoop :
      Metta.Bindings.hasLoop [.val "u" (.sym "A")] = false :=
    Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _
      (by simp [Metta.Atom.vars])
  have hmatch : Metta.matchAtoms (.sym "A") (.var "u") =
      [[.val "u" (.sym "A")]] := by
    simp [Metta.matchAtoms, Metta.matchAtomsWith, Metta.Subst.occurs,
      hcandidateLoop]
  have hclass :
      Metta.Bindings.classValues [.val "t" (.sym "B")] "u" = [] := by
    simp [Metta.Bindings.classValues, Metta.Bindings.eqClassOrdered,
      Metta.Bindings.eqVarsInOrder, Metta.Bindings.lookupVal]
  have hadd : Metta.Bindings.addVarBinding [.val "t" (.sym "B")]
      "u" (.sym "A") =
        [[.val "u" (.sym "A"), .val "t" (.sym "B")]] := by
    simpa [Metta.Bindings.addValRaw, Metta.Bindings.removeVal] using
      (Metta.Bindings.addVarBinding_fresh hclass
        (by intro name h; cases h))
  have hmerge : Metta.Bindings.merge [.val "t" (.sym "B")]
      [.val "u" (.sym "A")] =
        [[.val "u" (.sym "A"), .val "t" (.sym "B")]] := by
    simpa [Metta.Bindings.merge, Metta.Bindings.mergeOne] using hadd
  have houtputLoop : Metta.Bindings.hasLoop
      [.val "u" (.sym "A"), .val "t" (.sym "B")] = false := by
    simp (config := { maxSteps := 1000000 })
      [Metta.Bindings.hasLoop, Metta.Bindings.vars,
        Metta.Bindings.resolveAtomAux, Metta.Bindings.resolutionFuel,
        Metta.Bindings.relationResolutionFuel, Metta.Atom.vars,
        Metta.Bindings.classValues, Metta.Bindings.lookupVal,
        Metta.Bindings.eqRepresentative, Metta.Bindings.eqClassOrdered,
        Metta.Bindings.eqVarsInOrder, Metta.Bindings.eqClass,
        Metta.Bindings.eqClassAux, Metta.Bindings.eqStep,
        Metta.Atom.size]
  simp [Metta.Minimal.matchType, Metta.Minimal.matchReduced,
    Metta.Atom.beq, BEq.beq, hmatch, hmerge, houtputLoop]

private theorem empty_variable_matches_B (name : String) :
    Metta.Minimal.matchType [] (.var name) (.sym "B") =
      some [.val name (.sym "B")] := by
  have hloop : Metta.Bindings.hasLoop [.val name (.sym "B")] = false :=
    Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _
      (by simp [Metta.Atom.vars])
  have hmatch : Metta.matchAtoms (.var name) (.sym "B") =
      [[.val name (.sym "B")]] := by
    simp [Metta.matchAtoms, Metta.matchAtomsWith, Metta.Subst.occurs,
      hloop]
  have hmerge : Metta.Bindings.merge [] [.val name (.sym "B")] =
      [[.val name (.sym "B")]] := by
    simp [Metta.Bindings.merge, Metta.Bindings.mergeOne,
      Metta.Bindings.addVarBinding_fresh, Metta.Bindings.classValues,
      Metta.Bindings.lookupVal, Metta.Bindings.addValRaw,
      Metta.Bindings.removeVal]
  simp [Metta.Minimal.matchType, Metta.Minimal.matchReduced,
    Metta.Atom.beq, BEq.beq, hmatch, hmerge, hloop]

private theorem distinct_variable_matches_A
    {first second : String} (hne : first ≠ second)
    : Metta.Minimal.matchType [.val first (.sym "B")]
      (.sym "A") (.var second) =
        some [.val second (.sym "A"), .val first (.sym "B")] := by
  have hne' : second ≠ first := Ne.symm hne
  have hcandidateLoop :
      Metta.Bindings.hasLoop [.val second (.sym "A")] = false :=
    Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _
      (by simp [Metta.Atom.vars])
  have hmatch : Metta.matchAtoms (.sym "A") (.var second) =
      [[.val second (.sym "A")]] := by
    simp [Metta.matchAtoms, Metta.matchAtomsWith, Metta.Subst.occurs,
      hcandidateLoop]
  have hclass : Metta.Bindings.classValues
      [.val first (.sym "B")] second = [] := by
    simp [Metta.Bindings.classValues, Metta.Bindings.eqClassOrdered,
      Metta.Bindings.eqVarsInOrder, Metta.Bindings.lookupVal, hne']
  have hadd : Metta.Bindings.addVarBinding
      [.val first (.sym "B")] second (.sym "A") =
        [[.val second (.sym "A"), .val first (.sym "B")]] := by
    have hnotvar : ∀ name, (Metta.Atom.sym "A") ≠ .var name := by
      intro name
      simp
    have hkeep : first != second := by
      simpa only [bne_iff_ne] using hne
    simpa [Metta.Bindings.addValRaw, Metta.Bindings.removeVal, hkeep] using
      (Metta.Bindings.addVarBinding_fresh hclass hnotvar)
  have hmerge : Metta.Bindings.merge [.val first (.sym "B")]
      [.val second (.sym "A")] =
        [[.val second (.sym "A"), .val first (.sym "B")]] := by
    simpa [Metta.Bindings.merge, Metta.Bindings.mergeOne] using hadd
  have houtputLoop : Metta.Bindings.hasLoop
      [.val second (.sym "A"), .val first (.sym "B")] = false := by
    simp (config := { maxSteps := 1000000 })
      [Metta.Bindings.hasLoop, Metta.Bindings.vars,
        Metta.Bindings.resolveAtomAux, Metta.Bindings.resolutionFuel,
        Metta.Bindings.relationResolutionFuel, Metta.Atom.vars,
        Metta.Bindings.classValues, Metta.Bindings.lookupVal,
        Metta.Bindings.eqRepresentative, Metta.Bindings.eqClassOrdered,
        Metta.Bindings.eqVarsInOrder, Metta.Bindings.eqClass,
        Metta.Bindings.eqClassAux, Metta.Bindings.eqStep,
        Metta.Atom.size, hne]
  simp [Metta.Minimal.matchType, Metta.Minimal.matchReduced,
    Metta.Atom.beq, BEq.beq, hmatch, hmerge, houtputLoop]

/-- Reusing the spelling `t` in two independent annotations makes the escaped
return variable collide with the outer argument fold.  The outer fold has
already constrained `t` to `B`, so checking the second argument against `A`
fails and no result type is inferred. -/
theorem annotation_variable_spelling_collision_rejects :
    legacyGetTypes collisionEnv capturedApplication =
      [.sym "%Undefined%"] := by
  have hfold : Metta.Minimal.matchApplicationTypeArguments []
      [.var "t", .sym "A"] [.sym "B", .var "t"] = none := by
    simp [Metta.Minimal.matchApplicationTypeArguments,
      first_argument_binds_t, second_argument_collides]
  simp [collisionEnv, capturedApplication, legacyGetTypes,
    Metta.Minimal.MinEnv.ofAtomsGT, Std.HashMap.getD_insert,
    Std.HashMap.getD_emptyWithCapacity,
    Metta.Minimal.matchApplicationTypeArguments, Metta.instantiate_nil,
    hfold]

/-- Alpha-renaming only the inner annotation variable to `u` changes the
runtime result: the independent variable can be constrained to `A`, and the
same outer application infers `R`. -/
theorem alpha_renamed_annotation_variable_accepts :
    legacyGetTypes hygienicEnv capturedApplication = [.sym "R"] := by
  have hfold : Metta.Minimal.matchApplicationTypeArguments []
      [.var "t", .sym "A"] [.sym "B", .var "u"] =
        some [.val "u" (.sym "A"), .val "t" (.sym "B")] := by
    simp [Metta.Minimal.matchApplicationTypeArguments,
      first_argument_binds_t, second_argument_fresh_u]
  have hclosed : Metta.instantiate
      [.val "u" (.sym "A"), .val "t" (.sym "B")] (.sym "R") =
        .sym "R" :=
    Metta.instantiate_of_closed _ _ (by simp [Metta.Atom.vars])
  simp [hygienicEnv, capturedApplication, legacyGetTypes,
    Metta.Minimal.MinEnv.ofAtomsGT, Std.HashMap.getD_insert,
    Std.HashMap.getD_emptyWithCapacity,
    Metta.Minimal.matchApplicationTypeArguments, Metta.instantiate_nil,
    hfold, hclosed]

private def escapeAvoid : List Metta.VarName :=
  Metta.Minimal.typeInferenceAvoid escapeEnv nullaryK
    [.expr [.sym "->", .var "t"]]

private def escapeFreshT : Metta.VarName :=
  Metta.Minimal.captureAvoidingName escapeAvoid 0 "t"

/-- The repaired lookup preserves unresolved polymorphism as a variable but
gives the variable a private spelling for this inference occurrence. -/
theorem repaired_unresolved_return_variable_is_fresh :
    Metta.Minimal.getTypes escapeEnv nullaryK = [.var escapeFreshT] := by
  simp [escapeEnv, nullaryK, escapeFreshT, escapeAvoid,
    Metta.Minimal.getTypes, Metta.Minimal.MinEnv.ofAtomsGT,
    Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity,
    Metta.Minimal.typeInferenceAvoid, Metta.Minimal.freshenArgumentTypes,
    Metta.Minimal.freshenTypeCandidate, Metta.Minimal.renameAllVars,
    Metta.Minimal.matchApplicationTypeArguments, Metta.instantiate_nil]

/-- The new unresolved variable cannot reuse the source annotation spelling. -/
theorem repaired_unresolved_return_variable_avoids_annotation :
    escapeFreshT ≠ "t" := by
  intro heq
  have hfresh := Metta.Minimal.captureAvoidingName_not_mem
    escapeAvoid 0 "t"
  apply hfresh
  have heq' : Metta.Minimal.captureAvoidingName escapeAvoid 0 "t" = "t" := by
    simpa [escapeFreshT] using heq
  rw [heq']
  simp [escapeAvoid, Metta.Minimal.typeInferenceAvoid, escapeEnv, nullaryK,
    Metta.Minimal.MinEnv.ofAtomsGT, Metta.Atom.vars]

/-- The exact legacy spelling collision is accepted after each annotation
candidate receives an independent private variable identity. -/
theorem repaired_annotation_variable_spelling_collision_accepts :
    Metta.Minimal.getTypes collisionEnv capturedApplication = [.sym "R"] := by
  have hinner : Metta.Minimal.getTypes collisionEnv (.expr [.sym "k"]) =
      [.var collisionInnerT] := by
    simp [collisionEnv, collisionInnerT, collisionInnerAvoid,
      Metta.Minimal.getTypes, Metta.Minimal.MinEnv.ofAtomsGT,
      Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity,
      Metta.Minimal.typeInferenceAvoid, Metta.Minimal.freshenArgumentTypes,
      Metta.Minimal.freshenTypeCandidate, Metta.Minimal.renameAllVars,
      Metta.Minimal.matchApplicationTypeArguments, Metta.instantiate_nil]
  have hdistinct : collisionOuterFunctionT ≠ collisionOuterArgumentT := by
    intro heq
    have hfresh := Metta.Minimal.captureAvoidingName_not_mem
      collisionFunctionAvoid 2 "t"
    apply hfresh
    have heq' : Metta.Minimal.captureAvoidingName
        collisionFunctionAvoid 2 "t" = collisionOuterArgumentT := by
      simpa [collisionOuterFunctionT] using heq
    rw [heq']
    simp [collisionFunctionAvoid]
  have hfold : Metta.Minimal.matchApplicationTypeArguments []
      [.var collisionOuterFunctionT, .sym "A"]
      [.sym "B", .var collisionOuterArgumentT] =
        some [.val collisionOuterArgumentT (.sym "A"),
          .val collisionOuterFunctionT (.sym "B")] := by
    simp [Metta.Minimal.matchApplicationTypeArguments,
      empty_variable_matches_B,
      distinct_variable_matches_A hdistinct]
  have hg : Metta.Minimal.getTypes collisionEnv (.sym "g") =
      [.expr [.sym "->", .var "t", .sym "A", .sym "R"]] := by
    simp [collisionEnv, Metta.Minimal.getTypes,
      Metta.Minimal.MinEnv.ofAtomsGT, Std.HashMap.getD_insert,
      Std.HashMap.getD_emptyWithCapacity]
  have hb : Metta.Minimal.getTypes collisionEnv (.sym "b") = [.sym "B"] := by
    simp [collisionEnv, Metta.Minimal.getTypes,
      Metta.Minimal.MinEnv.ofAtomsGT, Std.HashMap.getD_insert,
      Std.HashMap.getD_emptyWithCapacity]
  have houterAvoid : Metta.Minimal.typeInferenceAvoid collisionEnv
      (.expr [.sym "g", .sym "b", .expr [.sym "k"]])
      [.expr [.sym "->", .var "t", .sym "A", .sym "R"],
        .sym "B", .var collisionInnerT] = collisionOuterAvoid := rfl
  have harguments : Metta.Minimal.freshenArgumentTypes
      collisionOuterAvoid 0 [.sym "B", .var collisionInnerT] =
        [.sym "B", .var collisionOuterArgumentT] := by
    simp [Metta.Minimal.freshenArgumentTypes,
      Metta.Minimal.freshenTypeCandidate, Metta.Minimal.renameAllVars,
      Metta.Atom.vars, collisionOuterArgumentT]
  have hfunctionAvoid : collisionOuterAvoid ++
      [.sym "B", .var collisionOuterArgumentT].flatMap Metta.Atom.vars =
        collisionFunctionAvoid := by
    simp [collisionFunctionAvoid, Metta.Atom.vars]
  have hfunction : Metta.Minimal.freshenTypeCandidate
      collisionFunctionAvoid 2
      (.expr [.sym "->", .var "t", .sym "A", .sym "R"]) =
        .expr [.sym "->", .var collisionOuterFunctionT,
          .sym "A", .sym "R"] := by
    simp [Metta.Minimal.freshenTypeCandidate,
      Metta.Minimal.renameAllVars, collisionOuterFunctionT]
  have hdirect : collisionEnv.exprTypes.filter
      (fun pair => pair.1 == Metta.Atom.expr
        [.sym "g", .sym "b", .expr [.sym "k"]]) = [] := by
    simp [collisionEnv, Metta.Minimal.MinEnv.ofAtomsGT]
  have hnotState : ∀ value,
      Metta.Atom.sym "g" = Metta.Atom.sym "StateValue" →
        [Metta.Atom.sym "b", Metta.Atom.expr [Metta.Atom.sym "k"]] =
          [value] → False := by
    intro value hhead
    simp at hhead
  change Metta.Minimal.getTypes collisionEnv
      (.expr [.sym "g", .sym "b", .expr [.sym "k"]]) = [.sym "R"]
  rw [Metta.Minimal.getTypes.eq_10 collisionEnv (.sym "g")
    [.sym "b", .expr [.sym "k"]] hnotState]
  rw [hdirect]
  dsimp only
  simp only [hg]
  simp only [List.map]
  rw [hb, hinner]
  simp only [List.head?_cons, Option.getD_some, List.cons_append,
    List.nil_append, List.length_cons, List.length_nil, Nat.reduceAdd]
  simp only [houterAvoid, harguments, hfunctionAvoid, hfunction]
  rw [List.filterMap_cons]
  simp only [List.dropLast_cons_cons, List.dropLast_singleton,
    List.getLast?_cons, List.getLast?_nil, Option.getD_some,
    List.filterMap_nil]
  rw [hfold]
  simp [Metta.instantiate_of_closed, Metta.Atom.vars]

end Mettapedia.Languages.MeTTa.HE.LeaTTaTypeVariableEscapeCounterexample
