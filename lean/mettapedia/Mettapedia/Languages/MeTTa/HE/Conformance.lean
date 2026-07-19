import Mettapedia.Languages.MeTTa.HE.MinimalMeTTa
import Mettapedia.Languages.MeTTa.HE.Eval
import Mettapedia.Languages.MeTTa.HE.Certification
import Mettapedia.Languages.MeTTa.HE.CoreFragment
import Mettapedia.Languages.MeTTa.HE.DeclMatchSpec
import Mettapedia.Languages.MeTTa.HE.HumanMatchMergeSpec
import Mettapedia.Languages.MeTTa.HE.HumanMatchSolutionTheory
import Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
import Mettapedia.Languages.MeTTa.HE.LeaTTaBindingTransport
import Mettapedia.Languages.MeTTa.HE.MatchSolutionTheory
import Mettapedia.Languages.MeTTa.HE.LeaTTaMatcherCongruence
import Mettapedia.Languages.MeTTa.HE.LeaTTaMergeExistence
import Mettapedia.Languages.MeTTa.HE.LeaTTaHumanConformance
import Mettapedia.Languages.MeTTa.HE.HumanMatchLPBridge
import Mettapedia.Languages.MeTTa.HE.HumanMatchStructuralModel
import Mettapedia.Languages.MeTTa.HE.HumanMatchCompleteness
import Mettapedia.Languages.MeTTa.HE.LeaTTaHumanSoundness
import Mettapedia.Languages.MeTTa.HE.LeaTTaQueryObservationalAnchor
import Mettapedia.Languages.MeTTa.HE.LeaTTaHumanSeal
import Mettapedia.Languages.MeTTa.HE.LeaTTaConcreteConformance
import Mettapedia.Languages.MeTTa.HE.MatcherMergeCompleteness
import Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp
import Mettapedia.OSLF.MeTTaIL.Match
import MettaHyperonFull.Proofs.BindingLaws

/-!
# HE MeTTa Conformance

Conformance verification for the HE MeTTa evaluation specification.

## Two kinds of conformance:
1. **Leaf function tests** (sections 2-4): `rfl`-checked against computable
   functions in Matching.lean / TypeCheck.lean. These are exact equality tests.
2. **Derivation witnesses** (sections 1, 5-7): Explicit derivation trees
   witnessing that `EvalAtom`/`MettaCall`/etc. hold for specific inputs.
   These prove that the declarative spec allows the expected derivations.

## Source of Truth
- `https://trueagi-io.github.io/hyperon-experimental/metta/`
- Conformance with `metta` CLI (conda hyperon environment, v0.2.10)
-/

namespace Mettapedia.Languages.MeTTa.HE.Conformance

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.RuntimeCorrectness
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge

/-! ## Test Infrastructure -/

private def emptySpace : Space := Space.empty
private def emptyB : Bindings := Bindings.empty
private def noDispatch : GroundedDispatch := .none
private def fuel : Nat := 50

/-! ## 1. EvalAtom derivation witnesses (spec lines 105-136)

These construct explicit derivation trees showing that specific inputs
have valid derivations in the declarative spec. -/

/-- Empty atom passes through unchanged.
    Spec line 117: `if $atom == Empty ... return [($atom, $bindings)]` -/
theorem eval_empty_passthrough :
    EvalAtom emptySpace noDispatch Atom.empty Atom.undefinedType emptyB
      (Atom.empty, emptyB) :=
  .empty_or_error _ _ _ rfl

/-- Error atom passes through unchanged.
    Spec line 117: `$atom ~ (Error ...)` -/
theorem eval_error_passthrough :
    EvalAtom emptySpace noDispatch
      (Atom.error (.symbol "x") (.symbol "msg")) Atom.undefinedType emptyB
      (Atom.error (.symbol "x") (.symbol "msg"), emptyB) :=
  .empty_or_error _ _ _ rfl

/-- Variable always passes through (metatype is Variable).
    Spec line 119: `$metatype == Variable` -/
theorem eval_variable_passthrough :
    EvalAtom emptySpace noDispatch (.var "x") Atom.undefinedType emptyB
      (.var "x", emptyB) :=
  .type_pass _ _ _ rfl (Or.inr (Or.inr rfl))

/-- When expected type is Atom, return unchanged.
    Spec line 119: `$type == Atom` -/
theorem eval_type_atom :
    EvalAtom emptySpace noDispatch (.symbol "x") Atom.atomType emptyB
      (.symbol "x", emptyB) :=
  .type_pass _ _ _ rfl (Or.inl rfl)

/-- When expected type matches metatype, return unchanged.
    Spec line 119: `$type == $metatype` -/
theorem eval_type_matches_metatype :
    EvalAtom emptySpace noDispatch (.symbol "x") (.symbol "Symbol") emptyB
      (.symbol "x", emptyB) :=
  .type_pass _ _ _ rfl (Or.inr (Or.inl rfl))

/-- Symbol with no type info → typeCast → %Undefined% matches anything.
    Spec line 123: `$metatype == Symbol` → `type_cast` -/
theorem eval_symbol_typecast :
    EvalAtom emptySpace noDispatch (.symbol "x") (.symbol "Foo") emptyB
      (.symbol "x", emptyB) := by
  apply EvalAtom.type_cast (fuel := fuel)
  · rfl
  · decide
  · left; rfl
  · show _ ∈ typeCast _ _ _ _ fuel
    decide

/-- Unit expression → typeCast.
    Spec line 123: `$atom == ()` -/
theorem eval_unit_typecast :
    EvalAtom emptySpace noDispatch Atom.unit Atom.undefinedType emptyB
      (Atom.unit, emptyB) := by
  apply EvalAtom.type_cast (fuel := fuel)
  · rfl
  · decide
  · right; right; rfl
  · show _ ∈ typeCast _ _ _ _ fuel
    decide

/-- Grounded atom → typeCast with matching type.
    Spec line 123: `$metatype == Grounded`.
    Grounded int has intrinsic type `Number` (from `Grounded::type_()`). -/
theorem eval_grounded_typecast :
    EvalAtom emptySpace noDispatch (.grounded (.int 42)) (.symbol "Number") emptyB
      (.grounded (.int 42), emptyB) := by
  apply EvalAtom.type_cast (fuel := fuel)
  · rfl
  · decide
  · right; left; rfl
  · show _ ∈ typeCast _ _ _ _ fuel
    decide

/-! ## 2. typeCast clauses (metta.md lines 275-296) — computable `rfl` tests -/

/-- Atom with matching type annotation. -/
theorem typeCast_matching_type :
    let space := Space.ofList [.expression [.symbol ":", .symbol "x", .symbol "Int"]]
    typeCast (.symbol "x") (.symbol "Int") space emptyB fuel =
    [(.symbol "x", emptyB)] := rfl

/-- Atom with non-matching type: error. -/
theorem typeCast_mismatch :
    let space := Space.ofList [.expression [.symbol ":", .symbol "x", .symbol "Int"]]
    typeCast (.symbol "x") (.symbol "Bool") space emptyB fuel =
    [(mkError (.symbol "x") (.badType (.symbol "Bool") (.symbol "Int")), emptyB)] := rfl

/-- Atom with no type annotation: gets %Undefined%, which matches anything. -/
theorem typeCast_no_annotation :
    typeCast (.symbol "x") (.symbol "Foo") emptySpace emptyB fuel =
    [(.symbol "x", emptyB)] := rfl

/-- %Undefined% always matches as expected type. -/
theorem typeCast_undefined_type :
    let space := Space.ofList [.expression [.symbol ":", .symbol "x", .symbol "Int"]]
    typeCast (.symbol "x") Atom.undefinedType space emptyB fuel =
    [(.symbol "x", emptyB)] := rfl

/-! ## 3. matchTypes clauses (metta.md lines 298-314) -/

theorem matchTypes_undef_left :
    matchTypes Atom.undefinedType (.symbol "Anything") emptyB =
    [emptyB] := rfl

theorem matchTypes_atom_right :
    matchTypes (.symbol "Anything") Atom.atomType emptyB =
    [emptyB] := rfl

theorem matchTypes_same :
    matchTypes (.symbol "Int") (.symbol "Int") emptyB = [emptyB] := rfl

theorem matchTypes_different :
    matchTypes (.symbol "Int") (.symbol "Bool") emptyB = [] := rfl

/-! ## 4. matchAtoms clauses (metta.md lines 577-617) -/

theorem matchAtoms_same_symbol :
    matchAtoms (.symbol "a") (.symbol "a") fuel = [emptyB] := rfl

theorem matchAtoms_diff_symbol :
    matchAtoms (.symbol "a") (.symbol "b") fuel = [] := rfl

theorem matchAtoms_two_vars :
    matchAtoms (.var "x") (.var "y") fuel =
    [emptyB.addEquality "x" "y"] := rfl

/-- HE var/var matching is first-class equality, not an oriented assignment. -/
theorem matchAtoms_two_vars_not_oriented_assignment :
    matchAtoms (.var "x") (.var "y") fuel ≠
    [emptyB.assign "x" (.var "y")] := by
  decide

/-- OSLF's native matcher has the assignment shape that is correct for
MeTTaIL rewriting but too weak to replace HE's equality-bearing bindings. -/
theorem oslf_matchPattern_fvar_fvar_assignment_shape :
    Mettapedia.OSLF.MeTTaIL.Match.matchPattern
      (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar "x")
      (Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar "y") =
    [[("x", Mettapedia.OSLF.MeTTaIL.Syntax.Pattern.fvar "y")]] := by
  simp [Mettapedia.OSLF.MeTTaIL.Match.matchPattern]

/-- Conformance-facing audit hook for the retired one-sided query path:
`DeclMatchSpec` owns the semantic counterexample, and the conformance suite
exposes it so the old `simpleMatch` query surface cannot be mistaken for the
faithful HE matcher again. -/
theorem retiredSimpleMatch_query_path_fails_HE_faithfulness :
    ¬ DeclMatchSpec.RetiredSimpleMatchQueryPathFaithfulOn
        (.var "y") (.var "x") (.symbol "rhs") 10 :=
  DeclMatchSpec.retiredSimpleMatch_varVar_query_path_fails_faithfulness

/-- Public query-path faithfulness hook: every active `queryEquations` hit is
backed by the dedicated HE declarative match relation on the freshened equation
left-hand side.  This is the positive counterpart to
`retiredSimpleMatch_query_path_fails_HE_faithfulness`. -/
theorem queryEquations_hits_are_declarative_matches
    {space : Space} {atom : Atom} {fuel : Nat} {rhs : Atom} {qb : Bindings}
    (h : (rhs, qb) ∈ queryEquations space atom fuel) :
    ∃ lhs rhs0 idx,
      (.expression [.symbol "=", lhs, rhs0], idx) ∈ space.atoms.zipIdx ∧
      rhs = (freshenEquation idx lhs rhs0 fuel).2 ∧
      DeclMatchSpec.MatchRel atom (freshenEquation idx lhs rhs0 fuel).1 qb := by
  rcases queryEquations_matchAtoms_witness h with
    ⟨lhs, rhs0, idx, hmem, hrhs, hmatch⟩
  exact
    ⟨lhs, rhs0, idx, hmem, hrhs, DeclMatchSpec.matchAtoms_sound hmatch⟩

/-- Visible-avoid query faithfulness hook: the repaired query surface used by
the LeaTTa visible-observation bridge is also backed by the dedicated HE
declarative match relation. -/
theorem queryEquationsAgainstVisible_hits_are_declarative_matches
    {space : Space} {atom : Atom} {fuel : Nat} {rhs : Atom} {qb : Bindings}
    (h : (rhs, qb) ∈ queryEquationsAgainstVisible space atom fuel) :
    ∃ lhs rhs0 idx,
      (.expression [.symbol "=", lhs, rhs0], idx) ∈ space.atoms.zipIdx ∧
      rhs =
        (freshenEquationAgainst (collectVars atom fuel).eraseDups idx lhs rhs0 fuel).2 ∧
      DeclMatchSpec.MatchRel atom
        (freshenEquationAgainst (collectVars atom fuel).eraseDups idx lhs rhs0 fuel).1 qb := by
  rcases queryEquationsAgainstVisible_matchAtoms_witness h with
    ⟨lhs, rhs0, idx, hmem, hrhs, hmatch⟩
  exact
    ⟨lhs, rhs0, idx, hmem, hrhs, DeclMatchSpec.matchAtoms_sound hmatch⟩

theorem matchAtoms_var_left :
    matchAtoms (.var "x") (.symbol "a") fuel =
    [emptyB.assign "x" (.symbol "a")] := rfl

theorem matchAtoms_var_right :
    matchAtoms (.symbol "a") (.var "x") fuel =
    [emptyB.assign "x" (.symbol "a")] := rfl

theorem matchAtoms_expr_match :
    matchAtoms (.expression [.symbol "a", .var "x"])
               (.expression [.symbol "a", .symbol "b"]) fuel =
    [emptyB.assign "x" (.symbol "b")] := rfl

theorem matchAtoms_expr_length_mismatch :
    matchAtoms (.expression [.symbol "a"])
               (.expression [.symbol "a", .symbol "b"]) fuel = [] := rfl

theorem matchAtoms_grounded_same :
    matchAtoms (.grounded (.int 42)) (.grounded (.int 42)) fuel = [emptyB] := rfl

theorem matchAtoms_grounded_diff :
    matchAtoms (.grounded (.int 42)) (.grounded (.int 43)) fuel = [] := rfl

theorem matchAtoms_sym_expr :
    matchAtoms (.symbol "a") (.expression [.symbol "a"]) fuel = [] := rfl

/-! ## 5. MettaCall derivation witnesses (spec lines 348-389) -/

/-- Error atom passes through mettaCall.
    Spec line 359: `if $atom ~ (Error ...)` -/
theorem mettaCall_error_passthrough :
    MettaCall emptySpace noDispatch
      (Atom.error (.symbol "x") (.symbol "e")) Atom.undefinedType emptyB
      (Atom.error (.symbol "x") (.symbol "e"), emptyB) :=
  .error_passthrough _ _ _ rfl

private def leattaErrorPassthroughAtom : Metta.Atom :=
  Metta.Atom.expr
    [Metta.Atom.sym "Error", Metta.Atom.sym "x", Metta.Atom.sym "e"]

theorem leatta_error_passthrough_atom_is_HE_error_translation :
    LeaTTaBridge.toLeaTTaAtom (Atom.error (.symbol "x") (.symbol "e")) =
      leattaErrorPassthroughAtom := rfl

private theorem empty_minimal_symbol_candidates (s : String) :
    Metta.Minimal.candidatesW (Metta.Minimal.MinEnv.ofAtomsGT [] [])
      Metta.Minimal.St.init.world (Metta.Atom.sym s) = [] := by
  simp [Metta.Minimal.candidatesW, Metta.Minimal.MinEnv.candidates,
    Metta.Minimal.MinEnv.ofAtomsGT, Metta.Minimal.extractRules,
    Metta.Minimal.headKey, Metta.Minimal.St.init, Metta.Minimal.World.empty]

private theorem empty_minimal_error_passthrough_candidates :
    Metta.Minimal.candidatesW (Metta.Minimal.MinEnv.ofAtomsGT [] [])
      Metta.Minimal.St.init.world leattaErrorPassthroughAtom = [] := by
  simp [leattaErrorPassthroughAtom, Metta.Minimal.candidatesW,
    Metta.Minimal.MinEnv.candidates, Metta.Minimal.MinEnv.ofAtomsGT,
    Metta.Minimal.extractRules, Metta.Minimal.headKey,
    Metta.Minimal.St.init, Metta.Minimal.World.empty]

theorem leatta_minimal_error_passthrough_mettaEval :
    Metta.Minimal.mettaEval (Metta.Minimal.MinEnv.ofAtomsGT [] []) 4
      Metta.Minimal.St.init [] leattaErrorPassthroughAtom =
    ([(leattaErrorPassthroughAtom, [])], Metta.Minimal.St.init) := by
  let env : Metta.Minimal.MinEnv := Metta.Minimal.MinEnv.ofAtomsGT [] []
  have hx :
      Metta.Minimal.mettaEval env 3 Metta.Minimal.St.init []
        (Metta.Atom.sym "x") =
      ([(Metta.Atom.sym "x", [])], Metta.Minimal.St.init) := by
    exact mettaEval_symbol_eq_of_notReducible_eq
      env 2 Metta.Minimal.St.init [] "x"
      (by
        simpa [env, atomToStack_eval] using
          (interpretFuel_eval_symbol_notReducible_of_no_candidates_eq
            env Metta.Minimal.St.init 2 (Metta.Atom.sym "x") [] "x"
            (by simp [Metta.instantiate]) rfl
            (by simpa [env] using empty_minimal_symbol_candidates "x")))
  have he :
      Metta.Minimal.mettaEval env 3 Metta.Minimal.St.init []
        (Metta.Atom.sym "e") =
      ([(Metta.Atom.sym "e", [])], Metta.Minimal.St.init) := by
    exact mettaEval_symbol_eq_of_notReducible_eq
      env 2 Metta.Minimal.St.init [] "e"
      (by
        simpa [env, atomToStack_eval] using
          (interpretFuel_eval_symbol_notReducible_of_no_candidates_eq
            env Metta.Minimal.St.init 2 (Metta.Atom.sym "e") [] "e"
            (by simp [Metta.instantiate]) rfl
            (by simpa [env] using empty_minimal_symbol_candidates "e")))
  have hRoot :
      Metta.Minimal.interpretFuel env 4 Metta.Minimal.St.init
        [evalItemNil leattaErrorPassthroughAtom] [] =
      ([(Metta.Minimal.notReducibleA, [])], Metta.Minimal.St.init) := by
    simpa [env, leattaErrorPassthroughAtom, evalItemNil, atomToStack_eval] using
      (interpretFuel_eval_notReducible_of_no_candidates_eq
        env Metta.Minimal.St.init 3 leattaErrorPassthroughAtom [] "Error"
        [Metta.Atom.sym "x", Metta.Atom.sym "e"]
        (by simp [leattaErrorPassthroughAtom, Metta.instantiate])
        rfl rfl rfl
        (by
          simpa [env, leattaErrorPassthroughAtom] using
            empty_minimal_error_passthrough_candidates))
  simpa [env, leattaErrorPassthroughAtom] using
    (mettaEval_binary_expr_eq_of_tuple_fallback_and_root_notReducible
      env 3 Metta.Minimal.St.init Metta.Minimal.St.init Metta.Minimal.St.init
      Metta.Minimal.St.init "Error" (Metta.Atom.sym "x") (Metta.Atom.sym "e")
      (Metta.Atom.sym "x") (Metta.Atom.sym "e") ([] : Metta.Bindings)
      (by simp [Metta.Atom.vars]) (by simp [Metta.Atom.vars]) hx he
      (by
        have hprep : Metta.Minimal.typePrep Metta.Minimal.St.init.world
            (.sym "Error") = .sym "Error" := by
          simp [Metta.Minimal.typePrep, Metta.Minimal.subTokens.eq_1,
            Metta.Minimal.wrapStates.eq_3, Metta.Minimal.St.init,
            Metta.Minimal.World.empty]
        have htypes : Metta.Minimal.getTypes env (.sym "Error") =
            [.sym "%Undefined%"] := by
          rw [Metta.Minimal.getTypes.eq_8]
          simp [env, Metta.Minimal.MinEnv.ofAtomsGT,
            Std.HashMap.getD_emptyWithCapacity]
        rw [Metta.Minimal.selectFunctionType, hprep, htypes]
        rfl)
      rfl hRoot)

theorem leatta_minimal_error_passthrough_matches_HE_mettaCall_surface :
    LeaTTaBridge.toLeaTTaAtom (Atom.error (.symbol "x") (.symbol "e")) =
        leattaErrorPassthroughAtom ∧
      Metta.Minimal.mettaEval (Metta.Minimal.MinEnv.ofAtomsGT [] []) 4
        Metta.Minimal.St.init [] leattaErrorPassthroughAtom =
        ([(leattaErrorPassthroughAtom, [])], Metta.Minimal.St.init) ∧
      MettaCall emptySpace noDispatch
        (Atom.error (.symbol "x") (.symbol "e")) Atom.undefinedType emptyB
        (Atom.error (.symbol "x") (.symbol "e"), emptyB) := by
  exact ⟨leatta_error_passthrough_atom_is_HE_error_translation,
    leatta_minimal_error_passthrough_mettaEval, mettaCall_error_passthrough⟩

/-- Equation match: `(= (f a) result)` in space, calling `(f a)`.
    Spec lines 376-382: query equations, merge bindings, recurse.
    Note: RHS is ground (`.symbol "result"`), so `merged.applyFull rhs fuel = rhs`. -/
theorem mettaCall_equation_match :
    let space := Space.ofList [
      .expression [.symbol "=", .expression [.symbol "f", .symbol "a"], .symbol "result"]]
    MettaCall space noDispatch
      (.expression [.symbol "f", .symbol "a"]) Atom.undefinedType emptyB
      (.symbol "result", emptyB) := by
  apply MettaCall.equation_match (fuel := fuel) (rhs := .symbol "result")
    (queryBindings := emptyB) (merged := emptyB)
  case h_not_error => rfl
  case h_not_grounded => trivial
  case h_query => decide
  case h_merge => decide
  case h_no_loop => rfl
  case h_recurse =>
    -- merged.apply (.symbol "result") fuel = .symbol "result" (ground, no vars)
    apply EvalAtom.type_cast (fuel := fuel)
    · rfl
    · decide
    · left; rfl
    · show _ ∈ typeCast _ _ _ _ fuel; decide

/-- No equations match → return atom unchanged.
    Spec lines 383-384. -/
theorem mettaCall_no_match :
    MettaCall emptySpace noDispatch
      (.expression [.symbol "f", .symbol "a"]) Atom.undefinedType emptyB
      (.expression [.symbol "f", .symbol "a"], emptyB) := by
  apply MettaCall.no_match (fuel := fuel)
  case h_not_error => rfl
  case h_not_grounded => trivial
  case h_no_eqs => rfl

/-- Equation match with symbol RHS: `(= (g b) answer)`.
    `(g b)` → equation match → `answer` (symbol, type_cast succeeds). -/
theorem mettaCall_symbol_rhs :
    let space := Space.ofList [
      .expression [.symbol "=",
        .expression [.symbol "g", .symbol "b"],
        .symbol "answer"]]
    MettaCall space noDispatch
      (.expression [.symbol "g", .symbol "b"]) Atom.undefinedType emptyB
      (.symbol "answer", emptyB) := by
  apply MettaCall.equation_match (fuel := fuel)
    (rhs := .symbol "answer")
    (queryBindings := emptyB) (merged := emptyB)
  case h_not_error => rfl
  case h_not_grounded => trivial
  case h_query => decide
  case h_merge => decide
  case h_no_loop => rfl
  case h_recurse =>
    apply EvalAtom.type_cast (fuel := fuel)
    · rfl
    · decide
    · left; rfl
    · show _ ∈ typeCast _ _ _ _ fuel; decide

/-! ## 6. Equation RHS Substitution Regression (Bug 1 fix)

The equation `(= (id $x) $x)` with input `(id hello)` must produce `hello`,
not the raw freshened variable `$x#0`. This is the key regression test for
the `merged.applyFull rhs fuel` fix in `MettaCall.equation_match`. -/

/-- Verify queryEquations returns freshened variable as RHS. -/
theorem queryEquations_id_pattern :
    let space := Space.ofList [
      .expression [.symbol "=", .expression [.symbol "id", .var "x"], .var "x"]]
    queryEquations space (.expression [.symbol "id", .symbol "hello"]) =
    [(.var "x#0", emptyB.assign "x#0" (.symbol "hello"))] := rfl

/-- Equation `(= (id $x) $x)` with input `(id hello)` produces `hello`.
    After merging, `merged = { x#0 → hello }`, so `merged.apply (.var "x#0") fuel = hello`.
    This would FAIL without the `merged.applyFull rhs fuel` fix. -/
theorem mettaCall_equation_rhs_substitution :
    let space := Space.ofList [
      .expression [.symbol "=", .expression [.symbol "id", .var "x"], .var "x"]]
    MettaCall space noDispatch
      (.expression [.symbol "id", .symbol "hello"]) Atom.undefinedType emptyB
      (.symbol "hello", emptyB.assign "x#0" (.symbol "hello")) := by
  apply MettaCall.equation_match (fuel := fuel)
    (rhs := .var "x#0")
    (queryBindings := emptyB.assign "x#0" (.symbol "hello"))
    (merged := emptyB.assign "x#0" (.symbol "hello"))
  case h_not_error => rfl
  case h_not_grounded => trivial
  case h_query => decide
  case h_merge => decide
  case h_no_loop => rfl
  case h_recurse =>
    -- merged.apply (.var "x#0") fuel = .symbol "hello" by kernel reduction
    change EvalAtom _ _ (.symbol "hello") _ _ _
    apply EvalAtom.type_cast (fuel := fuel)
    · rfl
    · decide
    · left; rfl
    · show _ ∈ typeCast _ _ _ _ fuel; decide

/-! ## 6b. Equation RHS Fuel Drift Regression

The coarse declarative `MettaCall.equation_match` constructor can recurse on a
low-fuel `merged.applyFull rhs fuel` result that has not stabilized yet. This is
exactly why the aligned completeness bridge in `Correctness.lean` uses the
stronger `ApplyStableEventually` witness instead of naively mirroring the
public constructor one-for-one.
-/

private def unstableChainB : Bindings :=
  (emptyB.assign "z#0" (.var "y")).assign "y" (.symbol "a")

private def unstableChainSpace : Space := Space.ofList [
  .expression [.symbol "=", .symbol "q", .var "z"]]

/-- Low fuel can leave the equation RHS only partially substituted. -/
theorem equation_rhs_apply_fuel2_unstable :
    unstableChainB.apply (.var "z#0") 2 = .var "z#0" := rfl

/-- Larger fuel resolves the same RHS all the way to the final symbol. -/
theorem equation_rhs_apply_fuel4_stabilized :
    unstableChainB.apply (.var "z#0") 4 = .symbol "a" := rfl

/-- The coarse public spec admits an equation-match derivation through the
    unstable low-fuel RHS. This is a real derivation, not a hypothetical one. -/
theorem mettaCall_equation_rhs_unstable_low_fuel :
    MettaCall unstableChainSpace noDispatch
      (.symbol "q") Atom.undefinedType unstableChainB
      (.var "z#0", unstableChainB) := by
  apply MettaCall.equation_match (fuel := 2)
    (rhs := .var "z#0") (queryBindings := emptyB) (merged := unstableChainB)
  case h_not_error => rfl
  case h_not_grounded => trivial
  case h_query => decide
  case h_merge => decide
  case h_no_loop => rfl
  case h_recurse =>
    change EvalAtom _ _ (.var "z#0") _ _ _
    apply EvalAtom.type_pass
    · rfl
    · exact Or.inr (Or.inr rfl)

private def unstableTopAtom : Atom := .expression [.symbol "q"]

/-- The unstable low-fuel equation-match witness bubbles up to a genuine
    top-level `evalAtom` result. -/
theorem evalAtom_unstable_top_level_low_fuel_reaches :
    (.var "z#0", unstableChainB) ∈
      evalAtom unstableChainSpace noDispatch
        unstableTopAtom Atom.undefinedType unstableChainB 5 := by
  decide

/-- From fuel 6 onward, the executable evaluator has stabilized to the final
    fully-substituted result, so the low-fuel top-level witness disappears. -/
theorem evalAtom_unstable_top_level_stabilized_from_fuel6 (n : Nat) :
    evalAtom unstableChainSpace noDispatch
      unstableTopAtom Atom.undefinedType unstableChainB (n + 6) =
      [(.symbol "a", unstableChainB)] := by
  rfl

/-- The coarse public `EvalAtom` spec admits the unstable low-fuel top-level
    result. This is exactly the kind of derivation that should NOT be forced
    into the exported certification boundary. -/
theorem evalAtom_unstable_top_level_derivation :
    EvalAtom unstableChainSpace noDispatch
      unstableTopAtom Atom.undefinedType unstableChainB
      (.var "z#0", unstableChainB) := by
  exact evalAtom_sound unstableChainSpace noDispatch
    unstableTopAtom Atom.undefinedType unstableChainB 5
    (.var "z#0", unstableChainB)
    evalAtom_unstable_top_level_low_fuel_reaches

/-- The unstable low-fuel top-level derivation is NOT certified: certification
    requires stable eventual reachability, but from fuel 6 onward the evaluator
    only returns the stabilized symbol result. -/
theorem evalAtom_unstable_top_level_not_certified :
    ¬ EvalAtomCertified unstableChainSpace noDispatch
      unstableTopAtom Atom.undefinedType unstableChainB
      (.var "z#0", unstableChainB) := by
  intro h_cert
  rcases (evalAtomCertified_iff_stably_reaches
      unstableChainSpace noDispatch
      unstableTopAtom Atom.undefinedType unstableChainB
      (.var "z#0", unstableChainB)).mp h_cert with ⟨fuel0, h_eventual⟩
  have h_mem :
      (.var "z#0", unstableChainB) ∈
        evalAtom unstableChainSpace noDispatch
          unstableTopAtom Atom.undefinedType unstableChainB (fuel0 + 6) := by
    exact h_eventual (fuel0 + 6) (Nat.le_add_right fuel0 6)
  rw [evalAtom_unstable_top_level_stabilized_from_fuel6 fuel0] at h_mem
  simp at h_mem

/-- The same unstable top-level result still has an honest fuel-indexed
    filtered witness at the low subfuel used by the evaluator. This shows that
    even filtered-at-fuel evidence is weaker than certification. -/
theorem evalAtom_unstable_top_level_filtered_witness :
    ∃ n, EvalAtomFilteredAtFuel unstableChainSpace noDispatch
      unstableTopAtom Atom.undefinedType unstableChainB n
      (.var "z#0", unstableChainB) := by
  exact evalAtom_reaches_filtered_sound unstableChainSpace noDispatch
    unstableTopAtom Atom.undefinedType unstableChainB
    (.var "z#0", unstableChainB)
    ⟨4, evalAtom_unstable_top_level_low_fuel_reaches⟩

/-- So the global implication `EvalAtom -> EvalAtomCertified` is false.
    This blocks the tempting but wrong plan to prove certification for every
    coarse public `EvalAtom` derivation without strengthening the theorem
    boundary. -/
theorem evalAtom_to_stably_reaches_not_valid :
    ¬ (∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (r : ResultPair),
        EvalAtom space dispatch atom type_ b r →
          EvalAtomStablyReaches space dispatch atom type_ b r) := by
  intro h
  exact evalAtom_unstable_top_level_not_certified <|
    evalAtomStablyReaches_to_certified unstableChainSpace noDispatch
      unstableTopAtom Atom.undefinedType unstableChainB
      (.var "z#0", unstableChainB)
      (h unstableChainSpace noDispatch
        unstableTopAtom Atom.undefinedType unstableChainB
        (.var "z#0", unstableChainB)
        evalAtom_unstable_top_level_derivation)

/-- So the global implication `EvalAtom -> EvalAtomCertified` is false.
    This blocks the tempting but wrong plan to prove certification for every
    coarse public `EvalAtom` derivation without strengthening the theorem
    boundary. -/
theorem evalAtom_to_certified_not_valid :
    ¬ (∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (r : ResultPair),
        EvalAtom space dispatch atom type_ b r →
          EvalAtomCertified space dispatch atom type_ b r) := by
  intro h
  exact evalAtom_unstable_top_level_not_certified <|
    h unstableChainSpace noDispatch
      unstableTopAtom Atom.undefinedType unstableChainB
      (.var "z#0", unstableChainB)
      evalAtom_unstable_top_level_derivation

/-- Even the honest fuel-indexed filtered witness is still not strong enough
    to imply certification. This rules out the next tempting-but-false theorem
    target above the public certification boundary. -/
theorem filtered_witness_to_stably_reaches_not_valid :
    ¬ (∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (r : ResultPair),
        (∃ n, EvalAtomFilteredAtFuel space dispatch atom type_ b n r) →
          EvalAtomStablyReaches space dispatch atom type_ b r) := by
  intro h
  exact evalAtom_unstable_top_level_not_certified <|
    evalAtomStablyReaches_to_certified unstableChainSpace noDispatch
      unstableTopAtom Atom.undefinedType unstableChainB
      (.var "z#0", unstableChainB)
      (h unstableChainSpace noDispatch
        unstableTopAtom Atom.undefinedType unstableChainB
        (.var "z#0", unstableChainB)
        evalAtom_unstable_top_level_filtered_witness)

/-- Even the honest fuel-indexed filtered witness is still not strong enough
    to imply certification. This rules out the next tempting-but-false theorem
    target above the public certification boundary. -/
theorem filtered_witness_to_certified_not_valid :
    ¬ (∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (r : ResultPair),
        (∃ n, EvalAtomFilteredAtFuel space dispatch atom type_ b n r) →
          EvalAtomCertified space dispatch atom type_ b r) := by
  intro h
  exact evalAtom_unstable_top_level_not_certified <|
    h unstableChainSpace noDispatch
      unstableTopAtom Atom.undefinedType unstableChainB
      (.var "z#0", unstableChainB)
      evalAtom_unstable_top_level_filtered_witness

/-! ## 7. MinimalStep derivation witnesses -/

/-- cons-atom builds an expression. -/
theorem minimal_cons_atom :
    MinimalStep noDispatch emptySpace
      (.expression [.symbol "cons-atom", .symbol "a", .expression [.symbol "b"]]) emptyB
      emptySpace
      (.expression [.symbol "a", .symbol "b"], emptyB) :=
  .cons_atom _ _ _ _

/-- decons-atom splits an expression. -/
theorem minimal_decons_atom :
    MinimalStep noDispatch emptySpace
      (.expression [.symbol "decons-atom", .expression [.symbol "a", .symbol "b"]]) emptyB
      emptySpace
      (.expression [.symbol "a", .expression [.symbol "b"]], emptyB) :=
  .decons_atom _ _ _ _

/-! ## 8. queryEquations `rfl` tests (Space.lean) -/

/-- Simple ground equation query. -/
theorem queryEquations_simple :
    let space := Space.ofList [
      .expression [.symbol "=", .symbol "foo", .grounded (.int 42)]]
    queryEquations space (.symbol "foo") =
    [(.grounded (.int 42), emptyB)] := rfl

/-- Pattern variable equation query with freshening. -/
theorem queryEquations_pattern :
    let space := Space.ofList [
      .expression [.symbol "=", .expression [.var "x"], .var "x"]]
    queryEquations space (.expression [.symbol "hello"]) =
    [(.var "x#0", emptyB.assign "x#0" (.symbol "hello"))] := rfl

/-! ## 9. Engine-parametric conformance boundary

OSLF supplies the reduction skeleton, while HE keeps its dedicated two-sided
binding relation.  The theorem below is parametric in the executable engine:
each engine contributes observable run relations and proof-bearing bridge
obligations, and the shared theorem packages those obligations as HE
declarative-spec conformance.  Concrete evaluators, the metacircular
interpreter, and future runtimes should instantiate this boundary rather than
rebuilding the refinement statement.
-/

private abbrev ILPattern := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern
private abbrev ILRelEnv := Mettapedia.OSLF.MeTTaIL.Engine.RelationEnv

/-- Observable evaluation surfaces of an executable HE engine.  The record
carries exactly the surfaces every engine under grading exposes; OSLF
LanguageDef-rule steps are carried once by the standalone
`he_premise_core_step_models_oslf_decl_reduction` theorem below, not by a
per-engine field, because that leg is not derived from the engine under
grading. -/
structure HEOperationalEngine where
  evalAtomStep :
    Space → GroundedDispatch → Atom → Atom → Bindings → Nat → ResultPair → Prop
  mettaCallStep :
    Space → GroundedDispatch → Atom → Atom → Bindings → Nat → ResultPair → Prop

/-- Stable top-level reachability through an engine's own `evalAtomStep` surface. -/
def StableEvalAtomStep (engine : HEOperationalEngine)
    (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (r : ResultPair) : Prop :=
  ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
    engine.evalAtomStep space dispatch atom type_ b fuel r

/-- Stable `mettaCall` reachability through an engine's own call-step surface. -/
def StableMettaCallStep (engine : HEOperationalEngine)
    (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (r : ResultPair) : Prop :=
  ∃ fuel0, ∀ fuel, fuel ≥ fuel0 →
    engine.mettaCallStep space dispatch atom type_ b fuel r

/-- Local proof obligations needed to refine an engine to the HE declarative spec. -/
structure HEEngineBridge (engine : HEOperationalEngine) : Prop where
  evalAtom_sound :
    ∀ (space : Space) (dispatch : GroundedDispatch)
      (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
      engine.evalAtomStep space dispatch atom type_ b fuel r →
        EvalAtom space dispatch atom type_ b r
  mettaCall_sound :
    ∀ (space : Space) (dispatch : GroundedDispatch)
      (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
      engine.mettaCallStep space dispatch atom type_ b fuel r →
        MettaCall space dispatch atom type_ b r

/-- Engine-parametric HE conformance, stated against the declarative spec. -/
structure HEEngineModelsDeclarativeSpec (engine : HEOperationalEngine) : Prop where
  evalAtom_models :
    ∀ (space : Space) (dispatch : GroundedDispatch)
      (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
      engine.evalAtomStep space dispatch atom type_ b fuel r →
        EvalAtom space dispatch atom type_ b r
  stableEvalAtom_models :
    ∀ (space : Space) (dispatch : GroundedDispatch)
      (atom type_ : Atom) (b : Bindings) (r : ResultPair),
      StableEvalAtomStep engine space dispatch atom type_ b r →
        EvalAtom space dispatch atom type_ b r
  mettaCall_models :
    ∀ (space : Space) (dispatch : GroundedDispatch)
      (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
      engine.mettaCallStep space dispatch atom type_ b fuel r →
        MettaCall space dispatch atom type_ b r
  stableMettaCall_models :
    ∀ (space : Space) (dispatch : GroundedDispatch)
      (atom type_ : Atom) (b : Bindings) (r : ResultPair),
      StableMettaCallStep engine space dispatch atom type_ b r →
        MettaCall space dispatch atom type_ b r

theorem engine_parametric_he_refinement
    (engine : HEOperationalEngine) (bridge : HEEngineBridge engine) :
    HEEngineModelsDeclarativeSpec engine where
  evalAtom_models := bridge.evalAtom_sound
  stableEvalAtom_models := by
    intro space dispatch atom type_ b r hstable
    rcases hstable with ⟨fuel0, hstep⟩
    exact bridge.evalAtom_sound space dispatch atom type_ b fuel0 r
      (hstep fuel0 le_rfl)
  mettaCall_models := bridge.mettaCall_sound
  stableMettaCall_models := by
    intro space dispatch atom type_ b r hstable
    rcases hstable with ⟨fuel0, hstep⟩
    exact bridge.mettaCall_sound space dispatch atom type_ b fuel0 r
      (hstep fuel0 le_rfl)

def heFuelEvaluatorEngine : HEOperationalEngine where
  evalAtomStep := fun space dispatch atom type_ b fuel r =>
    r ∈ evalAtom space dispatch atom type_ b fuel
  mettaCallStep := fun space dispatch atom type_ b fuel r =>
    r ∈ mettaCall space dispatch atom type_ b fuel
/-- HE premise-core LanguageDef steps are exactly framed by OSLF's
    premise-aware declarative reduction skeleton.  The HE matcher itself stays
    the dedicated `matchAtoms`/`Bindings` relation; this theorem only uses OSLF
    for the reduction/congruence layer where the abstraction is faithful. -/
theorem he_premise_core_step_models_oslf_decl_reduction
    {relEnv : ILRelEnv} {p q : ILPattern}
    (h : Mettapedia.Languages.MeTTa.HE.CoreFragment.HEPremiseCoreStep relEnv p q) :
    Mettapedia.OSLF.MeTTaIL.DeclReducesPremises.DeclReducesWithPremises
      relEnv Mettapedia.Languages.MeTTa.HE.LanguageDef.mettaHE p q := by
  exact Mettapedia.Languages.MeTTa.HE.CoreFragment.toDeclReducesWithPremises h

theorem heFuelEvaluatorEngine_bridge : HEEngineBridge heFuelEvaluatorEngine where
  evalAtom_sound := by
    intro space dispatch atom type_ b fuel r hmem
    exact evalAtom_sound space dispatch atom type_ b fuel r hmem
  mettaCall_sound := by
    intro space dispatch atom type_ b fuel r hmem
    exact mettaCall_sound space dispatch atom type_ b fuel r hmem

theorem heFuelEvaluatorEngine_models_declarative_he :
    HEEngineModelsDeclarativeSpec heFuelEvaluatorEngine :=
  engine_parametric_he_refinement heFuelEvaluatorEngine heFuelEvaluatorEngine_bridge

/-! ### LeaTTa equation-call fragment hook

This is not a complete LeaTTa engine instance.  It exposes the exact local
`mettaCall_sound` obligation discharged by the equation-call bridge in
`LeaTTaBridge`: any future engine whose call-step relation refines that
step-shaped fragment already satisfies the corresponding declarative HE
`MettaCall` obligation. -/

theorem leattaEquationFragment_mettaCall_sound
    (engine : HEOperationalEngine)
    (h_refines :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.mettaCallStep space dispatch atom type_ b fuel r →
          LeaTTaBridge.LeaTTaEquationMettaCallStep
            space dispatch fuel atom type_ b r) :
    ∀ (space : Space) (dispatch : GroundedDispatch)
      (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
      engine.mettaCallStep space dispatch atom type_ b fuel r →
        MettaCall space dispatch atom type_ b r := by
  intro space dispatch atom type_ b fuel r hstep
  exact LeaTTaBridge.leattaEquationMettaCallStep_sound
    (h_refines space dispatch atom type_ b fuel r hstep)

/-- Assemble a full `HEEngineBridge` from explicit non-LeaTTa obligations plus
the proven LeaTTa equation-call fragment for `mettaCallStep`.

This theorem is deliberately obligation-preserving: it does not manufacture a
LeaTTa engine, and it does not claim the equation fragment covers all possible
runtimes unless the caller proves that their engine's `mettaCallStep` relation
really refines `LeaTTaEquationMettaCallStep`. -/
theorem engine_bridge_of_leattaEquationFragment_mettaCall
    (engine : HEOperationalEngine)
    (h_eval :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.evalAtomStep space dispatch atom type_ b fuel r →
          EvalAtom space dispatch atom type_ b r)
    (h_metta_refines :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.mettaCallStep space dispatch atom type_ b fuel r →
          LeaTTaBridge.LeaTTaEquationMettaCallStep
            space dispatch fuel atom type_ b r) :
    HEEngineBridge engine where
  evalAtom_sound := h_eval
  mettaCall_sound := leattaEquationFragment_mettaCall_sound engine h_metta_refines
/-- Engine-parametric declarative HE model theorem for any engine whose
`mettaCallStep` surface is proven to refine the LeaTTa equation-call fragment,
with the remaining engine obligations supplied explicitly. -/
theorem engine_models_declarative_he_of_leattaEquationFragment_mettaCall
    (engine : HEOperationalEngine)
    (h_eval :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.evalAtomStep space dispatch atom type_ b fuel r →
          EvalAtom space dispatch atom type_ b r)
    (h_metta_refines :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.mettaCallStep space dispatch atom type_ b fuel r →
          LeaTTaBridge.LeaTTaEquationMettaCallStep
            space dispatch fuel atom type_ b r) :
    HEEngineModelsDeclarativeSpec engine :=
  engine_parametric_he_refinement engine
    (engine_bridge_of_leattaEquationFragment_mettaCall
      engine h_eval h_metta_refines)

/-- The currently proved LeaTTa-backed HE engine instance for the equation-call
fragment.  It is intentionally not named as a complete LeaTTa runtime: the
`mettaCallStep` field is exactly the observed equation-call fragment from
`LeaTTaBridge`, while the `evalAtomStep` field exposes the already-declarative
HE eval surface needed by the shared refinement theorem. -/
def leattaEquationFragmentEngine : HEOperationalEngine where
  evalAtomStep := fun space dispatch atom type_ b _fuel r =>
    EvalAtom space dispatch atom type_ b r
  mettaCallStep := fun space dispatch atom type_ b fuel r =>
    LeaTTaBridge.LeaTTaEquationMettaCallStep
      space dispatch fuel atom type_ b r

theorem leattaEquationFragmentEngine_bridge :
    HEEngineBridge leattaEquationFragmentEngine :=
  engine_bridge_of_leattaEquationFragment_mettaCall
    leattaEquationFragmentEngine
    (by
      intro space dispatch atom type_ b fuel r hstep
      simpa [leattaEquationFragmentEngine] using hstep)
    (by
      intro space dispatch atom type_ b fuel r hstep
      simpa [leattaEquationFragmentEngine] using hstep)
theorem leattaEquationFragmentEngine_models_declarative_he :
    HEEngineModelsDeclarativeSpec leattaEquationFragmentEngine :=
  engine_parametric_he_refinement
    leattaEquationFragmentEngine leattaEquationFragmentEngine_bridge

/-! ### LeaTTa equation/no-match fragment hook

The next honest widening adds the non-ground no-match branch.  It is still a
fragment instance, not a full LeaTTa engine: the executable side contributes
LeaTTa `queryOp` observations for equation hits or `NotReducible`, while the
official HE query premises remain explicit. -/

theorem leattaEquationNoMatchFragment_mettaCall_sound
    (engine : HEOperationalEngine)
    (h_refines :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.mettaCallStep space dispatch atom type_ b fuel r →
          LeaTTaBridge.LeaTTaEquationNoMatchMettaCallStep
            space dispatch fuel atom type_ b r) :
    ∀ (space : Space) (dispatch : GroundedDispatch)
      (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
      engine.mettaCallStep space dispatch atom type_ b fuel r →
        MettaCall space dispatch atom type_ b r := by
  intro space dispatch atom type_ b fuel r hstep
  exact LeaTTaBridge.leattaEquationNoMatchMettaCallStep_sound
    (h_refines space dispatch atom type_ b fuel r hstep)

def leattaEquationNoMatchFragmentEngine : HEOperationalEngine where
  evalAtomStep := fun space dispatch atom type_ b _fuel r =>
    EvalAtom space dispatch atom type_ b r
  mettaCallStep := fun space dispatch atom type_ b fuel r =>
    LeaTTaBridge.LeaTTaEquationNoMatchMettaCallStep
      space dispatch fuel atom type_ b r
theorem leattaEquationNoMatchFragmentEngine_bridge :
    HEEngineBridge leattaEquationNoMatchFragmentEngine where
  evalAtom_sound := by
    intro space dispatch atom type_ b fuel r hstep
    simpa [leattaEquationNoMatchFragmentEngine] using hstep
  mettaCall_sound := by
    intro space dispatch atom type_ b fuel r hstep
    exact LeaTTaBridge.leattaEquationNoMatchMettaCallStep_sound hstep
theorem leattaEquationNoMatchFragmentEngine_models_declarative_he :
    HEEngineModelsDeclarativeSpec leattaEquationNoMatchFragmentEngine :=
  engine_parametric_he_refinement
    leattaEquationNoMatchFragmentEngine
    leattaEquationNoMatchFragmentEngine_bridge

/-- Concrete positive readout for the widened fragment: the empty-space
symbol-headed no-match executable observation satisfies official HE
`MettaCall.no_match` through the engine-parametric call surface. -/
theorem emptySpace_foo_equationNoMatchFragment_models_mettaCall :
    MettaCall Space.empty GroundedDispatch.none
      (.expression [.symbol "foo"]) Atom.undefinedType Bindings.empty
      (.expression [.symbol "foo"], Bindings.empty) :=
  leattaEquationNoMatchFragmentEngine_models_declarative_he.mettaCall_models
    Space.empty GroundedDispatch.none
    (.expression [.symbol "foo"]) Atom.undefinedType Bindings.empty 10
    (.expression [.symbol "foo"], Bindings.empty)
    LeaTTaBridge.emptySpace_foo_equationNoMatchMettaCallStep_counter0

/-! ### LeaTTa query/unify fragment hook

This widening adds the primitive `unify` raw success/fallback lane to the
already-proved equation/no-match query fragment. -/

theorem leattaQueryUnifyFragment_mettaCall_sound
    (engine : HEOperationalEngine)
    (h_refines :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.mettaCallStep space dispatch atom type_ b fuel r →
          LeaTTaBridge.LeaTTaQueryUnifyMettaCallStep
            space dispatch fuel atom type_ b r) :
    ∀ (space : Space) (dispatch : GroundedDispatch)
      (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
      engine.mettaCallStep space dispatch atom type_ b fuel r →
        MettaCall space dispatch atom type_ b r := by
  intro space dispatch atom type_ b fuel r hstep
  exact LeaTTaBridge.leattaQueryUnifyMettaCallStep_sound
    (h_refines space dispatch atom type_ b fuel r hstep)

def leattaQueryUnifyFragmentEngine : HEOperationalEngine where
  evalAtomStep := fun space dispatch atom type_ b _fuel r =>
    EvalAtom space dispatch atom type_ b r
  mettaCallStep := fun space dispatch atom type_ b fuel r =>
    LeaTTaBridge.LeaTTaQueryUnifyMettaCallStep
      space dispatch fuel atom type_ b r
theorem leattaQueryUnifyFragmentEngine_bridge :
    HEEngineBridge leattaQueryUnifyFragmentEngine where
  evalAtom_sound := by
    intro space dispatch atom type_ b fuel r hstep
    simpa [leattaQueryUnifyFragmentEngine] using hstep
  mettaCall_sound := by
    intro space dispatch atom type_ b fuel r hstep
    exact LeaTTaBridge.leattaQueryUnifyMettaCallStep_sound hstep
theorem leattaQueryUnifyFragmentEngine_models_declarative_he :
    HEEngineModelsDeclarativeSpec leattaQueryUnifyFragmentEngine :=
  engine_parametric_he_refinement
    leattaQueryUnifyFragmentEngine
    leattaQueryUnifyFragmentEngine_bridge

/-- Concrete positive readout for the primitive `unify` fallback lane: a
symbol mismatch in LeaTTa `unifyOp` and the official HE raw fallback premise
produce the declarative HE `MettaCall.unify_no_match_raw` result. -/
theorem emptySpace_unifySymbolMismatch_queryUnifyFragment_models_mettaCall :
    MettaCall Space.empty GroundedDispatch.none
      (.expression [.symbol "unify", .symbol "a", .symbol "b",
        .symbol "then", .symbol "else"])
      Atom.undefinedType Bindings.empty
      (.symbol "else", Bindings.empty) :=
  leattaQueryUnifyFragmentEngine_models_declarative_he.mettaCall_models
    Space.empty GroundedDispatch.none
    (.expression [.symbol "unify", .symbol "a", .symbol "b",
      .symbol "then", .symbol "else"])
    Atom.undefinedType Bindings.empty 10
    (.symbol "else", Bindings.empty)
    LeaTTaBridge.emptySpace_unifySymbolMismatch_queryUnifyMettaCallStep_counter0

/-- General positive readout for the primitive `unify` success lane on the
ground-target/variable-pattern fragment. The executable LeaTTa singleton
match/merge evidence is derived by `LeaTTaBridge` from `GroundAtom target`; the
declarative conclusion is the official HE `MettaCall` result. -/
theorem groundTarget_unifyVar_queryUnifyFragment_models_mettaCall
    {space : Space} {d : GroundedDispatch}
    {target thenBranch elseBranch type_ : Atom} {v : String}
    (hground : GroundAtom target)
    (hdepth : LeaTTaBridge.atomDepth thenBranch + 2 ≤ 100) :
    MettaCall space d
      (.expression [.symbol "unify", target, .var v, thenBranch, elseBranch])
      type_ Bindings.empty
      ((Bindings.empty.assign v target).applyDefault thenBranch,
        Bindings.empty.assign v target) :=
  leattaQueryUnifyFragmentEngine_models_declarative_he.mettaCall_models
    space d
    (.expression [.symbol "unify", target, .var v, thenBranch, elseBranch])
    type_ Bindings.empty 10
    ((Bindings.empty.assign v target).applyDefault thenBranch,
      Bindings.empty.assign v target)
    (Or.inr <|
      LeaTTaBridge.leattaUnifyMettaCallStep_success_ground_var_empty_seed
        (space := space) (d := d) (n := 9)
        (target := target) (v := v) (thenBranch := thenBranch)
        (elseBranch := elseBranch) (type_ := type_)
        hground hdepth)

/-- Concrete positive readout for the primitive `unify` success lane: matching
`a` against `$x` returns the success branch `$x` instantiated to `a`, with the
official HE match binding carried through the query/unify fragment engine. -/
theorem emptySpace_unifyVarSymbol_queryUnifyFragment_models_mettaCall :
    MettaCall Space.empty GroundedDispatch.none
      (.expression [.symbol "unify", .symbol "a", .var "x",
        .var "x", .symbol "else"])
      Atom.undefinedType Bindings.empty
      (.symbol "a", Bindings.empty.assign "x" (.symbol "a")) := by
  simpa [Bindings.applyDefault, Bindings.apply, Bindings.resolve,
    Bindings.resolveAtomAux, Bindings.hasAssignedVar, Bindings.hasAssignedVarAux,
    Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup] using
    groundTarget_unifyVar_queryUnifyFragment_models_mettaCall
      (space := Space.empty) (d := GroundedDispatch.none)
      (target := .symbol "a") (v := "x") (thenBranch := .var "x")
      (elseBranch := .symbol "else") (type_ := Atom.undefinedType)
      (GroundAtom.symbol "a") (by simp [LeaTTaBridge.atomDepth])

private def heBadUnifyThreeArgs : Atom :=
  .expression [.symbol "unify", .symbol "a", .symbol "p", .symbol "t"]

private def leattaBadUnifyThreeArgs : Metta.Atom :=
  Metta.Atom.expr
    [Metta.Atom.sym "unify", Metta.Atom.sym "a",
      Metta.Atom.sym "p", Metta.Atom.sym "t"]

theorem leatta_bad_unify_three_args_is_HE_translation :
    LeaTTaBridge.toLeaTTaAtom heBadUnifyThreeArgs =
      leattaBadUnifyThreeArgs := rfl

private def leattaBadUnifyThreeArgsError : Metta.Atom :=
  Metta.Minimal.errAtom leattaBadUnifyThreeArgs
    (Metta.Minimal.unifyBadArityMessage leattaBadUnifyThreeArgs)

/-- LeaTTa's minimal interpreter surfaces malformed primitive `unify` with the
same descriptive bad-arity message as the HE reference. -/
theorem leatta_minimal_unify_bad_arity_eval_message :
    Metta.Minimal.evalAtomMin
      (Metta.Minimal.MinEnv.ofAtomsGT [] []) 4
      leattaBadUnifyThreeArgs =
    [leattaBadUnifyThreeArgsError] := by
  simp [Metta.Minimal.evalAtomMin, Metta.Minimal.interpretAtom,
    Metta.Minimal.interpretFuel, Metta.Minimal.interpretStack1,
    Metta.Minimal.evalOp, Metta.Minimal.atomToStack, Metta.Minimal.isEmbeddedOp,
    Metta.Minimal.isFinal, Metta.Minimal.finalPair,
    Metta.Minimal.MinEnv.ofAtomsGT, Metta.Minimal.extractRules,
    Metta.callGrounded, Metta.GroundingTable.lookup,
    Metta.instantiate,
    Metta.Minimal.St.init, Metta.Minimal.World.empty,
    leattaBadUnifyThreeArgs, leattaBadUnifyThreeArgsError,
    Metta.Minimal.errAtom, Metta.Minimal.unifyBadArityMessage]
  exact ⟨[], rfl⟩

/-- The malformed-`unify` minimal-interpreter message is not the HE reserved
arity-error symbol. -/
theorem leatta_minimal_unify_bad_arity_message_not_HE_reserved_symbol :
    leattaBadUnifyThreeArgsError ≠
      Metta.Minimal.errAtom leattaBadUnifyThreeArgs
        "IncorrectNumberOfArguments" := by
  intro h
  simp [leattaBadUnifyThreeArgsError, leattaBadUnifyThreeArgs,
    Metta.Minimal.errAtom, Metta.Minimal.unifyBadArityMessage] at h

theorem HE_unify_bad_arity_three_args_mettaCall :
    MettaCall Space.empty GroundedDispatch.none
      heBadUnifyThreeArgs Atom.undefinedType Bindings.empty
      (mkUnifyBadArityError heBadUnifyThreeArgs, Bindings.empty) := by
  exact MettaCall.unify_bad_arity
    heBadUnifyThreeArgs Atom.undefinedType Bindings.empty
    [.symbol "a", .symbol "p", .symbol "t"]
    rfl (by decide) rfl

theorem leatta_minimal_unify_bad_arity_error_is_HE_bad_arity_translation :
    leattaBadUnifyThreeArgsError =
      LeaTTaBridge.toLeaTTaAtom
        (mkUnifyBadArityError heBadUnifyThreeArgs) := by
  simp [leattaBadUnifyThreeArgsError, leattaBadUnifyThreeArgs,
    heBadUnifyThreeArgs, mkUnifyBadArityError, mkErrorMessage,
    unifyBadArityMessage, Atom.error, LeaTTaBridge.toLeaTTaAtom,
    LeaTTaBridge.toLeaTTaAtoms, Metta.Minimal.errAtom,
    Metta.Minimal.unifyBadArityMessage]

/-- Exact malformed-`unify` branch agreement: LeaTTa's minimal executable
readout and the HE declarative reference surface the same bad-arity error for a
three-argument primitive `unify`. -/
theorem leatta_minimal_unify_bad_arity_matches_HE_bad_arity_surface :
    Metta.Minimal.evalAtomMin
        (Metta.Minimal.MinEnv.ofAtomsGT [] []) 4
        leattaBadUnifyThreeArgs =
      [LeaTTaBridge.toLeaTTaAtom
        (mkUnifyBadArityError heBadUnifyThreeArgs)] ∧
    MettaCall Space.empty GroundedDispatch.none
      heBadUnifyThreeArgs Atom.undefinedType Bindings.empty
      (mkUnifyBadArityError heBadUnifyThreeArgs, Bindings.empty) := by
  constructor
  · rw [← leatta_minimal_unify_bad_arity_error_is_HE_bad_arity_translation]
    exact leatta_minimal_unify_bad_arity_eval_message
  · exact HE_unify_bad_arity_three_args_mettaCall

/-- LeaTTa-backed executable observation for malformed primitive `unify`.
The executable readout is recorded as evidence, while soundness below is
discharged against the HE `MettaCall.unify_bad_arity` reference constructor. -/
def LeaTTaUnifyBadArityMettaCallStep
    (_space : Space) (_d : GroundedDispatch) (fuel : Nat)
    (atom _type_ : Atom) (inputBindings : Bindings)
    (result : ResultPair) : Prop :=
  ∃ tail,
    atom = .expression (.symbol "unify" :: tail) ∧
    tail.length ≠ 4 ∧
    isErrorAtom atom = false ∧
    result = (mkUnifyBadArityError atom, inputBindings) ∧
    Metta.Minimal.evalAtomMin
        (Metta.Minimal.MinEnv.ofAtomsGT [] []) fuel
        (LeaTTaBridge.toLeaTTaAtom atom) =
      [LeaTTaBridge.toLeaTTaAtom (mkUnifyBadArityError atom)]

theorem leattaUnifyBadArityMettaCallStep_sound
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {atom type_ : Atom} {inputBindings : Bindings}
    {result : ResultPair}
    (hstep :
      LeaTTaUnifyBadArityMettaCallStep
        space d fuel atom type_ inputBindings result) :
    MettaCall space d atom type_ inputBindings result := by
  rcases hstep with
    ⟨tail, h_shape, h_arity, h_not_error, h_result, _h_exec⟩
  subst result
  exact MettaCall.unify_bad_arity
    atom type_ inputBindings tail h_shape h_arity h_not_error

theorem leattaBadUnifyThreeArgs_unifyBadArityMettaCallStep_counter4 :
    LeaTTaUnifyBadArityMettaCallStep
      Space.empty GroundedDispatch.none 4
      heBadUnifyThreeArgs Atom.undefinedType Bindings.empty
      (mkUnifyBadArityError heBadUnifyThreeArgs, Bindings.empty) := by
  refine ⟨[.symbol "a", .symbol "p", .symbol "t"], rfl, by decide, rfl, rfl, ?_⟩
  exact leatta_minimal_unify_bad_arity_matches_HE_bad_arity_surface.1

/-! ### LeaTTa query/unify fragment with extensional primitive bindings

This sibling fragment keeps the same engine-parametric refinement surface, but
uses the lookup-extensional executable observation for primitive `unify`. -/

theorem leattaQueryUnifyFragmentExt_mettaCall_sound
    (engine : HEOperationalEngine)
    (h_refines :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.mettaCallStep space dispatch atom type_ b fuel r →
          LeaTTaBridge.LeaTTaQueryUnifyMettaCallStepExt
            space dispatch fuel atom type_ b r) :
    ∀ (space : Space) (dispatch : GroundedDispatch)
      (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
      engine.mettaCallStep space dispatch atom type_ b fuel r →
        MettaCall space dispatch atom type_ b r := by
  intro space dispatch atom type_ b fuel r hstep
  exact LeaTTaBridge.leattaQueryUnifyMettaCallStepExt_sound
    (h_refines space dispatch atom type_ b fuel r hstep)

def leattaQueryUnifyFragmentExtEngine : HEOperationalEngine where
  evalAtomStep := fun space dispatch atom type_ b _fuel r =>
    EvalAtom space dispatch atom type_ b r
  mettaCallStep := fun space dispatch atom type_ b fuel r =>
    LeaTTaBridge.LeaTTaQueryUnifyMettaCallStepExt
      space dispatch fuel atom type_ b r
theorem leattaQueryUnifyFragmentExtEngine_bridge :
    HEEngineBridge leattaQueryUnifyFragmentExtEngine where
  evalAtom_sound := by
    intro space dispatch atom type_ b fuel r hstep
    simpa [leattaQueryUnifyFragmentExtEngine] using hstep
  mettaCall_sound := by
    intro space dispatch atom type_ b fuel r hstep
    exact LeaTTaBridge.leattaQueryUnifyMettaCallStepExt_sound hstep
theorem leattaQueryUnifyFragmentExtEngine_models_declarative_he :
    HEEngineModelsDeclarativeSpec leattaQueryUnifyFragmentExtEngine :=
  engine_parametric_he_refinement
    leattaQueryUnifyFragmentExtEngine
    leattaQueryUnifyFragmentExtEngine_bridge

/-- Concrete positive readout for the non-empty-seed primitive `unify` lane:
LeaTTa's runtime merge order differs from the official HE raw result order,
but the emitted binding set is direct-lookup equivalent, so the shared
engine-parametric refinement still yields the exact HE `MettaCall`. -/
theorem seededUnifyOrder_queryUnifyFragmentExt_models_mettaCall :
    MettaCall Space.empty GroundedDispatch.none
      (.expression [.symbol "unify", .symbol "a", .var "x",
        .var "x", .symbol "else"])
      Atom.undefinedType LeaTTaBridge.seededUnifyOrderSeed
      (.symbol "a", LeaTTaBridge.seededUnifyOrderHEMerged) :=
  leattaQueryUnifyFragmentExtEngine_models_declarative_he.mettaCall_models
    Space.empty GroundedDispatch.none
    (.expression [.symbol "unify", .symbol "a", .var "x",
      .var "x", .symbol "else"])
    Atom.undefinedType LeaTTaBridge.seededUnifyOrderSeed 10
    (.symbol "a", LeaTTaBridge.seededUnifyOrderHEMerged)
    LeaTTaBridge.seededUnifyOrder_queryUnifyMettaCallStepExt_counter0

/-- Conformance-facing schema for the equality-aware visible equation bridge.
The executable side supplies a repaired LeaTTa visible observation; the
declarative side remains the official HE `queryEquations`/`mergeBindings`/
recursive-`EvalAtom` premise bundle. This is the bridge shape needed for
equality-bearing matches that cannot pass through the assignment-only
instantiated-RHS shortcut. -/
theorem leattaVisibleEquationObservation_models_mettaCall
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {src dst type_ rhs : Atom}
    {queryBindings inputBindings merged outputBindings : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat}
    (hobs :
      LeaTTaBridge.LeaTTaVisibleEquationStepObservation
        space d fuel src dst gt prev counter)
    (h_not_error : isErrorAtom src = false)
    (h_not_grounded : HeadNotExecutable d src)
    (h_query_public : (rhs, queryBindings) ∈ queryEquations space src fuel)
    (h_merge : merged ∈ mergeBindings queryBindings inputBindings fuel)
    (h_no_loop : merged.hasLoop = false)
    (h_recurse :
      EvalAtom space d (merged.applyFull rhs fuel) type_ merged
        (dst, outputBindings)) :
    MettaCall space d src type_ inputBindings (dst, outputBindings) := by
  exact
    (LeaTTaBridge.observedMettaCall_of_equation_match
      (space := space)
      (d := d)
      (fuel := fuel)
      (src := src)
      (dst := dst)
      (type_ := type_)
      (rhs := rhs)
      (queryBindings := queryBindings)
      (inputBindings := inputBindings)
      (merged := merged)
      (outputBindings := outputBindings)
      (gt := gt)
      (prev := prev)
      (counter := counter)
      hobs h_not_error h_not_grounded h_query_public h_merge
      h_no_loop h_recurse).2

/-- Conformance-facing schema for the repaired visible-avoid transport path.
This is the equality-aware counterpart of the instantiated-RHS fragment below:
once the public HE query witness, visible HE query witness, avoid-aware LeaTTa
transport, and recursive `EvalAtom` premise are supplied, the official
declarative HE `MettaCall` result follows. -/
theorem leattaTransportAgainstVisible_models_mettaCall
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {rhs type_ : Atom} {qb outputBindings : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat} {k : String}
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_error : isErrorAtom (.expression es) = false)
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (hk : Metta.Minimal.headKey
      (LeaTTaBridge.toLeaTTaAtom (.expression es)) = some k)
    (h_query_visible : (rhs, qb) ∈
      queryEquationsAgainstVisible space (.expression es) fuel)
    (h_query_public : (rhs, qb) ∈
      queryEquations space (.expression es) fuel)
    (htransport : LeaTTaBridge.EquationMatchVisibleItemTransportAgainst
      space (.expression es) rhs qb fuel gt prev counter)
    (h_recurse :
      EvalAtom space d (qb.applyFull rhs fuel) type_ qb
        (qb.applyFull rhs fuel, outputBindings)) :
  MettaCall space d (.expression es) type_ Bindings.empty
      (qb.applyFull rhs fuel, outputBindings) := by
  exact
    LeaTTaBridge.leattaEquationMettaCallStep_sound
      (LeaTTaBridge.leattaEquationMettaCallStep_of_transport_againstVisible_empty_input
        (space := space)
        (d := d)
        (fuel := fuel)
        (es := es)
        (rhs := rhs)
        (type_ := type_)
        (qb := qb)
        (outputBindings := outputBindings)
        (gt := gt)
        (prev := prev)
        (counter := counter)
        (k := k)
        h_not_special h_not_error h_not_grounded hk h_query_visible
        h_query_public htransport h_recurse)

/-- Binding-threaded conformance schema for the repaired visible-avoid
transport path. This removes the empty-input restriction from
`leattaTransportAgainstVisible_models_mettaCall` while keeping the exact HE
merge, loop, and recursive-evaluation premises visible. The result atom is
still the visible equation successor observed by LeaTTa. -/
theorem leattaTransportAgainstVisibleWithMerge_models_mettaCall
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {rhs type_ : Atom}
    {qb inputBindings merged outputBindings : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat} {k : String}
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_error : isErrorAtom (.expression es) = false)
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (hk : Metta.Minimal.headKey
      (LeaTTaBridge.toLeaTTaAtom (.expression es)) = some k)
    (h_query_visible : (rhs, qb) ∈
      queryEquationsAgainstVisible space (.expression es) fuel)
    (h_query_public : (rhs, qb) ∈
      queryEquations space (.expression es) fuel)
    (htransport : LeaTTaBridge.EquationMatchVisibleItemTransportAgainst
      space (.expression es) rhs qb fuel gt prev counter)
    (h_merge : merged ∈ mergeBindings qb inputBindings fuel)
    (h_no_loop : merged.hasLoop = false)
    (h_recurse :
      EvalAtom space d (merged.applyFull rhs fuel) type_ merged
        (qb.applyFull rhs fuel, outputBindings)) :
  MettaCall space d (.expression es) type_ inputBindings
      (qb.applyFull rhs fuel, outputBindings) := by
  exact
    LeaTTaBridge.leattaEquationMettaCallStep_sound
      (LeaTTaBridge.leattaEquationMettaCallStep_of_transport_againstVisible_with_merge
        (space := space)
        (d := d)
        (fuel := fuel)
        (es := es)
        (rhs := rhs)
        (type_ := type_)
        (qb := qb)
        (inputBindings := inputBindings)
        (merged := merged)
        (outputBindings := outputBindings)
        (gt := gt)
        (prev := prev)
        (counter := counter)
        (k := k)
        h_not_special h_not_error h_not_grounded hk h_query_visible
        h_query_public htransport h_merge h_no_loop h_recurse)

/-- Continuation-aware conformance schema for an equality-aware visible LeaTTa
observation.  The executable observation records the immediate equation
successor, while the official HE `MettaCall` result is exactly the result of
the recursive `EvalAtom` premise. -/
theorem leattaVisibleEquationObservation_models_mettaCall_final
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {src visibleDst type_ rhs : Atom}
    {queryBindings inputBindings merged : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat} {finalResult : ResultPair}
    (hobs :
      LeaTTaBridge.LeaTTaVisibleEquationStepObservation
        space d fuel src visibleDst gt prev counter)
    (h_not_error : isErrorAtom src = false)
    (h_not_grounded : HeadNotExecutable d src)
    (h_query_public : (rhs, queryBindings) ∈ queryEquations space src fuel)
    (h_merge : merged ∈ mergeBindings queryBindings inputBindings fuel)
    (h_no_loop : merged.hasLoop = false)
    (h_recurse :
      EvalAtom space d (merged.applyFull rhs fuel) type_ merged finalResult) :
  MettaCall space d src type_ inputBindings finalResult := by
  exact
    LeaTTaBridge.leattaEquationMettaCallStep_sound
      (LeaTTaBridge.leattaEquationMettaCallStep_of_visible_observation_with_merge_final
        (space := space)
        (d := d)
        (fuel := fuel)
        (src := src)
        (visibleDst := visibleDst)
        (type_ := type_)
        (rhs := rhs)
        (queryBindings := queryBindings)
        (inputBindings := inputBindings)
        (merged := merged)
        (gt := gt)
        (prev := prev)
        (counter := counter)
        (finalResult := finalResult)
        hobs h_not_error h_not_grounded h_query_public h_merge
        h_no_loop h_recurse)

/-- Continuation-aware conformance schema for the repaired visible-avoid
transport path. This is the version needed by the full equation-call rule: the
visible LeaTTa `queryOp` item only has to agree with the immediate HE equation
successor, not with the recursive final result. -/
theorem leattaTransportAgainstVisibleWithMerge_models_mettaCall_final
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {rhs type_ : Atom}
    {qb inputBindings merged : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat} {k : String} {finalResult : ResultPair}
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_error : isErrorAtom (.expression es) = false)
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (hk : Metta.Minimal.headKey
      (LeaTTaBridge.toLeaTTaAtom (.expression es)) = some k)
    (h_query_visible : (rhs, qb) ∈
      queryEquationsAgainstVisible space (.expression es) fuel)
    (h_query_public : (rhs, qb) ∈
      queryEquations space (.expression es) fuel)
    (htransport : LeaTTaBridge.EquationMatchVisibleItemTransportAgainst
      space (.expression es) rhs qb fuel gt prev counter)
    (h_merge : merged ∈ mergeBindings qb inputBindings fuel)
    (h_no_loop : merged.hasLoop = false)
    (h_recurse :
      EvalAtom space d (merged.applyFull rhs fuel) type_ merged finalResult) :
  MettaCall space d (.expression es) type_ inputBindings finalResult := by
  exact
    LeaTTaBridge.leattaEquationMettaCallStep_sound
      (LeaTTaBridge.leattaEquationMettaCallStep_of_transport_againstVisible_with_merge_final
        (space := space)
        (d := d)
        (fuel := fuel)
        (es := es)
        (rhs := rhs)
        (type_ := type_)
        (qb := qb)
        (inputBindings := inputBindings)
        (merged := merged)
        (gt := gt)
        (prev := prev)
        (counter := counter)
        (k := k)
        (finalResult := finalResult)
        h_not_special h_not_error h_not_grounded hk h_query_visible
        h_query_public htransport h_merge h_no_loop h_recurse)

/-- Conformance schema for the concrete executable `queryOp` hit boundary.
Unlike the transport-based schema, this theorem consumes the runtime evidence
directly: a LeaTTa `queryOp` item alpha-equivalent to the immediate HE visible
equation successor. -/
theorem leattaQueryOpHitAgainstVisibleWithMerge_models_mettaCall_final
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {rhs type_ : Atom}
    {qb inputBindings merged : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat} {finalResult : ResultPair}
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_error : isErrorAtom (.expression es) = false)
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (h_query_visible : (rhs, qb) ∈
      queryEquationsAgainstVisible space (.expression es) fuel)
    (h_query_public : (rhs, qb) ∈
      queryEquations space (.expression es) fuel)
    (hhit :
      LeaTTaBridge.LeaTTaEquationQueryOpHit
        space fuel (.expression es) (qb.applyFull rhs fuel) gt prev counter)
    (h_merge : merged ∈ mergeBindings qb inputBindings fuel)
    (h_no_loop : merged.hasLoop = false)
    (h_recurse :
      EvalAtom space d (merged.applyFull rhs fuel) type_ merged finalResult) :
  MettaCall space d (.expression es) type_ inputBindings finalResult := by
  exact
    LeaTTaBridge.leattaEquationMettaCallStep_sound
      (LeaTTaBridge.leattaEquationMettaCallStep_of_queryOp_hit_againstVisible_with_merge_final
        (space := space)
        (d := d)
        (fuel := fuel)
        (es := es)
        (rhs := rhs)
        (type_ := type_)
        (qb := qb)
        (inputBindings := inputBindings)
        (merged := merged)
        (gt := gt)
        (prev := prev)
        (counter := counter)
        (finalResult := finalResult)
        h_not_special h_not_error h_not_grounded h_query_visible
        h_query_public hhit h_merge h_no_loop h_recurse)

/-- Query-match-aware version of the concrete executable `queryOp` boundary.
In addition to the official HE `MettaCall`, this packages the public and
visible query hits with their dedicated HE `MatchRel` witnesses.  The result
keeps the executable observation and the declarative query evidence together,
which is the shape the engine-parametric conformance theorem needs. -/
theorem leattaQueryOpHitAgainstVisibleWithMerge_models_mettaCall_final_with_queryMatchRel
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {rhs type_ : Atom}
    {qb inputBindings merged : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat} {finalResult : ResultPair}
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_error : isErrorAtom (.expression es) = false)
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (h_query_visible : (rhs, qb) ∈
      queryEquationsAgainstVisible space (.expression es) fuel)
    (h_query_public : (rhs, qb) ∈
      queryEquations space (.expression es) fuel)
    (hhit :
      LeaTTaBridge.LeaTTaEquationQueryOpHit
        space fuel (.expression es) (qb.applyFull rhs fuel) gt prev counter)
    (h_merge : merged ∈ mergeBindings qb inputBindings fuel)
    (h_no_loop : merged.hasLoop = false)
    (h_recurse :
      EvalAtom space d (merged.applyFull rhs fuel) type_ merged finalResult) :
    MettaCall space d (.expression es) type_ inputBindings finalResult ∧
    (∃ lhs rhs0 idx,
      (.expression [.symbol "=", lhs, rhs0], idx) ∈ space.atoms.zipIdx ∧
      rhs = (freshenEquation idx lhs rhs0 fuel).2 ∧
      DeclMatchSpec.MatchRel
        (.expression es) (freshenEquation idx lhs rhs0 fuel).1 qb) ∧
    (∃ lhs rhs0 idx,
      (.expression [.symbol "=", lhs, rhs0], idx) ∈ space.atoms.zipIdx ∧
      rhs =
        (freshenEquationAgainst
          (collectVars (.expression es) fuel).eraseDups idx lhs rhs0 fuel).2 ∧
      DeclMatchSpec.MatchRel
        (.expression es)
        (freshenEquationAgainst
          (collectVars (.expression es) fuel).eraseDups idx lhs rhs0 fuel).1
        qb) := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      leattaQueryOpHitAgainstVisibleWithMerge_models_mettaCall_final
        (space := space)
        (d := d)
        (fuel := fuel)
        (es := es)
        (rhs := rhs)
        (type_ := type_)
        (qb := qb)
        (inputBindings := inputBindings)
        (merged := merged)
        (gt := gt)
        (prev := prev)
        (counter := counter)
        (finalResult := finalResult)
        h_not_special h_not_error h_not_grounded h_query_visible
        h_query_public hhit h_merge h_no_loop h_recurse
  · exact queryEquations_hits_are_declarative_matches h_query_public
  · exact queryEquationsAgainstVisible_hits_are_declarative_matches h_query_visible

/-- Pure HE evidence package for one visible equation-query step.
It records the public query premise consumed by `MettaCall.equation_match`, the
visible-avoid query premise used by the LeaTTa bridge, and the declarative
`MatchRel` witnesses for both query surfaces.  The package is deliberately
engine-independent: executable engines prove that their observations carry this
evidence, and the theorem below turns the evidence into the official HE
`MettaCall`. -/
structure HEVisibleEquationQueryEvidence
    (space : Space) (d : GroundedDispatch) (fuel : Nat)
    (es : List Atom) (type_ : Atom) (inputBindings : Bindings)
    (finalResult : ResultPair) where
  rhs : Atom
  qb : Bindings
  merged : Bindings
  not_error : isErrorAtom (.expression es) = false
  not_grounded : HeadNotExecutable d (.expression es)
  query_visible : (rhs, qb) ∈
    queryEquationsAgainstVisible space (.expression es) fuel
  query_public : (rhs, qb) ∈
    queryEquations space (.expression es) fuel
  public_match :
    ∃ lhs rhs0 idx,
      (.expression [.symbol "=", lhs, rhs0], idx) ∈ space.atoms.zipIdx ∧
      rhs = (freshenEquation idx lhs rhs0 fuel).2 ∧
      DeclMatchSpec.MatchRel
        (.expression es) (freshenEquation idx lhs rhs0 fuel).1 qb
  visible_match :
    ∃ lhs rhs0 idx,
      (.expression [.symbol "=", lhs, rhs0], idx) ∈ space.atoms.zipIdx ∧
      rhs =
        (freshenEquationAgainst
          (collectVars (.expression es) fuel).eraseDups idx lhs rhs0 fuel).2 ∧
      DeclMatchSpec.MatchRel
        (.expression es)
        (freshenEquationAgainst
          (collectVars (.expression es) fuel).eraseDups idx lhs rhs0 fuel).1
        qb
  merge : merged ∈ mergeBindings qb inputBindings fuel
  no_loop : merged.hasLoop = false
  recurse :
    EvalAtom space d (merged.applyFull rhs fuel) type_ merged finalResult

def visibleEquationQueryEvidence_of_repaired_query_premises
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {rhs type_ : Atom}
    {qb inputBindings merged : Bindings} {finalResult : ResultPair}
    (h_not_error : isErrorAtom (.expression es) = false)
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (h_query_visible : (rhs, qb) ∈
      queryEquationsAgainstVisible space (.expression es) fuel)
    (h_query_public : (rhs, qb) ∈
      queryEquations space (.expression es) fuel)
    (h_merge : merged ∈ mergeBindings qb inputBindings fuel)
    (h_no_loop : merged.hasLoop = false)
    (h_recurse :
      EvalAtom space d (merged.applyFull rhs fuel) type_ merged finalResult) :
    HEVisibleEquationQueryEvidence
      space d fuel es type_ inputBindings finalResult where
  rhs := rhs
  qb := qb
  merged := merged
  not_error := h_not_error
  not_grounded := h_not_grounded
  query_visible := h_query_visible
  query_public := h_query_public
  public_match := queryEquations_hits_are_declarative_matches h_query_public
  visible_match :=
    queryEquationsAgainstVisible_hits_are_declarative_matches h_query_visible
  merge := h_merge
  no_loop := h_no_loop
  recurse := h_recurse

/-- LeaTTa-facing evidence for the repaired visible equation-query path.
It keeps the concrete `queryOp` observation together with the pure HE evidence
consumed by the engine-parametric declarative soundness theorem. -/
structure LeaTTaVisibleEquationQueryEvidence
    (space : Space) (d : GroundedDispatch) (fuel : Nat)
    (es : List Atom) (type_ : Atom) (inputBindings : Bindings)
    (finalResult : ResultPair)
    (gt : Metta.GroundingTable) (prev : Metta.Minimal.Stack)
    (counter : Nat) where
  he : HEVisibleEquationQueryEvidence
    space d fuel es type_ inputBindings finalResult
  hit : LeaTTaBridge.LeaTTaEquationQueryOpHit
    space fuel (.expression es) (he.qb.applyFull he.rhs fuel) gt prev counter

def leattaVisibleEquationQueryEvidence_of_queryOp_hit
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {rhs type_ : Atom}
    {qb inputBindings merged : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat} {finalResult : ResultPair}
    (h_not_error : isErrorAtom (.expression es) = false)
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (h_query_visible : (rhs, qb) ∈
      queryEquationsAgainstVisible space (.expression es) fuel)
    (h_query_public : (rhs, qb) ∈
      queryEquations space (.expression es) fuel)
    (hhit :
      LeaTTaBridge.LeaTTaEquationQueryOpHit
        space fuel (.expression es) (qb.applyFull rhs fuel) gt prev counter)
    (h_merge : merged ∈ mergeBindings qb inputBindings fuel)
    (h_no_loop : merged.hasLoop = false)
    (h_recurse :
      EvalAtom space d (merged.applyFull rhs fuel) type_ merged finalResult) :
    LeaTTaVisibleEquationQueryEvidence
      space d fuel es type_ inputBindings finalResult gt prev counter where
  he :=
    visibleEquationQueryEvidence_of_repaired_query_premises
      h_not_error h_not_grounded h_query_visible h_query_public
      h_merge h_no_loop h_recurse
  hit := hhit

/-- Any engine observation carrying `HEVisibleEquationQueryEvidence` satisfies
the declarative HE equation-call rule.  This is the engine-parametric interface
for the repaired equation-query path; LeaTTa, the metacircular interpreter, and
future engines should prove evidence-production lemmas against this predicate
instead of reopening `queryEquations`. -/
theorem HEVisibleEquationQueryEvidence.models_mettaCall
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {type_ : Atom} {inputBindings : Bindings}
    {finalResult : ResultPair}
    (h : HEVisibleEquationQueryEvidence
      space d fuel es type_ inputBindings finalResult) :
    MettaCall space d (.expression es) type_ inputBindings finalResult := by
  rcases h with
    ⟨rhs, qb, merged, h_not_error, h_not_grounded, _h_query_visible,
      h_query_public, _h_public_match, _h_visible_match,
      h_merge, h_no_loop, h_recurse⟩
  exact
    MettaCall.equation_match
      (.expression es) type_ inputBindings rhs qb merged finalResult fuel
      h_not_error
      (by
        cases es with
        | nil =>
            trivial
        | cons op rest =>
            simpa [HeadNotExecutable] using h_not_grounded)
      h_query_public h_merge h_no_loop h_recurse

/-- A concrete LeaTTa visible-query evidence package models the official
declarative HE `MettaCall` rule by forgetting only the executable observation
and retaining the dedicated HE query evidence. -/
theorem LeaTTaVisibleEquationQueryEvidence.models_mettaCall
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {type_ : Atom} {inputBindings : Bindings}
    {finalResult : ResultPair}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat}
    (h : LeaTTaVisibleEquationQueryEvidence
      space d fuel es type_ inputBindings finalResult gt prev counter) :
    MettaCall space d (.expression es) type_ inputBindings finalResult :=
  HEVisibleEquationQueryEvidence.models_mettaCall h.he

theorem engine_mettaCall_sound_of_visibleEquationQueryEvidence
    (engine : HEOperationalEngine)
    (h_evidence :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (fuel : Nat) (es : List Atom) (type_ : Atom)
        (b : Bindings) (r : ResultPair),
        engine.mettaCallStep space dispatch (.expression es) type_ b fuel r →
          HEVisibleEquationQueryEvidence
            space dispatch fuel es type_ b r) :
    ∀ (space : Space) (dispatch : GroundedDispatch)
      (fuel : Nat) (es : List Atom) (type_ : Atom)
      (b : Bindings) (r : ResultPair),
      engine.mettaCallStep space dispatch (.expression es) type_ b fuel r →
        MettaCall space dispatch (.expression es) type_ b r := by
  intro space dispatch fuel es type_ b r hstep
  exact HEVisibleEquationQueryEvidence.models_mettaCall
    (h_evidence space dispatch fuel es type_ b r hstep)

theorem engine_mettaCall_sound_of_leattaVisibleEquationQueryEvidence
    (engine : HEOperationalEngine)
    (h_evidence :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (fuel : Nat) (es : List Atom) (type_ : Atom)
        (b : Bindings) (r : ResultPair),
        engine.mettaCallStep space dispatch (.expression es) type_ b fuel r →
          Sigma fun gt : Metta.GroundingTable =>
          Sigma fun prev : Metta.Minimal.Stack =>
          Sigma fun counter : Nat =>
            LeaTTaVisibleEquationQueryEvidence
              space dispatch fuel es type_ b r gt prev counter) :
    ∀ (space : Space) (dispatch : GroundedDispatch)
      (fuel : Nat) (es : List Atom) (type_ : Atom)
      (b : Bindings) (r : ResultPair),
      engine.mettaCallStep space dispatch (.expression es) type_ b fuel r →
        MettaCall space dispatch (.expression es) type_ b r := by
  intro space dispatch fuel es type_ b r hstep
  rcases h_evidence space dispatch fuel es type_ b r hstep with
    ⟨gt, prev, counter, hev⟩
  exact LeaTTaVisibleEquationQueryEvidence.models_mettaCall hev

/-! ### LeaTTa visible equation-query evidence fragment

This fragment is narrower than `leattaEquationFragmentEngine`: its executable
call surface is exactly the repaired visible equation-query path, with public
and visible HE query premises present in the observation. -/

def LeaTTaVisibleEquationQueryOpMettaCallStep
    (space : Space) (d : GroundedDispatch) (fuel : Nat)
    (atom type_ : Atom) (inputBindings : Bindings)
    (finalResult : ResultPair) : Prop :=
  ∃ (es : List Atom) (rhs : Atom) (qb merged : Bindings)
    (gt : Metta.GroundingTable) (prev : Metta.Minimal.Stack)
    (counter : Nat),
    atom = .expression es ∧
    ¬ SpecialFormHead (.expression es) ∧
    isErrorAtom (.expression es) = false ∧
    HeadNotExecutable d (.expression es) ∧
    (rhs, qb) ∈ queryEquationsAgainstVisible space (.expression es) fuel ∧
    (rhs, qb) ∈ queryEquations space (.expression es) fuel ∧
    LeaTTaBridge.LeaTTaEquationQueryOpHit
      space fuel (.expression es) (qb.applyFull rhs fuel) gt prev counter ∧
    merged ∈ mergeBindings qb inputBindings fuel ∧
    merged.hasLoop = false ∧
    EvalAtom space d (merged.applyFull rhs fuel) type_ merged finalResult

theorem leattaVisibleEquationQueryOpMettaCallStep_sound
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {atom type_ : Atom} {inputBindings : Bindings}
    {finalResult : ResultPair}
    (hstep :
      LeaTTaVisibleEquationQueryOpMettaCallStep
        space d fuel atom type_ inputBindings finalResult) :
    MettaCall space d atom type_ inputBindings finalResult := by
  rcases hstep with
    ⟨es, rhs, qb, merged, gt, prev, counter, h_atom, _h_not_special,
      h_not_error, h_not_grounded, h_query_visible, h_query_public,
      hhit, h_merge, h_no_loop, h_recurse⟩
  subst atom
  exact
    LeaTTaVisibleEquationQueryEvidence.models_mettaCall
      (leattaVisibleEquationQueryEvidence_of_queryOp_hit
        (space := space)
        (d := d)
        (fuel := fuel)
        (es := es)
        (rhs := rhs)
        (type_ := type_)
        (qb := qb)
        (inputBindings := inputBindings)
        (merged := merged)
        (gt := gt)
        (prev := prev)
        (counter := counter)
        (finalResult := finalResult)
        h_not_error h_not_grounded h_query_visible h_query_public
        hhit h_merge h_no_loop h_recurse)

def leattaVisibleEquationQueryOpFragmentEngine : HEOperationalEngine where
  evalAtomStep := fun space dispatch atom type_ b _fuel r =>
    EvalAtom space dispatch atom type_ b r
  mettaCallStep := fun space dispatch atom type_ b fuel r =>
    LeaTTaVisibleEquationQueryOpMettaCallStep
      space dispatch fuel atom type_ b r
theorem leattaVisibleEquationQueryOpFragmentEngine_bridge :
    HEEngineBridge leattaVisibleEquationQueryOpFragmentEngine where
  evalAtom_sound := by
    intro space dispatch atom type_ b fuel r hstep
    simpa [leattaVisibleEquationQueryOpFragmentEngine] using hstep
  mettaCall_sound := by
    intro space dispatch atom type_ b fuel r hstep
    exact leattaVisibleEquationQueryOpMettaCallStep_sound hstep
theorem leattaVisibleEquationQueryOpFragmentEngine_models_declarative_he :
    HEEngineModelsDeclarativeSpec leattaVisibleEquationQueryOpFragmentEngine :=
  engine_parametric_he_refinement
    leattaVisibleEquationQueryOpFragmentEngine
    leattaVisibleEquationQueryOpFragmentEngine_bridge

/-! ### LeaTTa repaired query/extensional-unify fragment

This is the widest currently proved call fragment that keeps the repaired
equation-query path explicit: `Error` passthrough is carried by the HE
surface rule and checked against LeaTTa's executable translation above,
equation hits must come through the visible `matchAtoms`-backed query evidence
above, no-match stays the official empty public-query branch, and primitive
`unify` uses the lookup-extensional executable binding observation from
`LeaTTaBridge`. -/

def LeaTTaErrorPassthroughMettaCallStep
    (_space : Space) (_d : GroundedDispatch) (_fuel : Nat)
    (atom : Atom) (_type_ : Atom) (inputBindings : Bindings)
    (result : ResultPair) : Prop :=
  ∃ src msg,
    atom = Atom.error src msg ∧
    result = (Atom.error src msg, inputBindings) ∧
    LeaTTaBridge.toLeaTTaAtom atom =
      Metta.Atom.expr
        [Metta.Atom.sym "Error",
          LeaTTaBridge.toLeaTTaAtom src,
          LeaTTaBridge.toLeaTTaAtom msg]

theorem leattaErrorPassthroughMettaCallStep_sound
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {atom type_ : Atom} {inputBindings : Bindings}
    {result : ResultPair}
    (hstep :
      LeaTTaErrorPassthroughMettaCallStep
        space d fuel atom type_ inputBindings result) :
    MettaCall space d atom type_ inputBindings result := by
  rcases hstep with ⟨src, msg, h_atom, h_result, _h_translate⟩
  subst atom
  subst result
  exact MettaCall.error_passthrough _ _ _ rfl

def LeaTTaRepairedQueryUnifyExtMettaCallStep
    (space : Space) (d : GroundedDispatch) (fuel : Nat)
    (atom type_ : Atom) (inputBindings : Bindings)
    (result : ResultPair) : Prop :=
  LeaTTaErrorPassthroughMettaCallStep
      space d fuel atom type_ inputBindings result ∨
  LeaTTaVisibleEquationQueryOpMettaCallStep
      space d fuel atom type_ inputBindings result ∨
  LeaTTaBridge.LeaTTaNoMatchMettaCallStep
      space d fuel atom type_ inputBindings result ∨
  LeaTTaBridge.LeaTTaUnifyMettaCallStepExt
      space d fuel atom type_ inputBindings result

theorem leattaRepairedQueryUnifyExtMettaCallStep_sound
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {atom type_ : Atom} {inputBindings : Bindings}
    {result : ResultPair}
    (hstep :
      LeaTTaRepairedQueryUnifyExtMettaCallStep
        space d fuel atom type_ inputBindings result) :
    MettaCall space d atom type_ inputBindings result := by
  rcases hstep with herr | hrest
  · exact leattaErrorPassthroughMettaCallStep_sound herr
  rcases hrest with hvisible | hrest
  · exact leattaVisibleEquationQueryOpMettaCallStep_sound hvisible
  rcases hrest with hno | hunify
  · exact LeaTTaBridge.leattaNoMatchMettaCallStep_sound hno
  · exact LeaTTaBridge.leattaUnifyMettaCallStepExt_sound hunify

/-- Any engine whose call surface refines the repaired LeaTTa-backed
error/query/no-match/extensional-`unify` fragment satisfies the corresponding
declarative HE `MettaCall` obligation. -/
theorem leattaRepairedQueryUnifyExtFragment_mettaCall_sound
    (engine : HEOperationalEngine)
    (h_refines :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.mettaCallStep space dispatch atom type_ b fuel r →
          LeaTTaRepairedQueryUnifyExtMettaCallStep
            space dispatch fuel atom type_ b r) :
    ∀ (space : Space) (dispatch : GroundedDispatch)
      (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
      engine.mettaCallStep space dispatch atom type_ b fuel r →
        MettaCall space dispatch atom type_ b r := by
  intro space dispatch atom type_ b fuel r hstep
  exact leattaRepairedQueryUnifyExtMettaCallStep_sound
    (h_refines space dispatch atom type_ b fuel r hstep)

/-- Assemble a full engine bridge from explicit non-call obligations plus a
proof that the engine's call surface refines the repaired LeaTTa-backed
error/query/no-match/extensional-`unify` fragment. -/
theorem engine_bridge_of_leattaRepairedQueryUnifyExtFragment_mettaCall
    (engine : HEOperationalEngine)
    (h_eval :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.evalAtomStep space dispatch atom type_ b fuel r →
          EvalAtom space dispatch atom type_ b r)
    (h_metta_refines :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.mettaCallStep space dispatch atom type_ b fuel r →
          LeaTTaRepairedQueryUnifyExtMettaCallStep
            space dispatch fuel atom type_ b r) :
    HEEngineBridge engine where
  evalAtom_sound := h_eval
  mettaCall_sound :=
    leattaRepairedQueryUnifyExtFragment_mettaCall_sound engine h_metta_refines
/-- Engine-parametric declarative HE model theorem for any engine whose
`mettaCallStep` surface is proven to refine the repaired LeaTTa-backed
error/query/no-match/extensional-`unify` fragment. -/
theorem engine_models_declarative_he_of_leattaRepairedQueryUnifyExtFragment_mettaCall
    (engine : HEOperationalEngine)
    (h_eval :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.evalAtomStep space dispatch atom type_ b fuel r →
          EvalAtom space dispatch atom type_ b r)
    (h_metta_refines :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.mettaCallStep space dispatch atom type_ b fuel r →
          LeaTTaRepairedQueryUnifyExtMettaCallStep
            space dispatch fuel atom type_ b r) :
    HEEngineModelsDeclarativeSpec engine :=
  engine_parametric_he_refinement engine
    (engine_bridge_of_leattaRepairedQueryUnifyExtFragment_mettaCall
      engine h_eval h_metta_refines)

def leattaRepairedQueryUnifyExtFragmentEngine : HEOperationalEngine where
  evalAtomStep := fun space dispatch atom type_ b _fuel r =>
    EvalAtom space dispatch atom type_ b r
  mettaCallStep := fun space dispatch atom type_ b fuel r =>
    LeaTTaRepairedQueryUnifyExtMettaCallStep
      space dispatch fuel atom type_ b r
theorem leattaRepairedQueryUnifyExtFragmentEngine_bridge :
    HEEngineBridge leattaRepairedQueryUnifyExtFragmentEngine where
  evalAtom_sound := by
    intro space dispatch atom type_ b fuel r hstep
    simpa [leattaRepairedQueryUnifyExtFragmentEngine] using hstep
  mettaCall_sound := by
    intro space dispatch atom type_ b fuel r hstep
    exact leattaRepairedQueryUnifyExtMettaCallStep_sound hstep
theorem leattaRepairedQueryUnifyExtFragmentEngine_models_declarative_he :
    HEEngineModelsDeclarativeSpec leattaRepairedQueryUnifyExtFragmentEngine :=
  engine_parametric_he_refinement
    leattaRepairedQueryUnifyExtFragmentEngine
    leattaRepairedQueryUnifyExtFragmentEngine_bridge

/-- Concrete no-match readout through the repaired query/extensional-unify
fragment. -/
theorem emptySpace_foo_repairedQueryUnifyExtFragment_models_mettaCall :
    MettaCall Space.empty GroundedDispatch.none
      (.expression [.symbol "foo"]) Atom.undefinedType Bindings.empty
      (.expression [.symbol "foo"], Bindings.empty) :=
  leattaRepairedQueryUnifyExtFragmentEngine_models_declarative_he.mettaCall_models
    Space.empty GroundedDispatch.none
    (.expression [.symbol "foo"]) Atom.undefinedType Bindings.empty 10
    (.expression [.symbol "foo"], Bindings.empty)
    (Or.inr (Or.inr
      (Or.inl LeaTTaBridge.emptySpace_foo_noMatchMettaCallStep_counter0)))

/-- Concrete extensional-`unify` readout through the repaired
query/extensional-unify fragment. -/
theorem seededUnifyOrder_repairedQueryUnifyExtFragment_models_mettaCall :
    MettaCall Space.empty GroundedDispatch.none
      (.expression [.symbol "unify", .symbol "a", .var "x",
        .var "x", .symbol "else"])
      Atom.undefinedType LeaTTaBridge.seededUnifyOrderSeed
      (.symbol "a", LeaTTaBridge.seededUnifyOrderHEMerged) :=
  leattaRepairedQueryUnifyExtFragmentEngine_models_declarative_he.mettaCall_models
    Space.empty GroundedDispatch.none
    (.expression [.symbol "unify", .symbol "a", .var "x",
      .var "x", .symbol "else"])
    Atom.undefinedType LeaTTaBridge.seededUnifyOrderSeed 10
    (.symbol "a", LeaTTaBridge.seededUnifyOrderHEMerged)
    (Or.inr (Or.inr (Or.inr
      LeaTTaBridge.seededUnifyOrder_leattaUnifyMettaCallStepExt_counter0)))

/-- Concrete `Error` passthrough through the repaired query/extensional-unify
fragment, paired with the executable LeaTTa minimal readout for the translated
atom. -/
theorem leatta_minimal_error_passthrough_repairedQueryUnifyExtFragment_models_mettaCall :
    Metta.Minimal.mettaEval (Metta.Minimal.MinEnv.ofAtomsGT [] []) 4
      Metta.Minimal.St.init [] leattaErrorPassthroughAtom =
        ([(leattaErrorPassthroughAtom, [])], Metta.Minimal.St.init) ∧
    MettaCall Space.empty GroundedDispatch.none
      (Atom.error (.symbol "x") (.symbol "e")) Atom.undefinedType Bindings.empty
      (Atom.error (.symbol "x") (.symbol "e"), Bindings.empty) := by
  constructor
  · exact leatta_minimal_error_passthrough_mettaEval
  · exact
      leattaRepairedQueryUnifyExtFragmentEngine_models_declarative_he.mettaCall_models
        Space.empty GroundedDispatch.none
        (Atom.error (.symbol "x") (.symbol "e")) Atom.undefinedType Bindings.empty 10
        (Atom.error (.symbol "x") (.symbol "e"), Bindings.empty)
        (Or.inl
          ⟨.symbol "x", .symbol "e", rfl, rfl,
            leatta_error_passthrough_atom_is_HE_error_translation⟩)

/-! ### Repaired query/unify fragment plus malformed-`unify` surface

This super-fragment keeps the repaired query/extensional-`unify` bridge intact
and adds the subject-side malformed-`unify` observation repaired above. -/

def LeaTTaRepairedQueryUnifyExtBadArityMettaCallStep
    (space : Space) (d : GroundedDispatch) (fuel : Nat)
    (atom type_ : Atom) (inputBindings : Bindings)
    (result : ResultPair) : Prop :=
  LeaTTaRepairedQueryUnifyExtMettaCallStep
    space d fuel atom type_ inputBindings result ∨
  LeaTTaUnifyBadArityMettaCallStep
    space d fuel atom type_ inputBindings result ∨
  LeaTTaBridge.LeaTTaEquationMettaCallStep
    space d fuel atom type_ inputBindings result

theorem leattaRepairedQueryUnifyExtBadArityMettaCallStep_sound
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {atom type_ : Atom} {inputBindings : Bindings}
    {result : ResultPair}
    (hstep :
      LeaTTaRepairedQueryUnifyExtBadArityMettaCallStep
        space d fuel atom type_ inputBindings result) :
    MettaCall space d atom type_ inputBindings result := by
  rcases hstep with hbase | hrest
  · exact leattaRepairedQueryUnifyExtMettaCallStep_sound hbase
  rcases hrest with hbad | heq
  · exact leattaUnifyBadArityMettaCallStep_sound hbad
  · exact LeaTTaBridge.leattaEquationMettaCallStep_sound heq

/-- Any engine whose call surface refines the repaired query/extensional-`unify`
fragment plus the malformed-`unify` executable observation satisfies the
corresponding declarative HE `MettaCall` obligation. -/
theorem leattaRepairedQueryUnifyExtBadArityFragment_mettaCall_sound
    (engine : HEOperationalEngine)
    (h_refines :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.mettaCallStep space dispatch atom type_ b fuel r →
          LeaTTaRepairedQueryUnifyExtBadArityMettaCallStep
            space dispatch fuel atom type_ b r) :
    ∀ (space : Space) (dispatch : GroundedDispatch)
      (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
      engine.mettaCallStep space dispatch atom type_ b fuel r →
        MettaCall space dispatch atom type_ b r := by
  intro space dispatch atom type_ b fuel r hstep
  exact leattaRepairedQueryUnifyExtBadArityMettaCallStep_sound
    (h_refines space dispatch atom type_ b fuel r hstep)

theorem engine_bridge_of_leattaRepairedQueryUnifyExtBadArityFragment_mettaCall
    (engine : HEOperationalEngine)
    (h_eval :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.evalAtomStep space dispatch atom type_ b fuel r →
          EvalAtom space dispatch atom type_ b r)
    (h_metta_refines :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.mettaCallStep space dispatch atom type_ b fuel r →
          LeaTTaRepairedQueryUnifyExtBadArityMettaCallStep
            space dispatch fuel atom type_ b r) :
    HEEngineBridge engine where
  evalAtom_sound := h_eval
  mettaCall_sound :=
    leattaRepairedQueryUnifyExtBadArityFragment_mettaCall_sound
      engine h_metta_refines
theorem engine_models_declarative_he_of_leattaRepairedQueryUnifyExtBadArityFragment_mettaCall
    (engine : HEOperationalEngine)
    (h_eval :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.evalAtomStep space dispatch atom type_ b fuel r →
          EvalAtom space dispatch atom type_ b r)
    (h_metta_refines :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.mettaCallStep space dispatch atom type_ b fuel r →
          LeaTTaRepairedQueryUnifyExtBadArityMettaCallStep
            space dispatch fuel atom type_ b r) :
    HEEngineModelsDeclarativeSpec engine :=
  engine_parametric_he_refinement engine
    (engine_bridge_of_leattaRepairedQueryUnifyExtBadArityFragment_mettaCall
      engine h_eval h_metta_refines)

def leattaRepairedQueryUnifyExtBadArityFragmentEngine : HEOperationalEngine where
  evalAtomStep := fun space dispatch atom type_ b _fuel r =>
    EvalAtom space dispatch atom type_ b r
  mettaCallStep := fun space dispatch atom type_ b fuel r =>
    LeaTTaRepairedQueryUnifyExtBadArityMettaCallStep
      space dispatch fuel atom type_ b r
theorem leattaRepairedQueryUnifyExtBadArityFragmentEngine_bridge :
    HEEngineBridge leattaRepairedQueryUnifyExtBadArityFragmentEngine where
  evalAtom_sound := by
    intro space dispatch atom type_ b fuel r hstep
    simpa [leattaRepairedQueryUnifyExtBadArityFragmentEngine] using hstep
  mettaCall_sound := by
    intro space dispatch atom type_ b fuel r hstep
    exact leattaRepairedQueryUnifyExtBadArityMettaCallStep_sound hstep
theorem leattaRepairedQueryUnifyExtBadArityFragmentEngine_models_declarative_he :
    HEEngineModelsDeclarativeSpec
      leattaRepairedQueryUnifyExtBadArityFragmentEngine :=
  engine_parametric_he_refinement
    leattaRepairedQueryUnifyExtBadArityFragmentEngine
    leattaRepairedQueryUnifyExtBadArityFragmentEngine_bridge

/-- The bad-arity-inclusive repaired fragment subsumes the previous repaired
query/extensional-`unify` fragment. -/
theorem leattaRepairedQueryUnifyExt_step_subsumed_by_badArityFragment
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {atom type_ : Atom} {inputBindings : Bindings}
    {result : ResultPair}
    (hstep :
      LeaTTaRepairedQueryUnifyExtMettaCallStep
        space d fuel atom type_ inputBindings result) :
    LeaTTaRepairedQueryUnifyExtBadArityMettaCallStep
        space d fuel atom type_ inputBindings result :=
  Or.inl hstep

/-- The bad-arity-inclusive repaired fragment also subsumes the general
LeaTTa equation-call step.  This is the migration path away from the separate
equation fragment engine. -/
theorem leattaEquationStep_subsumed_by_badArityFragment
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {atom type_ : Atom} {inputBindings : Bindings}
    {result : ResultPair}
    (hstep :
      LeaTTaBridge.LeaTTaEquationMettaCallStep
        space d fuel atom type_ inputBindings result) :
    LeaTTaRepairedQueryUnifyExtBadArityMettaCallStep
        space d fuel atom type_ inputBindings result :=
  Or.inr (Or.inr hstep)

/-- The older repaired fragment engine is justified through the stronger
bad-arity-inclusive bridge, giving a migration path for downstream readouts
while fragment engines are consolidated. -/
theorem leattaRepairedQueryUnifyExtFragmentEngine_models_declarative_he_via_badArityFragment :
    HEEngineModelsDeclarativeSpec leattaRepairedQueryUnifyExtFragmentEngine :=
  engine_models_declarative_he_of_leattaRepairedQueryUnifyExtBadArityFragment_mettaCall
    leattaRepairedQueryUnifyExtFragmentEngine
    (by
      intro space dispatch atom type_ b fuel r hstep
      simpa [leattaRepairedQueryUnifyExtFragmentEngine] using hstep)
    (by
      intro space dispatch atom type_ b fuel r hstep
      exact
        leattaRepairedQueryUnifyExt_step_subsumed_by_badArityFragment
          (by
            simpa [leattaRepairedQueryUnifyExtFragmentEngine] using hstep))
/-- The older equation fragment engine is justified through the stronger
bad-arity-inclusive bridge. -/
theorem leattaEquationFragmentEngine_models_declarative_he_via_badArityFragment :
    HEEngineModelsDeclarativeSpec leattaEquationFragmentEngine :=
  engine_models_declarative_he_of_leattaRepairedQueryUnifyExtBadArityFragment_mettaCall
    leattaEquationFragmentEngine
    (by
      intro space dispatch atom type_ b fuel r hstep
      simpa [leattaEquationFragmentEngine] using hstep)
    (by
      intro space dispatch atom type_ b fuel r hstep
      exact
        leattaEquationStep_subsumed_by_badArityFragment
          (by
            simpa [leattaEquationFragmentEngine] using hstep))
/-- Concrete no-match readout through the bad-arity-inclusive repaired
fragment. -/
theorem emptySpace_foo_repairedQueryUnifyExtBadArityFragment_models_mettaCall :
    MettaCall Space.empty GroundedDispatch.none
      (.expression [.symbol "foo"]) Atom.undefinedType Bindings.empty
      (.expression [.symbol "foo"], Bindings.empty) :=
  leattaRepairedQueryUnifyExtBadArityFragmentEngine_models_declarative_he.mettaCall_models
    Space.empty GroundedDispatch.none
    (.expression [.symbol "foo"]) Atom.undefinedType Bindings.empty 10
    (.expression [.symbol "foo"], Bindings.empty)
    (Or.inl (Or.inr (Or.inr
      (Or.inl LeaTTaBridge.emptySpace_foo_noMatchMettaCallStep_counter0))))

/-- Concrete extensional-`unify` readout through the bad-arity-inclusive
repaired fragment. -/
theorem seededUnifyOrder_repairedQueryUnifyExtBadArityFragment_models_mettaCall :
    MettaCall Space.empty GroundedDispatch.none
      (.expression [.symbol "unify", .symbol "a", .var "x",
        .var "x", .symbol "else"])
      Atom.undefinedType LeaTTaBridge.seededUnifyOrderSeed
      (.symbol "a", LeaTTaBridge.seededUnifyOrderHEMerged) :=
  leattaRepairedQueryUnifyExtBadArityFragmentEngine_models_declarative_he.mettaCall_models
    Space.empty GroundedDispatch.none
    (.expression [.symbol "unify", .symbol "a", .var "x",
      .var "x", .symbol "else"])
    Atom.undefinedType LeaTTaBridge.seededUnifyOrderSeed 10
    (.symbol "a", LeaTTaBridge.seededUnifyOrderHEMerged)
    (Or.inl (Or.inr (Or.inr (Or.inr
      LeaTTaBridge.seededUnifyOrder_leattaUnifyMettaCallStepExt_counter0))))

/-- Concrete `Error` passthrough through the bad-arity-inclusive repaired
fragment, paired with the executable LeaTTa minimal readout for the translated
atom. -/
theorem leatta_minimal_error_passthrough_repairedQueryUnifyExtBadArityFragment_models_mettaCall :
    Metta.Minimal.mettaEval (Metta.Minimal.MinEnv.ofAtomsGT [] []) 4
      Metta.Minimal.St.init [] leattaErrorPassthroughAtom =
        ([(leattaErrorPassthroughAtom, [])], Metta.Minimal.St.init) ∧
    MettaCall Space.empty GroundedDispatch.none
      (Atom.error (.symbol "x") (.symbol "e")) Atom.undefinedType Bindings.empty
      (Atom.error (.symbol "x") (.symbol "e"), Bindings.empty) := by
  constructor
  · exact leatta_minimal_error_passthrough_mettaEval
  · exact
      leattaRepairedQueryUnifyExtBadArityFragmentEngine_models_declarative_he.mettaCall_models
        Space.empty GroundedDispatch.none
        (Atom.error (.symbol "x") (.symbol "e")) Atom.undefinedType Bindings.empty 10
        (Atom.error (.symbol "x") (.symbol "e"), Bindings.empty)
        (Or.inl (Or.inl
          ⟨.symbol "x", .symbol "e", rfl, rfl,
            leatta_error_passthrough_atom_is_HE_error_translation⟩))

/-- Concrete equality-bearing chain-resolution readout through the
bad-arity-inclusive repaired fragment, subsuming the older equation-fragment
readout. -/
theorem chainResolveBoundary_badArityFragment_models_mettaCall_counter0 :
    MettaCall
      (Space.ofList
        [.expression
          [.symbol "=",
            .expression [.symbol "f", .var "x", .var "y"],
            .var "x"]])
      GroundedDispatch.none
      (.expression [.symbol "f", .var "y#1", .symbol "a"])
      Atom.undefinedType Bindings.empty
      (.symbol "a",
        ({ assignments := [("y#1", .symbol "a")]
         , equalities := [("y#1", "x#0")] } : Bindings)) :=
  leattaRepairedQueryUnifyExtBadArityFragmentEngine_models_declarative_he.mettaCall_models
    (Space.ofList
      [.expression
        [.symbol "=",
          .expression [.symbol "f", .var "x", .var "y"],
          .var "x"]])
    GroundedDispatch.none
    (.expression [.symbol "f", .var "y#1", .symbol "a"])
    Atom.undefinedType Bindings.empty 10
    (.symbol "a",
      ({ assignments := [("y#1", .symbol "a")]
       , equalities := [("y#1", "x#0")] } : Bindings))
    (leattaEquationStep_subsumed_by_badArityFragment
      LeaTTaBridge.chainResolveBoundary_leattaEquationMettaCallStep_counter0)

/-- Concrete malformed-`unify` readout through the repaired fragment extended
with the bad-arity subject observation. -/
theorem leatta_minimal_unify_bad_arity_repairedQueryUnifyExtBadArityFragment_models_mettaCall :
    Metta.Minimal.evalAtomMin
        (Metta.Minimal.MinEnv.ofAtomsGT [] []) 4
        leattaBadUnifyThreeArgs =
      [LeaTTaBridge.toLeaTTaAtom
        (mkUnifyBadArityError heBadUnifyThreeArgs)] ∧
    MettaCall Space.empty GroundedDispatch.none
      heBadUnifyThreeArgs Atom.undefinedType Bindings.empty
      (mkUnifyBadArityError heBadUnifyThreeArgs, Bindings.empty) := by
  constructor
  · exact leatta_minimal_unify_bad_arity_matches_HE_bad_arity_surface.1
  · exact
      leattaRepairedQueryUnifyExtBadArityFragmentEngine_models_declarative_he.mettaCall_models
        Space.empty GroundedDispatch.none
        heBadUnifyThreeArgs Atom.undefinedType Bindings.empty 4
        (mkUnifyBadArityError heBadUnifyThreeArgs, Bindings.empty)
        (Or.inr
          (Or.inl
            leattaBadUnifyThreeArgs_unifyBadArityMettaCallStep_counter4))

/-- Transport-backed conformance through the concrete `queryOp` hit boundary.
This theorem makes explicit that the older avoid-aware transport certificate is
now only one way to produce the executable hit consumed by the smaller bridge. -/
theorem leattaTransportAgainstVisibleWithMerge_models_mettaCall_final_via_queryOpHit
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {rhs type_ : Atom}
    {qb inputBindings merged : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat} {k : String} {finalResult : ResultPair}
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_error : isErrorAtom (.expression es) = false)
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (hk : Metta.Minimal.headKey
      (LeaTTaBridge.toLeaTTaAtom (.expression es)) = some k)
    (h_query_visible : (rhs, qb) ∈
      queryEquationsAgainstVisible space (.expression es) fuel)
    (h_query_public : (rhs, qb) ∈
      queryEquations space (.expression es) fuel)
    (htransport : LeaTTaBridge.EquationMatchVisibleItemTransportAgainst
      space (.expression es) rhs qb fuel gt prev counter)
    (h_merge : merged ∈ mergeBindings qb inputBindings fuel)
    (h_no_loop : merged.hasLoop = false)
    (h_recurse :
      EvalAtom space d (merged.applyFull rhs fuel) type_ merged finalResult) :
    MettaCall space d (.expression es) type_ inputBindings finalResult := by
  exact
    leattaRepairedQueryUnifyExtBadArityFragmentEngine_models_declarative_he.mettaCall_models
      space d (.expression es) type_ inputBindings fuel finalResult
      (leattaEquationStep_subsumed_by_badArityFragment
        (LeaTTaBridge.leattaEquationMettaCallStep_of_transport_againstVisible_with_merge_final
          (space := space)
          (d := d)
          (fuel := fuel)
          (es := es)
          (rhs := rhs)
          (type_ := type_)
          (qb := qb)
          (inputBindings := inputBindings)
          (merged := merged)
          (gt := gt)
          (prev := prev)
          (counter := counter)
          (k := k)
          (finalResult := finalResult)
          h_not_special h_not_error h_not_grounded hk h_query_visible
          h_query_public htransport h_merge h_no_loop h_recurse))

/-- Conformance schema through the smaller local freshened-item transport
boundary. Candidate selection is discharged from the HE visible query witness;
the supplied obligation is only the single-candidate LeaTTa freshening,
matching, merge, loop-filter, instantiation, and alpha-agreement step. -/
theorem leattaFreshenedItemTransportAgainstVisibleWithMerge_models_mettaCall_final
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {rhs type_ : Atom}
    {qb inputBindings merged : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat} {k : String} {finalResult : ResultPair}
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_error : isErrorAtom (.expression es) = false)
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (hk : Metta.Minimal.headKey
      (LeaTTaBridge.toLeaTTaAtom (.expression es)) = some k)
    (h_query_visible : (rhs, qb) ∈
      queryEquationsAgainstVisible space (.expression es) fuel)
    (h_query_public : (rhs, qb) ∈
      queryEquations space (.expression es) fuel)
    (hitemTransport :
      LeaTTaBridge.FreshenedQueryOpItemTransportAgainstVisible
        space (.expression es) rhs qb fuel gt prev counter)
    (h_merge : merged ∈ mergeBindings qb inputBindings fuel)
    (h_no_loop : merged.hasLoop = false)
    (h_recurse :
      EvalAtom space d (merged.applyFull rhs fuel) type_ merged finalResult) :
    MettaCall space d (.expression es) type_ inputBindings finalResult := by
  exact
    leattaRepairedQueryUnifyExtBadArityFragmentEngine_models_declarative_he.mettaCall_models
      space d (.expression es) type_ inputBindings fuel finalResult
      (leattaEquationStep_subsumed_by_badArityFragment
        (LeaTTaBridge.leattaEquationMettaCallStep_of_freshened_item_transport_againstVisible_with_merge_final
          (space := space)
          (d := d)
          (fuel := fuel)
          (es := es)
          (rhs := rhs)
          (type_ := type_)
          (qb := qb)
          (inputBindings := inputBindings)
          (merged := merged)
          (gt := gt)
          (prev := prev)
          (counter := counter)
          (k := k)
          (finalResult := finalResult)
          h_not_special h_not_error h_not_grounded hk h_query_visible
          h_query_public hitemTransport h_merge h_no_loop h_recurse))

/-- Variable-successor specialization of the freshened-item conformance schema.
The caller proves only that the executable local item emits a variable and the
HE visible successor is a variable; the bridge supplies the alpha-equivalence
needed by the official `MettaCall` conclusion. -/
theorem leattaFreshenedVariableItemTransportAgainstVisibleWithMerge_models_mettaCall_final
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {rhs type_ : Atom}
    {qb inputBindings merged : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat} {k : String} {finalResult : ResultPair}
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_error : isErrorAtom (.expression es) = false)
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (hk : Metta.Minimal.headKey
      (LeaTTaBridge.toLeaTTaAtom (.expression es)) = some k)
    (h_query_visible : (rhs, qb) ∈
      queryEquationsAgainstVisible space (.expression es) fuel)
    (h_query_public : (rhs, qb) ∈
      queryEquations space (.expression es) fuel)
    (hvarTransport :
      LeaTTaBridge.FreshenedVariableQueryOpItemTransportAgainstVisible
        space (.expression es) rhs qb fuel gt prev counter)
    (h_merge : merged ∈ mergeBindings qb inputBindings fuel)
    (h_no_loop : merged.hasLoop = false)
    (h_recurse :
      EvalAtom space d (merged.applyFull rhs fuel) type_ merged finalResult) :
    MettaCall space d (.expression es) type_ inputBindings finalResult := by
  exact
    leattaRepairedQueryUnifyExtBadArityFragmentEngine_models_declarative_he.mettaCall_models
      space d (.expression es) type_ inputBindings fuel finalResult
      (leattaEquationStep_subsumed_by_badArityFragment
        (LeaTTaBridge.leattaEquationMettaCallStep_of_freshened_variable_item_transport_againstVisible_with_merge_final
          (space := space)
          (d := d)
          (fuel := fuel)
          (es := es)
          (rhs := rhs)
          (type_ := type_)
          (qb := qb)
          (inputBindings := inputBindings)
          (merged := merged)
          (gt := gt)
          (prev := prev)
          (counter := counter)
          (k := k)
          (finalResult := finalResult)
          h_not_special h_not_error h_not_grounded hk h_query_visible
          h_query_public hvarTransport h_merge h_no_loop h_recurse))

/-- Concrete equality-bearing query readout through the engine-parametric
LeaTTa equation fragment.  This is the repaired path for the chain-resolution
boundary where HE's visible query surface preserves an equality relation that
the assignment-only instantiated-item shortcut cannot carry. -/
theorem chainResolveBoundary_equationFragment_models_mettaCall_counter0 :
    MettaCall
      (Space.ofList
        [.expression
          [.symbol "=",
            .expression [.symbol "f", .var "x", .var "y"],
            .var "x"]])
      GroundedDispatch.none
      (.expression [.symbol "f", .var "y#1", .symbol "a"])
      Atom.undefinedType Bindings.empty
      (.symbol "a",
        ({ assignments := [("y#1", .symbol "a")]
         , equalities := [("y#1", "x#0")] } : Bindings)) :=
  chainResolveBoundary_badArityFragment_models_mettaCall_counter0

/-- Negative companion for the equality-bearing query boundary: there is a
faithful visible-query hit whose expected instantiated item is absent from the
assignment-only shortcut's `queryOp` target. -/
theorem equalityBearing_query_hit_not_carried_by_instantiated_item_shortcut :
    ∃ (space : Space) (src rhs : Atom) (qb : Bindings)
      (fuel counter : Nat) (gt : Metta.GroundingTable),
      (rhs, qb) ∈ queryEquationsAgainstVisible space src fuel ∧
      LeaTTaBridge.NoVarAssignmentValues qb ∧
      LeaTTaBridge.AssignmentsNodup qb ∧
      LeaTTaBridge.atomDepth rhs + 2 ≤ fuel ∧
      Metta.Minimal.evalResult []
          (Metta.instantiate (LeaTTaBridge.toLeaTTaMatchBindings qb)
            (LeaTTaBridge.toLeaTTaAtom rhs))
          (LeaTTaBridge.toLeaTTaMatchBindings qb) ∉
        (Metta.Minimal.queryOp
          (Metta.Minimal.MinEnv.ofAtomsGT
            (LeaTTaBridge.toLeaTTaAtoms space.atoms) gt)
          { counter := counter, world := Metta.Minimal.World.empty }
          [] (LeaTTaBridge.toLeaTTaAtom src) Metta.Bindings.empty).1 :=
  LeaTTaBridge.exists_visible_query_hit_not_carried_by_instantiated_item_shortcut

/-- Generic conformance schema for the no-variable-values instantiated-RHS
equation fragment.  It exposes the reusable bridge behind the unary-identity
fixture: once the repaired visible query, public HE query, LeaTTa `queryOp` item,
and recursive `EvalAtom` premise are supplied, the official declarative HE
`MettaCall` result follows. -/
theorem leattaInstantiatedEquationFragment_models_mettaCall
    {space : Space} {d : GroundedDispatch} {n : Nat}
    {es : List Atom} {rhs type_ : Atom} {qb outputBindings : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat}
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_error : isErrorAtom (.expression es) = false)
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (h_query_visible : (rhs, qb) ∈
      queryEquationsAgainstVisible space (.expression es) (n + 1))
    (h_query_public : (rhs, qb) ∈
      queryEquations space (.expression es) (n + 1))
    (heq : qb.equalities = [])
    (hfresh : ValueKeysFreshForValues (LeaTTaBridge.toLeaTTaMatchBindings qb))
    (hdepth : LeaTTaBridge.atomDepth rhs + 2 ≤ n + 1)
    (hitem :
      Metta.Minimal.evalResult prev
          (Metta.instantiate (LeaTTaBridge.toLeaTTaMatchBindings qb)
            (LeaTTaBridge.toLeaTTaAtom rhs))
          (LeaTTaBridge.toLeaTTaMatchBindings qb) ∈
        (Metta.Minimal.queryOp
          (Metta.Minimal.MinEnv.ofAtomsGT
            (LeaTTaBridge.toLeaTTaAtoms space.atoms) gt)
          { counter := counter, world := Metta.Minimal.World.empty }
          prev (LeaTTaBridge.toLeaTTaAtom (.expression es))
          Metta.Bindings.empty).1)
    (h_recurse :
      EvalAtom space d (qb.applyFull rhs (n + 1)) type_ qb
        (qb.applyFull rhs (n + 1), outputBindings)) :
    MettaCall space d (.expression es) type_ Bindings.empty
      (qb.applyFull rhs (n + 1), outputBindings) := by
  exact
    leattaRepairedQueryUnifyExtBadArityFragmentEngine_models_declarative_he.mettaCall_models
      space d (.expression es) type_ Bindings.empty (n + 1)
      (qb.applyFull rhs (n + 1), outputBindings)
      (leattaEquationStep_subsumed_by_badArityFragment
        (LeaTTaBridge.leattaEquationMettaCallStep_of_instantiated_item_againstVisible_empty_input
          (space := space) (d := d) (n := n) (es := es)
          (rhs := rhs) (type_ := type_) (qb := qb)
          (outputBindings := outputBindings) (gt := gt) (prev := prev)
          (counter := counter)
          h_not_special h_not_error h_not_grounded h_query_visible
          h_query_public heq hfresh
          hdepth hitem h_recurse))

/-- Conformance-facing positive fixture for the LeaTTa equation-call fragment:
the arbitrary unary-identity non-ground assignment witness satisfies the
official HE `MettaCall` rule through the step-shaped bridge hook. -/
theorem leattaUnaryIdentityFragment_models_mettaCall
    (head var value : String)
    (h_not_special :
      ¬ SpecialFormHead (.expression [.symbol head, .symbol value]))
    (h_not_error :
      isErrorAtom (.expression [.symbol head, .symbol value]) = false)
    (h_recurse :
      EvalAtom (LeaTTaBridge.unaryIdentitySpace head var) GroundedDispatch.none
        (.symbol value) Atom.undefinedType
        (LeaTTaBridge.unaryIdentityBindings var value)
        (.symbol value, LeaTTaBridge.unaryIdentityBindings var value)) :
    MettaCall (LeaTTaBridge.unaryIdentitySpace head var) GroundedDispatch.none
      (.expression [.symbol head, .symbol value]) Atom.undefinedType
      Bindings.empty (.symbol value, LeaTTaBridge.unaryIdentityBindings var value) := by
  have heq :
      (LeaTTaBridge.unaryIdentityBindings var value).equalities = [] := by
    simp [LeaTTaBridge.unaryIdentityBindings, Bindings.assign, Bindings.empty]
  have hfull :
      (LeaTTaBridge.unaryIdentityBindings var value).applyFull
          (.var (LeaTTaBridge.unaryIdentityFresh0 var)) 10 =
        .symbol value := by
    rw [Bindings.applyFull_no_equalities heq]
    simp [Bindings.apply, Bindings.resolve, Bindings.resolveAtomAux,
      Bindings.hasAssignedVar, LeaTTaBridge.unaryIdentityBindings,
      LeaTTaBridge.unaryIdentityFresh0, Bindings.assign, Bindings.isBound,
      Bindings.empty, Bindings.lookup]
  simpa [hfull] using
    (leattaInstantiatedEquationFragment_models_mettaCall
      (space := LeaTTaBridge.unaryIdentitySpace head var)
      (d := GroundedDispatch.none)
      (n := 9)
      (es := [.symbol head, .symbol value])
      (rhs := .var (LeaTTaBridge.unaryIdentityFresh0 var))
      (type_ := Atom.undefinedType)
      (qb := LeaTTaBridge.unaryIdentityBindings var value)
      (outputBindings := LeaTTaBridge.unaryIdentityBindings var value)
      (gt := (default : Metta.GroundingTable))
      (prev := [])
      (counter := 0)
      h_not_special
      h_not_error
      (by
        simp [HeadNotExecutable, GroundedDispatch.none]
        constructor
        · intro hunify
          apply h_not_special
          simp [SpecialFormHead, hunify]
        · intro hswitch
          apply h_not_special
          simp [SpecialFormHead, hswitch])
      (LeaTTaBridge.queryEquationsAgainstVisible_unaryIdentity_counter0_mem
        head var value)
      (LeaTTaBridge.queryEquations_unaryIdentity_counter0_mem
        head var value)
      heq
      (by
        have htranslated :
            LeaTTaBridge.toLeaTTaMatchBindings
                (LeaTTaBridge.unaryIdentityBindings var value) =
              [Metta.BindingRel.val
                (LeaTTaBridge.unaryIdentityFresh0 var) (Metta.Atom.sym value)] := by
          simp [LeaTTaBridge.toLeaTTaMatchBindings,
            LeaTTaBridge.toLeaTTaMatchSubst,
            LeaTTaBridge.unaryIdentityBindings,
            LeaTTaBridge.unaryIdentityFresh0, Bindings.assign,
            Bindings.isBound, Bindings.lookup, Bindings.empty,
            LeaTTaBridge.toLeaTTaAtom, Metta.Bindings.ofSubst]
        rw [htranslated]
        exact ClosedValueBindings.valueKeysFreshForValues
          (ClosedValueBindings.val (by simp [Metta.Atom.vars])
            ClosedValueBindings.nil))
      (by simp [LeaTTaBridge.atomDepth])
      (LeaTTaBridge.unaryIdentity_instantiated_queryOp_item_counter0
        head var value (default : Metta.GroundingTable))
      (by
        simpa [hfull] using h_recurse))

/-- Stable reachability through the concrete fuel evaluator gives the public
    implementation-refined HE certification boundary. -/
theorem heFuelEvaluatorEngine_stable_evalAtom_models_certified
    (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (r : ResultPair) :
    StableEvalAtomStep heFuelEvaluatorEngine space dispatch atom type_ b r →
      EvalAtomCertified space dispatch atom type_ b r := by
  intro hstable
  exact evalAtomStablyReaches_to_certified space dispatch atom type_ b r
    (by
      simpa [StableEvalAtomStep, heFuelEvaluatorEngine, EvalAtomStablyReaches]
        using hstable)

/-- For the concrete HE fuel evaluator, the engine-parametric stable
`evalAtomStep` surface is exactly the public certified evaluator boundary. -/
theorem heFuelEvaluatorEngine_stable_evalAtom_iff_certified
    (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (r : ResultPair) :
    StableEvalAtomStep heFuelEvaluatorEngine space dispatch atom type_ b r ↔
      EvalAtomCertified space dispatch atom type_ b r := by
  constructor
  · exact heFuelEvaluatorEngine_stable_evalAtom_models_certified
      space dispatch atom type_ b r
  · intro hcert
    rcases hcert.2 with ⟨fuel0, hstable⟩
    refine ⟨fuel0, ?_⟩
    intro fuel hfuel
    simpa [heFuelEvaluatorEngine] using hstable fuel hfuel

/-- Stable reachability through the concrete fuel evaluator's `mettaCall`
    surface gives the internal implementation-refined call certificate. -/
theorem heFuelEvaluatorEngine_stable_mettaCall_models_certified
    (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (r : ResultPair) :
    StableMettaCallStep heFuelEvaluatorEngine space dispatch atom type_ b r →
      Mettapedia.Languages.MeTTa.HE.Internal.MettaCallCertified
        space dispatch atom type_ b r := by
  intro hstable
  refine ⟨?_, ?_⟩
  · exact heFuelEvaluatorEngine_models_declarative_he.stableMettaCall_models
      space dispatch atom type_ b r hstable
  · simpa [StableMettaCallStep, heFuelEvaluatorEngine,
      Mettapedia.Languages.MeTTa.HE.Internal.MettaCallStablyReaches]
      using hstable

/-- For the concrete HE fuel evaluator, the engine-parametric stable
`mettaCallStep` surface is exactly the implementation-refined `MettaCall`
certificate used by the conformance bridge. -/
theorem heFuelEvaluatorEngine_stable_mettaCall_iff_certified
    (space : Space) (dispatch : GroundedDispatch)
    (atom type_ : Atom) (b : Bindings) (r : ResultPair) :
    StableMettaCallStep heFuelEvaluatorEngine space dispatch atom type_ b r ↔
      Mettapedia.Languages.MeTTa.HE.Internal.MettaCallCertified
        space dispatch atom type_ b r := by
  constructor
  · exact heFuelEvaluatorEngine_stable_mettaCall_models_certified
      space dispatch atom type_ b r
  · intro hcert
    rcases hcert.2 with ⟨fuel0, hstable⟩
    refine ⟨fuel0, ?_⟩
    intro fuel hfuel
    simpa [heFuelEvaluatorEngine] using hstable fuel hfuel

/-! ### Metacircular self-interpreter corpus boundary

The finite self-interpreter corpus is not a whole HE engine instance.  The
bridge below records the reusable evidence it does provide: a fuel-bounded
MeTTaIL normalizer run together with its declarative many-step reduction trace.
-/

/-- A certified MeTTaIL normalizer run packages the executable output equality
with the declarative reduction trace guaranteed by `MeTTaIL.eval_sound`. -/
structure MeTTaILCertifiedRun
    (p : MeTTaIL.Presentation) (fuel : Nat) (input output : MeTTaIL.AST) :
    Prop where
  computes : MeTTaIL.eval p fuel input = output
  reduces : MeTTaIL.RewStepMany p input output

/-- Any concrete `MeTTaIL.eval` equality can be upgraded to a certified run
without treating the normalizer output as an oracle. -/
theorem mettaILCertifiedRun_of_eval_eq
    {p : MeTTaIL.Presentation} {fuel : Nat} {input output : MeTTaIL.AST}
    (h : MeTTaIL.eval p fuel input = output) :
    MeTTaILCertifiedRun p fuel input output where
  computes := h
  reduces := by
    rw [← h]
    exact MeTTaIL.eval_sound p fuel input

def selfInterpMatchQueryInput : MeTTaIL.AST :=
  Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.miRun
    Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.rulesMatchQuery
    Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.miMatchQuery
    (Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.fuel 8)

def selfInterpMatchQueryAnswer : MeTTaIL.AST :=
  Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.N
    (Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.S
      (Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.S
        Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.Z))

def selfInterpCorpusOracle : Prop :=
  MeTTaIL.eval
      Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.pMI
      500 selfInterpMatchQueryInput =
    selfInterpMatchQueryAnswer

theorem selfInterp_corpus_oracle : selfInterpCorpusOracle := by
  exact Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.self_match_query_answer

def selfInterpCorpusCertifiedRun : Prop :=
  MeTTaILCertifiedRun
    Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.pMI
    500 selfInterpMatchQueryInput selfInterpMatchQueryAnswer

/-- The metacircular match-query corpus check has a certified MeTTaIL
reduction trace, not just a computed answer equality. -/
theorem selfInterp_corpus_certified_run :
    selfInterpCorpusCertifiedRun := by
  exact
    mettaILCertifiedRun_of_eval_eq
      Mettapedia.Languages.MeTTa.LeaTTa.Corpus.SelfInterp.self_match_query_answer

/-! ## Conformance Summary

| Section | Count | Method |
|---------|-------|--------|
| 1. EvalAtom witnesses | 8 | derivation tree |
| 2. typeCast | 4 | rfl |
| 3. matchTypes | 4 | rfl |
| 4. matchAtoms | 10 | rfl |
| 5. MettaCall witnesses | 4 | derivation tree |
| 6. Equation RHS regression | 2 | derivation tree + rfl |
| 7. MinimalStep witnesses | 2 | derivation tree |
| 8. queryEquations | 2 | rfl |
| **Total** | **36** | |

The derivation witnesses are explicit proof terms showing that the declarative
spec (EvalSpec.lean) allows exactly the expected derivations for each test case.
-/

/-! ## 8. Fuel-Sensitivity Regression Witness

Counterexample showing that `EvalAtomFiltered` (global, non-fuel-indexed) is NOT
provable from soundness alone. The same atom produces an error at low fuel and a
non-error at high fuel, so a low-fuel error does NOT justify "no non-error derivation
exists at any depth."

This witness prevents regression to the false global filtered soundness claim.
The honest fuel-indexed version is `EvalAtomFilteredAtFuel` in Correctness.lean,
where it lives because it talks about the evaluator's computed subfuel results. -/

private def fuelTestSpace := Space.ofList [
  .expression [.symbol ":", .symbol "x", .symbol "Int"],
  .expression [.symbol ":", .symbol "f",
    .expression [.symbol "->", .symbol "Int", .symbol "Int"]]
]

private def fuelTestAtom := Atom.expression [.symbol "f", .symbol "x"]

/-- At low fuel (7), evalAtom returns an error result. -/
example : (evalAtom fuelTestSpace GroundedDispatch.none
    fuelTestAtom Atom.undefinedType Bindings.empty 7).any
    (fun r => isErrorAtom r.1) = true := by decide

/-- At high fuel (11), evalAtom returns a non-error result. -/
example : (evalAtom fuelTestSpace GroundedDispatch.none
    fuelTestAtom Atom.undefinedType Bindings.empty 11).any
    (fun r => !isErrorAtom r.1) = true := by decide

/-! ## 9. Connected Equality-Class Conformance Oracles

The nonlinear three-edge case checks the atom-level observable, while the
smaller two-edge case checks the binding readout directly.  LeaTTa and HE now
preserve the same connected variable classes at both surfaces. -/

private def connectedClassLeaPattern : Metta.Atom :=
  .expr [.sym "g", .var "p1", .var "p2", .var "p2"]

private def connectedClassLeaQuery : Metta.Atom :=
  .expr [.sym "g", .var "q1", .var "q1", .var "q2"]

private def connectedClassLeaRhs : Metta.Atom :=
  .expr [.sym "f", .var "p1", .var "p2"]

private def connectedClassHEPattern : Atom :=
  .expression [.symbol "g", .var "p1", .var "p2", .var "p2"]

private def connectedClassHEQuery : Atom :=
  .expression [.symbol "g", .var "q1", .var "q1", .var "q2"]

private def connectedClassHERhs : Atom :=
  .expression [.symbol "f", .var "p1", .var "p2"]

/-- LeaTTa preserves all three variable equalities in the nonlinear match. -/
theorem leatta_connected_class_match_preserves_equalities :
    Metta.matchAtoms connectedClassLeaPattern connectedClassLeaQuery =
      [[Metta.BindingRel.eq "p2" "q2",
        Metta.BindingRel.eq "p2" "q1",
        Metta.BindingRel.eq "p1" "q1"]] := by
  simpa [connectedClassLeaPattern, connectedClassLeaQuery,
    Metta.connectedClassPattern, Metta.connectedClassQuery,
    Metta.connectedClassBindings] using Metta.connectedClass_match

theorem leatta_connected_class_atom_output :
    (Metta.matchAtoms connectedClassLeaPattern connectedClassLeaQuery).map
        (fun b => Metta.instantiate b connectedClassLeaRhs) =
      [.expr [.sym "f", .var "q1", .var "q1"]] := by
  rw [leatta_connected_class_match_preserves_equalities]
  simp only [List.map_singleton]
  simpa [connectedClassLeaRhs, Metta.connectedClassBindings] using
    Metta.connectedClass_instantiation

set_option maxRecDepth 10000 in
/-- HE retains all three equality edges in one order-free binding class. -/
theorem he_connected_class_match_preserves_equalities :
    matchAtoms connectedClassHEQuery connectedClassHEPattern 20 =
      [⟨[], [("q1", "p1"), ("q1", "p2"), ("q2", "p2")]⟩] := by
  decide

set_option maxRecDepth 10000 in
theorem he_connected_class_atom_output :
    (matchAtoms connectedClassHEQuery connectedClassHEPattern 20).map
        (fun b => b.applyFull connectedClassHERhs 20) =
      [.expression [.symbol "f", .var "q1", .var "q1"]] := by
  decide

/-- The healed three-edge LeaTTa and HE atom outputs coincide modulo alpha. -/
theorem connected_class_atom_outputs_alpha_equivalent :
    Metta.AlphaEq
      (.expr [.sym "f", .var "q1", .var "q1"])
      (.expr [.sym "f", .var "q1", .var "q1"]) := by
  rfl

/-- Negative law: equality classes carrying incompatible ground values are
rejected rather than silently choosing one value. -/
theorem leatta_connected_class_rejects_incompatible_ground_values :
    Metta.Bindings.addVarEquality
      [Metta.BindingRel.val "x" (.sym "A"),
        Metta.BindingRel.val "y" (.sym "B")]
      "x" "y" = [] := by
  exact Metta.incompatibleClassValues_rejected

private def bindingReadoutLeaPattern : Metta.Atom :=
  .expr [.sym "g", .var "p", .var "p"]

private def bindingReadoutLeaQuery : Metta.Atom :=
  .expr [.sym "g", .var "q1", .var "q2"]

private def bindingReadoutLeaRhs : Metta.Atom :=
  .expr [.sym "f", .var "p"]

private def bindingReadoutHEPattern : Atom :=
  .expression [.symbol "g", .var "p", .var "p"]

private def bindingReadoutHEQuery : Atom :=
  .expression [.symbol "g", .var "q1", .var "q2"]

private def bindingReadoutHERhs : Atom :=
  .expression [.symbol "f", .var "p"]

/-- Minimal two-edge LeaTTa match: both query variables remain connected to
the repeated pattern variable by explicit equality relations. -/
theorem leatta_binding_readout_match_connects_q1_q2 :
    Metta.matchAtoms bindingReadoutLeaPattern bindingReadoutLeaQuery =
      [[Metta.BindingRel.eq "p" "q2",
        Metta.BindingRel.eq "p" "q1"]] := by
  rfl

/-- Equality-only matches have no direct value readout; clients must resolve
the equality class rather than treating direct lookup as the observable. -/
theorem leatta_binding_readout_is_equality_only :
    ∀ b ∈ Metta.matchAtoms bindingReadoutLeaPattern bindingReadoutLeaQuery,
      Metta.Bindings.lookupVal b "q1" = none ∧
        Metta.Bindings.lookupVal b "q2" = none := by
  rw [leatta_binding_readout_match_connects_q1_q2]
  simp [Metta.Bindings.lookupVal]

/-- Full LeaTTa binding readout resolves both query variables to the stable
representative of their shared equality class. -/
theorem leatta_binding_readout_resolves_shared_class :
    (Metta.matchAtoms bindingReadoutLeaPattern bindingReadoutLeaQuery).map
        (fun b => Metta.instantiate b (.expr [.var "q1", .var "q2"])) =
      [.expr [.var "q1", .var "q1"]] := by
  rw [leatta_binding_readout_match_connects_q1_q2]
  change [Metta.instantiate
    [Metta.BindingRel.eq "p" "q2", Metta.BindingRel.eq "p" "q1"]
    (.expr [.var "q1", .var "q2"])] = _
  rw [LeaTTaBridge.connectedClass_lea_instantiate_oracles.1]

/-- HE's corresponding two-edge match keeps both query variables in one class. -/
theorem he_binding_readout_match_connects_q1_q2 :
    matchAtoms bindingReadoutHEQuery bindingReadoutHEPattern 20 =
      [⟨[], [("q1", "p"), ("q2", "p")]⟩] := by
  decide

/-- Both runtimes instantiate the repeated pattern variable to the same stable
query representative. -/
theorem binding_readout_equation_outputs :
    (Metta.matchAtoms bindingReadoutLeaPattern bindingReadoutLeaQuery).map
        (fun b => Metta.instantiate b bindingReadoutLeaRhs) =
      [.expr [.sym "f", .var "q1"]] ∧
    (matchAtoms bindingReadoutHEQuery bindingReadoutHEPattern 20).map
        (fun b => b.applyFull bindingReadoutHERhs 20) =
      [.expression [.symbol "f", .var "q1"]] := by
  constructor
  · rw [leatta_binding_readout_match_connects_q1_q2]
    change [Metta.instantiate
      [Metta.BindingRel.eq "p" "q2", Metta.BindingRel.eq "p" "q1"]
      (.expr [.sym "f", .var "p"])] = _
    rw [LeaTTaBridge.connectedClass_lea_instantiate_oracles.2]
  · set_option maxRecDepth 10000 in decide

theorem binding_readout_equation_outputs_alpha_equivalent :
    Metta.AlphaEq
      (.expr [.sym "f", .var "q1"])
      (.expr [.sym "f", .var "q1"]) := by
  rfl

set_option maxRecDepth 10000 in
/-- Reading both query variables exposes the shared equality class directly in
both runtimes. -/
theorem connected_class_binding_readouts :
    (Metta.matchAtoms bindingReadoutLeaPattern bindingReadoutLeaQuery).map
        (fun b => Metta.instantiate b (.expr [.var "q1", .var "q2"])) =
      [.expr [.var "q1", .var "q1"]] ∧
    (matchAtoms bindingReadoutHEQuery bindingReadoutHEPattern 20).map
        (fun b => b.applyFull (.expression [.var "q1", .var "q2"]) 20) =
      [.expression [.var "q1", .var "q1"]] := by
  constructor
  · exact leatta_binding_readout_resolves_shared_class
  · decide

theorem connected_class_binding_readouts_alpha_equivalent :
    Metta.AlphaEq
      (.expr [.var "q1", .var "q1"])
      (.expr [.var "q1", .var "q1"]) := by
  rfl

end Mettapedia.Languages.MeTTa.HE.Conformance
