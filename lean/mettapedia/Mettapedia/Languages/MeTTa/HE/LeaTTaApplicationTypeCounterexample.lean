import Mettapedia.Languages.MeTTa.HE.HumanTypeConformance
import Mettapedia.Languages.MeTTa.HE.HumanTypeRuntimeRefinement
import Mettapedia.Languages.MeTTa.HE.LeaTTaTypeLoopCounterexample
import MettaHyperonFull.Minimal.Interpreter
import Std.Data.HashMap.Lemmas

/-!
# Unsound application-result inference counterexample

The pre-repair minimal type service retained its incoming type bindings when
an argument match failed, then emitted the declared return type anyway.  The
human R1 relation rejects the same application because its argument types are
inconsistent.  These two facts pin the semantic capability change required at
the application-type boundary.  This failure-swallowing defect is distinct
from the reduced-type loop-filter defect: routing the repaired argument fold
through `matchType` also closes that earlier cycle class at this second call
site, but does not constitute a separate repair.

Upstream reference, pending an executable confirmation: the recursive
`check_arg_types_internal` in `lib/src/metta/types.rs` appears to merge
argument bindings without a completed-state loop check.  The witness shape is
the cross-argument system `x = f(y)`, `y = f(x)`.  This is recorded as a
possible upstream issue, not as an established defect.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaApplicationTypeCounterexample

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open HumanTypeSpec
open HumanTypeConformance
open HumanTypeRuntimeRefinement

private def badApplicationSpace : Space :=
  Space.ofList [
    .expression [.symbol ":", .symbol "g",
      .expression [.symbol "->", .symbol "A", .symbol "R"]],
    .expression [.symbol ":", .symbol "b", .symbol "B"]]

private def badApplicationEnv : Metta.Minimal.MinEnv :=
  Metta.Minimal.MinEnv.ofAtomsGT [
    .expr [.sym ":", .sym "g", .expr [.sym "->", .sym "A", .sym "R"]],
    .expr [.sym ":", .sym "b", .sym "B"]] []

private def badApplication : Atom :=
  .expression [.symbol "g", .symbol "b"]

private def badLeaApplication : Metta.Atom :=
  .expr [.sym "g", .sym "b"]

/-- Pre-repair type lookup retained locally so the failure-swallowing behavior
remains pinned after the executable is corrected. -/
private def legacyGetTypes (env : Metta.Minimal.MinEnv) :
    Metta.Atom → List Metta.Atom
  | .gnd (.int _) => [.sym "Number"]
  | .gnd (.float _) => [.sym "Number"]
  | .gnd (.str _) => [.sym "String"]
  | .gnd (.bool _) => [.sym "Bool"]
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
                  let bindings := (types.dropLast.zip argumentTypes).foldl
                    (fun bindings pair =>
                      match (Metta.matchAtoms
                          (Metta.instantiate bindings pair.1) pair.2).head? with
                      | some matched =>
                          ((Metta.Bindings.merge bindings matched).head?).getD
                            bindings
                      | none => bindings) []
                  some (Metta.instantiate bindings returnType)
              | _ => none with
          | [] => [.sym "%Undefined%"]
          | results => results
  | .expr [] => [.sym "%Undefined%"]

/-- Negative legacy witness: the pre-repair type service inferred `R` even
though the sole argument has declared type `B` where `A` is required. -/
theorem legacy_getTypes_infers_return_after_failed_argument_match :
    legacyGetTypes badApplicationEnv badLeaApplication =
      [.sym "R"] := by
  simp [badApplicationEnv, badLeaApplication, legacyGetTypes,
    Metta.Minimal.MinEnv.ofAtomsGT, Std.HashMap.getD_insert,
    Std.HashMap.getD_emptyWithCapacity, Metta.matchAtoms,
    Metta.matchAtomsWith, Metta.Bindings.merge, Metta.instantiate]

/-- Positive repair witness: a failed argument match contributes no inferred
application result, so the gradual fallback is `%Undefined%`. -/
theorem repaired_getTypes_rejects_failed_argument_match :
    Metta.Minimal.getTypes badApplicationEnv badLeaApplication =
      [.sym "%Undefined%"] := by
  have hg : Metta.Minimal.getTypes badApplicationEnv (.sym "g") =
      [.expr [.sym "->", .sym "A", .sym "R"]] := by
    rw [Metta.Minimal.getTypes.eq_8]
    simp [badApplicationEnv, Metta.Minimal.MinEnv.ofAtomsGT,
      Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity]
  have hb : Metta.Minimal.getTypes badApplicationEnv (.sym "b") =
      [.sym "B"] := by
    rw [Metta.Minimal.getTypes.eq_8]
    simp [badApplicationEnv, Metta.Minimal.MinEnv.ofAtomsGT,
      Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity]
  have hexpr : badApplicationEnv.exprTypes = [] := rfl
  have hatoms : badApplicationEnv.atoms = [
    .expr [.sym ":", .sym "g", .expr [.sym "->", .sym "A", .sym "R"]],
    .expr [.sym ":", .sym "b", .sym "B"]] := rfl
  rw [show badLeaApplication = .expr [.sym "g", .sym "b"] from rfl,
    Metta.Minimal.getTypes.eq_10 _ _ _ (by simp)]
  simp [hg, hb, hexpr, hatoms, Metta.Minimal.typeInferenceAvoid,
    Metta.Atom.vars, Metta.Minimal.freshenArgumentTypes,
    Metta.Minimal.freshenTypeCandidate, Metta.Minimal.renameAllVars,
    Metta.Minimal.matchApplicationTypeArguments, Metta.Minimal.matchType,
    Metta.Minimal.matchReduced, Metta.matchAtoms, Metta.matchAtomsWith,
    BEq.beq, Metta.Atom.beq]

private def cyclicApplicationEnv : Metta.Minimal.MinEnv :=
  Metta.Minimal.MinEnv.ofAtomsGT [
    .expr [.sym ":", .sym "cyclic-g",
      .expr [.sym "->", .var "x", .var "y", .sym "R"]],
    .expr [.sym ":", .sym "cyclic-a", .expr [.sym "f", .var "y"]],
    .expr [.sym ":", .sym "cyclic-b", .expr [.sym "f", .var "x"]]] []

private def cyclicLeaApplication : Metta.Atom :=
  .expr [.sym "cyclic-g", .sym "cyclic-a", .sym "cyclic-b"]

/-- The same legacy fold also accepted two individually loop-free argument
matches whose conjunction is the cross-child cycle pinned by repair #4. -/
theorem legacy_getTypes_infers_return_after_cyclic_argument_matches :
    legacyGetTypes cyclicApplicationEnv cyclicLeaApplication = [.sym "R"] := by
  simp [cyclicApplicationEnv, cyclicLeaApplication, legacyGetTypes,
    Metta.Minimal.MinEnv.ofAtomsGT, Std.HashMap.getD_insert,
    Std.HashMap.getD_emptyWithCapacity, Metta.matchAtoms,
    Metta.matchAtomsWith, Metta.Bindings.merge, Metta.instantiate,
    Metta.Bindings.resolveAtom]

/-- The raw shared-spelling conjunction is still rejected by the repaired
matcher — repair #4's loop filter at its own level.  This is the permanent
witness that the cross-child cycle is real when the spellings genuinely
coincide. -/
theorem raw_cyclic_argument_matches_still_rejected :
    Metta.Minimal.matchApplicationTypeArguments []
      [.var "x", .var "y"]
      [.expr [.sym "f", .var "y"], .expr [.sym "f", .var "x"]] =
        none := by
  simp only [Metta.Minimal.matchApplicationTypeArguments,
    Metta.Minimal.matchType]
  simp only [Metta.Atom.beq, BEq.beq, Bool.false_or,
    Bool.false_eq_true, if_false]
  change Metta.Minimal.matchReducedList []
    [.var "x", .var "y"]
    [.expr [.sym "f", .var "y"], .expr [.sym "f", .var "x"]] =
      none
  exact
    Mettapedia.Languages.MeTTa.HE.LeaTTaTypeLoopCounterexample.repaired_matchReducedList_rejects_cyclic_type_binding

/-! The freshened spellings that `getTypes` produces for the cyclic
application are concrete strings built by `captureAvoidingName`
(avoidance prefix ++ name ++ "#" ++ position):

* argument 1 type `(f $y)` freshens `y` to `"#########y#0"`,
* argument 2 type `(f $x)` freshens `x` to `"#####################x#1"`,
* the annotation `(-> $x $y R)` freshens its binders at position 2 to
  `"#...#x#2"` / `"#...#y#2"` (45-`#` prefix).

The lemmas below evaluate the argument-match fold on these freshened
atoms.  `b1`/`b2a` denote the singleton binding sets produced by each
argument match in isolation, `b2` the threaded final state.  Fueled
functions (`resolveAtomAux`) are kernel-computable, so once the
well-founded wrappers (`Bindings.vars`, `resolutionFuel`) are rewritten
away, plain `rfl` evaluates the loop check. -/

private theorem vars_b1 : Metta.Bindings.vars
    [.val "#############################################x#2"
      (.expr [.sym "f", .var "#########y#0"])] =
    ["#############################################x#2", "#########y#0"] := by
  simp [Metta.Bindings.vars, Metta.Atom.vars]
  rfl

private theorem vars_b2a : Metta.Bindings.vars
    [.val "#############################################y#2"
      (.expr [.sym "f", .var "#####################x#1"])] =
    ["#############################################y#2",
     "#####################x#1"] := by
  simp [Metta.Bindings.vars, Metta.Atom.vars]
  rfl

private theorem vars_b2 : Metta.Bindings.vars
    [.val "#############################################y#2"
      (.expr [.sym "f", .var "#####################x#1"]),
     .val "#############################################x#2"
      (.expr [.sym "f", .var "#########y#0"])] =
    ["#############################################y#2",
     "#####################x#1",
     "#############################################x#2",
     "#########y#0"] := by
  simp [Metta.Bindings.vars, Metta.Atom.vars]
  rfl

private theorem fuel_b1 : ∀ z, Metta.Bindings.resolutionFuel
    [.val "#############################################x#2"
      (.expr [.sym "f", .var "#########y#0"])] (.var z) = 6 := by
  intro z
  simp [Metta.Bindings.resolutionFuel,
    Metta.Bindings.relationResolutionFuel, Metta.Atom.size]

private theorem fuel_b2a : ∀ z, Metta.Bindings.resolutionFuel
    [.val "#############################################y#2"
      (.expr [.sym "f", .var "#####################x#1"])] (.var z) = 6 := by
  intro z
  simp [Metta.Bindings.resolutionFuel,
    Metta.Bindings.relationResolutionFuel, Metta.Atom.size]

private theorem fuel_b2 : ∀ z, Metta.Bindings.resolutionFuel
    [.val "#############################################y#2"
      (.expr [.sym "f", .var "#####################x#1"]),
     .val "#############################################x#2"
      (.expr [.sym "f", .var "#########y#0"])] (.var z) = 10 := by
  intro z
  simp [Metta.Bindings.resolutionFuel,
    Metta.Bindings.relationResolutionFuel, Metta.Atom.size]

private theorem loop_b1 : Metta.Bindings.hasLoop
    [.val "#############################################x#2"
      (.expr [.sym "f", .var "#########y#0"])] = false := by
  simp only [Metta.Bindings.hasLoop, vars_b1, fuel_b1]
  rfl

private theorem loop_b2a : Metta.Bindings.hasLoop
    [.val "#############################################y#2"
      (.expr [.sym "f", .var "#####################x#1"])] = false := by
  simp only [Metta.Bindings.hasLoop, vars_b2a, fuel_b2a]
  rfl

private theorem loop_b2 : Metta.Bindings.hasLoop
    [.val "#############################################y#2"
      (.expr [.sym "f", .var "#####################x#1"]),
     .val "#############################################x#2"
      (.expr [.sym "f", .var "#########y#0"])] = false := by
  simp only [Metta.Bindings.hasLoop, vars_b2, fuel_b2]
  rfl

private theorem atoms_arg1 : Metta.matchAtoms
    (.var "#############################################x#2")
    (.expr [.sym "f", .var "#########y#0"]) =
    [[.val "#############################################x#2"
      (.expr [.sym "f", .var "#########y#0"])]] := by
  simp [Metta.matchAtoms, Metta.matchAtomsWith, Metta.Subst.occurs, loop_b1]

private theorem atoms_arg2 : Metta.matchAtoms
    (.var "#############################################y#2")
    (.expr [.sym "f", .var "#####################x#1"]) =
    [[.val "#############################################y#2"
      (.expr [.sym "f", .var "#####################x#1"])]] := by
  simp [Metta.matchAtoms, Metta.matchAtomsWith, Metta.Subst.occurs, loop_b2a]

private theorem merge_arg1 : Metta.Bindings.merge []
    [.val "#############################################x#2"
      (.expr [.sym "f", .var "#########y#0"])] =
    [[.val "#############################################x#2"
      (.expr [.sym "f", .var "#########y#0"])]] := by
  simp [Metta.Bindings.merge, Metta.Bindings.mergeOne,
    Metta.Bindings.addVarBinding, Metta.Bindings.addValRaw,
    Metta.Bindings.removeVal]

private theorem horder_b1 : Metta.Bindings.eqVarsInOrder
    [.val "#############################################x#2"
      (.expr [.sym "f", .var "#########y#0"])] = [] := by
  simp [Metta.Bindings.eqVarsInOrder]

private theorem heqco_b1 : ∀ z, Metta.Bindings.eqClassOrdered
    [.val "#############################################x#2"
      (.expr [.sym "f", .var "#########y#0"])] z = [z] := by
  intro z
  simp [Metta.Bindings.eqClassOrdered, horder_b1]

private theorem merge_arg2 : Metta.Bindings.merge
    [.val "#############################################x#2"
      (.expr [.sym "f", .var "#########y#0"])]
    [.val "#############################################y#2"
      (.expr [.sym "f", .var "#####################x#1"])] =
    [[.val "#############################################y#2"
        (.expr [.sym "f", .var "#####################x#1"]),
      .val "#############################################x#2"
        (.expr [.sym "f", .var "#########y#0"])]] := by
  simp [Metta.Bindings.merge, Metta.Bindings.mergeOne,
    Metta.Bindings.addVarBinding, Metta.Bindings.addValRaw,
    Metta.Bindings.removeVal, Metta.Bindings.classValues,
    Metta.Bindings.lookupVal, heqco_b1]

private theorem red_arg1 : Metta.Minimal.matchReduced []
    (.var "#############################################x#2")
    (.expr [.sym "f", .var "#########y#0"]) =
    some [.val "#############################################x#2"
      (.expr [.sym "f", .var "#########y#0"])] := by
  rw [Metta.Minimal.matchReduced] <;>
    simp [atoms_arg1, merge_arg1, loop_b1,
      (show ∀ s t : String,
          (Metta.Atom.var s == Metta.Atom.sym t) = false from
        fun _ _ => rfl),
      (show ∀ (xs : List Metta.Atom) (t : String),
          (Metta.Atom.expr xs == Metta.Atom.sym t) = false from
        fun _ _ => rfl)]

private theorem red_arg2 : Metta.Minimal.matchReduced
    [.val "#############################################x#2"
      (.expr [.sym "f", .var "#########y#0"])]
    (.var "#############################################y#2")
    (.expr [.sym "f", .var "#####################x#1"]) =
    some [.val "#############################################y#2"
        (.expr [.sym "f", .var "#####################x#1"]),
      .val "#############################################x#2"
        (.expr [.sym "f", .var "#########y#0"])] := by
  rw [Metta.Minimal.matchReduced] <;>
    simp [atoms_arg2, merge_arg2, loop_b2,
      (show ∀ s t : String,
          (Metta.Atom.var s == Metta.Atom.sym t) = false from
        fun _ _ => rfl),
      (show ∀ (xs : List Metta.Atom) (t : String),
          (Metta.Atom.expr xs == Metta.Atom.sym t) = false from
        fun _ _ => rfl)]

/-- The two freshened argument matches succeed and thread to the acyclic
binding state `b2`: fresh function-type binders map to fresh argument-type
values, so no spelling participates in a dependency cycle. -/
private theorem match_freshened_args :
    Metta.Minimal.matchApplicationTypeArguments []
      [.var "#############################################x#2",
        .var "#############################################y#2"]
      [.expr [.sym "f", .var "#########y#0"],
        .expr [.sym "f", .var "#####################x#1"]] =
      some [.val "#############################################y#2"
          (.expr [.sym "f", .var "#####################x#1"]),
        .val "#############################################x#2"
          (.expr [.sym "f", .var "#########y#0"])] := by
  simp [Metta.Minimal.matchApplicationTypeArguments,
    Metta.Minimal.matchType, red_arg1, red_arg2,
    (show ∀ s t : String,
        (Metta.Atom.var s == Metta.Atom.sym t) = false from
      fun _ _ => rfl),
    (show ∀ (xs : List Metta.Atom) (t : String),
        (Metta.Atom.expr xs == Metta.Atom.sym t) = false from
      fun _ _ => rfl)]

private theorem inst_ret : Metta.instantiate
    [.val "#############################################y#2"
        (.expr [.sym "f", .var "#####################x#1"]),
      .val "#############################################x#2"
        (.expr [.sym "f", .var "#########y#0"])] (Metta.Atom.sym "R") =
    Metta.Atom.sym "R" := by
  simp [Metta.instantiate, Metta.Bindings.resolveAtom]

/-- Repair #7 dissolves the getTypes-level instance of that cycle: the
"cycle" between the annotation binders `$x $y` and the argument types' free
`$x $y` was spelling capture, not semantics.  With capture-avoiding
freshening the binder and argument scopes separate, the match legitimately
succeeds, and the application types as `R` — matching upstream's hygienic
behavior.  The genuine cycle rejection remains pinned one level down by
`raw_cyclic_argument_matches_still_rejected`. -/
theorem repaired_freshening_dissolves_cyclic_spelling_capture :
    Metta.Minimal.getTypes cyclicApplicationEnv cyclicLeaApplication =
      [.sym "R"] := by
  have hcg : Metta.Minimal.getTypes cyclicApplicationEnv (.sym "cyclic-g") =
      [.expr [.sym "->", .var "x", .var "y", .sym "R"]] := by
    rw [Metta.Minimal.getTypes.eq_8]
    simp [cyclicApplicationEnv, Metta.Minimal.MinEnv.ofAtomsGT,
      Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity]
  have hca : Metta.Minimal.getTypes cyclicApplicationEnv (.sym "cyclic-a") =
      [.expr [.sym "f", .var "y"]] := by
    rw [Metta.Minimal.getTypes.eq_8]
    simp [cyclicApplicationEnv, Metta.Minimal.MinEnv.ofAtomsGT,
      Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity]
  have hcb : Metta.Minimal.getTypes cyclicApplicationEnv (.sym "cyclic-b") =
      [.expr [.sym "f", .var "x"]] := by
    rw [Metta.Minimal.getTypes.eq_8]
    simp [cyclicApplicationEnv, Metta.Minimal.MinEnv.ofAtomsGT,
      Std.HashMap.getD_insert, Std.HashMap.getD_emptyWithCapacity]
  have hexpr : cyclicApplicationEnv.exprTypes = [] := rfl
  have hatoms : cyclicApplicationEnv.atoms = [
    .expr [.sym ":", .sym "cyclic-g",
      .expr [.sym "->", .var "x", .var "y", .sym "R"]],
    .expr [.sym ":", .sym "cyclic-a", .expr [.sym "f", .var "y"]],
    .expr [.sym ":", .sym "cyclic-b", .expr [.sym "f", .var "x"]]] := rfl
  have hn1 : Metta.Minimal.captureAvoidingName
      ["x", "y", "y", "x", "x", "y", "y", "x"] 0 "y" =
      "#########y#0" := rfl
  have hn2 : Metta.Minimal.captureAvoidingName
      ["x", "y", "y", "x", "x", "y", "y", "x", "#########y#0"] 1 "x" =
      "#####################x#1" := rfl
  have hn3x : Metta.Minimal.captureAvoidingName
      ["x", "y", "y", "x", "x", "y", "y", "x", "#########y#0",
        "#####################x#1"] 2 "x" =
      "#############################################x#2" := rfl
  have hn3y : Metta.Minimal.captureAvoidingName
      ["x", "y", "y", "x", "x", "y", "y", "x", "#########y#0",
        "#####################x#1"] 2 "y" =
      "#############################################y#2" := rfl
  have havoid : Metta.Minimal.typeInferenceAvoid cyclicApplicationEnv
      (.expr [.sym "cyclic-g", .sym "cyclic-a", .sym "cyclic-b"])
      [.expr [.sym "->", .var "x", .var "y", .sym "R"],
        .expr [.sym "f", .var "y"], .expr [.sym "f", .var "x"]] =
      ["x", "y", "y", "x", "x", "y", "y", "x"] := by
    simp [Metta.Minimal.typeInferenceAvoid, hatoms, Metta.Atom.vars]
  have hargTs : Metta.Minimal.freshenArgumentTypes
      ["x", "y", "y", "x", "x", "y", "y", "x"] 0
      [.expr [.sym "f", .var "y"], .expr [.sym "f", .var "x"]] =
      [.expr [.sym "f", .var "#########y#0"],
        .expr [.sym "f", .var "#####################x#1"]] := by
    simp [Metta.Minimal.freshenArgumentTypes,
      Metta.Minimal.freshenTypeCandidate, Metta.Minimal.renameAllVars,
      Metta.Atom.vars, hn1, hn2]
  have hfunT : Metta.Minimal.freshenTypeCandidate
      ["x", "y", "y", "x", "x", "y", "y", "x", "#########y#0",
        "#####################x#1"] 2
      (.expr [.sym "->", .var "x", .var "y", .sym "R"]) =
      .expr [.sym "->",
        .var "#############################################x#2",
        .var "#############################################y#2",
        .sym "R"] := by
    simp [Metta.Minimal.freshenTypeCandidate, Metta.Minimal.renameAllVars,
      hn3x, hn3y]
  rw [show cyclicLeaApplication =
      .expr [.sym "cyclic-g", .sym "cyclic-a", .sym "cyclic-b"] from rfl,
    Metta.Minimal.getTypes.eq_10 _ _ _ (by simp)]
  simp [hcg, hca, hcb, hexpr, havoid, hargTs, hfunT, Metta.Atom.vars,
    match_freshened_args, inst_ret, List.dropLast, List.getLast?]

private theorem badApplication_g_type
    {type : Atom} (h : TypeOfRel badApplicationSpace (.symbol "g") type) :
    type = .expression [.symbol "->", .symbol "A", .symbol "R"] := by
  have hmem := (typeOfRel_iff_mem_getAtomTypes _ _ _).mp h
  simpa [badApplicationSpace, Space.ofList, getAtomTypes,
    getAnnotatedTypes, Atom.undefinedType, BEq.beq, Atom.beq] using hmem

private theorem badApplication_b_type
    {type : Atom} (h : TypeOfRel badApplicationSpace (.symbol "b") type) :
    type = .symbol "B" := by
  have hmem := (typeOfRel_iff_mem_getAtomTypes _ _ _).mp h
  simpa [badApplicationSpace, Space.ofList, getAtomTypes,
    getAnnotatedTypes, Atom.undefinedType, BEq.beq, Atom.beq] using hmem

private theorem symbol_runtime_evidence_g
    {type : Atom}
    (h : RuntimeTypeEvidenceRel badApplicationSpace (.symbol "g") type) :
    type = .expression [.symbol "->", .symbol "A", .symbol "R"] := by
  cases h with
  | published htype => exact badApplication_g_type htype
  | application happ =>
      cases happ with
      | mk hshape => simp at hshape
  | stateValue hstate =>
      cases hstate

private theorem symbol_runtime_evidence_b
    {type : Atom}
    (h : RuntimeTypeEvidenceRel badApplicationSpace (.symbol "b") type) :
    type = .symbol "B" := by
  cases h with
  | published htype => exact badApplication_b_type htype
  | application happ =>
      cases happ with
      | mk hshape => simp at hshape
  | stateValue hstate =>
      cases hstate

/-- Semantic counterpart: the named R1 relation has no derivation for this
ill-typed application and return type. -/
theorem no_human_r1_result_after_failed_argument_match :
    ¬R1ApplicationResultRel badApplicationSpace badApplication
      (.symbol "R") := by
  intro hinfer
  cases hinfer with
  | @mk _ _ operator functionBase functionType declaredReturnType arguments
      argumentTypes typeBindings hshape hoperator hrenaming hfunction
      harguments hreturn =>
      simp [badApplication] at hshape
      rcases hshape with ⟨rfl, rfl⟩
      have hfunctionBase := symbol_runtime_evidence_g hoperator
      subst hfunctionBase
      obtain ⟨ρ, _, rfl⟩ := hrenaming
      have hground : renameHumanTypeVars ρ
          (.expression [.symbol "->", .symbol "A", .symbol "R"]) =
          .expression [.symbol "->", .symbol "A", .symbol "R"] := by
        simp [renameHumanTypeVars]
      rw [hground] at hfunction
      have hparts := functionTypeRel_getFunctionParts hfunction
      have hargumentTypes : argumentTypes = [.symbol "A"] := by
        simpa [getFunctionArgTypes] using hparts.2.1.symm
      have hdeclaredReturnType : declaredReturnType = .symbol "R" := by
        simpa [getFunctionRetType] using hparts.2.2.symm
      subst argumentTypes
      subst declaredReturnType
      cases harguments with
      | cons hactual hactualRenaming hmatch htail =>
          have hactualBase := symbol_runtime_evidence_b hactual
          subst hactualBase
          obtain ⟨ρ', _, rfl⟩ := hactualRenaming
          have hgroundB : renameHumanTypeVars ρ' (.symbol "B") =
              .symbol "B" := by
            simp [renameHumanTypeVars]
          rw [hgroundB] at hmatch
          obtain ⟨valuation, hmodel⟩ := hmatch.satisfiable
          have hconsistent := (hmatch.solutions valuation).mp hmodel |>.2
          simp [CorePlusR2TypeConsistent, ReducedTypeConsistent,
            Atom.undefinedType, Atom.atomType] at hconsistent

end Mettapedia.Languages.MeTTa.HE.LeaTTaApplicationTypeCounterexample
