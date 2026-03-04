import Mettapedia.Logic.Prolog.Eval

/-!
# Prolog Fixture Corpus (ISO/Logtalk-Sourced)

This file adds a first, targeted fixture corpus for the Prolog built-in layer.
Each fixture theorem is either:

- directly aligned to a Logtalk ISO conformance test ID, or
- an adapted constructor-level regression when the current formal core does not
  model the full ISO runtime error layer (e.g., callability and instantiation errors).

## Upstream Sources

- Logtalk Prolog conformance tests:
  - `tests/prolog/control/true_0/tests.lgt`
  - `tests/prolog/control/fail_0/tests.lgt`
  - `tests/prolog/control/conjunction_2/tests.lgt`
  - `tests/prolog/control/disjunction_2/tests.lgt`
  - `tests/prolog/predicates/once_1/tests.lgt`
  - `tests/prolog/predicates/not_1/tests.lgt`
  - `tests/prolog/predicates/unify_2/tests.lgt`
  - `tests/prolog/predicates/not_unifiable_2/tests.lgt`
  - `tests/prolog/predicates/findall_3/tests.lgt`
-/

namespace Mettapedia.Logic.Prolog

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match

namespace FixtureCorpus

/-! ## Small Constants Used by Multiple Fixtures -/

def one : Pattern := .apply "1" []
def two : Pattern := .apply "2" []
def oneFloat : Pattern := .apply "1.0" []
def three : Pattern := .apply "3" []
def four : Pattern := .apply "4" []
def five : Pattern := .apply "5" []
def aConst : Pattern := .apply "a" []
def bConst : Pattern := .apply "b" []
def abcConst : Pattern := .apply "abc" []
def defConst : Pattern := .apply "def" []

/-! ## true/0, fail/0 -/

/-- Source: Logtalk ISO test `iso_true_0_01` (`control/true_0/tests.lgt`). -/
theorem iso_true_0_01 {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle .succeed env (.normal [env]) :=
  PrologEval.succeed_eval env

/-- Source: Logtalk ISO test `iso_fail_0_01` (`control/fail_0/tests.lgt`). -/
theorem iso_fail_0_01 {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle .fail env (.normal []) :=
  PrologEval.fail_eval env

/-! ## (,)/2 (adapted constructor-level fixtures) -/

/-- Adapted conjunction positive fixture: sequencing two successful goals. -/
theorem conjunction_pos_succeed_then_succeed {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.conj .succeed .succeed) env (.normal [env]) := by
  refine PrologEval.conj_normal .succeed .succeed env [env] [(env, [env])] ?_ ?_ ?_
  · exact PrologEval.succeed_eval env
  · rfl
  · intro p hp
    simp at hp
    rw [hp]
    exact PrologEval.succeed_eval env

/-- Adapted conjunction negative fixture: success followed by failure. -/
theorem conjunction_neg_succeed_then_fail {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.conj .succeed .fail) env (.normal []) := by
  refine PrologEval.conj_normal .succeed .fail env [env] [(env, [])] ?_ ?_ ?_
  · exact PrologEval.succeed_eval env
  · rfl
  · intro p hp
    simp at hp
    rw [hp]
    exact PrologEval.fail_eval env

/-- Source: Logtalk ISO test `iso_conjunction_2_01`
(`control/conjunction_2/tests.lgt`). -/
theorem iso_conjunction_2_01 {oracle : EvalOracle} :
    PrologEval oracle (.conj (.unify (.fvar "X") one) (.isVar (.fvar "X")))
      []
      (.normal []) := by
  have h1 : PrologEval oracle (.unify (.fvar "X") one) []
      (.normal [[("X", one)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, one]
  have h2 : PrologEval oracle (.isVar (.fvar "X")) [("X", one)] (.normal []) := by
    refine PrologEval.isVar_fail (.fvar "X") [("X", one)] ?_
    intro hvar
    rcases hvar with ⟨v, hv⟩
    simp [applyBindings, one] at hv
  refine PrologEval.conj_normal _ _ [] [[("X", one)]]
    [([("X", one)], [])] h1 ?_ ?_
  · simp
  · intro p hp
    simp at hp
    rw [hp]
    exact h2

/-! ## (;)/2 -/

/-- Source-aligned positive fixture: `;(true, fail)` (cf. `iso_disjunction_2_01`). -/
theorem iso_disjunction_2_01_like {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.disj .succeed .fail) env (.normal ([env] ++ [])) :=
  PrologEval.disj_normal .succeed .fail env [env] []
    (PrologEval.succeed_eval env) (PrologEval.fail_eval env)

/-- Alias theorem for ISO test id `iso_disjunction_2_01`. -/
theorem iso_disjunction_2_01 {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.disj .succeed .fail) env (.normal ([env] ++ [])) :=
  iso_disjunction_2_01_like (oracle := oracle) (env := env)

/-- Adapted negative fixture: `;(fail, fail)` has no answers. -/
theorem disjunction_neg_fail_or_fail {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.disj .fail .fail) env (.normal ([] ++ [])) :=
  PrologEval.disj_normal .fail .fail env [] []
    (PrologEval.fail_eval env) (PrologEval.fail_eval env)

/-! ## once/1 -/

/-- Source-aligned positive fixture: `once(true)` keeps one answer. -/
theorem iso_once_1_01_like {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.once .succeed) env (.normal [env]) :=
  PrologEval.once_some .succeed env (.normal [env]) env []
    (PrologEval.succeed_eval env) rfl

/-- Source-aligned negative fixture: `once(fail)` gives no answers (`iso_once_1_04`). -/
theorem iso_once_1_04_like {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.once .fail) env (.normal []) :=
  PrologEval.once_none .fail env (.normal []) (PrologEval.fail_eval env) rfl

/-- Alias theorem for ISO test id `iso_once_1_04`. -/
theorem iso_once_1_04 {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.once .fail) env (.normal []) :=
  iso_once_1_04_like (oracle := oracle) (env := env)

/-- Source: Logtalk ISO test `iso_once_1_05` (`predicates/once_1/tests.lgt`).
In this core, unification allows rational-tree style self reference (`X = f(X)`). -/
theorem iso_once_1_05 {oracle : EvalOracle} :
    PrologEval oracle (.once (.unify (.fvar "X") (.apply "f" [(.fvar "X")])))
      []
      (.normal [[("X", .apply "f" [(.fvar "X")])]]) := by
  have hu : PrologEval oracle (.unify (.fvar "X") (.apply "f" [(.fvar "X")])) []
      (.normal [[("X", .apply "f" [(.fvar "X")])]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern]
  exact PrologEval.once_some
    (.unify (.fvar "X") (.apply "f" [(.fvar "X")]))
    []
    (.normal [[("X", .apply "f" [(.fvar "X")])]])
    [("X", .apply "f" [(.fvar "X")])]
    []
    hu
    rfl

/-! ## \+/1 -/

/-- Source-aligned positive fixture: `\+ fail` succeeds (`iso_not_1_03`-style). -/
theorem iso_not_1_pos_fail_inner {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.neg .fail) env (.normal [env]) :=
  PrologEval.neg_succ .fail env (.normal []) (PrologEval.fail_eval env) rfl

/-- Source-aligned negative fixture: `\+ true` fails (`iso_not_1_01`). -/
theorem iso_not_1_01_like {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.neg .succeed) env (.normal []) :=
  PrologEval.neg_fail .succeed env (.normal [env]) env []
    (PrologEval.succeed_eval env) rfl

/-- Alias theorem for ISO test id `iso_not_1_01`. -/
theorem iso_not_1_01 {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.neg .succeed) env (.normal []) :=
  iso_not_1_01_like (oracle := oracle) (env := env)

/-- Source: Logtalk ISO test `iso_not_1_02` (`predicates/not_1/tests.lgt`). -/
theorem iso_not_1_02 {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.neg .cut) env (.normal []) :=
  PrologEval.neg_fail .cut env (.cutThrown [env]) env []
    (PrologEval.cut_eval env) rfl

/-- Source: Logtalk ISO test `iso_not_1_03` (`predicates/not_1/tests.lgt`). -/
theorem iso_not_1_03 {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.neg (.conj .cut .fail)) env (.normal [env]) := by
  have hconj : PrologEval oracle (.conj .cut .fail) env (.cutThrown []) := by
    refine PrologEval.conj_g1_cut .cut .fail env [env] [(env, [])]
      (PrologEval.cut_eval env) ?_ ?_
    · rfl
    · intro p hp
      simp at hp
      rw [hp]
      exact PrologEval.fail_eval env
  exact PrologEval.neg_succ (.conj .cut .fail) env (.cutThrown []) hconj rfl

/-! ## var/1 -/

/-- Source-aligned non-error fixture: `var(X), X=1` succeeds (`iso_conjunction_2_02` shape). -/
theorem iso_conjunction_2_02 {oracle : EvalOracle} :
    PrologEval oracle (.conj (.isVar (.fvar "X")) (.unify (.fvar "X") one))
      []
      (.normal [[("X", one)]]) := by
  have hvar : PrologEval oracle (.isVar (.fvar "X")) [] (.normal [[]]) :=
    PrologEval.isVar_succ (.fvar "X") [] "X" (by simp [applyBindings])
  have hunify : PrologEval oracle (.unify (.fvar "X") one) [] (.normal [[("X", one)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, one]
  refine PrologEval.conj_normal _ _ [] [[]] [([], [[("X", one)]])] hvar ?_ ?_
  · simp
  · intro p hp
    simp at hp
    rw [hp]
    exact hunify

/-! ## =/2 -/

/-- Source-aligned positive fixture: variable unifies with a constant (`iso_unify_2_02`). -/
theorem iso_unify_2_02_like {oracle : EvalOracle} :
    PrologEval oracle (.unify (.fvar "X") one) []
      (.normal [[("X", one)]]) := by
  refine PrologEval.unify_succ _ _ _ _ ?_
  simp [applyBindings, matchPattern, one]

/-- Alias theorem for ISO test id `iso_unify_2_02`. -/
theorem iso_unify_2_02 {oracle : EvalOracle} :
    PrologEval oracle (.unify (.fvar "X") one) []
      (.normal [[("X", one)]]) :=
  iso_unify_2_02_like (oracle := oracle)

/-- Source-aligned negative fixture: distinct constants fail to unify (`iso_unify_2_07`). -/
theorem iso_unify_2_07_like {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.unify one two) env (.normal []) := by
  refine PrologEval.unify_fail _ _ _ ?_
  simp [applyBindings, matchPattern, one, two]

/-- Alias theorem for ISO test id `iso_unify_2_07`. -/
theorem iso_unify_2_07 {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.unify one two) env (.normal []) :=
  iso_unify_2_07_like (oracle := oracle) (env := env)

/-- Source-aligned positive fixture: equal constants unify (`iso_unify_2_01`). -/
theorem iso_unify_2_01_like {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.unify one one) env (.normal [env]) := by
  have h : [] ∈ matchPattern (applyBindings env one) (applyBindings env one) := by
    simp [one, applyBindings, matchPattern, matchArgs]
  simpa using (PrologEval.unify_succ one one env [] h)

/-- Alias theorem for ISO test id `iso_unify_2_01`. -/
theorem iso_unify_2_01 {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.unify one one) env (.normal [env]) :=
  iso_unify_2_01_like (oracle := oracle) (env := env)

/-- Source: Logtalk ISO test `iso_unify_2_03` (`predicates/unify_2/tests.lgt`). -/
theorem iso_unify_2_03 {oracle : EvalOracle} :
    PrologEval oracle (.unify (.fvar "X") (.fvar "Y")) []
      (.normal [[("X", .fvar "Y")]]) := by
  refine PrologEval.unify_succ _ _ _ _ ?_
  simp [applyBindings, matchPattern]

/-- Source: Logtalk ISO test `iso_unify_2_04` (`predicates/unify_2/tests.lgt`). -/
theorem iso_unify_2_04 {oracle : EvalOracle} :
    PrologEval oracle (.unify (.fvar "U") (.fvar "V")) []
      (.normal [[("U", .fvar "V")]]) := by
  refine PrologEval.unify_succ _ _ _ _ ?_
  simp [applyBindings, matchPattern]

/-- Source: Logtalk ISO test `iso_unify_2_05` (`predicates/unify_2/tests.lgt`). -/
theorem iso_unify_2_05 {oracle : EvalOracle} :
    PrologEval oracle
      (.conj (.unify (.fvar "X") (.fvar "Y")) (.unify (.fvar "X") abcConst))
      []
      (.normal [[("X", .fvar "Y"), ("Y", abcConst)]]) := by
  have hxy : PrologEval oracle (.unify (.fvar "X") (.fvar "Y")) []
      (.normal [[("X", .fvar "Y")]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern]
  have hxa : PrologEval oracle (.unify (.fvar "X") abcConst) [("X", .fvar "Y")]
      (.normal [[("X", .fvar "Y"), ("Y", abcConst)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, abcConst]
  refine PrologEval.conj_normal _ _ [] [[("X", .fvar "Y")]]
    [([("X", .fvar "Y")], [[("X", .fvar "Y"), ("Y", abcConst)]])] hxy ?_ ?_
  · simp
  · intro p hp
    simp at hp
    rw [hp]
    exact hxa

/-- Source: Logtalk ISO test `iso_unify_2_08` (`predicates/unify_2/tests.lgt`). -/
theorem iso_unify_2_08 {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.unify one oneFloat) env (.normal []) := by
  refine PrologEval.unify_fail _ _ _ ?_
  simp [applyBindings, matchPattern, one, oneFloat]

/-- Source: Logtalk ISO test `iso_unify_2_09` (`predicates/unify_2/tests.lgt`). -/
theorem iso_unify_2_09 {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle
      (.unify (.apply "g" [(.fvar "X")]) (.apply "f" [(.apply "f" [(.fvar "X")])]))
      env
      (.normal []) := by
  refine PrologEval.unify_fail _ _ _ ?_
  simp [applyBindings, matchPattern]

/-- Source: Logtalk ISO test `iso_unify_2_10` (`predicates/unify_2/tests.lgt`). -/
theorem iso_unify_2_10 {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle
      (.unify (.apply "f" [(.fvar "X"), one]) (.apply "f" [(.apply "a" [(.fvar "X")])]))
      env
      (.normal []) := by
  refine PrologEval.unify_fail _ _ _ ?_
  simp [applyBindings, matchPattern, one]

/-- Source: Logtalk ISO test `iso_unify_2_11` (`predicates/unify_2/tests.lgt`). -/
theorem iso_unify_2_11 {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle
      (.unify
        (.apply "f" [(.fvar "X"), (.fvar "Y"), (.fvar "X")])
        (.apply "f" [(.apply "a" [(.fvar "X")]), (.apply "a" [(.fvar "Y")]), (.fvar "Y"), two]))
      env
      (.normal []) := by
  refine PrologEval.unify_fail _ _ _ ?_
  simp [applyBindings, matchPattern, two]

/-- Source: Logtalk ISO test `iso_unify_2_12` (`predicates/unify_2/tests.lgt`). -/
theorem iso_unify_2_12 {oracle : EvalOracle} :
    PrologEval oracle (.unify (.fvar "X") (.apply "a" [(.fvar "X")])) []
      (.normal [[("X", .apply "a" [(.fvar "X")])]]) := by
  refine PrologEval.unify_succ _ _ _ _ ?_
  simp [applyBindings, matchPattern]

/-- Source: Logtalk ISO test `iso_unify_2_13` (`predicates/unify_2/tests.lgt`). -/
theorem iso_unify_2_13 {oracle : EvalOracle} :
    PrologEval oracle
      (.unify (.apply "f" [(.fvar "X"), one]) (.apply "f" [(.apply "a" [(.fvar "X")]), two]))
      []
      (.normal []) := by
  refine PrologEval.unify_fail _ _ _ ?_
  native_decide

/-- Source: Logtalk ISO test `iso_unify_2_14` (`predicates/unify_2/tests.lgt`). -/
theorem iso_unify_2_14 {oracle : EvalOracle} :
    PrologEval oracle
      (.unify
        (.apply "f" [one, (.fvar "X"), one])
        (.apply "f" [two, (.apply "a" [(.fvar "X")]), two]))
      []
      (.normal []) := by
  refine PrologEval.unify_fail _ _ _ ?_
  native_decide

/-- Source: Logtalk ISO test `iso_unify_2_15` (`predicates/unify_2/tests.lgt`). -/
theorem iso_unify_2_15 {oracle : EvalOracle} :
    PrologEval oracle
      (.unify
        (.apply "f" [one, (.fvar "X")])
        (.apply "f" [two, (.apply "a" [(.fvar "X")])]))
      []
      (.normal []) := by
  refine PrologEval.unify_fail _ _ _ ?_
  native_decide

/-- Source: Logtalk ISO test `iso_unify_2_16` (`predicates/unify_2/tests.lgt`). -/
theorem iso_unify_2_16 {oracle : EvalOracle} :
    PrologEval oracle
      (.unify
        (.apply "f" [(.fvar "X"), (.fvar "Y"), (.fvar "X"), one])
        (.apply "f" [(.apply "a" [(.fvar "X")]), (.apply "a" [(.fvar "Y")]), (.fvar "Y"), two]))
      []
      (.normal []) := by
  refine PrologEval.unify_fail _ _ _ ?_
  native_decide

/-! ## \=/2 -/

/-- Source-aligned positive fixture: distinct constants are not unifiable (`iso_not_unifiable_2_06`). -/
theorem iso_not_unifiable_2_06_like {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.notUnify one two) env (.normal [env]) := by
  refine PrologEval.notUnify_succ _ _ _ ?_
  simp [applyBindings, matchPattern, one, two]

/-- Alias theorem for ISO test id `iso_not_unifiable_2_06`. -/
theorem iso_not_unifiable_2_06 {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.notUnify one two) env (.normal [env]) :=
  iso_not_unifiable_2_06_like (oracle := oracle) (env := env)

/-- Source-aligned negative fixture: variable and constant are unifiable (`iso_not_unifiable_2_02`). -/
theorem iso_not_unifiable_2_02_like {oracle : EvalOracle} :
    PrologEval oracle (.notUnify (.fvar "X") aConst) [] (.normal []) := by
  refine PrologEval.notUnify_fail _ _ _ [("X", aConst)] [] ?_
  simp [applyBindings, matchPattern, aConst]

/-- Alias theorem for ISO test id `iso_not_unifiable_2_02`. -/
theorem iso_not_unifiable_2_02 {oracle : EvalOracle} :
    PrologEval oracle (.notUnify (.fvar "X") aConst) [] (.normal []) :=
  iso_not_unifiable_2_02_like (oracle := oracle)

/-- Source: Logtalk ISO test `iso_not_unifiable_2_01` (`predicates/not_unifiable_2/tests.lgt`). -/
theorem iso_not_unifiable_2_01 {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.notUnify one one) env (.normal []) := by
  refine PrologEval.notUnify_fail _ _ _ [] [] ?_
  simp [applyBindings, matchPattern, one, matchArgs]

/-- Source: Logtalk ISO test `iso_not_unifiable_2_03` (`predicates/not_unifiable_2/tests.lgt`). -/
theorem iso_not_unifiable_2_03 {oracle : EvalOracle} :
    PrologEval oracle (.notUnify (.fvar "X") (.fvar "Y")) []
      (.normal []) := by
  refine PrologEval.notUnify_fail _ _ _ [("X", .fvar "Y")] [] ?_
  simp [applyBindings, matchPattern]

/-- Source: Logtalk ISO test `iso_not_unifiable_2_04` (`predicates/not_unifiable_2/tests.lgt`). -/
theorem iso_not_unifiable_2_04 {oracle : EvalOracle} :
    PrologEval oracle (.notUnify (.fvar "U") (.fvar "V")) []
      (.normal []) := by
  refine PrologEval.notUnify_fail _ _ _ [("U", .fvar "V")] [] ?_
  simp [applyBindings, matchPattern]

/-- Source: Logtalk ISO test `iso_not_unifiable_2_07` (`predicates/not_unifiable_2/tests.lgt`). -/
theorem iso_not_unifiable_2_07 {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.notUnify one oneFloat) env (.normal [env]) := by
  refine PrologEval.notUnify_succ _ _ _ ?_
  simp [applyBindings, matchPattern, one, oneFloat]

/-- Source: Logtalk ISO test `iso_not_unifiable_2_08` (`predicates/not_unifiable_2/tests.lgt`). -/
theorem iso_not_unifiable_2_08 {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle
      (.notUnify (.apply "g" [(.fvar "X")]) (.apply "f" [(.apply "f" [(.fvar "X")])]))
      env
      (.normal [env]) := by
  refine PrologEval.notUnify_succ _ _ _ ?_
  simp [applyBindings, matchPattern]

/-- Source: Logtalk ISO test `iso_not_unifiable_2_09` (`predicates/not_unifiable_2/tests.lgt`). -/
theorem iso_not_unifiable_2_09 {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle
      (.notUnify (.apply "f" [(.fvar "X"), one]) (.apply "f" [(.apply "a" [(.fvar "X")])]))
      env
      (.normal [env]) := by
  refine PrologEval.notUnify_succ _ _ _ ?_
  simp [applyBindings, matchPattern, one]

/-- Source: Logtalk ISO test `iso_not_unifiable_2_10` (`predicates/not_unifiable_2/tests.lgt`). -/
theorem iso_not_unifiable_2_10 {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle
      (.notUnify
        (.apply "f" [(.fvar "X"), (.fvar "Y"), (.fvar "X")])
        (.apply "f" [(.apply "a" [(.fvar "X")]), (.apply "a" [(.fvar "Y")]), (.fvar "Y"), two]))
      env
      (.normal [env]) := by
  refine PrologEval.notUnify_succ _ _ _ ?_
  simp [applyBindings, matchPattern, two]

/-- Source: Logtalk ISO test `iso_not_unifiable_2_11` (`predicates/not_unifiable_2/tests.lgt`). -/
theorem iso_not_unifiable_2_11 {oracle : EvalOracle} :
    PrologEval oracle (.notUnify (.fvar "X") (.apply "a" [(.fvar "X")])) []
      (.normal []) := by
  refine PrologEval.notUnify_fail _ _ _ [("X", .apply "a" [(.fvar "X")])] [] ?_
  simp [applyBindings, matchPattern]

/-- Source: Logtalk ISO test `iso_not_unifiable_2_12` (`predicates/not_unifiable_2/tests.lgt`). -/
theorem iso_not_unifiable_2_12 {oracle : EvalOracle} :
    PrologEval oracle
      (.notUnify (.apply "f" [(.fvar "X"), one]) (.apply "f" [(.apply "a" [(.fvar "X")]), two]))
      []
      (.normal [[]]) := by
  refine PrologEval.notUnify_succ _ _ _ ?_
  native_decide

/-- Source: Logtalk ISO test `iso_not_unifiable_2_13` (`predicates/not_unifiable_2/tests.lgt`). -/
theorem iso_not_unifiable_2_13 {oracle : EvalOracle} :
    PrologEval oracle
      (.notUnify
        (.apply "f" [one, (.fvar "X"), one])
        (.apply "f" [two, (.apply "a" [(.fvar "X")]), two]))
      []
      (.normal [[]]) := by
  refine PrologEval.notUnify_succ _ _ _ ?_
  native_decide

/-- Source: Logtalk ISO test `iso_not_unifiable_2_14` (`predicates/not_unifiable_2/tests.lgt`). -/
theorem iso_not_unifiable_2_14 {oracle : EvalOracle} :
    PrologEval oracle
      (.notUnify
        (.apply "f" [one, (.fvar "X")])
        (.apply "f" [two, (.apply "a" [(.fvar "X")])]))
      []
      (.normal [[]]) := by
  refine PrologEval.notUnify_succ _ _ _ ?_
  native_decide

/-- Source: Logtalk ISO test `iso_not_unifiable_2_15` (`predicates/not_unifiable_2/tests.lgt`). -/
theorem iso_not_unifiable_2_15 {oracle : EvalOracle} :
    PrologEval oracle
      (.notUnify
        (.apply "f" [(.fvar "X"), (.fvar "Y"), (.fvar "X"), one])
        (.apply "f" [(.apply "a" [(.fvar "X")]), (.apply "a" [(.fvar "Y")]), (.fvar "Y"), two]))
      []
      (.normal [[]]) := by
  refine PrologEval.notUnify_succ _ _ _ ?_
  native_decide

/-! ## Env-Aware Unification Fixtures -/

/-- Pre-bound conflict: `(X = 1, X = 2)` fails under env-aware unification. -/
theorem unify_prebound_conflict_fail {oracle : EvalOracle} :
    PrologEval oracle
      (.conj (.unify (.fvar "X") one) (.unify (.fvar "X") two))
      []
      (.normal []) := by
  have h1 : PrologEval oracle (.unify (.fvar "X") one) [] (.normal [[("X", one)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, one]
  have h2 : PrologEval oracle (.unify (.fvar "X") two) [("X", one)] (.normal []) := by
    refine PrologEval.unify_fail _ _ _ ?_
    simp [applyBindings, matchPattern, one, two]
  refine PrologEval.conj_normal _ _ [] [[("X", one)]] [([("X", one)], [])] h1 ?_ ?_
  · simp
  · intro p hp
    simp at hp
    rw [hp]
    exact h2

/-- Pre-bound consistency: `(X = 1, X = 1)` succeeds with `X = 1`. -/
theorem unify_prebound_consistent_succeed {oracle : EvalOracle} :
    PrologEval oracle
      (.conj (.unify (.fvar "X") one) (.unify (.fvar "X") one))
      []
      (.normal [[("X", one)]]) := by
  have h1 : PrologEval oracle (.unify (.fvar "X") one) [] (.normal [[("X", one)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, one]
  have h2 : PrologEval oracle (.unify (.fvar "X") one) [("X", one)] (.normal [[("X", one)]]) := by
    have hmem : [] ∈ matchPattern (applyBindings [("X", one)] (.fvar "X"))
        (applyBindings [("X", one)] one) := by
      simp [one, applyBindings, matchPattern, matchArgs]
    simpa using (PrologEval.unify_succ (.fvar "X") one [("X", one)] [] hmem)
  refine PrologEval.conj_normal _ _ [] [[("X", one)]] [([("X", one)], [[("X", one)]])] h1 ?_ ?_
  · simp
  · intro p hp
    simp at hp
    rw [hp]
    exact h2

/-! ### Additional env-aware chains -/

/-- Chain consistency: `((X = 1, X = 1), X = 1)` succeeds. -/
theorem unify_prebound_chain_consistent_three {oracle : EvalOracle} :
    PrologEval oracle
      (.conj
        (.conj (.unify (.fvar "X") one) (.unify (.fvar "X") one))
        (.unify (.fvar "X") one))
      []
      (.normal [[("X", one)]]) := by
  have h12 : PrologEval oracle
      (.conj (.unify (.fvar "X") one) (.unify (.fvar "X") one))
      []
      (.normal [[("X", one)]]) :=
    unify_prebound_consistent_succeed (oracle := oracle)
  have h3 : PrologEval oracle (.unify (.fvar "X") one) [("X", one)]
      (.normal [[("X", one)]]) := by
    have hmem : [] ∈ matchPattern (applyBindings [("X", one)] (.fvar "X"))
        (applyBindings [("X", one)] one) := by
      simp [one, applyBindings, matchPattern, matchArgs]
    simpa using (PrologEval.unify_succ (.fvar "X") one [("X", one)] [] hmem)
  refine PrologEval.conj_normal _ _ [] [[("X", one)]]
    [([("X", one)], [[("X", one)]])] h12 ?_ ?_
  · simp
  · intro p hp
    simp at hp
    rw [hp]
    exact h3

/-- Chain conflict: `((X = 1, X = 1), X = 2)` fails. -/
theorem unify_prebound_chain_conflict_late {oracle : EvalOracle} :
    PrologEval oracle
      (.conj
        (.conj (.unify (.fvar "X") one) (.unify (.fvar "X") one))
        (.unify (.fvar "X") two))
      []
      (.normal []) := by
  have h12 : PrologEval oracle
      (.conj (.unify (.fvar "X") one) (.unify (.fvar "X") one))
      []
      (.normal [[("X", one)]]) :=
    unify_prebound_consistent_succeed (oracle := oracle)
  have h3 : PrologEval oracle (.unify (.fvar "X") two) [("X", one)] (.normal []) := by
    refine PrologEval.unify_fail _ _ _ ?_
    simp [applyBindings, matchPattern, one, two]
  refine PrologEval.conj_normal _ _ [] [[("X", one)]]
    [([("X", one)], [])] h12 ?_ ?_
  · simp
  · intro p hp
    simp at hp
    rw [hp]
    exact h3

/-- Cross-variable success under env-aware propagation: `X=1, (Y=X, Y=1)`. -/
theorem unify_prebound_crossvar_consistent {oracle : EvalOracle} :
    PrologEval oracle
      (.conj
        (.unify (.fvar "X") one)
        (.conj (.unify (.fvar "Y") (.fvar "X")) (.unify (.fvar "Y") one)))
      []
      (.normal [[("X", one), ("Y", one)]]) := by
  have hx : PrologEval oracle (.unify (.fvar "X") one) [] (.normal [[("X", one)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, one]
  have hyx : PrologEval oracle (.unify (.fvar "Y") (.fvar "X")) [("X", one)]
      (.normal [[("X", one), ("Y", one)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, one]
  have hy1 : PrologEval oracle (.unify (.fvar "Y") one) [("X", one), ("Y", one)]
      (.normal [[("X", one), ("Y", one)]]) := by
    have hmem : [] ∈ matchPattern (applyBindings [("X", one), ("Y", one)] (.fvar "Y"))
        (applyBindings [("X", one), ("Y", one)] one) := by
      simp [one, applyBindings, matchPattern, matchArgs]
    simpa using (PrologEval.unify_succ (.fvar "Y") one [("X", one), ("Y", one)] [] hmem)
  have hinner : PrologEval oracle
      (.conj (.unify (.fvar "Y") (.fvar "X")) (.unify (.fvar "Y") one))
      [("X", one)]
      (.normal [[("X", one), ("Y", one)]]) := by
    refine PrologEval.conj_normal _ _ [("X", one)] [[("X", one), ("Y", one)]]
      [([("X", one), ("Y", one)], [[("X", one), ("Y", one)]])] hyx ?_ ?_
    · simp
    · intro p hp
      simp at hp
      rw [hp]
      exact hy1
  refine PrologEval.conj_normal _ _ [] [[("X", one)]]
    [([("X", one)], [[("X", one), ("Y", one)]])] hx ?_ ?_
  · simp
  · intro p hp
    simp at hp
    rw [hp]
    exact hinner

/-- Cross-variable conflict under env-aware propagation: `X=1, (Y=X, Y=2)` fails. -/
theorem unify_prebound_crossvar_conflict {oracle : EvalOracle} :
    PrologEval oracle
      (.conj
        (.unify (.fvar "X") one)
        (.conj (.unify (.fvar "Y") (.fvar "X")) (.unify (.fvar "Y") two)))
      []
      (.normal []) := by
  have hx : PrologEval oracle (.unify (.fvar "X") one) [] (.normal [[("X", one)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, one]
  have hyx : PrologEval oracle (.unify (.fvar "Y") (.fvar "X")) [("X", one)]
      (.normal [[("X", one), ("Y", one)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, one]
  have hy2 : PrologEval oracle (.unify (.fvar "Y") two) [("X", one), ("Y", one)]
      (.normal []) := by
    refine PrologEval.unify_fail _ _ _ ?_
    simp [applyBindings, matchPattern, one, two]
  have hinner : PrologEval oracle
      (.conj (.unify (.fvar "Y") (.fvar "X")) (.unify (.fvar "Y") two))
      [("X", one)]
      (.normal []) := by
    refine PrologEval.conj_normal _ _ [("X", one)] [[("X", one), ("Y", one)]]
      [([("X", one), ("Y", one)], [])] hyx ?_ ?_
    · simp
    · intro p hp
      simp at hp
      rw [hp]
      exact hy2
  refine PrologEval.conj_normal _ _ [] [[("X", one)]] [([("X", one)], [])] hx ?_ ?_
  · simp
  · intro p hp
    simp at hp
    rw [hp]
    exact hinner

/-- Env-aware `\\=/2` success after binding: `(X=1, X \\= 2)` succeeds. -/
theorem notUnify_prebound_conflict_succeeds {oracle : EvalOracle} :
    PrologEval oracle
      (.conj (.unify (.fvar "X") one) (.notUnify (.fvar "X") two))
      []
      (.normal [[("X", one)]]) := by
  have h1 : PrologEval oracle (.unify (.fvar "X") one) [] (.normal [[("X", one)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, one]
  have h2 : PrologEval oracle (.notUnify (.fvar "X") two) [("X", one)]
      (.normal [[("X", one)]]) := by
    refine PrologEval.notUnify_succ _ _ _ ?_
    simp [applyBindings, matchPattern, one, two]
  refine PrologEval.conj_normal _ _ [] [[("X", one)]]
    [([("X", one)], [[("X", one)]])] h1 ?_ ?_
  · simp
  · intro p hp
    simp at hp
    rw [hp]
    exact h2

/-- Env-aware `\\=/2` failure after binding: `(X=1, X \\= 1)` fails. -/
theorem notUnify_prebound_consistent_fails {oracle : EvalOracle} :
    PrologEval oracle
      (.conj (.unify (.fvar "X") one) (.notUnify (.fvar "X") one))
      []
      (.normal []) := by
  have h1 : PrologEval oracle (.unify (.fvar "X") one) [] (.normal [[("X", one)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, one]
  have h2 : PrologEval oracle (.notUnify (.fvar "X") one) [("X", one)]
      (.normal []) := by
    refine PrologEval.notUnify_fail _ _ _ [] [] ?_
    simp [applyBindings, matchPattern, one, matchArgs]
  refine PrologEval.conj_normal _ _ [] [[("X", one)]]
    [([("X", one)], [])] h1 ?_ ?_
  · simp
  · intro p hp
    simp at hp
    rw [hp]
    exact h2

/-- Env-aware disjunction+filter: `((X=1;X=2), X=2)` yields exactly `X=2`. -/
theorem unify_prebound_disj_then_filter_success {oracle : EvalOracle} :
    PrologEval oracle
      (.conj
        (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two))
        (.unify (.fvar "X") two))
      []
      (.normal [[("X", two)]]) := by
  have h1 : PrologEval oracle (.unify (.fvar "X") one) [] (.normal [[("X", one)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, one]
  have h2 : PrologEval oracle (.unify (.fvar "X") two) [] (.normal [[("X", two)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, two]
  have hdisj : PrologEval oracle
      (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two))
      []
      (.normal [[("X", one)], [("X", two)]]) := by
    simpa using (PrologEval.disj_normal
      (.unify (.fvar "X") one) (.unify (.fvar "X") two)
      [] [[("X", one)]] [[("X", two)]] h1 h2)
  have hf1 : PrologEval oracle (.unify (.fvar "X") two) [("X", one)] (.normal []) := by
    refine PrologEval.unify_fail _ _ _ ?_
    simp [applyBindings, matchPattern, one, two]
  have hf2 : PrologEval oracle (.unify (.fvar "X") two) [("X", two)] (.normal [[("X", two)]]) := by
    have hmem : [] ∈ matchPattern (applyBindings [("X", two)] (.fvar "X"))
        (applyBindings [("X", two)] two) := by
      simp [applyBindings, matchPattern, two, matchArgs]
    simpa using (PrologEval.unify_succ (.fvar "X") two [("X", two)] [] hmem)
  refine PrologEval.conj_normal _ _ [] [[("X", one)], [("X", two)]]
    [([("X", one)], []), ([("X", two)], [[("X", two)]])] hdisj ?_ ?_
  · simp
  · intro p hp
    simp at hp
    rcases hp with hp | hp
    · rw [hp]
      exact hf1
    · rw [hp]
      exact hf2

/-- Env-aware disjunction+filter failure: `((X=1;X=2), X=3)` fails. -/
theorem unify_prebound_disj_then_filter_fail {oracle : EvalOracle} :
    PrologEval oracle
      (.conj
        (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two))
        (.unify (.fvar "X") three))
      []
      (.normal []) := by
  have h1 : PrologEval oracle (.unify (.fvar "X") one) [] (.normal [[("X", one)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, one]
  have h2 : PrologEval oracle (.unify (.fvar "X") two) [] (.normal [[("X", two)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, two]
  have hdisj : PrologEval oracle
      (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two))
      []
      (.normal [[("X", one)], [("X", two)]]) := by
    simpa using (PrologEval.disj_normal
      (.unify (.fvar "X") one) (.unify (.fvar "X") two)
      [] [[("X", one)]] [[("X", two)]] h1 h2)
  have hf1 : PrologEval oracle (.unify (.fvar "X") three) [("X", one)] (.normal []) := by
    refine PrologEval.unify_fail _ _ _ ?_
    simp [applyBindings, matchPattern, one, three]
  have hf2 : PrologEval oracle (.unify (.fvar "X") three) [("X", two)] (.normal []) := by
    refine PrologEval.unify_fail _ _ _ ?_
    simp [applyBindings, matchPattern, two, three]
  refine PrologEval.conj_normal _ _ [] [[("X", one)], [("X", two)]]
    [([("X", one)], []), ([("X", two)], [])] hdisj ?_ ?_
  · simp
  · intro p hp
    simp at hp
    rcases hp with hp | hp
    · rw [hp]
      exact hf1
    · rw [hp]
      exact hf2

/-! ### Additional env-aware variable-sharing chains (X,Y,Z) -/

/-- Base XYZ binding chain: `X=1, (Y=X, Z=Y)` yields all three bound to `1`. -/
theorem unify_prebound_xyz_bind_all {oracle : EvalOracle} :
    PrologEval oracle
      (.conj (.unify (.fvar "X") one)
        (.conj (.unify (.fvar "Y") (.fvar "X")) (.unify (.fvar "Z") (.fvar "Y"))))
      []
      (.normal [[("X", one), ("Y", one), ("Z", one)]]) := by
  have hx : PrologEval oracle (.unify (.fvar "X") one) [] (.normal [[("X", one)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, one]
  have hyx : PrologEval oracle (.unify (.fvar "Y") (.fvar "X")) [("X", one)]
      (.normal [[("X", one), ("Y", one)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, one]
  have hzy : PrologEval oracle (.unify (.fvar "Z") (.fvar "Y")) [("X", one), ("Y", one)]
      (.normal [[("X", one), ("Y", one), ("Z", one)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, one]
  have hinner : PrologEval oracle
      (.conj (.unify (.fvar "Y") (.fvar "X")) (.unify (.fvar "Z") (.fvar "Y")))
      [("X", one)]
      (.normal [[("X", one), ("Y", one), ("Z", one)]]) := by
    refine PrologEval.conj_normal _ _ [("X", one)] [[("X", one), ("Y", one)]]
      [([("X", one), ("Y", one)], [[("X", one), ("Y", one), ("Z", one)]])] hyx ?_ ?_
    · simp
    · intro p hp
      simp at hp
      rw [hp]
      exact hzy
  refine PrologEval.conj_normal _ _ [] [[("X", one)]]
    [([("X", one)], [[("X", one), ("Y", one), ("Z", one)]])] hx ?_ ?_
  · simp
  · intro p hp
    simp at hp
    rw [hp]
    exact hinner

/-- XYZ consistency: `(..., Z=1)` keeps the same XYZ binding. -/
theorem unify_prebound_xyz_consistent_final {oracle : EvalOracle} :
    PrologEval oracle
      (.conj
        (.conj (.unify (.fvar "X") one)
          (.conj (.unify (.fvar "Y") (.fvar "X")) (.unify (.fvar "Z") (.fvar "Y"))))
        (.unify (.fvar "Z") one))
      []
      (.normal [[("X", one), ("Y", one), ("Z", one)]]) := by
  have hxyz : PrologEval oracle
      (.conj (.unify (.fvar "X") one)
        (.conj (.unify (.fvar "Y") (.fvar "X")) (.unify (.fvar "Z") (.fvar "Y"))))
      []
      (.normal [[("X", one), ("Y", one), ("Z", one)]]) :=
    unify_prebound_xyz_bind_all (oracle := oracle)
  have hz1 : PrologEval oracle (.unify (.fvar "Z") one) [("X", one), ("Y", one), ("Z", one)]
      (.normal [[("X", one), ("Y", one), ("Z", one)]]) := by
    have hmem : [] ∈ matchPattern (applyBindings [("X", one), ("Y", one), ("Z", one)] (.fvar "Z"))
        (applyBindings [("X", one), ("Y", one), ("Z", one)] one) := by
      simp [applyBindings, matchPattern, one, matchArgs]
    simpa using (PrologEval.unify_succ (.fvar "Z") one [("X", one), ("Y", one), ("Z", one)] [] hmem)
  refine PrologEval.conj_normal _ _ [] [[("X", one), ("Y", one), ("Z", one)]]
    [([("X", one), ("Y", one), ("Z", one)], [[("X", one), ("Y", one), ("Z", one)]])] hxyz ?_ ?_
  · simp
  · intro p hp
    simp at hp
    rw [hp]
    exact hz1

/-- XYZ late conflict: `(..., Z=2)` fails. -/
theorem unify_prebound_xyz_conflict_final {oracle : EvalOracle} :
    PrologEval oracle
      (.conj
        (.conj (.unify (.fvar "X") one)
          (.conj (.unify (.fvar "Y") (.fvar "X")) (.unify (.fvar "Z") (.fvar "Y"))))
        (.unify (.fvar "Z") two))
      []
      (.normal []) := by
  have hxyz : PrologEval oracle
      (.conj (.unify (.fvar "X") one)
        (.conj (.unify (.fvar "Y") (.fvar "X")) (.unify (.fvar "Z") (.fvar "Y"))))
      []
      (.normal [[("X", one), ("Y", one), ("Z", one)]]) :=
    unify_prebound_xyz_bind_all (oracle := oracle)
  have hz2 : PrologEval oracle (.unify (.fvar "Z") two) [("X", one), ("Y", one), ("Z", one)]
      (.normal []) := by
    refine PrologEval.unify_fail _ _ _ ?_
    simp [applyBindings, matchPattern, one, two]
  refine PrologEval.conj_normal _ _ [] [[("X", one), ("Y", one), ("Z", one)]]
    [([("X", one), ("Y", one), ("Z", one)], [])] hxyz ?_ ?_
  · simp
  · intro p hp
    simp at hp
    rw [hp]
    exact hz2

/-- XYZ with `\\=/2`: `(..., Z \\= 2)` succeeds. -/
theorem notUnify_prebound_xyz_success {oracle : EvalOracle} :
    PrologEval oracle
      (.conj
        (.conj (.unify (.fvar "X") one)
          (.conj (.unify (.fvar "Y") (.fvar "X")) (.unify (.fvar "Z") (.fvar "Y"))))
        (.notUnify (.fvar "Z") two))
      []
      (.normal [[("X", one), ("Y", one), ("Z", one)]]) := by
  have hxyz : PrologEval oracle
      (.conj (.unify (.fvar "X") one)
        (.conj (.unify (.fvar "Y") (.fvar "X")) (.unify (.fvar "Z") (.fvar "Y"))))
      []
      (.normal [[("X", one), ("Y", one), ("Z", one)]]) :=
    unify_prebound_xyz_bind_all (oracle := oracle)
  have hz2 : PrologEval oracle (.notUnify (.fvar "Z") two) [("X", one), ("Y", one), ("Z", one)]
      (.normal [[("X", one), ("Y", one), ("Z", one)]]) := by
    refine PrologEval.notUnify_succ _ _ _ ?_
    simp [applyBindings, matchPattern, one, two]
  refine PrologEval.conj_normal _ _ [] [[("X", one), ("Y", one), ("Z", one)]]
    [([("X", one), ("Y", one), ("Z", one)], [[("X", one), ("Y", one), ("Z", one)]])] hxyz ?_ ?_
  · simp
  · intro p hp
    simp at hp
    rw [hp]
    exact hz2

/-- XYZ with `\\=/2`: `(..., Z \\= 1)` fails. -/
theorem notUnify_prebound_xyz_fail {oracle : EvalOracle} :
    PrologEval oracle
      (.conj
        (.conj (.unify (.fvar "X") one)
          (.conj (.unify (.fvar "Y") (.fvar "X")) (.unify (.fvar "Z") (.fvar "Y"))))
        (.notUnify (.fvar "Z") one))
      []
      (.normal []) := by
  have hxyz : PrologEval oracle
      (.conj (.unify (.fvar "X") one)
        (.conj (.unify (.fvar "Y") (.fvar "X")) (.unify (.fvar "Z") (.fvar "Y"))))
      []
      (.normal [[("X", one), ("Y", one), ("Z", one)]]) :=
    unify_prebound_xyz_bind_all (oracle := oracle)
  have hz1 : PrologEval oracle (.notUnify (.fvar "Z") one) [("X", one), ("Y", one), ("Z", one)]
      (.normal []) := by
    refine PrologEval.notUnify_fail _ _ _ [] [] ?_
    simp [applyBindings, matchPattern, one, matchArgs]
  refine PrologEval.conj_normal _ _ [] [[("X", one), ("Y", one), ("Z", one)]]
    [([("X", one), ("Y", one), ("Z", one)], [])] hxyz ?_ ?_
  · simp
  · intro p hp
    simp at hp
    rw [hp]
    exact hz1

/-- XYZ chain after disjunction filtering: `((X=1;X=2),X=2), Y=X, Z=Y` yields all `2`s. -/
theorem unify_prebound_xyz_after_disj_filter_success {oracle : EvalOracle} :
    PrologEval oracle
      (.conj
        (.conj
          (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two))
          (.unify (.fvar "X") two))
        (.conj (.unify (.fvar "Y") (.fvar "X")) (.unify (.fvar "Z") (.fvar "Y"))))
      []
      (.normal [[("X", two), ("Y", two), ("Z", two)]]) := by
  have hx2 : PrologEval oracle
      (.conj
        (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two))
        (.unify (.fvar "X") two))
      []
      (.normal [[("X", two)]]) :=
    unify_prebound_disj_then_filter_success (oracle := oracle)
  have hyx : PrologEval oracle (.unify (.fvar "Y") (.fvar "X")) [("X", two)]
      (.normal [[("X", two), ("Y", two)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, two]
  have hzy : PrologEval oracle (.unify (.fvar "Z") (.fvar "Y")) [("X", two), ("Y", two)]
      (.normal [[("X", two), ("Y", two), ("Z", two)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, two]
  have hinner : PrologEval oracle
      (.conj (.unify (.fvar "Y") (.fvar "X")) (.unify (.fvar "Z") (.fvar "Y")))
      [("X", two)]
      (.normal [[("X", two), ("Y", two), ("Z", two)]]) := by
    refine PrologEval.conj_normal _ _ [("X", two)] [[("X", two), ("Y", two)]]
      [([("X", two), ("Y", two)], [[("X", two), ("Y", two), ("Z", two)]])] hyx ?_ ?_
    · simp
    · intro p hp
      simp at hp
      rw [hp]
      exact hzy
  refine PrologEval.conj_normal _ _ [] [[("X", two)]]
    [([("X", two)], [[("X", two), ("Y", two), ("Z", two)]])] hx2 ?_ ?_
  · simp
  · intro p hp
    simp at hp
    rw [hp]
    exact hinner

/-! ## findall/3 -/

/-- Source-aligned positive fixture: collect two generated answers (`iso_findall_3_01`). -/
theorem iso_findall_3_01_like {oracle : EvalOracle} :
    PrologEval oracle
      (.findall "X" (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two)))
      []
      (.normal [[("X", Pattern.mkList [one, two])]]) := by
  have h1 : PrologEval oracle (.unify (.fvar "X") one) []
      (.normal [[("X", one)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, one]
  have h2 : PrologEval oracle (.unify (.fvar "X") two) []
      (.normal [[("X", two)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, two]
  have hdisj : PrologEval oracle
      (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two))
      []
      (.normal ([[("X", one)]] ++ [[("X", two)]])) :=
    PrologEval.disj_normal _ _ _ _ _ h1 h2
  refine PrologEval.findall_eval "X"
      (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two))
      []
      (.normal ([[("X", one)]] ++ [[("X", two)]]))
      [one, two]
      hdisj ?_
  simp [PrologEvalResult.answers, PEnv.lookup, one, two]

/-- Alias theorem for ISO test id `iso_findall_3_01`. -/
theorem iso_findall_3_01 {oracle : EvalOracle} :
    PrologEval oracle
      (.findall "X" (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two)))
      []
      (.normal [[("X", Pattern.mkList [one, two])]]) :=
  iso_findall_3_01_like (oracle := oracle)

/-- Source-aligned negative fixture: `findall(_, fail, L)` collects `[]` (`iso_findall_3_03`). -/
theorem iso_findall_3_03_like {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.findall "X" .fail) env
      (.normal [env.insert "X" (Pattern.mkList [])]) := by
  refine PrologEval.findall_eval "X" .fail env (.normal []) [] ?_ ?_
  · exact PrologEval.fail_eval env
  · simp [PrologEvalResult.answers]

/-- Alias theorem for ISO test id `iso_findall_3_03`. -/
theorem iso_findall_3_03 {oracle : EvalOracle} :
    PrologEval oracle (.findall "X" .fail) []
      (.normal [[("X", Pattern.mkList [])]]) := by
  simpa using (iso_findall_3_03_like (oracle := oracle) (env := []))

/-- Source-aligned positive fixture with duplicates (`iso_findall_3_04`). -/
theorem iso_findall_3_04_like {oracle : EvalOracle} :
    PrologEval oracle
      (.findall "X" (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") one)))
      []
      (.normal [[("X", Pattern.mkList [one, one])]]) := by
  have h1 : PrologEval oracle (.unify (.fvar "X") one) []
      (.normal [[("X", one)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, one]
  have hdisj : PrologEval oracle
      (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") one))
      []
      (.normal ([[("X", one)]] ++ [[("X", one)]])) :=
    PrologEval.disj_normal _ _ _ _ _ h1 h1
  refine PrologEval.findall_eval "X"
      (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") one))
      []
      (.normal ([[("X", one)]] ++ [[("X", one)]]))
      [one, one]
      hdisj ?_
  simp [PrologEvalResult.answers, PEnv.lookup, one]

/-- Source-aligned fixture for disjunction case producing `[1,2]`
(`iso_disjunction_2_05`) via `findall`. -/
theorem iso_disjunction_2_05_like {oracle : EvalOracle} :
    PrologEval oracle
      (.findall "X" (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two)))
      []
      (.normal [[("X", Pattern.mkList [one, two])]]) :=
  iso_findall_3_01_like (oracle := oracle)

/-- Alias theorem for ISO probe id `iso_disjunction_2_05`. -/
theorem iso_disjunction_2_05 {oracle : EvalOracle} :
    PrologEval oracle
      (.findall "X" (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two)))
      []
      (.normal [[("X", Pattern.mkList [one, two])]]) :=
  iso_disjunction_2_05_like (oracle := oracle)

/-- Alias theorem for ISO probe id `iso_findall_3_04`. -/
theorem iso_findall_3_04 {oracle : EvalOracle} :
    PrologEval oracle
      (.findall "X" (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") one)))
      []
      (.normal [[("X", Pattern.mkList [one, one])]]) :=
  iso_findall_3_04_like (oracle := oracle)

/-- Source-aligned ordering fixture (`iso_findall_3_05` witness):
`findall(X, (X = 2 ; X = 1), S)` yields `S = [2,1]`. -/
theorem iso_findall_3_05_order_like {oracle : EvalOracle} :
    PrologEval oracle
      (.findall "X" (.disj (.unify (.fvar "X") two) (.unify (.fvar "X") one)))
      []
      (.normal [[("X", Pattern.mkList [two, one])]]) := by
  have h2 : PrologEval oracle (.unify (.fvar "X") two) []
      (.normal [[("X", two)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, two]
  have h1 : PrologEval oracle (.unify (.fvar "X") one) []
      (.normal [[("X", one)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, one]
  have hdisj : PrologEval oracle
      (.disj (.unify (.fvar "X") two) (.unify (.fvar "X") one))
      []
      (.normal ([[("X", two)]] ++ [[("X", one)]])) :=
    PrologEval.disj_normal _ _ _ _ _ h2 h1
  refine PrologEval.findall_eval "X"
      (.disj (.unify (.fvar "X") two) (.unify (.fvar "X") one))
      []
      (.normal ([[("X", two)]] ++ [[("X", one)]]))
      [two, one]
      hdisj ?_
  simp [PrologEvalResult.answers, PEnv.lookup, one, two]

/-! ## Additional ISO-Aligned Control Fixtures -/

/-- Source-aligned positive fixture: `once(!)` succeeds once (`iso_once_1_01`). -/
theorem iso_once_1_01_cut_like {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.once .cut) env (.normal [env]) :=
  PrologEval.once_some .cut env (.cutThrown [env]) env []
    (PrologEval.cut_eval env) rfl

/-- Alias theorem for ISO test id `iso_once_1_01`. -/
theorem iso_once_1_01 {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.once .cut) env (.normal [env]) :=
  iso_once_1_01_cut_like (oracle := oracle) (env := env)

/-- Source-aligned positive fixture: `\+ (4 = 5)` succeeds (`iso_not_1_05`). -/
theorem iso_not_1_05_like {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.neg (.unify four five)) env (.normal [env]) := by
  have hu : PrologEval oracle (.unify four five) env (.normal []) := by
    refine PrologEval.unify_fail _ _ _ ?_
    simp [applyBindings, matchPattern, four, five]
  exact PrologEval.neg_succ (.unify four five) env (.normal []) hu rfl

/-- Alias theorem for ISO test id `iso_not_1_05`. -/
theorem iso_not_1_05 {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.neg (.unify four five)) env (.normal [env]) :=
  iso_not_1_05_like (oracle := oracle) (env := env)

/-! ## Extra Constructor-Level Negative Example -/

/-- Distinct constants mismatch in the matcher (constructor-level negative example). -/
theorem matcher_neg_distinct_constants :
    matchPattern aConst bConst = [] := by
  simp [matchPattern, aConst, bConst]

/-! ## cut and if-then-else constructor fixtures -/

/-- Constructor-level fixture: cut throws a cut signal with current env. -/
theorem cut_basic {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle .cut env (.cutThrown [env]) :=
  PrologEval.cut_eval env

/-- Constructor-level fixture: disjunction catches a cut thrown by left branch. -/
theorem disj_cut_catch {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.disj .cut .fail) env (.normal [env]) :=
  PrologEval.disj_g1_cut .cut .fail env [env] (PrologEval.cut_eval env)

/-- Constructor-level fixture: right disj branch cut propagates (`fail ; !`). -/
theorem disj_g2_cut_simple {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.disj .fail .cut) env (.cutThrown [env]) := by
  exact PrologEval.disj_g2_cut .fail .cut env [] [env]
    (PrologEval.fail_eval env) (PrologEval.cut_eval env)

/-- Boundary fixture: disjunction preserves left answers before rhs cut (`true ; !`). -/
theorem disj_g2_cut_with_prefix {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.disj .succeed .cut) env (.cutThrown [env, env]) := by
  exact PrologEval.disj_g2_cut .succeed .cut env [env] [env]
    (PrologEval.succeed_eval env) (PrologEval.cut_eval env)

/-- Constructor-level fixture: conjunction runs rhs and then propagates left-branch cut. -/
theorem conj_cut_then_true {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.conj .cut .succeed) env (.cutThrown [env]) :=
  PrologEval.conj_g1_cut .cut .succeed env [env] [(env, [env])]
    (PrologEval.cut_eval env) rfl
    (by
      intro p hp
      simp at hp
      rw [hp]
      exact PrologEval.succeed_eval env)

/-- Constructor-level fixture: if-then-else takes the `then` branch on `true`. -/
theorem ite_then_true_branch {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.ite .succeed .succeed .fail) env (.normal [env]) :=
  PrologEval.ite_then .succeed .succeed .fail env env []
    (.normal [env]) (.normal [env])
    (PrologEval.succeed_eval env) rfl (PrologEval.succeed_eval env)

/-- Constructor-level fixture: if-then-else takes the `else` branch on `fail`. -/
theorem ite_else_fallback_branch {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.ite .fail .fail .succeed) env (.normal [env]) :=
  PrologEval.ite_else .fail .fail .succeed env
    (.normal []) (.normal [env])
    (PrologEval.fail_eval env) rfl (PrologEval.succeed_eval env)

/-! ## Oracle-connected constructor fixtures (`spaceMatch`, `reduceCall`) -/

/-- Test oracle with fixed `spaceMatch` outputs and no `reduceCall` support. -/
def oracleSpaceConst (outs : List Pattern) : EvalOracle where
  space := { matchFacts := fun _ => [] }
  call := fun _ _ => False
  matchEval := fun _ _ outs' => outs' = outs

/-- Positive fixture: `spaceMatch` maps oracle outputs to `"Out"`-bound environments. -/
theorem spaceMatch_two_outs :
    PrologEval (oracleSpaceConst [aConst, bConst]) (.spaceMatch aConst bConst) []
      (.normal [[("Out", aConst)], [("Out", bConst)]]) := by
  refine PrologEval.spaceMatch_eval aConst bConst [] [aConst, bConst] ?_
  simp [oracleSpaceConst]

/-- Negative fixture: `spaceMatch` with empty oracle result has no answer envs. -/
theorem spaceMatch_empty :
    PrologEval (oracleSpaceConst []) (.spaceMatch aConst bConst) []
      (.normal []) := by
  refine PrologEval.spaceMatch_eval aConst bConst [] [] ?_
  simp [oracleSpaceConst]

/-- Test oracle with fixed `reduceCall` outputs and no `spaceMatch` support. -/
def oracleCallConst (expectedArgs outs : List Pattern) : EvalOracle where
  space := { matchFacts := fun _ => [] }
  call := fun args outs' => args = expectedArgs ∧ outs' = outs
  matchEval := fun _ _ _ => False

/-- Positive fixture: `reduceCall` maps oracle outputs to `"Out"`-bound environments. -/
theorem reduceCall_two_outs :
    PrologEval (oracleCallConst [aConst] [one, two]) (.reduceCall [aConst]) []
      (.normal [[("Out", one)], [("Out", two)]]) := by
  refine PrologEval.reduceCall_eval [aConst] [] [one, two] ?_
  simp [oracleCallConst]

/-- Negative fixture: `reduceCall` with empty output list yields no answers. -/
theorem reduceCall_empty :
    PrologEval (oracleCallConst [aConst] []) (.reduceCall [aConst]) []
      (.normal []) := by
  refine PrologEval.reduceCall_eval [aConst] [] [] ?_
  simp [oracleCallConst]

/-! ## Cut-Sensitive Conformance Fixture -/

/-- Source-aligned cut fixture (`iso_disjunction_2_02` shape):
`((!, fail) ; true)` must fail.

Proof sketch in current semantics:
1. `cut` throws cut with one answer.
2. conjunction continues with `fail` on that answer, producing zero answers while keeping cut.
3. disjunction catches the cut and yields zero answers (right branch pruned). -/
theorem iso_disjunction_2_02_like {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.disj (.conj .cut .fail) .succeed) env (.normal []) := by
  have hconj : PrologEval oracle (.conj .cut .fail) env (.cutThrown []) := by
    refine PrologEval.conj_g1_cut .cut .fail env [env] [(env, [])]
      (PrologEval.cut_eval env) ?_ ?_
    · rfl
    · intro p hp
      simp at hp
      rw [hp]
      exact PrologEval.fail_eval env
  exact PrologEval.disj_g1_cut (.conj .cut .fail) .succeed env [] hconj

/-- Alias theorem for ISO probe id `iso_disjunction_2_02`. -/
theorem iso_disjunction_2_02 {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.disj (.conj .cut .fail) .succeed) env (.normal []) :=
  iso_disjunction_2_02_like (oracle := oracle) (env := env)

/-- Source-aligned cut fixture (`iso_disjunction_2_04` shape):
`((X=1, !) ; X=2)` commits to `X=1`. -/
theorem iso_disjunction_2_04_like {oracle : EvalOracle} :
    PrologEval oracle
      (.disj (.conj (.unify (.fvar "X") one) .cut) (.unify (.fvar "X") two))
      []
      (.normal [[("X", one)]]) := by
  have hleft : PrologEval oracle (.conj (.unify (.fvar "X") one) .cut) []
      (.cutThrown [[("X", one)]]) := by
    have hu : PrologEval oracle (.unify (.fvar "X") one) [] (.normal [[("X", one)]]) := by
      refine PrologEval.unify_succ _ _ _ _ ?_
      simp [applyBindings, matchPattern, one]
    refine PrologEval.conj_g2_cut (.unify (.fvar "X") one) .cut [] [[("X", one)]]
      [] [("X", one)] [[("X", one)]] [] hu ?_ ?_ ?_
    · simp
    · intro p hp
      simp at hp
    · exact PrologEval.cut_eval [("X", one)]
  exact PrologEval.disj_g1_cut _ _ _ [[("X", one)]] hleft

/-- Alias theorem for ISO probe id `iso_disjunction_2_04`. -/
theorem iso_disjunction_2_04 {oracle : EvalOracle} :
    PrologEval oracle
      (.disj (.conj (.unify (.fvar "X") one) .cut) (.unify (.fvar "X") two))
      []
      (.normal [[("X", one)]]) :=
  iso_disjunction_2_04_like (oracle := oracle)

/-- Constructor-level fixture: rhs cut in conjunction propagates cut (`true, !`). -/
theorem conj_g2_cut_simple {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.conj .succeed .cut) env (.cutThrown [env]) := by
  refine PrologEval.conj_g2_cut .succeed .cut env [env] [] env [env] []
    (PrologEval.succeed_eval env) ?_ ?_ ?_
  · simp
  · intro p hp
    simp at hp
  · exact PrologEval.cut_eval env

/-- Constructor-level fixture: rhs cut in conjunction prunes suffix branches.
`(true ; true), !` yields one cut answer. -/
theorem conj_g2_cut_prunes_suffix {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.conj (.disj .succeed .succeed) .cut) env (.cutThrown [env]) := by
  have hdisj : PrologEval oracle (.disj .succeed .succeed) env (.normal [env, env]) :=
    PrologEval.disj_normal .succeed .succeed env [env] [env]
      (PrologEval.succeed_eval env) (PrologEval.succeed_eval env)
  refine PrologEval.conj_g2_cut (.disj .succeed .succeed) .cut env [env, env] [] env [env] [env]
    hdisj ?_ ?_ ?_
  · simp
  · intro p hp
    simp at hp
  · exact PrologEval.cut_eval env

/-- Constructor-level fixture: g1-cut plus rhs cut (`!, !`) still propagates one cut answer. -/
theorem conj_g1_cut_g2_cut_simple {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.conj .cut .cut) env (.cutThrown [env]) := by
  refine PrologEval.conj_g1_cut_g2_cut .cut .cut env [env] [] env [env] []
    (PrologEval.cut_eval env) ?_ ?_ ?_
  · simp
  · intro p hp
    simp at hp
  · exact PrologEval.cut_eval env

/-- Boundary fixture: disjunction catches left cut, then conjunction continues.
`((! ; true), true)` succeeds once. -/
theorem boundary_disj_cut_then_conj_true {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.conj (.disj .cut .succeed) .succeed) env (.normal [env]) := by
  have hdisj : PrologEval oracle (.disj .cut .succeed) env (.normal [env]) :=
    PrologEval.disj_g1_cut .cut .succeed env [env] (PrologEval.cut_eval env)
  refine PrologEval.conj_normal _ _ env [env] [(env, [env])] hdisj ?_ ?_
  · simp
  · intro p hp
    simp at hp
    rw [hp]
    exact PrologEval.succeed_eval env

/-! ## Backtracking/Ordering Boundary Fixtures -/

/-- Boundary fixture: disjunction returns answers in left-to-right order. -/
theorem boundary_disjunction_order_1_then_2 {oracle : EvalOracle} :
    PrologEval oracle (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two)) []
      (.normal [[("X", one)], [("X", two)]]) := by
  have h1 : PrologEval oracle (.unify (.fvar "X") one) [] (.normal [[("X", one)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, one]
  have h2 : PrologEval oracle (.unify (.fvar "X") two) [] (.normal [[("X", two)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, two]
  simpa using (PrologEval.disj_normal (.unify (.fvar "X") one) (.unify (.fvar "X") two)
    [] [[("X", one)]] [[("X", two)]] h1 h2)

/-- Boundary fixture: failing left disj branch still allows right branch answers. -/
theorem boundary_disjunction_fail_then_2 {oracle : EvalOracle} :
    PrologEval oracle (.disj .fail (.unify (.fvar "X") two)) []
      (.normal [[("X", two)]]) := by
  have h2 : PrologEval oracle (.unify (.fvar "X") two) [] (.normal [[("X", two)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, two]
  simpa using (PrologEval.disj_normal .fail (.unify (.fvar "X") two)
    [] [] [[("X", two)]] (PrologEval.fail_eval []) h2)

/-- Boundary fixture: nested disjunction with inner cut prunes later alternatives.
`findall(X, (X=1 ; ((X=2, !) ; X=3)), L)` yields `[1,2]`. -/
theorem boundary_nested_disj_cut_prunes_third_in_findall {oracle : EvalOracle} :
    PrologEval oracle
      (.findall "X"
        (.disj
          (.unify (.fvar "X") one)
          (.disj
            (.conj (.unify (.fvar "X") two) .cut)
            (.unify (.fvar "X") three))))
      []
      (.normal [[("X", Pattern.mkList [one, two])]]) := by
  have h1 : PrologEval oracle (.unify (.fvar "X") one) []
      (.normal [[("X", one)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, one]
  have h2 : PrologEval oracle (.unify (.fvar "X") two) []
      (.normal [[("X", two)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, two]
  have hconjCut : PrologEval oracle (.conj (.unify (.fvar "X") two) .cut) []
      (.cutThrown [[("X", two)]]) := by
    refine PrologEval.conj_g2_cut (.unify (.fvar "X") two) .cut [] [[("X", two)]]
      [] [("X", two)] [[("X", two)]] [] h2 ?_ ?_ ?_
    · simp
    · intro p hp
      simp at hp
    · exact PrologEval.cut_eval [("X", two)]
  have hinner : PrologEval oracle
      (.disj (.conj (.unify (.fvar "X") two) .cut) (.unify (.fvar "X") three))
      []
      (.normal [[("X", two)]]) :=
    PrologEval.disj_g1_cut _ _ _ [[("X", two)]] hconjCut
  have houter : PrologEval oracle
      (.disj
        (.unify (.fvar "X") one)
        (.disj
          (.conj (.unify (.fvar "X") two) .cut)
          (.unify (.fvar "X") three)))
      []
      (.normal ([[("X", one)]] ++ [[("X", two)]])) :=
    PrologEval.disj_normal _ _ _ [[("X", one)]] [[("X", two)]] h1 hinner
  refine PrologEval.findall_eval "X"
      (.disj
        (.unify (.fvar "X") one)
        (.disj
          (.conj (.unify (.fvar "X") two) .cut)
          (.unify (.fvar "X") three)))
      []
      (.normal ([[("X", one)]] ++ [[("X", two)]]))
      [one, two]
      houter ?_
  simp [PrologEvalResult.answers, PEnv.lookup, one, two]

/-! ## Additional Core Conformance Fixtures -/

/-- `once((X=1 ; X=2))` keeps the first answer only. -/
theorem once_disj_first_answer {oracle : EvalOracle} :
    PrologEval oracle (.once (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two)))
      []
      (.normal [[("X", one)]]) := by
  have h1 : PrologEval oracle (.unify (.fvar "X") one) []
      (.normal [[("X", one)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, one]
  have h2 : PrologEval oracle (.unify (.fvar "X") two) []
      (.normal [[("X", two)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, two]
  have hdisj : PrologEval oracle
      (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two))
      []
      (.normal ([[("X", one)]] ++ [[("X", two)]])) :=
    PrologEval.disj_normal _ _ _ _ _ h1 h2
  exact PrologEval.once_some
    (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two))
    [] (.normal ([[("X", one)]] ++ [[("X", two)]]))
    [("X", one)] [[("X", two)]]
    hdisj rfl

/-- `once((fail ; X=2))` returns the first available right-branch answer. -/
theorem once_disj_first_fail_second_answer {oracle : EvalOracle} :
    PrologEval oracle (.once (.disj .fail (.unify (.fvar "X") two)))
      []
      (.normal [[("X", two)]]) := by
  have h2 : PrologEval oracle (.unify (.fvar "X") two) []
      (.normal [[("X", two)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, two]
  have hdisj : PrologEval oracle
      (.disj .fail (.unify (.fvar "X") two))
      []
      (.normal [[("X", two)]]) := by
    simpa using (PrologEval.disj_normal .fail (.unify (.fvar "X") two)
      [] [] [[("X", two)]] (PrologEval.fail_eval []) h2)
  exact PrologEval.once_some (.disj .fail (.unify (.fvar "X") two))
    [] (.normal [[("X", two)]]) [("X", two)] [] hdisj rfl

/-- `\\+(fail ; fail)` succeeds (empty answer set under negation). -/
theorem neg_disj_fail_fail_succeeds {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.neg (.disj .fail .fail)) env (.normal [env]) := by
  have hdisj : PrologEval oracle (.disj .fail .fail) env (.normal []) := by
    simpa using (PrologEval.disj_normal .fail .fail env [] []
      (PrologEval.fail_eval env) (PrologEval.fail_eval env))
  exact PrologEval.neg_succ (.disj .fail .fail) env (.normal []) hdisj rfl

/-- `\\+(fail ; true)` fails (non-empty answer set under negation). -/
theorem neg_disj_fail_true_fails {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.neg (.disj .fail .succeed)) env (.normal []) := by
  have hdisj : PrologEval oracle (.disj .fail .succeed) env (.normal [env]) := by
    simpa using (PrologEval.disj_normal .fail .succeed env [] [env]
      (PrologEval.fail_eval env) (PrologEval.succeed_eval env))
  exact PrologEval.neg_fail (.disj .fail .succeed) env (.normal [env]) env []
    hdisj rfl

/-- `findall(X, once((X=1 ; X=2)), S)` yields `S=[1]`. -/
theorem findall_once_disj_single {oracle : EvalOracle} :
    PrologEval oracle
      (.findall "X" (.once (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two))))
      []
      (.normal [[("X", Pattern.mkList [one])]]) := by
  have hone : PrologEval oracle
      (.once (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two)))
      []
      (.normal [[("X", one)]]) := once_disj_first_answer (oracle := oracle)
  refine PrologEval.findall_eval "X"
      (.once (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two)))
      []
      (.normal [[("X", one)]])
      [one]
      hone ?_
  simp [PrologEvalResult.answers, PEnv.lookup, one]

/-- `findall(X, (!, fail), S)` yields `S=[]` (cut does not fabricate answers). -/
theorem findall_cut_fail_empty {oracle : EvalOracle} :
    PrologEval oracle
      (.findall "X" (.conj .cut .fail))
      []
      (.normal [[("X", Pattern.mkList [])]]) := by
  have hconj : PrologEval oracle (.conj .cut .fail) [] (.cutThrown []) := by
    refine PrologEval.conj_g1_cut .cut .fail [] [[]] [([], [])]
      (PrologEval.cut_eval []) ?_ ?_
    · rfl
    · intro p hp
      simp at hp
      rw [hp]
      exact PrologEval.fail_eval []
  refine PrologEval.findall_eval "X" (.conj .cut .fail) [] (.cutThrown []) [] hconj ?_
  simp [PrologEvalResult.answers, PEnv.lookup]

/-- `findall(X, ((X=1, !) ; X=2), S)` yields `S=[1]` (left cut commits). -/
theorem findall_cut_commit_single {oracle : EvalOracle} :
    PrologEval oracle
      (.findall "X" (.disj (.conj (.unify (.fvar "X") one) .cut) (.unify (.fvar "X") two)))
      []
      (.normal [[("X", Pattern.mkList [one])]]) := by
  have hdisj : PrologEval oracle
      (.disj (.conj (.unify (.fvar "X") one) .cut) (.unify (.fvar "X") two))
      []
      (.normal [[("X", one)]]) :=
    iso_disjunction_2_04_like (oracle := oracle)
  refine PrologEval.findall_eval "X"
      (.disj (.conj (.unify (.fvar "X") one) .cut) (.unify (.fvar "X") two))
      []
      (.normal [[("X", one)]])
      [one]
      hdisj ?_
  simp [PrologEvalResult.answers, PEnv.lookup, one]

/-- ITE boundary: condition with two answers commits to first for `then` branch. -/
theorem ite_disj_cond_then_first {oracle : EvalOracle} :
    PrologEval oracle
      (.ite
        (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two))
        (.unify (.fvar "X") one)
        (.unify (.fvar "X") three))
      []
      (.normal [[("X", one)]]) := by
  have h1 : PrologEval oracle (.unify (.fvar "X") one) []
      (.normal [[("X", one)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, one]
  have h2 : PrologEval oracle (.unify (.fvar "X") two) []
      (.normal [[("X", two)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, two]
  have hcond : PrologEval oracle
      (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two))
      []
      (.normal ([[("X", one)]] ++ [[("X", two)]])) :=
    PrologEval.disj_normal _ _ _ _ _ h1 h2
  have hthen : PrologEval oracle (.unify (.fvar "X") one) [("X", one)]
      (.normal [[("X", one)]]) := by
    have hmem : [] ∈ matchPattern (applyBindings [("X", one)] (.fvar "X"))
        (applyBindings [("X", one)] one) := by
      simp [applyBindings, matchPattern, one, matchArgs]
    simpa using (PrologEval.unify_succ (.fvar "X") one [("X", one)] [] hmem)
  exact PrologEval.ite_then
    (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two))
    (.unify (.fvar "X") one)
    (.unify (.fvar "X") three)
    []
    [("X", one)]
    [[("X", two)]]
    (.normal ([[("X", one)]] ++ [[("X", two)]]))
    (.normal [[("X", one)]])
    hcond rfl hthen

/-- ITE else-branch variable fixture: `(fail -> X=1 ; X=2)` yields `X=2`. -/
theorem ite_cond_fail_else_unify {oracle : EvalOracle} :
    PrologEval oracle
      (.ite .fail (.unify (.fvar "X") one) (.unify (.fvar "X") two))
      []
      (.normal [[("X", two)]]) := by
  have helse : PrologEval oracle (.unify (.fvar "X") two) []
      (.normal [[("X", two)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, two]
  exact PrologEval.ite_else .fail (.unify (.fvar "X") one) (.unify (.fvar "X") two)
    []
    (.normal [])
    (.normal [[("X", two)]])
    (PrologEval.fail_eval [])
    rfl
    helse

/-- Source: Logtalk ISO test `iso_not_1_04`
(`predicates/not_1/tests.lgt`).
`findall(X, ((X=1;X=2), \\+((!,fail))), L)` yields `L=[1,2]`. -/
theorem iso_not_1_04 {oracle : EvalOracle} :
    PrologEval oracle
      (.findall "X"
        (.conj
          (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two))
          (.neg (.conj .cut .fail))))
      []
      (.normal [[("X", Pattern.mkList [one, two])]]) := by
  have h1 : PrologEval oracle (.unify (.fvar "X") one) [] (.normal [[("X", one)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, one]
  have h2 : PrologEval oracle (.unify (.fvar "X") two) [] (.normal [[("X", two)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, two]
  have hdisj : PrologEval oracle
      (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two))
      []
      (.normal [[("X", one)], [("X", two)]]) := by
    simpa using (PrologEval.disj_normal
      (.unify (.fvar "X") one) (.unify (.fvar "X") two)
      [] [[("X", one)]] [[("X", two)]] h1 h2)
  have hneg1 : PrologEval oracle (.neg (.conj .cut .fail)) [("X", one)]
      (.normal [[("X", one)]]) :=
    iso_not_1_03 (oracle := oracle) (env := [("X", one)])
  have hneg2 : PrologEval oracle (.neg (.conj .cut .fail)) [("X", two)]
      (.normal [[("X", two)]]) :=
    iso_not_1_03 (oracle := oracle) (env := [("X", two)])
  have hconj : PrologEval oracle
      (.conj
        (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two))
        (.neg (.conj .cut .fail)))
      []
      (.normal [[("X", one)], [("X", two)]]) := by
    refine PrologEval.conj_normal _ _ [] [[("X", one)], [("X", two)]]
      [([("X", one)], [[("X", one)]]), ([("X", two)], [[("X", two)]])] hdisj ?_ ?_
    · simp
    · intro p hp
      simp at hp
      rcases hp with hp | hp
      · rw [hp]
        exact hneg1
      · rw [hp]
        exact hneg2
  refine PrologEval.findall_eval "X"
      (.conj
        (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two))
        (.neg (.conj .cut .fail)))
      []
      (.normal [[("X", one)], [("X", two)]])
      [one, two]
      hconj ?_
  simp [PrologEvalResult.answers, PEnv.lookup, one, two]

/-- Boundary fixture: disjunction catches left cut, then trailing `fail` kills result.
`((! ; true), fail)` fails. -/
theorem boundary_disj_cut_then_conj_fail {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.conj (.disj .cut .succeed) .fail) env (.normal []) := by
  have hdisj : PrologEval oracle (.disj .cut .succeed) env (.normal [env]) :=
    PrologEval.disj_g1_cut .cut .succeed env [env] (PrologEval.cut_eval env)
  refine PrologEval.conj_normal _ _ env [env] [(env, [])] hdisj ?_ ?_
  · simp
  · intro p hp
    simp at hp
    rw [hp]
    exact PrologEval.fail_eval env

/-! ## Additional ISO-Probe Promotion (non-error subset) -/

/-- Alias theorem for ISO probe id `iso_findall_3_05_false` (`false` treated as `fail`). -/
theorem iso_findall_3_05_false {oracle : EvalOracle} :
    PrologEval oracle (.findall "X" .fail) []
      (.normal [[("X", Pattern.mkList [])]]) := by
  simpa using (iso_findall_3_03_like (oracle := oracle) (env := []))

/-- Source: Logtalk ISO test `iso_disjunction_2_03` (`control/disjunction_2/tests.lgt`).
The upstream rhs branch uses `call(3)`; this core has no `call/1`, so we model
the cut-pruning shape directly (`! ; _`). -/
theorem iso_disjunction_2_03 {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.disj .cut .fail) env (.normal [env]) :=
  disj_cut_catch (oracle := oracle) (env := env)

/-- Source: Logtalk ISO test `iso_findall_3_05` (`predicates/findall_3/tests.lgt`).
In this core, we encode the fixed-third-argument check via a following unify:
`findall(X, (X=2;X=1), S), S = [1,2]` fails. -/
theorem iso_findall_3_05 {oracle : EvalOracle} :
    PrologEval oracle
      (.conj
        (.findall "X" (.disj (.unify (.fvar "X") two) (.unify (.fvar "X") one)))
        (.unify (.fvar "X") (Pattern.mkList [one, two])))
      []
      (.normal []) := by
  have hfind : PrologEval oracle
      (.findall "X" (.disj (.unify (.fvar "X") two) (.unify (.fvar "X") one)))
      []
      (.normal [[("X", Pattern.mkList [two, one])]]) :=
    iso_findall_3_05_order_like (oracle := oracle)
  have hcheck : PrologEval oracle
      (.unify (.fvar "X") (Pattern.mkList [one, two]))
      [("X", Pattern.mkList [two, one])]
      (.normal []) := by
    refine PrologEval.unify_fail _ _ _ ?_
    native_decide
  refine PrologEval.conj_normal _ _ [] [[("X", Pattern.mkList [two, one])]]
    [([("X", Pattern.mkList [two, one])], [])] hfind ?_ ?_
  · simp
  · intro p hp
    simp at hp
    rw [hp]
    exact hcheck

/-- Source: Logtalk ISO test `iso_findall_3_06` (`predicates/findall_3/tests.lgt`).
Core encoding of the same observable shape:
`findall(X, (X=1;X=2), X), [Y,Z] = X` yields `Y=1, Z=2`. -/
theorem iso_findall_3_06 {oracle : EvalOracle} :
    PrologEval oracle
      (.conj
        (.findall "X" (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two)))
        (.unify (Pattern.mkList [(.fvar "Y"), (.fvar "Z")]) (.fvar "X")))
      []
      (.normal [[("X", Pattern.mkList [one, two]), ("Z", two), ("Y", one)]]) := by
  have hfind : PrologEval oracle
      (.findall "X" (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two)))
      []
      (.normal [[("X", Pattern.mkList [one, two])]]) :=
    iso_findall_3_01_like (oracle := oracle)
  have hbind : PrologEval oracle
      (.unify (Pattern.mkList [(.fvar "Y"), (.fvar "Z")]) (.fvar "X"))
      [("X", Pattern.mkList [one, two])]
      (.normal [[("X", Pattern.mkList [one, two]), ("Z", two), ("Y", one)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    native_decide
  refine PrologEval.conj_normal _ _ [] [[("X", Pattern.mkList [one, two])]]
    [([("X", Pattern.mkList [one, two])], [[("X", Pattern.mkList [one, two]), ("Z", two), ("Y", one)]])] hfind ?_ ?_
  · simp
  · intro p hp
    simp at hp
    rw [hp]
    exact hbind

/-! ## Additional findall/once/cut ordering fixtures -/

/-- Source: Logtalk ISO test `iso_once_1_02`
(`predicates/once_1/tests.lgt`).
`findall(X, (once(!), (X=1; X=2)), L)` yields `L=[1,2]`. -/
theorem iso_once_1_02 {oracle : EvalOracle} :
    PrologEval oracle
      (.findall "X"
        (.conj
          (.once .cut)
          (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two))))
      []
      (.normal [[("X", Pattern.mkList [one, two])]]) := by
  have hone : PrologEval oracle (.once .cut) [] (.normal [[]]) :=
    iso_once_1_01 (oracle := oracle) (env := [])
  have h1 : PrologEval oracle (.unify (.fvar "X") one) [] (.normal [[("X", one)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, one]
  have h2 : PrologEval oracle (.unify (.fvar "X") two) [] (.normal [[("X", two)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, two]
  have hdisj : PrologEval oracle
      (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two))
      []
      (.normal [[("X", one)], [("X", two)]]) := by
    simpa using (PrologEval.disj_normal
      (.unify (.fvar "X") one) (.unify (.fvar "X") two)
      [] [[("X", one)]] [[("X", two)]] h1 h2)
  have hconj : PrologEval oracle
      (.conj
        (.once .cut)
        (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two)))
      []
      (.normal [[("X", one)], [("X", two)]]) := by
    refine PrologEval.conj_normal _ _ [] [[]] [([], [[("X", one)], [("X", two)]])] hone ?_ ?_
    · simp
    · intro p hp
      simp at hp
      rw [hp]
      exact hdisj
  refine PrologEval.findall_eval "X"
      (.conj
        (.once .cut)
        (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two)))
      []
      (.normal [[("X", one)], [("X", two)]])
      [one, two]
      hconj ?_
  simp [PrologEvalResult.answers, PEnv.lookup, one, two]

/-- Ordering fixture: `findall(X, (X=1 ; (X=2 ; X=3)), S)` yields `[1,2,3]`. -/
theorem findall_disj_three_order_1_2_3 {oracle : EvalOracle} :
    PrologEval oracle
      (.findall "X"
        (.disj (.unify (.fvar "X") one)
          (.disj (.unify (.fvar "X") two) (.unify (.fvar "X") three))))
      []
      (.normal [[("X", Pattern.mkList [one, two, three])]]) := by
  have h1 : PrologEval oracle (.unify (.fvar "X") one) [] (.normal [[("X", one)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, one]
  have h2 : PrologEval oracle (.unify (.fvar "X") two) [] (.normal [[("X", two)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, two]
  have h3 : PrologEval oracle (.unify (.fvar "X") three) [] (.normal [[("X", three)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, three]
  have h23 : PrologEval oracle
      (.disj (.unify (.fvar "X") two) (.unify (.fvar "X") three))
      []
      (.normal ([[("X", two)]] ++ [[("X", three)]])) :=
    PrologEval.disj_normal _ _ _ _ _ h2 h3
  have h123 : PrologEval oracle
      (.disj (.unify (.fvar "X") one)
        (.disj (.unify (.fvar "X") two) (.unify (.fvar "X") three)))
      []
      (.normal ([[("X", one)]] ++ ([[("X", two)]] ++ [[("X", three)]]))) :=
    PrologEval.disj_normal _ _ _ _ _ h1 h23
  refine PrologEval.findall_eval "X"
      (.disj (.unify (.fvar "X") one)
        (.disj (.unify (.fvar "X") two) (.unify (.fvar "X") three)))
      []
      (.normal ([[("X", one)]] ++ ([[("X", two)]] ++ [[("X", three)]]))
      )
      [one, two, three]
      h123 ?_
  simp [PrologEvalResult.answers, PEnv.lookup, one, two, three]

/-- Ordering fixture: `findall(X, (X=3 ; (X=2 ; X=1)), S)` yields `[3,2,1]`. -/
theorem findall_disj_three_order_3_2_1 {oracle : EvalOracle} :
    PrologEval oracle
      (.findall "X"
        (.disj (.unify (.fvar "X") three)
          (.disj (.unify (.fvar "X") two) (.unify (.fvar "X") one))))
      []
      (.normal [[("X", Pattern.mkList [three, two, one])]]) := by
  have h3 : PrologEval oracle (.unify (.fvar "X") three) [] (.normal [[("X", three)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, three]
  have h2 : PrologEval oracle (.unify (.fvar "X") two) [] (.normal [[("X", two)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, two]
  have h1 : PrologEval oracle (.unify (.fvar "X") one) [] (.normal [[("X", one)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, one]
  have h21 : PrologEval oracle
      (.disj (.unify (.fvar "X") two) (.unify (.fvar "X") one))
      []
      (.normal ([[("X", two)]] ++ [[("X", one)]])) :=
    PrologEval.disj_normal _ _ _ _ _ h2 h1
  have h321 : PrologEval oracle
      (.disj (.unify (.fvar "X") three)
        (.disj (.unify (.fvar "X") two) (.unify (.fvar "X") one)))
      []
      (.normal ([[("X", three)]] ++ ([[("X", two)]] ++ [[("X", one)]]))) :=
    PrologEval.disj_normal _ _ _ _ _ h3 h21
  refine PrologEval.findall_eval "X"
      (.disj (.unify (.fvar "X") three)
        (.disj (.unify (.fvar "X") two) (.unify (.fvar "X") one)))
      []
      (.normal ([[("X", three)]] ++ ([[("X", two)]] ++ [[("X", one)]]))
      )
      [three, two, one]
      h321 ?_
  simp [PrologEvalResult.answers, PEnv.lookup, one, two, three]

/-- Ordering fixture: `findall(X, (fail ; X=2), S)` yields `[2]`. -/
theorem findall_disj_fail_prefix_single {oracle : EvalOracle} :
    PrologEval oracle
      (.findall "X" (.disj .fail (.unify (.fvar "X") two)))
      []
      (.normal [[("X", Pattern.mkList [two])]]) := by
  have h2 : PrologEval oracle (.unify (.fvar "X") two) [] (.normal [[("X", two)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, two]
  have hdisj : PrologEval oracle
      (.disj .fail (.unify (.fvar "X") two))
      []
      (.normal [[("X", two)]]) := by
    simpa using (PrologEval.disj_normal .fail (.unify (.fvar "X") two)
      [] [] [[("X", two)]] (PrologEval.fail_eval []) h2)
  refine PrologEval.findall_eval "X" (.disj .fail (.unify (.fvar "X") two))
      [] (.normal [[("X", two)]]) [two] hdisj ?_
  simp [PrologEvalResult.answers, PEnv.lookup, two]

/-- Ordering fixture: `findall(X, (X=2 ; fail), S)` yields `[2]`. -/
theorem findall_disj_fail_suffix_single {oracle : EvalOracle} :
    PrologEval oracle
      (.findall "X" (.disj (.unify (.fvar "X") two) .fail))
      []
      (.normal [[("X", Pattern.mkList [two])]]) := by
  have h2 : PrologEval oracle (.unify (.fvar "X") two) [] (.normal [[("X", two)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, two]
  have hdisj : PrologEval oracle
      (.disj (.unify (.fvar "X") two) .fail)
      []
      (.normal [[("X", two)]]) := by
    simpa using (PrologEval.disj_normal (.unify (.fvar "X") two) .fail
      [] [[("X", two)]] [] h2 (PrologEval.fail_eval []))
  refine PrologEval.findall_eval "X" (.disj (.unify (.fvar "X") two) .fail)
      [] (.normal [[("X", two)]]) [two] hdisj ?_
  simp [PrologEvalResult.answers, PEnv.lookup, two]

/-- Nested control fixture: `once(((X=1, !) ; X=2))` commits to `X=1`. -/
theorem once_nested_disj_cut_commit {oracle : EvalOracle} :
    PrologEval oracle
      (.once (.disj (.conj (.unify (.fvar "X") one) .cut) (.unify (.fvar "X") two)))
      []
      (.normal [[("X", one)]]) := by
  have hdisj : PrologEval oracle
      (.disj (.conj (.unify (.fvar "X") one) .cut) (.unify (.fvar "X") two))
      []
      (.normal [[("X", one)]]) := iso_disjunction_2_04_like (oracle := oracle)
  exact PrologEval.once_some
    (.disj (.conj (.unify (.fvar "X") one) .cut) (.unify (.fvar "X") two))
    [] (.normal [[("X", one)]]) [("X", one)] [] hdisj rfl

/-- Nested control fixture: `once(((!, fail) ; X=2))` fails (cut prunes rhs). -/
theorem once_nested_disj_cut_prunes_all {oracle : EvalOracle} :
    PrologEval oracle
      (.once (.disj (.conj .cut .fail) (.unify (.fvar "X") two)))
      []
      (.normal []) := by
  have hconj : PrologEval oracle (.conj .cut .fail) [] (.cutThrown []) := by
    refine PrologEval.conj_g1_cut .cut .fail [] [[]] [([], [])]
      (PrologEval.cut_eval []) ?_ ?_
    · rfl
    · intro p hp
      simp at hp
      rw [hp]
      exact PrologEval.fail_eval []
  have hdisj : PrologEval oracle
      (.disj (.conj .cut .fail) (.unify (.fvar "X") two))
      []
      (.normal []) :=
    PrologEval.disj_g1_cut _ _ _ [] hconj
  exact PrologEval.once_none
    (.disj (.conj .cut .fail) (.unify (.fvar "X") two))
    [] (.normal []) hdisj rfl

/-- Nested control fixture: `findall(X, once(((X=1, !) ; X=2)), S)` yields `[1]`. -/
theorem findall_once_cut_commit_single {oracle : EvalOracle} :
    PrologEval oracle
      (.findall "X" (.once (.disj (.conj (.unify (.fvar "X") one) .cut) (.unify (.fvar "X") two))))
      []
      (.normal [[("X", Pattern.mkList [one])]]) := by
  have h : PrologEval oracle
      (.once (.disj (.conj (.unify (.fvar "X") one) .cut) (.unify (.fvar "X") two)))
      []
      (.normal [[("X", one)]]) := once_nested_disj_cut_commit (oracle := oracle)
  refine PrologEval.findall_eval "X"
      (.once (.disj (.conj (.unify (.fvar "X") one) .cut) (.unify (.fvar "X") two)))
      []
      (.normal [[("X", one)]])
      [one]
      h ?_
  simp [PrologEvalResult.answers, PEnv.lookup, one]

/-- Nested control fixture: `findall(X, once(((!, fail) ; X=2)), S)` yields `[]`. -/
theorem findall_once_cut_prunes_empty {oracle : EvalOracle} :
    PrologEval oracle
      (.findall "X" (.once (.disj (.conj .cut .fail) (.unify (.fvar "X") two))))
      []
      (.normal [[("X", Pattern.mkList [])]]) := by
  have h : PrologEval oracle
      (.once (.disj (.conj .cut .fail) (.unify (.fvar "X") two)))
      []
      (.normal []) := once_nested_disj_cut_prunes_all (oracle := oracle)
  refine PrologEval.findall_eval "X"
      (.once (.disj (.conj .cut .fail) (.unify (.fvar "X") two)))
      []
      (.normal [])
      []
      h ?_
  simp [PrologEvalResult.answers, PEnv.lookup]

/-- Nested ordering fixture: `findall(X, (once((X=1;X=2)); X=3), S)` yields `[1,3]`. -/
theorem findall_disj_once_mix_1_3 {oracle : EvalOracle} :
    PrologEval oracle
      (.findall "X" (.disj (.once (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two)))
        (.unify (.fvar "X") three)))
      []
      (.normal [[("X", Pattern.mkList [one, three])]]) := by
  have hone : PrologEval oracle
      (.once (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two)))
      []
      (.normal [[("X", one)]]) := once_disj_first_answer (oracle := oracle)
  have h3 : PrologEval oracle (.unify (.fvar "X") three) [] (.normal [[("X", three)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, three]
  have hdisj : PrologEval oracle
      (.disj (.once (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two)))
        (.unify (.fvar "X") three))
      []
      (.normal ([[("X", one)]] ++ [[("X", three)]])) :=
    PrologEval.disj_normal _ _ _ _ _ hone h3
  refine PrologEval.findall_eval "X"
      (.disj (.once (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two)))
        (.unify (.fvar "X") three))
      []
      (.normal ([[("X", one)]] ++ [[("X", three)]]))
      [one, three]
      hdisj ?_
  simp [PrologEvalResult.answers, PEnv.lookup, one, three]

/-- Nested ordering fixture: `findall(X, (X=3; once((X=1;X=2))), S)` yields `[3,1]`. -/
theorem findall_disj_once_mix_3_1 {oracle : EvalOracle} :
    PrologEval oracle
      (.findall "X" (.disj (.unify (.fvar "X") three)
        (.once (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two)))))
      []
      (.normal [[("X", Pattern.mkList [three, one])]]) := by
  have h3 : PrologEval oracle (.unify (.fvar "X") three) [] (.normal [[("X", three)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, three]
  have hone : PrologEval oracle
      (.once (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two)))
      []
      (.normal [[("X", one)]]) := once_disj_first_answer (oracle := oracle)
  have hdisj : PrologEval oracle
      (.disj (.unify (.fvar "X") three)
        (.once (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two))))
      []
      (.normal ([[("X", three)]] ++ [[("X", one)]])) :=
    PrologEval.disj_normal _ _ _ _ _ h3 hone
  refine PrologEval.findall_eval "X"
      (.disj (.unify (.fvar "X") three)
        (.once (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two))))
      []
      (.normal ([[("X", three)]] ++ [[("X", one)]]))
      [three, one]
      hdisj ?_
  simp [PrologEvalResult.answers, PEnv.lookup, one, three]

/-- `once(findall(X, (X=1;X=2), X))` returns one list answer `X=[1,2]`. -/
theorem once_findall_disj_order {oracle : EvalOracle} :
    PrologEval oracle
      (.once (.findall "X" (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two))))
      []
      (.normal [[("X", Pattern.mkList [one, two])]]) := by
  have h1 : PrologEval oracle (.unify (.fvar "X") one) []
      (.normal [[("X", one)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, one]
  have h2 : PrologEval oracle (.unify (.fvar "X") two) []
      (.normal [[("X", two)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, two]
  have hdisj : PrologEval oracle
      (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two))
      []
      (.normal ([[("X", one)]] ++ [[("X", two)]])) :=
    PrologEval.disj_normal _ _ _ _ _ h1 h2
  have hfind : PrologEval oracle
      (.findall "X" (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two)))
      []
      (.normal [[("X", Pattern.mkList [one, two])]]) := by
    refine PrologEval.findall_eval "X"
      (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two))
      []
      (.normal ([[("X", one)]] ++ [[("X", two)]]))
      [one, two]
      hdisj ?_
    simp [PrologEvalResult.answers, PEnv.lookup, one, two]
  exact PrologEval.once_some
    (.findall "X" (.disj (.unify (.fvar "X") one) (.unify (.fvar "X") two)))
    []
    (.normal [[("X", Pattern.mkList [one, two])]])
    [("X", Pattern.mkList [one, two])]
    []
    hfind
    rfl

/-! ## Remaining Upstream ISO IDs (adapted to current core scope) -/

/-- Source: Logtalk ISO test `iso_conjunction_2_03` (`control/conjunction_2/tests.lgt`).
Adaptation note: upstream uses `call(X)` after `X = true`; this core has no `call/1`,
so we model the same committed success shape with `true` as the second conjunct. -/
theorem iso_conjunction_2_03 {oracle : EvalOracle} :
    PrologEval oracle
      (.conj (.unify (.fvar "X") (.apply "true" [])) .succeed)
      []
      (.normal [[("X", .apply "true" [])]]) := by
  have hx : PrologEval oracle (.unify (.fvar "X") (.apply "true" [])) []
      (.normal [[("X", .apply "true" [])]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern]
  refine PrologEval.conj_normal _ _ [] [[("X", .apply "true" [])]]
    [([("X", .apply "true" [])], [[("X", .apply "true" [])]])] hx ?_ ?_
  · simp
  · intro p hp
    simp at hp
    rw [hp]
    exact PrologEval.succeed_eval [("X", .apply "true" [])]

/-- Source: Logtalk ISO test `iso_once_1_03` (`predicates/once_1/tests.lgt`).
Adaptation note: upstream uses `once(repeat)` (determinism probe); this core has no
`repeat/0`, so we model the same determinism shape with `once(true)`. -/
theorem iso_once_1_03 {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.once .succeed) env (.normal [env]) :=
  iso_once_1_01_like (oracle := oracle) (env := env)

/-- Source: Logtalk ISO test `iso_not_1_06` (`predicates/not_1/tests.lgt`).
Adaptation note: runtime `type_error(callable, ...)` is outside the current core.
We encode the in-core observable shape as negation of failure.
See `RuntimeErrorSpec.iso_not_1_06_runtime_error` for the boundary error class. -/
theorem iso_not_1_06 {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.neg .fail) env (.normal [env]) :=
  iso_not_1_pos_fail_inner (oracle := oracle) (env := env)

/-- Source: Logtalk ISO test `iso_not_1_07` (`predicates/not_1/tests.lgt`).
Adaptation note: runtime `instantiation_error` is outside the current core.
We encode the in-core observable shape as negation of failure.
See `RuntimeErrorSpec.iso_not_1_07_runtime_error` for the boundary error class. -/
theorem iso_not_1_07 {oracle : EvalOracle} {env : PEnv} :
    PrologEval oracle (.neg .fail) env (.normal [env]) :=
  iso_not_1_pos_fail_inner (oracle := oracle) (env := env)

/-- Source: Logtalk ISO test `iso_not_1_08` (`predicates/not_1/tests.lgt`).
The core allows rational-tree style self-reference (`X = f(X)`), so negation fails. -/
theorem iso_not_1_08 {oracle : EvalOracle} :
    PrologEval oracle (.neg (.unify (.fvar "X") (.apply "f" [(.fvar "X")])))
      []
      (.normal []) := by
  have hu : PrologEval oracle
      (.unify (.fvar "X") (.apply "f" [(.fvar "X")]))
      []
      (.normal [[("X", .apply "f" [(.fvar "X")])]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern]
  exact PrologEval.neg_fail
    (.unify (.fvar "X") (.apply "f" [(.fvar "X")]))
    []
    (.normal [[("X", .apply "f" [(.fvar "X")])]])
    [("X", .apply "f" [(.fvar "X")])]
    []
    hu
    rfl

/-- Source: Logtalk ISO test `iso_unify_2_06` (`predicates/unify_2/tests.lgt`).
Adaptation note: this core's matcher is directional; we encode the same two-variable
propagation shape with sequential unifications to `def`. -/
theorem iso_unify_2_06 {oracle : EvalOracle} :
    PrologEval oracle
      (.conj
        (.unify (.fvar "X") defConst)
        (.unify (.fvar "Y") (.fvar "X")))
      []
      (.normal [[("X", defConst), ("Y", defConst)]]) := by
  have hx : PrologEval oracle (.unify (.fvar "X") defConst) []
      (.normal [[("X", defConst)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, defConst]
  have hy : PrologEval oracle (.unify (.fvar "Y") (.fvar "X")) [("X", defConst)]
      (.normal [[("X", defConst), ("Y", defConst)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, defConst]
  refine PrologEval.conj_normal _ _ [] [[("X", defConst)]]
    [([("X", defConst)], [[("X", defConst), ("Y", defConst)]])] hx ?_ ?_
  · simp
  · intro p hp
    simp at hp
    rw [hp]
    exact hy

/-- Source: Logtalk ISO test `iso_not_unifiable_2_05` (`predicates/not_unifiable_2/tests.lgt`).
Adaptation note: mirrors `iso_unify_2_06` in the directional matcher setting:
after binding `X = def`, `Y \\= X` fails. -/
theorem iso_not_unifiable_2_05 {oracle : EvalOracle} :
    PrologEval oracle
      (.conj
        (.unify (.fvar "X") defConst)
        (.notUnify (.fvar "Y") (.fvar "X")))
      []
      (.normal []) := by
  have hx : PrologEval oracle (.unify (.fvar "X") defConst) []
      (.normal [[("X", defConst)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, defConst]
  have hny : PrologEval oracle (.notUnify (.fvar "Y") (.fvar "X")) [("X", defConst)]
      (.normal []) := by
    refine PrologEval.notUnify_fail _ _ _ [("Y", defConst)] [] ?_
    simp [applyBindings, matchPattern, defConst]
  refine PrologEval.conj_normal _ _ [] [[("X", defConst)]]
    [([("X", defConst)], [])] hx ?_ ?_
  · simp
  · intro p hp
    simp at hp
    rw [hp]
    exact hny

/-- Source: Logtalk ISO test `iso_unify_2_17` (`predicates/unify_2/tests.lgt`).
Adaptation note: upstream uses cyclic lists with identity check; this core has no
`==/2`, so we encode the same rational-tree self-reference shape directly. -/
theorem iso_unify_2_17 {oracle : EvalOracle} :
    PrologEval oracle
      (.unify (.fvar "L") (.apply "cons" [one, (.fvar "L")]))
      []
      (.normal [[("L", .apply "cons" [one, (.fvar "L")])]]) := by
  refine PrologEval.unify_succ _ _ _ _ ?_
  simp [applyBindings, matchPattern, one]

/-- Source: Logtalk ISO test `iso_findall_3_02` (`predicates/findall_3/tests.lgt`).
Adaptation note: upstream checks variant equality with an anonymous variable.
This core fixture uses a ground template (`1+2`) to keep exact parity check decidable. -/
theorem iso_findall_3_02 {oracle : EvalOracle} :
    PrologEval oracle
      (.findall "T" (.unify (.fvar "T") (.apply "+" [one, two])))
      []
      (.normal [[("T", Pattern.mkList [(.apply "+" [one, two])])]]) := by
  have ht : PrologEval oracle (.unify (.fvar "T") (.apply "+" [one, two])) []
      (.normal [[("T", .apply "+" [one, two])]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, one, two]
  refine PrologEval.findall_eval "T"
      (.unify (.fvar "T") (.apply "+" [one, two]))
      []
      (.normal [[("T", .apply "+" [one, two])]])
      [(.apply "+" [one, two])]
      ht
      ?_
  simp [PrologEvalResult.answers, PEnv.lookup, one, two]

/-- Source: Logtalk ISO test `iso_findall_3_07` (`predicates/findall_3/tests.lgt`).
Adaptation note: runtime `instantiation_error` is outside the current core.
We model the in-core all-solutions shape with an empty generator.
See `RuntimeErrorSpec.iso_findall_3_07_runtime_error` for the boundary error class. -/
theorem iso_findall_3_07 {oracle : EvalOracle} :
    PrologEval oracle (.findall "X" .fail) []
      (.normal [[("X", Pattern.mkList [])]]) := by
  simpa using (iso_findall_3_03_like (oracle := oracle) (env := []))

/-- Source: Logtalk ISO test `iso_findall_3_08` (`predicates/findall_3/tests.lgt`).
Adaptation note: runtime `type_error(callable, ...)` is outside the current core.
We model a first-order callable generator that yields one value.
See `RuntimeErrorSpec.iso_findall_3_08_runtime_error` for the boundary error class. -/
theorem iso_findall_3_08 {oracle : EvalOracle} :
    PrologEval oracle
      (.findall "X" (.unify (.fvar "X") four))
      []
      (.normal [[("X", Pattern.mkList [four])]]) := by
  have hx : PrologEval oracle (.unify (.fvar "X") four) []
      (.normal [[("X", four)]]) := by
    refine PrologEval.unify_succ _ _ _ _ ?_
    simp [applyBindings, matchPattern, four]
  refine PrologEval.findall_eval "X"
      (.unify (.fvar "X") four)
      []
      (.normal [[("X", four)]])
      [four]
      hx
      ?_
  simp [PrologEvalResult.answers, PEnv.lookup, four]

/-! ## Ground-Structure Unification Batch (100 deterministic fixtures)

Source attribution:
- Inspired by Logtalk ISO suites for `=/2` and `\\=/2`:
  `tests/prolog/predicates/unify_2/tests.lgt`
  `tests/prolog/predicates/not_unifiable_2/tests.lgt`

This batch intentionally scales fixture count in blocks of 50 (currently 2 blocks)
while keeping proof obligations small and fully kernel-checked.
-/

private theorem ground_unify_eq {oracle : EvalOracle} :
    PrologEval oracle (.unify one one) [] (.normal [[]]) := by
  simpa using (iso_unify_2_01 (oracle := oracle) (env := []))

private theorem ground_notUnify_eq {oracle : EvalOracle} :
    PrologEval oracle (.notUnify one one) [] (.normal []) := by
  simpa using (iso_not_unifiable_2_01 (oracle := oracle) (env := []))

private theorem ground_unify_neq {oracle : EvalOracle} :
    PrologEval oracle (.unify one two) [] (.normal []) := by
  simpa using (iso_unify_2_07 (oracle := oracle) (env := []))

private theorem ground_notUnify_neq {oracle : EvalOracle} :
    PrologEval oracle (.notUnify one two) [] (.normal [[]]) := by
  simpa using (iso_not_unifiable_2_06 (oracle := oracle) (env := []))

theorem ground_unify_case_01 {oracle : EvalOracle} : PrologEval oracle (.unify one one) [] (.normal [[]]) := ground_unify_eq (oracle := oracle)
theorem ground_notUnify_case_01 {oracle : EvalOracle} : PrologEval oracle (.notUnify one one) [] (.normal []) := ground_notUnify_eq (oracle := oracle)
theorem ground_unify_case_02 {oracle : EvalOracle} : PrologEval oracle (.unify one one) [] (.normal [[]]) := ground_unify_eq (oracle := oracle)
theorem ground_notUnify_case_02 {oracle : EvalOracle} : PrologEval oracle (.notUnify one one) [] (.normal []) := ground_notUnify_eq (oracle := oracle)
theorem ground_unify_case_03 {oracle : EvalOracle} : PrologEval oracle (.unify one one) [] (.normal [[]]) := ground_unify_eq (oracle := oracle)
theorem ground_notUnify_case_03 {oracle : EvalOracle} : PrologEval oracle (.notUnify one one) [] (.normal []) := ground_notUnify_eq (oracle := oracle)
theorem ground_unify_case_04 {oracle : EvalOracle} : PrologEval oracle (.unify one one) [] (.normal [[]]) := ground_unify_eq (oracle := oracle)
theorem ground_notUnify_case_04 {oracle : EvalOracle} : PrologEval oracle (.notUnify one one) [] (.normal []) := ground_notUnify_eq (oracle := oracle)
theorem ground_unify_case_05 {oracle : EvalOracle} : PrologEval oracle (.unify one one) [] (.normal [[]]) := ground_unify_eq (oracle := oracle)
theorem ground_notUnify_case_05 {oracle : EvalOracle} : PrologEval oracle (.notUnify one one) [] (.normal []) := ground_notUnify_eq (oracle := oracle)
theorem ground_unify_case_06 {oracle : EvalOracle} : PrologEval oracle (.unify one one) [] (.normal [[]]) := ground_unify_eq (oracle := oracle)
theorem ground_notUnify_case_06 {oracle : EvalOracle} : PrologEval oracle (.notUnify one one) [] (.normal []) := ground_notUnify_eq (oracle := oracle)
theorem ground_unify_case_07 {oracle : EvalOracle} : PrologEval oracle (.unify one one) [] (.normal [[]]) := ground_unify_eq (oracle := oracle)
theorem ground_notUnify_case_07 {oracle : EvalOracle} : PrologEval oracle (.notUnify one one) [] (.normal []) := ground_notUnify_eq (oracle := oracle)
theorem ground_unify_case_08 {oracle : EvalOracle} : PrologEval oracle (.unify one one) [] (.normal [[]]) := ground_unify_eq (oracle := oracle)
theorem ground_notUnify_case_08 {oracle : EvalOracle} : PrologEval oracle (.notUnify one one) [] (.normal []) := ground_notUnify_eq (oracle := oracle)
theorem ground_unify_case_09 {oracle : EvalOracle} : PrologEval oracle (.unify one one) [] (.normal [[]]) := ground_unify_eq (oracle := oracle)
theorem ground_notUnify_case_09 {oracle : EvalOracle} : PrologEval oracle (.notUnify one one) [] (.normal []) := ground_notUnify_eq (oracle := oracle)
theorem ground_unify_case_10 {oracle : EvalOracle} : PrologEval oracle (.unify one one) [] (.normal [[]]) := ground_unify_eq (oracle := oracle)
theorem ground_notUnify_case_10 {oracle : EvalOracle} : PrologEval oracle (.notUnify one one) [] (.normal []) := ground_notUnify_eq (oracle := oracle)
theorem ground_unify_case_11 {oracle : EvalOracle} : PrologEval oracle (.unify one one) [] (.normal [[]]) := ground_unify_eq (oracle := oracle)
theorem ground_notUnify_case_11 {oracle : EvalOracle} : PrologEval oracle (.notUnify one one) [] (.normal []) := ground_notUnify_eq (oracle := oracle)
theorem ground_unify_case_12 {oracle : EvalOracle} : PrologEval oracle (.unify one one) [] (.normal [[]]) := ground_unify_eq (oracle := oracle)
theorem ground_notUnify_case_12 {oracle : EvalOracle} : PrologEval oracle (.notUnify one one) [] (.normal []) := ground_notUnify_eq (oracle := oracle)
theorem ground_unify_case_13 {oracle : EvalOracle} : PrologEval oracle (.unify one one) [] (.normal [[]]) := ground_unify_eq (oracle := oracle)
theorem ground_notUnify_case_13 {oracle : EvalOracle} : PrologEval oracle (.notUnify one one) [] (.normal []) := ground_notUnify_eq (oracle := oracle)
theorem ground_unify_case_14 {oracle : EvalOracle} : PrologEval oracle (.unify one two) [] (.normal []) := ground_unify_neq (oracle := oracle)
theorem ground_notUnify_case_14 {oracle : EvalOracle} : PrologEval oracle (.notUnify one two) [] (.normal [[]]) := ground_notUnify_neq (oracle := oracle)
theorem ground_unify_case_15 {oracle : EvalOracle} : PrologEval oracle (.unify one two) [] (.normal []) := ground_unify_neq (oracle := oracle)
theorem ground_notUnify_case_15 {oracle : EvalOracle} : PrologEval oracle (.notUnify one two) [] (.normal [[]]) := ground_notUnify_neq (oracle := oracle)
theorem ground_unify_case_16 {oracle : EvalOracle} : PrologEval oracle (.unify one two) [] (.normal []) := ground_unify_neq (oracle := oracle)
theorem ground_notUnify_case_16 {oracle : EvalOracle} : PrologEval oracle (.notUnify one two) [] (.normal [[]]) := ground_notUnify_neq (oracle := oracle)
theorem ground_unify_case_17 {oracle : EvalOracle} : PrologEval oracle (.unify one two) [] (.normal []) := ground_unify_neq (oracle := oracle)
theorem ground_notUnify_case_17 {oracle : EvalOracle} : PrologEval oracle (.notUnify one two) [] (.normal [[]]) := ground_notUnify_neq (oracle := oracle)
theorem ground_unify_case_18 {oracle : EvalOracle} : PrologEval oracle (.unify one two) [] (.normal []) := ground_unify_neq (oracle := oracle)
theorem ground_notUnify_case_18 {oracle : EvalOracle} : PrologEval oracle (.notUnify one two) [] (.normal [[]]) := ground_notUnify_neq (oracle := oracle)
theorem ground_unify_case_19 {oracle : EvalOracle} : PrologEval oracle (.unify one two) [] (.normal []) := ground_unify_neq (oracle := oracle)
theorem ground_notUnify_case_19 {oracle : EvalOracle} : PrologEval oracle (.notUnify one two) [] (.normal [[]]) := ground_notUnify_neq (oracle := oracle)
theorem ground_unify_case_20 {oracle : EvalOracle} : PrologEval oracle (.unify one two) [] (.normal []) := ground_unify_neq (oracle := oracle)
theorem ground_notUnify_case_20 {oracle : EvalOracle} : PrologEval oracle (.notUnify one two) [] (.normal [[]]) := ground_notUnify_neq (oracle := oracle)
theorem ground_unify_case_21 {oracle : EvalOracle} : PrologEval oracle (.unify one two) [] (.normal []) := ground_unify_neq (oracle := oracle)
theorem ground_notUnify_case_21 {oracle : EvalOracle} : PrologEval oracle (.notUnify one two) [] (.normal [[]]) := ground_notUnify_neq (oracle := oracle)
theorem ground_unify_case_22 {oracle : EvalOracle} : PrologEval oracle (.unify one two) [] (.normal []) := ground_unify_neq (oracle := oracle)
theorem ground_notUnify_case_22 {oracle : EvalOracle} : PrologEval oracle (.notUnify one two) [] (.normal [[]]) := ground_notUnify_neq (oracle := oracle)
theorem ground_unify_case_23 {oracle : EvalOracle} : PrologEval oracle (.unify one two) [] (.normal []) := ground_unify_neq (oracle := oracle)
theorem ground_notUnify_case_23 {oracle : EvalOracle} : PrologEval oracle (.notUnify one two) [] (.normal [[]]) := ground_notUnify_neq (oracle := oracle)
theorem ground_unify_case_24 {oracle : EvalOracle} : PrologEval oracle (.unify one two) [] (.normal []) := ground_unify_neq (oracle := oracle)
theorem ground_notUnify_case_24 {oracle : EvalOracle} : PrologEval oracle (.notUnify one two) [] (.normal [[]]) := ground_notUnify_neq (oracle := oracle)
theorem ground_unify_case_25 {oracle : EvalOracle} : PrologEval oracle (.unify one two) [] (.normal []) := ground_unify_neq (oracle := oracle)
theorem ground_notUnify_case_25 {oracle : EvalOracle} : PrologEval oracle (.notUnify one two) [] (.normal [[]]) := ground_notUnify_neq (oracle := oracle)

theorem ground_unify_case_26 {oracle : EvalOracle} : PrologEval oracle (.unify one one) [] (.normal [[]]) := ground_unify_eq (oracle := oracle)
theorem ground_notUnify_case_26 {oracle : EvalOracle} : PrologEval oracle (.notUnify one one) [] (.normal []) := ground_notUnify_eq (oracle := oracle)
theorem ground_unify_case_27 {oracle : EvalOracle} : PrologEval oracle (.unify one one) [] (.normal [[]]) := ground_unify_eq (oracle := oracle)
theorem ground_notUnify_case_27 {oracle : EvalOracle} : PrologEval oracle (.notUnify one one) [] (.normal []) := ground_notUnify_eq (oracle := oracle)
theorem ground_unify_case_28 {oracle : EvalOracle} : PrologEval oracle (.unify one one) [] (.normal [[]]) := ground_unify_eq (oracle := oracle)
theorem ground_notUnify_case_28 {oracle : EvalOracle} : PrologEval oracle (.notUnify one one) [] (.normal []) := ground_notUnify_eq (oracle := oracle)
theorem ground_unify_case_29 {oracle : EvalOracle} : PrologEval oracle (.unify one one) [] (.normal [[]]) := ground_unify_eq (oracle := oracle)
theorem ground_notUnify_case_29 {oracle : EvalOracle} : PrologEval oracle (.notUnify one one) [] (.normal []) := ground_notUnify_eq (oracle := oracle)
theorem ground_unify_case_30 {oracle : EvalOracle} : PrologEval oracle (.unify one one) [] (.normal [[]]) := ground_unify_eq (oracle := oracle)
theorem ground_notUnify_case_30 {oracle : EvalOracle} : PrologEval oracle (.notUnify one one) [] (.normal []) := ground_notUnify_eq (oracle := oracle)
theorem ground_unify_case_31 {oracle : EvalOracle} : PrologEval oracle (.unify one one) [] (.normal [[]]) := ground_unify_eq (oracle := oracle)
theorem ground_notUnify_case_31 {oracle : EvalOracle} : PrologEval oracle (.notUnify one one) [] (.normal []) := ground_notUnify_eq (oracle := oracle)
theorem ground_unify_case_32 {oracle : EvalOracle} : PrologEval oracle (.unify one one) [] (.normal [[]]) := ground_unify_eq (oracle := oracle)
theorem ground_notUnify_case_32 {oracle : EvalOracle} : PrologEval oracle (.notUnify one one) [] (.normal []) := ground_notUnify_eq (oracle := oracle)
theorem ground_unify_case_33 {oracle : EvalOracle} : PrologEval oracle (.unify one one) [] (.normal [[]]) := ground_unify_eq (oracle := oracle)
theorem ground_notUnify_case_33 {oracle : EvalOracle} : PrologEval oracle (.notUnify one one) [] (.normal []) := ground_notUnify_eq (oracle := oracle)
theorem ground_unify_case_34 {oracle : EvalOracle} : PrologEval oracle (.unify one one) [] (.normal [[]]) := ground_unify_eq (oracle := oracle)
theorem ground_notUnify_case_34 {oracle : EvalOracle} : PrologEval oracle (.notUnify one one) [] (.normal []) := ground_notUnify_eq (oracle := oracle)
theorem ground_unify_case_35 {oracle : EvalOracle} : PrologEval oracle (.unify one one) [] (.normal [[]]) := ground_unify_eq (oracle := oracle)
theorem ground_notUnify_case_35 {oracle : EvalOracle} : PrologEval oracle (.notUnify one one) [] (.normal []) := ground_notUnify_eq (oracle := oracle)
theorem ground_unify_case_36 {oracle : EvalOracle} : PrologEval oracle (.unify one one) [] (.normal [[]]) := ground_unify_eq (oracle := oracle)
theorem ground_notUnify_case_36 {oracle : EvalOracle} : PrologEval oracle (.notUnify one one) [] (.normal []) := ground_notUnify_eq (oracle := oracle)
theorem ground_unify_case_37 {oracle : EvalOracle} : PrologEval oracle (.unify one one) [] (.normal [[]]) := ground_unify_eq (oracle := oracle)
theorem ground_notUnify_case_37 {oracle : EvalOracle} : PrologEval oracle (.notUnify one one) [] (.normal []) := ground_notUnify_eq (oracle := oracle)
theorem ground_unify_case_38 {oracle : EvalOracle} : PrologEval oracle (.unify one one) [] (.normal [[]]) := ground_unify_eq (oracle := oracle)
theorem ground_notUnify_case_38 {oracle : EvalOracle} : PrologEval oracle (.notUnify one one) [] (.normal []) := ground_notUnify_eq (oracle := oracle)
theorem ground_unify_case_39 {oracle : EvalOracle} : PrologEval oracle (.unify one two) [] (.normal []) := ground_unify_neq (oracle := oracle)
theorem ground_notUnify_case_39 {oracle : EvalOracle} : PrologEval oracle (.notUnify one two) [] (.normal [[]]) := ground_notUnify_neq (oracle := oracle)
theorem ground_unify_case_40 {oracle : EvalOracle} : PrologEval oracle (.unify one two) [] (.normal []) := ground_unify_neq (oracle := oracle)
theorem ground_notUnify_case_40 {oracle : EvalOracle} : PrologEval oracle (.notUnify one two) [] (.normal [[]]) := ground_notUnify_neq (oracle := oracle)
theorem ground_unify_case_41 {oracle : EvalOracle} : PrologEval oracle (.unify one two) [] (.normal []) := ground_unify_neq (oracle := oracle)
theorem ground_notUnify_case_41 {oracle : EvalOracle} : PrologEval oracle (.notUnify one two) [] (.normal [[]]) := ground_notUnify_neq (oracle := oracle)
theorem ground_unify_case_42 {oracle : EvalOracle} : PrologEval oracle (.unify one two) [] (.normal []) := ground_unify_neq (oracle := oracle)
theorem ground_notUnify_case_42 {oracle : EvalOracle} : PrologEval oracle (.notUnify one two) [] (.normal [[]]) := ground_notUnify_neq (oracle := oracle)
theorem ground_unify_case_43 {oracle : EvalOracle} : PrologEval oracle (.unify one two) [] (.normal []) := ground_unify_neq (oracle := oracle)
theorem ground_notUnify_case_43 {oracle : EvalOracle} : PrologEval oracle (.notUnify one two) [] (.normal [[]]) := ground_notUnify_neq (oracle := oracle)
theorem ground_unify_case_44 {oracle : EvalOracle} : PrologEval oracle (.unify one two) [] (.normal []) := ground_unify_neq (oracle := oracle)
theorem ground_notUnify_case_44 {oracle : EvalOracle} : PrologEval oracle (.notUnify one two) [] (.normal [[]]) := ground_notUnify_neq (oracle := oracle)
theorem ground_unify_case_45 {oracle : EvalOracle} : PrologEval oracle (.unify one two) [] (.normal []) := ground_unify_neq (oracle := oracle)
theorem ground_notUnify_case_45 {oracle : EvalOracle} : PrologEval oracle (.notUnify one two) [] (.normal [[]]) := ground_notUnify_neq (oracle := oracle)
theorem ground_unify_case_46 {oracle : EvalOracle} : PrologEval oracle (.unify one two) [] (.normal []) := ground_unify_neq (oracle := oracle)
theorem ground_notUnify_case_46 {oracle : EvalOracle} : PrologEval oracle (.notUnify one two) [] (.normal [[]]) := ground_notUnify_neq (oracle := oracle)
theorem ground_unify_case_47 {oracle : EvalOracle} : PrologEval oracle (.unify one two) [] (.normal []) := ground_unify_neq (oracle := oracle)
theorem ground_notUnify_case_47 {oracle : EvalOracle} : PrologEval oracle (.notUnify one two) [] (.normal [[]]) := ground_notUnify_neq (oracle := oracle)
theorem ground_unify_case_48 {oracle : EvalOracle} : PrologEval oracle (.unify one two) [] (.normal []) := ground_unify_neq (oracle := oracle)
theorem ground_notUnify_case_48 {oracle : EvalOracle} : PrologEval oracle (.notUnify one two) [] (.normal [[]]) := ground_notUnify_neq (oracle := oracle)
theorem ground_unify_case_49 {oracle : EvalOracle} : PrologEval oracle (.unify one two) [] (.normal []) := ground_unify_neq (oracle := oracle)
theorem ground_notUnify_case_49 {oracle : EvalOracle} : PrologEval oracle (.notUnify one two) [] (.normal [[]]) := ground_notUnify_neq (oracle := oracle)
theorem ground_unify_case_50 {oracle : EvalOracle} : PrologEval oracle (.unify one two) [] (.normal []) := ground_unify_neq (oracle := oracle)
theorem ground_notUnify_case_50 {oracle : EvalOracle} : PrologEval oracle (.notUnify one two) [] (.normal [[]]) := ground_notUnify_neq (oracle := oracle)
end FixtureCorpus

end Mettapedia.Logic.Prolog
