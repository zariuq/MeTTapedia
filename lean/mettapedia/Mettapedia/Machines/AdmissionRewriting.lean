import Mettapedia.Machines.AdmissionRewriting.Syntax
import Mettapedia.Machines.AdmissionRewriting.Normalizer
import Mettapedia.Machines.AdmissionRewriting.Semantics
import Mettapedia.Machines.AdmissionRewriting.Dialects
import Mettapedia.Machines.AdmissionRewriting.Invariance
import Mettapedia.Machines.AdmissionRewriting.LocalDeclines
import Mettapedia.Machines.AdmissionRewriting.MinPolicies
import Mettapedia.Machines.AdmissionRewriting.Observation
import Mettapedia.Machines.AdmissionRewriting.TierNormalForms
import Mettapedia.Machines.AdmissionRewriting.MinMaxSWI
import Mettapedia.Machines.AdmissionRewriting.MinMaxSelection
import Mettapedia.Machines.AdmissionRewriting.BuiltinOwnership

/-!
# Admission by normal form, and local declines

A compiled tier should not charge for a spelling the language defines as equal to one it
accepts, nor for code a run never reaches.

* `Syntax`: the admission fragment, the rules oriented into the spellings the tier
  admits, and termination in every order (`step_wellFounded`).
* `Normalizer`: the one-pass normalizer `N`; every step leaves it unchanged (`step_N`,
  where the critical pairs are joined), every term rewrites to it (`reduces`), and its
  output is irreducible (`N_irreducible`): rewriting is confluent (`confluent`) and
  convertible terms share one normal form (`canonical`).
* `Semantics`: traces (answers and effects in order), dialects, the soundness of each
  rule under its own side condition, and of every step on a ready dialect
  (`step_sound`, `N_sound`).
* `Dialects`: PeTTa is ready (`petta_ready`); HE, the Prime draft and a metered run are
  not, each with the spellings that separate them.
* `Invariance`: a tier offered normal forms has a boundary that is a union of the rules'
  conversion classes (`admission_invariant`), answers as the original does
  (`normalized_answers`), and satisfies the fixture law (`fixture_law`).
* `MinPolicies`: `min` on integers, signed zeros and NaN; the `(<= $x $y)` spelling is
  the comparison policy on every pair of values, errors included (`viaLe_eq_minOp`), the
  `(< $y $x)` spelling agrees off NaN only (`minLe_eq_minLt`, `nan_controls`), and no
  single-comparison spelling gives IEEE's `minNum` or `minimum`.
* `MinMaxSWI`: SWI-PeTTa's `min` and `max` are SWI-Prolog's arithmetic functions; CeTTa's
  case analysis before DIFF-17 computed them on every pair of integers and doubles
  (`c_min_eq`, `c_max_eq`), as did its integer paths (`int_select`, `int_prim`); the
  comparison policy differs from them at a mixed tie, signed zeros and NaN
  (`Controls.le_select_differs`).
* `MinMaxSelection`: CeTTa's PeTTa `min` and `max` select an operand by the exact order
  (DIFF-17), with the laws (`selMin_mem`, `selMin_assoc`, `selMin_comm` up to equivalence,
  `stable_sort`, `absorb_min_max`); the C is the selection on every pair (`c_select_eq`,
  `c_select_operands`, `int_paths`, `Controls.big_double_exact`), where comparing a big
  integer beside a double as doubles breaks commutativity and associativity
  (`Controls.big_double_inexact`); SWI's rule and the earlier test rule are no stable sort
  (`Controls.swi_breaks_sort`, `Controls.le_rule_breaks_sort`).
* `BuiltinOwnership`: a space that authors equations for a builtin head answers its
  calls by them outside `&self`; the machine's refusal of such heads answers as the
  canonical evaluator on every call (`machine_eq_canon`).
* `Observation`: `collapse` is a context whose result is a function of its argument's
  trace in the same dialect (`CollapseLaw`, `collapse_N_sound`); an answer `Empty` is not
  the absence of answers (`empty_answer_ne_no_answer`); HE's empty-scrutinee `case`
  composes under `collapse` (`he_case_empty_composes`) and PeTTa's rule under HE's
  `collapse` breaks the law (`machine_case_rule_breaks_collapse`); equal traces give equal
  observations at every fuel (`underFuel_congr`), while charging saved steps afterwards
  (`charge_afterwards_insufficient`) or keeping only the answer bag and the effects
  (`bag_and_effects_insufficient`) does not.
* `LocalDeclines`: declining sites locally is invisible (`local_observes`), never costs
  more than refusing the graph and is strictly cheaper on the cliff families
  (`localCost_lt_wholeCost`); declarations are monotone under local admission
  (`type_monotone`, `type_neutral_unexecuted`) and not under whole-graph admission
  (`contagious_not_monotone`); uncalled and integer-guard declarations are
  answer-neutral (`eval_fn_irrelevant`, `eval_guard_neutral`).

**The normalizer, as a specification.**  Normalize the tier's input, never the stored
atoms (equation bodies are data a program can read back) and never inside a held
position (an `Atom` parameter, a `quote`, HE's `size-atom` argument).  Work bottom-up:
normalize every child, then rebuild the node:
1. `(if c t)` → `(if c t (empty))`;
2. `(let* ((x1 e1) … (xn en)) b)` → nested `let`s, each built as in 8;
3. `(case e (($x b)))`, one branch with a fresh variable → a `let` built as in 8;
4. `(id x)` → `x`;
5. `(superpose (x))` → `x`;
6. a callable iterator → its body form; the body is the call of the callable on the bound
   variables, rebuilt as in 7;
7. a strict call: `(size-atom e)` → the `let` of 8 on `e` and `(size-atom $v)`; `(min a b)`
   → `(let $x a (let $y b (if (<= $x $y) $x $y)))`, for any operands, on a dialect whose
   `min` is that test (`Semantics.MinProtocol`);
8. a `let`: a source `(let $y e $y)` dissolves into `e`; `(let $v $x (size-atom $v))` →
   `(size-atom $x)`;
9. `(once b)` → `(let $y (once b) $y)`, dissolved by 8 where it is a `let` source.
The fixture law: on every fixture, the normalized program and the original have one
trace, which fixes every observable prefix: effects, answers with their multiplicities,
their order, and where fuel runs out between effects.  It holds on ready dialects; under a
fuel meter the normalizer must be off, since charging the saved steps afterwards moves
effects across the point where fuel runs out.

* `TierNormalForms`: the prepared tier's PeTTa spellings, `(if c t)`,
  `(superpose (x))`, `(let $y e $y)`, `(case k (($v b) ..))` with no arm written
  `Empty`, and `(let* (.. ($y e)) $y)`, mean their normal forms at every position
  that is not held; the two-armed `if` is a guarded equation whose declining
  single-answer reading answers only the spelling's answer; HE differs on rules 1
  and 8 and on the `case` rule; a bound binder arm falls through.
-/
