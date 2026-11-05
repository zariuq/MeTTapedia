import Mettapedia.Machines.AdmissionRewriting.Syntax
import Mettapedia.Machines.AdmissionRewriting.Normalizer
import Mettapedia.Machines.AdmissionRewriting.Semantics
import Mettapedia.Machines.AdmissionRewriting.Dialects
import Mettapedia.Machines.AdmissionRewriting.Invariance
import Mettapedia.Machines.AdmissionRewriting.LocalDeclines

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
   with integer atoms `a`, `b` → `(if (< a b) a b)`;
8. a `let`: a source `(let $y e $y)` dissolves into `e`; `(let $v $x (size-atom $v))` →
   `(size-atom $x)`;
9. `(once b)` → `(let $y (once b) $y)`, dissolved by 8 where it is a `let` source.
The fixture law: on every fixture, the normalized program and the original have one
trace.  It holds on ready dialects; under a fuel meter the normalizer must be off.
-/
