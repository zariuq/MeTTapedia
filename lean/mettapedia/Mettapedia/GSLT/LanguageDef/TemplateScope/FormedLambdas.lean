import Mettapedia.GSLT.LanguageDef.TemplateScope.Spectrum

/-!
# Lambdas formed while the program runs

`Src.form` is one former. It is the ownership outcome of cons-atom,
union-atom, a substitution head, and a beta head, not an interpreter of
those four heads. The theorems below are the route rows that this language
can run. Rows that name the same program are the same proof.

The answer bags are `answersCfg` of the shipped elaborator and evaluator.
Rule M is `cfgM`. Lexical fresh, which is also the no-profile default, is
`cfgLF`.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.FormedLambdas

open Mettapedia.GSLT.LanguageDef.TemplateScope

inductive Sp where
  | f | y | z | n | x | w
  deriving DecidableEq, Repr

inductive Sy where
  | Pair | g | n1 | n2 | n5 | n7 | n8 | n99 | wrong
  deriving DecidableEq, Repr

abbrev A := Src Sy Sp
abbrev T := Tm Sy (Slot Sp)

def noProg : Sy → Option T := fun _ => none

def sv (sp : Sp) : A := .sv sp
def pr (sp : Sp) : A := .par sp
def k (s : Sy) : A := .sym s
def ap (f a : A) : A := .app f a
def pair (a b : A) : A := ap (ap (k .Pair) a) b
def lt (sp : Sp) (v b : A) : A := .letS (sv sp) v b none
def lm (sp : Sp) (b : A) : A := .lam sp none b
def fm (sp : Sp) (b : A) : A := .form sp b
def nw (ys : List Sp) (b : A) : A := .new ys b
def gApp (a : A) : A := ap (k .g) a

def pairT (a b : T) : T := .app (.app (.sym .Pair) a) b
def gOf (s : Sy) : T := .app (.sym .g) (.sym s)
def g1 : T := gOf .n1
def g2 : T := gOf .n2

/-- `(let $y (.par z) (g $y))`, the body of the formed and written `L`. -/
def bodyY : A := lt .y (pr .z) (gApp (sv .y))

/-- `(let $f (form z bodyY) (Pair ($f 1) ($f 2)))`. -/
def formedCaptures : A :=
  lt .f (fm .z bodyY) (pair (ap (sv .f) (k .n1)) (ap (sv .f) (k .n2)))

/-- The same formation, both calls passing `1`. -/
def formedAgree : A :=
  lt .f (fm .z bodyY) (pair (ap (sv .f) (k .n1)) (ap (sv .f) (k .n1)))

/-- `(let $f (lam z bodyY) (Pair ($f 1) ($f 2)))`. -/
def writtenOwns : A :=
  lt .f (lm .z bodyY) (pair (ap (sv .f) (k .n1)) (ap (sv .f) (k .n2)))

/-- `(let $f (form z (new ($y) bodyY)) (Pair ($f 1) ($f 2)))`. -/
def formedNew : A :=
  lt .f (fm .z (nw [.y] bodyY)) (pair (ap (sv .f) (k .n1)) (ap (sv .f) (k .n2)))

/-- `(let $f (form z (Pair z $n)) (let $n 5 ($f 1)))`. -/
def timingAfter : A :=
  lt .f (fm .z (pair (pr .z) (sv .n))) (lt .n (k .n5) (ap (sv .f) (k .n1)))

/-- `(let $n 5 (let $f (form z (Pair z $n)) ($f 1)))`. -/
def timingBefore : A :=
  lt .n (k .n5) (lt .f (fm .z (pair (pr .z) (sv .n))) (ap (sv .f) (k .n1)))

/-- `(let $f (lam z (Pair z $n)) (let $n 5 ($f 1)))`. -/
def writtenCaptures : A :=
  lt .f (lm .z (pair (pr .z) (sv .n))) (lt .n (k .n5) (ap (sv .f) (k .n1)))

/-- `(let $f (form x (g x)) (Pair ($f 1) $x))`. The parameter and the outer store name share a spelling. -/
def formedParam : A :=
  lt .f (fm .x (gApp (pr .x))) (pair (ap (sv .f) (k .n1)) (sv .x))

def nest : A := lt .y (k .n7) (lt .y (sv .y) (sv .y))
def pairLets : A := lt .y (k .n7) (pair (lt .y (k .n8) (sv .y)) (sv .y))
def shadow : A := lt .x (k .n1) (pair (lt .x (k .n2) (sv .x)) (sv .x))
def rhsOut : A := lt .x (k .n1) (pair (lt .x (sv .x) (sv .x)) (sv .x))
def newInner : A := lt .y (k .n7) (nw [.y] (lt .y (sv .y) (sv .y)))
def sameOut : A :=
  lt .y (k .n99) formedCaptures
def repeated : A :=
  .letS (pair (sv .x) (sv .x)) (pair (k .n1) (k .n2)) (k .wrong) none
def escaping : A :=
  lt .f (ap (lm .z (lt .y (pr .z) (lm .w (pair (sv .y) (pr .w))))) (k .n1))
    (ap (sv .f) (k .n2))
def escapingDistinct : A :=
  lt .f (lm .z (lt .y (pr .z) (lm .w (pair (sv .y) (pr .w)))))
    (pair (ap (ap (sv .f) (k .n1)) (k .n7)) (ap (ap (sv .f) (k .n2)) (k .n8)))

/-- Fuel 16 already returns the answer. The same bags at fuel 80 are the same
lists; the kernel check uses the fuel at which the run has finished. -/
def bag (c : Config) (t : A) : Option (List T) := answersCfg c noProg 16 t

def captured : T := pairT (.sym .n1) (.sym .n5)

/-! ## Timing independence -/

theorem timing_after_bag : bag cfgM timingAfter = some [captured] := by
  decide

theorem timing_before_bag : bag cfgM timingBefore = some [captured] := by
  decide

/-- The answer bag is the same whether the captured name is bound before or after formation. -/
theorem timing_independent : bag cfgM timingAfter = bag cfgM timingBefore := by
  rw [timing_after_bag, timing_before_bag]

theorem timing_after_not_empty : bag cfgM timingAfter ≠ some [] := by
  rw [timing_after_bag]
  decide

/-- `formed_names_keep_scope`: cons-atom, union-atom, substitution-head, and beta-head, bound after. -/
theorem cons_atom_bound_after : bag cfgM timingAfter = some [captured] := timing_after_bag
theorem union_atom_bound_after : bag cfgM timingAfter = some [captured] := timing_after_bag
theorem substitution_head_bound_after : bag cfgM timingAfter = some [captured] := timing_after_bag
theorem beta_head_bound_after : bag cfgM timingAfter = some [captured] := timing_after_bag

/-- The same four heads, bound before. -/
theorem cons_atom_bound_before : bag cfgM timingBefore = some [captured] := timing_before_bag
theorem union_atom_bound_before : bag cfgM timingBefore = some [captured] := timing_before_bag
theorem substitution_head_bound_before : bag cfgM timingBefore = some [captured] := timing_before_bag
theorem beta_head_bound_before : bag cfgM timingBefore = some [captured] := timing_before_bag

theorem written_captures_bag : bag cfgM writtenCaptures = some [captured] := by
  decide

/-- `formed_lambdas`, row written-captures. -/
theorem written_captures : bag cfgM writtenCaptures = some [captured] := written_captures_bag

/-! ## Formed captures versus written owns, rule M -/

theorem formed_captures_M : bag cfgM formedCaptures = some [] := by
  decide

theorem written_owns_M : bag cfgM writtenOwns = some [pairT g1 g2] := by
  decide

theorem formed_agree_M : bag cfgM formedAgree = some [pairT g1 g1] := by
  decide

theorem formed_new_owns_M : bag cfgM formedNew = some [pairT g1 g2] := by
  decide

theorem formed_captures_M_not_owned : bag cfgM formedCaptures ≠ some [pairT g1 g2] := by
  rw [formed_captures_M]
  decide

theorem written_owns_M_not_empty : bag cfgM writtenOwns ≠ some [] := by
  rw [written_owns_M]
  decide

/-- The four empty head rows of `formed_lambdas` are this capture. -/
theorem cons_atom_captures : bag cfgM formedCaptures = some [] := formed_captures_M
theorem union_atom_captures : bag cfgM formedCaptures = some [] := formed_captures_M
theorem substitution_head_captures : bag cfgM formedCaptures = some [] := formed_captures_M
theorem beta_head_captures : bag cfgM formedCaptures = some [] := formed_captures_M

/-- `formed_lambdas`, row written. -/
theorem written_owns : bag cfgM writtenOwns = some [pairT g1 g2] := written_owns_M

/-- `formed_names_keep_scope`, rows formed-captures, formed-captures-agree, formed-new-owns. -/
theorem formed_names_captures : bag cfgM formedCaptures = some [] := formed_captures_M
theorem formed_names_agree : bag cfgM formedAgree = some [pairT g1 g1] := formed_agree_M
theorem formed_names_new_owns : bag cfgM formedNew = some [pairT g1 g2] := formed_new_owns_M

theorem formed_param_M : bag cfgM formedParam = some [pairT g1 (.var (.src ([], .x)))] := by
  decide

/-- `formed_lambdas`, row formed-parameter. -/
theorem formed_parameter : bag cfgM formedParam = some [pairT g1 (.var (.src ([], .x)))] :=
  formed_param_M

end Mettapedia.GSLT.LanguageDef.TemplateScope.FormedLambdas
