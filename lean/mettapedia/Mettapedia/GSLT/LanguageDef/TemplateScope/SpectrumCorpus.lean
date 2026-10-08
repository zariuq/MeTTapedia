import Mettapedia.GSLT.LanguageDef.TemplateScope.SpectrumTheorems

/-!
# Template scope, part 7: the spectrum corpus and the criterion matrix

The corpus of `docs/prime/scope-policy-spectrum-20261006.md`, run under the six
configurations by kernel-checked computation (`decide`).  Every table lists
the answer bags in the order `[M, LF, EC, Q, PC, SN]`:

| name | ownership | lifetime | readout |
|---|---|---|---|
| M | mercury-implicit | per-call | reference |
| LF | lexical-fresh | per-call | reference |
| EC | explicit-capture | per-call | reference |
| Q | query-wide | — | — |
| PC | mercury-implicit | per-closure | reference |
| SN | mercury-implicit | per-call | snapshot |

Notation: `L = (lam z (let $y z (g $y)))`, `K = (lam z (Pair z $y))`.  In the
answers, `qv y` is the query slot `$y` left unbound, `fv ρ o y` is the copy
made by the activation at `ρ` of the slot `(o, y)`.

Rows 15 (code from text), 19 (effects), 20 (quotation round trips) and 21
(modules) are not modeled: the language has no `parse`/`eval`, effects,
`lift` or modules.  Criterion 9 (effects) is therefore not evaluated.

Equations are clauses elaborated as their own forms (`clauseOf`), curried,
with head variables bound by `let`s from the parameters.  Under SN the
curried encoding would snapshot an argument passed before the last
parameter, which an HE equation does not do; the criterion-1 comparison
therefore runs the equation with clause (reference) semantics.
-/

namespace Mettapedia.GSLT.LanguageDef.TemplateScope.SpectrumCorpus

open Mettapedia.GSLT.LanguageDef.TemplateScope

/-- Spellings of the corpus. -/
inductive Sp where
  | f | y | y2 | z | w | x | r | t | a | e | s | p | tm | u | p1 | p2 | hole | b
  deriving DecidableEq, Repr

/-- Symbols of the corpus. -/
inductive Sy where
  | Pair | g | d | ok | n1 | n2 | n3 | n4 | n5 | n7 | list2 | Got | ca | cb | cc
  | mk | second | lifted | Lf | unit | Left | Right
  deriving DecidableEq, Repr

abbrev A := Src Sy Sp
abbrev T := Tm Sy (Slot Sp)

/-! ## Authored text -/

def sv (n : Sp) : A := .sv n
def pr (n : Sp) : A := .par n
def lm (n : Sp) (b : A) : A := .lam n none b
/-- A lambda with its crossing set, `(lam z body){$t}`: it shares `$t` and owns
every other name its body uses. -/
def lsh (n : Sp) (sh : List Sp) (b : A) : A := .lam n (some sh) b
def ap (f a : A) : A := .app f a
def k (s : Sy) : A := .sym s
def pair (a b : A) : A := ap (ap (k .Pair) a) b
def lt (n : Sp) (v b : A) : A := .letS (sv n) v b none
/-- A `let` with its crossing set, `(let $n v b){$t}`: the pattern's names
outside the set are fresh. -/
def lts (n : Sp) (v b : A) (sh : List Sp) : A := .letS (sv n) v b (some sh)
def un (n : Sp) (v b : A) : A := .unify (sv n) v b

/-- `L = (lam z (let $y z (g $y)))`. -/
def L : A := lm .z (lt .y (pr .z) (ap (k .g) (sv .y)))
/-- `L` with its private name renamed to `$y2`. -/
def L2 : A := lm .z (lt .y2 (pr .z) (ap (k .g) (sv .y2)))
/-- `L` sharing `$y`, `(lam z (let $y z (g $y))){$y}`. -/
def Lec : A := lsh .z [.y] (lt .y (pr .z) (ap (k .g) (sv .y)))
/-- `L` refining with `unify`. -/
def Lu : A := lm .z (un .y (pr .z) (ap (k .g) (sv .y)))
/-- `K = (lam z (Pair z $y))`. -/
def K : A := lm .z (pair (pr .z) (sv .y))
/-- `K` sharing `$y`. -/
def Kec : A := lsh .z [.y] (pair (pr .z) (sv .y))
/-- The template `(Pair $e $y)` of `(map-atom (1 2) $e (Pair $e $y))`. -/
def T0 : A := lm .e (pair (pr .e) (sv .y))
/-- The template sharing `$y`. -/
def Tec : A := lsh .e [.y] (pair (pr .e) (sv .y))
/-- `(map-atom (1 2) $e T)`: one template, used once per element. -/
def mapT (tmpl : A) : A :=
  lt .tm tmpl (ap (ap (k .list2) (ap (sv .tm) (k .n1))) (ap (sv .tm) (k .n2)))
def f1 : A := ap (sv .f) (k .n1)
def f2 : A := ap (sv .f) (k .n2)
/-- Row 9's family: the outsider spelled `v`. -/
def progV (v : Sp) : A :=
  lt .f (lm .z (.letS (ap (k .d) (sv .t)) (pr .z) (k .ok) none))
    (lt .r (ap (sv .f) (ap (k .d) (k .n7))) (pair (sv v) (sv .r)))
/-- Row 10: nested templates. -/
def nested (n : Sy) : A :=
  ap (lm .z (pair (lt .y (pr .z) (sv .y)) (ap (lm .w (lt .y (pr .w) (sv .y))) (k .n3)))) (k n)
/-- The context of row 11. -/
def ctxW : A := ap (lm .w (pair f1 (lt .y (pr .w) (sv .y)))) (k .n5)

/-! ## Equations -/

/-- `(= (mk) L)`, `(= (second $s $t) (let (d $s $t) (d a b) (Got $t)))`,
`(= (lifted $y $z) (let $y $z (g $y)))` and the per-call lifted equation of
`L`, `(= (Lf $z) (let $y $z (g $y)))`. -/
def clauses : Sy → Option A
  | .mk => some L
  | .second => some (lm .p1 (lm .p2 (lt .s (pr .p1) (lt .t (pr .p2)
      (.letS (ap (ap (k .d) (sv .s)) (sv .t)) (ap (ap (k .d) (k .ca)) (k .cb))
        (ap (k .Got) (sv .t)) none)))))
  | .lifted => some (lm .p1 (lm .p2 (lt .y (pr .p1) (lt .z (pr .p2)
      (lt .y (sv .z) (ap (k .g) (sv .y)))))))
  | .Lf => some (lm .p1 (lt .z (pr .p1) (lt .y (sv .z) (ap (k .g) (sv .y)))))
  | _ => none

/-- The same equations with `unify` in place of the inner `let`. -/
def clausesU : Sy → Option A
  | .second => some (lm .p1 (lm .p2 (lt .s (pr .p1) (lt .t (pr .p2)
      (.unify (ap (ap (k .d) (sv .s)) (sv .t)) (ap (ap (k .d) (k .ca)) (k .cb))
        (ap (k .Got) (sv .t)))))))
  | .lifted => some (lm .p1 (lm .p2 (lt .y (pr .p1) (lt .z (pr .p2)
      (un .y (sv .z) (ap (k .g) (sv .y)))))))
  | F => clauses F

/-- The program of a configuration: each clause elaborated as its own form. -/
def progOf (c : Config) (cl : Sy → Option A) : Sy → Option T :=
  fun F => (cl F).map (clauseOf c [5] .u .unit)

/-- Answers under a configuration. -/
def ans (c : Config) (cl : Sy → Option A) (t : A) : Option (List T) :=
  answersCfg c (progOf c cl) 80 t

/-- Answers under the six configurations, in the order `[M, LF, EC, Q, PC, SN]`. -/
def six (cl : Sy → Option A) (t : A) : List (Option (List T)) :=
  [cfgM, cfgLF, cfgEC, cfgQ, cfgPC, cfgSN].map fun c => ans c cl t

/-! ## Answer notation -/

def kT (s : Sy) : T := .sym s
def apT (f a : T) : T := .app f a
def pairT (a b : T) : T := apT (apT (kT .Pair) a) b
def gT (a : T) : T := apT (kT .g) a
/-- The query slot `$y`, unbound. -/
def qv (n : Sp) : T := .var (.src ([], n))
/-- The copy, made by the activation at `ρ`, of the slot `(o, y)`. -/
def fv (ρ : Path) (o : Owner) (n : Sp) : T := .var (.inst ρ (.src (o, n)))

/-! ## The corpus -/

/-- Row 1: independent locals across calls. -/
def row1 : A := lt .f L (pair f1 f2)

/-- Row 2: side-by-side inlining. -/
def row2 : A := pair (ap L (k .n1)) (ap L (k .n2))

/-- Row 3: the same argument twice. -/
def row3 : A := lt .f L (pair f1 f1)

/-- Row 4: a same-spelled outsider, read. -/
def row4 : A := lt .f L (pair f1 (sv .y))

/-- Row 4w: row 4 with the outsider renamed. -/
def row4w : A := lt .f L (pair f1 (sv .w))

/-- Row 5: an outsider bound before definition. -/
def row5 : A := lt .y (k .n5) (lt .f L f1)

/-- Row 5w: row 5 with the outsider renamed. -/
def row5w : A := lt .w (k .n5) (lt .f L f1)

/-- Row 6: an outsider bound elsewhere in the scope. -/
def row6 : A := lt .f L (pair f1 (lt .y (k .n5) (sv .y)))

/-- Row 6w: row 6 with the outsider renamed. -/
def row6w : A := lt .f L (pair f1 (lt .w (k .n5) (sv .w)))

/-- Row 7: capture: the call before `$y := 5`. -/
def row7 : A := lt .f K (lt .r f1 (lt .y (k .n5) (sv .r)))

/-- Row 8: capture: the call after `$y := 5`. -/
def row8 : A := lt .f K (lt .y (k .n5) (lt .r f1 (sv .r)))

/-- Row 7u: row 7, explicit `unify`. -/
def row7u : A := lt .f K (lt .r f1 (un .y (k .n5) (sv .r)))

/-- Row 8u: row 8, explicit `unify`. -/
def row8u : A := lt .f K (un .y (k .n5) (lt .r f1 (sv .r)))

/-- Row 7ec: row 7, `K` shares `$y`. -/
def row7ec : A := lt .f Kec (lt .r f1 (lt .y (k .n5) (sv .r)))

/-- Row 8ec: row 8, `K` shares `$y`. -/
def row8ec : A := lt .f Kec (lt .y (k .n5) (lt .r f1 (sv .r)))

/-- Row 9: an intentional captured hole. -/
def row9 : A := progV .t

/-- Row 9w: row 9 with the outsider renamed to `$u`. -/
def row9w : A := progV .u

/-- Row 9u: row 9, explicit `unify`. -/
def row9u : A := lt .f (lm .z (.unify (ap (k .d) (sv .t)) (pr .z) (k .ok))) (lt .r (ap (sv .f) (ap (k .d) (k .n7))) (pair (sv .t) (sv .r)))

/-- Row 10a: nested templates, 3. -/
def row10a : A := nested .n3

/-- Row 10b: nested templates, 4. -/
def row10b : A := nested .n4

/-- Row 11: inlining with hygiene: the `let` form. -/
def row11 : A := lt .f L ctxW

/-- Row 11i: row 11 inlined as text. -/
def row11i : A := ap (lm .w (pair (ap L (k .n1)) (lt .y (pr .w) (sv .y)))) (k .n5)

/-- Row 11h: row 11 inlined hygienically (`L`’s `$y` renamed apart). -/
def row11h : A := ap (lm .w (pair (ap L2 (k .n1)) (lt .y (pr .w) (sv .y)))) (k .n5)

/-- Row 11ec: row 11, `lam w` shares `$f`. -/
def row11ec : A := lt .f L (ap (lsh .w [.f] (pair f1 (lt .y (pr .w) (sv .y)))) (k .n5))

/-- Row 11eci: row 11ec inlined as text. -/
def row11eci : A := ap (lsh .w [.f] (pair (ap L (k .n1)) (lt .y (pr .w) (sv .y)))) (k .n5)

/-- Row 12a: template capture, binding after. -/
def row12a : A := lt .r (mapT T0) (lt .y (k .n5) (sv .r))

/-- Row 12b: template capture, binding before. -/
def row12b : A := lt .y (k .n5) (mapT T0)

/-- Row 12au: row 12a, explicit `unify`. -/
def row12au : A := lt .r (mapT T0) (un .y (k .n5) (sv .r))

/-- Row 12bu: row 12b, explicit `unify`. -/
def row12bu : A := un .y (k .n5) (mapT T0)

/-- Row 12aec: row 12a, the template shares `$y`. -/
def row12aec : A := lt .r (mapT Tec) (lt .y (k .n5) (sv .r))

/-- Row 12bec: row 12b, the template shares `$y`. -/
def row12bec : A := lt .y (k .n5) (mapT Tec)

/-- Row 13a: a returned closure, two calls. -/
def row13a : A := lt .f (.fn .mk) (pair f1 f2)

/-- Row 13b: library immunity. -/
def row13b : A := lt .f (.fn .mk) (pair f1 (lt .y (k .n5) (sv .y)))

/-- Row mk2: two closures from two calls of `(mk)`. -/
def rowmk2 : A := pair (lt .f (.fn .mk) f1) (lt .p (.fn .mk) (ap (sv .p) (k .n2)))

/-- Row 14: row 9 with the lambda's crossing set `{$t}`. -/
def row14 : A := lt .f (lsh .z [.t] (.letS (ap (k .d) (sv .t)) (pr .z) (k .ok) none)) (lt .r (ap (sv .f) (ap (k .d) (k .n7))) (pair (sv .t) (sv .r)))

/-- Row 16: partial application. -/
def row16 : A := lt .p (ap (lm .z (lm .w (lt .y (pair (pr .z) (pr .w)) (sv .y)))) (k .n1)) (pair (ap (sv .p) (k .n2)) (ap (sv .p) (k .n3)))

/-- Row 18: Need sharing: one application, read twice. -/
def row18 : A := lt .f L (lt .a f1 (pair (sv .a) (sv .a)))

/-- Row 22a: caller refinement through an equation. -/
def row22a : A := lt .r (ap (ap (.fn .second) (k .ca)) (sv .t)) (pair (sv .t) (sv .r))

/-- Row 22b: caller refinement: conflict. -/
def row22b : A := ap (ap (.fn .second) (k .cc)) (sv .t)

/-- Row 23a: one slot or two: sibling `let`s. -/
def row23a : A := pair (lt .x (k .n1) (sv .x)) (lt .x (k .n2) (sv .x))

/-- Row 23b: independent local slots printing the same name. -/
def row23b : A := pair (ap L (k .n1)) (ap L (k .n2))

/-- Row 23c: a nested `let` of the same spelling. -/
def row23c : A := lt .y (k .n1) (pair (sv .y) (lt .y (k .n2) (sv .y)))

/-- Row 23cu: row 23c, explicit `unify`. -/
def row23cu : A := lt .y (k .n1) (pair (sv .y) (un .y (k .n2) (sv .y)))

/-- Row LfEq: the per-call lifted equation of `L`, called twice. -/
def rowLfEq : A := pair (ap (.fn .Lf) (k .n1)) (ap (.fn .Lf) (k .n2))

/-- Row H1: a name written only in the body, introduced by no pattern:
`(let $f (lam z $hole) (Pair ($f 1) ($f 2)))`. -/
def rowH1 : A := lt .f (lm .z (sv .hole)) (pair f1 f2)

/-- Row H2: the two holes of row H1 refined apart:
`(let $f (lam z $hole) (let* (($a ($f 1)) ($b ($f 2))) (unify $a Left (unify $b Right
(Pair $a $b)))))`, with `let*` as nested `let`s and no else branch. -/
def rowH2 : A :=
  lt .f (lm .z (sv .hole)) (lt .a f1 (lt .b f2
    (un .a (k .Left) (un .b (k .Right) (pair (sv .a) (sv .b))))))

/-- Row 4 with `L` sharing `$y`. -/
def row4ec : A := lt .f Lec (pair f1 (sv .y))
/-- Row 4 with `L` refining by `unify`. -/
def row4u : A := lt .f Lu (pair f1 (sv .y))
/-- Row 4 with `L`'s private name renamed. -/
def row4L2 : A := lt .f L2 (pair f1 (sv .y))
/-- Row 17: `(Pair (lifted $y 1) $y)`. -/
def row17eq : A := pair (ap (ap (.fn .lifted) (sv .y)) (k .n1)) (sv .y)

/-! ## Answer tables, `[M, LF, EC, Q, PC, SN]` -/

theorem row1_table :
    six clauses row1 =
      [some [(pairT (gT (kT .n1)) (gT (kT .n2)))], some [(pairT (gT (kT .n1)) (gT (kT .n2)))], some [(pairT (gT (kT .n1)) (gT (kT .n2)))], some [], some [], some [(pairT (gT (kT .n1)) (gT (kT .n2)))]] := by
  decide +kernel

theorem row2_table :
    six clauses row2 =
      [some [(pairT (gT (kT .n1)) (gT (kT .n2)))], some [(pairT (gT (kT .n1)) (gT (kT .n2)))], some [(pairT (gT (kT .n1)) (gT (kT .n2)))], some [], some [(pairT (gT (kT .n1)) (gT (kT .n2)))], some [(pairT (gT (kT .n1)) (gT (kT .n2)))]] := by
  decide +kernel

theorem row3_table :
    six clauses row3 =
      [some [(pairT (gT (kT .n1)) (gT (kT .n1)))], some [(pairT (gT (kT .n1)) (gT (kT .n1)))], some [(pairT (gT (kT .n1)) (gT (kT .n1)))], some [(pairT (gT (kT .n1)) (gT (kT .n1)))], some [(pairT (gT (kT .n1)) (gT (kT .n1)))], some [(pairT (gT (kT .n1)) (gT (kT .n1)))]] := by
  decide +kernel

theorem row4_table :
    six clauses row4 =
      [some [(pairT (gT (kT .n1)) (kT .n1))], some [(pairT (gT (kT .n1)) (qv .y))], some [(pairT (gT (kT .n1)) (qv .y))], some [(pairT (gT (kT .n1)) (kT .n1))], some [(pairT (gT (kT .n1)) (kT .n1))], some [(pairT (gT (kT .n1)) (qv .y))]] := by
  decide +kernel

theorem row4w_table :
    six clauses row4w =
      [some [(pairT (gT (kT .n1)) (qv .w))], some [(pairT (gT (kT .n1)) (qv .w))], some [(pairT (gT (kT .n1)) (qv .w))], some [(pairT (gT (kT .n1)) (qv .w))], some [(pairT (gT (kT .n1)) (qv .w))], some [(pairT (gT (kT .n1)) (qv .w))]] := by
  decide +kernel

theorem row5_table :
    six clauses row5 =
      [some [], some [(gT (kT .n1))], some [(gT (kT .n1))], some [], some [], some []] := by
  decide +kernel

theorem row5w_table :
    six clauses row5w =
      [some [(gT (kT .n1))], some [(gT (kT .n1))], some [(gT (kT .n1))], some [(gT (kT .n1))], some [(gT (kT .n1))], some [(gT (kT .n1))]] := by
  decide +kernel

theorem row6_table :
    six clauses row6 =
      [some [], some [(pairT (gT (kT .n1)) (kT .n5))], some [(pairT (gT (kT .n1)) (kT .n5))], some [], some [], some [(pairT (gT (kT .n1)) (kT .n5))]] := by
  decide +kernel

theorem row6w_table :
    six clauses row6w =
      [some [(pairT (gT (kT .n1)) (kT .n5))], some [(pairT (gT (kT .n1)) (kT .n5))], some [(pairT (gT (kT .n1)) (kT .n5))], some [(pairT (gT (kT .n1)) (kT .n5))], some [(pairT (gT (kT .n1)) (kT .n5))], some [(pairT (gT (kT .n1)) (kT .n5))]] := by
  decide +kernel

theorem row7_table :
    six clauses row7 =
      [some [(pairT (kT .n1) (kT .n5))], some [(pairT (kT .n1) (qv .y))], some [(pairT (kT .n1) (fv [0, 2] [1, 0] .y))], some [(pairT (kT .n1) (kT .n5))], some [(pairT (kT .n1) (kT .n5))], some [(pairT (kT .n1) (fv [0, 2] [] .y))]] := by
  decide +kernel

theorem row8_table :
    six clauses row8 =
      [some [(pairT (kT .n1) (kT .n5))], some [(pairT (kT .n1) (qv .y))], some [(pairT (kT .n1) (fv [1, 0, 2] [1, 0] .y))], some [(pairT (kT .n1) (kT .n5))], some [(pairT (kT .n1) (kT .n5))], some [(pairT (kT .n1) (kT .n5))]] := by
  decide +kernel

theorem row7u_table :
    six clauses row7u =
      [some [(pairT (kT .n1) (kT .n5))], some [(pairT (kT .n1) (kT .n5))], some [(pairT (kT .n1) (fv [0, 2] [1, 0] .y))], some [(pairT (kT .n1) (kT .n5))], some [(pairT (kT .n1) (kT .n5))], some [(pairT (kT .n1) (fv [0, 2] [] .y))]] := by
  decide +kernel

theorem row8u_table :
    six clauses row8u =
      [some [(pairT (kT .n1) (kT .n5))], some [(pairT (kT .n1) (kT .n5))], some [(pairT (kT .n1) (fv [1, 0, 2] [1, 0] .y))], some [(pairT (kT .n1) (kT .n5))], some [(pairT (kT .n1) (kT .n5))], some [(pairT (kT .n1) (kT .n5))]] := by
  decide +kernel

theorem row7ec_table :
    six clauses row7ec =
      [some [(pairT (kT .n1) (kT .n5))], some [(pairT (kT .n1) (qv .y))], some [(pairT (kT .n1) (kT .n5))], some [(pairT (kT .n1) (kT .n5))], some [(pairT (kT .n1) (kT .n5))], some [(pairT (kT .n1) (fv [0, 2] [] .y))]] := by
  decide +kernel

theorem row8ec_table :
    six clauses row8ec =
      [some [(pairT (kT .n1) (kT .n5))], some [(pairT (kT .n1) (qv .y))], some [(pairT (kT .n1) (kT .n5))], some [(pairT (kT .n1) (kT .n5))], some [(pairT (kT .n1) (kT .n5))], some [(pairT (kT .n1) (kT .n5))]] := by
  decide +kernel

theorem row9_table :
    six clauses row9 =
      [some [(pairT (kT .n7) (kT .ok))], some [(pairT (qv .t) (kT .ok))], some [(pairT (qv .t) (kT .ok))], some [(pairT (kT .n7) (kT .ok))], some [(pairT (kT .n7) (kT .ok))], some [(pairT (qv .t) (kT .ok))]] := by
  decide +kernel

theorem row9w_table :
    six clauses row9w =
      [some [(pairT (qv .u) (kT .ok))], some [(pairT (qv .u) (kT .ok))], some [(pairT (qv .u) (kT .ok))], some [(pairT (qv .u) (kT .ok))], some [(pairT (qv .u) (kT .ok))], some [(pairT (qv .u) (kT .ok))]] := by
  decide +kernel

theorem row9u_table :
    six clauses row9u =
      [some [(pairT (kT .n7) (kT .ok))], some [(pairT (kT .n7) (kT .ok))], some [(pairT (qv .t) (kT .ok))], some [(pairT (kT .n7) (kT .ok))], some [(pairT (kT .n7) (kT .ok))], some [(pairT (qv .t) (kT .ok))]] := by
  decide +kernel

theorem row10a_table :
    six clauses row10a =
      [some [(pairT (kT .n3) (kT .n3))], some [(pairT (kT .n3) (kT .n3))], some [(pairT (kT .n3) (kT .n3))], some [(pairT (kT .n3) (kT .n3))], some [(pairT (kT .n3) (kT .n3))], some [(pairT (kT .n3) (kT .n3))]] := by
  decide +kernel

theorem row10b_table :
    six clauses row10b =
      [some [], some [(pairT (kT .n4) (kT .n3))], some [(pairT (kT .n4) (kT .n3))], some [], some [], some []] := by
  decide +kernel

theorem row11_table :
    six clauses row11 =
      [some [(pairT (gT (kT .n1)) (kT .n5))], some [(pairT (gT (kT .n1)) (kT .n5))], some [(pairT (apT (fv [2] [2, 0, 0] .f) (kT .n1)) (kT .n5))], some [], some [(pairT (gT (kT .n1)) (kT .n5))], some [(pairT (gT (kT .n1)) (kT .n5))]] := by
  decide +kernel

theorem row11i_table :
    six clauses row11i =
      [some [], some [(pairT (gT (kT .n1)) (kT .n5))], some [(pairT (gT (kT .n1)) (kT .n5))], some [], some [], some [(pairT (gT (kT .n1)) (kT .n5))]] := by
  decide +kernel

theorem row11h_table :
    six clauses row11h =
      [some [(pairT (gT (kT .n1)) (kT .n5))], some [(pairT (gT (kT .n1)) (kT .n5))], some [(pairT (gT (kT .n1)) (kT .n5))], some [(pairT (gT (kT .n1)) (kT .n5))], some [(pairT (gT (kT .n1)) (kT .n5))], some [(pairT (gT (kT .n1)) (kT .n5))]] := by
  decide +kernel

theorem row11ec_table :
    six clauses row11ec =
      [some [(pairT (gT (kT .n1)) (kT .n5))], some [(pairT (gT (kT .n1)) (kT .n5))], some [(pairT (gT (kT .n1)) (kT .n5))], some [(pairT (gT (kT .n1)) (kT .n5))], some [(pairT (gT (kT .n1)) (kT .n5))], some [(pairT (gT (kT .n1)) (kT .n5))]] := by
  decide +kernel

theorem row11eci_table :
    six clauses row11eci =
      [some [], some [(pairT (gT (kT .n1)) (kT .n5))], some [(pairT (gT (kT .n1)) (kT .n5))], some [], some [], some [(pairT (gT (kT .n1)) (kT .n5))]] := by
  decide +kernel

theorem row12a_table :
    six clauses row12a =
      [some [(apT (apT (kT .list2) (pairT (kT .n1) (kT .n5))) (pairT (kT .n2) (kT .n5)))], some [(apT (apT (kT .list2) (pairT (kT .n1) (qv .y))) (pairT (kT .n2) (qv .y)))], some [(apT (apT (kT .list2) (pairT (kT .n1) (fv [0, 0, 1, 2] [1, 1, 0] .y))) (pairT (kT .n2) (fv [0, 1, 2] [1, 1, 0] .y)))], some [(apT (apT (kT .list2) (pairT (kT .n1) (kT .n5))) (pairT (kT .n2) (kT .n5)))], some [(apT (apT (kT .list2) (pairT (kT .n1) (kT .n5))) (pairT (kT .n2) (kT .n5)))], some [(apT (apT (kT .list2) (pairT (kT .n1) (fv [0, 0, 1, 2] [] .y))) (pairT (kT .n2) (fv [0, 1, 2] [] .y)))]] := by
  decide +kernel

theorem row12b_table :
    six clauses row12b =
      [some [(apT (apT (kT .list2) (pairT (kT .n1) (kT .n5))) (pairT (kT .n2) (kT .n5)))], some [(apT (apT (kT .list2) (pairT (kT .n1) (kT .n5))) (pairT (kT .n2) (kT .n5)))], some [(apT (apT (kT .list2) (pairT (kT .n1) (fv [1, 0, 1, 2] [2, 1, 0] .y))) (pairT (kT .n2) (fv [1, 1, 2] [2, 1, 0] .y)))], some [(apT (apT (kT .list2) (pairT (kT .n1) (kT .n5))) (pairT (kT .n2) (kT .n5)))], some [(apT (apT (kT .list2) (pairT (kT .n1) (kT .n5))) (pairT (kT .n2) (kT .n5)))], some [(apT (apT (kT .list2) (pairT (kT .n1) (kT .n5))) (pairT (kT .n2) (kT .n5)))]] := by
  decide +kernel

theorem row12au_table :
    six clauses row12au =
      [some [(apT (apT (kT .list2) (pairT (kT .n1) (kT .n5))) (pairT (kT .n2) (kT .n5)))], some [(apT (apT (kT .list2) (pairT (kT .n1) (kT .n5))) (pairT (kT .n2) (kT .n5)))], some [(apT (apT (kT .list2) (pairT (kT .n1) (fv [0, 0, 1, 2] [1, 1, 0] .y))) (pairT (kT .n2) (fv [0, 1, 2] [1, 1, 0] .y)))], some [(apT (apT (kT .list2) (pairT (kT .n1) (kT .n5))) (pairT (kT .n2) (kT .n5)))], some [(apT (apT (kT .list2) (pairT (kT .n1) (kT .n5))) (pairT (kT .n2) (kT .n5)))], some [(apT (apT (kT .list2) (pairT (kT .n1) (fv [0, 0, 1, 2] [] .y))) (pairT (kT .n2) (fv [0, 1, 2] [] .y)))]] := by
  decide +kernel

theorem row12bu_table :
    six clauses row12bu =
      [some [(apT (apT (kT .list2) (pairT (kT .n1) (kT .n5))) (pairT (kT .n2) (kT .n5)))], some [(apT (apT (kT .list2) (pairT (kT .n1) (kT .n5))) (pairT (kT .n2) (kT .n5)))], some [(apT (apT (kT .list2) (pairT (kT .n1) (fv [1, 0, 1, 2] [2, 1, 0] .y))) (pairT (kT .n2) (fv [1, 1, 2] [2, 1, 0] .y)))], some [(apT (apT (kT .list2) (pairT (kT .n1) (kT .n5))) (pairT (kT .n2) (kT .n5)))], some [(apT (apT (kT .list2) (pairT (kT .n1) (kT .n5))) (pairT (kT .n2) (kT .n5)))], some [(apT (apT (kT .list2) (pairT (kT .n1) (kT .n5))) (pairT (kT .n2) (kT .n5)))]] := by
  decide +kernel

theorem row12aec_table :
    six clauses row12aec =
      [some [(apT (apT (kT .list2) (pairT (kT .n1) (kT .n5))) (pairT (kT .n2) (kT .n5)))], some [(apT (apT (kT .list2) (pairT (kT .n1) (qv .y))) (pairT (kT .n2) (qv .y)))], some [(apT (apT (kT .list2) (pairT (kT .n1) (kT .n5))) (pairT (kT .n2) (kT .n5)))], some [(apT (apT (kT .list2) (pairT (kT .n1) (kT .n5))) (pairT (kT .n2) (kT .n5)))], some [(apT (apT (kT .list2) (pairT (kT .n1) (kT .n5))) (pairT (kT .n2) (kT .n5)))], some [(apT (apT (kT .list2) (pairT (kT .n1) (fv [0, 0, 1, 2] [] .y))) (pairT (kT .n2) (fv [0, 1, 2] [] .y)))]] := by
  decide +kernel

theorem row12bec_table :
    six clauses row12bec =
      [some [(apT (apT (kT .list2) (pairT (kT .n1) (kT .n5))) (pairT (kT .n2) (kT .n5)))], some [(apT (apT (kT .list2) (pairT (kT .n1) (kT .n5))) (pairT (kT .n2) (kT .n5)))], some [(apT (apT (kT .list2) (pairT (kT .n1) (kT .n5))) (pairT (kT .n2) (kT .n5)))], some [(apT (apT (kT .list2) (pairT (kT .n1) (kT .n5))) (pairT (kT .n2) (kT .n5)))], some [(apT (apT (kT .list2) (pairT (kT .n1) (kT .n5))) (pairT (kT .n2) (kT .n5)))], some [(apT (apT (kT .list2) (pairT (kT .n1) (kT .n5))) (pairT (kT .n2) (kT .n5)))]] := by
  decide +kernel

theorem row13a_table :
    six clauses row13a =
      [some [(pairT (gT (kT .n1)) (gT (kT .n2)))], some [(pairT (gT (kT .n1)) (gT (kT .n2)))], some [(pairT (gT (kT .n1)) (gT (kT .n2)))], some [], some [], some [(pairT (gT (kT .n1)) (gT (kT .n2)))]] := by
  decide +kernel

theorem row13b_table :
    six clauses row13b =
      [some [(pairT (gT (kT .n1)) (kT .n5))], some [(pairT (gT (kT .n1)) (kT .n5))], some [(pairT (gT (kT .n1)) (kT .n5))], some [(pairT (gT (kT .n1)) (kT .n5))], some [(pairT (gT (kT .n1)) (kT .n5))], some [(pairT (gT (kT .n1)) (kT .n5))]] := by
  decide +kernel

theorem rowmk2_table :
    six clauses rowmk2 =
      [some [(pairT (gT (kT .n1)) (gT (kT .n2)))], some [(pairT (gT (kT .n1)) (gT (kT .n2)))], some [(pairT (gT (kT .n1)) (gT (kT .n2)))], some [(pairT (gT (kT .n1)) (gT (kT .n2)))], some [(pairT (gT (kT .n1)) (gT (kT .n2)))], some [(pairT (gT (kT .n1)) (gT (kT .n2)))]] := by
  decide +kernel

theorem row14_table :
    six clauses row14 =
      [some [(pairT (kT .n7) (kT .ok))], some [(pairT (kT .n7) (kT .ok))], some [(pairT (kT .n7) (kT .ok))], some [(pairT (kT .n7) (kT .ok))], some [(pairT (kT .n7) (kT .ok))], some [(pairT (qv .t) (kT .ok))]] := by
  decide +kernel

theorem row16_table :
    six clauses row16 =
      [some [(pairT (pairT (kT .n1) (kT .n2)) (pairT (kT .n1) (kT .n3)))], some [(pairT (pairT (kT .n1) (kT .n2)) (pairT (kT .n1) (kT .n3)))], some [(pairT (pairT (kT .n1) (kT .n2)) (pairT (kT .n1) (kT .n3)))], some [], some [], some [(pairT (pairT (kT .n1) (kT .n2)) (pairT (kT .n1) (kT .n3)))]] := by
  decide +kernel

theorem row18_table :
    six clauses row18 =
      [some [(pairT (gT (kT .n1)) (gT (kT .n1)))], some [(pairT (gT (kT .n1)) (gT (kT .n1)))], some [(pairT (gT (kT .n1)) (gT (kT .n1)))], some [(pairT (gT (kT .n1)) (gT (kT .n1)))], some [(pairT (gT (kT .n1)) (gT (kT .n1)))], some [(pairT (gT (kT .n1)) (gT (kT .n1)))]] := by
  decide +kernel

theorem row22a_table :
    six clauses row22a =
      [some [(pairT (kT .cb) (apT (kT .Got) (kT .cb)))], some [(pairT (qv .t) (apT (kT .Got) (kT .cb)))], some [(pairT (kT .cb) (apT (kT .Got) (kT .cb)))], some [(pairT (kT .cb) (apT (kT .Got) (kT .cb)))], some [(pairT (kT .cb) (apT (kT .Got) (kT .cb)))], some [(pairT (kT .cb) (apT (kT .Got) (kT .cb)))]] := by
  decide +kernel

theorem row22b_table :
    six clauses row22b =
      [some [], some [(apT (kT .Got) (kT .cb))], some [], some [], some [], some []] := by
  decide +kernel

theorem row23a_table :
    six clauses row23a =
      [some [], some [(pairT (kT .n1) (kT .n2))], some [], some [], some [], some []] := by
  decide +kernel

theorem row23b_table :
    six clauses row23b =
      [some [(pairT (gT (kT .n1)) (gT (kT .n2)))], some [(pairT (gT (kT .n1)) (gT (kT .n2)))], some [(pairT (gT (kT .n1)) (gT (kT .n2)))], some [], some [(pairT (gT (kT .n1)) (gT (kT .n2)))], some [(pairT (gT (kT .n1)) (gT (kT .n2)))]] := by
  decide +kernel

theorem row23c_table :
    six clauses row23c =
      [some [], some [(pairT (kT .n1) (kT .n2))], some [], some [], some [], some []] := by
  decide +kernel

theorem row23cu_table :
    six clauses row23cu =
      [some [], some [], some [], some [], some [], some []] := by
  decide +kernel

theorem rowLfEq_table :
    six clauses rowLfEq =
      [some [(pairT (gT (kT .n1)) (gT (kT .n2)))], some [(pairT (gT (kT .n1)) (gT (kT .n2)))], some [(pairT (gT (kT .n1)) (gT (kT .n2)))], some [(pairT (gT (kT .n1)) (gT (kT .n2)))], some [(pairT (gT (kT .n1)) (gT (kT .n2)))], some [(pairT (gT (kT .n1)) (gT (kT .n2)))]] := by
  decide +kernel

theorem rowH1_table :
    six clauses rowH1 =
      [some [(pairT (fv [0, 1, 2] [1, 0] .hole) (fv [1, 2] [1, 0] .hole))], some [(pairT (qv .hole) (qv .hole))], some [(pairT (fv [0, 1, 2] [1, 0] .hole) (fv [1, 2] [1, 0] .hole))], some [(pairT (qv .hole) (qv .hole))], some [(pairT (.var (.src ([1, 0], .hole))) (.var (.src ([1, 0], .hole))))], some [(pairT (fv [0, 1, 2] [1, 0] .hole) (fv [1, 2] [1, 0] .hole))]] := by
  decide +kernel

theorem rowH2_table :
    six clauses rowH2 =
      [some [(pairT (kT .Left) (kT .Right))], some [], some [(pairT (kT .Left) (kT .Right))], some [], some [], some [(pairT (kT .Left) (kT .Right))]] := by
  decide +kernel

/-- **Lexical fresh and rule M differ on a name that no pattern introduces.**
In rows H1 and H2, `$hole` is written only in the lambda's body.  Lexical
fresh introduces names only by patterns, so the lambda owns nothing and
`$hole` is the enclosing scope's slot: both calls return the query's one hole
(H1), and refining it to `Left` and then to `Right` conflicts (H2).  Rule M
owns `$hole`, so each call has a fresh hole (H1), and the two are refined
apart (H2).  The options differ not only on refining patterns but on
body-only names. -/
theorem body_only_name :
    elabCfg cfgLF [] (lm .z (sv .hole)) = .lam (parName .z) [] (.var (.src ([], .hole))) ∧
    elabCfg cfgM [] (lm .z (sv .hole)) =
      .lam (parName .z) [([0], .hole)] (.var (.src ([0], .hole))) ∧
    ans cfgLF clauses rowH1 = some [pairT (qv .hole) (qv .hole)] ∧
    ans cfgLF clauses rowH2 = some [] ∧
    ans cfgM clauses rowH2 = some [pairT (kT .Left) (kT .Right)] := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-! ## The criterion matrix -/

/-- Decide whether two answer bags are equal. -/
def same (a b : Option (List T)) : Bool := decide (a = b)

theorem same_iff (a b : Option (List T)) : same a b = true ↔ a = b := by
  simp [same]

/-- Decide whether the six-configuration tables are equal. -/
def sameSix (a b : List (Option (List T))) : Bool := decide (a = b)

/-- **Criterion 1, lambda ≡ lifted equation.**  For every per-call reference
configuration (M, LF, EC, Q) it holds in general: `run_lifted_call` applies to
any elaborated lambda, whatever its own list, with the captured references
as extra parameters and only the own (local) slots fresh, on the whole
observation.  Witnesses: the row-4 lambda against the row-17 equation agree
under M and Q (`$y` captured), under EC when `L` shares `$y`, and under LF
when both refine by `unify` (with implicit `let`s neither refines, and they
agree too).  It breaks under PC (row 1 against the per-call lifted equation)
and under SN (the snapshot lambda against the equation's clause semantics). -/
theorem crit1_matrix :
    same (ans cfgM clauses row4) (ans cfgM clauses row17eq) = true ∧
    same (ans cfgQ clauses row4) (ans cfgQ clauses row17eq) = true ∧
    same (ans cfgEC clauses row4ec) (ans cfgEC clauses row17eq) = true ∧
    same (ans cfgLF clausesU row4u) (ans cfgLF clausesU row17eq) = true ∧
    same (ans cfgLF clauses row4) (ans cfgLF clauses row17eq) = true ∧
    same (ans cfgPC clauses row1) (ans cfgPC clauses rowLfEq) = false ∧
    same (ans cfgSN clauses row4) (ans cfgM clauses row17eq) = false := by
  decide +kernel

/-- **Criterion 2, inlining.**  Side by side (rows 1, 2): holds for M, LF,
EC, Q, SN; breaks for PC (one closure versus two).  With hygiene (row 11
against its hygienic inlining 11h, which renames `L`'s binder apart): holds
for M, LF, PC, SN; EC needs `lam w` to share `$f` (rows 11ec, 11eci); Q has
no binders, so its hygienic inlining is the text (row 11i).  Inlining the
text without renaming breaks M (row 11i), the negative control of
`elabTopM_inline`. -/
theorem crit2_matrix :
    same (ans cfgM clauses row1) (ans cfgM clauses row2) = true ∧
    same (ans cfgLF clauses row1) (ans cfgLF clauses row2) = true ∧
    same (ans cfgEC clauses row1) (ans cfgEC clauses row2) = true ∧
    same (ans cfgQ clauses row1) (ans cfgQ clauses row2) = true ∧
    same (ans cfgSN clauses row1) (ans cfgSN clauses row2) = true ∧
    same (ans cfgPC clauses row1) (ans cfgPC clauses row2) = false ∧
    same (ans cfgM clauses row11) (ans cfgM clauses row11h) = true ∧
    same (ans cfgLF clauses row11) (ans cfgLF clauses row11h) = true ∧
    same (ans cfgLF clauses row11) (ans cfgLF clauses row11i) = true ∧
    same (ans cfgPC clauses row11) (ans cfgPC clauses row11h) = true ∧
    same (ans cfgSN clauses row11) (ans cfgSN clauses row11h) = true ∧
    same (ans cfgEC clauses row11ec) (ans cfgEC clauses row11eci) = true ∧
    same (ans cfgQ clauses row11) (ans cfgQ clauses row11i) = true ∧
    same (ans cfgM clauses row11) (ans cfgM clauses row11i) = false := by
  decide +kernel

/-- **Criterion 3, order independence of capture.**  Holds for M, Q, PC (rows
7/8, 12a/12b), for LF with explicit `unify` (7u/8u, 12au/12bu), for EC when
`K` and the template share `$y` (7ec/8ec, 12aec/12bec).  Breaks for SN.  Under
LF the implicit `let $y 5` is a new lexical slot, not a refinement: rows 7
and 8 agree (neither binds `K`'s `$y`), and 12a/12b differ because the
template sits inside the `let` only in 12b. -/
theorem crit3_matrix :
    same (ans cfgM clauses row7) (ans cfgM clauses row8) = true ∧
    same (ans cfgM clauses row12a) (ans cfgM clauses row12b) = true ∧
    same (ans cfgQ clauses row7) (ans cfgQ clauses row8) = true ∧
    same (ans cfgQ clauses row12a) (ans cfgQ clauses row12b) = true ∧
    same (ans cfgPC clauses row7) (ans cfgPC clauses row8) = true ∧
    same (ans cfgPC clauses row12a) (ans cfgPC clauses row12b) = true ∧
    same (ans cfgLF clauses row7u) (ans cfgLF clauses row8u) = true ∧
    same (ans cfgLF clauses row12au) (ans cfgLF clauses row12bu) = true ∧
    same (ans cfgEC clauses row7ec) (ans cfgEC clauses row8ec) = true ∧
    same (ans cfgEC clauses row12aec) (ans cfgEC clauses row12bec) = true ∧
    same (ans cfgSN clauses row7) (ans cfgSN clauses row8) = false ∧
    same (ans cfgSN clauses row12a) (ans cfgSN clauses row12b) = false ∧
    same (ans cfgLF clauses row7) (ans cfgLF clauses row8) = true ∧
    same (ans cfgLF clauses row12a) (ans cfgLF clauses row12b) = false := by
  decide +kernel

/-- Rename the query slot `$old` to `$new` in an answer. -/
def renameQ (old new : Sp) : T → T
  | .var (.src ([], m)) => if m = old then .var (.src ([], new)) else .var (.src ([], m))
  | .app f x => .app (renameQ old new f) (renameQ old new x)
  | t => t

/-- Same-spelled outsider: the answers of a row agree with those of the row
whose outsider is renamed, up to that renaming. -/
def outsiderInvariant (c : Config) (t tw : A) : Bool :=
  decide ((ans c clauses t).map (List.map (renameQ .y .w)) = ans c clauses tw)

/-- **Criterion 4, modularity.**  Same-spelled outsiders (rows 4, 5, 6 against
4w, 5w, 6w) and renaming a private name (row 4 with `L2`): LF and EC hold;
M, Q, PC break at row 5 (and 4, 6); SN breaks at row 5 (an outsider bound
before the definition is snapshotted into the call). -/
theorem crit4_matrix :
    (outsiderInvariant cfgLF row4 row4w && outsiderInvariant cfgLF row5 row5w &&
      outsiderInvariant cfgLF row6 row6w) = true ∧
    (outsiderInvariant cfgEC row4 row4w && outsiderInvariant cfgEC row5 row5w &&
      outsiderInvariant cfgEC row6 row6w) = true ∧
    outsiderInvariant cfgM row5 row5w = false ∧
    outsiderInvariant cfgM row6 row6w = false ∧
    outsiderInvariant cfgM row4 row4w = false ∧
    outsiderInvariant cfgQ row5 row5w = false ∧
    outsiderInvariant cfgPC row5 row5w = false ∧
    outsiderInvariant cfgSN row5 row5w = false ∧
    (outsiderInvariant cfgSN row4 row4w && outsiderInvariant cfgSN row6 row6w) = true ∧
    same (ans cfgLF clauses row4) (ans cfgLF clauses row4L2) = true ∧
    same (ans cfgEC clauses row4) (ans cfgEC clauses row4L2) = true ∧
    same (ans cfgM clauses row4) (ans cfgM clauses row4L2) = false := by
  decide +kernel

/-- **Criterion 5, relational closures.**  Without annotation: M, Q, PC hold
(row 9); LF, EC, SN break.  With annotation: LF holds with `unify` (row 9u,
and row 22 with the `unify` clause) or with the crossing set (row 14: no
pattern inside makes `$t` fresh), EC with its crossing set (row 14); SN still
breaks (row 14: the shared hole is snapshotted at the call). -/
theorem crit5_matrix :
    same (ans cfgM clauses row9) (some [pairT (kT .n7) (kT .ok)]) = true ∧
    same (ans cfgQ clauses row9) (some [pairT (kT .n7) (kT .ok)]) = true ∧
    same (ans cfgPC clauses row9) (some [pairT (kT .n7) (kT .ok)]) = true ∧
    same (ans cfgLF clauses row9) (some [pairT (qv .t) (kT .ok)]) = true ∧
    same (ans cfgEC clauses row9) (some [pairT (qv .t) (kT .ok)]) = true ∧
    same (ans cfgSN clauses row9) (some [pairT (qv .t) (kT .ok)]) = true ∧
    same (ans cfgLF clauses row9u) (some [pairT (kT .n7) (kT .ok)]) = true ∧
    same (ans cfgEC clauses row14) (some [pairT (kT .n7) (kT .ok)]) = true ∧
    same (ans cfgLF clauses row14) (some [pairT (kT .n7) (kT .ok)]) = true ∧
    same (ans cfgSN clauses row14) (some [pairT (qv .t) (kT .ok)]) = true ∧
    same (ans cfgM clauses row22a) (some [pairT (kT .cb) (apT (kT .Got) (kT .cb))]) = true ∧
    same (ans cfgLF clauses row22a) (some [pairT (qv .t) (apT (kT .Got) (kT .cb))]) = true ∧
    same (ans cfgLF clausesU row22a) (some [pairT (kT .cb) (apT (kT .Got) (kT .cb))]) = true ∧
    same (ans cfgLF clauses row22b) (some [apT (kT .Got) (kT .cb)]) = true ∧
    same (ans cfgLF clausesU row22b) (some []) = true := by
  decide +kernel

/-- **Criterion 6, library immunity.**  A closure returned by an equation
keeps its local slot against the caller's same-spelled `$y` (row 13b), and two
calls of the equation make two closures (row mk2): all six hold. -/
theorem crit6_matrix :
    sameSix (six clauses row13b) (List.replicate 6 (some [pairT (gT (kT .n1)) (kT .n5)])) =
      true ∧
    sameSix (six clauses rowmk2)
      (List.replicate 6 (some [pairT (gT (kT .n1)) (gT (kT .n2))])) = true := by
  decide +kernel

/-- **Criterion 7, independent calls** (rows 1, 3, 16, 18): M, LF, EC, SN hold;
Q and PC break at rows 1 and 16 (the calls of one closure share a slot). -/
theorem crit7_matrix :
    same (ans cfgM clauses row1) (some [pairT (gT (kT .n1)) (gT (kT .n2))]) = true ∧
    same (ans cfgLF clauses row1) (ans cfgM clauses row1) = true ∧
    same (ans cfgEC clauses row1) (ans cfgM clauses row1) = true ∧
    same (ans cfgSN clauses row1) (ans cfgM clauses row1) = true ∧
    same (ans cfgQ clauses row1) (some []) = true ∧
    same (ans cfgPC clauses row1) (some []) = true ∧
    same (ans cfgM clauses row16)
      (some [pairT (pairT (kT .n1) (kT .n2)) (pairT (kT .n1) (kT .n3))]) = true ∧
    same (ans cfgLF clauses row16) (ans cfgM clauses row16) = true ∧
    same (ans cfgEC clauses row16) (ans cfgM clauses row16) = true ∧
    same (ans cfgSN clauses row16) (ans cfgM clauses row16) = true ∧
    same (ans cfgQ clauses row16) (some []) = true ∧
    same (ans cfgPC clauses row16) (some []) = true ∧
    sameSix (six clauses row3) (List.replicate 6 (some [pairT (gT (kT .n1)) (gT (kT .n1))])) =
      true ∧
    sameSix (six clauses row18) (List.replicate 6 (some [pairT (gT (kT .n1)) (gT (kT .n1))])) =
      true := by
  decide +kernel

/-- **Criterion 8, relational coherence.**  Information grows monotonically
under every configuration (`run_store_mono`, both readouts).  One shared slot
fails on inconsistency: rows 23a and 23c under M, EC, Q, PC, SN, and row 23cu
(explicit `unify`) under all six.  Independent slots never conflict: row 23b
(two activations of `L`) under every configuration with local slots (all but
Q, which has none), and rows 23a, 23c under LF, whose sibling or nested `let`s
are distinct slots. -/
theorem crit8_matrix :
    sameSix (six clauses row23a)
      [some [], some [pairT (kT .n1) (kT .n2)], some [], some [], some [], some []] = true ∧
    sameSix (six clauses row23c)
      [some [], some [pairT (kT .n1) (kT .n2)], some [], some [], some [], some []] = true ∧
    sameSix (six clauses row23cu) (List.replicate 6 (some [])) = true ∧
    sameSix (six clauses row23b) [some [pairT (gT (kT .n1)) (gT (kT .n2))],
      some [pairT (gT (kT .n1)) (gT (kT .n2))], some [pairT (gT (kT .n1)) (gT (kT .n2))],
      some [], some [pairT (gT (kT .n1)) (gT (kT .n2))],
      some [pairT (gT (kT .n1)) (gT (kT .n2))]] = true := by
  decide +kernel

/-! ## Headline (a): the 4-versus-5 tension, observationally -/

/-- **The observational tension.**  Take any semantics of the
annotation-free family `progV v` (row 9 with its outsider spelled `v`).  If
the lambda's name is private when the context does not write it (P, at
`v = u`), and renaming the outsider is invisible (Mod: the answers at `v = t`
are those at `v = u`, renamed), then row 9 cannot refine its hole (Rel). -/
theorem observational_tension (Sem : Sp → Option (List T)) (rn : T → T)
    (hP : Sem .u = some [pairT (qv .u) (kT .ok)])
    (hMod : Sem .t = (Sem .u).map (List.map rn))
    (hrn : rn (pairT (qv .u) (kT .ok)) = pairT (qv .t) (kT .ok)) :
    Sem .t ≠ some [pairT (kT .n7) (kT .ok)] := by
  rw [hMod, hP, Option.map_some, List.map_cons, List.map_nil, hrn]
  decide

/-- Each configuration's verdicts on the family: P, Rel, Mod. -/
def tensionSides (c : Config) : Bool × Bool × Bool :=
  (same (ans c clauses (progV .u)) (some [pairT (qv .u) (kT .ok)]),
   same (ans c clauses (progV .t)) (some [pairT (kT .n7) (kT .ok)]),
   same (ans c clauses (progV .t)) ((ans c clauses (progV .u)).map (List.map (renameQ .u .t))))

/-- The class is not vacuous, and each configuration takes a side: all six
have P; M, Q and PC have Rel and not Mod; LF, EC and SN have Mod and not
Rel.  None has all three, as `observational_tension` requires. -/
theorem observational_tension_sides :
    tensionSides cfgM = (true, true, false) ∧ tensionSides cfgQ = (true, true, false) ∧
    tensionSides cfgPC = (true, true, false) ∧ tensionSides cfgLF = (true, false, true) ∧
    tensionSides cfgEC = (true, false, true) ∧ tensionSides cfgSN = (true, false, true) := by
  decide +kernel

/-- With explicit sharing both hold: EC's annotated row 9 (row 14) refines,
and its ownership never depends on the context (`ownRuleEC_both`,
`elabEC_congr`); LF's `unify` spelling (row 9u) refines, and its elaboration
reads the context only at the names it does not bind (`elabLF_congr`). -/
theorem explicit_sharing_has_both :
    same (ans cfgEC clauses row14) (some [pairT (kT .n7) (kT .ok)]) = true ∧
    same (ans cfgLF clauses row9u) (some [pairT (kT .n7) (kT .ok)]) = true ∧
    same (ans cfgEC clauses (progV .u)) (some [pairT (qv .u) (kT .ok)]) = true ∧
    same (ans cfgLF clauses (progV .u)) (some [pairT (qv .u) (kT .ok)]) = true := by
  decide +kernel

/-! ## Headline (b): modularity at the elaboration level -/

/-- Rule M's ownership of `L` depends on the context: with `$y` written at an
enclosing level, `L` captures it.  Explicit capture and lexical fresh
elaborate `L` identically in every context (`elabEC_closed_lam`,
`elabLF_congr`). -/
theorem elaboration_context_dependence :
    elabMS [] (fun _ => []) [] L ≠ elabMS [.y] (fun _ => []) [] L ∧
    elabEC (fun _ => []) [] L = elabEC (fun m => if m = .y then [3] else []) [] L ∧
    elabLF (fun _ => []) [] [] L = elabLF (fun m => if m = .y then [3] else []) [] [] L := by
  refine ⟨by decide +kernel, elabEC_closed_lam _ _ _ _ _, elabLF_congr _ _ _ _ _ ?_⟩
  decide

end Mettapedia.GSLT.LanguageDef.TemplateScope.SpectrumCorpus
