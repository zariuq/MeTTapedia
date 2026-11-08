import Mathlib.Tactic

/-!
# Admission normal forms: the rewrite system and its termination

A compiled tier that admits programs by spelling refuses forms the language defines as
equal to forms it accepts: the two-armed `if`, `let*`, a single-branch `case`, `id`, a
singleton `superpose`, the callable spellings of the list iterators, a size observer
applied to a computation, a bare `once`, and `min`.  This file orients those equalities
as rewrite rules into the spellings the tier admits.  Each rule keeps its call's
protocol: what is evaluated, in which order, how often, and how alternatives combine.

**The fragment.**  `Tm` is the admission fragment of MeTTa, with variables as de Bruijn
indices: `let_ e b` binds index 0 in `b`; `letStar es b` binds one index per source, the
`i`-th source sitting under `i` binders and the body under all of them; a `case` branch
whose pattern is `bind` binds index 0 in its body; an iteration body form binds one index
per variable it names (`foldl` two: index 1 the accumulator, index 0 the element).  A
`quote` is a held position: its term is data, and no rule rewrites inside it.  Strict calls
`call f args` cover library heads (`id`, `size-atom`, `min`, `<`, `<=`) and user functions.  An
elaborator maps a dialect's surface syntax to this fragment; in particular, a dialect that
holds an argument (an `Atom`-typed parameter, or the `Expression` argument of `size-atom`
in HE) elaborates it as a `quote`.

**Facts.**  `Facts` records which indices are known to hold integers; a binder pushes an
index without facts.  No rule reads them now; they remain the hook of analyses over the
fragment (`LocalDeclines.intCalls`).

**Shifting.**  `shift c` lifts the free indices at or above `c` by one, under binders at
their depths, and leaves held positions as written: a term moved under one more binder.

**Rules** (`Rule`), and the context condition of `once`:
* `if2`: `(if c t)` → `(if c t (empty))`;
* `letStar`: `(let* ((x1 e1) … (xn en)) b)` → `(let x1 e1 (… (let xn en b)))`;
* `case1`: `(case e (($x b)))` → `(let $x e b)`, for a binding pattern;
* `id`: `(id x)` → `x`;
* `sup1`: `(superpose (x))` → `x`;
* `callable`: a callable iterator → its body form, the body calling the callable on the
  bound variables;
* `size`: `(size-atom e)` → `(let $v e (size-atom $v))`, for `e` not a variable;
* `min`: `(min a b)` → `(let $x a (let $y b (if (<= $x $y) $x $y)))`: `a` once, then `b`
  once for each answer of `a`, as `min`'s arguments are evaluated, then the first argument
  unless it is not `<=` the second.  The rule is sound on a dialect whose `min` is that
  test on every pair of values (`Semantics.Ready.min`); it replaces the rule that rewrote
  integer atoms to `(if (< a b) a b)`, which answers the second argument on ties;
* `sizeVar`: `(let $v $x (size-atom $v))` → `(size-atom $x)`;
* `letEta`: `(let $x (let $y e $y) b)` → `(let $x e b)`;
* `wrap` (a `Step` constructor): `(once b)` → `(let $y (once b) $y)`, except where the
  `once` already is the source of a `let`.

`sizeVar` and `letEta` are the completion of the system.  Its critical pairs are:
* `size` against any rule that turns the argument into a variable (`id`, `sup1`, the
  empty `letStar`): `(size-atom (id $x))` reaches `(let $v $x (size-atom $v))` one way and
  `(size-atom $x)` the other; `sizeVar` joins them;
* `wrap` against every rule that moves a term into the source of a `let` (`letStar`,
  `case1`, `size`, and `id`/`sup1` under a `let` source): `(case (once b) (($x B)))`
  reaches `(let $x (once b) B)` one way and `(let $x (let $y (once b) $y) B)` the other;
  `letEta` joins them.
The other overlaps are variable overlaps of left-linear rules that neither duplicate
nor erase a reducible subterm (`min` moves its second argument under one binder, by
`shift`, which the normalizer commutes with).  `Normalizer` proves the
joins: the normalizer is invariant under every step, which gives confluence.

**Steps.**  `Step top Γ` is the closure of the rules under every position except held
ones; `top` is `false` exactly at the source of a `let`, where `wrap` does not fire.

This file proves `step_decreases` (each step lowers the measure `μ`) and
`step_wellFounded` (no infinite rewriting, in any order).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.AdmissionRewriting

/-- Symbols the rules and controls distinguish. -/
inductive Sym
  | tru
  | fls
  | emp
  | other (n : ℕ)
  deriving DecidableEq, Repr

/-- Literals: integers and symbols. -/
inductive Lit
  | int (n : ℤ)
  | sym (s : Sym)
  deriving DecidableEq, Repr

/-- A branch pattern: a binding variable, or a literal. -/
inductive Pat
  | bind
  | lit (l : Lit)
  deriving DecidableEq, Repr

/-- Heads of strict calls. -/
inductive Name
  | id
  | size
  | min
  | lt
  | le
  | user (n : ℕ)
  deriving DecidableEq, Repr

/-- The list iterators. -/
inductive Iter
  | foldl
  | map
  | filter
  deriving DecidableEq, Repr

/-- The variables an iterator's body form binds. -/
def Iter.binders : Iter → ℕ
  | .foldl => 2
  | .map => 1
  | .filter => 1

/-- The admission fragment, de Bruijn style. -/
inductive Tm
  | var (k : ℕ)
  | lit (l : Lit)
  | quote (t : Tm)
  | tup (xs : List Tm)
  | empty
  | if3 (c t e : Tm)
  | if2 (c t : Tm)
  | let_ (e b : Tm)
  | letStar (es : List Tm) (b : Tm)
  | case_ (e : Tm) (alts : List (Pat × Tm))
  | sup (xs : List Tm)
  | once (b : Tm)
  | call (f : Name) (args : List Tm)
  | iterC (k : Iter) (ops : List Tm) (f : Name)
  | iterB (k : Iter) (ops : List Tm) (body : Tm)

/-- The bound variables an iterator's body form passes to the callable, in call order
(`foldl`: accumulator, element). -/
def Iter.vars : Iter → List Tm
  | .foldl => [.var 1, .var 0]
  | .map => [.var 0]
  | .filter => [.var 0]

/-- Integer facts per de Bruijn index. -/
abbrev Facts := ℕ → Bool

/-- Under a binder: the new index carries no fact. -/
def push (Γ : Facts) : Facts
  | 0 => false
  | k + 1 => Γ k

/-- Under `n` binders. -/
def pushN : ℕ → Facts → Facts
  | 0, Γ => Γ
  | n + 1, Γ => pushN n (push Γ)

/-- The facts a branch body sees. -/
def Pat.scope : Pat → Facts → Facts
  | .bind, Γ => push Γ
  | .lit _, Γ => Γ

/-- The binders a branch pattern introduces. -/
def Pat.binders : Pat → ℕ
  | .bind => 1
  | .lit _ => 0

mutual
/-- Lift the free indices at or above `c` by one.  A held position is data: its term stays
as written. -/
def shift (c : ℕ) : Tm → Tm
  | .var k => .var (if k < c then k else k + 1)
  | .lit l => .lit l
  | .quote t => .quote t
  | .tup xs => .tup (shifts c xs)
  | .empty => .empty
  | .if3 a b d => .if3 (shift c a) (shift c b) (shift c d)
  | .if2 a b => .if2 (shift c a) (shift c b)
  | .let_ e b => .let_ (shift c e) (shift (c + 1) b)
  | .letStar es b => .letStar (shiftLS c es) (shift (c + es.length) b)
  | .case_ e alts => .case_ (shift c e) (shiftAlts c alts)
  | .sup xs => .sup (shifts c xs)
  | .once b => .once (shift c b)
  | .call f args => .call f (shifts c args)
  | .iterC k ops f => .iterC k (shifts c ops) f
  | .iterB k ops b => .iterB k (shifts c ops) (shift (c + k.binders) b)
/-- Terms at one depth. -/
def shifts (c : ℕ) : List Tm → List Tm
  | [] => []
  | x :: xs => shift c x :: shifts c xs
/-- `let*` sources, each one binder deeper. -/
def shiftLS (c : ℕ) : List Tm → List Tm
  | [] => []
  | e :: es => shift c e :: shiftLS (c + 1) es
/-- Branches: a binding pattern's body one binder deeper. -/
def shiftAlts (c : ℕ) : List (Pat × Tm) → List (Pat × Tm)
  | [] => []
  | (p, b) :: rest => (p, shift (c + p.binders) b) :: shiftAlts c rest
end

/-- The test of `min`'s protocol form: the first argument (index 1) unless it is not `<=`
the second (index 0). -/
def minIf : Tm := .if3 (.call .le [.var 1, .var 0]) (.var 1) (.var 0)

/-- `(let $x a (let $y b (if (<= $x $y) $x $y)))`: `b` moved under the binder of `$x`. -/
def minForm (a b : Tm) : Tm := .let_ a (.let_ (shift 0 b) minIf)

/-- An integer atom: an integer literal, or a variable known to hold an integer. -/
def IntAtom (Γ : Facts) : Tm → Bool
  | .lit (.int _) => true
  | .var k => Γ k
  | _ => false

/-- `let*` as nested `let`s. -/
def nest : List Tm → Tm → Tm
  | [], b => b
  | e :: es, b => .let_ e (nest es b)

/-- The rules, at the root. -/
inductive Rule (Γ : Facts) : Tm → Tm → Prop
  | if2 (c t : Tm) : Rule Γ (.if2 c t) (.if3 c t .empty)
  | letStar (es : List Tm) (b : Tm) : Rule Γ (.letStar es b) (nest es b)
  | case1 (e b : Tm) : Rule Γ (.case_ e [(.bind, b)]) (.let_ e b)
  | id (x : Tm) : Rule Γ (.call .id [x]) x
  | sup1 (x : Tm) : Rule Γ (.sup [x]) x
  | callable (k : Iter) (ops : List Tm) (f : Name) :
      Rule Γ (.iterC k ops f) (.iterB k ops (.call f k.vars))
  | size (e : Tm) (h : ∀ j, e ≠ .var j) :
      Rule Γ (.call .size [e]) (.let_ e (.call .size [.var 0]))
  | min (a b : Tm) : Rule Γ (.call .min [a, b]) (minForm a b)
  | sizeVar (j : ℕ) : Rule Γ (.let_ (.var j) (.call .size [.var 0])) (.call .size [.var j])
  | letEta (e b : Tm) : Rule Γ (.let_ (.let_ e (.var 0)) b) (.let_ e b)

/-- One rewrite step: a rule at any position that is not held; `top` is `false` at the
source of a `let`, where a `once` is not wrapped. -/
inductive Step : Bool → Facts → Tm → Tm → Prop
  | rule {top : Bool} {Γ : Facts} {t t' : Tm} : Rule Γ t t' → Step top Γ t t'
  | wrap {Γ : Facts} (b : Tm) : Step true Γ (.once b) (.let_ (.once b) (.var 0))
  | tup {top : Bool} {Γ : Facts} (pre post : List Tm) {x x' : Tm} :
      Step true Γ x x' → Step top Γ (.tup (pre ++ x :: post)) (.tup (pre ++ x' :: post))
  | if3c {top : Bool} {Γ : Facts} {c c' : Tm} (t e : Tm) :
      Step true Γ c c' → Step top Γ (.if3 c t e) (.if3 c' t e)
  | if3t {top : Bool} {Γ : Facts} (c : Tm) {t t' : Tm} (e : Tm) :
      Step true Γ t t' → Step top Γ (.if3 c t e) (.if3 c t' e)
  | if3e {top : Bool} {Γ : Facts} (c t : Tm) {e e' : Tm} :
      Step true Γ e e' → Step top Γ (.if3 c t e) (.if3 c t e')
  | if2c {top : Bool} {Γ : Facts} {c c' : Tm} (t : Tm) :
      Step true Γ c c' → Step top Γ (.if2 c t) (.if2 c' t)
  | if2t {top : Bool} {Γ : Facts} (c : Tm) {t t' : Tm} :
      Step true Γ t t' → Step top Γ (.if2 c t) (.if2 c t')
  | letE {top : Bool} {Γ : Facts} {e e' : Tm} (b : Tm) :
      Step false Γ e e' → Step top Γ (.let_ e b) (.let_ e' b)
  | letB {top : Bool} {Γ : Facts} (e : Tm) {b b' : Tm} :
      Step true (push Γ) b b' → Step top Γ (.let_ e b) (.let_ e b')
  | letStarE {top : Bool} {Γ : Facts} (pre post : List Tm) {e e' : Tm} (b : Tm) :
      Step true (pushN pre.length Γ) e e' →
        Step top Γ (.letStar (pre ++ e :: post) b) (.letStar (pre ++ e' :: post) b)
  | letStarB {top : Bool} {Γ : Facts} (es : List Tm) {b b' : Tm} :
      Step true (pushN es.length Γ) b b' → Step top Γ (.letStar es b) (.letStar es b')
  | caseE {top : Bool} {Γ : Facts} {e e' : Tm} (alts : List (Pat × Tm)) :
      Step true Γ e e' → Step top Γ (.case_ e alts) (.case_ e' alts)
  | caseB {top : Bool} {Γ : Facts} (e : Tm) (pre post : List (Pat × Tm)) (p : Pat)
      {b b' : Tm} :
      Step true (p.scope Γ) b b' →
        Step top Γ (.case_ e (pre ++ (p, b) :: post)) (.case_ e (pre ++ (p, b') :: post))
  | sup {top : Bool} {Γ : Facts} (pre post : List Tm) {x x' : Tm} :
      Step true Γ x x' → Step top Γ (.sup (pre ++ x :: post)) (.sup (pre ++ x' :: post))
  | once {top : Bool} {Γ : Facts} {b b' : Tm} :
      Step true Γ b b' → Step top Γ (.once b) (.once b')
  | call {top : Bool} {Γ : Facts} (f : Name) (pre post : List Tm) {x x' : Tm} :
      Step true Γ x x' → Step top Γ (.call f (pre ++ x :: post)) (.call f (pre ++ x' :: post))
  | iterCOps {top : Bool} {Γ : Facts} (k : Iter) (pre post : List Tm) {x x' : Tm} (f : Name) :
      Step true Γ x x' →
        Step top Γ (.iterC k (pre ++ x :: post) f) (.iterC k (pre ++ x' :: post) f)
  | iterBOps {top : Bool} {Γ : Facts} (k : Iter) (pre post : List Tm) {x x' : Tm} (b : Tm) :
      Step true Γ x x' →
        Step top Γ (.iterB k (pre ++ x :: post) b) (.iterB k (pre ++ x' :: post) b)
  | iterBBody {top : Bool} {Γ : Facts} (k : Iter) (ops : List Tm) {b b' : Tm} :
      Step true (pushN k.binders Γ) b b' → Step top Γ (.iterB k ops b) (.iterB k ops b')

/-- A step at the source of a `let` is a step anywhere. -/
theorem Step.toTrue {top : Bool} {Γ : Facts} {t t' : Tm} (h : Step top Γ t t') :
    Step true Γ t t' := by
  cases h with
  | rule r => exact .rule r
  | wrap b => exact .wrap b
  | tup pre post h => exact .tup pre post h
  | if3c t e h => exact .if3c t e h
  | if3t c e h => exact .if3t c e h
  | if3e c t h => exact .if3e c t h
  | if2c t h => exact .if2c t h
  | if2t c h => exact .if2t c h
  | letE b h => exact .letE b h
  | letB e h => exact .letB e h
  | letStarE pre post b h => exact .letStarE pre post b h
  | letStarB es h => exact .letStarB es h
  | caseE alts h => exact .caseE alts h
  | caseB e pre post p h => exact .caseB e pre post p h
  | sup pre post h => exact .sup pre post h
  | once h => exact .once h
  | call f pre post h => exact .call f pre post h
  | iterCOps k pre post f h => exact .iterCOps k pre post f h
  | iterBOps k pre post b h => exact .iterBOps k pre post b h
  | iterBBody k ops h => exact .iterBBody k ops h

/-! ## Termination -/

/-- The weight of a call node: a size observer of a computation, and `min`, weigh more
than the spellings they rewrite to. -/
def callWeight : Name → List Tm → ℕ
  | .size, [.var _] => 1
  | .size, _ => 5
  | .min, _ => 9
  | _, _ => 1

mutual
/-- The termination measure; a bare `once` outside a `let` source weighs 3 more. -/
def μ : Bool → Tm → ℕ
  | _, .var _ => 1
  | _, .lit _ => 1
  | _, .quote _ => 1
  | _, .tup xs => 1 + μs xs
  | _, .empty => 1
  | _, .if3 c t e => 1 + μ true c + μ true t + μ true e
  | _, .if2 c t => 3 + μ true c + μ true t
  | _, .let_ e b => 1 + μ false e + μ true b
  | _, .letStar es b => 1 + μs es + es.length + μ true b
  | _, .case_ e alts => 2 + μ true e + μAlts alts
  | _, .sup xs => 1 + μs xs
  | top, .once b => (if top then 4 else 1) + μ true b
  | _, .call f args => callWeight f args + μs args
  | _, .iterC _ ops _ => 14 + μs ops
  | _, .iterB _ ops b => 1 + μs ops + μ true b
/-- The measure of a list of terms in non-source positions. -/
def μs : List Tm → ℕ
  | [] => 0
  | x :: xs => μ true x + μs xs
/-- The measure of a list of branches. -/
def μAlts : List (Pat × Tm) → ℕ
  | [] => 0
  | (_, b) :: rest => 1 + μ true b + μAlts rest
end

theorem μ_false_le (t : Tm) : μ false t ≤ μ true t := by
  cases t <;> simp [μ]

theorem μ_le_true (top : Bool) (t : Tm) : μ top t ≤ μ true t := by
  cases top
  · exact μ_false_le t
  · exact le_rfl

theorem μs_append (xs ys : List Tm) : μs (xs ++ ys) = μs xs + μs ys := by
  induction xs with
  | nil => simp [μs]
  | cons x xs ih => simp only [List.cons_append, μs, ih]; omega

theorem μAlts_append (xs ys : List (Pat × Tm)) : μAlts (xs ++ ys) = μAlts xs + μAlts ys := by
  induction xs with
  | nil => simp [μAlts]
  | cons a xs ih => obtain ⟨p, b⟩ := a; simp only [List.cons_append, μAlts, ih]; omega

theorem μ_nest (top : Bool) (es : List Tm) (b : Tm) :
    μ top (nest es b) + 1 ≤ 1 + μs es + es.length + μ true b := by
  induction es generalizing top with
  | nil => simp only [nest, μs, List.length_nil]; have := μ_le_true top b; omega
  | cons e es ih =>
    simp only [nest, μ, μs, List.length_cons]
    have h1 := ih true
    have h2 := μ_false_le e
    omega

theorem μ_of_intAtom {Γ : Facts} {a : Tm} (h : IntAtom Γ a = true) (top : Bool) :
    μ top a = 1 := by
  cases a with
  | var k => simp [μ]
  | lit l => simp [μ]
  | _ => simp [IntAtom] at h

theorem μ_lt_one_add (top : Bool) (x : Tm) : μ top x < 1 + μ true x := by
  have := μ_le_true top x; omega

theorem callWeight_shifts (f : Name) (c : ℕ) (args : List Tm) :
    callWeight f (shifts c args) = callWeight f args := by
  cases f with
  | size =>
    rcases args with _ | ⟨x, _ | ⟨y, rest⟩⟩
    · rfl
    · cases x <;> simp [shifts, shift, callWeight]
    · simp [shifts, callWeight]
  | _ => simp [callWeight]

mutual
/-- Shifting leaves the measure alone. -/
theorem μ_shift : ∀ (top : Bool) (c : ℕ) (t : Tm), μ top (shift c t) = μ top t
  | _, _, .var _ => rfl
  | _, _, .lit _ => rfl
  | _, _, .quote _ => rfl
  | _, c, .tup xs => by simp only [shift, μ, μs_shifts c xs]
  | _, _, .empty => rfl
  | _, c, .if3 a b d => by simp only [shift, μ, μ_shift true c a, μ_shift true c b, μ_shift true c d]
  | _, c, .if2 a b => by simp only [shift, μ, μ_shift true c a, μ_shift true c b]
  | _, c, .let_ e b => by simp only [shift, μ, μ_shift false c e, μ_shift true (c + 1) b]
  | _, c, .letStar es b => by
    simp only [shift, μ, μs_shiftLS c es, shiftLS_length c es, μ_shift true (c + es.length) b]
  | _, c, .case_ e alts => by simp only [shift, μ, μ_shift true c e, μAlts_shiftAlts c alts]
  | _, c, .sup xs => by simp only [shift, μ, μs_shifts c xs]
  | top, c, .once b => by simp only [shift, μ, μ_shift true c b]
  | _, c, .call f args => by simp only [shift, μ, μs_shifts c args, callWeight_shifts]
  | _, c, .iterC k ops f => by simp only [shift, μ, μs_shifts c ops]
  | _, c, .iterB k ops b => by
    simp only [shift, μ, μs_shifts c ops, μ_shift true (c + k.binders) b]
theorem μs_shifts : ∀ (c : ℕ) (xs : List Tm), μs (shifts c xs) = μs xs
  | _, [] => rfl
  | c, x :: xs => by simp only [shifts, μs, μ_shift true c x, μs_shifts c xs]
theorem μs_shiftLS : ∀ (c : ℕ) (es : List Tm), μs (shiftLS c es) = μs es
  | _, [] => rfl
  | c, e :: es => by simp only [shiftLS, μs, μ_shift true c e, μs_shiftLS (c + 1) es]
theorem μAlts_shiftAlts : ∀ (c : ℕ) (alts : List (Pat × Tm)), μAlts (shiftAlts c alts) = μAlts alts
  | _, [] => rfl
  | c, (p, b) :: rest => by
    simp only [shiftAlts, μAlts, μ_shift true (c + p.binders) b, μAlts_shiftAlts c rest]
theorem shiftLS_length : ∀ (c : ℕ) (es : List Tm), (shiftLS c es).length = es.length
  | _, [] => rfl
  | c, _ :: es => by simp only [shiftLS, List.length_cons, shiftLS_length (c + 1) es]
end

theorem rule_decreases {Γ : Facts} {t t' : Tm} (h : Rule Γ t t') (top : Bool) :
    μ top t' < μ top t := by
  cases h with
  | if2 c t => simp only [μ]; omega
  | letStar es b => have := μ_nest top es b; simp only [μ]; omega
  | case1 e b => have := μ_false_le e; simp only [μ, μAlts]; omega
  | id => simpa [μ, μs, callWeight] using μ_lt_one_add top _
  | sup1 => simpa [μ, μs] using μ_lt_one_add top _
  | callable k ops f =>
    cases k <;> simp only [μ, Iter.vars, μs] <;>
      (rcases f with _ | _ | _ | _ | _ | _ <;> simp [callWeight] <;> omega)
  | size e he =>
    have h2 := μ_false_le e
    have hw : callWeight .size [e] = 5 := by
      cases e with
      | var j => exact absurd rfl (he j)
      | _ => rfl
    simp only [μ, μs, hw, show callWeight .size [.var 0] = 1 from rfl]; omega
  | min a b =>
    have ha := μ_false_le a
    have hb := μ_false_le b
    simp only [minForm, minIf, μ, μs, μ_shift,
      show callWeight .min [a, b] = 9 from rfl,
      show callWeight .le [Tm.var 1, Tm.var 0] = 1 from rfl]
    omega
  | sizeVar j => simp [μ, μs, callWeight]
  | letEta e b => simp only [μ]; omega

/-- Every step lowers the measure. -/
theorem step_decreases {top : Bool} {Γ : Facts} {t t' : Tm} (h : Step top Γ t t') :
    μ top t' < μ top t := by
  induction h with
  | rule r => exact rule_decreases r _
  | wrap b => simp only [μ, if_true, Bool.false_eq_true, if_false]; omega
  | tup pre post _ ih => simp only [μ, μs_append, μs]; omega
  | if3c t e _ ih => simp only [μ]; omega
  | if3t c e _ ih => simp only [μ]; omega
  | if3e c t _ ih => simp only [μ]; omega
  | if2c t _ ih => simp only [μ]; omega
  | if2t c _ ih => simp only [μ]; omega
  | letE b _ ih => simp only [μ]; omega
  | letB e _ ih => simp only [μ]; omega
  | letStarE pre post b _ ih =>
    simp only [μ, μs_append, μs, List.length_append, List.length_cons]; omega
  | letStarB es _ ih => simp only [μ]; omega
  | caseE alts _ ih => simp only [μ]; omega
  | caseB e pre post p _ ih => simp only [μ, μAlts_append, μAlts]; omega
  | sup pre post _ ih => simp only [μ, μs_append, μs]; omega
  | @once top Γ b b' _ ih => simp only [μ]; split <;> omega
  | @call top Γ f pre post x x' hx ih =>
    simp only [μ, μs_append, μs]
    have hw : callWeight f (pre ++ x' :: post) ≤ callWeight f (pre ++ x :: post) := by
      cases f with
      | size =>
        rcases pre with _ | ⟨p, pre⟩
        · rcases post with _ | ⟨q, post⟩
          · cases x with
            | var j => cases hx with
              | rule r => cases r
            | _ => simp only [List.nil_append]; cases x' <;> simp [callWeight]
          · simp [callWeight]
        · simp [callWeight]
      | _ => simp [callWeight]
    omega
  | iterCOps k pre post f _ ih => simp only [μ, μs_append, μs]; omega
  | iterBOps k pre post b _ ih => simp only [μ, μs_append, μs]; omega
  | iterBBody k ops _ ih => simp only [μ]; omega

/-- Rewriting terminates in every order: the converse of each step relation is
well-founded. -/
theorem step_wellFounded (top : Bool) (Γ : Facts) :
    WellFounded (fun t' t => Step top Γ t t') :=
  Subrelation.wf (fun h => step_decreases h) (InvImage.wf (μ top) wellFounded_lt)

end Mettapedia.Machines.AdmissionRewriting
