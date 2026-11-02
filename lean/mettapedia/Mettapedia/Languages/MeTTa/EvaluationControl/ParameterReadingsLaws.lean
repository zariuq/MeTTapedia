import Mettapedia.Languages.MeTTa.EvaluationControl.ParameterReadings

/-!
# The one-marker rule, law by law

Each law of `ParameterReadings` is tested here on the programs that probe it, under the one-marker
rule (`oneMarker`: only `Atom` and `(Data T)` hold) and under the readings it is contrasted with.
Every answer below is computed by the kernel.

**Law 1, renaming** (`holds_rename`, `uniform_rename_fails_iff`). Before the switch, `(Data T)`
held and `Atom` was the top type, held only at a grounded operation, at a declaration of the
standard library written in HE, or at a call whose head is not a symbol (`oldHolds`). Spelling an
old `Atom` as `Proc` where it ran and as `Atom` where it held gives the new rule exactly; spelling
every old `Atom` as `Proc` differs exactly at those exempt positions.

**Law 2, weakening within a line.** `Number`, `Proc` and an undeclared parameter give the same
answers on the line's programs, except the type errors that `Number` raises (`line_weakening`,
`line_*`). Moving between the lines, `Number` to `Atom`, changes answers with no type error removed
(`between_lines_not_weakening`). Readings whose demand depends on the declared type break the law:
running a checked argument at the call (`eagerChecked_breaks_weakening`), and checking a copy of
the argument that the body then runs again (`copyChecked_breaks_weakening`). Running every argument
again at each use keeps the law but loses the shared choice (`byName_keeps_weakening`,
`byName_loses_shared_choice`); running every argument at the call keeps it but is not by need
(`eagerAll_not_by_need`).

**Law 3, when a value runs again** (`Rerun`). Three candidates, from the lanes: `substitute` (a
value read by `match` or bound by `let` runs again where it lands: HE), `forward` (syntax held by a
parameter runs when passed to a running parameter: the draft before the switch), and `stay`
(nothing runs again except by `eval`: PeTTa, and the draft now). A `match` unifies its pattern
with each row read in the reading's role (`eval_matchSelf`): under `stay` and `forward` the role of
a value (`bindRole_marks`), so every variable it binds is bound to a value (`wrap_val_marks`), and
a value evaluates to itself (`eval_val`); under `substitute` the plain role
(`bindRole_substitute`). On ground rows, `(match &self p $x)` answers each matched part as a value
under `stay` and `forward` and runs it under `substitute` (`match_reads_values`,
`match_runs_reads` in `ParameterReadingsMatching`). Their answers on reading a row, on a computed
`let` source, on a transform-like read, on forwarding, and on a client's message read from a space
(`rerun_*`).

**Law 4, checks see values.** Forcing an argument checks the value it computes, with the branch's
bindings applied (`checks_see_values`), and the check adds no binding (`checks_never_bind`). The
draft judges a running parameter once, on the written argument, before it runs (`draftCheck`).
With those verdicts the evaluator gives the draft's answers on the probe table (`draft_table`);
with verdicts on values it gives the answers the law requires (`value_table`). The draft's verdict
is not a function of the value (`draft_does_not_see_values`).

**Two-way unification** (`unify_*`). A call binds the caller's variables through a row's head and
through the callee's `let`; a row stored with variables is renamed apart at each use and its
variables are bound by `match`; `let` unifies both ways; a pattern head runs a by-need argument and
a variable head does not; an unbound variable passes a check and stays unbound, so a later binding
can reach a value a check has accepted. Each call renames its row apart, so unfolding a call must
rename it too (`unfold_needs_renaming`).

**Law 6, type variables** (`tvar_*`). A parameter typed `$t` runs: weakening it keeps answers, it
runs by need, and a polymorphic `apply` does not pass syntax through to an `Atom` parameter.

**Law 7, the shape rule** (`shapeRule`). Holding when the argument already has the declared
metatype keeps every call written at an `Expression` parameter (`shape_expression_holds_calls`),
so such a parameter never receives a computed expression, and weakening `Expression` to an
undeclared parameter changes a non-error answer (`shape_breaks_weakening`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.EvaluationControl.ParameterReadings.Laws

open ParameterReadings

/-! ## Writing programs -/

def S (s : String) : Tm := .sym s
def N (n : Int) : Tm := .num n
def Str (s : String) : Tm := .str s
def V (x : String) : Tm := .var x
def E (items : List Tm) : Tm := .expr items
def call (f : String) (args : List Tm) : Tm := E (S f :: args)
/-- `(= (f $x1 .. $xn) body)` -/
def eqn (f : String) (params : List String) (body : Tm) : Tm :=
  E [S "=", E (S f :: params.map V), body]
def sup (alternatives : List Tm) : Tm := call "superpose" [E alternatives]
def plus (a b : Tm) : Tm := call "+" [a, b]
def letIn (x : String) (source body : Tm) : Tm := call "let" [V x, source, body]
def matchSelf (pattern template : Tm) : Tm := call "match" [S "&self", pattern, template]
def addSelf (row : Tm) : Tm := call "add-atom" [S "&self", row]
def evalCode (code : Tm) : Tm := call "eval" [code]

/-- Declared types given site by site: `params` lists `((f, i), T)`, every other parameter is
undeclared, and `+` takes two numbers and returns a number. -/
def decls (params : List (Site × Ty)) (results : List (String × Ty)) : Decls where
  param site :=
    if site.1 = "+" then .number
    else match params.find? (fun p => p.1 == site) with
      | some p => p.2
      | none => .undeclared
  result f := if f = "+" then some .number else (results.find? (fun p => p.1 == f)).map (·.2)

/-- Run a request under a reading of `D`, with the value verdicts of `D`. -/
def runWith (R : Decls → Reading) (D : Decls) (space : List Tm) (t : Tm) : List Obs :=
  answers (R D) (valueCheck D) 40 space t

def value (t : Tm) : Obs := .value t

/-! ## Law 1: renaming -/

/-- Parameter types as spelled before the switch. -/
inductive OldTy where
  | atom
  | data (inner : OldTy)
  | number
  | symbol
  | expression
  | string
  | undeclared
  | tvar (name : String)
  deriving DecidableEq

/-- **The hold rule before the switch**, as the draft's `prime_position_holds` had it: `(Data T)`
held; `Atom` held only at an exempt position (a grounded operation, a declaration of the standard
library written in HE, or a call whose head is not a symbol). -/
def oldHolds (exempt : Bool) : OldTy → Bool
  | .data _ => true
  | .atom => exempt
  | _ => false

/-- **The value check before the switch** of a running parameter: `Atom` was the top type. -/
def oldValueHas (t : Tm) : OldTy → Bool
  | .number => valueHas t .number
  | .symbol => valueHas t .symbol
  | .expression => valueHas t .expression
  | .string => valueHas t .string
  | _ => true

/-- **The renaming.** An old `Atom` is spelled `Proc` where it ran and `Atom` where it held; the
other types keep their spelling. -/
def rename (exempt : Bool) : OldTy → Ty
  | .atom => if exempt then .atom else .proc
  | .data inner => .data (rename false inner)
  | .number => .number
  | .symbol => .symbol
  | .expression => .expression
  | .string => .string
  | .undeclared => .undeclared
  | .tvar n => .tvar n

/-- **Law 1, holding**: the renamed type holds exactly where the old one held. -/
theorem holds_rename (exempt : Bool) (T : OldTy) : holdsTy (rename exempt T) = oldHolds exempt T := by
  cases T <;> cases exempt <;> rfl

/-- **Law 1, checks**: at a running position the renamed type checks values as the old one did. -/
theorem check_rename (exempt : Bool) (T : OldTy) (running : oldHolds exempt T = false) (t : Tm) :
    valueHas t (rename exempt T) = oldValueHas t T := by
  cases T <;> cases exempt <;> simp_all [oldHolds, rename, oldValueHas, valueHas]

/-- **The exception, exactly**: spelling every old `Atom` as `Proc` changes holding exactly at the
exempt `Atom` positions. -/
theorem uniform_rename_fails_iff (exempt : Bool) (T : OldTy) :
    holdsTy (rename false T) ≠ oldHolds exempt T ↔ exempt = true ∧ T = .atom := by
  cases T <;> cases exempt <;> simp [rename, oldHolds, holdsTy]

/-! ## Law 2: weakening within a line -/

/-- `l` ignores its argument, `u` uses it twice, `k` pairs it with itself; each parameter is
declared `t`, and `+` takes numbers. -/
def lineDecls (t : Ty) : Decls where
  param site :=
    if site.1 = "+" then .number
    else if site.2 = 0 ∧ (site.1 = "l" ∨ site.1 = "u" ∨ site.1 = "k") then t else .undeclared
  result f := if f = "+" then some .number else none

def lineSpace : List Tm :=
  [eqn "l" ["x"] (S "unused"), eqn "u" ["x"] (plus (V "x") (V "x")),
    eqn "k" ["x"] (E [S "pair", V "x", V "x"])]

def lineRun (R : Decls → Reading) (t : Ty) (request : Tm) : List Obs :=
  runWith R (lineDecls t) lineSpace request

/-- The running line, `Number`, `Proc`, undeclared. -/
def runningLine : List Ty := [.number, .proc, .undeclared]

theorem lineDecls_weaker {t t' : Ty} (h : TyWeaker t t') :
    WeakerOnLine (lineDecls t) (lineDecls t') := by
  refine weakerOnLine_of_pointwise rfl fun site => ?_
  simp only [lineDecls]
  by_cases h1 : site.1 = "+"
  · rw [if_pos h1, if_pos h1]; exact .inl rfl
  · rw [if_neg h1, if_neg h1]
    by_cases h2 : site.2 = 0 ∧ (site.1 = "l" ∨ site.1 = "u" ∨ site.1 = "k")
    · rw [if_pos h2, if_pos h2]; exact .inr h
    · rw [if_neg h2, if_neg h2]; exact .inl rfl

/-- **Law 2 on the line's programs**: `Number` to `Proc` and `Proc` to undeclared are weakenings,
so every request's answers are related. -/
theorem line_weakening (request : Tm) :
    ObsRefines (lineRun oneMarker .number request) (lineRun oneMarker .proc request) ∧
    ObsRefines (lineRun oneMarker .proc request) (lineRun oneMarker .undeclared request) :=
  ⟨weakening_within_line (lineDecls_weaker (tyWeaker_proc rfl)) _ _ _,
    weakening_within_line (lineDecls_weaker (tyWeaker_undeclared rfl)) _ _ _⟩

/-- An unused argument with two answers: one answer on the whole line (by need). -/
theorem line_unused_choice :
    runningLine.map (fun t => lineRun oneMarker t (call "l" [sup [N 1, N 2]])) =
      [[value (S "unused")], [value (S "unused")], [value (S "unused")]] := by
  decide +kernel

/-- An unused argument with no answer: still one answer on the whole line. -/
theorem line_unused_empty :
    runningLine.map (fun t => lineRun oneMarker t (call "l" [sup []])) =
      [[value (S "unused")], [value (S "unused")], [value (S "unused")]] := by
  decide +kernel

/-- An argument used twice: one choice per call (shared). -/
theorem line_used_twice :
    runningLine.map (fun t => lineRun oneMarker t (call "u" [sup [N 1, N 2]])) =
      [[value (N 2), value (N 4)], [value (N 2), value (N 4)], [value (N 2), value (N 4)]] := by
  decide +kernel

/-- A value refused in one branch only: weakening replaces that refusal by an answer. -/
theorem line_branch_refused :
    runningLine.map (fun t => lineRun oneMarker t (call "k" [sup [N 1, Str "a"]])) =
      [[value (E [S "pair", N 1, N 1]), .badArg ("k", 0) (Str "a")],
       [value (E [S "pair", N 1, N 1]), value (E [S "pair", Str "a", Str "a"])],
       [value (E [S "pair", N 1, N 1]), value (E [S "pair", Str "a", Str "a"])]] := by
  decide +kernel

/-- A literal of the wrong type is refused at the call, unused as it is; weakening removes the
refusal. -/
theorem line_literal_refused :
    runningLine.map (fun t => lineRun oneMarker t (call "l" [Str "text"])) =
      [[.badArg ("l", 0) (Str "text")], [value (S "unused")], [value (S "unused")]] := by
  decide +kernel

/-- The holding line, `(Data Number)` then `Atom`: the same held code, and the code check removed. -/
def holdDecls (t : Ty) : Decls := decls [(("d", 0), t)] []

def holdRun (t : Ty) (request : Tm) : List Obs :=
  runWith oneMarker (holdDecls t) [eqn "d" ["x"] (V "x")] request

theorem hold_line :
    [Ty.data .number, .atom].map (fun t => holdRun t (call "d" [plus (N 1) (N 2)])) =
      [[value (plus (N 1) (N 2))], [value (plus (N 1) (N 2))]] ∧
    [Ty.data .number, .atom].map (fun t => holdRun t (call "d" [Str "text"])) =
      [[.badArg ("d", 0) (Str "text")], [value (Str "text")]] := by
  decide +kernel

/-- Two answer lists with no refused argument on the left that differ are not related by
weakening. -/
theorem not_obsRefines_of_ne {xs ys : List Obs} (clean : ∀ o ∈ xs, ∀ site v, o ≠ .badArg site v)
    (ne : xs ≠ ys) : ¬ ObsRefines xs ys := fun h =>
  ne (h.eq_of_no_badArg fun site v m => clean _ m site v rfl)

/-- **Moving between the lines is not weakening.** `Atom` accepts every argument, yet replacing
`Number` by `Atom` changes what the function receives: the held `(superpose (1 2))` instead of one
of its values. The answers change with no type error removed, so the gradual guarantee cannot
decide whether a parameter holds. -/
theorem between_lines_not_weakening :
    lineRun oneMarker .number (call "k" [sup [N 1, N 2]]) =
      [value (E [S "pair", N 1, N 1]), value (E [S "pair", N 2, N 2])] ∧
    lineRun oneMarker .atom (call "k" [sup [N 1, N 2]]) =
      [value (E [S "pair", sup [N 1, N 2], sup [N 1, N 2]])] ∧
    ¬ ObsRefines (lineRun oneMarker .number (call "k" [sup [N 1, N 2]]))
      (lineRun oneMarker .atom (call "k" [sup [N 1, N 2]])) := by
  have h1 : lineRun oneMarker .number (call "k" [sup [N 1, N 2]]) =
      [value (E [S "pair", N 1, N 1]), value (E [S "pair", N 2, N 2])] := by decide +kernel
  have h2 : lineRun oneMarker .atom (call "k" [sup [N 1, N 2]]) =
      [value (E [S "pair", sup [N 1, N 2], sup [N 1, N 2]])] := by decide +kernel
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2]
  exact not_obsRefines_of_ne (by simp [value]) (by simp)

/-- **Naming an argument with `let` is visible** when arguments run by need and `let` runs its
source at once: the unused argument `(superpose (1 2))` gives one answer, named it gives two;
`(superpose ())` gives one answer, named it gives none (the draft agrees, probe `x_let_naming`).
Whether a `let` with a variable pattern should bind by need is open. -/
theorem let_naming_visible :
    lineRun oneMarker .number (call "l" [sup [N 1, N 2]]) = [value (S "unused")] ∧
    lineRun oneMarker .number (letIn "v" (sup [N 1, N 2]) (call "l" [V "v"])) =
      [value (S "unused"), value (S "unused")] ∧
    lineRun oneMarker .number (call "l" [sup []]) = [value (S "unused")] ∧
    lineRun oneMarker .number (letIn "v" (sup []) (call "l" [V "v"])) = [] := by
  decide +kernel

/-! ### Readings that break the law -/

/-- The types whose check constrains values. -/
def checksValues : Ty → Bool
  | .number | .symbol | .expression | .string => true
  | _ => false

/-- **Eager checking**: a checked argument runs when the call is made (its value is shared with the
body); an unchecked one runs by need. -/
def eagerChecked (D : Decls) : Reading where
  holds site _ := holdsTy (D.param site)
  eagerAt site := checksValues (D.param site)

/-- **Unshared checking**: the check of a checked argument runs its own copy at the call; the body
runs the argument again when it needs it. -/
def copyChecked (D : Decls) : Reading where
  holds site _ := holdsTy (D.param site)
  copyAt site := checksValues (D.param site)

/-- **By name**: every use of a running argument runs it again. -/
def byName (D : Decls) : Reading where
  holds site _ := holdsTy (D.param site)
  shares := false

/-- **Eager everywhere**, as HE and PeTTa run arguments. -/
def eagerAll (D : Decls) : Reading where
  holds site _ := holdsTy (D.param site)
  eagerAt site := !holdsTy (D.param site)

theorem eagerChecked_answers :
    lineRun eagerChecked .number (call "l" [sup [N 1, N 2]]) =
      [value (S "unused"), value (S "unused")] ∧
    lineRun eagerChecked .proc (call "l" [sup [N 1, N 2]]) = [value (S "unused")] ∧
    lineRun eagerChecked .number (call "l" [sup []]) = [] ∧
    lineRun eagerChecked .proc (call "l" [sup []]) = [value (S "unused")] := by
  decide +kernel

/-- **Eager checking breaks Law 2**: weakening `Number` to `Proc` changes the number of answers of
an unused argument, and brings back an answer that no type error removed. -/
theorem eagerChecked_breaks_weakening :
    ¬ ObsRefines (lineRun eagerChecked .number (call "l" [sup [N 1, N 2]]))
        (lineRun eagerChecked .proc (call "l" [sup [N 1, N 2]])) ∧
    ¬ ObsRefines (lineRun eagerChecked .number (call "l" [sup []]))
        (lineRun eagerChecked .proc (call "l" [sup []])) := by
  obtain ⟨h1, h2, h3, h4⟩ := eagerChecked_answers
  rw [h1, h2, h3, h4]
  exact ⟨not_obsRefines_of_ne (by simp [value]) (by simp),
    not_obsRefines_of_ne (by simp) (by simp)⟩

theorem copyChecked_answers :
    lineRun copyChecked .number (call "u" [sup [N 1, N 2]]) =
      [value (N 2), value (N 4), value (N 2), value (N 4)] ∧
    lineRun copyChecked .proc (call "u" [sup [N 1, N 2]]) = [value (N 2), value (N 4)] := by
  decide +kernel

/-- **Unshared checking breaks Law 2**: the check's own run of the argument doubles the answers. -/
theorem copyChecked_breaks_weakening :
    ¬ ObsRefines (lineRun copyChecked .number (call "u" [sup [N 1, N 2]]))
        (lineRun copyChecked .proc (call "u" [sup [N 1, N 2]])) := by
  obtain ⟨h1, h2⟩ := copyChecked_answers
  rw [h1, h2]
  exact not_obsRefines_of_ne (by simp [value]) (by simp)

/-- **By name keeps Law 2**: its demand does not depend on the declared type. -/
theorem byName_keeps_weakening {t t' : Ty} (h : TyWeaker t t') (request : Tm) :
    ObsRefines (lineRun byName t request) (lineRun byName t' request) := by
  have same : byName (lineDecls t) = byName (lineDecls t') := by
    unfold byName
    congr 1
    funext site _
    exact (lineDecls_weaker h).sameLine site
  unfold lineRun runWith
  rw [same]
  exact answers_refines _ (lineDecls_weaker h).accepts _ _ _

/-- **By name loses the shared choice**: `(+ $x $x)` sees two choices of its argument. -/
theorem byName_loses_shared_choice :
    lineRun byName .undeclared (call "u" [sup [N 1, N 2]]) =
      [value (N 2), value (N 3), value (N 3), value (N 4)] ∧
    lineRun oneMarker .undeclared (call "u" [sup [N 1, N 2]]) = [value (N 2), value (N 4)] := by
  decide +kernel

/-- **Eager everywhere keeps Law 2**: which arguments run at the call depends only on the line. -/
theorem eagerAll_keeps_weakening {t t' : Ty} (h : TyWeaker t t') (request : Tm) :
    ObsRefines (lineRun eagerAll t request) (lineRun eagerAll t' request) := by
  have line := (lineDecls_weaker h).sameLine
  have same : eagerAll (lineDecls t) = eagerAll (lineDecls t') := by
    unfold eagerAll
    congr 1
    · funext site _
      exact line site
    · funext site
      rw [line site]
  unfold lineRun runWith
  rw [same]
  exact answers_refines _ (lineDecls_weaker h).accepts _ _ _

/-- **Eager everywhere is not by need**: an unused argument with no answer leaves no answer. -/
theorem eagerAll_not_by_need :
    lineRun eagerAll .undeclared (call "l" [sup []]) = [] ∧
    lineRun eagerAll .undeclared (call "l" [sup [N 1, N 2]]) =
      [value (S "unused"), value (S "unused")] := by
  decide +kernel

/-! ## Law 3: when a value runs again -/

/-- The one-marker rule with a choice of when values run again. -/
def withRerun (r : Rerun) (D : Decls) : Reading where
  holds site _ := holdsTy (D.param site)
  rerun := r

/-- `n` takes a number, `fwd` holds its argument and passes it to `n`, `inc` adds one, `run1`
takes anything; the space holds a stored rule `(+ 1 2)` and a client's message. -/
def rerunDecls : Decls :=
  decls [(("n", 0), .number), (("fwd", 0), .atom), (("inc", 0), .number), (("run1", 0), .proc)]
    [("inc", .number)]

def rerunSpace : List Tm :=
  [E [S "rule", plus (N 1) (N 2)], E [S "msg", addSelf (S "pwned")],
    eqn "n" ["x"] (V "x"), eqn "fwd" ["y"] (call "n" [V "y"]),
    eqn "inc" ["z"] (plus (V "z") (N 1)), eqn "run1" ["w"] (V "w")]

def rerunRun (r : Rerun) (request : Tm) : List Obs :=
  runWith (withRerun r) rerunDecls rerunSpace request

def candidates : List Rerun := [.stay, .forward, .substitute]

/-- Reading a stored row: only `substitute` runs it. -/
theorem rerun_read :
    candidates.map (fun r => rerunRun r (matchSelf (E [S "rule", V "x"]) (V "x"))) =
      [[value (plus (N 1) (N 2))], [value (plus (N 1) (N 2))], [value (N 3)]] := by
  decide +kernel

/-- A row read through a `let` source and passed to a `Number` parameter: under `stay` and
`forward` the value is the expression, which `Number` refuses. -/
theorem rerun_let_source :
    candidates.map (fun r => rerunRun r
      (letIn "v" (matchSelf (E [S "rule", V "x"]) (V "x")) (call "n" [V "v"]))) =
      [[.badArg ("n", 0) (plus (N 1) (N 2))], [.badArg ("n", 0) (plus (N 1) (N 2))],
       [value (N 3)]] := by
  decide +kernel

/-- A transform-like read: match a row, compute a `let` source from it. -/
theorem rerun_transform :
    candidates.map (fun r => rerunRun r
      (matchSelf (E [S "rule", V "x"]) (letIn "m" (call "inc" [V "x"]) (E [S "got", V "m"])))) =
      [[.badArg ("inc", 0) (plus (N 1) (N 2))], [.badArg ("inc", 0) (plus (N 1) (N 2))],
       [value (E [S "got", N 4])]] := by
  decide +kernel

/-- Held syntax passed on to a `Number` parameter: `stay` refuses the expression it holds,
`forward` and `substitute` run it. -/
theorem rerun_forward :
    candidates.map (fun r => rerunRun r (call "fwd" [plus (N 1) (N 2)])) =
      [[.badArg ("n", 0) (plus (N 1) (N 2))], [value (N 3)], [value (N 3)]] ∧
    candidates.map (fun r => rerunRun r (call "fwd" [N 5])) =
      [[value (N 5)], [value (N 5)], [value (N 5)]] := by
  decide +kernel

/-- **A client's message read from a space**: under `substitute` passing it to a running
parameter runs the client's `add-atom`, and the space then holds the client's row. -/
theorem rerun_injection :
    candidates.map (fun r => rerunRun r
      (letIn "u" (matchSelf (E [S "msg", V "m"]) (call "run1" [V "m"]))
        (matchSelf (S "pwned") (S "yes")))) =
      [[], [], [value (S "yes")]] := by
  decide +kernel

/-- **A value bound before a redefinition**: under `substitute` it runs again where it lands, so the
equation added in between rewrites it (as HE does, probe `l3_live_rerun2`); under `stay` and
`forward` it keeps the value it had (as the draft and PeTTa do). -/
theorem rerun_live :
    candidates.map (fun r => rerunRun r
      (letIn "v" (E [S "a", S "b"])
        (letIn "u" (addSelf (eqn "a" ["y"] (S "z"))) (call "run1" [V "v"])))) =
      [[value (E [S "a", S "b"])], [value (E [S "a", S "b"])], [value (S "z")]] := by
  decide +kernel

/-- **Explicit `eval` runs data** under every candidate. -/
theorem rerun_explicit_eval :
    candidates.map (fun r => rerunRun r (matchSelf (E [S "rule", V "x"]) (evalCode (V "x")))) =
      [[value (N 3)], [value (N 3)], [value (N 3)]] ∧
    candidates.map (fun r => rerunRun r
      (letIn "v" (matchSelf (E [S "rule", V "x"]) (V "x")) (call "n" [evalCode (V "v")]))) =
      [[value (N 3)], [value (N 3)], [value (N 3)]] := by
  decide +kernel

/-- Under `stay`, a running parameter passed held syntax runs no code: its cell holds the syntax as
data. -/
theorem cellCode_stay (R : Reading) (h : R.rerun = .stay) (a : Tm) : R.cellCode a = a := by
  simp [Reading.cellCode, h]

/-- Under `forward` and `substitute`, held syntax passed to a running parameter is code again. -/
theorem cellCode_held (R : Reading) (h : R.rerun ≠ .stay) (t : Tm) : R.cellCode (.held t) = t := by
  unfold Reading.cellCode
  cases hr : R.rerun with
  | stay => exact absurd hr h
  | forward => rfl
  | substitute => rfl

/-- Under `substitute`, `let` binds and `match` reads in the plain role; otherwise in the value
role. -/
theorem bindRole_substitute (R : Reading) (h : R.rerun = .substitute) : R.bindRole = .plain := by
  simp [Reading.bindRole, h]

theorem bindRole_marks (R : Reading) (h : R.rerun ≠ .substitute) : R.bindRole = .val := by
  unfold Reading.bindRole
  cases hr : R.rerun with
  | stay => rfl
  | forward => rfl
  | substitute => exact absurd hr h

/-- A variable bound in the value role is bound to a value: the term carries the value role, or
the data role it already had. -/
theorem wrap_val_marks (t : Tm) : ∃ u, Role.wrap .val t = .val u ∨ Role.wrap .val t = .held u := by
  cases t with
  | held u => exact ⟨u, .inr rfl⟩
  | val u => exact ⟨u, .inl rfl⟩
  | _ => exact ⟨_, .inl rfl⟩

/-- **A value never runs again**: a term in the value role evaluates to itself, with the branch's
bindings applied, and so does held syntax. -/
theorem eval_val (R : Reading) (check : Verdicts) (n : Nat) (t : Tm) (st : Store) :
    eval R check (n + 1) (.val t) st = [.ok (.val (inst st.binds t)) st] := rfl

theorem eval_held (R : Reading) (check : Verdicts) (n : Nat) (t : Tm) (st : Store) :
    eval R check (n + 1) (.held t) st = [.ok (.held (inst st.binds t)) st] := rfl

/-- An unbound variable evaluates to itself. -/
theorem eval_var (R : Reading) (check : Verdicts) (n : Nat) (x : String) (st : Store)
    (h : lookupVar st.binds x = none) :
    eval R check (n + 1) (.var x) st = [.ok (.var x) st] := by
  show stepForm R check (eval R check n) n (classify (inst st.binds (.var x))) st = _
  simp only [inst, h, Option.getD_none]
  rfl

/-- **One level of `(match &self pattern template)`**: each row, renamed apart for this use, is
unified with the pattern, the row read in the reading's role (`bindRole`: a value under `stay` and
`forward`, plain code under `substitute`), and the template runs under the bindings each unifier
gives. -/
theorem eval_matchSelf (R : Reading) (check : Verdicts) (n : Nat) (pattern template : Tm)
    (st : Store) :
    eval R check (n + 1) (matchSelf pattern template) st =
      st.space.flatMap fun row =>
        M.bind (unifyM (forceWith R check (eval R check n)) n .plain (inst st.binds pattern)
            R.bindRole (ParameterReadings.rename st.fresh row))
          (fun _ => eval R check n (inst st.binds template)) { st with fresh := st.fresh + 1 } :=
  rfl

/-! ## Law 4: checks see values -/

/-- **The evaluator's checks see values**: forcing a pending cell runs its code, and each value
the code computes is judged by the declared type, then kept or refused. Nothing else is judged. -/
theorem checks_see_values (R : Reading) (check : Verdicts) (run : Tm → M Tm) (s : Store)
    (i : Nat) (code : Tm) (site : Site) (h : s.cells[i]? = some (.pending code site)) :
    forceWith R check run i s =
      (run code s).flatMap (Out.next fun v s' =>
        if check.onValue site (inst s'.binds v) then
          [.ok v (if R.shares then s'.setCell i (.done v) else s')]
        else [.badArg site (inst s'.binds v)]) := by
  simp only [forceWith, h]

/-- **Checks never bind**: every value that forcing a cell gives comes with the bindings that
running the argument left; the check adds none. -/
theorem checks_never_bind (R : Reading) (check : Verdicts) (run : Tm → M Tm) (s : Store)
    (i : Nat) (code : Tm) (site : Site) (h : s.cells[i]? = some (.pending code site))
    (v : Tm) (s'' : Store) (hv : Out.ok v s'' ∈ forceWith R check run i s) :
    ∃ s', Out.ok v s' ∈ run code s ∧ s''.binds = s'.binds := by
  rw [checks_see_values R check run s i code site h] at hv
  simp only [List.mem_flatMap] at hv
  obtain ⟨o, ho, hmem⟩ := hv
  cases o with
  | ok v' s' =>
      simp only [Out.next] at hmem
      split at hmem
      · simp only [List.mem_singleton, Out.ok.injEq] at hmem
        obtain ⟨rfl, rfl⟩ := hmem
        refine ⟨s', ho, ?_⟩
        split <;> rfl
      · simp at hmem
  | badArg _ _ => simp [Out.next] at hmem
  | fault _ => simp [Out.next] at hmem
  | exhausted => simp [Out.next] at hmem

/-- **The draft's verdict on a running parameter**, judged once on the written argument before it
runs: a symbol or expression parameter by the argument's own form, excused when a call's declared
result is that type; a number parameter by the type the declarations give the argument, an unknown
type passing. Held data passes a number parameter and is refused by a symbol parameter. -/
def draftVerdict (D : Decls) : Ty → Tm → Bool
  | .symbol, .sym _ => true
  | .symbol, .expr (.sym f :: _) => D.result f == some .symbol
  | .symbol, _ => false
  | .expression, .expr _ => true
  | .expression, _ => false
  | .number, a =>
      match inferCode D a with
      | none => true
      | some ty => ty == .number
  | _, _ => true

/-- The draft's verdicts: nothing is judged when a value is computed. -/
def draftCheck (D : Decls) : Verdicts :=
  ⟨fun _ _ => true, fun site a => draftVerdict D (D.param site) a⟩

/-- The probe table: `(h)` gives 5, `(g)` and `(gd)` give `baz` (`gd` is declared to return a
symbol), `(e)` gives `(a b)`, `(t)` gives `"text"`; `ns`, `nx`, `nn` take a symbol, an expression
and a number; `fwd`, `fwds` hold their argument and pass it to `nn`, `ns`. -/
def tableDecls : Decls :=
  decls [(("ns", 0), .symbol), (("nx", 0), .expression), (("nn", 0), .number),
      (("k", 0), .number), (("fwd", 0), .atom), (("fwds", 0), .atom)]
    [("gd", .symbol)]

def tableSpace : List Tm :=
  [eqn "h" [] (N 5), eqn "g" [] (S "baz"), eqn "gd" [] (S "baz"), eqn "e" [] (E [S "a", S "b"]),
    eqn "t" [] (Str "text"), eqn "ns" ["x"] (V "x"), eqn "nx" ["x"] (V "x"), eqn "nn" ["x"] (V "x"),
    eqn "k" ["x"] (E [S "pair", V "x", V "x"]), eqn "fwd" ["y"] (call "nn" [V "y"]),
    eqn "fwds" ["y"] (call "ns" [V "y"])]

/-- The probe table's requests. -/
def tableRequests : List Tm :=
  [call "ns" [call "g" []], call "ns" [call "gd" []], call "nx" [call "e" []],
    call "nx" [call "h" []], call "nx" [plus (N 1) (N 2)], call "nn" [call "t" []],
    call "k" [sup [N 1, Str "a"]], call "fwds" [S "baz"], call "fwd" [Str "text"],
    call "fwd" [call "gd" []]]

/-- **The draft's verdicts give the draft's answers** on the table (probes `l4_values`,
`l4_forward`, `l2_weaken`): `(g)` refused at a symbol parameter, 5 and 3 passed as expressions,
`"text"` passed as a number, `"a"` passed as a number, a held symbol refused at a symbol
parameter, held `"text"` and `(gd)` passed as numbers. -/
theorem draft_table :
    tableRequests.map (answers (oneMarker tableDecls) (draftCheck tableDecls) 40 tableSpace) =
      [[.badArg ("ns", 0) (call "g" [])], [value (S "baz")], [value (E [S "a", S "b"])],
       [value (N 5)], [value (N 3)], [value (Str "text")],
       [value (E [S "pair", N 1, N 1]), value (E [S "pair", Str "a", Str "a"])],
       [.badArg ("ns", 0) (S "baz")], [value (Str "text")], [value (call "gd" [])]] := by
  decide +kernel

/-- **Checking values gives the answers Law 4 requires** on the same table. -/
theorem value_table :
    tableRequests.map (answers (oneMarker tableDecls) (valueCheck tableDecls) 40 tableSpace) =
      [[value (S "baz")], [value (S "baz")], [value (E [S "a", S "b"])],
       [.badArg ("nx", 0) (N 5)], [.badArg ("nx", 0) (N 3)], [.badArg ("nn", 0) (Str "text")],
       [value (E [S "pair", N 1, N 1]), .badArg ("k", 0) (Str "a")],
       [value (S "baz")], [.badArg ("nn", 0) (Str "text")], [.badArg ("nn", 0) (call "gd" [])]] := by
  decide +kernel

/-- The value of a closed piece of code in the table's program, when it has exactly one. -/
def tableValue (a : Tm) : Option Tm :=
  match answers (oneMarker tableDecls) (valueCheck tableDecls) 40 tableSpace a with
  | [.value v] => some v
  | _ => none

/-- **A verdict sees values** when its judgment of an argument is the declared type's judgment of
the argument's value. -/
def SeesValues (verdict : Ty → Tm → Bool) : Prop :=
  ∀ ty a v, tableValue a = some v → verdict ty a = valueHas v ty

/-- **The draft's verdict does not see values**: `(g)` and `(gd)` both compute `baz`, a symbol, and
the draft refuses `(g)`; `(h)` computes 5, not an expression, and the draft accepts it. -/
theorem draft_does_not_see_values : ¬ SeesValues (draftVerdict tableDecls) := by
  intro h
  have value_g : tableValue (call "g" []) = some (S "baz") := by decide +kernel
  have verdict_g : draftVerdict tableDecls .symbol (call "g" []) = false := by decide +kernel
  have := h .symbol _ _ value_g
  rw [verdict_g] at this
  exact absurd this (by decide +kernel)

/-- **Each bug of the probe table violates Law 4**: for each written argument and declared type,
the draft's verdict differs from the declared type's verdict on the argument's value. Calls `(g)`
(value `baz`) at `Symbol`; `(h)` (5) and `(+ 1 2)` (3) at `Expression`; `(t)` (`"text"`) at
`Number`; and held data passed on to a running parameter: `"text"` and `(gd)` at `Number`, `baz`
at `Symbol`. -/
theorem draft_violations :
    [(Ty.symbol, call "g" []), (.expression, call "h" []), (.expression, plus (N 1) (N 2)),
      (.number, call "t" []), (.number, .held (Str "text")), (.number, .held (call "gd" [])),
      (.symbol, .held (S "baz"))].all (fun (ty, a) =>
        match tableValue a with
        | some v => draftVerdict tableDecls ty a != valueHas v ty
        | none => false) = true := by
  decide +kernel

/-! ## Two-way unification -/

/-- A row with a pattern head, rows stored with variables, a function whose `let` binds its
parameter, and a function that ignores its argument. -/
def unifySpace : List Tm :=
  [E [S "=", call "z" [N 0], S "yes"], E [S "fact", V "y", N 2], E [S "pair", V "a", V "a"],
    eqn "g" ["x"] (letIn "x" (N 5) (V "x")), eqn "bindv" ["x"] (letIn "x" (N 7) (S "ok")),
    E [S "=", call "isz" [N 0], S "yes"], eqn "k1" ["x"] (S "one")]

def unifyRun (request : Tm) : List Obs := runWith oneMarker (decls [] []) unifySpace request

/-- **Calls bind the caller's variables** (probe `u_calls`, and `u_later_binding` for `bindv`):
the head `(z 0)` binds the caller's `$u`; the callee's `let` binds the caller's variable through
the parameter. -/
theorem unify_calls :
    unifyRun (letIn "r" (call "z" [V "u"]) (E [V "r", V "u"])) = [value (E [S "yes", N 0])] ∧
    unifyRun (call "g" [V "u"]) = [value (N 5)] ∧
    unifyRun (letIn "r" (call "bindv" [V "w"]) (E [V "r", V "w"])) =
      [value (E [S "ok", N 7])] := by
  decide +kernel

/-- **A row's variables are fresh at each use, and bindable** (probe `u_rows`). -/
theorem unify_rows :
    unifyRun (matchSelf (E [S "fact", N 1, V "v"]) (V "v")) = [value (N 2)] ∧
    unifyRun (matchSelf (E [S "pair", N 3, V "w"]) (V "w")) = [value (N 3)] := by
  decide +kernel

/-- **`let` unifies both ways** (probe `u_let_pattern`). -/
theorem unify_let :
    unifyRun (call "let" [E [S "pair", V "a", V "a"], E [S "pair", N 3, V "w"], V "w"]) =
      [value (N 3)] ∧
    unifyRun (call "let" [E [V "x", N 2], E [N 1, V "y"], E [V "x", V "y"]]) =
      [value (E [N 1, N 2])] := by
  decide +kernel

/-- **A pattern head needs the argument's value; a variable head does not** (probe
`u_head_force`). By need, `(k1 (superpose (1 2)))` has one answer; `(isz ..)` runs its argument
and keeps the branches whose value unifies with `0`. -/
theorem unify_head_demand :
    unifyRun (call "isz" [plus (N 0) (N 0)]) = [value (S "yes")] ∧
    unifyRun (call "k1" [sup [N 1, N 2]]) = [value (S "one")] ∧
    unifyRun (call "isz" [sup [N 0, N 1, N 0]]) = [value (S "yes"), value (S "yes")] := by
  decide +kernel

def renameSpace : List Tm :=
  [E [S "=", E [S "fresh"], V "y"], E [S "=", call "is1" [N 1], S "one"],
    E [S "=", call "is2" [N 2], S "two"]]

/-- **Unfolding a call must rename its row apart** (probe `u_inline_rename`). Each call of
`(= (fresh) $y)` renames `$y`, so two calls give two variables, bound to `1` and `2` by the heads
of `is1` and `is2`; the two bodies unfolded without renaming share `$y`, and the second head then
fails to unify. -/
theorem unfold_needs_renaming :
    runWith oneMarker (decls [] []) renameSpace
      (letIn "a" (call "fresh" []) (letIn "b" (call "fresh" [])
        (letIn "p" (call "is1" [V "a"]) (letIn "q" (call "is2" [V "b"]) (E [V "p", V "q"]))))) =
      [value (E [S "one", S "two"])] ∧
    runWith oneMarker (decls [] []) renameSpace
      (letIn "a" (V "y") (letIn "b" (V "y")
        (letIn "p" (call "is1" [V "a"]) (letIn "q" (call "is2" [V "b"]) (E [V "p", V "q"]))))) =
      [] := by
  decide +kernel

def checkVarDecls : Decls := decls [(("nn", 0), .number)] []

def checkVarSpace : List Tm := [eqn "nn" ["x"] (E [S "ok", V "x"])]

/-- **An unbound variable passes a check, which leaves it unbound** (probes `u_check_var`,
`u_check_stability`); a later binding then reaches the value the check accepted, so a `Number`
parameter can end up holding a string, through a `let` or through a callee's head
(`(= (bind-a "a") done)`). A check that never binds is not stable under later bindings. -/
theorem unify_check_var :
    runWith oneMarker checkVarDecls checkVarSpace (call "nn" [V "u"]) =
      [value (E [S "ok", V "u"])] ∧
    runWith oneMarker checkVarDecls checkVarSpace
      (letIn "r" (call "nn" [V "u"]) (letIn "u" (Str "a") (V "r"))) =
      [value (E [S "ok", Str "a"])] ∧
    runWith oneMarker checkVarDecls
      (checkVarSpace ++ [E [S "=", call "bind-a" [Str "a"], S "done"]])
      (letIn "r" (call "nn" [V "u"]) (letIn "d" (call "bind-a" [V "u"]) (E [V "d", V "r"]))) =
      [value (E [S "done", E [S "ok", Str "a"]])] := by
  decide +kernel

/-! ## Law 6: type variables -/

/-- `q` holds its argument; `apply1` applies a function to an argument, both typed by variables;
`idt` is the identity at `$t`; `nt` ignores an argument of type `$t`; `q2` passes its argument,
typed `$t`, to `q`, and `qa` passes its argument, held, to `q`. -/
def tvarDecls : Decls :=
  decls [(("q", 0), .atom), (("apply1", 0), .tvar "f"), (("apply1", 1), .tvar "t"),
    (("idt", 0), .tvar "t"), (("nt", 0), .tvar "t"), (("q2", 0), .tvar "t"), (("qa", 0), .atom)] []

def tvarSpace : List Tm :=
  [eqn "q" ["x"] (V "x"), eqn "apply1" ["f", "y"] (E [V "f", V "y"]), eqn "idt" ["x"] (V "x"),
    eqn "nt" ["x"] (S "unused"), eqn "q2" ["x"] (call "q" [V "x"]), eqn "qa" ["x"] (call "q" [V "x"])]

def tvarRun (request : Tm) : List Obs := runWith oneMarker tvarDecls tvarSpace request

/-- A parameter typed by a variable runs. -/
theorem tvar_runs (n : String) : holdsTy (.tvar n) = false := rfl

/-- **Law 2 for a type variable**: `Proc` and an undeclared parameter are weaker on its line. -/
theorem tvar_weaker (n : String) : TyWeaker (.tvar n) .proc ∧ TyWeaker (.tvar n) .undeclared :=
  ⟨tyWeaker_proc rfl, tyWeaker_undeclared rfl⟩

/-- **A polymorphic `apply` does not pass syntax through**: `(q (+ 1 2))` holds `(+ 1 2)`, while
`(apply1 q (+ 1 2))` runs it at the `$t` parameter and gives `3`; a wrapper typed `$t` runs, a
wrapper declared `Atom` passes the syntax on. A `$t` parameter runs by need. -/
theorem tvar_apply :
    tvarRun (call "q" [plus (N 1) (N 2)]) = [value (plus (N 1) (N 2))] ∧
    tvarRun (call "apply1" [S "q", plus (N 1) (N 2)]) = [value (N 3)] ∧
    tvarRun (call "idt" [plus (N 1) (N 2)]) = [value (N 3)] ∧
    tvarRun (call "q2" [plus (N 1) (N 2)]) = [value (N 3)] ∧
    tvarRun (call "qa" [plus (N 1) (N 2)]) = [value (plus (N 1) (N 2))] ∧
    tvarRun (call "nt" [sup []]) = [value (S "unused")] := by
  decide +kernel

/-! ## Law 7: HE's shape rule -/

/-- **The shape rule**: `Atom` and `(Data T)` hold; an `Expression` parameter holds an argument
written as an expression, a `Symbol` parameter one written as a symbol; the rest run. -/
def shapeHolds (ty : Ty) (a : Tm) : Bool :=
  match ty, a with
  | .atom, _ => true
  | .data _, _ => true
  | .expression, .expr _ => true
  | .symbol, .sym _ => true
  | _, _ => false

def shapeRule (D : Decls) : Reading where
  holds site a := shapeHolds (D.param site) a

/-- The shape rule with bare symbols rewritten by their rows, as the Prime draft rewrites them. -/
def shapeRuleRewriting (D : Decls) : Reading :=
  { shapeRule D with symbolsRewrite := true }

/-- The one-marker rule with bare symbols rewritten. -/
def oneMarkerRewriting (D : Decls) : Reading :=
  { oneMarker D with symbolsRewrite := true }

/-- **An `Expression` parameter under the shape rule holds every call**: a call is written as an
expression, so the parameter receives it as written and never its value. -/
theorem shape_expression_holds_calls (D : Decls) (site : Site) (h : D.param site = .expression)
    (f : String) (args : List Tm) : (shapeRule D).holds site (call f args) = true := by
  simp [shapeRule, shapeHolds, h, call, E]

def shapeDecls (t : Ty) : Decls := decls [(("p", 0), t)] []

def shapeSpace : List Tm :=
  [eqn "e" [] (E [S "a", S "b"]), eqn "h" [] (N 5), eqn "p" ["x"] (V "x"),
    E [S "=", S "foo", S "bar"]]

def shapeRun (R : Decls → Reading) (t : Ty) (request : Tm) : List Obs :=
  runWith R (shapeDecls t) shapeSpace request

theorem shape_answers :
    shapeRun shapeRule .expression (call "p" [call "e" []]) = [value (call "e" [])] ∧
    shapeRun shapeRule .undeclared (call "p" [call "e" []]) = [value (E [S "a", S "b"])] ∧
    shapeRun oneMarker .expression (call "p" [call "e" []]) = [value (E [S "a", S "b"])] ∧
    shapeRun shapeRule .expression (letIn "v" (call "e" []) (call "p" [V "v"])) =
      [value (E [S "a", S "b"])] ∧
    shapeRun shapeRule .expression (call "p" [call "h" []]) = [value (call "h" [])] ∧
    shapeRun oneMarker .expression (call "p" [call "h" []]) = [.badArg ("p", 0) (N 5)] := by
  decide +kernel

/-- **The shape rule breaks Law 2 on the running line**: weakening `Expression` to an undeclared
parameter turns the answer `(e)` into `(a b)`, with no type error removed. -/
theorem shape_breaks_weakening :
    ¬ ObsRefines (shapeRun shapeRule .expression (call "p" [call "e" []]))
        (shapeRun shapeRule .undeclared (call "p" [call "e" []])) := by
  obtain ⟨h1, h2, -⟩ := shape_answers
  rw [h1, h2]
  exact not_obsRefines_of_ne (by simp [value]) (by decide)

/-- **With bare symbols rewritten, the shape rule's `Symbol` parameter leaves its line**: it holds
`foo` while an undeclared parameter runs it to `bar`; without rewriting, as in HE, both give
`foo`. The one-marker rule runs `foo` at a `Symbol` parameter. -/
theorem shape_symbol :
    shapeRun shapeRuleRewriting .symbol (call "p" [S "foo"]) = [value (S "foo")] ∧
    shapeRun shapeRuleRewriting .undeclared (call "p" [S "foo"]) = [value (S "bar")] ∧
    shapeRun oneMarkerRewriting .symbol (call "p" [S "foo"]) = [value (S "bar")] ∧
    shapeRun shapeRule .symbol (call "p" [S "foo"]) = [value (S "foo")] ∧
    shapeRun shapeRule .undeclared (call "p" [S "foo"]) = [value (S "foo")] := by
  decide +kernel

end Mettapedia.Languages.MeTTa.EvaluationControl.ParameterReadings.Laws
