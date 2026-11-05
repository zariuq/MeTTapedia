import Mettapedia.GSLT.LanguageDef.Collections.Evaluation

/-!
# Controls for the evaluation semantics

One program, read under three result rules: `Dialect.he`, `Dialect.petta`
and `Dialect.primeCandidate`. It has `(= (f a) 5)`, the native `+`,
`(= (h $x) (wrapped $x))` with a data parameter, five probe functions with a
data parameter, the conversions `list:from` and `tuple:from`, and a library
wrapper `tuple:from*` around the native conversion, as a library writes it.

| probe | body | result type | argument | HE | PeTTa | candidate |
|---|---|---|---|---|---|---|
| `p1` | `$x` | `Atom` | `(+ 1 2)` | `(+ 1 2)` | `(+ 1 2)` | `(+ 1 2)` |
| `p2` | `(+ 1 2)` | `Atom` | `(f a)` | `(+ 1 2)` | `(+ 1 2)` | `3` |
| `p3` | `(h $x)` | `Atom` | `(f a)` | `(h (f a))` | `(h (f a))` | `(wrapped (f a))` |
| `p4` | `(h $x)` | `%Undefined%` | `(f a)` | `(wrapped 5)` | `(wrapped (f a))` | `(wrapped (f a))` |
| `p5` | `$x` | `%Undefined%` | `(f a)` | `5` | `(f a)` | `(f a)` |

The HE column is what HE's own interpreter model computes
(`HECorrespondence.Interpreter.he_probe_table`, at every budget of at least seventeen), and the PeTTa column the reference
dialect's answers; the theorems `probe_*` derive each of them in the model,
and `probe_p2_exact` and `probe_p5_exact` show that the rows where the rules
differ have one answer each.

Under the candidate rule, the list controls: a literal is data
(`literal_is_data`, `literal_after_let`); `tuple:from` returns data and a
literal survives both conversions (`tupleFrom_returns_data`,
`literal_round_trip`); `list:from` of an expression in code position and
`list:map` evaluate the elements (`listFrom_evaluates`,
`map_evaluates_elements`); a head/tail pattern binds the rest
(`head_tail_let`); binding an open rest appends, as a difference list does
(`difference_list_append`); `let` binds its pattern while `unify` checks
occurrences (`let_is_a_binder`, `unify_occurs_check`); matching a pattern
against every element answers once per matching element
(`match_every_element`). A library wrapper around `tuple:from` runs the data it
converted under HE's rule, which evaluates a native's output, and keeps it
under the candidate (`he_runs_converted_data`, `once_keeps_converted_data`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.Evaluation.Controls

open Mettapedia.Logic.Unification.ListSplice

/-- The symbols of the control program. -/
inductive Sym where
  | num (n : ℕ)
  | a | b | c | d | e
  | f | plus | h | wrapped
  | p1 | p2 | p3 | p4 | p5
  | listFrom | tupleFrom | tupleFromLibrary
  | yes | no
  deriving DecidableEq, Repr

abbrev T := Tm Sym ℕ

abbrev s (x : Sym) : T := .atom (.sym x)
abbrev n (k : ℕ) : T := s (.num k)
abbrev call (g : Sym) (args : List T) : T := .expr (s g :: args)

/-- The data parameter `$x` of the probes and of `h`. -/
def x : T := .var 0

/-- The body of each probe. -/
def probeBody : Sym → T
  | .p1 => x
  | .p2 => call .plus [n 1, n 2]
  | .p3 | .p4 => call .h [x]
  | _ => x

/-- The declared result type of each equation-defined function. -/
def resultType : Sym → ResultType
  | .p1 | .p2 | .p3 => .data
  | _ => .undefined

def isProbe : Sym → Bool
  | .p1 | .p2 | .p3 | .p4 | .p5 => true
  | _ => false

def passingOf : Sym → Option (List Passing)
  | .f => some [.evaluated]
  | .plus => some [.evaluated, .evaluated]
  | .h | .p1 | .p2 | .p3 | .p4 | .p5 => some [.data]
  | .listFrom | .tupleFrom | .tupleFromLibrary => some [.evaluated]
  | _ => none

def nativeOf : Sym → List T → T → Prop
  | .plus, received, value => ∃ i j, received = [n i, n j] ∧ value = n (i + j)
  | .listFrom, received, value => ∃ xs, received = [.expr xs] ∧ value = .list xs
  | .tupleFrom, received, value => ∃ xs, received = [.list xs] ∧ value = .expr xs
  | _, _, _ => False

def ruleOf : Sym → List T → Env Sym ℕ → T → Prop
  | .f, received, σ, rhs => received = [s .a] ∧ σ = Term.var ∧ rhs = n 5
  | .h, received, σ, rhs => ∃ v, received = [v] ∧ σ = Program.bindOne Term.var 0 v ∧
      rhs = .expr [s .wrapped, x]
  | .tupleFromLibrary, received, σ, rhs => ∃ v, received = [v] ∧
      σ = Program.bindOne Term.var 0 v ∧ rhs = call .tupleFrom [x]
  | g, received, σ, rhs => isProbe g = true ∧ ∃ v, received = [v] ∧
      σ = Program.bindOne Term.var 0 v ∧ rhs = probeBody g

/-- The control program under a dialect's result rule. -/
def program (D : Dialect) : Program Sym ℕ where
  lookup := D.lookup
  stored := []
  passing := passingOf
  native := nativeOf
  rule := ruleOf
  returning g := D.returning (resultType g)
  nativeReturning g := D.nativeReturning (resultType g)

variable {D : Dialect}

theorem eval_num (θ : Env Sym ℕ) (k : ℕ) : Eval (program D) θ (n k) (n k) := .symbol rfl

theorem eval_sym (θ : Env Sym ℕ) (g : Sym) (none_ : passingOf g = none) :
    Eval (program D) θ (s g) (s g) := .symbol none_

/-- A number is a value under every output rule. -/
theorem output_num (mode : Returning) (k : ℕ) (result : T) :
    Output (program D) mode (n k) result ↔ result = n k := by
  cases mode with
  | asWritten => exact output_asWritten_iff _ _
  | once => exact (output_once_iff _ _).trans ((eval_sym_iff _ _).trans ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩)

/-- `(+ i j)` evaluates to `i + j`. -/
theorem eval_plus (θ : Env Sym ℕ) (i j : ℕ) :
    Eval (program D) θ (call .plus [n i, n j]) (n (i + j)) :=
  .native rfl (.evaluated (eval_num θ i) (.evaluated (eval_num θ j) .nil)) ⟨i, j, rfl, rfl⟩
    ((output_num _ _ _).mpr rfl)

theorem eval_plus_iff (θ : Env Sym ℕ) (i j : ℕ) (result : T) :
    Eval (program D) θ (call .plus [n i, n j]) result ↔ result = n (i + j) := by
  constructor
  · intro h
    rcases (eval_call_iff .plus [n i, n j] result).mp h with
      ⟨notFunction, -⟩ | ⟨modes, received, passes, receives, ⟨value, computed, delivered⟩ | ⟨σ, rhs, rule, -⟩⟩
    · cases notFunction
    · cases passes
      cases receives with
      | evaluated first rest =>
        cases rest with
        | evaluated second nil =>
          cases nil
          obtain ⟨-, rfl⟩ := (eval_sym_iff _ _).mp first
          obtain ⟨-, rfl⟩ := (eval_sym_iff _ _).mp second
          obtain ⟨i', j', same, rfl⟩ := computed
          simp only [n, s, List.cons.injEq, Term.atom.injEq, Leaf.sym.injEq, Sym.num.injEq,
            and_true] at same
          rw [(output_num _ _ _).mp delivered, same.1, same.2]
    · exact absurd rule.1 (by decide)
  · rintro rfl; exact eval_plus θ i j

/-- `(f a)` evaluates to `5`, and to nothing else, under every result rule. -/
theorem eval_fa_iff (θ : Env Sym ℕ) (result : T) :
    Eval (program D) θ (call .f [s .a]) result ↔ result = n 5 := by
  have five : ∀ v : T, Eval (program D) Term.var (n 5) v ↔ v = n 5 := fun v =>
    (eval_sym_iff _ _).trans ⟨fun h => h.2, fun h => ⟨rfl, h⟩⟩
  constructor
  · intro h
    rcases (eval_call_iff .f [s .a] result).mp h with
      ⟨notFunction, -⟩ | ⟨modes, received, passes, receives, ⟨value, computed, -⟩ | ⟨σ, rhs, rule, returned⟩⟩
    · cases notFunction
    · exact computed.elim
    · cases passes
      obtain ⟨v, value, rfl⟩ := (receive_evaluated_iff _ _).mp receives
      obtain ⟨-, rfl, rfl⟩ := rule
      change Return (program D) (D.returning .undefined) _ _ _ at returned
      cases hD : D.returning .undefined <;> rw [hD] at returned
      · rw [return_asWritten_iff] at returned
        simpa [inst, n, s, normalize, subst] using returned
      · exact (five _).mp ((return_once_iff _ _ _).mp returned)
  · rintro rfl
    refine .call rfl (.evaluated (eval_sym θ .a rfl) .nil) ⟨rfl, rfl, rfl⟩ ?_
    change Return (program D) (D.returning .undefined) _ _ _
    cases D.returning .undefined with
    | asWritten => exact (return_asWritten_iff _ _ _).mpr (by simp [inst, n, s, normalize, subst])
    | once => exact .once (eval_num _ 5)

theorem eval_fa (θ : Env Sym ℕ) : Eval (program D) θ (call .f [s .a]) (n 5) :=
  (eval_fa_iff θ _).mpr rfl

/-! ## The probe table -/

section Probes

/-- The data argument `(f a)`, and `(+ 1 2)`. -/
def fa : T := call .f [s .a]
def onePlusTwo : T := call .plus [n 1, n 2]

theorem inst_fa (θ : Env Sym ℕ) : inst θ fa = fa := by
  simp [inst, fa, call, s, normalize, subst]

theorem inst_onePlusTwo (θ : Env Sym ℕ) : inst θ onePlusTwo = onePlusTwo := by
  simp [inst, onePlusTwo, call, n, s, normalize, subst]

theorem bindOne_x (v : T) : Program.bindOne (Term.var : Env Sym ℕ) 0 v 0 = v := by
  simp [Program.bindOne]

theorem passing_probe (g : Sym) (probe : isProbe g = true) : passingOf g = some [.data] := by
  cases g <;> simp_all [isProbe, passingOf]

/-- A probe's call: its argument arrives as data and only the probe's rule applies. -/
theorem eval_probe_iff (g : Sym) (probe : isProbe g = true) (arg : T)
    (ground : inst Term.var arg = arg) (result : T) :
    Eval (program D) Term.var (call g [arg]) result ↔
      Return (program D) (D.returning (resultType g)) (Program.bindOne Term.var 0 arg)
        (probeBody g) result := by
  have passing := passing_probe g probe
  constructor
  · intro h
    rcases (eval_call_iff g [arg] result).mp h with
      ⟨notFunction, -⟩ | ⟨modes, received, passes, receives, ⟨value, computed, -⟩ | ⟨σ, rhs, rule, returned⟩⟩
    · change passingOf g = none at notFunction
      rw [passing] at notFunction; cases notFunction
    · change passingOf g = some modes at passes
      rw [passing] at passes; cases passes
      change nativeOf g _ _ at computed
      cases g <;> simp_all [isProbe, nativeOf]
    · change passingOf g = some modes at passes
      rw [passing] at passes; cases passes
      obtain rfl := (receive_data_iff arg received).mp receives
      rw [ground] at rule
      change ruleOf g [arg] σ rhs at rule
      have shape : σ = Program.bindOne Term.var 0 arg ∧ rhs = probeBody g := by
        cases g <;> simp_all [isProbe, ruleOf]
      obtain ⟨rfl, rfl⟩ := shape
      exact returned
  · intro returned
    have received : Receive (program D) Term.var [.data] [arg] [arg] := by
      have := Receive.data (P := program D) (θ := Term.var) (x := arg) Receive.nil
      rwa [ground] at this
    have rule : ruleOf g [arg] (Program.bindOne Term.var 0 arg) (probeBody g) := by
      cases g <;> simp_all [isProbe, ruleOf]
    exact .call passing received rule returned

/-- `h` on the data `(f a)`: its body builds `(wrapped (f a))`, and under the
substituting rule of HE the data runs, giving `(wrapped 5)`. -/
theorem eval_h_body_data (D : Dialect) (data : D.lookup = .data) :
    Eval (program D) (Program.bindOne Term.var 0 fa) (.expr [s .wrapped, x])
      (.expr [s .wrapped, fa]) :=
  .construct rfl (.cons (eval_sym _ .wrapped rfl)
    (.cons ((eval_var_iff data _ _).mpr (bindOne_x fa).symm) .nil))

theorem eval_h_body_code :
    Eval (program .he) (Program.bindOne Term.var 0 fa) (.expr [s .wrapped, x])
      (.expr [s .wrapped, n 5]) := by
  refine .construct rfl (.cons (eval_sym _ .wrapped rfl) (.cons ?_ .nil))
  refine .variableCode rfl (by simp [Program.bindOne, fa, call, s]) ?_
  rw [bindOne_x]
  exact eval_fa _

/-- `h` called on `$x` holding `(f a)` receives it as data. -/
theorem eval_h_call (D : Dialect) (result : T)
    (returned : Return (program D) (D.returning .undefined) (Program.bindOne Term.var 0 fa)
      (.expr [s .wrapped, x]) result) :
    Eval (program D) (Program.bindOne Term.var 0 fa) (call .h [x]) result := by
  have received : Receive (program D) (Program.bindOne Term.var 0 fa) [.data] [x] [fa] := by
    have := Receive.data (P := program D) (θ := Program.bindOne Term.var 0 fa) (x := x) Receive.nil
    convert this using 2
    simp [inst, x, subst, bindOne_x, fa, call, s, normalize]
  exact .call rfl received ⟨fa, rfl, rfl, rfl⟩ returned

/-- Row `p1`, the identity on a data parameter: `(+ 1 2)` under all three rules. -/
theorem probe_p1_he : Eval (program .he) Term.var (call .p1 [onePlusTwo]) onePlusTwo :=
  (eval_probe_iff .p1 rfl _ (inst_onePlusTwo _) _).mpr ((return_asWritten_iff _ _ _).mpr (by
    simp [probeBody, inst, x, subst, bindOne_x, onePlusTwo, call, n, s, normalize]))

theorem probe_p1_petta : Eval (program .petta) Term.var (call .p1 [onePlusTwo]) onePlusTwo :=
  (eval_probe_iff .p1 rfl _ (inst_onePlusTwo _) _).mpr ((return_asWritten_iff _ _ _).mpr (by
    simp [probeBody, inst, x, subst, bindOne_x, onePlusTwo, call, n, s, normalize]))

theorem probe_p1_candidate :
    Eval (program .primeCandidate) Term.var (call .p1 [onePlusTwo]) onePlusTwo :=
  (eval_probe_iff .p1 rfl _ (inst_onePlusTwo _) _).mpr
    (.once ((eval_var_iff rfl _ _).mpr (bindOne_x _).symm))

/-- **Row `p2` has one answer under each rule**: the references return the body
`(+ 1 2)` as written, the candidate runs it and returns `3`. -/
theorem probe_p2_exact (result : T) :
    (Eval (program .he) Term.var (call .p2 [fa]) result ↔ result = onePlusTwo) ∧
      (Eval (program .petta) Term.var (call .p2 [fa]) result ↔ result = onePlusTwo) ∧
      (Eval (program .primeCandidate) Term.var (call .p2 [fa]) result ↔ result = n 3) := by
  have body : inst (Program.bindOne Term.var 0 fa) (probeBody .p2) = onePlusTwo := by
    simp [probeBody, inst, onePlusTwo, call, n, s, normalize, subst]
  refine ⟨?_, ?_, ?_⟩
  · rw [eval_probe_iff .p2 rfl fa (inst_fa _)]
    exact (return_asWritten_iff _ _ _).trans (by rw [body])
  · rw [eval_probe_iff .p2 rfl fa (inst_fa _)]
    exact (return_asWritten_iff _ _ _).trans (by rw [body])
  · rw [eval_probe_iff .p2 rfl fa (inst_fa _)]
    exact (return_once_iff _ _ _).trans (eval_plus_iff _ 1 2 result)

/-- Row `p3`: the references return `(h (f a))` as written; the candidate runs
`h`, whose data parameter keeps `(f a)` as data. -/
theorem probe_p3_he : Eval (program .he) Term.var (call .p3 [fa]) (call .h [fa]) :=
  (eval_probe_iff .p3 rfl _ (inst_fa _) _).mpr ((return_asWritten_iff _ _ _).mpr (by
    simp [probeBody, inst, fa, call, s, x, normalize, subst, bindOne_x]))

theorem probe_p3_petta : Eval (program .petta) Term.var (call .p3 [fa]) (call .h [fa]) :=
  (eval_probe_iff .p3 rfl _ (inst_fa _) _).mpr ((return_asWritten_iff _ _ _).mpr (by
    simp [probeBody, inst, fa, call, s, x, normalize, subst, bindOne_x]))

theorem probe_p3_candidate :
    Eval (program .primeCandidate) Term.var (call .p3 [fa]) (.expr [s .wrapped, fa]) :=
  (eval_probe_iff .p3 rfl _ (inst_fa _) _).mpr
    (.once (eval_h_call _ _ (.once (eval_h_body_data _ rfl))))

/-- Row `p4`: HE runs the data held by the parameter, giving `(wrapped 5)`;
PeTTa and the candidate keep it, giving `(wrapped (f a))`. -/
theorem probe_p4_he : Eval (program .he) Term.var (call .p4 [fa]) (.expr [s .wrapped, n 5]) :=
  (eval_probe_iff .p4 rfl _ (inst_fa _) _).mpr (.once (eval_h_call _ _ (.once eval_h_body_code)))

theorem probe_p4_petta :
    Eval (program .petta) Term.var (call .p4 [fa]) (.expr [s .wrapped, fa]) :=
  (eval_probe_iff .p4 rfl _ (inst_fa _) _).mpr
    (.once (eval_h_call _ _ (.once (eval_h_body_data _ rfl))))

theorem probe_p4_candidate :
    Eval (program .primeCandidate) Term.var (call .p4 [fa]) (.expr [s .wrapped, fa]) :=
  (eval_probe_iff .p4 rfl _ (inst_fa _) _).mpr
    (.once (eval_h_call _ _ (.once (eval_h_body_data _ rfl))))

/-- **Row `p5` has one answer under each rule**: HE runs the returned data and
gives `5`; PeTTa and the candidate return `(f a)`. -/
theorem probe_p5_exact (result : T) :
    (Eval (program .he) Term.var (call .p5 [fa]) result ↔ result = n 5) ∧
      (Eval (program .petta) Term.var (call .p5 [fa]) result ↔ result = fa) ∧
      (Eval (program .primeCandidate) Term.var (call .p5 [fa]) result ↔ result = fa) := by
  have bound : Program.bindOne (Term.var : Env Sym ℕ) 0 fa 0 ≠ .var 0 := by
    simp [Program.bindOne, fa, call, s]
  refine ⟨?_, ?_, ?_⟩
  · rw [eval_probe_iff .p5 rfl fa (inst_fa _)]
    change Return _ .once _ x _ ↔ _
    rw [return_once_iff]
    change Eval _ _ (.var 0) result ↔ _
    rw [eval_var_code_iff (P := program .he) rfl 0 bound, bindOne_x]
    exact eval_fa_iff (D := Dialect.he) Term.var result
  · rw [eval_probe_iff .p5 rfl fa (inst_fa _)]
    exact (return_once_iff _ _ _).trans ((eval_var_iff rfl _ _).trans (by rw [bindOne_x]))
  · rw [eval_probe_iff .p5 rfl fa (inst_fa _)]
    exact (return_once_iff _ _ _).trans ((eval_var_iff rfl _ _).trans (by rw [bindOne_x]))

end Probes

/-! ## Lists, conversions and templates under the candidate rule -/

section Lists

abbrev C := program .primeCandidate

theorem candidate_data : C.lookup = .data := rfl

theorem listFromNative : ListFrom C .listFrom :=
  ⟨rfl, fun _ _ => Iff.rfl, fun _ _ _ h => absurd h.1 (by decide), rfl⟩

theorem tupleFromNative : TupleFrom C .tupleFrom :=
  ⟨rfl, fun _ _ => Iff.rfl, fun _ _ _ h => absurd h.1 (by decide), rfl⟩

/-- `[(f a) (+ 1 2)]`, a list literal whose elements are calls. -/
def calls : T := .list [fa, onePlusTwo]

theorem inst_calls (θ : Env Sym ℕ) : inst θ calls = calls := by
  simp [inst, calls, fa, onePlusTwo, call, n, s, normalize, subst]

/-- **The literal is data**: it evaluates to itself, its calls unevaluated. -/
theorem literal_is_data (v : T) : Eval C Term.var calls v ↔ v = calls := by
  rw [calls, eval_list_iff, ← calls, inst_calls]

/-- `(let $x 3 [$x (+ 1 2)])` gives `[3 (+ 1 2)]`. -/
theorem literal_after_let :
    Eval C Term.var (.expr [head .let_, x, n 3, .list [x, onePlusTwo]]) (.list [n 3, onePlusTwo]) := by
  refine .letIn (σ := fun _ => n 3) (eval_num _ 3)
    (by rw [equivalent_iff_normalize_eq]; simp [subst, x, normalize, n, s]) ?_
  have : inst (Program.bindPattern Term.var (fun _ => n 3) x) (.list [x, onePlusTwo]) =
      .list [n 3, onePlusTwo] := by
    simp [inst, Program.bindPattern, x, Encoding.encode, Mettapedia.Logic.LP.Term.freeVars,
      onePlusTwo, call, n, s, normalize, subst]
  rw [← this]
  exact .list

/-- **`tuple:from` returns data**: `(tuple:from [(f a) (+ 1 2)])` gives
`((f a) (+ 1 2))`, not evaluated again. -/
theorem tupleFrom_returns_data (v : T) :
    Eval C Term.var (call .tupleFrom [calls]) v ↔ v = .expr [fa, onePlusTwo] := by
  rw [show call .tupleFrom [calls] = .expr [.atom (.sym .tupleFrom), calls] from rfl,
    eval_tupleFrom_iff tupleFromNative]
  constructor
  · rintro ⟨xs, literal, rfl⟩
    rw [literal_is_data] at literal
    cases literal
    rfl
  · rintro rfl; exact ⟨_, (literal_is_data _).mpr rfl, rfl⟩

/-- **A literal survives both conversions**: `(list:from (tuple:from [(f a) (+ 1 2)]))`
gives the literal back, unevaluated. -/
theorem literal_round_trip (v : T) :
    Eval C Term.var (call .listFrom [call .tupleFrom [calls]]) v ↔ v = calls := by
  rw [show call .listFrom [call .tupleFrom [calls]] =
    .expr [.atom (.sym .listFrom), .expr [.atom (.sym .tupleFrom), .list [fa, onePlusTwo]]] from rfl,
    eval_round_trip listFromNative tupleFromNative, ← calls, inst_calls]

/-- **`list:from` of an expression in code position evaluates its elements**:
`(list:from ((f a) (+ 1 2)))` gives `[5 3]`, one list per combination of values. -/
theorem listFrom_evaluates :
    Eval C Term.var (call .listFrom [.expr [fa, onePlusTwo]]) (.list [n 5, n 3]) := by
  rw [show call .listFrom [.expr [fa, onePlusTwo]] =
    .expr [.atom (.sym .listFrom), .expr [fa, onePlusTwo]] from rfl, eval_listFrom_iff listFromNative]
  exact ⟨[n 5, n 3], .construct trivial (.cons (eval_fa _) (.cons (eval_plus _ 1 2) .nil)), rfl⟩

/-- **`list:map` evaluates each element**: `(list:map [(f a) (+ 1 2)] $e $e)`
gives `[5 3]`. -/
theorem map_evaluates_elements :
    Eval C Term.var (.expr [head .map, calls, .var 4, .var 4]) (.list [n 5, n 3]) := by
  refine .map ((literal_is_data _).mpr rfl) (.cons ?_ (.cons ?_ .nil))
  · rw [show inst (Program.bindOne Term.var 4 fa) (.var 4) = fa by
      simp [inst, Program.bindOne, subst, fa, call, s, normalize]]
    exact eval_fa _
  · rw [show inst (Program.bindOne Term.var 4 onePlusTwo) (.var 4) = onePlusTwo by
      simp [inst, Program.bindOne, subst, onePlusTwo, call, n, s, normalize]]
    exact eval_plus _ 1 2

/-- `(let [$h | $t] [1 2 3] ($h $t))` gives `(1 [2 3])`. -/
theorem head_tail_let :
    Eval C Term.var
      (.expr [head .let_, .rest [.var 1] (.var 2), .list [n 1, n 2, n 3], .expr [.var 1, .var 2]])
      (.expr [n 1, .list [n 2, n 3]]) := by
  let σ : ℕ → T := fun v => if v = 1 then n 1 else if v = 2 then .list [n 2, n 3] else .var v
  refine .letIn (σ := σ) (bound := .list [n 1, n 2, n 3]) ?_ ?_ ?_
  · rw [eval_list_iff]; simp [inst, n, s, normalize, subst]
  · rw [equivalent_iff_normalize_eq]; simp [σ, subst, normalize, splice, n, s]
  · have mem1 : (1 : ℕ) ∈ (Encoding.encode (.rest [.var 1] (.var 2) : T)).freeVars := by
      simp [Encoding.encode, Mettapedia.Logic.Unification.ListPrefixMeeting.spine,
        Mettapedia.Logic.Unification.ListPrefixMeeting.cons, Mettapedia.Logic.LP.Term.freeVars,
        Fin.exists_fin_two]
    have mem2 : (2 : ℕ) ∈ (Encoding.encode (.rest [.var 1] (.var 2) : T)).freeVars := by
      simp [Encoding.encode, Mettapedia.Logic.Unification.ListPrefixMeeting.spine,
        Mettapedia.Logic.Unification.ListPrefixMeeting.cons, Mettapedia.Logic.LP.Term.freeVars,
        Fin.exists_fin_two]
    refine .construct trivial (.cons ((eval_var_iff rfl _ _).mpr ?_)
      (.cons ((eval_var_iff rfl _ _).mpr ?_) .nil))
    · simp [Program.bindPattern, mem1, σ, normalize, n, s]
    · simp [Program.bindPattern, mem2, σ, normalize, n, s]

/-- **`let` binds its pattern**: `(let $t [a | $t] $t)` gives `[a | $t]`, the
bound `$t` and the free `$t` of the value being different variables. -/
theorem let_is_a_binder (v : T) :
    Eval C Term.var (.expr [head .let_, .var 2, .rest [s .a] (.var 2), .var 2]) v ↔
      v = .rest [s .a] (.var 2) := by
  have value : inst Term.var (.rest [s .a] (.var 2) : T) = .rest [s .a] (.var 2) := by
    simp [inst, s, normalize, subst, splice]
  have mem : (2 : ℕ) ∈ (Encoding.encode (.var 2 : T)).freeVars := by
    simp [Encoding.encode, Mettapedia.Logic.LP.Term.freeVars]
  rw [eval_let_iff]
  constructor
  · rintro ⟨bound, σ, evaluated, matched, body⟩
    rw [eval_rest_iff, value] at evaluated
    subst evaluated
    rw [eval_var_iff rfl] at body
    have normal := matched.normalize_eq
    simp only [subst, normalize, splice, s, List.map_cons, List.map_nil] at normal
    rw [body]
    simp [Program.bindPattern, mem, normal]
  · rintro rfl
    refine ⟨_, fun _ => .rest [s .a] (.var 2), (eval_rest_iff _ _ _).mpr value.symm, ?_, ?_⟩
    · rw [equivalent_iff_normalize_eq]; simp [subst]
    · rw [eval_var_iff rfl]
      simp [Program.bindPattern, mem, normalize, s, splice]

/-- **Unification checks occurrences**: `(unify $t [a | $t] yes no)` gives `no`. -/
theorem unify_occurs_check (v : T) :
    Eval C Term.var (.expr [head .unify, .var 2, .rest [s .a] (.var 2), s .yes, s .no]) v ↔
      v = s .no := by
  have failed : Encoding.solve (inst Term.var (.var 2 : T)) (inst Term.var (.rest [s .a] (.var 2))) =
      none := by
    have left : inst Term.var (.var 2 : T) = .var 2 := by simp [inst, subst, normalize]
    have right : inst Term.var (.rest [s .a] (.var 2) : T) = .rest [s .a] (.var 2) := by
      simp [inst, s, normalize, subst, splice]
    rw [left, right, Encoding.solve_none_iff]
    rintro ⟨σ, h⟩
    apply Mettapedia.Logic.Unification.ListPrefixMeeting.occurs_rest_unsatisfiable
      (Leaf := Leaf Sym) (Var := ℕ) 2 (.const (.atom (.sym .a)))
    refine ⟨Encoding.encodeSubst σ, ?_⟩
    simpa only [Encoding.encode, s, List.map_cons, List.map_nil] using
      (Encoding.solution_iff _ _ _).mp h
  rw [eval_unify_iff, failed]
  constructor
  · rintro (⟨σ, impossible, -⟩ | ⟨-, branch⟩)
    · cases impossible
    · exact ((eval_sym_iff _ _).mp branch).2
  · rintro rfl
    exact Or.inr ⟨rfl, eval_sym _ .no rfl⟩

/-- **Appending through an open rest**: binding the rest of `[a b | $t]` to
`[c d]` gives `[a b c d]`, as a difference list does:
`(let $l [a b | $t] (unify $t [c d] $l none))`. -/
theorem difference_list_append :
    Eval C Term.var
      (.expr [head .let_, .var 3, .rest [s .a, s .b] (.var 2),
        .expr [head .unify, .var 2, .list [s .c, s .d], .var 3, s .no]])
      (.list [s .a, s .b, s .c, s .d]) := by
  have value : inst Term.var (.rest [s .a, s .b] (.var 2) : T) = .rest [s .a, s .b] (.var 2) := by
    simp [inst, s, normalize, subst, splice]
  have mem : (3 : ℕ) ∈ (Encoding.encode (.var 3 : T)).freeVars := by
    simp [Encoding.encode, Mettapedia.Logic.LP.Term.freeVars]
  have notMem : (2 : ℕ) ∉ (Encoding.encode (.var 3 : T)).freeVars := by
    simp [Encoding.encode, Mettapedia.Logic.LP.Term.freeVars]
  let θ := Program.bindPattern (Term.var : Env Sym ℕ) (fun _ => .rest [s .a, s .b] (.var 2)) (.var 3)
  have θ3 : θ 3 = .rest [s .a, s .b] (.var 2) := by
    simp [θ, Program.bindPattern, mem, normalize, s, splice]
  have θ2 : θ 2 = .var 2 := by simp [θ, Program.bindPattern, notMem]
  have left : inst θ (.var 2 : T) = .var 2 := by simp [inst, subst, θ2, normalize]
  have right : inst θ (.list [s .c, s .d] : T) = .list [s .c, s .d] := by
    simp [inst, subst, normalize, s]
  obtain ⟨σ, solved⟩ := Encoding.solve_complete (inst θ (.var 2)) (inst θ (.list [s .c, s .d]))
    ⟨fun v => if v = 2 then .list [s .c, s .d] else .var v, by
      rw [left, right, equivalent_iff_normalize_eq]; simp [subst, normalize, s]⟩
  have sound := Encoding.solve_sound _ _ σ solved
  rw [left, right] at sound
  have σ2 : normalize (σ 2) = .list [s .c, s .d] := by
    have := sound.normalize_eq
    simpa [subst, normalize, s] using this
  refine .letIn (σ := fun _ => .rest [s .a, s .b] (.var 2)) (bound := .rest [s .a, s .b] (.var 2))
    ((eval_rest_iff _ _ _).mpr value.symm)
    (by rw [equivalent_iff_normalize_eq]; simp [subst]) ?_
  refine .unifyYes solved ((eval_var_iff rfl _ _).mpr ?_)
  change _ = inst σ (θ 3)
  rw [θ3]
  simp only [inst, subst, normalize, s, List.map_cons, List.map_nil]
  rw [σ2]
  simp [splice]

/-- **Matching a pattern against every element** (`match'`, the list as a
small space): `(let ($x b) (superpose [(a b) (c d) (e b)]) $x)` answers `a`
and `e`, and nothing else. -/
theorem match_every_element (v : T) :
    Eval C Term.var
      (.expr [head .let_, .expr [.var 0, s .b],
        .expr [head .superpose, .list [.expr [s .a, s .b], .expr [s .c, s .d], .expr [s .e, s .b]]],
        .var 0]) v ↔ v = s .a ∨ v = s .e := by
  have mem : (0 : ℕ) ∈ (Encoding.encode (.expr [.var 0, s .b] : T)).freeVars := by
    simp only [Encoding.encode, Mettapedia.Logic.Unification.ListPrefixMeeting.expr,
      Mettapedia.Logic.LP.Term.freeVars, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨⟨0, by simp⟩, by simp [Encoding.encode, Mettapedia.Logic.LP.Term.freeVars]⟩
  have literal : inst Term.var
      (.list [.expr [s .a, s .b], .expr [s .c, s .d], .expr [s .e, s .b]] : T) =
        .list [.expr [s .a, s .b], .expr [s .c, s .d], .expr [s .e, s .b]] := by
    simp [inst, subst, normalize, s]
  rw [eval_let_iff]
  constructor
  · rintro ⟨bound, σ, chosen, matched, body⟩
    obtain ⟨xs, listed, member⟩ := (eval_superpose_iff _ _).mp chosen
    rw [eval_list_iff, literal] at listed
    cases listed
    rw [eval_var_iff rfl] at body
    have normal := matched.normalize_eq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rw [body]
    simp only [Program.bindPattern, mem, if_true]
    rcases member with rfl | rfl | rfl <;>
      simp only [subst, normalize, s, List.map_cons, List.map_nil, Term.expr.injEq,
        List.cons.injEq, Term.atom.injEq, Leaf.sym.injEq, and_true, reduceCtorEq, and_false] at normal
    · exact Or.inl normal
    · exact Or.inr normal
  · rintro (rfl | rfl)
    · refine ⟨.expr [s .a, s .b], fun _ => s .a, (eval_superpose_iff _ _).mpr
        ⟨_, (eval_list_iff _ _).mpr literal.symm, by simp⟩, ?_, ?_⟩
      · rw [equivalent_iff_normalize_eq]; simp [subst, normalize]
      · rw [eval_var_iff rfl]; simp [Program.bindPattern, mem, normalize]
    · refine ⟨.expr [s .e, s .b], fun _ => s .e, (eval_superpose_iff _ _).mpr
        ⟨_, (eval_list_iff _ _).mpr literal.symm, by simp⟩, ?_, ?_⟩
      · rw [equivalent_iff_normalize_eq]; simp [subst, normalize]
      · rw [eval_var_iff rfl]; simp [Program.bindPattern, mem, normalize]

/-- **HE runs the data a conversion returns**: HE evaluates a native's output
once at a result type other than `Atom`, so under HE's rule the library
wrapper `(tuple:from* [(f a) (+ 1 2)])` gives `(5 3)`, the converted
expression run. -/
theorem he_runs_converted_data :
    Eval (program .he) Term.var (call .tupleFromLibrary [calls]) (.expr [n 5, n 3]) := by
  have literal : Eval (program .he) Term.var calls calls :=
    (eval_list_iff _ _).mpr (inst_calls _).symm
  refine .call rfl (.evaluated literal .nil) ⟨calls, rfl, rfl, rfl⟩ ?_
  change Return _ .once _ _ _
  refine .once (.native rfl (.evaluated ?_ .nil) ⟨[fa, onePlusTwo], rfl, rfl⟩ ?_)
  · refine .variableCode rfl (by simp [Program.bindOne, calls]) ?_
    rw [show Program.bindOne (Term.var : Env Sym ℕ) 0 calls 0 = calls from bindOne_x calls]
    exact literal
  · exact .once (.construct trivial (.cons (eval_fa _) (.cons (eval_plus _ 1 2) .nil)))

/-- Under the candidate rule the same wrapper returns the converted data. -/
theorem once_keeps_converted_data :
    Eval C Term.var (call .tupleFromLibrary [calls]) (.expr [fa, onePlusTwo]) := by
  have literal : Eval C Term.var calls calls := (eval_list_iff _ _).mpr (inst_calls _).symm
  refine .call rfl (.evaluated literal .nil) ⟨calls, rfl, rfl, rfl⟩ ?_
  change Return _ .once _ _ _
  refine .once (.native rfl (.evaluated ?_ .nil) ⟨[fa, onePlusTwo], rfl, rfl⟩ .asWritten)
  change Eval _ _ (.var 0) _
  rw [eval_var_iff rfl, bindOne_x]
  rfl

end Lists

end Mettapedia.GSLT.LanguageDef.Collections.Evaluation.Controls
