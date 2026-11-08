import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramCompiledInterpreter

/-!
# Controls for the interpreter and its join with the compiled account

* **A repeated variable is checked** (`repeated_matches`, `repeated_rejects`): with
  `(= (f $x $x) yes)`, the interpreter answers `(f a a)` with `yes` and gives `(f a b)` no answer.
  The second occurrence of `$x` is compiled to a check against the environment.
* **Two equations, two answers** (`two_answers_interpreted`): with `(= (f $x) (one $x))` and
  `(= (f $x) (two $x))`, the interpreter reaches both answers to `(f a)`, and no third.
* **Range restriction is necessary** (`unrestricted_mismatch`): the equation `(= g $y)` rewrites
  `g` to every expression, and the interpreter reaches no answer at all, since its building code
  reads a variable no match bound. Without the hypothesis, `interpreter_iff` fails.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramCompiled.Controls

open Mettapedia.Logic.LP
open ProgramRows ProgramTranslation ProgramEquationsOpen ProgramEquations ProgramCompiled

def ka : Sx := .sym 60
def kb : Sx := .sym 61
def kYes : Sx := .sym 62

/-- `(f x y)` as an S-expression. -/
def call2 (x y : Sx) : Sx := .cell (.sym 50) (.cell x y)

/-- `(= (f $x $x) yes)`. -/
def repeated : ProgramEquations.Equation := ⟨.cell (.sym 50) (.cell (.var 0) (.var 0)), .sym 62⟩

theorem repeated_restricted : ∀ e ∈ [repeated], RangeRestricted e := by
  intro e he x hx
  rw [List.mem_singleton] at he
  subst he
  simp [repeated, Pat.vars] at hx

theorem repeated_matches : Rt (evS (progCode [repeated]) (call2 ka ka)) (ansS kYes) :=
  (interpreter_iff repeated_restricted _ _).mpr
    ⟨repeated, List.mem_singleton_self _, fun _ => ka, rfl, rfl⟩

theorem repeated_rejects (a : Sx) : ¬ Rt (evS (progCode [repeated]) (call2 ka kb)) (ansS a) := by
  intro run
  obtain ⟨e, he, θ, matched, -⟩ := (interpreter_iff repeated_restricted _ _).mp run
  rw [List.mem_singleton] at he
  subst he
  simp only [repeated, Pat.inst, call2, Sx.cell.injEq, true_and] at matched
  obtain ⟨one, two⟩ := matched
  rw [one] at two
  simp [ka, kb] at two

/-- `(= (f $x) (one $x))` and `(= (f $x) (two $x))`. -/
def twoEquations : Program :=
  [⟨.cell (.sym 50) (.var 0), .cell (.sym 63) (.var 0)⟩, ⟨.cell (.sym 50) (.var 0), .cell (.sym 64) (.var 0)⟩]

theorem two_restricted : ∀ e ∈ twoEquations, RangeRestricted e := by
  intro e he x hx
  simp only [twoEquations, List.mem_cons, List.mem_nil_iff, or_false] at he
  rcases he with rfl | rfl <;> simpa [Pat.vars] using hx

/-- **Both answers, and no third.** -/
theorem two_answers_interpreted (a : Sx) :
    Rt (evS (progCode twoEquations) (.cell (.sym 50) ka)) (ansS a) ↔
      a = .cell (.sym 63) ka ∨ a = .cell (.sym 64) ka := by
  rw [interpreter_iff two_restricted]
  constructor
  · rintro ⟨e, he, θ, matched, rfl⟩
    simp only [twoEquations, List.mem_cons, List.mem_nil_iff, or_false] at he
    rcases he with rfl | rfl
    · simp only [Pat.inst, Sx.cell.injEq, true_and] at matched
      left
      simp [Pat.inst, matched]
    · simp only [Pat.inst, Sx.cell.injEq, true_and] at matched
      right
      simp [Pat.inst, matched]
  · rintro (rfl | rfl)
    · exact ⟨_, List.mem_cons_self, fun _ => ka, rfl, rfl⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, fun _ => ka, rfl, rfl⟩

/-! ## Range restriction is necessary -/

/-- `(= g $y)`: the right-hand side has a variable the left-hand side does not bind. -/
def unrestricted : ProgramEquations.Equation := ⟨.sym 50, .var 0⟩

theorem unrestricted_rewrites (a : Sx) : GRewrite [unrestricted] (.sym 50) a :=
  ⟨unrestricted, List.mem_singleton_self _, fun _ => a, rfl, rfl⟩

theorem meta_lhs_107 : ∀ e ∈ metaProg, phtag e.lhs = some 107 → e ∈ [rRdSucc, rRdZero] := by decide

theorem stuck_rd_nil {Bl S E : Sx} : Stuck (rdS (nat 0) knil Bl S E) := by
  rintro Y ⟨e, he, θ, h, -⟩
  have tag := congrArg htag h
  rw [htag_inst _ (meta_lhs_rigid e he)] at tag
  have group := meta_lhs_107 e he tag
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at group
  rcases group with rfl | rfl
  · have h' : rdS (tup 97 [θ 0]) (kons (θ 1) (θ 2)) (θ 3) (θ 4) (θ 5) = rdS (nat 0) knil Bl S E := h
    simp [rdS, nat, tup_inj] at h'
  · have h' : rdS (tup 96 []) (kons (θ 0) (θ 1)) (θ 2) (θ 3) (θ 4) = rdS (nat 0) knil Bl S E := h
    simp [rdS, kons, knil, tup_inj] at h'

/-- **Control: without range restriction the interpreter reaches no answer**, though every
expression is a ground rewrite of `g`. -/
theorem unrestricted_mismatch (a : Sx) :
    GRewrite [unrestricted] (.sym 50) a ∧ ¬ Rt (evS (progCode [unrestricted]) (.sym 50)) (ansS a) := by
  refine ⟨unrestricted_rewrites a, fun run => ?_⟩
  obtain ⟨e, he, tryRun⟩ := ev_answers (.sym 50) a [unrestricted] run
  rw [List.mem_singleton] at he
  subst he
  -- the deterministic run: try, match the symbol, finish matching, read an unbound variable
  have codes : eqCode unrestricted = eqcS (codeOf [msymI 50]) (codeOf [bvarI 0]) := rfl
  have s1 : GRewrite metaProg (tryS (eqCode unrestricted) (.sym 50))
      (mtS (codeOf [msymI 50]) (kons (.sym 50) knil) knil (codeOf [bvarI 0])) :=
    fire (e := rTry) (by simp [metaProg]) (sub [codeOf [msymI 50], codeOf [bvarI 0], .sym 50])
  have s2 : GRewrite metaProg (mtS (codeOf [msymI 50]) (kons (.sym 50) knil) knil (codeOf [bvarI 0]))
      (mtS knil knil knil (codeOf [bvarI 0])) :=
    fire (e := rMsym) (by simp [metaProg]) (sub [.sym 50, knil, knil, knil, codeOf [bvarI 0]])
  have s3 : GRewrite metaProg (mtS knil knil knil (codeOf [bvarI 0])) (bjS (codeOf [bvarI 0]) knil knil) :=
    fire (e := rMdone) (by simp [metaProg]) (sub [knil, codeOf [bvarI 0]])
  have s4 : GRewrite metaProg (bjS (codeOf [bvarI 0]) knil knil) (rdS (nat 0) knil knil knil knil) :=
    fire (e := rBvar) (by simp [metaProg]) (sub [nat 0, knil, knil, knil])
  have toZ : Rt (tryS (eqCode unrestricted) (.sym 50)) (rdS (nat 0) knil knil knil knil) :=
    (((Relation.ReflTransGen.single s1).tail s2).tail s3).tail s4
  have back := det_terminal toZ (try_nonEv _ _) tryRun (stuck_ans a)
  rcases Relation.ReflTransGen.cases_head back with h | ⟨c, step, -⟩
  · simp [rdS, ansS, tup_inj] at h
  · exact stuck_rd_nil c step

#print axioms repeated_matches
#print axioms repeated_rejects
#print axioms two_answers_interpreted
#print axioms unrestricted_mismatch

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramCompiled.Controls
