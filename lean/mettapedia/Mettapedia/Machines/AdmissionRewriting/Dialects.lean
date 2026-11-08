import Mettapedia.Machines.AdmissionRewriting.Semantics

/-!
# Three dialects, a metered one, and the spellings that look equal but are not

Each dialect below is the function table and policies of `Dialect`, filled in as the
dialect behaves on the probes these controls reproduce (HE's Rust runner, SWI PeTTa,
and CeTTa's PeTTa, HE and Prime lanes, 2026-11-04).

* `petta`: PeTTa and CeTTa's PeTTa lane.  `petta_ready`: the full rule system is sound.
* `he`: HE.  A held value is evaluated again wherever a variable brings it into an
  evaluated position, and `id`'s answer is such a read; a `case` on an empty scrutinee
  runs the first branch whose pattern matches `Empty`; the two-armed `if` is an arity
  error; `min` is not defined; `size-atom` holds its argument (its elaboration is a
  `quote`).
* `prime`: the Prime draft on CeTTa.  `case` on an empty scrutinee runs nothing; the
  two-armed `if` exists, but a non-Boolean condition is an error quoting the `if`'s own
  spelling (CeTTa's HE lane does the same); `min` is not defined.
* `metered`: PeTTa under a fuel meter: every compound node is an observable step.

The negative controls, each a pair of spellings and their two different traces:
* `he_case1`: `(case (empty) (($x z)))` answers `z`; `(let $x (empty) z)` answers nothing;
* `he_id`: `(id (quoteit (+ 1 2)))` answers `3`; `(quoteit (+ 1 2))` answers `(+ 1 2)`;
* `he_letEta`: `(let $y (quoteit (+ 1 2)) $y)` answers `3`: a held value is evaluated
  again where a variable brings it (`he_case1_held`: the `case` spelling answers `3` too);
* `he_if2`: `(if True 1)` is an arity error; `(if True 1 (empty))` answers `1`;
* `he_size`: `(size-atom (id (1 2 3)))` answers `2` (the held expression has two
  elements); `(let $v (id (1 2 3)) (size-atom $v))` answers `3`;
* `prime_if2`: `(if 5 1)` and `(if 5 1 (empty))` are errors quoting different spellings;
* `prime_min`, `he_min`: `(min 3 5)` is data, `(if (< 3 5) 3 5)` answers `3`;
* `petta_min_choice`: `(min (superpose (1 2)) 3)` answers `1 2`; the retired spelling
  `(if (< a b) a b)` with a non-atomic operand answers `1 2 1 2`;
* `petta_min_effect`: an effectful operand runs once under `min`, twice in that spelling;
* `petta_quote`: rewriting inside a held position changes the answer
  (`(quoteit (if True 1))` answers its own spelling);
* `metered_id`: under a meter, `(id 5)` and `5` take different numbers of steps.
Positive controls: `petta_if2`, `petta_if_else` (a non-Boolean condition takes the else
branch), `petta_case1_empty`, `petta_id`, `petta_size`, `petta_min_protocol` (the protocol
form of `min` answers and prints as `min` does), and in HE on settled answers
`he_id_settled`, `he_case1_productive`.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.AdmissionRewriting.Dialects

open AdmissionRewriting

/-- `+` on integers. -/
abbrev plus : Name := .user 0
/-- A function declared `(-> Atom Atom)` with equation `(= (quoteit $x) $x)`. -/
abbrev quoteit : Name := .user 1
/-- A function with an effect: prints, then answers `1`. -/
abbrev noisy : Name := .user 2

/-- A symbol the controls use as a plain constant. -/
abbrev zSym : Sym := .other 1
/-- The head of an error value. -/
abbrev errSym : Sym := .other 99
/-- The head of an unevaluated `min` expression. -/
abbrev minSym : Sym := .other 98

/-- An error value quoting the offending form. -/
def errorVal (t : Tm) : Val := .tup [.sym errSym, .syn t]

/-- The number of elements of a held expression. -/
def synSize : Tm → ℤ
  | .call _ args => args.length + 1
  | .tup xs => xs.length
  | _ => 0

/-- A Boolean value. -/
def boolVal (b : Prop) [Decidable b] : Val := .sym (if b then .tru else .fls)

/-- HE's second evaluation of an answer: held integer additions are evaluated. -/
def settle : Val → Val
  | .syn (.call (.user 0) [.lit (.int a), .lit (.int b)]) => .int (a + b)
  | v => v

/-- The functions every control dialect shares. -/
def baseFn : Name → List Val → Trace
  | .size, [.tup vs] => ret (.int vs.length)
  | .size, [.syn t] => ret (.int (synSize t))
  | .user 0, [.int x, .int y] => ret (.int (x + y))
  | .user 1, [v] => ret v
  | .user 2, [] => [.eff 0, .ans (.int 1)]
  | _, _ => []

/-- PeTTa's library: `id`, integer `min`, `<` and `<=`. -/
def pettaFn : Name → List Val → Trace
  | .id, [v] => ret v
  | .min, [.int x, .int y] => ret (.int (min x y))
  | .lt, [.int x, .int y] => ret (boolVal (x < y))
  | .le, [.int x, .int y] => ret (boolVal (x ≤ y))
  | f, vs => baseFn f vs

/-- PeTTa, as CeTTa's PeTTa lane runs it. -/
def petta : Dialect where
  fn := pettaFn
  caseEmpty := .literal
  if2 := true
  elseOnNonBool := true
  nonBool := fun _ _ => []
  arity := fun _ => []
  meter := []
  varRead := ret

/-- HE's library: `id` evaluates its answer again; `min` is undefined. -/
def heFn : Name → List Val → Trace
  | .id, [v] => ret (settle v)
  | .min, [.int x, .int y] => ret (.tup [.sym minSym, .int x, .int y])
  | .lt, [.int x, .int y] => ret (boolVal (x < y))
  | f, vs => baseFn f vs

/-- HE. -/
def he : Dialect where
  fn := heFn
  caseEmpty := .matching
  if2 := false
  elseOnNonBool := false
  nonBool := fun t _ => ret (errorVal t)
  arity := fun t => ret (errorVal t)
  meter := []
  varRead := fun v => ret (settle v)

/-- The Prime draft's library: `id` and a held answer are settled; `min` is undefined. -/
def primeFn : Name → List Val → Trace
  | .id, [v] => ret (settle v)
  | .user 1, [v] => ret (settle v)
  | .min, [.int x, .int y] => ret (.tup [.sym minSym, .int x, .int y])
  | .lt, [.int x, .int y] => ret (boolVal (x < y))
  | f, vs => baseFn f vs

/-- The Prime draft. -/
def prime : Dialect where
  fn := primeFn
  caseEmpty := .none
  if2 := true
  elseOnNonBool := false
  nonBool := fun t _ => ret (errorVal t)
  arity := fun t => ret (errorVal t)
  meter := []
  varRead := ret

/-- PeTTa under a fuel meter. -/
def metered : Dialect := { petta with meter := [.eff 7] }

/-! ## PeTTa is ready -/

/-- PeTTa's `min` is its protocol: the first argument unless it is not `<=` the second, on
integers; on anything else both answer nothing. -/
theorem petta_minProtocol : MinProtocol petta := by
  intro x y
  cases x <;> cases y
  case int.int a b =>
    by_cases h : a ≤ b <;> simp [petta, pettaFn, boolVal, branch3, min_def, h]
  all_goals simp [petta, pettaFn, baseFn]

theorem petta_ready : Ready petta where
  meter := rfl
  varRead := fun _ => rfl
  if2 := rfl
  nonBool := fun _ _ _ => rfl
  caseEmpty := by decide
  id := fun _ => rfl
  min := petta_minProtocol

/-! ## Terms of the controls -/

/-- `(+ 1 2)`. -/
def onePlusTwo : Tm := .call plus [.lit (.int 1), .lit (.int 2)]
/-- `(quoteit (+ 1 2))`, its argument held. -/
def quoted : Tm := .call quoteit [.quote onePlusTwo]
/-- `(1 2 3)`. -/
def oneTwoThree : Tm := .tup [.lit (.int 1), .lit (.int 2), .lit (.int 3)]
/-- `(superpose (1 2))`. -/
def oneOrTwo : Tm := .sup [.lit (.int 1), .lit (.int 2)]
/-- `True`. -/
def tt : Tm := .lit (.sym .tru)

/-! ## HE -/

theorem he_case1 :
    eval he (.case_ .empty [(.bind, .lit (.sym zSym))]) [] = ret (.sym zSym) ∧
      eval he (.let_ .empty (.lit (.sym zSym))) [] = [] := ⟨rfl, rfl⟩

theorem he_id :
    eval he (.call .id [quoted]) [] = ret (.int 3) ∧
      eval he quoted [] = ret (.syn onePlusTwo) := ⟨rfl, rfl⟩

theorem he_letEta :
    eval he (.let_ quoted (.var 0)) [] = ret (.int 3) ∧
      eval he quoted [] = ret (.syn onePlusTwo) := ⟨rfl, rfl⟩

theorem he_case1_held :
    eval he (.case_ quoted [(.bind, .var 0)]) [] = ret (.int 3) ∧
      eval he (.let_ quoted (.var 0)) [] = ret (.int 3) := ⟨rfl, rfl⟩

theorem he_if2 :
    eval he (.if2 tt (.lit (.int 1))) [] = ret (errorVal (.if2 tt (.lit (.int 1)))) ∧
      eval he (.if3 tt (.lit (.int 1)) .empty) [] = ret (.int 1) := ⟨rfl, rfl⟩

theorem he_size :
    eval he (.call .size [.quote (.call .id [oneTwoThree])]) [] = ret (.int 2) ∧
      eval he (.let_ (.call .id [oneTwoThree]) (.call .size [.var 0])) [] = ret (.int 3) :=
  ⟨rfl, rfl⟩

theorem he_min :
    eval he (.call .min [.lit (.int 3), .lit (.int 5)]) [] =
        ret (.tup [.sym minSym, .int 3, .int 5]) ∧
      eval he (.if3 (.call .lt [.lit (.int 3), .lit (.int 5)]) (.lit (.int 3)) (.lit (.int 5))) [] =
        ret (.int 3) := ⟨rfl, rfl⟩

/-- On settled answers HE's `id` is the identity, and on a scrutinee that answers its
single-branch `case` is a `let` (`id_sound_on`, `case1_sound_on`). -/
theorem he_id_settled : eval he (.call .id [.lit (.int 5)]) [] = eval he (.lit (.int 5)) [] :=
  id_sound_on he rfl _ _ (fun v hv => by simp [eval, Lit.val, ret] at hv; subst hv; rfl)

theorem he_case1_productive :
    eval he (.case_ (.lit (.int 1)) [(.bind, .lit (.sym zSym))]) [] =
      eval he (.let_ (.lit (.int 1)) (.lit (.sym zSym))) [] :=
  case1_sound_answering he rfl _ _ _ rfl

theorem he_not_ready : ¬ Ready he := fun h => by
  have := h.caseEmpty
  exact this rfl

/-! ## The Prime draft -/

theorem prime_if2 :
    eval prime (.if2 (.lit (.int 5)) (.lit (.int 1))) [] =
        ret (errorVal (.if2 (.lit (.int 5)) (.lit (.int 1)))) ∧
      eval prime (.if3 (.lit (.int 5)) (.lit (.int 1)) .empty) [] =
        ret (errorVal (.if3 (.lit (.int 5)) (.lit (.int 1)) .empty)) := ⟨rfl, rfl⟩

theorem prime_min :
    eval prime (.call .min [.lit (.int 3), .lit (.int 5)]) [] =
      ret (.tup [.sym minSym, .int 3, .int 5]) := rfl

theorem prime_case1_empty :
    eval prime (.case_ .empty [(.bind, .lit (.sym zSym))]) [] = [] := rfl

theorem prime_not_ready : ¬ Ready prime := fun h => by
  have := h.nonBool (.if2 (.lit (.int 5)) (.lit (.int 1))) (.if3 (.lit (.int 5)) (.lit (.int 1)) .empty)
    (.int 5)
  simp [prime, errorVal, ret] at this

/-! ## PeTTa -/

theorem petta_if2 :
    eval petta (.if2 (.lit (.sym .fls)) (.lit (.int 1))) [] = [] ∧
      eval petta (.if2 (.lit (.int 5)) (.lit (.int 1))) [] = [] ∧
      eval petta (.if3 (.lit (.int 5)) (.lit (.int 1)) .empty) [] = [] := ⟨rfl, rfl, rfl⟩

theorem petta_if_else :
    eval petta (.if3 (.lit (.int 5)) (.lit (.int 1)) (.lit (.int 2))) [] = ret (.int 2) := rfl

theorem petta_case1_empty :
    eval petta (.case_ .empty [(.bind, .lit (.sym zSym))]) [] = [] := rfl

theorem petta_id : eval petta (.call .id [quoted]) [] = ret (.syn onePlusTwo) := rfl

theorem petta_size :
    eval petta (.call .size [.call .id [oneTwoThree]]) [] = ret (.int 3) := rfl

theorem petta_min_choice :
    eval petta (.call .min [oneOrTwo, .lit (.int 3)]) [] = [.ans (.int 1), .ans (.int 2)] ∧
      eval petta (.if3 (.call .lt [oneOrTwo, .lit (.int 3)]) oneOrTwo (.lit (.int 3))) [] =
        [.ans (.int 1), .ans (.int 2), .ans (.int 1), .ans (.int 2)] := ⟨rfl, rfl⟩

theorem petta_min_effect :
    eval petta (.call .min [.call noisy [], .lit (.int 3)]) [] = [.eff 0, .ans (.int 1)] ∧
      eval petta (.if3 (.call .lt [.call noisy [], .lit (.int 3)]) (.call noisy [])
          (.lit (.int 3))) [] = [.eff 0, .eff 0, .ans (.int 1)] := ⟨rfl, rfl⟩

/-- The protocol form keeps `min`'s answers and effects where the retired integer spelling
duplicates them: `(min (superpose (1 2)) 3)` answers `1 2` either way, and a printing operand
prints once. -/
theorem petta_min_protocol :
    eval petta (minForm oneOrTwo (.lit (.int 3))) [] = [.ans (.int 1), .ans (.int 2)] ∧
      eval petta (minForm (.call noisy []) (.lit (.int 3))) [] = [.eff 0, .ans (.int 1)] ∧
      eval petta (.call .min [oneOrTwo, .lit (.int 3)]) [] =
        eval petta (minForm oneOrTwo (.lit (.int 3))) [] ∧
      eval petta (.call .min [.call noisy [], .lit (.int 3)]) [] =
        eval petta (minForm (.call noisy []) (.lit (.int 3))) [] := ⟨rfl, rfl, rfl, rfl⟩

theorem petta_quote :
    eval petta (.call quoteit [.quote (.if2 tt (.lit (.int 1)))]) [] =
        ret (.syn (.if2 tt (.lit (.int 1)))) ∧
      eval petta (.call quoteit [.quote (.if3 tt (.lit (.int 1)) .empty)]) [] =
        ret (.syn (.if3 tt (.lit (.int 1)) .empty)) := ⟨rfl, rfl⟩

/-! ## The meter -/

theorem metered_id :
    eval metered (.call .id [.lit (.int 5)]) [] = [.eff 7, .ans (.int 5)] ∧
      eval metered (.lit (.int 5)) [] = [.ans (.int 5)] := ⟨rfl, rfl⟩

theorem metered_not_ready : ¬ Ready metered := fun h => by
  have := h.meter
  simp [metered] at this

/-! ## The controls differ -/

theorem he_case1_differs :
    eval he (.case_ .empty [(.bind, .lit (.sym zSym))]) [] ≠
      eval he (.let_ .empty (.lit (.sym zSym))) [] := by
  rw [he_case1.1, he_case1.2]; simp [ret]

theorem he_id_differs : eval he (.call .id [quoted]) [] ≠ eval he quoted [] := by
  rw [he_id.1, he_id.2]; simp [ret]

theorem he_letEta_differs : eval he (.let_ quoted (.var 0)) [] ≠ eval he quoted [] := by
  rw [he_letEta.1, he_letEta.2]; simp [ret]

theorem he_size_differs :
    eval he (.call .size [.quote (.call .id [oneTwoThree])]) [] ≠
      eval he (.let_ (.call .id [oneTwoThree]) (.call .size [.var 0])) [] := by
  rw [he_size.1, he_size.2]; simp [ret]

theorem prime_if2_differs :
    eval prime (.if2 (.lit (.int 5)) (.lit (.int 1))) [] ≠
      eval prime (.if3 (.lit (.int 5)) (.lit (.int 1)) .empty) [] := by
  rw [prime_if2.1, prime_if2.2]; simp [ret, errorVal]

theorem petta_min_choice_differs :
    eval petta (.call .min [oneOrTwo, .lit (.int 3)]) [] ≠
      eval petta (.if3 (.call .lt [oneOrTwo, .lit (.int 3)]) oneOrTwo (.lit (.int 3))) [] := by
  rw [petta_min_choice.1, petta_min_choice.2]; simp

theorem petta_quote_differs :
    eval petta (.call quoteit [.quote (.if2 tt (.lit (.int 1)))]) [] ≠
      eval petta (.call quoteit [.quote (.if3 tt (.lit (.int 1)) .empty)]) [] := by
  rw [petta_quote.1, petta_quote.2]; simp [ret]

theorem metered_id_differs :
    eval metered (.call .id [.lit (.int 5)]) [] ≠ eval metered (.lit (.int 5)) [] := by
  rw [metered_id.1, metered_id.2]; simp

end Mettapedia.Machines.AdmissionRewriting.Dialects
