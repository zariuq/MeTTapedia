import Mettapedia.Machines.AdmissionRewriting.Normalizer

/-!
# The meaning of the admission fragment, per dialect, and the soundness of each rule

**Observations.**  A run is a `Trace`: its answers and its effects, in the order they
occur.  Two runs with one trace have one answer bag, one effect sequence, and one
answer order; `bindT` runs a continuation on each answer and passes effects through.

**Dialects.**  HE, PeTTa and the Prime draft share the fragment's syntax and differ in
what `Dialect` records:
* `fn`: the function table on values, library heads included.  HE evaluates a call's
  answer again under the callee's declared range, so its `id` re-evaluates a held answer
  (`(id (quoteit (+ 1 2)))` answers `3` where `(quoteit (+ 1 2))` answers `(+ 1 2)`);
  PeTTa's `id` returns its argument;
* `caseEmpty`: what a `case` does when its scrutinee has no answer.  HE runs the first
  branch whose pattern matches the symbol `Empty`, a binding variable included; PeTTa and
  CeTTa run an explicit `Empty` branch only; the Prime draft runs none;
* `if2`, `elseOnNonBool`, `nonBool`, `arity`: whether the two-armed `if` exists (HE:
  arity error), and what an `if` does with a condition that is not `True`: PeTTa takes
  the else branch (none for the two-armed `if`); HE and CeTTa's HE and Prime lanes return
  an error that quotes the `if`'s own spelling when the condition is not a Boolean;
* `meter`: a trace every compound node emits first, for a dialect run under a fuel
  meter, where steps are observable;
* `varRead`: reading a variable in an evaluated position; HE evaluates a held value
  again wherever it lands (`(let $y (quoteit (+ 1 2)) $y)` answers `3`), PeTTa does not;
* argument holding is not a field: the elaborator writes a held argument as `quote`.
  A `quote` holds its term as written, without the values of its free variables; the
  controls hold closed terms.

`Ready` collects what the full rule system needs; for `min` it is `MinProtocol`: on two
evaluated arguments `min` answers as `(if (<= $x $y) $x $y)` does.  CeTTa's PeTTa lane has
it on integers, and on operands that are not numbers, raising its type error on the first
one, as `<=` does.  On doubles and the numeric constants it selects an operand by the exact
order (`MinMaxSelection`, DIFF-17).  The test agrees at a mixed tie (`(min 1 1.0)` is `1`)
and not at signed zeros, a NaN first operand, or an integer and a double equal only as
doubles: `(min 0.0 -0.0)` is `-0.0`, `(min nan 1)` is `nan`, `(min 9007199254740993
9007199254740992.0)` is the double (`MinMaxSelection.Controls.le_test_differs`).  No single
test spells the selection (`MinMaxSelection.Controls.no_single_test`), so on doubles the
rule is not the dialect's `min`; CeTTa's C has no such rewrite and runs `min` as an
intrinsic.
The rules' soundness lemmas take only the conditions each rule uses, so they also give the
sound subsystem of a dialect that is not ready.

**Shifting** (`eval_shift`): a term lifted by `shift c` reads the environment with a value
inserted at `c` as the term reads the original, on a dialect whose non-Boolean `if` does
not quote its own spelling; this is what lets `min`'s second argument move under the
binder of the first.

This file proves the root lemmas (`if2_sound`, `letStar_sound`, `case1_sound`,
`id_sound`, `sup1_sound`, `callable_sound`, `size_sound`, `min_sound` for every pair of
operands, `sizeVar_sound`, `letEta_sound`, `wrap_sound`), and `step_sound`: on a ready
dialect a step at any position keeps the trace, in every environment that respects the
facts.  The
consequences for the normalizer, `N_sound` and `conv_sound`, follow.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.AdmissionRewriting

/-- Values: integers, symbols, tuples, and held syntax. -/
inductive Val
  | int (n : ℤ)
  | sym (s : Sym)
  | tup (vs : List Val)
  | syn (t : Tm)

/-- The value of a literal. -/
def Lit.val : Lit → Val
  | .int n => .int n
  | .sym s => .sym s

/-- Whether a literal pattern matches a value. -/
def Lit.matches : Lit → Val → Bool
  | .int n, .int m => decide (n = m)
  | .sym s, .sym s' => decide (s = s')
  | _, _ => false

/-- An event of a run. -/
inductive Ev
  | ans (v : Val)
  | eff (n : ℕ)

/-- A run: answers and effects in order. -/
abbrev Trace := List Ev

/-- One answer. -/
def ret (v : Val) : Trace := [.ans v]

/-- Run a continuation on every answer; effects pass through. -/
def bindT (t : Trace) (f : Val → Trace) : Trace :=
  t.flatMap fun e => match e with
    | .ans v => f v
    | .eff n => [.eff n]

/-- Whether a run answers at all. -/
def hasAns : Trace → Bool
  | [] => false
  | .ans _ :: _ => true
  | .eff _ :: t => hasAns t

/-- Committed choice: the run up to its first answer. -/
def firstAns : Trace → Trace
  | [] => []
  | .ans v :: _ => [.ans v]
  | .eff n :: t => .eff n :: firstAns t

/-- A `case` with a scrutinee that has no answer. -/
inductive CaseEmpty
  /-- No branch runs. -/
  | none
  /-- An explicit `Empty` branch runs. -/
  | literal
  /-- The first branch whose pattern matches the symbol `Empty` runs. -/
  | matching
  deriving DecidableEq

/-- What a dialect decides about the fragment. -/
structure Dialect where
  /-- The function table, library heads included. -/
  fn : Name → List Val → Trace
  /-- A `case` whose scrutinee has no answer. -/
  caseEmpty : CaseEmpty
  /-- Whether the two-armed `if` exists. -/
  if2 : Bool
  /-- Whether an `if` whose condition is not `True` takes the else branch (PeTTa). -/
  elseOnNonBool : Bool
  /-- Otherwise, an `if` whose condition is not a Boolean, given the `if` itself. -/
  nonBool : Tm → Val → Trace
  /-- A form the dialect does not have at this arity, given the form. -/
  arity : Tm → Trace
  /-- What every compound node emits first (a fuel meter). -/
  meter : Trace
  /-- Reading a variable in an evaluated position (HE evaluates a held value again
  wherever it lands). -/
  varRead : Val → Trace

/-- Choose a branch on a condition's value. -/
def branch3 (v : Val) (t e nb : Trace) : Trace :=
  match v with
  | .sym .tru => t
  | .sym .fls => e
  | _ => nb

/-- Apply a function to an argument tuple. -/
def applyTup (g : List Val → Trace) : Val → Trace
  | .tup vs => g vs
  | _ => []

/-- Prepend a value to a tuple. -/
def consTup (v : Val) : Val → Trace
  | .tup vs => ret (.tup (v :: vs))
  | _ => []

/-- `map` over a list, the step run on `[element]`. -/
def mapT (step : List Val → Trace) : List Val → Trace
  | [] => ret (.tup [])
  | x :: xs => bindT (step [x]) fun y => bindT (mapT step xs) (consTup y)

/-- `filter` over a list, the step run on `[element]`. -/
def filterT (step : List Val → Trace) : List Val → Trace
  | [] => ret (.tup [])
  | x :: xs => bindT (step [x]) fun c => bindT (filterT step xs) fun w =>
      match c with
      | .sym .tru => consTup x w
      | _ => ret w

/-- `foldl` over a list, the step run on `[accumulator, element]`. -/
def foldlT (step : List Val → Trace) : Val → List Val → Trace
  | acc, [] => ret acc
  | acc, x :: xs => bindT (step [acc, x]) fun a => foldlT step a xs

/-- An iterator on its evaluated operands. -/
def iterate (k : Iter) (step : List Val → Trace) : Val → Trace
  | .tup [.tup xs] =>
    match k with
    | .map => mapT step xs
    | .filter => filterT step xs
    | .foldl => []
  | .tup [.tup xs, init] =>
    match k with
    | .foldl => foldlT step init xs
    | _ => []
  | _ => []

mutual
/-- The meaning of a term in an environment (index `k` is `ρ[k]`). -/
def eval (D : Dialect) : Tm → List Val → Trace
  | .var k, ρ => D.varRead (ρ.getD k (.sym .emp))
  | .lit l, _ => ret l.val
  | .quote t, _ => ret (.syn t)
  | .tup xs, ρ => D.meter ++ evalArgs D xs ρ
  | .empty, _ => D.meter
  | .if3 c t e, ρ => D.meter ++ bindT (eval D c ρ) fun v =>
      branch3 v (eval D t ρ) (eval D e ρ)
        (if D.elseOnNonBool then eval D e ρ else D.nonBool (.if3 c t e) v)
  | .if2 c t, ρ => D.meter ++
      if D.if2 then bindT (eval D c ρ) (fun v => branch3 v (eval D t ρ) []
        (if D.elseOnNonBool then [] else D.nonBool (.if2 c t) v))
      else D.arity (.if2 c t)
  | .let_ e b, ρ => D.meter ++ bindT (eval D e ρ) fun v => eval D b (v :: ρ)
  | .letStar es b, ρ => D.meter ++ evalLS D es (fun ρ' => eval D b ρ') ρ
  | .case_ e alts, ρ => D.meter ++
      (bindT (eval D e ρ) (fun v => select D alts v ρ) ++
        if hasAns (eval D e ρ) then [] else onEmpty D alts ρ)
  | .sup xs, ρ => D.meter ++ evalSup D xs ρ
  | .once b, ρ => D.meter ++ firstAns (eval D b ρ)
  | .call f args, ρ => D.meter ++ bindT (evalArgs D args ρ) (applyTup (D.fn f))
  | .iterC k ops f, ρ => D.meter ++ bindT (evalArgs D ops ρ) (iterate k (D.fn f))
  | .iterB k ops b, ρ => D.meter ++
      bindT (evalArgs D ops ρ) (iterate k fun vs => eval D b (vs.reverse ++ ρ))
/-- Strict arguments: every combination of answers, as a tuple. -/
def evalArgs (D : Dialect) : List Tm → List Val → Trace
  | [], _ => ret (.tup [])
  | x :: xs, ρ => bindT (eval D x ρ) fun v => bindT (evalArgs D xs ρ) (consTup v)
/-- Alternatives, in order. -/
def evalSup (D : Dialect) : List Tm → List Val → Trace
  | [], _ => []
  | x :: xs, ρ => eval D x ρ ++ evalSup D xs ρ
/-- `let*`: each source binds one index, then `k` runs. -/
def evalLS (D : Dialect) : List Tm → (List Val → Trace) → List Val → Trace
  | [], k, ρ => k ρ
  | e :: es, k, ρ => bindT (eval D e ρ) fun v => evalLS D es k (v :: ρ)
/-- The first branch matching a value. -/
def select (D : Dialect) : List (Pat × Tm) → Val → List Val → Trace
  | [], _, _ => []
  | (.bind, b) :: _, v, ρ => eval D b (v :: ρ)
  | (.lit l, b) :: rest, v, ρ => if l.matches v then eval D b ρ else select D rest v ρ
/-- The branch a dialect runs when the scrutinee has no answer. -/
def onEmpty (D : Dialect) : List (Pat × Tm) → List Val → Trace
  | [], _ => []
  | (p, b) :: rest, ρ =>
    match D.caseEmpty, p with
    | .none, _ => []
    | .literal, .bind => onEmpty D rest ρ
    | .literal, .lit l => if l.matches (.sym .emp) then eval D b ρ else onEmpty D rest ρ
    | .matching, .bind => eval D b (.sym .emp :: ρ)
    | .matching, .lit l => if l.matches (.sym .emp) then eval D b ρ else onEmpty D rest ρ
end

/-! ## The trace monad -/

@[simp] theorem bindT_nil (f : Val → Trace) : bindT [] f = [] := rfl

@[simp] theorem bindT_ret (v : Val) (f : Val → Trace) : bindT (ret v) f = f v := by
  simp [bindT, ret]

theorem bindT_append (t u : Trace) (f : Val → Trace) :
    bindT (t ++ u) f = bindT t f ++ bindT u f := by
  simp [bindT]

theorem bindT_ret_right (t : Trace) : bindT t ret = t := by
  induction t with
  | nil => rfl
  | cons e t ih => cases e <;> simp_all [bindT, ret]

theorem bindT_assoc (t : Trace) (f g : Val → Trace) :
    bindT (bindT t f) g = bindT t fun v => bindT (f v) g := by
  induction t with
  | nil => rfl
  | cons e t ih =>
    cases e with
    | ans v => simp only [bindT, List.flatMap_cons] at ih ⊢; rw [List.flatMap_append, ih]
    | eff n => simp only [bindT, List.flatMap_cons] at ih ⊢; rw [List.flatMap_append, ih]; rfl

theorem bindT_congr (t : Trace) {f g : Val → Trace} (h : ∀ v, f v = g v) :
    bindT t f = bindT t g := by
  simp only [bindT]; congr 1; funext e; cases e <;> simp [h]

theorem firstAns_bindT_ret (t : Trace) : bindT (firstAns t) ret = firstAns t :=
  bindT_ret_right _

/-- Continuations that agree on a run's answers agree on the run. -/
theorem bindT_congr_on (t : Trace) {f g : Val → Trace} (h : ∀ v, Ev.ans v ∈ t → f v = g v) :
    bindT t f = bindT t g := by
  induction t with
  | nil => rfl
  | cons e t ih =>
    have ht : bindT t f = bindT t g := ih fun v hv => h v (List.mem_cons_of_mem _ hv)
    cases e with
    | ans v =>
      have hv := h v (by simp)
      simp only [bindT, List.flatMap_cons] at ht ⊢
      rw [hv, ht]
    | eff n => simp only [bindT, List.flatMap_cons] at ht ⊢; rw [ht]

theorem hasAns_of_mem {t : Trace} {v : Val} (h : Ev.ans v ∈ t) : hasAns t = true := by
  induction t with
  | nil => simp at h
  | cons e t ih =>
    cases e with
    | ans w => rfl
    | eff n => exact ih (by simpa using h)

/-! ## Environments that respect facts -/

/-- An environment respects facts: every index known to hold an integer does. -/
def Sat (Γ : Facts) (ρ : List Val) : Prop :=
  ∀ k, Γ k = true → ∃ n, ρ.getD k (.sym .emp) = .int n

theorem Sat.push {Γ : Facts} {ρ : List Val} (h : Sat Γ ρ) (v : Val) :
    Sat (AdmissionRewriting.push Γ) (v :: ρ) := by
  intro k hk
  cases k with
  | zero => simp [AdmissionRewriting.push] at hk
  | succ k => simpa using h k hk

theorem Sat.pushN : ∀ {Γ : Facts} {ρ : List Val} (_ : Sat Γ ρ) (vs : List Val),
    Sat (AdmissionRewriting.pushN vs.length Γ) (vs.reverse ++ ρ)
  | _, _, h, [] => h
  | _, _, h, v :: vs => by
    have := Sat.pushN (h.push v) vs
    simpa [pushN_succ, List.reverse_cons, List.append_assoc] using this

theorem eval_intAtom {Γ : Facts} {ρ : List Val} (hρ : Sat Γ ρ) (D : Dialect)
    (hvr : ∀ n : ℤ, D.varRead (.int n) = ret (.int n)) {a : Tm}
    (ha : IntAtom Γ a = true) : ∃ n, eval D a ρ = ret (.int n) := by
  cases a with
  | var k => obtain ⟨n, hn⟩ := hρ k ha; exact ⟨n, by simp only [eval]; rw [hn, hvr]⟩
  | lit l =>
    cases l with
    | int n => exact ⟨n, rfl⟩
    | sym s => simp [IntAtom] at ha
  | _ => simp [IntAtom] at ha

/-! ## What the full system needs of a dialect -/

/-- `min`'s protocol: on its two evaluated arguments, the first unless it is not `<=` the
second, as the test of `minIf` answers it. -/
def MinProtocol (D : Dialect) : Prop :=
  ∀ x y : Val, D.fn .min [x, y] = bindT (D.fn .le [x, y]) fun c =>
    branch3 c (ret x) (ret y) (if D.elseOnNonBool then ret y else D.nonBool minIf c)

/-- A dialect on which every rule is sound. -/
structure Ready (D : Dialect) : Prop where
  meter : D.meter = []
  varRead : ∀ v, D.varRead v = ret v
  if2 : D.if2 = true
  nonBool : ∀ t t' v, D.nonBool t v = D.nonBool t' v
  caseEmpty : D.caseEmpty ≠ .matching
  id : ∀ v, D.fn .id [v] = ret v
  min : MinProtocol D

/-! ## Iterators respect their steps -/

theorem mapT_congr {s₁ s₂ : List Val → Trace} (h : ∀ x, s₁ [x] = s₂ [x]) :
    ∀ xs, mapT s₁ xs = mapT s₂ xs
  | [] => rfl
  | x :: xs => by simp only [mapT, h x, mapT_congr h xs]

theorem filterT_congr {s₁ s₂ : List Val → Trace} (h : ∀ x, s₁ [x] = s₂ [x]) :
    ∀ xs, filterT s₁ xs = filterT s₂ xs
  | [] => rfl
  | x :: xs => by simp only [filterT, h x, filterT_congr h xs]

theorem foldlT_congr {s₁ s₂ : List Val → Trace} (h : ∀ a x, s₁ [a, x] = s₂ [a, x]) :
    ∀ acc xs, foldlT s₁ acc xs = foldlT s₂ acc xs
  | _, [] => rfl
  | acc, x :: xs => by
    simp only [foldlT, h acc x]
    exact bindT_congr _ fun a => foldlT_congr h a xs

theorem iterate_congr (k : Iter) {s₁ s₂ : List Val → Trace}
    (h : ∀ vs, vs.length = k.binders → s₁ vs = s₂ vs) (v : Val) :
    iterate k s₁ v = iterate k s₂ v := by
  have h1 : ∀ x, k.binders = 1 → s₁ [x] = s₂ [x] := fun x hk => h [x] (by simp [hk])
  have h2 : ∀ a x, k.binders = 2 → s₁ [a, x] = s₂ [a, x] := fun a x hk => h [a, x] (by simp [hk])
  unfold iterate
  split
  · cases k with
    | map => exact mapT_congr (fun x => h1 x rfl) _
    | filter => exact filterT_congr (fun x => h1 x rfl) _
    | foldl => rfl
  · cases k with
    | foldl => exact foldlT_congr (fun a x => h2 a x rfl) _ _
    | _ => rfl
  · rfl

/-! ## Shifting: a term moved under a binder means what it meant -/

/-- An environment with `v` inserted at index `c` (missing indices read as `Empty`). -/
def insertAt : ℕ → Val → List Val → List Val
  | 0, v, ρ => v :: ρ
  | c + 1, v, [] => .sym .emp :: insertAt c v []
  | c + 1, v, w :: ρ => w :: insertAt c v ρ

theorem insertAt_cons (c : ℕ) (v w : Val) (ρ : List Val) :
    insertAt (c + 1) v (w :: ρ) = w :: insertAt c v ρ := rfl

theorem insertAt_append (v : Val) :
    ∀ (ws ρ : List Val) (c : ℕ), insertAt (c + ws.length) v (ws ++ ρ) = ws ++ insertAt c v ρ
  | [], _, _ => rfl
  | w :: ws, ρ, c => by
    rw [List.length_cons, show c + (ws.length + 1) = (c + ws.length) + 1 by omega,
      List.cons_append, insertAt_cons, insertAt_append v ws ρ c]
    rfl

theorem getD_insertAt_lt (v : Val) :
    ∀ (c k : ℕ) (ρ : List Val), k < c →
      (insertAt c v ρ).getD k (.sym .emp) = ρ.getD k (.sym .emp)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | c + 1, 0, [], _ => rfl
  | c + 1, 0, _ :: _, _ => rfl
  | c + 1, k + 1, [], h => by
    have := getD_insertAt_lt v c k [] (by omega)
    simpa [insertAt] using this
  | c + 1, k + 1, _ :: ρ, h => by
    have := getD_insertAt_lt v c k ρ (by omega)
    simpa [insertAt] using this

theorem getD_insertAt_ge (v : Val) :
    ∀ (c k : ℕ) (ρ : List Val), c ≤ k →
      (insertAt c v ρ).getD (k + 1) (.sym .emp) = ρ.getD k (.sym .emp)
  | 0, _, _, _ => rfl
  | c + 1, 0, _, h => absurd h (by omega)
  | c + 1, k + 1, [], h => by
    have := getD_insertAt_ge v c k [] (by omega)
    simpa [insertAt] using this
  | c + 1, k + 1, _ :: ρ, h => by
    have := getD_insertAt_ge v c k ρ (by omega)
    simpa [insertAt] using this

section Shift

variable {D : Dialect}

mutual
/-- **A shifted term reads the inserted environment as the term reads the original**, on a
dialect whose non-Boolean `if` does not quote its own spelling. -/
theorem eval_shift (hnb : ∀ t t' v, D.nonBool t v = D.nonBool t' v) (hif2 : D.if2 = true)
    (v : Val) :
    ∀ (c : ℕ) (t : Tm) (ρ : List Val), eval D (shift c t) (insertAt c v ρ) = eval D t ρ
  | c, .var k, ρ => by
    simp only [shift, eval]
    split
    · rename_i h; rw [getD_insertAt_lt v c k ρ h]
    · rename_i h; rw [getD_insertAt_ge v c k ρ (by omega)]
  | _, .lit _, _ => rfl
  | _, .quote _, _ => rfl
  | c, .tup xs, ρ => by simp only [shift, eval, evalArgs_shift hnb hif2 v c xs ρ]
  | _, .empty, _ => rfl
  | c, .if3 a b d, ρ => by
    simp only [shift, eval, eval_shift hnb hif2 v c a ρ, eval_shift hnb hif2 v c b ρ, eval_shift hnb hif2 v c d ρ]
    congr 1
    exact bindT_congr _ fun w => by rw [hnb]
  | c, .if2 a b, ρ => by
    simp only [shift, eval, hif2, if_true, eval_shift hnb hif2 v c a ρ, eval_shift hnb hif2 v c b ρ]
    congr 1
    exact bindT_congr _ fun w => by rw [hnb]
  | c, .let_ e b, ρ => by
    simp only [shift, eval, eval_shift hnb hif2 v c e ρ]
    congr 1
    exact bindT_congr _ fun w => by rw [← insertAt_cons, eval_shift hnb hif2 v (c + 1) b (w :: ρ)]
  | c, .letStar es b, ρ => by
    simp only [shift, eval]
    congr 1
    exact evalLS_shift hnb hif2 v es b (fun c' ρ' => eval_shift hnb hif2 v c' b ρ') c ρ
  | c, .case_ e alts, ρ => by
    simp only [shift, eval, eval_shift hnb hif2 v c e ρ, onEmpty_shift hnb hif2 v c alts ρ]
    congr 2
    exact bindT_congr _ fun w => select_shift hnb hif2 v c alts w ρ
  | c, .sup xs, ρ => by simp only [shift, eval, evalSup_shift hnb hif2 v c xs ρ]
  | c, .once b, ρ => by simp only [shift, eval, eval_shift hnb hif2 v c b ρ]
  | c, .call f args, ρ => by simp only [shift, eval, evalArgs_shift hnb hif2 v c args ρ]
  | c, .iterC k ops f, ρ => by simp only [shift, eval, evalArgs_shift hnb hif2 v c ops ρ]
  | c, .iterB k ops b, ρ => by
    simp only [shift, eval, evalArgs_shift hnb hif2 v c ops ρ]
    congr 1
    refine bindT_congr _ fun w => iterate_congr k (fun vs hl => ?_) w
    have := eval_shift hnb hif2 v (c + vs.reverse.length) b (vs.reverse ++ ρ)
    rw [insertAt_append, List.length_reverse, hl] at this
    exact this
/-- The argument version. -/
theorem evalArgs_shift (hnb : ∀ t t' v, D.nonBool t v = D.nonBool t' v) (hif2 : D.if2 = true)
    (v : Val) :
    ∀ (c : ℕ) (xs : List Tm) (ρ : List Val),
      evalArgs D (shifts c xs) (insertAt c v ρ) = evalArgs D xs ρ
  | _, [], _ => rfl
  | c, x :: xs, ρ => by
    simp only [shifts, evalArgs, eval_shift hnb hif2 v c x ρ, evalArgs_shift hnb hif2 v c xs ρ]
/-- The alternative version. -/
theorem evalSup_shift (hnb : ∀ t t' v, D.nonBool t v = D.nonBool t' v) (hif2 : D.if2 = true)
    (v : Val) :
    ∀ (c : ℕ) (xs : List Tm) (ρ : List Val),
      evalSup D (shifts c xs) (insertAt c v ρ) = evalSup D xs ρ
  | _, [], _ => rfl
  | c, x :: xs, ρ => by
    simp only [shifts, evalSup, eval_shift hnb hif2 v c x ρ, evalSup_shift hnb hif2 v c xs ρ]
/-- The `let*` version: each source one binder deeper, the body under all of them. -/
theorem evalLS_shift (hnb : ∀ t t' v, D.nonBool t v = D.nonBool t' v) (hif2 : D.if2 = true)
    (v : Val) :
    ∀ (es : List Tm) (b : Tm),
      (∀ (c' : ℕ) (ρ' : List Val), eval D (shift c' b) (insertAt c' v ρ') = eval D b ρ') →
      ∀ (c : ℕ) (ρ : List Val),
        evalLS D (shiftLS c es) (fun ρ' => eval D (shift (c + es.length) b) ρ') (insertAt c v ρ) =
          evalLS D es (fun ρ' => eval D b ρ') ρ
  | [], b, hb, c, ρ => by simpa [shiftLS, evalLS] using hb c ρ
  | e :: es, b, hb, c, ρ => by
    simp only [shiftLS, evalLS, eval_shift hnb hif2 v c e ρ]
    refine bindT_congr _ fun w => ?_
    rw [← insertAt_cons]
    have := evalLS_shift hnb hif2 v es b hb (c + 1) (w :: ρ)
    rwa [show c + 1 + es.length = c + (e :: es).length by simp; omega] at this
/-- The branch version. -/
theorem select_shift (hnb : ∀ t t' v, D.nonBool t v = D.nonBool t' v) (hif2 : D.if2 = true)
    (v : Val) :
    ∀ (c : ℕ) (alts : List (Pat × Tm)) (w : Val) (ρ : List Val),
      select D (shiftAlts c alts) w (insertAt c v ρ) = select D alts w ρ
  | _, [], _, _ => rfl
  | c, (.bind, b) :: _, w, ρ => by
    simp only [shiftAlts, Pat.binders, select]
    rw [← insertAt_cons, eval_shift hnb hif2 v (c + 1) b (w :: ρ)]
  | c, (.lit l, b) :: rest, w, ρ => by
    simp only [shiftAlts, Pat.binders, Nat.add_zero, select, eval_shift hnb hif2 v c b ρ,
      select_shift hnb hif2 v c rest w ρ]
/-- The empty-scrutinee version. -/
theorem onEmpty_shift (hnb : ∀ t t' v, D.nonBool t v = D.nonBool t' v) (hif2 : D.if2 = true)
    (v : Val) :
    ∀ (c : ℕ) (alts : List (Pat × Tm)) (ρ : List Val),
      onEmpty D (shiftAlts c alts) (insertAt c v ρ) = onEmpty D alts ρ
  | _, [], _ => rfl
  | c, (.bind, b) :: rest, ρ => by
    simp only [shiftAlts, Pat.binders, onEmpty]
    have hb : eval D (shift (c + 1) b) (.sym .emp :: insertAt c v ρ) =
        eval D b (.sym .emp :: ρ) := by
      rw [← insertAt_cons, eval_shift hnb hif2 v (c + 1) b]
    have hr := onEmpty_shift hnb hif2 v c rest ρ
    cases D.caseEmpty with
    | none => rfl
    | literal => exact hr
    | matching => exact hb
  | c, (.lit l, b) :: rest, ρ => by
    simp only [shiftAlts, Pat.binders, Nat.add_zero, onEmpty]
    have hb := eval_shift hnb hif2 v c b ρ
    have hr := onEmpty_shift hnb hif2 v c rest ρ
    cases D.caseEmpty with
    | none => rfl
    | literal => simp only [hb, hr]
    | matching => simp only [hb, hr]
end

end Shift

/-! ## The rules, one by one -/

section Rules

variable (D : Dialect) (hm : D.meter = [])
include hm

theorem if2_sound (h2 : D.if2 = true) (c t : Tm)
    (hnb : D.elseOnNonBool = true ∨ ∀ v, D.nonBool (.if2 c t) v = D.nonBool (.if3 c t .empty) v)
    (ρ : List Val) : eval D (.if2 c t) ρ = eval D (.if3 c t .empty) ρ := by
  simp only [eval, h2, if_true, hm, List.nil_append]
  refine bindT_congr _ fun v => ?_
  rcases hnb with he | hnb
  · simp [he]
  · cases D.elseOnNonBool <;> simp [hnb]

theorem evalLS_nest (es : List Tm) (b : Tm) :
    ∀ ρ, eval D (nest es b) ρ = evalLS D es (fun ρ' => eval D b ρ') ρ := by
  induction es with
  | nil => intro ρ; rfl
  | cons e es ih =>
    intro ρ
    simp only [nest, eval, hm, List.nil_append, evalLS]
    exact bindT_congr _ fun v => ih (v :: ρ)

theorem letStar_sound (es : List Tm) (b : Tm) (ρ : List Val) :
    eval D (.letStar es b) ρ = eval D (nest es b) ρ := by
  rw [evalLS_nest D hm]; simp [eval, hm]

theorem case1_sound (hce : D.caseEmpty ≠ .matching) (e b : Tm) (ρ : List Val) :
    eval D (.case_ e [(.bind, b)]) ρ = eval D (.let_ e b) ρ := by
  have hz : onEmpty D [(.bind, b)] ρ = [] := by
    cases hc : D.caseEmpty with
    | none => simp [onEmpty, hc]
    | literal => simp [onEmpty, hc]
    | matching => exact absurd hc hce
  simp [eval, hm, select, hz]

theorem id_sound (hid : ∀ v, D.fn .id [v] = ret v) (x : Tm) (ρ : List Val) :
    eval D (.call .id [x]) ρ = eval D x ρ := by
  simp only [eval, evalArgs, hm, List.nil_append, bindT_assoc, bindT_ret, consTup, applyTup,
    hid]
  exact bindT_ret_right _

theorem sup1_sound (x : Tm) (ρ : List Val) : eval D (.sup [x]) ρ = eval D x ρ := by
  simp [eval, evalSup, hm]

theorem call_vars (hvr : ∀ v, D.varRead v = ret v) (f : Name) (k : Iter) (vs : List Val)
    (ρ : List Val) (hl : vs.length = k.binders) :
    eval D (.call f k.vars) (vs.reverse ++ ρ) = D.fn f vs := by
  cases k with
  | foldl =>
    match vs, hl with
    | [a, x], _ => simp [eval, evalArgs, Iter.vars, hm, hvr, consTup, applyTup]
  | map =>
    match vs, hl with
    | [x], _ => simp [eval, evalArgs, Iter.vars, hm, hvr, consTup, applyTup]
  | filter =>
    match vs, hl with
    | [x], _ => simp [eval, evalArgs, Iter.vars, hm, hvr, consTup, applyTup]

theorem callable_sound (hvr : ∀ v, D.varRead v = ret v) (k : Iter) (ops : List Tm) (f : Name)
    (ρ : List Val) : eval D (.iterC k ops f) ρ = eval D (.iterB k ops (.call f k.vars)) ρ := by
  simp only [eval]
  congr 1
  exact bindT_congr _ fun v =>
    iterate_congr k (fun vs hl => (call_vars D hm hvr f k vs ρ hl).symm) v

/-- A strict unary call and its argument bound by a `let` agree, whatever the call. -/
theorem size_sound (hvr : ∀ v, D.varRead v = ret v) (g : Name) (e : Tm) (ρ : List Val) :
    eval D (.call g [e]) ρ = eval D (.let_ e (.call g [.var 0])) ρ := by
  simp [eval, evalArgs, hm, hvr, bindT_assoc, consTup, applyTup]

/-- **`min` keeps its protocol**: its protocol form evaluates `a` once, then `b` once per
answer of `a`, and answers by `min`'s test, for every pair of operands. -/
theorem min_sound (hvr : ∀ v, D.varRead v = ret v)
    (hnb : ∀ t t' v, D.nonBool t v = D.nonBool t' v) (hif2 : D.if2 = true)
    (hmin : MinProtocol D) (a b : Tm) (ρ : List Val) :
    eval D (.call .min [a, b]) ρ = eval D (minForm a b) ρ := by
  simp only [minForm, eval, evalArgs, hm, List.nil_append, bindT_assoc]
  refine bindT_congr _ fun x => ?_
  rw [← eval_shift hnb hif2 x 0 b ρ]
  simp only [insertAt]
  refine bindT_congr _ fun y => ?_
  simp only [minIf, eval, evalArgs, hm, hvr, List.getD_cons_zero, List.getD_cons_succ,
    bindT_ret, consTup, applyTup, List.nil_append]
  exact hmin x y

theorem sizeVar_sound (hvr : ∀ v, D.varRead v = ret v) (j : ℕ) (ρ : List Val) :
    eval D (.let_ (.var j) (.call .size [.var 0])) ρ = eval D (.call .size [.var j]) ρ := by
  simp [eval, evalArgs, hm, hvr, consTup, applyTup]

theorem letEta_sound (hvr : ∀ v, D.varRead v = ret v) (e b : Tm) (ρ : List Val) :
    eval D (.let_ (.let_ e (.var 0)) b) ρ = eval D (.let_ e b) ρ := by
  simp only [eval, hm, List.nil_append, hvr, bindT_assoc]
  exact bindT_congr _ fun v => by simp

theorem wrap_sound (hvr : ∀ v, D.varRead v = ret v) (b : Tm) (ρ : List Val) :
    eval D (.let_ (.once b) (.var 0)) ρ = eval D (.once b) ρ := by
  simp only [eval, hm, List.nil_append, hvr]
  exact firstAns_bindT_ret _

/-! ### Where a dialect evaluates answers again: the rules on settled answers

HE evaluates a held value again wherever a variable brings it into an evaluated position,
and `id`'s answer is such a read.  On answers that are settled (evaluating them again
changes nothing) `id` and `letEta` are sound; `case1` needs only a scrutinee that
answers, since HE's `case` runs a binding branch on an empty scrutinee. -/

theorem id_sound_on (x : Tm) (ρ : List Val)
    (hset : ∀ v, Ev.ans v ∈ eval D x ρ → D.fn .id [v] = ret v) :
    eval D (.call .id [x]) ρ = eval D x ρ := by
  simp only [eval, evalArgs, hm, List.nil_append, bindT_assoc, bindT_ret, consTup, applyTup]
  rw [bindT_congr_on _ hset]
  exact bindT_ret_right _

theorem letEta_sound_on (e b : Tm) (ρ : List Val)
    (hset : ∀ v, Ev.ans v ∈ eval D e ρ → D.varRead v = ret v) :
    eval D (.let_ (.let_ e (.var 0)) b) ρ = eval D (.let_ e b) ρ := by
  simp only [eval, hm, List.nil_append]
  rw [bindT_congr_on (eval D e ρ) (g := ret) (fun v hv => by simpa using hset v hv),
    bindT_ret_right]

theorem case1_sound_answering (e b : Tm) (ρ : List Val) (hans : hasAns (eval D e ρ) = true) :
    eval D (.case_ e [(.bind, b)]) ρ = eval D (.let_ e b) ρ := by
  simp [eval, hm, select, hans]

end Rules

/-! ## Congruence -/

section Congruence

variable {D : Dialect}

theorem evalArgs_congr {x x' : Tm} {ρ : List Val} (h : eval D x ρ = eval D x' ρ) :
    ∀ pre post : List Tm, evalArgs D (pre ++ x :: post) ρ = evalArgs D (pre ++ x' :: post) ρ
  | [], post => by simp only [List.nil_append, evalArgs, h]
  | p :: pre, post => by
    simp only [List.cons_append, evalArgs]
    rw [evalArgs_congr h pre post]

theorem evalSup_congr {x x' : Tm} {ρ : List Val} (h : eval D x ρ = eval D x' ρ) :
    ∀ pre post : List Tm, evalSup D (pre ++ x :: post) ρ = evalSup D (pre ++ x' :: post) ρ
  | [], post => by simp only [List.nil_append, evalSup, h]
  | p :: pre, post => by
    simp only [List.cons_append, evalSup]
    rw [evalSup_congr h pre post]

theorem evalLS_congr_src {e e' : Tm} (post : List Tm) (k : List Val → Trace) :
    ∀ (pre : List Tm) (Γ : Facts) (ρ : List Val), Sat Γ ρ →
      (∀ ρ', Sat (pushN pre.length Γ) ρ' → eval D e ρ' = eval D e' ρ') →
      evalLS D (pre ++ e :: post) k ρ = evalLS D (pre ++ e' :: post) k ρ
  | [], Γ, ρ, hρ, h => by simp only [List.nil_append, evalLS, h ρ hρ]
  | p :: pre, Γ, ρ, hρ, h => by
    simp only [List.cons_append, evalLS]
    exact bindT_congr _ fun v =>
      evalLS_congr_src post k pre (push Γ) (v :: ρ) (hρ.push v) (by simpa [pushN_succ] using h)

theorem evalLS_congr_k {k k' : List Val → Trace} :
    ∀ (es : List Tm) (Γ : Facts) (ρ : List Val), Sat Γ ρ →
      (∀ ρ', Sat (pushN es.length Γ) ρ' → k ρ' = k' ρ') → evalLS D es k ρ = evalLS D es k' ρ
  | [], Γ, ρ, hρ, h => by simpa [evalLS] using h ρ hρ
  | e :: es, Γ, ρ, hρ, h => by
    simp only [evalLS]
    exact bindT_congr _ fun v =>
      evalLS_congr_k es (push Γ) (v :: ρ) (hρ.push v) (by simpa [pushN_succ] using h)

theorem select_congr {Γ : Facts} {p : Pat} {b b' : Tm} (v : Val) {ρ : List Val} (hρ : Sat Γ ρ)
    (h : ∀ ρ', Sat (p.scope Γ) ρ' → eval D b ρ' = eval D b' ρ') :
    ∀ pre post : List (Pat × Tm),
      select D (pre ++ (p, b) :: post) v ρ = select D (pre ++ (p, b') :: post) v ρ
  | [], post => by
    cases p with
    | bind => simp only [List.nil_append, select]; exact h _ (hρ.push v)
    | lit l => simp only [List.nil_append, select, h ρ hρ]
  | (q, c) :: pre, post => by
    cases q with
    | bind => rfl
    | lit l => simp only [List.cons_append, select]; rw [select_congr v hρ h pre post]

theorem onEmpty_congr {Γ : Facts} {p : Pat} {b b' : Tm} {ρ : List Val} (hρ : Sat Γ ρ)
    (h : ∀ ρ', Sat (p.scope Γ) ρ' → eval D b ρ' = eval D b' ρ') :
    ∀ pre post : List (Pat × Tm),
      onEmpty D (pre ++ (p, b) :: post) ρ = onEmpty D (pre ++ (p, b') :: post) ρ
  | [], post => by
    cases p with
    | bind =>
      simp only [List.nil_append, onEmpty]
      cases D.caseEmpty with
      | none => rfl
      | literal => rfl
      | matching => exact h _ (hρ.push _)
    | lit l =>
      simp only [List.nil_append, onEmpty]
      cases D.caseEmpty with
      | none => rfl
      | literal => rw [h ρ hρ]
      | matching => rw [h ρ hρ]
  | (q, c) :: pre, post => by
    simp only [List.cons_append, onEmpty]
    rw [onEmpty_congr hρ h pre post]

end Congruence

/-- On a ready dialect, a step at any position keeps the trace. -/
theorem step_sound {D : Dialect} (hD : Ready D) {top : Bool} {Γ : Facts} {t t' : Tm}
    (h : Step top Γ t t') : ∀ ρ, Sat Γ ρ → eval D t ρ = eval D t' ρ := by
  have hm := hD.meter
  induction h with
  | rule r =>
    intro ρ hρ
    cases r with
    | if2 c t => exact if2_sound D hm hD.if2 c t (.inr fun v => hD.nonBool _ _ v) ρ
    | letStar es b => exact letStar_sound D hm es b ρ
    | case1 e b => exact case1_sound D hm hD.caseEmpty e b ρ
    | id => exact id_sound D hm hD.id _ ρ
    | sup1 => exact sup1_sound D hm _ ρ
    | callable k ops f => exact callable_sound D hm hD.varRead k ops f ρ
    | size e _ => exact size_sound D hm hD.varRead .size e ρ
    | min a b => exact min_sound D hm hD.varRead hD.nonBool hD.if2 hD.min a b ρ
    | sizeVar j => exact sizeVar_sound D hm hD.varRead j ρ
    | letEta e b => exact letEta_sound D hm hD.varRead e b ρ
  | wrap b => intro ρ _; exact (wrap_sound D hm hD.varRead b ρ).symm
  | tup pre post _ ih => intro ρ hρ; simp only [eval, evalArgs_congr (ih ρ hρ)]
  | if3c t e _ ih =>
    intro ρ hρ; simp only [eval, ih ρ hρ]; congr 1
    exact bindT_congr _ fun v => by rw [hD.nonBool]
  | if3t c e _ ih =>
    intro ρ hρ; simp only [eval, ih ρ hρ]; congr 1
    exact bindT_congr _ fun v => by rw [hD.nonBool]
  | if3e c t _ ih =>
    intro ρ hρ; simp only [eval, ih ρ hρ]; congr 1
    exact bindT_congr _ fun v => by rw [hD.nonBool]
  | if2c t _ ih =>
    intro ρ hρ; simp only [eval, ih ρ hρ, hD.if2, if_true]; congr 1
    exact bindT_congr _ fun v => by rw [hD.nonBool]
  | if2t c _ ih =>
    intro ρ hρ; simp only [eval, ih ρ hρ, hD.if2, if_true]; congr 1
    exact bindT_congr _ fun v => by rw [hD.nonBool]
  | letE b _ ih => intro ρ hρ; simp only [eval, ih ρ hρ]
  | letB e _ ih =>
    intro ρ hρ; simp only [eval]; congr 1
    exact bindT_congr _ fun v => ih (v :: ρ) (hρ.push v)
  | letStarE pre post b _ ih =>
    intro ρ hρ; simp only [eval]; congr 1
    exact evalLS_congr_src post _ pre _ ρ hρ ih
  | letStarB es _ ih =>
    intro ρ hρ; simp only [eval]; congr 1
    exact evalLS_congr_k es _ ρ hρ ih
  | caseE alts _ ih => intro ρ hρ; simp only [eval, ih ρ hρ]
  | caseB e pre post p _ ih =>
    intro ρ hρ; simp only [eval]; congr 1
    rw [onEmpty_congr hρ ih pre post]
    congr 1
    exact bindT_congr _ fun v => select_congr v hρ ih pre post
  | sup pre post _ ih => intro ρ hρ; simp only [eval, evalSup_congr (ih ρ hρ)]
  | once _ ih => intro ρ hρ; simp only [eval, ih ρ hρ]
  | call f pre post _ ih => intro ρ hρ; simp only [eval, evalArgs_congr (ih ρ hρ)]
  | iterCOps k pre post f _ ih => intro ρ hρ; simp only [eval, evalArgs_congr (ih ρ hρ)]
  | iterBOps k pre post b _ ih => intro ρ hρ; simp only [eval, evalArgs_congr (ih ρ hρ)]
  | iterBBody k ops _ ih =>
    intro ρ hρ; simp only [eval]; congr 1
    refine bindT_congr _ fun v => iterate_congr k (fun vs hl => ?_) v
    exact ih _ (by simpa [hl] using hρ.pushN vs)

theorem star_sound {D : Dialect} (hD : Ready D) {top : Bool} {Γ : Facts} {t t' : Tm}
    (h : Relation.ReflTransGen (Step top Γ) t t') (ρ : List Val) (hρ : Sat Γ ρ) :
    eval D t ρ = eval D t' ρ := by
  induction h with
  | refl => rfl
  | tail _ hs ih => rw [ih, step_sound hD hs ρ hρ]

/-- Convertible terms mean the same. -/
theorem conv_sound {D : Dialect} (hD : Ready D) {Γ : Facts} {t t' : Tm}
    (h : Relation.EqvGen (Step true Γ) t t') (ρ : List Val) (hρ : Sat Γ ρ) :
    eval D t ρ = eval D t' ρ := by
  induction h with
  | rel _ _ h => exact step_sound hD h ρ hρ
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The normal form means what the term means. -/
theorem N_sound {D : Dialect} (hD : Ready D) (Γ : Facts) (t : Tm) (ρ : List Val)
    (hρ : Sat Γ ρ) : eval D (N Γ t) ρ = eval D t ρ :=
  (star_sound hD (reduces Γ t) ρ hρ).symm

end Mettapedia.Machines.AdmissionRewriting
