import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceSpec

/-!
# The `data` form: a constructor term built from evaluated fields

MeTTa writes a call and a constructor term alike: `(f a b)` runs the equations
of `f` when it has some, and is otherwise the term itself. The `data` form
fixes the second reading at one occurrence: `(data f a b)` evaluates the fields
`a` and `b` and builds the term `(f a' b')` without consulting the equations of
`f`.

In the branch-local Need calculus, `data f m₀ … m_{k-1}` sequences the field
computations and returns the spine of their values. This module proves its
laws and separates it from the neighbouring forms.

* **Building never consults the equations.** For any program, `data` over held
  syntax returns exactly the spine (`data_held_fields`), where a call dispatches
  to the head's equations (`Controls.call_runs_the_equation`).
* **The fields are computations of the building occurrence.** When every field
  answers without failure or store change, `data` answers one term for each
  combination of the fields' answers, the first field varying slowest
  (`data_answers`). Effects also happen when the term is built, in field order,
  and a failing field fails the combinations it belongs to
  (`Controls.fields_choose_at_build`, `Controls.field_effects_at_build`,
  `Controls.failing_field_fails_each_combination`).
* **`quote` holds code instead.** It yields one opaque cell, whose alternatives
  and effects happen only when it is run (`Controls.quote_defers_the_choice`),
  and which no constructor pattern matches (`code_matches_no_constructor`).
  A built term is matched by its head (`matchCon_spine`).
* **Per field, the two compose.** A field may be computed, held as code by
  `quote`, or given as held syntax, all in one occurrence
  (`Controls.fields_mix_modes`). Without `quote` every computed field runs when
  the term is built (`Controls.data_alone_evaluates_every_field`); without
  `data`, `quote` holds the whole term and nothing runs
  (`Controls.quote_alone_holds_every_field`).
* **Reflection eliminates built data.** A dispatch on the term's head over the
  program's heads calls the equations on exactly the built fields
  (`reflect_built`, `reflect_calls_on_fields`) and leaves a term whose head has
  no listed equations as it is (`reflect_unlisted`). `run` executes code only
  and leaves built data inert (`run_built_is_inert`).
* **Redundancy depends on the surface.** The calculus fails a call of a head
  without equations, so there `data` is the only builder
  (`Controls.call_without_equations_fails`). MeTTa reads such a head as data,
  so there `data` adds nothing for it. For a head with equations the surface
  reading calls them, and `data` gives a different result unless the equations
  rebuild the term (`Controls.surface_reading_differs_from_data`,
  `Controls.rebuilding_equation_is_indistinguishable`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.Native.DataForm

open Mettapedia.Machines.BranchLocalNeed.CallTimeChoice

/-! ## Constructor spines -/

/-- The constructor term `f w₀ … w_{k-1}`: nested applications to the head. -/
def spine (head : Nat) (fields : List (Val Nat)) : Val Nat :=
  fields.foldl Val.app (.sym head)

theorem spine_foldl (start : Val Nat) (fields : List (Val Nat)) :
    (fields.foldl Val.app start).spine =
      start.spine.map fun found => (found.1, found.2 ++ fields) := by
  induction fields generalizing start with
  | nil => cases h : start.spine <;> simp [h]
  | cons field fields ih =>
      rw [List.foldl_cons, ih]
      cases h : start.spine <;> simp [Val.spine, h]

theorem spine_spine (head : Nat) (fields : List (Val Nat)) :
    (spine head fields).spine = some (head, fields) := by
  simp [spine, spine_foldl, Val.spine]

/-- A built term is matched by the constructor pattern of its head and arity,
which binds exactly its fields. -/
theorem matchCon_spine (head : Nat) (fields : List (Val Nat)) :
    (spine head fields).matchCon head fields.length = some fields := by
  simp [Val.matchCon, spine_spine]

/-- No pattern of another head or arity matches it. -/
theorem matchCon_spine_other (head other arity : Nat) (fields : List (Val Nat))
    (different : other ≠ head ∨ arity ≠ fields.length) :
    (spine head fields).matchCon other arity = none := by
  rcases different with different | different
  · simp [Val.matchCon, spine_spine, Ne.symm different]
  · simp [Val.matchCon, spine_spine, Ne.symm different]

/-- Code is opaque to matching: no constructor pattern matches a code value. -/
theorem code_matches_no_constructor (cell head arity : Nat) :
    (Val.code cell : Val Nat).matchCon head arity = none := by
  simp [Val.matchCon, Val.spine]

theorem spine_ne_code (head : Nat) (fields : List (Val Nat)) (cell : Nat) :
    spine head fields ≠ .code cell := by
  intro same
  have h := spine_spine head fields
  rw [same] at h
  simp [Val.spine] at h

/-! ## The form -/

/-- Raise every variable of a value expression past one new binder. -/
def shiftExp : VExp → VExp
  | .var index => .var (index + 1)
  | .sym name => .sym name
  | .app head arg => .app (shiftExp head) (shiftExp arg)

theorem eval_shiftExp (value : Val Nat) (env : List (Val Nat)) (term : VExp) :
    (shiftExp term).eval (value :: env) = term.eval env := by
  induction term with
  | var index => simp [shiftExp, VExp.eval]
  | sym name => rfl
  | app head arg ihHead ihArg => simp [shiftExp, VExp.eval, ihHead, ihArg]

/-- Evaluate the remaining fields in order, binding each one, then return the
accumulated term applied to their values. -/
def build (accumulated : VExp) : List Comp → Comp
  | [] => .ret accumulated
  | field :: fields => .seq field (build (.app (shiftExp accumulated) (.var 0)) fields)

/-- `(data f m₀ … m_{k-1})`: evaluate the fields in order and build the term
with head `f`. Field `i` is written for the environment extended by the `i`
fields before it, as every sequenced computation of the calculus is. -/
def data (head : Nat) (fields : List Comp) : Comp :=
  build (.sym head) fields

/-! ## Building over held syntax -/

/-- A value expression without variables: held syntax. -/
def closedExp : VExp → Bool
  | .var _ => false
  | .sym _ => true
  | .app head arg => closedExp head && closedExp arg

theorem eval_closed {term : VExp} (closed : closedExp term = true)
    (env env' : List (Val Nat)) : term.eval env = term.eval env' := by
  induction term with
  | var index => simp [closedExp] at closed
  | sym name => rfl
  | app head arg ihHead ihArg =>
      simp only [closedExp, Bool.and_eq_true] at closed
      simp [VExp.eval, ihHead closed.1, ihArg closed.2]

/-- Returning a value and continuing is continuing with that value bound. -/
theorem seq_ret_iff (program : Program) (store : Store) (env : List (Val Nat))
    (value : VExp) (rest : Comp) (results : List Result) :
    Derives program (.eval store env (.seq (.ret value) rest)) results ↔
      Derives program (.eval store (value.eval env :: env) rest) results := by
  constructor
  · intro derived
    cases derived with
    | seq first tail =>
      cases first
      cases tail with
      | seqKOk body nil =>
        cases nil
        simpa only [List.append_nil] using body
      | seqKStop stopped _ => simp [Outcome.isOk] at stopped
  · intro body
    exact Derives.seq_single Derives.ret body

theorem build_held (program : Program) (store : Store) (fields : List VExp)
    (closed : ∀ field ∈ fields, closedExp field = true) :
    ∀ (accumulated : VExp) (env : List (Val Nat)),
      Derives program (.eval store env (build accumulated (fields.map .ret)))
        [(.ok ((fields.map (·.eval [])).foldl Val.app (accumulated.eval env)), store)] := by
  induction fields with
  | nil => intro accumulated env; exact Derives.ret
  | cons field fields ih =>
      intro accumulated env
      have closedField : closedExp field = true := closed field List.mem_cons_self
      have closedRest : ∀ next ∈ fields, closedExp next = true :=
        fun next member => closed next (List.mem_cons_of_mem _ member)
      rw [List.map_cons, build, seq_ret_iff]
      have rest := ih closedRest (.app (shiftExp accumulated) (.var 0)) (field.eval env :: env)
      simpa [VExp.eval, eval_shiftExp, eval_closed closedField env []] using rest

/-- **Building never consults the equations.** Over held syntax, `data` has
exactly one result, the spine, in the same store, for every program, including
one with equations for the head. -/
theorem data_held_fields (program : Program) (store : Store) (env : List (Val Nat))
    (head : Nat) (fields : List VExp) (closed : ∀ field ∈ fields, closedExp field = true) :
    Derives program (.eval store env (data head (fields.map .ret)))
      [(.ok (spine head (fields.map (·.eval []))), store)] :=
  build_held program store fields closed (.sym head) env

theorem data_held_fields_exact (program : Program) (store : Store) (env : List (Val Nat))
    (head : Nat) (fields : List VExp) (closed : ∀ field ∈ fields, closedExp field = true)
    {results : List Result}
    (derived : Derives program (.eval store env (data head (fields.map .ret))) results) :
    results = [(.ok (spine head (fields.map (·.eval []))), store)] :=
  Derives.deterministic derived (data_held_fields program store env head fields closed)

/-! ## Building over computed fields -/

/-- A computation that, in every store and environment, answers exactly
`answers`, in order, leaving the store as it found it. -/
def Answers (program : Program) (field : Comp) (answers : List (Val Nat)) : Prop :=
  ∀ (store : Store) (env : List (Val Nat)),
    Derives program (.eval store env field) (answers.map fun answer => (.ok answer, store))

theorem answers_ret (program : Program) {term : VExp} (closed : closedExp term = true) :
    Answers program (.ret term) [term.eval []] := by
  intro store env
  rw [eval_closed closed [] env]
  exact Derives.ret

theorem answers_choose (program : Program) {left right : Comp}
    {leftAnswers rightAnswers : List (Val Nat)}
    (first : Answers program left leftAnswers) (second : Answers program right rightAnswers) :
    Answers program (.choose left right) (leftAnswers ++ rightAnswers) := by
  intro store env
  rw [List.map_append]
  exact Derives.choose (first store env) (second store env)

/-- The ordered combinations of one answer per field; the first field varies
slowest. -/
def combinations : List (List (Val Nat)) → List (List (Val Nat))
  | [] => [[]]
  | answers :: rest => answers.flatMap fun answer => (combinations rest).map (answer :: ·)

theorem seqK_answers (program : Program) (rest : Comp) (env : List (Val Nat))
    (store : Store) (results : Val Nat → List Result) :
    ∀ answers : List (Val Nat),
      (∀ answer ∈ answers, Derives program (.eval store (answer :: env) rest) (results answer)) →
        Derives program (.seqK rest env (answers.map fun answer => (.ok answer, store)))
          (answers.flatMap results)
  | [], _ => Derives.seqKNil
  | answer :: answers, each => by
      rw [List.map_cons, List.flatMap_cons]
      exact Derives.seqKOk (each answer List.mem_cons_self)
        (seqK_answers program rest env store results answers
          fun next member => each next (List.mem_cons_of_mem _ member))

theorem build_answers (program : Program) (store : Store) :
    ∀ {fields : List Comp} {answerLists : List (List (Val Nat))},
      List.Forall₂ (Answers program) fields answerLists →
      ∀ (accumulated : VExp) (env : List (Val Nat)),
        Derives program (.eval store env (build accumulated fields))
          ((combinations answerLists).map fun values =>
            (.ok (values.foldl Val.app (accumulated.eval env)), store))
  | _, _, .nil, accumulated, env => by
      simpa [combinations, build] using
        (Derives.ret (P := program) (σ := store) (ρ := env) (v := accumulated))
  | _, _, .cons (a := field) (b := answers) (l₁ := fields) (l₂ := rest) first others,
      accumulated, env => by
      have continued := seqK_answers program
        (build (.app (shiftExp accumulated) (.var 0)) fields) env store
        (fun answer => (combinations rest).map fun values =>
          (.ok (values.foldl Val.app
            ((VExp.app (shiftExp accumulated) (.var 0)).eval (answer :: env))), store))
        answers fun answer _ =>
          build_answers program store others (.app (shiftExp accumulated) (.var 0)) (answer :: env)
      have derived := Derives.seq (first store env) continued
      simpa [build, combinations, List.map_flatMap, Function.comp_def, VExp.eval,
        eval_shiftExp] using derived

/-- **The fields' alternatives multiply, in field order.** When every field
answers without failure or store change, `data` answers the term built from
each combination of the fields' answers, the first field varying slowest, in
the store it started from. -/
theorem data_answers (program : Program) (store : Store) (env : List (Val Nat))
    (head : Nat) {fields : List Comp} {answerLists : List (List (Val Nat))}
    (answering : List.Forall₂ (Answers program) fields answerLists) :
    Derives program (.eval store env (data head fields))
      ((combinations answerLists).map fun values => (.ok (spine head values), store)) :=
  build_answers program store answering (.sym head) env

/-! ## Reflection: the elimination of built data -/

/-- The variables `0 … k-1`: the fields that a constructor pattern binds. -/
def fieldVars (arity : Nat) : List VExp :=
  (List.range arity).map VExp.var

theorem length_fieldVars (arity : Nat) : (fieldVars arity).length = arity := by
  simp [fieldVars]

theorem eval_fieldVars (fields env : List (Val Nat)) :
    (fieldVars fields.length).map (·.eval (fields ++ env)) = fields := by
  apply List.ext_getElem
  · simp [fieldVars]
  · intro index inRange _
    have bound : index < fields.length := by simpa [fieldVars] using inRange
    simp [fieldVars, VExp.eval, List.getD_eq_getElem?_getD,
      List.getElem?_append_left bound, List.getElem?_eq_getElem bound]

/-- Reflection over the listed heads, each with its arity: the first listed
constructor pattern that matches the term calls that head's equations on the
fields. A term matched by no listed pattern stays as it is, as MeTTa leaves an
expression it cannot interpret. -/
def reflect : List (Nat × Nat) → VExp → Comp
  | [], term => .ret term
  | (head, arity) :: heads, term =>
      .caseCon term head arity (.call head (fieldVars arity)) (reflect heads term)

/-- **β for reflection.** Reflecting a built term whose head is listed first
behaves exactly as the call of that head with the built fields. -/
theorem reflect_built (program : Program) (store : Store) (env : List (Val Nat))
    (term : VExp) (head : Nat) (fields : List (Val Nat)) (heads : List (Nat × Nat))
    (results : List Result) (built : term.eval env = spine head fields) :
    Derives program (.eval store env (reflect ((head, fields.length) :: heads) term)) results ↔
      Derives program (.eval store (fields ++ env) (.call head (fieldVars fields.length)))
        results := by
  constructor
  · intro derived
    cases derived with
    | caseConHit matched body =>
        rw [built, matchCon_spine] at matched
        cases matched
        exact body
    | caseConMiss missed _ =>
        rw [built, matchCon_spine] at missed
        cases missed
  · intro body
    exact Derives.caseConHit (by rw [built, matchCon_spine]) body

/-- That call dispatches to the head's equations with exactly the built fields
as arguments, and fails when the head has none. -/
theorem reflect_calls_on_fields (program : Program) (store : Store) (env : List (Val Nat))
    (head : Nat) (fields : List (Val Nat)) (results : List Result) :
    Derives program (.eval store (fields ++ env) (.call head (fieldVars fields.length)))
        results ↔
      (candidates program head fields.length ≠ [] ∧
        Derives program
          (.alts store ((candidates program head fields.length).map
            fun rule => (rule.body, fields))) results) ∨
      (candidates program head fields.length = [] ∧ results = [(.fail, store)]) := by
  have arguments := eval_fieldVars fields env
  have arity := length_fieldVars fields.length
  constructor
  · intro derived
    cases derived with
    | call nonempty branches =>
        rw [arity] at nonempty branches
        rw [arguments] at branches
        exact Or.inl ⟨nonempty, branches⟩
    | callNone none =>
        rw [arity] at none
        exact Or.inr ⟨none, rfl⟩
  · rintro (⟨nonempty, branches⟩ | ⟨none, rfl⟩)
    · apply Derives.call (by rwa [arity])
      rw [arity, arguments]
      exact branches
    · exact Derives.callNone (by rwa [arity])

/-- A term matched by no listed pattern stays as it is. -/
theorem reflect_unlisted (program : Program) (store : Store) (env : List (Val Nat))
    (term : VExp) :
    ∀ heads : List (Nat × Nat),
      (∀ entry ∈ heads, (term.eval env).matchCon entry.1 entry.2 = none) →
        Derives program (.eval store env (reflect heads term)) [(.ok (term.eval env), store)]
  | [], _ => Derives.ret
  | (head, arity) :: heads, missed =>
      Derives.caseConMiss (missed (head, arity) List.mem_cons_self)
        (reflect_unlisted program store env term heads
          fun entry member => missed entry (List.mem_cons_of_mem _ member))

/-- `run` executes code only: on a built term it leaves the inert residual. -/
theorem run_built_is_inert (program : Program) (store : Store) (env : List (Val Nat))
    (term : VExp) (head : Nat) (fields : List (Val Nat))
    (built : term.eval env = spine head fields) :
    Derives program (.eval store env (.run term))
      [(.ok (.app (.sym unquoteHead) (spine head fields)), store)] := by
  rw [← built]
  exact Derives.runOther fun cell same => spine_ne_code head fields cell (built ▸ same)

/-! ## Controls -/

namespace Controls

/-- The equation `f x = called`, for head `f = 5` and the symbol `called = 99`. -/
def callingProgram : Program := [⟨5, 1, .ret (.sym 99)⟩]

/-- The equation `f x = data f x`: it rebuilds the term it was called on. -/
def rebuildingProgram : Program := [⟨5, 1, data 5 [.ret (.var 0)]⟩]

def outcomes (program : Program) (computation : Comp) : Option (List Outcome) :=
  (run program 100 (.eval Store.empty [] computation)).map fun results => results.map (·.1)

def traced (program : Program) (computation : Comp) : Option (List (Outcome × List Nat)) :=
  (run program 100 (.eval Store.empty [] computation)).map
    fun results => results.map fun result => (result.1, result.2.trace)

def term (head : Nat) (fields : List Nat) : Val Nat :=
  spine head (fields.map Val.sym)

/-- Two alternatives for one field. -/
def twoAnswers : Comp := .choose (.ret (.sym 2)) (.ret (.sym 3))

theorem call_runs_the_equation :
    outcomes callingProgram (.call 5 [.sym 2]) = some [.ok (.sym 99)] := by
  decide +kernel

theorem data_builds_under_the_same_equation :
    outcomes callingProgram (data 5 [.ret (.sym 2)]) = some [.ok (term 5 [2])] := by
  decide +kernel

/-- The alternatives of a field are alternatives of the building occurrence,
in field order. -/
theorem fields_choose_at_build :
    outcomes [] (data 5 [twoAnswers, .ret (.sym 4)]) =
      some [.ok (term 5 [2, 4]), .ok (term 5 [3, 4])] := by
  decide +kernel

/-- The general law at this instance: two answers for the first field, one for
the second. -/
theorem fields_choose_by_the_law :
    Derives [] (.eval Store.empty [] (data 5 [twoAnswers, .ret (.sym 4)]))
      [(.ok (term 5 [2, 4]), Store.empty), (.ok (term 5 [3, 4]), Store.empty)] := by
  have answering : List.Forall₂ (Answers []) [twoAnswers, .ret (.sym 4)]
      [[.sym 2, .sym 3], [.sym 4]] :=
    .cons (answers_choose [] (answers_ret [] rfl) (answers_ret [] rfl))
      (.cons (answers_ret [] rfl) .nil)
  simpa [combinations, term, spine] using data_answers [] Store.empty [] 5 answering

/-- In this calculus a failure is an explicit result: a failing second field
fails once for each answer of the first. -/
theorem failing_field_fails_each_combination :
    outcomes [] (data 5 [twoAnswers, .fail]) = some [.fail, .fail] := by
  decide +kernel

/-- A field's effect happens when the term is built. -/
theorem field_effects_at_build :
    traced [] (data 5 [.emit 11 (.ret (.sym 2))]) = some [(.ok (term 5 [2]), [11])] := by
  decide +kernel

/-- `quote` yields one opaque cell; its choice and effect wait until it runs. -/
theorem quote_defers_the_choice :
    traced [] (.quote (data 5 [.emit 11 twoAnswers])) = some [(.ok (.code 0), [])] ∧
    traced [] (.seq (.quote (data 5 [.emit 11 twoAnswers])) (.run (.var 0))) =
      some [(.ok (term 5 [2]), [11]), (.ok (term 5 [3]), [11])] := by
  decide +kernel

/-- A constructor pattern selects a built term and misses a quoted one. -/
theorem pattern_reads_data_not_code :
    outcomes [] (.seq (data 5 [.ret (.sym 2)])
        (.caseCon (.var 0) 5 1 (.ret (.var 0)) (.ret (.sym 0)))) = some [.ok (.sym 2)] ∧
    outcomes [] (.seq (.quote (data 5 [.ret (.sym 2)]))
        (.caseCon (.var 0) 5 1 (.ret (.var 0)) (.ret (.sym 0)))) = some [.ok (.sym 0)] := by
  decide +kernel

/-- One occurrence with a computed field, a field held as code, and a field of
held syntax. -/
theorem fields_mix_modes :
    traced [] (data 5 [.emit 11 (.ret (.sym 2)), .quote (.emit 12 (.ret (.sym 3))),
        .ret (.sym 4)]) =
      some [(.ok (spine 5 [.sym 2, .code 0, .sym 4]), [11])] := by
  decide +kernel

/-- Without `quote`, every field of `data` runs: both effects happen at build,
in field order. -/
theorem data_alone_evaluates_every_field :
    traced [] (data 5 [.emit 11 (.ret (.sym 2)), .emit 12 (.ret (.sym 3))]) =
      some [(.ok (term 5 [2, 3]), [11, 12])] := by
  decide +kernel

/-- Without `data`, `quote` holds every field: nothing runs until the code does. -/
theorem quote_alone_holds_every_field :
    traced [] (.quote (data 5 [.emit 11 (.ret (.sym 2)), .emit 12 (.ret (.sym 3))])) =
      some [(.ok (.code 0), [])] := by
  decide +kernel

/-- Reflection calls the equation on the built fields; `run` leaves the built
term inert. -/
theorem reflect_calls_and_run_does_not :
    outcomes callingProgram (.seq (data 5 [.ret (.sym 2)]) (reflect [(5, 1)] (.var 0))) =
      some [.ok (.sym 99)] ∧
    outcomes callingProgram (.seq (data 5 [.ret (.sym 2)]) (.run (.var 0))) =
      some [.ok (.app (.sym unquoteHead) (term 5 [2]))] := by
  decide +kernel

/-- A head with no listed equations stays as data under reflection. -/
theorem reflect_leaves_unlisted_heads :
    outcomes [] (.seq (data 6 [.ret (.sym 2)]) (reflect [(5, 1)] (.var 0))) =
      some [.ok (term 6 [2])] := by
  decide +kernel

/-- In the calculus a call of a head without equations fails; `data` builds. -/
theorem call_without_equations_fails :
    outcomes [] (.call 5 [.sym 2]) = some [.fail] ∧
    outcomes [] (data 5 [.ret (.sym 2)]) = some [.ok (term 5 [2])] := by
  decide +kernel

/-- MeTTa's reading of an application: call the head's equations when it has
some, and otherwise build the term. -/
def surface (program : Program) (head : Nat) (fields : List VExp) : Comp :=
  if candidates program head fields.length = [] then data head (fields.map .ret)
  else .call head fields

theorem surface_reading_differs_from_data :
    outcomes callingProgram (surface callingProgram 5 [.sym 2]) = some [.ok (.sym 99)] ∧
    outcomes callingProgram (data 5 [.ret (.sym 2)]) = some [.ok (term 5 [2])] := by
  decide +kernel

/-- A head whose equation rebuilds its term is not told apart from `data`. -/
theorem rebuilding_equation_is_indistinguishable :
    outcomes rebuildingProgram (surface rebuildingProgram 5 [.sym 2]) =
      outcomes rebuildingProgram (data 5 [.ret (.sym 2)]) := by
  decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.PrimeCandidates.Native.DataForm
