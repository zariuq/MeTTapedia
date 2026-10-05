import Mettapedia.Languages.MM0.MeTTa.SpaceClearing
import Mettapedia.Languages.MM0.MeTTa.Data
import Mettapedia.GSLT.Dynamics.MemoizationObserver

/-!
# The retained inference cache

These paths execute the pinned `mm0:infer` body. A hit returns the one
captured answer; repeated occurrences are malformed. A miss runs the actual
uncached call and publishes its answer, including `None`.

The miss lemma composes a child execution; it does not establish the child's
typing contract. Logical cache authorization additionally needs the service's
declaration-scope invariant. Neither follows from handle identity.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.InferenceCache

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst matchAtom)
open Mettapedia.Languages.MeTTa.PeTTa
open SourceEvaluation SourceExecution
open SourcePrimitives (State boolean handleValue)
open NamedSpaces (Handle)

def cell : String := "mm0-inference-cache"

def row (terms context expression value : Atom) : Atom :=
  .expression [terms, context, expression, value]

def query (entries : List Atom) (terms context expression : Atom) : List Atom :=
  SourcePrimitives.query entries
    (.expression [terms, context, expression, .var "value"]) (.var "value")

/-! ## The concrete representation of a coherent cache -/

abbrev Key := Kernel.Context × Kernel.Preterm

def keyQuery (entries : List Atom) (terms : Atom) (key : Key) : List Atom :=
  query entries terms (Data.context key.1) (Data.preterm key.2)

/-- The proof-level partial map read from the concrete ordered queries.
Uniqueness remains a separate obligation; taking the head does not erase it. -/
def table (entries : List Atom) (terms : Atom) :
    Mettapedia.GSLT.Dynamics.MemoizationObserver.Table Key Atom :=
  fun key => (keyQuery entries terms key).head?

def observation (signature : Kernel.TermSignature) (key : Key) : Atom :=
  Data.inferred (Kernel.Preterm.infer signature key.1 key.2)

/-- Cache validity in one frozen term signature. The term-table value is
still part of every concrete key. Declaration transitions must establish the
scope separately; this property is not inferred from handle equality. -/
structure Valid (signature : Kernel.TermSignature) (terms : Atom) (entries : List Atom) : Prop where
  unambiguous : ∀ key, (keyQuery entries terms key).length ≤ 1
  coherent : Mettapedia.GSLT.Dynamics.MemoizationObserver.Coherent id
    (observation signature) (table entries terms)

theorem key_query_one_row (terms : Atom) (literal : SourceProgram.Literal terms)
    (wanted recorded : Key) (value : Atom) :
    keyQuery [row terms (Data.context recorded.1) (Data.preterm recorded.2) value] terms wanted =
      if wanted = recorded then [value] else [] := by
  simp only [keyQuery, query, row, SourcePrimitives.query, List.filterMap_cons, List.filterMap_nil]
  rw [SourceProgram.matchValue_expression_of_not_cons [] _ _ (by intro first rest; simp)]
  simp only [SourceProgram.matchValue.matchValues,
    SourceProgram.matchValue_literal literal,
    SourceProgram.matchValue_literal (Data.context_literal wanted.1),
    SourceProgram.matchValue_literal (Data.preterm_literal wanted.2), ↓reduceIte]
  by_cases sameContext : wanted.1 = recorded.1 <;>
    by_cases sameExpression : wanted.2 = recorded.2 <;>
    simp [sameContext, sameExpression, Data.context_injective.eq_iff,
      Data.preterm_injective.eq_iff, Prod.ext_iff,
      SourceProgram.matchValue, matchAtom, applySubst, Subst.lookup]

theorem key_query_append (entries : List Atom) (terms : Atom)
    (literal : SourceProgram.Literal terms) (wanted recorded : Key) (value : Atom) :
    keyQuery (entries ++ [row terms (Data.context recorded.1) (Data.preterm recorded.2) value])
        terms wanted =
      keyQuery entries terms wanted ++ (if wanted = recorded then [value] else []) := by
  change query (entries ++ _) terms _ _ = _
  rw [query, SourcePrimitives.query_append]
  exact congrArg (keyQuery entries terms wanted ++ ·) (key_query_one_row terms literal wanted recorded value)

theorem empty_valid (signature : Kernel.TermSignature) (terms : Atom) : Valid signature terms [] := by
  constructor
  · intro key; simp [keyQuery, query, SourcePrimitives.query]
  · intro key value stored point same
    simp [table, keyQuery, query, SourcePrimitives.query] at stored

theorem Valid.query_cases {signature : Kernel.TermSignature} {terms : Atom} {entries : List Atom}
    (valid : Valid signature terms entries) (key : Key) :
    keyQuery entries terms key = [] ∨
      keyQuery entries terms key = [observation signature key] := by
  have bounded := valid.unambiguous key
  cases answers : keyQuery entries terms key with
  | nil => exact .inl rfl
  | cons first rest =>
      cases rest with
      | nil =>
          have authorized : observation signature key = first :=
            valid.coherent key first (by simp [table, answers]) key rfl
          exact .inr (congrArg List.singleton authorized.symm)
      | cons second rest => simp [answers] at bounded

/-- Recording the computed answer after a miss is the shared coherent-table
operation, realized by appending a concrete row. -/
theorem valid_append {signature : Kernel.TermSignature} {terms : Atom} {entries : List Atom}
    (valid : Valid signature terms entries) (literal : SourceProgram.Literal terms) (recorded : Key)
    (missing : keyQuery entries terms recorded = []) :
    Valid signature terms
      (entries ++ [row terms (Data.context recorded.1) (Data.preterm recorded.2)
        (observation signature recorded)]) := by
  have projected : table
      (entries ++ [row terms (Data.context recorded.1) (Data.preterm recorded.2)
        (observation signature recorded)]) terms =
      Mettapedia.GSLT.Dynamics.MemoizationObserver.store id (observation signature)
        (table entries terms) recorded := by
    funext wanted
    unfold table
    rw [key_query_append entries terms literal wanted recorded]
    by_cases same : wanted = recorded
    · subst wanted
      simp [missing, Mettapedia.GSLT.Dynamics.MemoizationObserver.store]
    · simp [same, Mettapedia.GSLT.Dynamics.MemoizationObserver.store]
  constructor
  · intro wanted
    rw [key_query_append entries terms literal wanted recorded]
    by_cases same : wanted = recorded
    · subst wanted; simp [missing]
    · simpa [same] using valid.unambiguous wanted
  · rw [projected]
    exact Mettapedia.GSLT.Dynamics.MemoizationObserver.coherent_store_of_soundKey
      (fun first second same => congrArg (observation signature) same) valid.coherent recorded

/-- The concrete cache is allocated and belongs to the current checking
scope. Linking the supplied signature to the term table is a separate read
invariant. -/
def Ready (signature : Kernel.TermSignature) (terms : Atom) (cache : Handle) (state : State) : Prop :=
  state.cells cell = some (handleValue cache) ∧
    ∃ entries, state.read cache = some entries ∧ Valid signature terms entries

def storedQuery (state : State) (cache : Handle) (terms : Atom) (key : Key) : Option (List Atom) :=
  (state.read cache).map fun entries => keyQuery entries terms key

/-- Only the cache changes, and no expression larger than `bound` acquires
or loses an entry. The latter is needed when a child computes beneath an
uncached parent. -/
structure Frame (cache : Handle) (terms : Atom) (bound : Nat) (before after : State) : Prop where
  cells : after.cells = before.cells
  other : ∀ handle, handle ≠ cache → after.read handle = before.read handle
  larger : ∀ key, bound < sizeOf key.2 → storedQuery after cache terms key = storedQuery before cache terms key

theorem Frame.refl (cache : Handle) (terms : Atom) (bound : Nat) (state : State) :
    Frame cache terms bound state state := ⟨rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem Frame.weaken {cache : Handle} {terms : Atom} {first second : Nat} {before after : State}
    (frame : Frame cache terms first before after) (bounded : first ≤ second) :
    Frame cache terms second before after :=
  ⟨frame.cells, frame.other, fun key larger => frame.larger key (by omega)⟩

theorem Frame.trans {cache : Handle} {terms : Atom} {bound : Nat} {before middle after : State}
    (first : Frame cache terms bound before middle) (second : Frame cache terms bound middle after) :
    Frame cache terms bound before after := by
  constructor
  · exact second.cells.trans first.cells
  · intro handle different; rw [second.other handle different, first.other handle different]
  · intro key larger; rw [second.larger key larger, first.larger key larger]

theorem record_frame {signature : Kernel.TermSignature} {cache : Handle} {terms : Atom}
    {before after : State} (key : Key)
    (literal : SourceProgram.Literal terms)
    (inserted : SourcePrimitives.insert before cache
      (row terms (Data.context key.1) (Data.preterm key.2) (observation signature key)) = some after) :
    Frame cache terms (sizeOf key.2) before after := by
  constructor
  · exact SourcePrimitives.insert_preserves_cells inserted
  · intro handle different; exact SourcePrimitives.insert_read_other inserted different
  · intro wanted larger
    obtain ⟨entries, readBefore, readAfter⟩ := SourcePrimitives.insert_reads_back inserted
    have different : wanted ≠ key := by intro same; subst wanted; omega
    simp only [storedQuery, readBefore, readAfter, Option.map_some]
    rw [key_query_append entries terms literal wanted key, if_neg different, List.append_nil]

theorem ready_record {signature : Kernel.TermSignature} {terms : Atom} {cache : Handle}
    {before after : State} (ready : Ready signature terms cache before)
    (literal : SourceProgram.Literal terms) (key : Key)
    (missing : storedQuery before cache terms key = some [])
    (inserted : SourcePrimitives.insert before cache
      (row terms (Data.context key.1) (Data.preterm key.2) (observation signature key)) = some after) :
    Ready signature terms cache after := by
  obtain ⟨current, entries, allocated, valid⟩ := ready
  obtain ⟨old, readBefore, readAfter⟩ := SourcePrimitives.insert_reads_back inserted
  have same : old = entries := Option.some.inj (readBefore.symm.trans allocated)
  subst old
  have absent : keyQuery entries terms key = [] := by simpa [storedQuery, allocated] using missing
  refine ⟨?_, _, readAfter, valid_append valid literal key absent⟩
  rw [SourcePrimitives.insert_preserves_cells inserted]
  exact current

private def environment (terms context expression : Atom) : Subst :=
  [("expression", expression), ("ctx", context), ("terms", terms)]

private def cacheEnvironment (handle : Handle) (terms context expression : Atom) : Subst :=
  ("cache", handleValue handle) :: environment terms context expression

private def queryEnvironment (handle : Handle) (terms context expression : Atom)
    (answers : List Atom) : Subst :=
  ("found", .expression answers) :: cacheEnvironment handle terms context expression

private def queriedBody : Atom :=
  match cachedInferEquation.body with
  | .expression [_, _, _, body] => body
  | _ => .expression []

private def foundBody : Atom :=
  match queriedBody with
  | .expression [_, _, _, body] => body
  | _ => .expression []

private def cases : SourceProgram.Cases :=
  match foundBody with
  | .expression [_, _, .expression rows] => (readCases rows).getD []
  | _ => []

private def missBody : Atom := (cases[0]'(by decide)).2

private def publishBody : Atom :=
  match missBody with
  | .expression [_, _, _, body] => body
  | _ => .expression []

theorem cache_clause (terms context expression : Atom) :
    clauses program "mm0:infer" [terms, context, expression] =
      [.evaluate (environment terms context expression) cachedInferEquation.body] := by
  rw [clauses_use_only_the_named_equations, cached_infer_equation_is_unique]
  simp [cached_infer_formals, SourceProgram.matchValue, SourceProgram.matchValue.matchValues,
    matchAtom, Subst.lookup, environment]

private theorem body_shape :
    cachedInferEquation.body = .expression [.symbol "let", .var "cache",
      .expression [.symbol "get-state", .symbol "mm0-inference-cache"], queriedBody] := by decide

private theorem queried_body_shape :
    queriedBody = .expression [.symbol "let", .var "found",
      .expression [.symbol "collapse", .expression [.symbol "match", .var "cache",
        .expression [.var "terms", .var "ctx", .var "expression", .var "value"],
        .var "value"]], foundBody] := by decide

private theorem found_body_shape :
    foundBody = .expression [.symbol "case", .var "found",
      .expression (cases.map fun entry => .expression [entry.1, entry.2])] := by decide

private theorem cases_shape :
    cases = [(.expression [], missBody), (.expression [.var "value"], .var "value"),
      (.var "bad", .symbol "MM0:Malformed")] := by decide

private theorem miss_body_shape :
    missBody = .expression [.symbol "let", .var "value",
      .expression [.symbol "mm0:infer-uncached", .var "terms", .var "ctx", .var "expression"],
      publishBody] := by decide

private theorem publish_body_shape :
    publishBody = .expression [.symbol "let", .var "done",
      .expression [.symbol "add-atom", .var "cache",
        .expression [.var "terms", .var "ctx", .var "expression", .var "value"]],
      .var "value"] := by decide

private theorem cache_cell_returns (state : State) (handle : Handle)
    (terms context expression : Atom)
    (current : state.cells cell = some (handleValue handle)) :
    PureReturns program (environment terms context expression) state
      (.expression [.symbol "get-state", .symbol "mm0-inference-cache"])
      state (handleValue handle) := by
  apply native_unary_call_returns program (environment terms context expression)
    state state state "get-state" (.symbol "mm0-inference-cache") _ _
    (by decide) (by decide) (by decide)
    (symbol_returns program _ state "mm0-inference-cache") _ (by decide)
  simpa only [SourcePrimitives.apply, cell, current] using
    (show SourcePrimitives.apply state "get-state" [.symbol cell] =
      .ok (state, [handleValue handle]) by simp [SourcePrimitives.apply, current])

private theorem found_returns (state : State) (handle : Handle) (entries : List Atom)
    (terms context expression : Atom) (allocated : state.read handle = some entries) :
    PureReturns program (cacheEnvironment handle terms context expression) state
      (.expression [.symbol "collapse", .expression [.symbol "match", .var "cache",
        .expression [.var "terms", .var "ctx", .var "expression", .var "value"],
        .var "value"]]) state (.expression (query entries terms context expression)) := by
  apply match_collapse_returns program (cacheEnvironment handle terms context expression)
    state state "cache" _ _ (query entries terms context expression)
  simp [cacheEnvironment, environment, applySubst, applySubst.applySubstList,
    Subst.lookup, SourcePrimitives.apply, allocated, query]

private theorem body_returns_from_query (before after : State) (handle : Handle)
    (entries : List Atom) (terms context expression answer : Atom)
    (current : before.cells cell = some (handleValue handle))
    (allocated : before.read handle = some entries)
    (branch : PureReturns program
      (queryEnvironment handle terms context expression (query entries terms context expression))
      before foundBody after answer) :
    PureReturns program (environment terms context expression) before
      cachedInferEquation.body after answer := by
  rw [body_shape]
  apply let_returns program (environment terms context expression)
    (cacheEnvironment handle terms context expression)
    before before after (.var "cache") _ _ (handleValue handle) answer
    (cache_cell_returns before handle terms context expression current) _ _
  · simp [SourceProgram.matchValue, matchAtom, environment, Subst.lookup, cacheEnvironment]
  · rw [queried_body_shape]
    apply let_returns program (cacheEnvironment handle terms context expression)
      (queryEnvironment handle terms context expression (query entries terms context expression))
      before before after (.var "found") _ _ _ answer
      (found_returns before handle entries terms context expression allocated) _ branch
    simp [SourceProgram.matchValue, matchAtom, cacheEnvironment, environment,
      Subst.lookup, queryEnvironment]

theorem hit_body_returns (state : State) (handle : Handle) (entries : List Atom)
    (terms context expression value : Atom)
    (current : state.cells cell = some (handleValue handle))
    (allocated : state.read handle = some entries)
    (one : query entries terms context expression = [value]) :
    PureReturns program (environment terms context expression) state
      cachedInferEquation.body state value := by
  apply body_returns_from_query state state handle entries terms context expression value current allocated
  rw [one, found_body_shape]
  let bindings := queryEnvironment handle terms context expression [value]
  let bound := ("value", value) :: bindings
  apply case_returns program bindings bound state state state (.var "found")
    (.expression [value]) (.var "value") value _ cases (read_cases_encoded cases)
  · simpa [bindings, queryEnvironment, applySubst, Subst.lookup] using
      variable_returns program bindings state "found"
  · simp [cases_shape, SourceProgram.selectCase, SourceProgram.matchValue,
      SourceProgram.matchValue.matchValues, matchAtom, bindings, bound,
      queryEnvironment, cacheEnvironment, environment, Subst.lookup]
  · simpa [bound, applySubst, Subst.lookup] using variable_returns program bound state "value"

theorem duplicate_body_returns (state : State) (handle : Handle) (entries : List Atom)
    (terms context expression first second : Atom) (rest : List Atom)
    (current : state.cells cell = some (handleValue handle))
    (allocated : state.read handle = some entries)
    (many : query entries terms context expression = first :: second :: rest) :
    PureReturns program (environment terms context expression) state
      cachedInferEquation.body state (.symbol "MM0:Malformed") := by
  apply body_returns_from_query state state handle entries terms context expression _ current allocated
  rw [many, found_body_shape]
  let bindings := queryEnvironment handle terms context expression (first :: second :: rest)
  let bound := ("bad", .expression (first :: second :: rest)) :: bindings
  apply case_returns program bindings bound state state state (.var "found")
    (.expression (first :: second :: rest)) (.symbol "MM0:Malformed") _ _ cases
    (read_cases_encoded cases)
  · simpa [bindings, queryEnvironment, applySubst, Subst.lookup] using
      variable_returns program bindings state "found"
  · simp [cases_shape, SourceProgram.selectCase, SourceProgram.matchValue,
      SourceProgram.matchValue.matchValues, matchAtom, bindings, bound,
      queryEnvironment, cacheEnvironment, environment, Subst.lookup]
  · exact symbol_returns program bound state "MM0:Malformed"

private theorem publish_returns (before after : State) (handle : Handle)
    (terms context expression value : Atom)
    (inserted : SourcePrimitives.insert before handle (row terms context expression value) = some after) :
    PureReturns program
      (("value", value) :: queryEnvironment handle terms context expression [])
      before publishBody after value := by
  let bindings := ("value", value) :: queryEnvironment handle terms context expression []
  rw [publish_body_shape]
  apply let_returns program bindings (("done", boolean true) :: bindings)
    before after after (.var "done") _ _ (boolean true) value _ _ _
  · apply call_returns program bindings before after "add-atom" _ _ (by decide) _ (by decide)
    have insertedPath := native_function_arguments_return program bindings before after "add-atom"
      [handleValue handle, row terms context expression value] 2 (boolean true)
      (by decide) (by decide) (by simp [SourcePrimitives.apply, inserted])
    have last := raw_argument_answers program bindings before after "add-atom"
      (.expression [.var "terms", .var "ctx", .var "expression", .var "value"])
      [] [handleValue handle] 1 [boolean true] (by decide)
      (by simpa [bindings, queryEnvironment, cacheEnvironment, environment, row,
        applySubst, applySubst.applySubstList, Subst.lookup] using insertedPath)
    exact evaluated_argument_returns program bindings before before after (.function "add-atom")
      (.var "cache") (handleValue handle) _ _ [] 0 (by decide)
      (by simpa [bindings, queryEnvironment, cacheEnvironment, applySubst, Subst.lookup] using
        variable_returns program bindings before "cache") last
  · simp [SourceProgram.matchValue, matchAtom, bindings, queryEnvironment, cacheEnvironment,
      environment, Subst.lookup]
  · simpa [bindings, applySubst, Subst.lookup] using
      variable_returns program (("done", boolean true) :: bindings) after "value"

/-- This is the actual miss branch with its child execution left explicit.
The inference-family proof must discharge that child contract. -/
theorem miss_body_returns (before middle after : State) (handle : Handle) (entries : List Atom)
    (terms context expression value : Atom)
    (current : before.cells cell = some (handleValue handle))
    (allocated : before.read handle = some entries)
    (empty : query entries terms context expression = [])
    (computed : PureReturns program (queryEnvironment handle terms context expression []) before
      (.expression [.symbol "mm0:infer-uncached", .var "terms", .var "ctx", .var "expression"])
      middle value)
    (inserted : SourcePrimitives.insert middle handle (row terms context expression value) = some after) :
    PureReturns program (environment terms context expression) before
      cachedInferEquation.body after value := by
  apply body_returns_from_query before after handle entries terms context expression value current allocated
  rw [empty, found_body_shape]
  let bindings := queryEnvironment handle terms context expression []
  apply case_returns program bindings bindings before before after (.var "found")
    (.expression []) missBody value _ cases (read_cases_encoded cases)
  · simpa [bindings, queryEnvironment, applySubst, Subst.lookup] using
      variable_returns program bindings before "found"
  · simp [cases_shape, SourceProgram.selectCase, SourceProgram.matchValue,
      SourceProgram.matchValue.matchValues, bindings]
  · rw [miss_body_shape]
    apply let_returns program bindings (("value", value) :: bindings)
      before middle after (.var "value") _ _ value value computed _ _
    · simp [SourceProgram.matchValue, matchAtom, bindings, queryEnvironment,
        cacheEnvironment, environment, Subst.lookup]
    · exact publish_returns middle after handle terms context expression value inserted

theorem hit_returns (bindings : Subst) (state : State) (handle : Handle) (entries : List Atom)
    (terms context expression value : Atom) (termsName contextName expressionName : String)
    (current : state.cells cell = some (handleValue handle))
    (allocated : state.read handle = some entries)
    (one : query entries terms context expression = [value])
    (termsCaptured : applySubst bindings (.var termsName) = terms)
    (contextCaptured : applySubst bindings (.var contextName) = context)
    (expressionCaptured : applySubst bindings (.var expressionName) = expression) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:infer", .var termsName, .var contextName, .var expressionName])
      state value := by
  apply authored_variable_call_returns program bindings (environment terms context expression)
    state state "mm0:infer" [termsName, contextName, expressionName] cachedInferEquation.body value
    (by decide) (by decide) (by decide) _
    (hit_body_returns state handle entries terms context expression value current allocated one) (by decide)
  simpa [termsCaptured, contextCaptured, expressionCaptured] using cache_clause terms context expression

/-- Compose one uncached computation with the actual cache lookup and
publication. The supplied child path is a local composition premise; the
recursive inference proof must construct it. -/
theorem settle (signature : Kernel.TermSignature) (terms : Atom) (cache : Handle)
    (literal : SourceProgram.Literal terms) (key : Key) (before : State)
    (ready : Ready signature terms cache before)
    (computed : ∃ middle bound,
      (∀ bindings termsName contextName expressionName,
        applySubst bindings (.var termsName) = terms →
        applySubst bindings (.var contextName) = Data.context key.1 →
        applySubst bindings (.var expressionName) = Data.preterm key.2 →
        PureReturns program bindings before
          (.expression [.symbol "mm0:infer-uncached", .var termsName, .var contextName,
            .var expressionName]) middle (observation signature key)) ∧
      Ready signature terms cache middle ∧ Frame cache terms bound before middle ∧ bound < sizeOf key.2) :
    ∃ after,
      (∀ bindings termsName contextName expressionName,
        applySubst bindings (.var termsName) = terms →
        applySubst bindings (.var contextName) = Data.context key.1 →
        applySubst bindings (.var expressionName) = Data.preterm key.2 →
        PureReturns program bindings before
          (.expression [.symbol "mm0:infer", .var termsName, .var contextName, .var expressionName])
          after (observation signature key)) ∧
      Ready signature terms cache after ∧ Frame cache terms (sizeOf key.2) before after := by
  obtain ⟨current, entries, allocated, valid⟩ := ready
  rcases valid.query_cases key with missing | found
  · obtain ⟨middle, bound, child, readyMiddle, frame, smaller⟩ := computed
    have stillMissing : storedQuery middle cache terms key = some [] := by
      rw [frame.larger key smaller]
      simp [storedQuery, allocated, missing]
    obtain ⟨middleEntries, middleAllocated, _⟩ := readyMiddle.2
    obtain ⟨after, inserted⟩ := SourcePrimitives.insert_exists_of_read_some middleAllocated
      (row terms (Data.context key.1) (Data.preterm key.2) (observation signature key))
    refine ⟨after, ?_, ready_record readyMiddle literal key stillMissing inserted,
      (frame.weaken (Nat.le_of_lt smaller)).trans (record_frame key literal inserted)⟩
    intro bindings termsName contextName expressionName capturedTerms capturedContext capturedExpression
    apply authored_variable_call_returns program bindings
      (environment terms (Data.context key.1) (Data.preterm key.2)) before after
      "mm0:infer" [termsName, contextName, expressionName] cachedInferEquation.body _
      (by decide) (by decide) (by decide) _ _ (by decide)
    · simpa [capturedTerms, capturedContext, capturedExpression] using
        cache_clause terms (Data.context key.1) (Data.preterm key.2)
    · exact miss_body_returns before middle after cache entries terms
        (Data.context key.1) (Data.preterm key.2) (observation signature key) current allocated missing
        (child (queryEnvironment cache terms (Data.context key.1) (Data.preterm key.2) [])
          "terms" "ctx" "expression"
          (by simp [queryEnvironment, cacheEnvironment, environment, applySubst, Subst.lookup])
          (by simp [queryEnvironment, cacheEnvironment, environment, applySubst, Subst.lookup])
          (by simp [queryEnvironment, cacheEnvironment, environment, applySubst, Subst.lookup])) inserted
  · refine ⟨before, ?_, ⟨current, entries, allocated, valid⟩, Frame.refl cache terms _ before⟩
    intro bindings termsName contextName expressionName capturedTerms capturedContext capturedExpression
    exact hit_returns bindings before cache entries terms (Data.context key.1) (Data.preterm key.2)
      (observation signature key) termsName contextName expressionName current allocated found
      capturedTerms capturedContext capturedExpression

/-- Cached refusal values are returned as data, with no logical acceptance. -/
theorem negative_hit_returns (bindings : Subst) (state : State) (handle : Handle)
    (entries : List Atom) (terms context expression : Atom)
    (termsName contextName expressionName : String)
    (current : state.cells cell = some (handleValue handle))
    (allocated : state.read handle = some entries)
    (one : query entries terms context expression = [.symbol "None"])
    (termsCaptured : applySubst bindings (.var termsName) = terms)
    (contextCaptured : applySubst bindings (.var contextName) = context)
    (expressionCaptured : applySubst bindings (.var expressionName) = expression) :
    PureReturns program bindings state
      (.expression [.symbol "mm0:infer", .var termsName, .var contextName, .var expressionName])
      state (.symbol "None") :=
  hit_returns bindings state handle entries terms context expression (.symbol "None")
    termsName contextName expressionName current allocated one termsCaptured contextCaptured expressionCaptured

end Mettapedia.Languages.MM0.MeTTa.InferenceCache
