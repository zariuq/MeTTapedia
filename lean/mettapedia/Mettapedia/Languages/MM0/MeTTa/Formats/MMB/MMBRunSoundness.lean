import Mettapedia.Languages.MM0.MeTTa.Formats.MMB.MMBStateScopeSoundness

/-!
# MMB run preservation from available declarations

Store preservation follows the retained execution, with a fixed context whose
dummies occur in actual proof-command order. Term-table entries must decode to
declarations independently available in the existing kernel signature.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.MMBRunSoundness

open Formats.MMB Kernel
open MMBMachineSoundness MMBDependencySoundness MMBInitializationSoundness MMBStateScopeSoundness

theorem termDecl_fields (terms : List TermEntry) (entry : TermEntry)
    (declaration : TermDecl) (body : Option Definition.Body)
    (decoded : Statements.termDecl terms entry = some (declaration, body)) :
    declaration.arguments = Statements.context entry.args ∧ declaration.resultSort = entry.sort ∧
      declaration.dependencies = entry.ret.deps.image
        (fun rank => (Statements.boundPositions entry.args).getD rank rank) := by
  unfold Statements.termDecl at decoded
  split at decoded
  · cases Option.some.inj decoded
    exact ⟨rfl, rfl, rfl⟩
  · obtain ⟨value, _, checked⟩ := Option.bind_eq_some_iff.mp decoded
    rcases value with ⟨expression, state, remaining⟩
    change (if remaining ≠ [] then none else some
      (⟨Statements.context entry.args, entry.sort,
        entry.ret.deps.image (fun rank => (Statements.boundPositions entry.args).getD rank rank)⟩,
        some (⟨state.dummies, expression⟩ : Definition.Body))) = some (declaration, body) at checked
    split at checked
    · cases checked
    · cases Option.some.inj checked
      exact ⟨rfl, rfl, rfl⟩

theorem dummySorts_cons (command : ProofCmd) (commands : List ProofCmd) :
    dummySorts (command :: commands) = dummySorts [command] ++ dummySorts commands :=
  dummySorts_append [command] commands

theorem step_preserves_fixed_store (signature : TermSignature) (tables : Tables)
    (available : ∀ (term : Nat) (entry : TermEntry), tables.terms[term]? = some entry →
      ∃ declaration body, Statements.termDecl tables.terms entry = some (declaration, body) ∧ signature term = some declaration)
    (args : List ExprType) (seen : List Nat) (remaining : List ProofCmd)
    (command : ProofCmd) (before after : Formats.MMB.State)
    (boundCounter : before.nextBound = (Statements.boundPositions args).length + seen.length)
    (variableCounter : before.varCount = args.length + seen.length)
    (typed : TypedStore signature
      (Statements.context args ++ (seen ++ dummySorts (command :: remaining)).map Binder.bound) before.store)
    (ranked : RankedStore
      (Statements.context args ++ (seen ++ dummySorts (command :: remaining)).map Binder.bound) before.store)
    (executed : step tables .assertion before command = some after) :
    let context := Statements.context args ++ (seen ++ dummySorts (command :: remaining)).map Binder.bound
    TypedStore signature context after.store ∧ RankedStore context after.store := by
  dsimp only
  cases command with
  | term term =>
      have sourceRead := executed
      change stepTerm tables .assertion before term false = some after at sourceRead
      unfold stepTerm at sourceRead
      obtain ⟨entry, entryRead, _⟩ := Option.bind_eq_some_iff.mp sourceRead
      obtain ⟨declaration, body, decoded, known⟩ := available term entry entryRead
      have fields := termDecl_fields tables.terms entry declaration body decoded
      exact ⟨stepTerm_preserves_typing signature _ tables .assertion before after term false entry declaration typed
        entryRead known fields.1 fields.2.1 executed,
        stepTerm_preserves_ranked_support _ tables before after term false entry ranked entryRead executed⟩
  | termSave term =>
      have sourceRead := executed
      change stepTerm tables .assertion before term true = some after at sourceRead
      unfold stepTerm at sourceRead
      obtain ⟨entry, entryRead, _⟩ := Option.bind_eq_some_iff.mp sourceRead
      obtain ⟨declaration, body, decoded, known⟩ := available term entry entryRead
      have fields := termDecl_fields tables.terms entry declaration body decoded
      exact ⟨stepTerm_preserves_typing signature _ tables .assertion before after term true entry declaration typed
        entryRead known fields.1 fields.2.1 executed,
        stepTerm_preserves_ranked_support _ tables before after term true entry ranked entryRead executed⟩
  | dummy sort =>
      obtain ⟨_, _, _, _, same⟩ := step_dummy_shape tables .assertion before after sort executed
      rw [same]
      have position := fixed_dummy_position args seen (dummySorts remaining) sort
      dsimp only at position
      have history : dummySorts (.dummy sort :: remaining) = sort :: dummySorts remaining := rfl
      have lookup : (Statements.context args ++ (seen ++ dummySorts (.dummy sort :: remaining)).map Binder.bound)[before.varCount]? =
          some (.bound sort) := by simpa only [history, variableCounter] using position.1
      have rankLookup : (Soundness.rankPositions
          (Statements.context args ++ (seen ++ dummySorts (.dummy sort :: remaining)).map Binder.bound)).getD
          before.nextBound before.nextBound = before.varCount := by
        simpa only [history, boundCounter, variableCounter] using position.2.1
      have rankBound : before.nextBound < (Soundness.rankPositions
          (Statements.context args ++ (seen ++ dummySorts (.dummy sort :: remaining)).map Binder.bound)).length := by
        simpa only [history, boundCounter] using position.2.2
      exact ⟨allocate_bound_variable_typed signature _ before sort typed lookup,
        allocate_bound_variable_ranked _ before sort ranked lookup rankLookup rankBound⟩
  | ref _ | thm _ | thmSave _ | hyp | conv | refl | symm | cong | unfold | convCut | convSave | save =>
      have unchanged := step_nonallocating_keeps_store tables .assertion before after _
        (by intro; simp) (by intro; simp) (by intro; simp) executed
      simpa only [unchanged] using And.intro typed ranked

theorem run_preserves_fixed_store (signature : TermSignature) (tables : Tables)
    (available : ∀ (term : Nat) (entry : TermEntry), tables.terms[term]? = some entry →
      ∃ declaration body, Statements.termDecl tables.terms entry = some (declaration, body) ∧ signature term = some declaration)
    (args : List ExprType) (seen : List Nat) (commands : List ProofCmd) (before after : Formats.MMB.State)
    (boundCounter : before.nextBound = (Statements.boundPositions args).length + seen.length)
    (variableCounter : before.varCount = args.length + seen.length)
    (typed : TypedStore signature (Statements.context args ++ (seen ++ dummySorts commands).map Binder.bound) before.store)
    (ranked : RankedStore (Statements.context args ++ (seen ++ dummySorts commands).map Binder.bound) before.store)
    (executed : run tables .assertion before commands = some after) :
    let context := Statements.context args ++ (seen ++ dummySorts commands).map Binder.bound
    TypedStore signature context after.store ∧ RankedStore context after.store := by
  dsimp only
  induction commands generalizing seen before with
  | nil =>
      cases Option.some.inj executed
      exact ⟨typed, ranked⟩
  | cons command commands ih =>
      obtain ⟨middle, advanced, continued⟩ := Option.bind_eq_some_iff.mp executed
      have preserved := step_preserves_fixed_store signature tables available args seen commands command before middle
        boundCounter variableCounter typed ranked advanced
      have counters := step_counters tables .assertion before middle command advanced
      have nextBound : middle.nextBound = (Statements.boundPositions args).length +
          (seen ++ dummySorts [command]).length := by
        rw [counters.1, boundCounter, List.length_append, Nat.add_assoc]
      have varCount : middle.varCount = args.length + (seen ++ dummySorts [command]).length := by
        rw [counters.2, variableCounter, List.length_append, Nat.add_assoc]
      have sameContext : Statements.context args ++ (seen ++ dummySorts (command :: commands)).map Binder.bound =
          Statements.context args ++ ((seen ++ dummySorts [command]) ++ dummySorts commands).map Binder.bound := by
        rw [dummySorts_cons, List.append_assoc]
      rw [sameContext] at preserved ⊢
      exact ih (seen ++ dummySorts [command]) middle nextBound varCount preserved.1 preserved.2 continued

theorem run_initialized_fixed_store (signature : TermSignature) (tables : Tables)
    (available : ∀ (term : Nat) (entry : TermEntry), tables.terms[term]? = some entry →
      ∃ declaration body, Statements.termDecl tables.terms entry = some (declaration, body) ∧ signature term = some declaration)
    (args : List ExprType) (commands : List ProofCmd) (loaded after : Formats.MMB.State)
    (initialized : loadArgs tables.sorts args = some loaded)
    (executed : run tables .assertion loaded commands = some after) :
    let context := Statements.context args ++ (dummySorts commands).map Binder.bound
    TypedStore signature context after.store ∧ RankedStore context after.store := by
  obtain ⟨_, _, _, _, variableCount, boundCount⟩ := MMBExecution.loadArgs_variable_shape tables.sorts args loaded initialized
  have initial := loadArgs_initial_fixed_context signature tables.sorts args (dummySorts commands) loaded initialized
  exact run_preserves_fixed_store signature tables available args [] commands loaded after (by simpa using boundCount)
    (by simpa using variableCount) initial.1 initial.2 executed

theorem statement_original_hypotheses_of_run (signature : TermSignature) (tables : Tables)
    (available : ∀ (term : Nat) (entry : TermEntry), tables.terms[term]? = some entry →
      ∃ declaration body, Statements.termDecl tables.terms entry = some (declaration, body) ∧ signature term = some declaration)
    (entry : ThmEntry) (declaration : TheoremDecl) (commands : List ProofCmd)
    (loaded finalState : Formats.MMB.State) (conclusion : Nat) (unified : Unifier)
    (initialized : loadArgs tables.sorts entry.args = some loaded)
    (executed : run tables .assertion loaded commands = some finalState)
    (arities : ∀ term termDeclaration, signature term = some termDeclaration →
      Statements.arityOf tables.terms term = some termDeclaration.arguments.length)
    (declared : Statements.theoremDecl tables.terms entry = some declaration)
    (accepted : unifyRun finalState.store .statement
      ⟨[conclusion], (List.range entry.args.length).map (·, false), [], finalState.hyps⟩ entry.unify = some unified) :
    finalState.hyps.reverse.mapM (Soundness.decode finalState.store) = some declaration.hypotheses := by
  have typed := (run_initialized_fixed_store signature tables available entry.args commands loaded finalState initialized executed).1
  exact unify_statement_original_hypotheses signature _ finalState.store typed tables.terms entry declaration arities declared
    (run_initialized_public_roots tables .assertion entry.args loaded finalState commands initialized executed)
    conclusion finalState.hyps unified accepted

theorem step_hyp_preserves_scope_of_run (signature : TermSignature) (definitions : Definition.Signature)
    (theorems : TheoremSignature) (tables : Tables)
    (available : ∀ (term : Nat) (entry : TermEntry), tables.terms[term]? = some entry →
      ∃ declaration body, Statements.termDecl tables.terms entry = some (declaration, body) ∧ signature term = some declaration)
    (entry : ThmEntry) (declaration : TheoremDecl) (hypotheses : List Preterm)
    (commands remaining : List ProofCmd) (loaded before after finalState : Formats.MMB.State)
    (conclusion : Nat) (unified : Unifier)
    (initialized : loadArgs tables.sorts entry.args = some loaded)
    (executed : run tables .assertion loaded commands = some finalState)
    (arities : ∀ term termDeclaration, signature term = some termDeclaration →
      Statements.arityOf tables.terms term = some termDeclaration.arguments.length)
    (declared : Statements.theoremDecl tables.terms entry = some declaration)
    (hypothesesAgree : declaration.hypotheses = hypotheses)
    (accepted : unifyRun finalState.store .statement
      ⟨[conclusion], (List.range entry.args.length).map (·, false), [], finalState.hyps⟩ entry.unify = some unified)
    (typed : TypedStore signature (Statements.context entry.args ++ (dummySorts commands).map Binder.bound) before.store)
    (ranked : RankedStore (Statements.context entry.args ++ (dummySorts commands).map Binder.bound) before.store)
    (stack : StackSound signature definitions theorems
      (Statements.context entry.args ++ (dummySorts commands).map Binder.bound) hypotheses before.store before.stack)
    (heap : HeapSound signature definitions theorems
      (Statements.context entry.args ++ (dummySorts commands).map Binder.bound) hypotheses before.store before.heap)
    (hypExecuted : step tables .assertion before .hyp = some after)
    (continued : run tables .assertion after remaining = some finalState) :
    let context := Statements.context entry.args ++ (dummySorts commands).map Binder.bound
    TypedStore signature context after.store ∧ RankedStore context after.store ∧
      StackSound signature definitions theorems context hypotheses after.store after.stack ∧
      HeapSound signature definitions theorems context hypotheses after.store after.heap := by
  have original := statement_original_hypotheses_of_run signature tables available entry declaration commands loaded finalState
    conclusion unified initialized executed arities declared accepted
  rw [hypothesesAgree] at original
  exact step_hyp_preserves_original_scope signature definitions theorems _ hypotheses tables before after finalState remaining
    typed ranked stack heap hypExecuted continued original

namespace Controls

private def type : ExprType := ⟨0, false, ∅⟩
private def args : List ExprType := [type, ⟨0, true, {0}⟩]
private def constant : TermEntry := ⟨0, [], type, none⟩
private def identityEntry : TermEntry := ⟨0, [⟨0, true, {0}⟩], ⟨0, false, {0}⟩, some [.ref 0]⟩
private def constantDecl : TermDecl := ⟨[], 0, ∅⟩
private def identityDecl : TermDecl := ⟨[.bound 0], 0, {0}⟩
private def identityBody : Definition.Body := ⟨[], .var 0⟩
private def signature : TermSignature := fun term =>
  if term = 0 then some constantDecl else if term = 1 then some identityDecl else none
private def tables : Tables := ⟨[⟨false, false, true, false⟩], [constant, identityEntry], []⟩
private def commands : List ProofCmd := [.dummy 0, .termSave 1, .hyp, .ref 2, .ref 4,
  .conv, .symm, .ref 2, .unfold, .refl, .save, .dummy 0]
private def initial : Formats.MMB.State :=
  ⟨[⟨.var 0, type⟩, ⟨.var 1, ⟨0, true, {0}⟩⟩], [], [.expr 0, .expr 1], [], 1, 2⟩
private def finalState : Formats.MMB.State :=
  ⟨initial.store ++ [⟨.var 2, ⟨0, true, {1}⟩⟩, ⟨.app 1 [2], ⟨0, false, {1}⟩⟩, ⟨.var 3, ⟨0, true, {2}⟩⟩],
    [.expr 4, .proof 2], [.expr 0, .expr 1, .expr 2, .expr 3, .proof 3, .proof 2, .expr 4], [3], 3, 4⟩

private theorem available (term : Nat) (entry : TermEntry) (read : tables.terms[term]? = some entry) :
    ∃ declaration body, Statements.termDecl tables.terms entry = some (declaration, body) ∧ signature term = some declaration := by
  have inside : term < 2 := by
    have bound := (List.getElem?_eq_some_iff.mp read).choose
    simpa [tables] using bound
  have casesTerm : term = 0 ∨ term = 1 := by omega
  rcases casesTerm with rfl | rfl
  · have same : entry = constant := by simpa [tables] using read.symm
    subst entry
    exact ⟨constantDecl, none, by decide, by simp [signature]⟩
  · have same : entry = identityEntry := by simpa [tables] using read.symm
    subst entry
    exact ⟨identityDecl, some identityBody, by decide, by simp [signature]⟩

theorem actual_mixed_run_preserves_typed_ranked_store :
    let context := Statements.context args ++ (dummySorts commands).map Binder.bound
    TypedStore signature context finalState.store ∧ RankedStore context finalState.store :=
  run_initialized_fixed_store signature tables available args commands initial finalState (by decide) (by decide)

theorem actual_mixed_run_preserves_public_variable_roots :
    Soundness.decode finalState.store 0 = some (.var 0) ∧ Soundness.decode finalState.store 1 = some (.var 1) := by
  have preserved := run_initialized_public_roots tables .assertion args initial finalState commands (by decide) (by decide)
  exact ⟨preserved 0 (by decide), preserved 1 (by decide)⟩

theorem decoded_definition_earns_exact_term_fields :
    identityDecl.arguments = Statements.context identityEntry.args ∧ identityDecl.resultSort = identityEntry.sort ∧
      identityDecl.dependencies = identityEntry.ret.deps.image
        (fun rank => (Statements.boundPositions identityEntry.args).getD rank rank) :=
  termDecl_fields tables.terms identityEntry identityDecl (some identityBody) (by decide)

theorem absent_independent_declaration_cannot_supply_basis :
    ¬ ∃ declaration body, Statements.termDecl tables.terms constant = some (declaration, body) ∧
      (none : Option TermDecl) = some declaration := by simp

theorem mismatched_independent_declaration_cannot_supply_basis :
    ¬ ∃ declaration body, Statements.termDecl tables.terms identityEntry = some (declaration, body) ∧
      some constantDecl = some declaration := by
  have sourceRead : Statements.termDecl tables.terms identityEntry = some (identityDecl, some identityBody) := by decide
  rw [sourceRead]
  simp [constantDecl, identityDecl]

theorem incomplete_definition_stream_refused :
    Statements.termDecl tables.terms { identityEntry with value := some [.ref 0, .ref 0] } = none := by decide

theorem unknown_definition_arity_refused :
    Statements.termDecl tables.terms { identityEntry with value := some [.term 2] } = none := by decide

theorem well_typed_run_still_requires_original_hypothesis_matching :
    run tables .assertion initial commands = some finalState ∧
      unifyRun finalState.store .statement ⟨[0], [(0, false), (1, false)], [], finalState.hyps⟩
        [.ref 0, .hyp, .term 1, .ref 1] = none := by decide

namespace ScopedHypothesis

private def entry : ThmEntry := ⟨args, [.term 1, .ref 1, .hyp, .term 1, .ref 1]⟩
private def declaration : TheoremDecl :=
  ⟨Statements.context args, [.app (.term 1) (.var 1)], .app (.term 1) (.var 1)⟩
private def commands : List ProofCmd := [.ref 1, .termSave 1, .hyp, .ref 3]
private def before : Formats.MMB.State :=
  { initial with
    store := initial.store ++ [⟨.app 1 [1], ⟨0, false, {0}⟩⟩]
    stack := [.expr 2], heap := [.expr 0, .expr 1, .expr 2] }
private def after : Formats.MMB.State := { before with stack := [], heap := before.heap ++ [.proof 2], hyps := [2] }
private def finalState : Formats.MMB.State := { after with stack := [.proof 2] }
private def unified : Unifier := ⟨[], [(0, false), (1, false)], [], []⟩

private theorem arities (term : Nat) (termDecl : TermDecl) (known : signature term = some termDecl) :
    Statements.arityOf tables.terms term = some termDecl.arguments.length := by
  simp only [signature] at known
  split at known
  · rename_i zero
    subst term
    cases Option.some.inj known
    rfl
  · split at known
    · rename_i one
      subst term
      cases Option.some.inj known
      rfl
    · cases known

private theorem beforeTyping : TypedStore signature (Statements.context args) before.store := by
  have result := (run_initialized_fixed_store signature tables available args [.ref 1, .termSave 1] initial before
    (by decide) (by decide)).1
  simpa [dummySorts] using result

private theorem beforeRanking : RankedStore (Statements.context args) before.store := by
  have result := (run_initialized_fixed_store signature tables available args [.ref 1, .termSave 1] initial before
    (by decide) (by decide)).2
  simpa [dummySorts] using result

private theorem beforeStack : StackSound signature (fun _ => none) (fun _ => none) (Statements.context args)
    declaration.hypotheses before.store before.stack :=
  .expr (TypedStore.pointer signature _ before.store beforeTyping 2 ⟨.app 1 [1], ⟨0, false, {0}⟩⟩ (by decide)) .empty

private theorem beforeHeap : HeapSound signature (fun _ => none) (fun _ => none) (Statements.context args)
    declaration.hypotheses before.store before.heap := by
  intro element member
  simp [before] at member
  rcases member with rfl | rfl | rfl
  · exact TypedStore.pointer signature _ before.store beforeTyping 0 ⟨.var 0, type⟩ (by decide)
  · exact TypedStore.pointer signature _ before.store beforeTyping 1 ⟨.var 1, ⟨0, true, {0}⟩⟩ (by decide)
  · exact TypedStore.pointer signature _ before.store beforeTyping 2 ⟨.app 1 [1], ⟨0, false, {0}⟩⟩ (by decide)

theorem run_earns_original_hypotheses_without_assumed_final_typing :
    finalState.hyps.reverse.mapM (Soundness.decode finalState.store) = some declaration.hypotheses := by
  exact statement_original_hypotheses_of_run signature tables available entry declaration commands initial finalState 2 unified
    (by decide) (by decide) arities (by decide) (by rfl)

theorem run_earns_hypothesis_heap_evidence_without_assumed_final_typing :
    HeapSound signature (fun _ => none) (fun _ => none) (Statements.context args) declaration.hypotheses after.store after.heap := by
  have result := step_hyp_preserves_scope_of_run signature (fun _ => none) (fun _ => none) tables available entry declaration
    declaration.hypotheses commands [.ref 3] initial before after finalState 2 unified (by decide) (by decide)
    arities (by decide) rfl (by rfl)
    (by simpa [entry, dummySorts, commands] using beforeTyping) (by simpa [entry, dummySorts, commands] using beforeRanking)
    (by simpa [entry, dummySorts, commands] using beforeStack) (by simpa [entry, dummySorts, commands] using beforeHeap)
    (by decide) (by decide)
  simpa [entry, dummySorts, commands] using result.2.2.2

theorem independently_scoped_hypothesis_proof_is_accepted : checkAssertion tables entry commands false = true := by decide

theorem missing_original_premise_is_refused_despite_store_typing :
    checkAssertion tables ⟨args, [.term 1, .ref 1]⟩ commands false = false := by decide

end ScopedHypothesis

end Controls

end Mettapedia.Languages.MM0.MeTTa.MMBRunSoundness
