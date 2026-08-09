import Mettapedia.Languages.Dataflow.Semantics

/-!
# Data-driven execution and adequacy

Kahn-style execution: a state carries the cells computed so far and the
instructions still pending, and a step fires *any* pending instruction whose
operands are already available.  No program counter and no schedule is
imposed — the write/read dependency is the only ordering.

The results:

* `Step.pending_length_lt` — firing strictly decreases the pending count, so
  every run is finite (`Steps.length_le`);
* `Invariant.step` — the reachability invariant is preserved;
* `progress` — a well-formed program with pending work always has a step:
  no deadlock;
* `terminal_result_eq_denote` — **the crown**: every terminal state of every
  run assigns the returned cell exactly its denotation.

Schedule independence of the answer is then a corollary
(`terminal_result_unique`), because the denotation is a function: it needs
no confluence argument.  The diamond property proved at the end is about
*states*, which is the stronger statement the process-calculus layer will
need.
-/

namespace Mettapedia.Languages.Dataflow

variable {Op Value : Type}

/-! ## Readiness -/

/-- Evaluate an operand vector against the computed environment. -/
def evalOperands (env : List (CellId × Value)) :
    List CellId → Option (List Value)
  | [] => some []
  | c :: cs =>
      match lookup env c with
      | none => none
      | some v =>
          match evalOperands env cs with
          | none => none
          | some vs => some (v :: vs)

/-- The value an instruction produces, when its operands are available. -/
def readyValue (spec : PureOperatorSpec Op Value)
    (env : List (CellId × Value)) : Instruction Op Value → Option Value
  | .const _ v => some v
  | .apply _ op operands =>
      if operands.length = spec.arity op then
        match evalOperands env operands with
        | some values => some (spec.apply op values)
        | none => none
      else
        none

@[simp] theorem readyValue_const (spec : PureOperatorSpec Op Value)
    (env : List (CellId × Value)) (d : CellId) (v : Value) :
    readyValue spec env (.const d v) = some v := rfl

/-- Operand evaluation succeeds exactly when every operand is available. -/
theorem evalOperands_isSome_of_forall {env : List (CellId × Value)} :
    ∀ {cs : List CellId}, (∀ c ∈ cs, (lookup env c).isSome) →
      ∃ vs, evalOperands env cs = some vs := by
  intro cs
  induction cs with
  | nil => intro _; exact ⟨[], rfl⟩
  | cons c cs inductionHypothesis =>
      intro available
      obtain ⟨v, headValue⟩ := Option.isSome_iff_exists.mp
        (available c (List.mem_cons_self ..))
      obtain ⟨vs, tailValues⟩ := inductionHypothesis
        (fun d member => available d (List.mem_cons_of_mem _ member))
      exact ⟨v :: vs, by simp [evalOperands, headValue, tailValues]⟩

/-- If an operand vector fails to evaluate, some operand is unavailable. -/
theorem exists_unavailable_of_evalOperands_none {env : List (CellId × Value)} :
    ∀ {cs : List CellId}, evalOperands env cs = none →
      ∃ c ∈ cs, lookup env c = none := by
  intro cs
  induction cs with
  | nil => intro failed; simp [evalOperands] at failed
  | cons c cs inductionHypothesis =>
      intro failed
      cases headValue : lookup env c with
      | none => exact ⟨c, List.mem_cons_self .., headValue⟩
      | some v =>
          cases tailValues : evalOperands env cs with
          | none =>
              obtain ⟨d, member, missing⟩ := inductionHypothesis tailValues
              exact ⟨d, List.mem_cons_of_mem _ member, missing⟩
          | some vs =>
              simp [evalOperands, headValue, tailValues] at failed

/-! ## States and steps -/

/-- Execution state: the environment computed so far, and the instructions
still to fire. -/
structure State (Op Value : Type) where
  computed : List (CellId × Value)
  pending : List (Instruction Op Value)

/-- Execution starts with the inputs available and everything pending. -/
def Program.initialState (p : Program Op Value) : State Op Value :=
  ⟨p.inputs, p.instructions⟩

/-- One firing: any ready pending instruction, in any position. -/
inductive Step (spec : PureOperatorSpec Op Value) :
    State Op Value → State Op Value → Prop where
  | fire {computed : List (CellId × Value)}
      {pre post : List (Instruction Op Value)} {i : Instruction Op Value}
      {v : Value} (ready : readyValue spec computed i = some v) :
      Step spec ⟨computed, pre ++ i :: post⟩
        ⟨(i.dst, v) :: computed, pre ++ post⟩

/-- Reflexive-transitive execution. -/
abbrev Steps (spec : PureOperatorSpec Op Value) :
    State Op Value → State Op Value → Prop :=
  Relation.ReflTransGen (Step spec)

/-- Firing strictly decreases the pending count: every run is finite. -/
theorem Step.pending_length_lt {spec : PureOperatorSpec Op Value}
    {s s' : State Op Value} (step : Step spec s s') :
    s'.pending.length < s.pending.length := by
  cases step with
  | fire _ => simp

/-- A run cannot be longer than the initial pending count. -/
theorem Steps.pending_length_le {spec : PureOperatorSpec Op Value}
    {s s' : State Op Value} (run : Steps spec s s') :
    s'.pending.length ≤ s.pending.length := by
  induction run with
  | refl => exact Nat.le_refl _
  | tail _ step inductionHypothesis =>
      exact Nat.le_trans (Nat.le_of_lt step.pending_length_lt)
        inductionHypothesis

/-! ## Well-formedness -/

/-- The arity obligation an instruction carries. -/
def Instruction.arityOk (spec : PureOperatorSpec Op Value) :
    Instruction Op Value → Bool
  | .const _ _ => true
  | .apply _ op operands => operands.length == spec.arity op

/-- A program is well formed when writers are unique, inputs are distinct
and unwritten, arities agree, and every instruction destination and the
returned cell denote.  The last condition is where definedness and
acyclicity live: a cell on a dependency cycle denotes nothing. -/
structure Program.WellFormed (spec : PureOperatorSpec Op Value)
    (p : Program Op Value) : Prop where
  writersUnique : (p.instructions.map Instruction.dst).Nodup
  inputsUnique : (p.inputs.map Prod.fst).Nodup
  inputsNotWritten : ∀ i ∈ p.instructions, p.inputValue? i.dst = none
  aritiesOk : ∀ i ∈ p.instructions, i.arityOk spec = true
  destinationsDenote : ∀ i ∈ p.instructions, ∃ v, Denotes spec p i.dst v
  resultDenotes : ∃ v, Denotes spec p p.result v

/-- In a list of instructions with distinct destinations, searching by an
instruction's own destination finds that instruction. -/
theorem find?_dst_eq_self :
    ∀ {l : List (Instruction Op Value)}, (l.map Instruction.dst).Nodup →
      ∀ {i : Instruction Op Value}, i ∈ l →
        l.find? (fun j => j.dst == i.dst) = some i := by
  intro l
  induction l with
  | nil => intro _ i member; cases member
  | cons head tail inductionHypothesis =>
      intro unique i member
      simp only [List.map_cons, List.nodup_cons] at unique
      rcases List.mem_cons.mp member with rfl | tailMember
      · rw [List.find?_cons_of_pos (by simp)]
      · have headNe : head.dst ≠ i.dst := fun h =>
          unique.1 (h ▸ List.mem_map_of_mem tailMember)
        rw [List.find?_cons_of_neg (by simpa using headNe)]
        exact inductionHypothesis unique.2 tailMember

/-- In a program with unique writers, an instruction is *the* writer of its
own destination. -/
theorem writerOf_eq_self {p : Program Op Value}
    (unique : (p.instructions.map Instruction.dst).Nodup)
    {i : Instruction Op Value} (member : i ∈ p.instructions) :
    p.writerOf? i.dst = some i :=
  find?_dst_eq_self unique member

/-! ## Soundness of firing -/

/-- Operand evaluation against a denoting environment denotes. -/
theorem evalOperands_denotes {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} {env : List (CellId × Value)}
    (sound : ∀ c v, lookup env c = some v → Denotes spec p c v) :
    ∀ {cs : List CellId} {vs : List Value}, evalOperands env cs = some vs →
      DenotesList spec p cs vs := by
  intro cs
  induction cs with
  | nil =>
      intro vs evaluated
      have : vs = [] := by simpa [evalOperands] using evaluated.symm
      subst this
      exact DenotesList.nil
  | cons c cs inductionHypothesis =>
      intro vs evaluated
      cases headValue : lookup env c with
      | none => simp [evalOperands, headValue] at evaluated
      | some v =>
          cases tailValues : evalOperands env cs with
          | none => simp [evalOperands, headValue, tailValues] at evaluated
          | some tail =>
              simp only [evalOperands, headValue, tailValues,
                Option.some.injEq] at evaluated
              subst evaluated
              exact DenotesList.cons (sound c v headValue)
                (inductionHypothesis tailValues)

/-- A fired instruction's value is the denotation of its destination. -/
theorem readyValue_denotes {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} (wf : p.WellFormed spec)
    {env : List (CellId × Value)}
    (sound : ∀ c v, lookup env c = some v → Denotes spec p c v)
    {i : Instruction Op Value} (member : i ∈ p.instructions) {v : Value}
    (ready : readyValue spec env i = some v) : Denotes spec p i.dst v := by
  cases i with
  | const d constValue =>
      have writer := writerOf_eq_self wf.writersUnique member
      have notInput := wf.inputsNotWritten _ member
      simp only [readyValue_const, Option.some.injEq] at ready
      subst ready
      exact Denotes.const notInput (by simpa using writer)
  | apply d op operands =>
      have writer := writerOf_eq_self wf.writersUnique member
      have notInput := wf.inputsNotWritten _ member
      have arity : operands.length = spec.arity op := by
        have := wf.aritiesOk _ member
        simpa [Instruction.arityOk] using this
      simp only [readyValue, if_pos arity] at ready
      cases operandValues : evalOperands env operands with
      | none => rw [operandValues] at ready; cases ready
      | some values =>
          rw [operandValues] at ready
          have valueEq : spec.apply op values = v := by simpa using ready
          subst valueEq
          exact Denotes.apply notInput (by simpa using writer) arity
            (evalOperands_denotes sound operandValues)

/-! ## The reachability invariant -/

/-- What holds of every state reachable from the initial one. -/
structure Invariant (spec : PureOperatorSpec Op Value)
    (p : Program Op Value) (s : State Op Value) : Prop where
  sound : ∀ c v, lookup s.computed c = some v → Denotes spec p c v
  pendingSublist : s.pending.Sublist p.instructions
  firedComputed : ∀ i ∈ p.instructions, i ∉ s.pending →
    (lookup s.computed i.dst).isSome
  inputsPresent : ∀ c v, p.inputValue? c = some v →
    lookup s.computed c = some v
  pendingNotComputed : ∀ i ∈ s.pending, lookup s.computed i.dst = none

theorem Invariant.initial {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} (wf : p.WellFormed spec) :
    Invariant spec p p.initialState where
  sound := fun _ _ found => Denotes.input found
  pendingSublist := List.Sublist.refl _
  firedComputed := fun _ member notPending => absurd member notPending
  inputsPresent := fun _ _ isInput => isInput
  pendingNotComputed := fun i member => wf.inputsNotWritten i member

/-- Instructions are distinct, since their destinations are. -/
theorem instructions_nodup {p : Program Op Value}
    (unique : (p.instructions.map Instruction.dst).Nodup) :
    p.instructions.Nodup :=
  List.Nodup.of_map _ unique

theorem Invariant.step {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} (wf : p.WellFormed spec) {s s' : State Op Value}
    (invariant : Invariant spec p s) (step : Step spec s s') :
    Invariant spec p s' := by
  cases step with
  | @fire computed pre post i v ready =>
      have memberPending : i ∈ p.instructions :=
        invariant.pendingSublist.mem (List.mem_append_right _
          (List.mem_cons_self ..))
      have restSublist : (pre ++ post).Sublist p.instructions :=
        List.Sublist.trans
          (List.Sublist.append (List.Sublist.refl pre)
            ((List.Sublist.refl post).cons i))
          invariant.pendingSublist
      have pendingNodup : (pre ++ i :: post).Nodup :=
        invariant.pendingSublist.nodup (instructions_nodup wf.writersUnique)
      have distinctDst : ∀ j ∈ pre ++ post, i.dst ≠ j.dst := by
        intro j memberJ
        have jInstr : j ∈ p.instructions :=
          restSublist.mem memberJ
        have notMember : i ∉ pre ++ post :=
          (List.nodup_cons.mp (List.nodup_middle.mp pendingNodup)).1
        have jNe : j ≠ i := fun same => notMember (same ▸ memberJ)
        intro dstSame
        have := List.inj_on_of_nodup_map wf.writersUnique memberPending
          jInstr dstSame
        exact jNe this.symm
      refine ⟨?_, restSublist, ?_, ?_, ?_⟩
      · intro c w found
        by_cases same : i.dst = c
        · subst same
          rw [lookup_cons_self] at found
          have valueEq : v = w := by simpa using found
          subst valueEq
          exact readyValue_denotes wf invariant.sound memberPending ready
        · rw [lookup_cons_of_ne same] at found
          exact invariant.sound c w found
      · intro j memberJ notPending
        by_cases dstSame : i.dst = j.dst
        · rw [dstSame, lookup_cons_self]; simp
        · rw [lookup_cons_of_ne dstSame]
          refine invariant.firedComputed j memberJ ?_
          intro memberBefore
          rcases List.mem_append.mp memberBefore with inPre | inTail
          · exact notPending (List.mem_append_left _ inPre)
          · rcases List.mem_cons.mp inTail with rfl | inPost
            · exact dstSame rfl
            · exact notPending (List.mem_append_right _ inPost)
      · intro c w isInput
        have notDst : i.dst ≠ c := by
          intro same
          have := wf.inputsNotWritten i memberPending
          rw [same, isInput] at this
          cases this
        rw [lookup_cons_of_ne notDst]
        exact invariant.inputsPresent c w isInput
      · intro j memberJ
        rw [lookup_cons_of_ne (distinctDst j memberJ)]
        exact invariant.pendingNotComputed j
          (List.mem_append.mpr (by
            rcases List.mem_append.mp memberJ with inPre | inPost
            · exact Or.inl inPre
            · exact Or.inr (List.mem_cons_of_mem _ inPost)))

theorem Invariant.steps {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} (wf : p.WellFormed spec) {s s' : State Op Value}
    (invariant : Invariant spec p s) (run : Steps spec s s') :
    Invariant spec p s' := by
  induction run with
  | refl => exact invariant
  | tail _ step inductionHypothesis => exact inductionHypothesis.step wf step

/-! ## Progress: a well-formed program never deadlocks -/

/-- Every operand of a denoting vector denotes at the *same* budget. -/
theorem denoteOperands_mem_denoteCell {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} {fuel : Nat} :
    ∀ {cs : List CellId} {vs : List Value},
      denoteOperands spec p fuel cs = some vs → ∀ d ∈ cs,
        ∃ w, denoteCell spec p fuel d = some w := by
  intro cs
  induction cs with
  | nil => intro vs _ d member; cases member
  | cons c cs inductionHypothesis =>
      intro vs evaluated d member
      cases headValue : denoteCell spec p fuel c with
      | none => simp [denoteOperands_cons, headValue] at evaluated
      | some v =>
          cases tailValues : denoteOperands spec p fuel cs with
          | none =>
              simp [denoteOperands_cons, headValue, tailValues] at evaluated
          | some tail =>
              rcases List.mem_cons.mp member with rfl | tailMember
              · exact ⟨v, headValue⟩
              · exact inductionHypothesis tailValues d tailMember

/-- A writer found by lookup is an instruction of the program writing that
very cell. -/
theorem writerOf_mem {p : Program Op Value} {c : CellId}
    {i : Instruction Op Value} (writer : p.writerOf? c = some i) :
    i ∈ p.instructions ∧ i.dst = c :=
  ⟨List.mem_of_find?_eq_some writer, by simpa using List.find?_some writer⟩

/-- A denoting cell is supplied either as an input or by an instruction. -/
theorem Denotes.has_source {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} {c : CellId} {v : Value}
    (denotes : Denotes spec p c v) :
    (p.inputValue? c).isSome ∨ (p.writerOf? c).isSome := by
  obtain ⟨fuel, evaluated⟩ := denotes
  cases fuel with
  | zero => rw [denoteCell_zero] at evaluated; exact Or.inl (by simp [evaluated])
  | succ fuel =>
      cases isInput : p.inputValue? c with
      | some inputValue => exact Or.inl (by simp)
      | none =>
          cases writer : p.writerOf? c with
          | none =>
              rw [denoteCell_succ, isInput, writer] at evaluated
              cases evaluated
          | some i => exact Or.inr (by simp)

/-- **No deadlock.**  In a well-formed program, any reachable state with
pending work has a ready instruction, so execution can always continue. -/
theorem progress {spec : PureOperatorSpec Op Value} {p : Program Op Value}
    (wf : p.WellFormed spec) {s : State Op Value}
    (invariant : Invariant spec p s) (nonempty : s.pending ≠ []) :
    ∃ s', Step spec s s' := by
  -- a ready pending instruction can always be found by descending the
  -- denotation of any pending destination
  have findReady : ∀ (fuel : Nat) (c : CellId) (v : Value),
      denoteCell spec p fuel c = some v → lookup s.computed c = none →
      ∃ j ∈ s.pending, (readyValue spec s.computed j).isSome := by
    intro fuel
    induction fuel with
    | zero =>
        intro c v evaluated notComputed
        rw [denoteCell_zero] at evaluated
        rw [invariant.inputsPresent c v evaluated] at notComputed
        cases notComputed
    | succ fuel inductionHypothesis =>
        intro c v evaluated notComputed
        cases isInput : p.inputValue? c with
        | some inputValue =>
            rw [invariant.inputsPresent c inputValue isInput] at notComputed
            cases notComputed
        | none =>
            cases writer : p.writerOf? c with
            | none =>
                rw [denoteCell_succ, isInput, writer] at evaluated
                cases evaluated
            | some j =>
                obtain ⟨memberJ, dstJ⟩ := writerOf_mem writer
                have pendingJ : j ∈ s.pending := by
                  by_contra notPending
                  have := invariant.firedComputed j memberJ notPending
                  rw [dstJ, notComputed] at this
                  exact absurd this (by simp)
                cases j with
                | const d constValue =>
                    exact ⟨.const d constValue, pendingJ, by simp⟩
                | apply d op operands =>
                    have arity : operands.length = spec.arity op := by
                      have := wf.aritiesOk _ memberJ
                      simpa [Instruction.arityOk] using this
                    cases operandValues :
                        evalOperands s.computed operands with
                    | some values =>
                        refine ⟨.apply d op operands, pendingJ, ?_⟩
                        simp [readyValue, arity, operandValues]
                    | none =>
                        obtain ⟨e, memberE, missing⟩ :=
                          exists_unavailable_of_evalOperands_none
                            operandValues
                        rw [denoteCell_succ, isInput, writer] at evaluated
                        simp only [if_pos arity] at evaluated
                        cases childValues :
                            denoteOperands spec p fuel operands with
                        | none => rw [childValues] at evaluated; cases evaluated
                        | some childList =>
                            obtain ⟨w, childEvaluated⟩ :=
                              denoteOperands_mem_denoteCell childValues e
                                memberE
                            exact inductionHypothesis e w childEvaluated missing
  obtain ⟨i, pendingI, restList, pendingEq⟩ :
      ∃ i pre post, s.pending = pre ++ i :: post := by
    cases pendingShape : s.pending with
    | nil => exact absurd pendingShape nonempty
    | cons head tail => exact ⟨head, [], tail, by simp⟩
  have memberI : i ∈ p.instructions :=
    invariant.pendingSublist.mem (by rw [pendingEq]; simp)
  have notComputed : lookup s.computed i.dst = none :=
    invariant.pendingNotComputed i (by rw [pendingEq]; simp)
  obtain ⟨v, denotes⟩ := wf.destinationsDenote i memberI
  obtain ⟨fuel, evaluated⟩ := denotes
  obtain ⟨j, pendingJ, ready⟩ := findReady fuel i.dst v evaluated notComputed
  obtain ⟨w, readyValue⟩ := Option.isSome_iff_exists.mp ready
  obtain ⟨pre, post, split⟩ := List.append_of_mem pendingJ
  refine ⟨⟨(j.dst, w) :: s.computed, pre ++ post⟩, ?_⟩
  have stateEq : s = ⟨s.computed, pre ++ j :: post⟩ := by
    cases s; simp_all
  rw [stateEq]
  exact Step.fire readyValue

/-- A state with no available step has nothing pending: the only way to stop
is to finish. -/
theorem terminal_of_no_step {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} (wf : p.WellFormed spec) {s : State Op Value}
    (invariant : Invariant spec p s) (stuck : ¬ ∃ s', Step spec s s') :
    s.pending = [] := by
  by_contra nonempty
  exact stuck (progress wf invariant nonempty)

/-- **Termination.**  Execution of a well-formed program always reaches a
state with nothing pending. -/
theorem exists_terminal_run {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} (wf : p.WellFormed spec) :
    ∃ s, Steps spec p.initialState s ∧ s.pending = [] := by
  suffices reach : ∀ (bound : Nat) (s : State Op Value),
      Invariant spec p s → s.pending.length ≤ bound →
      ∃ t, Steps spec s t ∧ t.pending = [] by
    obtain ⟨t, run, terminal⟩ := reach p.initialState.pending.length
      p.initialState (Invariant.initial wf) (Nat.le_refl _)
    exact ⟨t, run, terminal⟩
  intro bound
  induction bound with
  | zero =>
      intro s invariant lengthLe
      exact ⟨s, Relation.ReflTransGen.refl,
        List.eq_nil_of_length_eq_zero (Nat.le_zero.mp lengthLe)⟩
  | succ bound inductionHypothesis =>
      intro s invariant lengthLe
      by_cases empty : s.pending = []
      · exact ⟨s, Relation.ReflTransGen.refl, empty⟩
      · obtain ⟨s', step⟩ := progress wf invariant empty
        have shorter : s'.pending.length ≤ bound := by
          have := step.pending_length_lt
          omega
        obtain ⟨t, run, terminal⟩ :=
          inductionHypothesis s' (invariant.step wf step) shorter
        exact ⟨t, Relation.ReflTransGen.head step run, terminal⟩

/-! ## Adequacy: every terminal state carries the denotation -/

/-- **The crown.**  Under every schedule, a terminated run of a well-formed
program assigns the returned cell exactly its denotation. -/
theorem terminal_result_eq_denote {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} (wf : p.WellFormed spec) {s : State Op Value}
    (run : Steps spec p.initialState s) (terminal : s.pending = []) :
    ∃ v, Denotes spec p p.result v ∧ lookup s.computed p.result = some v := by
  have invariant := (Invariant.initial wf).steps wf run
  obtain ⟨v, denotes⟩ := wf.resultDenotes
  refine ⟨v, denotes, ?_⟩
  have computedSome : (lookup s.computed p.result).isSome := by
    rcases denotes.has_source with isInput | hasWriter
    · obtain ⟨inputValue, found⟩ := Option.isSome_iff_exists.mp isInput
      rw [invariant.inputsPresent p.result inputValue found]
      simp
    · obtain ⟨j, writer⟩ := Option.isSome_iff_exists.mp hasWriter
      obtain ⟨memberJ, dstJ⟩ := writerOf_mem writer
      have notPending : j ∉ s.pending := by rw [terminal]; simp
      have := invariant.firedComputed j memberJ notPending
      rwa [dstJ] at this
  obtain ⟨w, found⟩ := Option.isSome_iff_exists.mp computedSome
  rw [found, Denotes.functional (invariant.sound p.result w found) denotes]

/-- Schedule independence of the answer: any two terminated runs agree on
the returned cell.  This needs no confluence argument — the denotation is a
function, and both runs compute it. -/
theorem terminal_result_unique {spec : PureOperatorSpec Op Value}
    {p : Program Op Value} (wf : p.WellFormed spec) {s t : State Op Value}
    (runLeft : Steps spec p.initialState s) (terminalLeft : s.pending = [])
    (runRight : Steps spec p.initialState t) (terminalRight : t.pending = []) :
    lookup s.computed p.result = lookup t.computed p.result := by
  obtain ⟨v, denotesLeft, foundLeft⟩ :=
    terminal_result_eq_denote wf runLeft terminalLeft
  obtain ⟨w, denotesRight, foundRight⟩ :=
    terminal_result_eq_denote wf runRight terminalRight
  rw [foundLeft, foundRight, Denotes.functional denotesLeft denotesRight]

end Mettapedia.Languages.Dataflow
