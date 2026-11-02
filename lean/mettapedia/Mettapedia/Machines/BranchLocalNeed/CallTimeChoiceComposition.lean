import Mettapedia.Machines.BranchLocalNeed.CallTimeChoiceSpec

/-!
# Compositional execution for branch-local call-time choice

The observation here retains the complete ordered result list, including the
branch store, memoized choices and event trace. The active contexts below are
sound for this observation. A producer placed under `quote`, `need` or `delay`
is stored as syntax, so replacing that producer requires a relation on stores;
it is deliberately not an active-context rule.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.BranchLocalNeed.CallTimeChoice

namespace Composition

/-- Equality of actual evaluations at every incoming store and environment. -/
def Equivalent (program : Program) (left right : Comp) : Prop :=
  ∀ store environment results,
    Derives program (.eval store environment left) results ↔
      Derives program (.eval store environment right) results

theorem Equivalent.refl (program : Program) (code : Comp) :
    Equivalent program code code := fun _ _ _ => Iff.rfl

theorem Equivalent.symm {program : Program} {left right : Comp}
    (same : Equivalent program left right) : Equivalent program right left :=
  fun store environment results => (same store environment results).symm

theorem Equivalent.trans {program : Program} {left middle right : Comp}
    (first : Equivalent program left middle) (second : Equivalent program middle right) :
    Equivalent program left right :=
  fun store environment results => (first store environment results).trans
    (second store environment results)

/-- Sequential composition runs each continuation in its own predecessor's
store. The intermediate results are neither flattened into one store nor
deduplicated. -/
theorem seq_iff (program : Program) (store : Store) (environment : List (Val Nat))
    (first rest : Comp) (results : List Result) :
    Derives program (.eval store environment (.seq first rest)) results ↔
      ∃ previous, Derives program (.eval store environment first) previous ∧
        Derives program (.seqK rest environment previous) results := by
  constructor
  · intro evaluated
    cases evaluated with
    | seq head tail => exact ⟨_, head, tail⟩
  · rintro ⟨previous, head, tail⟩
    exact Derives.seq head tail

/-- Lexical sequencing evaluates the right-hand side in the outer
environment, then adds one new binder for the continuation. -/
theorem seq_return_iff (program : Program) (store : Store)
    (environment : List (Val Nat)) (value : VExp) (body : Comp) (results : List Result) :
    Derives program (.eval store environment (.seq (.ret value) body)) results ↔
      Derives program (.eval store (value.eval environment :: environment) body) results := by
  constructor
  · intro evaluated
    cases evaluated with
    | seq first rest =>
      cases first
      cases rest with
      | seqKOk continued tail =>
        cases tail
        simpa only [List.append_nil] using continued
      | seqKStop stopped _ => simp [Outcome.isOk] at stopped
  · exact Derives.seq_single Derives.ret

/-- A selected equation uses exactly its argument environment. Its body
cannot acquire an additional caller variable through an implicit append. -/
theorem call_single_iff (program : Program) (store : Store)
    (environment : List (Val Nat)) (head : Nat) (arguments : List VExp)
    (rule : Rule) (results : List Result)
    (selected : candidates program head arguments.length = [rule]) :
    Derives program (.eval store environment (.call head arguments)) results ↔
      Derives program (.eval store (arguments.map (·.eval environment)) rule.body) results := by
  constructor
  · intro evaluated
    cases evaluated with
    | call _ branches =>
      rw [selected] at branches
      cases branches with
      | altsCons first tail =>
        cases tail
        simpa only [List.append_nil] using first
    | callNone absent => simp [selected] at absent
  · exact Derives.call_single_rule selected

theorem choose_iff (program : Program) (store : Store) (environment : List (Val Nat))
    (left right : Comp) (results : List Result) :
    Derives program (.eval store environment (.choose left right)) results ↔
      ∃ first second, Derives program (.eval store environment left) first ∧
        Derives program (.eval store environment right) second ∧ results = first ++ second := by
  constructor
  · intro evaluated
    cases evaluated with
    | choose first second => exact ⟨_, _, first, second, rfl⟩
  · rintro ⟨first, second, leftRun, rightRun, rfl⟩
    exact Derives.choose leftRun rightRun

theorem need_iff (program : Program) (store : Store) (environment : List (Val Nat))
    (producer body : Comp) (results : List Result) :
    Derives program (.eval store environment (.need producer body)) results ↔
      Derives program (.eval (store.alloc producer environment)
        (.need store.cells.length :: environment) body) results := by
  constructor
  · intro evaluated
    cases evaluated with
    | need bodyRun => exact bodyRun
  · exact Derives.need

theorem delay_iff (program : Program) (store : Store) (environment : List (Val Nat))
    (producer body : Comp) (results : List Result) :
    Derives program (.eval store environment (.delay producer body)) results ↔
      Derives program (.eval (store.alloc producer environment)
        (.thunk store.cells.length :: environment) body) results := by
  constructor
  · intro evaluated
    cases evaluated with
    | delay bodyRun => exact bodyRun
  · exact Derives.delay

theorem emit_iff (program : Program) (store : Store) (environment : List (Val Nat))
    (event : Nat) (body : Comp) (results : List Result) :
    Derives program (.eval store environment (.emit event body)) results ↔
      Derives program (.eval (store.emit event) environment body) results := by
  constructor
  · intro evaluated
    cases evaluated with
    | emit bodyRun => exact bodyRun
  · exact Derives.emit

theorem quote_iff (program : Program) (store : Store) (environment : List (Val Nat))
    (producer : Comp) (results : List Result) :
    Derives program (.eval store environment (.quote producer)) results ↔
      results = [(.ok (.code store.cells.length), store.alloc producer environment)] := by
  constructor
  · intro evaluated
    cases evaluated
    rfl
  · rintro rfl
    exact Derives.quote

/-- Explicit code activation uses the captured environment, and follows the
returned values using the already defined forcing judgment. -/
theorem run_code_iff (program : Program) (store : Store) (environment : List (Val Nat))
    (value : VExp) (cell : Nat) (suspension : Suspension) (results : List Result)
    (isCode : value.eval environment = .code cell)
    (stored : store.cells[cell]? = some suspension) :
    Derives program (.eval store environment (.run value)) results ↔
      ∃ previous, Derives program (.eval store suspension.env suspension.code) previous ∧
        Derives program (.followK previous) results := by
  constructor
  · intro evaluated
    cases evaluated with
    | runCode found lookup body follow =>
      have cellEq := Val.code.inj (found.symm.trans isCode)
      subst cell
      have suspensionEq := Option.some.inj (lookup.symm.trans stored)
      subst suspension
      exact ⟨_, body, follow⟩
    | runOther noncode => exact False.elim (noncode cell isCode)
  · rintro ⟨previous, body, follow⟩
    exact Derives.runCode isCode stored body follow

/-- A non-code activation terminates in the existing residual form. It does
not retry the same unmarked value indefinitely. -/
theorem run_residual_iff (program : Program) (store : Store)
    (environment : List (Val Nat)) (value : VExp) (results : List Result)
    (noncode : ∀ cell, value.eval environment ≠ .code cell) :
    Derives program (.eval store environment (.run value)) results ↔
      results = [(.ok (.app (.sym unquoteHead) (value.eval environment)), store)] := by
  constructor
  · intro evaluated
    cases evaluated with
    | runCode isCode _ _ _ => exact False.elim (noncode _ isCode)
    | runOther _ => rfl
  · rintro rfl
    exact Derives.runOther noncode

/-- All sequential continuations preserve a replacement valid at every
branch store, including failures and black holes. -/
theorem seqK_congr {program : Program} {left right : Comp}
    (same : Equivalent program left right) (environment : List (Val Nat))
    (previous results : List Result) :
    Derives program (.seqK left environment previous) results ↔
      Derives program (.seqK right environment previous) results := by
  have forward : ∀ a b, Equivalent program a b →
      ∀ previous results, Derives program (.seqK a environment previous) results →
        Derives program (.seqK b environment previous) results := by
    intro a b replacement previous
    induction previous with
    | nil =>
      intro results evaluated
      cases evaluated
      exact Derives.seqKNil
    | cons entry previous ih =>
      intro results evaluated
      cases evaluated with
      | seqKOk body rest =>
        exact Derives.seqKOk ((replacement _ _ _).mp body) (ih _ rest)
      | seqKStop stopped rest => exact Derives.seqKStop stopped (ih _ rest)
  exact ⟨forward left right same previous results,
    forward right left same.symm previous results⟩

theorem Equivalent.seq {program : Program} {first first' rest rest' : Comp}
    (head : Equivalent program first first') (tail : Equivalent program rest rest') :
    Equivalent program (.seq first rest) (.seq first' rest') := by
  intro store environment results
  rw [seq_iff, seq_iff]
  constructor
  · rintro ⟨previous, body, continued⟩
    exact ⟨previous, (head _ _ _).mp body, (seqK_congr tail _ _ _).mp continued⟩
  · rintro ⟨previous, body, continued⟩
    exact ⟨previous, (head _ _ _).mpr body, (seqK_congr tail _ _ _).mpr continued⟩

theorem Equivalent.choose {program : Program} {left left' right right' : Comp}
    (first : Equivalent program left left') (second : Equivalent program right right') :
    Equivalent program (.choose left right) (.choose left' right') := by
  intro store environment results
  rw [choose_iff, choose_iff]
  constructor
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact ⟨a, b, (first _ _ _).mp ha, (second _ _ _).mp hb, rfl⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact ⟨a, b, (first _ _ _).mpr ha, (second _ _ _).mpr hb, rfl⟩

theorem Equivalent.needBody {program : Program} {left right : Comp}
    (same : Equivalent program left right) (producer : Comp) :
    Equivalent program (.need producer left) (.need producer right) := by
  intro store environment results
  rw [need_iff, need_iff]
  exact same _ _ _

theorem Equivalent.delayBody {program : Program} {left right : Comp}
    (same : Equivalent program left right) (producer : Comp) :
    Equivalent program (.delay producer left) (.delay producer right) := by
  intro store environment results
  rw [delay_iff, delay_iff]
  exact same _ _ _

theorem Equivalent.emit {program : Program} {left right : Comp}
    (same : Equivalent program left right) (event : Nat) :
    Equivalent program (.emit event left) (.emit event right) := by
  intro store environment results
  rw [emit_iff, emit_iff]
  exact same _ _ _

theorem Equivalent.caseCon {program : Program} {hit hit' miss miss' : Comp}
    (onHit : Equivalent program hit hit') (onMiss : Equivalent program miss miss')
    (value : VExp) (name arity : Nat) :
    Equivalent program (.caseCon value name arity hit miss)
      (.caseCon value name arity hit' miss') := by
  intro store environment results
  constructor
  · intro evaluated
    cases evaluated with
    | caseConHit matched body => exact Derives.caseConHit matched ((onHit _ _ _).mp body)
    | caseConMiss unmatched body => exact Derives.caseConMiss unmatched ((onMiss _ _ _).mp body)
  · intro evaluated
    cases evaluated with
    | caseConHit matched body => exact Derives.caseConHit matched ((onHit _ _ _).mpr body)
    | caseConMiss unmatched body => exact Derives.caseConMiss unmatched ((onMiss _ _ _).mpr body)

theorem Equivalent.caseApp {program : Program} {hit hit' miss miss' : Comp}
    (onHit : Equivalent program hit hit') (onMiss : Equivalent program miss miss')
    (value : VExp) :
    Equivalent program (.caseApp value hit miss) (.caseApp value hit' miss') := by
  intro store environment results
  constructor
  · intro evaluated
    cases evaluated with
    | caseAppHit matched body => exact Derives.caseAppHit matched ((onHit _ _ _).mp body)
    | caseAppMiss unmatched body => exact Derives.caseAppMiss unmatched ((onMiss _ _ _).mp body)
  · intro evaluated
    cases evaluated with
    | caseAppHit matched body => exact Derives.caseAppHit matched ((onHit _ _ _).mpr body)
    | caseAppMiss unmatched body => exact Derives.caseAppMiss unmatched ((onMiss _ _ _).mpr body)

/-- Contexts whose hole is executed rather than stored as an opaque producer.
The fixed code around the hole may contain any supported computation. -/
inductive ActiveContext where
  | hole
  | seqFirst (inside : ActiveContext) (rest : Comp)
  | seqRest (first : Comp) (inside : ActiveContext)
  | needBody (producer : Comp) (inside : ActiveContext)
  | delayBody (producer : Comp) (inside : ActiveContext)
  | chooseLeft (inside : ActiveContext) (right : Comp)
  | chooseRight (left : Comp) (inside : ActiveContext)
  | emit (event : Nat) (inside : ActiveContext)
  | caseConHit (value : VExp) (name arity : Nat) (inside : ActiveContext) (miss : Comp)
  | caseConMiss (value : VExp) (name arity : Nat) (hit : Comp) (inside : ActiveContext)
  | caseAppHit (value : VExp) (inside : ActiveContext) (miss : Comp)
  | caseAppMiss (value : VExp) (hit : Comp) (inside : ActiveContext)

def ActiveContext.plug : ActiveContext → Comp → Comp
  | .hole, code => code
  | .seqFirst inside rest, code => .seq (inside.plug code) rest
  | .seqRest first inside, code => .seq first (inside.plug code)
  | .needBody producer inside, code => .need producer (inside.plug code)
  | .delayBody producer inside, code => .delay producer (inside.plug code)
  | .chooseLeft inside right, code => .choose (inside.plug code) right
  | .chooseRight left inside, code => .choose left (inside.plug code)
  | .emit event inside, code => .emit event (inside.plug code)
  | .caseConHit value name arity inside miss, code =>
      .caseCon value name arity (inside.plug code) miss
  | .caseConMiss value name arity hit inside, code =>
      .caseCon value name arity hit (inside.plug code)
  | .caseAppHit value inside miss, code => .caseApp value (inside.plug code) miss
  | .caseAppMiss value hit inside, code => .caseApp value hit (inside.plug code)

/-- Nested composition retains all ordered results and full branch state. -/
theorem Equivalent.context {program : Program} {left right : Comp}
    (same : Equivalent program left right) (context : ActiveContext) :
    Equivalent program (context.plug left) (context.plug right) := by
  induction context with
  | hole => exact same
  | seqFirst inside rest ih => exact ih.seq (.refl _ _)
  | seqRest first inside ih => exact (Equivalent.refl _ _).seq ih
  | needBody producer inside ih => exact ih.needBody producer
  | delayBody producer inside ih => exact ih.delayBody producer
  | chooseLeft inside right ih => exact ih.choose (.refl _ _)
  | chooseRight left inside ih => exact (Equivalent.refl _ _).choose ih
  | emit event inside ih => exact ih.emit event
  | caseConHit value name arity inside miss ih => exact ih.caseCon (.refl _ _) value name arity
  | caseConMiss value name arity hit inside ih =>
      exact (Equivalent.refl _ _).caseCon ih value name arity
  | caseAppHit value inside miss ih => exact ih.caseApp (.refl _ _) value
  | caseAppMiss value hit inside ih => exact (Equivalent.refl _ _).caseApp ih value

/-- The final normalization continuation is an active context, so this
strong equality gives equality at the independent source observation. -/
theorem Equivalent.observes {program : Program} {left right : Comp}
    (same : Equivalent (observed program) left right) (results : List Result) :
    Observes program left results ↔ Observes program right results := by
  exact (same.seq (.refl _ _)) Store.empty [] results

end Composition

end Mettapedia.Machines.BranchLocalNeed.CallTimeChoice
