import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeRecordRunsRealization

/-!
# Auxiliary arithmetic controls for the shared constrained-information queue

These Nat-valued clauses instantiate the same QueueClause rule builder as the
native record profile. They exercise actual rule admission, accumulated frames
and knowledge, and actual two-step runs. They are not native arithmetic or
EXPECT_ALPHA implementations; native clauses retain their actual source guards.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeRecordRunsControls

open NativeFieldSchema NativeRecordRuns InterpretedFrames
open MeTTaCalculus.OccurrenceCommits (Enabled)

noncomputable section

inductive ArithmeticRecord where
  | addSeven | double | neutral
  deriving DecidableEq, Repr

abbrev Cell (_ : Field) := Nat
abbrev numberFrame : Frame := ⟨Nat, ⟨0⟩⟩
abbrev Event := ArithmeticRecord × numberFrame.Carrier
abbrev Value := AtomData Cell Event
abbrev Store := StoreData Cell Event

def fields (number : Nat) : (name : Field) → Cell name :=
  fun name => if name = .context then number else 0

def arithmetic : ArithmeticRecord → Nat → Nat
  | .addSeven, number => number + 7
  | .double, number => 2 * number
  | .neutral, number => number

def permitted : ArithmeticRecord → Nat → Prop
  | .addSeven, number => number = 0
  | .double, number => number = 7
  | .neutral, _ => True

instance (record : ArithmeticRecord) (number : Nat) : Decidable (permitted record number) := by
  cases record <;> unfold permitted <;> infer_instance

def clause (record : ArithmeticRecord) : QueueClause Cell ArithmeticRecord numberFrame where
  witness := numberFrame
  before name number := fields number name
  after name number := fields (arithmetic record number) name
  record _ := record
  guard number effect := effect = arithmetic record number ∧ permitted record number
  writes := match record with | .neutral => [] | _ => [.context]
  writes_distinct := by cases record <;> decide
  unchanged name absent number := by
    cases record with
    | neutral => rfl
    | addSeven => simp only [List.mem_singleton] at absent; simp [fields, absent]
    | double => simp only [List.mem_singleton] at absent; simp [fields, absent]

def rules : RuleSyntax.Program (Terms Value) := familyProgram clause

theorem member (record : ArithmeticRecord) : (clause record).rule ∈ rules := ⟨record, rfl⟩

def initial (number : Nat) (pending : List Event) (generation : Field → Nat) (cursor : Nat) : Store where
  frame := ground
  knowledge := []
  present := (canonicalLayout generation cursor).support
  label occurrence _ := match occurrence with
    | .field name _ => .field name (fields number name)
    | .request _ => .pending cursor pending

theorem initial_view (number : Nat) (pending : List Event) (generation : Field → Nat) (cursor : Nat)
    (environment : (initial number pending generation cursor).frame.Carrier) :
    ViewData (initial number pending generation cursor) (canonicalLayout generation cursor)
      environment (fields number) cursor pending := by
  refine ⟨rfl, ?_, fun _ => rfl, rfl⟩
  intro equation present
  cases present

def active (record : ArithmeticRecord) (state : Store) (generation : Field → Nat) (cursor : Nat) :=
  (clause record).firing (member record) (old := state.frame)
    (selectionFor (clause record).writes generation cursor)

theorem active_shapes (record : ArithmeticRecord) (state : Store) (generation : Field → Nat) (cursor : Nat) :
    (active record state generation cursor).Shapes (frames Value) state := by
  refine ⟨canonical_fresh state (clause record).rule (member record) _, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · change (Occurrence.request cursor :: (clause record).writes.map (row generation)).Nodup
    apply List.nodup_cons.mpr
    exact ⟨by simp [row], (clause record).writes_distinct.map (row_injective generation)⟩
  · change (Occurrence.request (cursor+1) :: (clause record).writes.map (nextRow generation)).Nodup
    apply List.nodup_cons.mpr
    exact ⟨by simp [nextRow], (clause record).writes_distinct.map (nextRow_injective generation)⟩
  all_goals simp only [active, QueueClause.firing, canonical, QueueClause.rule, selectionFor,
    List.length_cons, List.length_map]

theorem canonical_enabled (writes : List Field) (generation : Field → Nat) (cursor : Nat) :
    Enabled (fun _ : Occurrence => ()) (canonicalLayout generation cursor).support
      ((selectionFor writes generation cursor).commit (T := Unit)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change (Occurrence.request cursor :: writes.map (row generation)).toFinset ⊆ _
    intro occurrence present
    rcases List.mem_cons.mp (List.mem_toFinset.mp present) with rfl | present
    · exact Finset.mem_insert_self _ _
    · obtain ⟨field, _, rfl⟩ := List.mem_map.mp present
      exact NativeRecordLayouts.field_mem_support _ field
  · change ((Field.all.filter (fun field => field ∉ writes)).map (row generation)).toFinset ⊆ _
    intro occurrence present
    obtain ⟨field, _, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp present)
    exact NativeRecordLayouts.field_mem_support _ field
  · change Disjoint (Occurrence.request cursor :: writes.map (row generation)).toFinset
      ((Field.all.filter (fun field => field ∉ writes)).map (row generation)).toFinset
    apply Finset.disjoint_left.mpr
    intro occurrence taken read
    obtain ⟨field, notWritten, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp read)
    have absent : field ∉ writes := by simpa using (List.mem_filter.mp notWritten).2
    rcases List.mem_cons.mp (List.mem_toFinset.mp taken) with same | taken
    · cases same
    · obtain ⟨other, written, same⟩ := List.mem_map.mp taken
      have equal := row_injective generation same
      subst other
      exact absent written
  · change Disjoint (Occurrence.request (cursor+1) :: writes.map (nextRow generation)).toFinset
      (canonicalLayout generation cursor).support
    apply Finset.disjoint_left.mpr
    intro occurrence made old
    rcases List.mem_cons.mp (List.mem_toFinset.mp made) with rfl | made
    · have same := (mem_support_request generation cursor (cursor+1)).mp old
      omega
    · obtain ⟨field, _, rfl⟩ := List.mem_map.mp made
      have same := (mem_support_field generation cursor field (generation field+1)).mp old
      omega
  · intro query present
    cases present

theorem admitted_from_view (record : ArithmeticRecord) (state : Store) (generation : Field → Nat)
    (cursor : Nat) (environment : state.frame.Carrier) (number : Nat) (pending : List Event)
    (view : ViewData state (canonicalLayout generation cursor) environment (fields number) cursor pending)
    (locals : (clause record).localFrame.Carrier)
    (same : locals.values = number) (sameCursor : locals.cursor = cursor)
    (samePending : pending = (record, locals.effect) :: locals.tail)
    (valid : (clause record).guard locals.values locals.effect) :
    (RuleSyntax.step (frames Value) Occurrence extensions rules).Admits
      (s := state) (active record state generation cursor) := by
  have fieldSame : ∀ name, fields number name = (clause record).before name locals.values := by
    intro name
    rw [same]
    rfl
  have satisfies := (clause record).satisfies_of_view (member record) state generation cursor environment
    (fields number) pending view locals fieldSame sameCursor samePending valid
  refine ⟨active_shapes record state generation cursor, ?_, ?_,
    (clause record).asks_from_information (member record) state _⟩
  · change Enabled _ state.present ((selectionFor (clause record).writes generation cursor).commit (T := Unit))
    rw [view.exact]
    exact canonical_enabled _ generation cursor
  · exact (InterpretedFrames.solvable_iff _).mpr ⟨(environment, locals), satisfies⟩

private def generation0 : Field → Nat := fun _ => 0
private def arithmeticWord : List Event := [(.addSeven, 7), (.double, 14)]
private def start : Store := initial 0 arithmeticWord generation0 0
private def addLocals : (clause .addSeven).localFrame.Carrier := ⟨0, [(.double, 14)], (0 : Nat), (7 : Nat)⟩

theorem distinct_records : ArithmeticRecord.addSeven ≠ .double := by decide

theorem add_facts : (clause .addSeven).guard addLocals.values addLocals.effect := by
  exact ⟨rfl, rfl⟩

private theorem add_admitted : (RuleSyntax.step (frames Value) Occurrence extensions rules).Admits
    (s := start) (active .addSeven start generation0 0) :=
  admitted_from_view .addSeven start generation0 0 PUnit.unit 0 arithmeticWord
    (initial_view _ _ _ _ _) addLocals rfl rfl rfl add_facts

private def first : ExecutionData rules start PUnit.unit 1 [(.double, 14)] 1 :=
  (clause .addSeven).one_step_execution (member .addSeven) start generation0 0 PUnit.unit (fields 0)
    arithmeticWord (initial_view _ _ _ _ _) addLocals (fun _ => rfl) rfl rfl add_facts add_admitted

private def generation1 : Field → Nat := generationAfter (clause .addSeven).writes generation0
private def doubleLocals : (clause .double).localFrame.Carrier := ⟨1, [], (7 : Nat), (14 : Nat)⟩

theorem double_facts : (clause .double).guard doubleLocals.values doubleLocals.effect := by
  exact ⟨rfl, rfl⟩

private theorem first_view : ViewData first.run.last (canonicalLayout generation1 1)
    first.environment (fields 7) 1 [(.double, 14)] := first.view

private theorem double_admitted : (RuleSyntax.step (frames Value) Occurrence extensions rules).Admits
    (s := first.run.last) (active .double first.run.last generation1 1) :=
  admitted_from_view .double first.run.last generation1 1 first.environment 7 [(.double, 14)]
    first_view doubleLocals rfl rfl rfl double_facts

private def second : ExecutionData rules first.run.last first.environment 2 [] 1 :=
  (clause .double).one_step_execution (member .double) first.run.last generation1 1 first.environment
    (fields 7) [(.double, 14)] first_view doubleLocals (fun _ => rfl) rfl rfl double_facts double_admitted

def arithmeticExecution : ExecutionData rules start PUnit.unit 2 [] 2 :=
  (clause .addSeven).prepend_execution (member .addSeven) start generation0 0 PUnit.unit (fields 0)
    arithmeticWord (initial_view _ _ _ _ _) addLocals (fun _ => rfl) rfl rfl add_facts add_admitted second

theorem arithmetic_fields : arithmeticExecution.fields = fields 14 := rfl

theorem arithmetic_count : arithmeticExecution.run.word.length = 2 := arithmeticExecution.count

theorem arithmetic_old_point :
    arithmeticExecution.run.toLast arithmeticExecution.environment = PUnit.unit := arithmeticExecution.restricts

theorem arithmetic_final_view :
    ViewData arithmeticExecution.run.last arithmeticExecution.layout arithmeticExecution.environment
      (fields 14) 2 [] := arithmeticExecution.view

theorem first_changed_identity : first.layout.field .context = .field .context 1 := rfl

theorem second_uses_changed_identity :
    .field .context 1 ∈ (active .double first.run.last generation1 1).selection.taken ∧
      .field .context 0 ∉ (active .double first.run.last generation1 1).selection.taken := by decide

theorem arithmetic_frames_extend :
    first.run.last.frame = extend start.frame (clause .addSeven).localFrame ∧
      arithmeticExecution.run.last.frame = extend first.run.last.frame (clause .double).localFrame := ⟨rfl, rfl⟩

theorem arithmetic_actual_labels :
    start.label ((canonicalLayout generation0 0).field .context) PUnit.unit = .field .context 0 ∧
    first.run.last.label (first.layout.field .context) first.environment = .field .context 7 ∧
    arithmeticExecution.run.last.label (arithmeticExecution.layout.field .context)
      arithmeticExecution.environment = .field .context 14 :=
  ⟨rfl, first_view.field .context, arithmetic_final_view.field .context⟩

theorem knowledge_grows (record : ArithmeticRecord) (state : Store) (generation : Field → Nat) (cursor : Nat) :
    state.knowledge.length < ((active record state generation cursor).result (frames Value) state).knowledge.length := by
  change state.knowledge.length < ((active record state generation cursor).information (frames Value) state).length
  simp only [RuleSyntax.Firing.information, List.length_append, Frames.applyStore, List.length_map]
  have told : ((active record state generation cursor).opened (frames Value)).tell.length = 1 := rfl
  omega

theorem arithmetic_knowledge_accumulates :
    start.knowledge.length < first.run.last.knowledge.length ∧
      first.run.last.knowledge.length < arithmeticExecution.run.last.knowledge.length :=
  ⟨knowledge_grows .addSeven start generation0 0, knowledge_grows .double first.run.last generation1 1⟩

private def reallocatedFirst : ExecutionData rules start PUnit.unit 1 [(.double, 14)] 1 :=
  (clause .addSeven).one_step_at_execution (member .addSeven) start (canonicalLayout generation0 0) 0
    PUnit.unit (fields 0) arithmeticWord (initial_view _ _ _ _ _) addLocals (fun _ => rfl) rfl rfl add_facts

private def reallocatedSecond : ExecutionData rules reallocatedFirst.run.last reallocatedFirst.environment 2 [] 1 :=
  (clause .double).one_step_at_execution (member .double) reallocatedFirst.run.last reallocatedFirst.layout 1
    reallocatedFirst.environment (fields 7) [(.double, 14)] reallocatedFirst.view doubleLocals
    (fun _ => rfl) rfl rfl double_facts

def reallocatedArithmeticExecution : ExecutionData rules start PUnit.unit 2 [] 2 :=
  (clause .addSeven).prepend_at_execution (member .addSeven) start (canonicalLayout generation0 0) 0
    PUnit.unit (fields 0) arithmeticWord (initial_view _ _ _ _ _) addLocals (fun _ => rfl) rfl rfl
    add_facts reallocatedSecond

theorem reallocated_field_uses_request_identity : reallocatedFirst.layout.field .context = .request 2 := by
  decide +kernel

theorem reallocated_second_consumes_changed_identity :
    .request 2 ∈ (selectionAt reallocatedFirst.layout (clause .double).writes
      (NativeRecordLayouts.allocate reallocatedFirst.layout (clause .double).writes)).taken := by
  rw [show (clause .double).writes = [.context] from rfl]
  simp only [selectionAt, List.map_cons, List.map_nil, List.mem_cons]
  exact Or.inr (Or.inl reallocated_field_uses_request_identity.symm)

theorem reallocated_actual_final_label :
    reallocatedArithmeticExecution.run.word.length = 2 ∧
    reallocatedArithmeticExecution.run.last.label (reallocatedArithmeticExecution.layout.field .context)
      reallocatedArithmeticExecution.environment = .field .context 14 ∧
    reallocatedArithmeticExecution.run.toLast reallocatedArithmeticExecution.environment = PUnit.unit :=
  ⟨reallocatedArithmeticExecution.count, reallocatedArithmeticExecution.view.field .context,
    reallocatedArithmeticExecution.restricts⟩

def UniformView (state : Store) (generation : Field → Nat) (cursor number : Nat) (pending : List Event) : Prop :=
  ∀ environment, Satisfies state.knowledge environment →
    ViewData state (canonicalLayout generation cursor) environment (fields number) cursor pending

theorem initial_uniform (number : Nat) (pending : List Event) (generation : Field → Nat) (cursor : Nat) :
    UniformView (initial number pending generation cursor) generation cursor number pending :=
  fun environment _ => initial_view number pending generation cursor environment

theorem solution_input (record : ArithmeticRecord) (state : Store) (generation : Field → Nat)
    (cursor number : Nat) (pending : List Event)
    (uniform : UniformView state generation cursor number pending)
    (admitted : (RuleSyntax.step (frames Value) Occurrence extensions rules).Admits
      (s := state) (active record state generation cursor))
    (environment : (extend state.frame (clause record).localFrame).Carrier)
    (satisfied : Satisfies ((active record state generation cursor).information (frames Value) state) environment) :
    (clause record).InputData state (canonicalLayout generation cursor) (fields number) cursor pending
      environment.2 (selectionFor (clause record).writes generation cursor) := by
  have information := ((clause record).information_iff (member record) state _ environment).mp satisfied
  exact (clause record).input_inversion state (canonicalLayout generation cursor) environment.1 (fields number)
    cursor pending (uniform environment.1 information.1) environment.2 _
    (by simp [QueueClause.rule, selectionFor]) (by simp [QueueClause.rule, selectionFor])
    admitted.2.1 information.2.1 information.2.2.1

theorem result_uniform (record : ArithmeticRecord) (state : Store) (generation : Field → Nat)
    (cursor number effectValue : Nat) (tail : List Event)
    (uniform : UniformView state generation cursor number ((record, effectValue) :: tail))
    (admitted : (RuleSyntax.step (frames Value) Occurrence extensions rules).Admits
      (s := state) (active record state generation cursor)) :
    UniformView ((active record state generation cursor).result (frames Value) state)
      (generationAfter (clause record).writes generation) (cursor+1) (arithmetic record number) tail := by
  intro environment satisfied
  have information := ((clause record).information_iff (member record) state _ environment).mp satisfied
  have oldView := uniform environment.1 information.1
  have inverted := solution_input record state generation cursor number _ uniform admitted environment satisfied
  have numberSame : environment.2.values = number := by
    have equal := inverted.fieldsSame .context
    change number = environment.2.values at equal
    exact equal.symm
  have tailSame : environment.2.tail = tail := (congrArg List.tail inverted.pendingSame).symm
  have resultView := (clause record).result_view (member record) state generation cursor admitted
    environment satisfied (fields number) ((record, effectValue) :: tail) oldView
  change ViewData _ _ environment (fields (arithmetic record environment.2.values)) _ environment.2.tail at resultView
  rw [numberSame, tailSame] at resultView
  exact resultView

theorem empty_pending_refused (record : ArithmeticRecord) (state : Store) (generation : Field → Nat)
    (cursor number : Nat) (uniform : UniformView state generation cursor number []) :
    ¬ (RuleSyntax.step (frames Value) Occurrence extensions rules).Admits
      (s := state) (active record state generation cursor) := by
  intro admitted
  obtain ⟨environment, satisfied⟩ := (InterpretedFrames.solvable_iff _).mp admitted.2.2.1
  have inverted := solution_input record state generation cursor number [] uniform admitted environment satisfied
  cases inverted.pendingSame

theorem initial_invalid_refused (record : ArithmeticRecord) (number effectValue : Nat)
    (generation : Field → Nat) (cursor : Nat)
    (invalid : ¬ (effectValue = arithmetic record number ∧ permitted record number)) :
    ¬ (RuleSyntax.step (frames Value) Occurrence extensions rules).Admits
      (s := initial number [(record, effectValue)] generation cursor)
      (active record (initial number [(record, effectValue)] generation cursor) generation cursor) := by
  intro admitted
  obtain ⟨environment, satisfied⟩ := (InterpretedFrames.solvable_iff _).mp admitted.2.2.1
  have inverted := solution_input record _ generation cursor number [(record, effectValue)]
    (initial_uniform _ _ _ _) admitted environment satisfied
  have information := ((clause record).information_iff (member record) _ _ environment).mp satisfied
  have numberSame : environment.2.values = number := by
    have equal := inverted.fieldsSame .context
    change number = environment.2.values at equal
    exact equal.symm
  have effectSame : effectValue = environment.2.effect :=
    congrArg Prod.snd (List.cons.inj inverted.pendingSame).1
  have valid := information.2.2.2
  change environment.2.effect = arithmetic record environment.2.values ∧
    permitted record environment.2.values at valid
  apply invalid
  simpa only [numberSame, ← effectSame] using valid

theorem wrong_result_refused :
    ¬ (RuleSyntax.step (frames Value) Occurrence extensions rules).Admits
      (s := initial 0 [(.addSeven, 8)] generation0 0)
      (active .addSeven (initial 0 [(.addSeven, 8)] generation0 0) generation0 0) :=
  initial_invalid_refused .addSeven 0 8 generation0 0 (by decide)

theorem denied_permission_refused :
    ¬ (RuleSyntax.step (frames Value) Occurrence extensions rules).Admits
      (s := initial 1 [(.addSeven, 8)] generation0 0)
      (active .addSeven (initial 1 [(.addSeven, 8)] generation0 0) generation0 0) :=
  initial_invalid_refused .addSeven 1 8 generation0 0 (by decide)

theorem initial_wrong_record_refused (record queued : ArithmeticRecord) (number effectValue : Nat)
    (generation : Field → Nat) (cursor : Nat) (different : queued ≠ record) :
    ¬ (RuleSyntax.step (frames Value) Occurrence extensions rules).Admits
      (s := initial number [(queued, effectValue)] generation cursor)
      (active record (initial number [(queued, effectValue)] generation cursor) generation cursor) := by
  intro admitted
  obtain ⟨environment, satisfied⟩ := (InterpretedFrames.solvable_iff _).mp admitted.2.2.1
  have inverted := solution_input record _ generation cursor number [(queued, effectValue)]
    (initial_uniform _ _ _ _) admitted environment satisfied
  exact different (congrArg Prod.fst (List.cons.inj inverted.pendingSame).1)

theorem genuinely_distinct_clauses :
    (RuleSyntax.step (frames Value) Occurrence extensions rules).Admits
      (s := start) (active .addSeven start generation0 0) ∧
    ¬ (RuleSyntax.step (frames Value) Occurrence extensions rules).Admits
      (s := initial 0 [(.addSeven, 7)] generation0 0)
      (active .double (initial 0 [(.addSeven, 7)] generation0 0) generation0 0) :=
  ⟨add_admitted, initial_wrong_record_refused .double .addSeven 0 7 generation0 0 (by decide)⟩

private theorem first_uniform : UniformView first.run.last generation1 1 7 [(.double, 14)] :=
  result_uniform .addSeven start generation0 0 0 7 [(.double, 14)]
    (initial_uniform _ _ _ _) add_admitted

private def generation2 : Field → Nat := generationAfter (clause .double).writes generation1

theorem arithmetic_uniform_final : UniformView arithmeticExecution.run.last generation2 2 14 [] :=
  result_uniform .double first.run.last generation1 1 7 14 [] first_uniform double_admitted

theorem arithmetic_exhausted (record : ArithmeticRecord) :
    ¬ (RuleSyntax.step (frames Value) Occurrence extensions rules).Admits
      (s := arithmeticExecution.run.last) (active record arithmeticExecution.run.last generation2 2) :=
  empty_pending_refused record _ generation2 2 14 arithmetic_uniform_final

private def neutralWord : List Event := [(.neutral, 14), (.neutral, 14)]
private def neutralStart : Store := initial 14 neutralWord generation0 0
private def neutralLocals0 : (clause .neutral).localFrame.Carrier :=
  ⟨0, [(.neutral, 14)], (14 : Nat), (14 : Nat)⟩
private def neutralLocals1 : (clause .neutral).localFrame.Carrier := ⟨1, [], (14 : Nat), (14 : Nat)⟩

private theorem neutral_admitted0 : (RuleSyntax.step (frames Value) Occurrence extensions rules).Admits
    (s := neutralStart) (active .neutral neutralStart generation0 0) :=
  admitted_from_view .neutral neutralStart generation0 0 PUnit.unit 14 neutralWord (initial_view _ _ _ _ _)
    neutralLocals0 rfl rfl rfl ⟨rfl, trivial⟩

private def neutralFirst : ExecutionData rules neutralStart PUnit.unit 1 [(.neutral, 14)] 1 :=
  (clause .neutral).one_step_execution (member .neutral) neutralStart generation0 0 PUnit.unit (fields 14)
    neutralWord (initial_view _ _ _ _ _) neutralLocals0 (fun _ => rfl) rfl rfl ⟨rfl, trivial⟩ neutral_admitted0

private theorem neutral_first_view : ViewData neutralFirst.run.last (canonicalLayout generation0 1)
    neutralFirst.environment (fields 14) 1 [(.neutral, 14)] := neutralFirst.view

private theorem neutral_admitted1 : (RuleSyntax.step (frames Value) Occurrence extensions rules).Admits
    (s := neutralFirst.run.last) (active .neutral neutralFirst.run.last generation0 1) :=
  admitted_from_view .neutral neutralFirst.run.last generation0 1 neutralFirst.environment 14 [(.neutral, 14)]
    neutral_first_view neutralLocals1 rfl rfl rfl ⟨rfl, trivial⟩

private def neutralSecond : ExecutionData rules neutralFirst.run.last neutralFirst.environment 2 [] 1 :=
  (clause .neutral).one_step_execution (member .neutral) neutralFirst.run.last generation0 1 neutralFirst.environment
    (fields 14) [(.neutral, 14)] neutral_first_view neutralLocals1 (fun _ => rfl) rfl rfl
    ⟨rfl, trivial⟩ neutral_admitted1

def neutralExecution : ExecutionData rules neutralStart PUnit.unit 2 [] 2 :=
  (clause .neutral).prepend_execution (member .neutral) neutralStart generation0 0 PUnit.unit (fields 14)
    neutralWord (initial_view _ _ _ _ _) neutralLocals0 (fun _ => rfl) rfl rfl
    ⟨rfl, trivial⟩ neutral_admitted0 neutralSecond

theorem neutral_consumes_two_identical_requests : neutralExecution.run.word.length = 2 ∧
    ViewData neutralExecution.run.last neutralExecution.layout neutralExecution.environment (fields 14) 2 [] :=
  ⟨neutralExecution.count, neutralExecution.view⟩

theorem neutral_retains_field_ids : ∀ field,
    neutralFirst.layout.field field = (canonicalLayout generation0 0).field field ∧
    neutralExecution.layout.field field = (canonicalLayout generation0 0).field field := fun _ => ⟨rfl, rfl⟩

theorem neutral_requests_are_distinct :
    neutralFirst.layout.request = .request 1 ∧ neutralExecution.layout.request = .request 2 := ⟨rfl, rfl⟩

theorem neutral_frames_extend :
    neutralFirst.run.last.frame = extend neutralStart.frame (clause .neutral).localFrame ∧
    neutralExecution.run.last.frame = extend neutralFirst.run.last.frame (clause .neutral).localFrame := ⟨rfl, rfl⟩

theorem neutral_knowledge_accumulates :
    neutralStart.knowledge.length < neutralFirst.run.last.knowledge.length ∧
      neutralFirst.run.last.knowledge.length < neutralExecution.run.last.knowledge.length :=
  ⟨knowledge_grows .neutral neutralStart generation0 0,
    knowledge_grows .neutral neutralFirst.run.last generation0 1⟩

theorem neutral_old_point : neutralExecution.run.toLast neutralExecution.environment = PUnit.unit :=
  neutralExecution.restricts

private theorem neutral_uniform_first : UniformView neutralFirst.run.last generation0 1 14 [(.neutral, 14)] :=
  result_uniform .neutral neutralStart generation0 0 14 14 [(.neutral, 14)]
    (initial_uniform _ _ _ _) neutral_admitted0

theorem neutral_uniform_final : UniformView neutralExecution.run.last generation0 2 14 [] :=
  result_uniform .neutral neutralFirst.run.last generation0 1 14 14 [] neutral_uniform_first neutral_admitted1

theorem neutral_exhausted (record : ArithmeticRecord) :
    ¬ (RuleSyntax.step (frames Value) Occurrence extensions rules).Admits
      (s := neutralExecution.run.last) (active record neutralExecution.run.last generation0 2) :=
  empty_pending_refused record _ generation0 2 14 neutral_uniform_final

end

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeRecordRunsControls
