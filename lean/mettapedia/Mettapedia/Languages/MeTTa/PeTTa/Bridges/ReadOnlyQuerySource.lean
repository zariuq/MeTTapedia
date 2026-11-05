import Mettapedia.Languages.MeTTa.PeTTa.Bridges.QueryRegionExtraction

/-!
# Read-dependent certificates for complete PeTTa query answers

Certificates retain every ordered answer and every consulted space snapshot.
Their constructors compose actual evaluator paths, including row-local body
bindings and authored call selection. Read validity is required in the state
where a certificate is used; unrelated state can differ.

This extends zero-or-one pure body extraction to nested reads and multiple
answers. It does not permit effects, claim a join implementation, or identify
source pages with completed observations. Preparation and snapshot comparison
remain real costs. These laws use the existing `Eval` profile; correspondence
with the separate two-way-unifying profile and concurrent mutation is not
inferred from them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ReadOnlyQuerySource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.GSLT.Dynamics ObservationQualified
open Eval SpaceSemantics

abbrev Reading := Atom × List Atom

def Valid (reads : List Reading) (state : Effects.State) : Prop :=
  ∀ reading ∈ reads, (Effects.readHandle reading.1 >>= state.read) = some reading.2

instance (reads : List Reading) (state : Effects.State) : Decidable (Valid reads state) :=
  inferInstanceAs (Decidable (∀ reading ∈ reads, (Effects.readHandle reading.1 >>= state.read) = some reading.2))

@[simp] theorem valid_nil (state : Effects.State) : Valid [] state := by simp [Valid]

@[simp] theorem valid_append (first second : List Reading) (state : Effects.State) :
    Valid (first ++ second) state ↔ Valid first state ∧ Valid second state := by
  simp [Valid, List.mem_append, or_imp, forall_and]

@[simp] theorem valid_singleton (space : Atom) (rows : List Atom) (state : Effects.State) :
    Valid [(space, rows)] state ↔ (Effects.readHandle space >>= state.read) = some rows := by simp [Valid]

@[simp] theorem valid_dedup (reads : List Reading) (state : Effects.State) :
    Valid reads.dedup state ↔ Valid reads state := by simp [Valid]

structure Certified (program : Program) (caller : Subst) (source : Atom) where
  reads : List Reading
  values : List Atom
  returns : ∀ state, Valid reads state → Returns program caller state source state values

/-- Duplicate validity requirements can be shared. Source answers and read
occurrence counts are not quotiented by this metadata normalization. -/
def Certified.normalize {program : Program} {caller : Subst} {source : Atom}
    (compiled : Certified program caller source) : Certified program caller source where
  reads := compiled.reads.dedup
  values := compiled.values
  returns state valid := compiled.returns state ((valid_dedup compiled.reads state).mp valid)

def fromOptional {program : Program} {caller : Subst} {source : Atom}
    (compiled : OptionalCallExtraction.Certified program caller source) : Certified program caller source :=
  ⟨[], compiled.value.toList, fun state _ => compiled.returns state⟩

def fromPure {program : Program} {caller : Subst} {source : Atom}
    (compiled : PureCallExtraction.Certified program caller source) : Certified program caller source :=
  ⟨[], [compiled.value], fun state _ => compiled.returns state⟩

structure Single (program : Program) (caller : Subst) (source : Atom) where
  compiled : Certified program caller source
  value : Atom
  singleton : compiled.values = [value]

def single {program : Program} {caller : Subst} {source : Atom}
    (compiled : Certified program caller source) : Option (Single program caller source) :=
  match values : compiled.values with
  | [value] => some ⟨compiled, value, values⟩
  | _ => none

theorem Single.returns {program : Program} {caller : Subst} {source : Atom}
    (one : Single program caller source) (state : Effects.State) (valid : Valid one.compiled.reads state) :
    PureReturns program caller state source state one.value := by
  simpa only [one.singleton] using one.compiled.returns state valid

structure Alternatives (program : Program) (controls : List Control) where
  reads : List Reading
  values : List Atom
  returns : ∀ state collected, Valid reads state → (theory program).MultiStep
    {state, control := .sequence controls collected} (finished state (collected ++ values) [] [])

def Alternatives.nil (program : Program) : Alternatives program [] where
  reads := []
  values := []
  returns state collected _ := by
    simpa using (.step (step_transition rfl) (.refl _) : (theory program).MultiStep
      {state, control := .sequence [] collected} (finished state collected [] []))

def Alternatives.cons {program : Program} {caller : Subst} {source : Atom} {controls : List Control}
    (first : Certified program caller source) (rest : Alternatives program controls) :
    Alternatives program (.evaluate caller source :: controls) where
  reads := first.reads ++ rest.reads
  values := first.values ++ rest.values
  returns state collected valid := by
    obtain ⟨headValid, tailValid⟩ := (valid_append _ _ _).mp valid
    simpa [List.append_assoc] using sequence_cons_answers program state state state
      (.evaluate caller source) controls collected first.values ((collected ++ first.values) ++ rest.values)
      (first.returns state headValid) (rest.returns state (collected ++ first.values) tailValid)

private theorem path_trans {system : Mettapedia.GSLT.GSLT} {a b c : system.Term}
    (first : system.MultiStep a b) (second : system.MultiStep b c) : system.MultiStep a c := by
  induction first with
  | refl _ => exact second
  | step step _ ih => exact .step step (ih second)

def query {program : Program} {caller : Subst} {space pattern body : Atom}
    (location : Single program caller space) (rows : List Atom)
    (bodies : Alternatives program (queryBodies caller rows pattern body)) :
    Certified program caller (.expression [.symbol "match", space, pattern, body]) where
  reads := location.compiled.reads ++ [(location.value, rows)] ++ bodies.reads
  values := bodies.values
  returns state valid := by
    have parts : Valid location.compiled.reads state ∧
        (Effects.readHandle location.value >>= state.read) = some rows ∧ Valid bodies.reads state := by
      simpa only [valid_append, valid_singleton, and_assoc] using valid
    refine .step (step_transition rfl) (path_trans
      (path_with_caller_frames program [.query caller pattern body] (location.returns state parts.1)) ?_)
    refine .step (step_transition rfl) ?_
    simp only [withFrames, finished, List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    change (theory program).MultiStep
      {state, control := .sequence (queryAlternatives state caller location.value pattern body) []}
      (finished state bodies.values [] [])
    simp only [queryAlternatives, parts.2.1]
    simpa using bodies.returns state [] parts.2.2

def collapse {program : Program} {caller : Subst} {source : Atom}
    (compiled : Certified program caller source) :
    Certified program caller (.expression [.symbol "collapse", source]) :=
  ⟨compiled.reads, [.expression compiled.values], fun state valid =>
    collapse_returns program caller state state source compiled.values (compiled.returns state valid)⟩

def branch {program : Program} {caller : Subst} {test yes no : Atom}
    (condition : Single program caller test) (flag : Bool) (boolean : condition.value = Effects.boolean flag)
    (chosen : Certified program caller (if flag then yes else no)) :
    Certified program caller (.expression [.symbol "if", test, yes, no]) where
  reads := condition.compiled.reads ++ chosen.reads
  values := chosen.values
  returns state valid := by
    obtain ⟨conditionValid, chosenValid⟩ := (valid_append _ _ _).mp valid
    have tested := condition.returns state conditionValid
    rw [boolean] at tested
    refine .step (step_transition rfl)
      (path_trans (path_with_caller_frames program [.branch caller yes no] tested) ?_)
    refine .step ?_ (single_sequence_answers program state state _ chosen.values (chosen.returns state chosenValid))
    apply step_transition
    cases flag <;> simp [step, withFrames, finished, Effects.boolean]

def size {program : Program} {caller : Subst} {source : Atom}
    (argument : Single program caller source) (values : List Atom) (expression : argument.value = .expression values) :
    Certified program caller (.expression [.symbol "size-atom", source]) where
  reads := argument.compiled.reads
  values := [.grounded (.int values.length)]
  returns state valid := by
    apply native_unary_call_returns program caller state state state "size-atom" source
      (.expression values) (.grounded (.int values.length)) (by decide) (by decide)
      (by simp [argumentIsRaw, StdLib.known, StdLib.rawArgument]) _ rfl (by decide)
    simpa only [expression] using argument.returns state valid

open Mettapedia.Machines.TypedScalar in
def binary {program : Program} {caller : Subst} {left right : Atom}
    (head : String) (first : Single program caller left) (second : Single program caller right) :
    Option (Certified program caller (.expression [.symbol head, left, right])) := do
  match leftDecoded : PureCallExtraction.decode first.value with
  | none => none
  | some x =>
    match rightDecoded : PureCallExtraction.decode second.value with
    | none => none
    | some y =>
      let ⟨kind, op⟩ ← ScalarSource.selectBinary head x.1 y.1
      if same : op.name = head then
        if _clear : ScalarSource.Clear program head then
          match computed : op.eval x.2 y.2 with
          | none => none
          | some value =>
              return ⟨first.compiled.reads ++ second.compiled.reads, [ScalarSource.encode value], fun state valid => by
                obtain ⟨firstValid, secondValid⟩ := (valid_append _ _ _).mp valid
                subst head
                exact PureCallExtraction.binary_returns op program caller state left right x.2 y.2 value
                  (by rw [← PureCallExtraction.decode_exact first.value x leftDecoded]; exact first.returns state firstValid)
                  (by rw [← PureCallExtraction.decode_exact second.value y rightDecoded]; exact second.returns state secondValid)
                  computed⟩
        else none
      else none

structure Arguments (program : Program) (caller : Subst) (sources : List Atom) where
  reads : List Reading
  values : List Atom
  returns : ∀ state, Valid reads state → List.Forall₂
    (fun source value => PureReturns program caller state source state value) sources values

def Arguments.nil (program : Program) (caller : Subst) : Arguments program caller [] :=
  ⟨[], [], fun _ _ => .nil⟩

def Arguments.cons {program : Program} {caller : Subst} {source : Atom} {sources : List Atom}
    (first : Single program caller source) (rest : Arguments program caller sources) :
    Arguments program caller (source :: sources) :=
  ⟨first.compiled.reads ++ rest.reads, first.value :: rest.values, fun state valid =>
    .cons (first.returns state ((valid_append _ _ _).mp valid).1)
      (rest.returns state ((valid_append _ _ _).mp valid).2)⟩

def call {program : Program} {caller : Subst} {head : String} {sources : List Atom} {controls : List Control}
    (admitted : PureCallExtraction.Callable program head sources.length)
    (arguments : Arguments program caller sources)
    (selected : application program head arguments.values = .sequence controls [])
    (bodies : Alternatives program controls) : Certified program caller (.expression (.symbol head :: sources)) where
  reads := arguments.reads ++ bodies.reads
  values := bodies.values
  returns state valid := by
    obtain ⟨argumentValid, bodiesValid⟩ := (valid_append _ _ _).mp valid
    apply call_answers program caller state state head sources bodies.values
      (by simp [admitted.registered]) _ admitted.ordinary
    apply OptionalCallExtraction.evaluated_arguments_answers program caller state head sources arguments.values
      (arguments.returns state argumentValid) [] 0 bodies.values (by simpa using admitted.demanded)
    have rest := bodies.returns state [] bodiesValid
    simp only [List.nil_append] at rest
    refine .step ?_ rest
    apply step_transition
    simp only [step, admitted.notIO, admitted.notNative, Bool.false_eq_true, ↓reduceIte,
      List.nil_append, selected]

theorem data_arguments (program : Program) (caller : Subst) (state : Effects.State)
    (sources values : List Atom)
    (returns : List.Forall₂ (fun source value => PureReturns program caller state source state value) sources values)
    (prior : List Atom) (index : Nat) :
    (theory program).MultiStep {state, control := .arguments caller .data sources prior index}
      (finished state [.expression (prior ++ values)] [] []) := by
  induction returns generalizing prior index with
  | nil => simpa using data_arguments_values_return program caller state prior index
  | @cons source value sources values first later ih =>
      apply evaluated_argument_returns program caller state state state .data source value
        (.expression (prior ++ value :: values)) sources prior index rfl first
      simpa [List.append_assoc] using ih (prior ++ [value]) (index + 1)

def data {program : Program} {caller : Subst} {head : String} {sources : List Atom}
    (inert : (ioHead head || StdLib.known head || program.equations.any (·.head == head)) = false)
    (ordinary : head ∉ ["let", "let*", "case", "if", "collapse", "superpose", "empty", "quote", "unique"])
    (arguments : Arguments program caller sources) : Certified program caller (.expression (.symbol head :: sources)) where
  reads := arguments.reads
  values := [.expression (.symbol head :: arguments.values)]
  returns state valid := by
    apply data_call_returns program caller state state head sources _ inert _ ordinary
    simpa using data_arguments program caller state (.symbol head :: sources) (.symbol head :: arguments.values)
      (.cons (symbol_returns program caller state head) (arguments.returns state valid)) [] 0

def quoted (program : Program) (caller : Subst) (value : Atom) :
    Certified program caller (.expression [.symbol "quote", value]) :=
  ⟨[], [Mettapedia.Languages.ProcessCalculi.MORK.applySubst caller value], fun state _ =>
    quote_returns program caller state value⟩

def superpose {program : Program} {caller : Subst} {sources : List Atom}
    (bodies : Alternatives program (sources.map (.evaluate caller))) :
    Certified program caller (.expression [.symbol "superpose", .expression sources]) where
  reads := bodies.reads
  values := bodies.values
  returns state valid := .step (step_transition rfl) (by simpa using bodies.returns state [] valid)

def bind {program : Program} {caller bound : Subst} {pattern value body : Atom}
    (argument : Single program caller value)
    (matched : matchBinding caller pattern argument.value = some bound)
    (compiled : Certified program bound body) :
    Certified program caller (.expression [.symbol "let", pattern, value, body]) where
  reads := argument.compiled.reads ++ compiled.reads
  values := compiled.values
  returns state valid := by
    obtain ⟨argumentValid, bodyValid⟩ := (valid_append _ _ _).mp valid
    refine .step (step_transition rfl) (path_trans
      (path_with_caller_frames program [.bind caller pattern body] (argument.returns state argumentValid)) ?_)
    refine .step ?_ (single_sequence_answers program state state (.evaluate bound body) compiled.values
      (compiled.returns state bodyValid))
    apply step_transition
    simp [withFrames, finished, step, matched]

def nestedLets {program : Program} {caller : Subst} {pairs : List Atom} {body nested : Atom}
    (expanded : Eval.nestedLets pairs body = some nested)
    (compiled : Certified program caller nested) :
    Certified program caller (.expression [.symbol "let*", .expression pairs, body]) where
  reads := compiled.reads
  values := compiled.values
  returns state valid := by
    refine .step ?_ (compiled.returns state valid)
    apply step_transition
    simp [step, expanded]

theorem completed_iff {program : Program} {caller : Subst} {source : Atom}
    (compiled : Certified program caller source) (state : Effects.State) (valid : Valid compiled.reads state)
    (after : Effects.State) (answers input output : List Atom) :
    (∃ fuel, run program fuel {state, control := .evaluate caller source} =
      .complete after answers input output) ↔
      after = state ∧ answers = compiled.values ∧ input = [] ∧ output = [] :=
  path_completed_iff program _ state compiled.values [] [] (compiled.returns state valid) after answers input output

theorem completed_source_exact {program : Program} {caller : Subst} {source : Atom}
    (compiled : Certified program caller source) (state : Effects.State) (valid : Valid compiled.reads state) :
    PureCallPortfolio.sourceMeaning program caller source state =
      {⟨state, compiled.values, [], []⟩} := by
  ext observed
  change DeclarativeSpec.Runs program {state, control := .evaluate caller source}
      (.complete observed.state observed.answers observed.input observed.output) ↔ _
  rw [← completed_run_iff_derivation, completed_iff compiled state valid]
  cases observed
  simp [PureCallPortfolio.Completed.mk.injEq]

def Certified.region {program : Program} {caller : Subst} {source : Atom}
    (compiled : Certified program caller source) :
    CertifiedRegion (PureCallPortfolio.boundary program caller source) Nat where
  regime := 2
  Artifact := PureCallPortfolio.Completed
  attempt state := if Valid compiled.reads state then
    .committed ⟨state, compiled.values, [], []⟩ else .declined state
  decode result := {result}
  restores state restored declined := by
    dsimp only at declined
    split at declined
    · cases declined
    · exact (PartialRegionPlan.Attempt.declined.inj declined).symm
  exact state _ accepted := by
    split at accepted
    next valid => cases accepted; exact (completed_source_exact compiled state valid).symm
    next => cases accepted

theorem stale_read_declines {program : Program} {caller : Subst} {source : Atom}
    (compiled : Certified program caller source) (state : Effects.State) (stale : ¬Valid compiled.reads state) :
    compiled.region.attempt state = .declined state := by simp [Certified.region, stale]

theorem normalized_attempt_exact {program : Program} {caller : Subst} {source : Atom}
    (compiled : Certified program caller source) (state : Effects.State) :
    compiled.normalize.region.attempt state = compiled.region.attempt state := by
  simp only [Certified.region, Certified.normalize, valid_dedup]

theorem reuse_under_same_reads {program : Program} {caller : Subst} {source : Atom}
    (compiled : Certified program caller source) (before after : Effects.State)
    (valid : Valid compiled.reads before)
    (same : ∀ reading ∈ compiled.reads,
      (Effects.readHandle reading.1 >>= after.read) = (Effects.readHandle reading.1 >>= before.read)) :
    compiled.region.attempt after = .committed ⟨after, compiled.values, [], []⟩ := by
  have validAfter : Valid compiled.reads after := fun reading member => (same reading member).trans (valid reading member)
  simp [Certified.region, validAfter]

/-- Program reuse needs agreement on dispatch, argument demand and selected
bodies throughout the admitted source closure, not merely equal answers. -/
def Certified.transport {allowed : String → Bool} {first second : Program}
    {caller : Subst} {source : Atom} (compiled : Certified first caller source)
    (closed : ProgramClosed allowed first) (agreement : ProgramAgreementOn allowed first second)
    (within : codeWithin allowed source = true) : Certified second caller source where
  reads := compiled.reads
  values := compiled.values
  returns state valid := path_of_closed_agreement closed agreement ⟨within, rfl⟩
    (compiled.returns state valid)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ReadOnlyQuerySource
