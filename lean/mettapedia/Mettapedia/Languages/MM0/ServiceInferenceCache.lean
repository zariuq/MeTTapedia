import Mettapedia.GSLT.Dynamics.CacheCoherenceContract
import Mettapedia.Languages.MM0.Kernel.Typing
import Mettapedia.Languages.MM0.Presentation.TypingProgram
import Mettapedia.Languages.MM0.Presentation.InstantiationComputation

/-!
# The MM0 service's inference cache

An abstract model of the state of the direct MM0 service. Term tables are
append-only spaces of rows behind handles. Inference is cached under the key
`(handle, context, expression)`. Submitting a declaration clears the cache and
begins its checks; the term signature does not change during those checks;
admission publishes a fresh row and ends them. A new session starts from empty
tables and a fresh cache.

* The authorized observation is the kernel's expression typing
  (`Kernel.Preterm.infer`) on the signature the rows denote, with a third
  outcome for a lookup that finds two matching rows (`inferRows`,
  `inferRows_eq_kernel`).
* **The service discipline is coherent**: in every reachable state that is
  running checks, a cached inference is the authorized inference
  (`run_good`, `checking_answer_authorized`). The proof uses the epoch steps of
  the shared cache-coherence core: submission clears, checks record, and
  publication ends the epoch.
* **Five controls.**
  1. The same live handle with changed rows: a live handle is not a frozen
     signature (`Controls.live_handle_not_frozen_signature`).
  2. The same expression in another context
     (`Controls.context_belongs_to_key`).
  3. A cached refusal followed by admission of a new constructor, under a
     protocol that does not clear (`Controls.cached_refusal_stale_after_admission`).
  4. Saved evidence reused across theory or session scopes, at the level of the
     authored contract (`Controls.saved_evidence_scoped_to_theory`). At the same
     level, an exhausted run is not a refusal
     (`Controls.exhaustion_is_not_refusal`).
  5. A second matching row turns a unique lookup into a malformed one
     (`Controls.second_row_malformed`); fresh admission prevents it
     (`publishRow_unique`).
* `Realization` is the interface for a concrete service state, for example a
  PeTTa state of named spaces and source primitives: a projection to this
  model that commutes with the commands gives the same guarantee
  (`Realization.answer_authorized`).

A cache space holding two rows for one key is unreachable in this sequential
model: a row is added only after a miss.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.ServiceInferenceCache

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.Languages.MM0.Presentation.ComputationalTyping (SignatureTable signatureOf)
open Mettapedia.GSLT.Dynamics.MemoizationObserver
open Mettapedia.GSLT.Dynamics.CacheCoherence
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.Machines

/-- A term-table handle. -/
abbrev Handle := Nat

/-- A row of a term table: a term index and its declaration. -/
abbrev Row := Nat × TermDecl

/-- The key of the inference cache. -/
abbrev Key := Handle × Context × Preterm

/-! ## Lookups and inference over rows -/

/-- A lookup in a space of rows: no row, one row, or several. -/
inductive Lookup where
  | absent
  | present (declaration : TermDecl)
  | malformed

def lookupRows (rows : List Row) (index : Nat) : Lookup :=
  match rows.filter (fun row => row.1 = index) with
  | [] => .absent
  | [row] => .present row.2
  | _ :: _ :: _ => .malformed

/-- A table admits a fresh row for an index that has none. -/
def fresh (rows : List Row) (index : Nat) : Bool :=
  (rows.filter fun row => row.1 = index).isEmpty

/-- Every lookup in the table finds at most one row. -/
def Unique (rows : List Row) : Prop :=
  ∀ index, (rows.filter fun row => row.1 = index).length ≤ 1

/-- The outcome of an inference over rows. -/
inductive Inferred where
  | malformed
  | refused
  | typed (type : ExpressionType)
  deriving DecidableEq

/-- Expression typing over the rows of a table. A malformed lookup makes the
whole inference malformed. -/
def inferRows (rows : List Row) (context : Context) : Preterm → Inferred
  | .var index =>
      match context[index]? with
      | some binder => .typed ([], binder.sort)
      | none => .refused
  | .term index =>
      match lookupRows rows index with
      | .absent => .refused
      | .present declaration => .typed (declaration.arguments, declaration.resultSort)
      | .malformed => .malformed
  | .app function argument =>
      match inferRows rows context function with
      | .malformed => .malformed
      | .refused => .refused
      | .typed (arguments, result) =>
          match arguments with
          | [] => .refused
          | .bound sort :: remaining =>
              if Preterm.boundSort? context argument = some sort then .typed (remaining, result)
              else .refused
          | .regular sort _ :: remaining =>
              match inferRows rows context argument with
              | .malformed => .malformed
              | .refused => .refused
              | .typed type => if type = ([], sort) then .typed (remaining, result) else .refused

/-- The kernel's outcome, read as an inference outcome. -/
def ofKernel : Option ExpressionType → Inferred
  | none => .refused
  | some type => .typed type

theorem signatureOf_of_filter_nil (index : Nat) :
    ∀ rows : List Row, rows.filter (fun row => row.1 = index) = [] → signatureOf rows index = none
  | [], _ => rfl
  | (key, declaration) :: rest, empty => by
      by_cases same : key = index
      · simp [same] at empty
      · simp only [List.filter_cons, same, decide_false] at empty
        have different : index ≠ key := fun equal => same equal.symm
        simp only [signatureOf, different, ↓reduceIte]
        exact signatureOf_of_filter_nil index rest empty

theorem signatureOf_of_filter_single (index : Nat) :
    ∀ (rows : List Row) (row : Row), rows.filter (fun row => row.1 = index) = [row] →
      signatureOf rows index = some row.2
  | [], _, single => by simp at single
  | (key, declaration) :: rest, row, single => by
      by_cases same : key = index
      · subst same
        simp only [List.filter_cons, decide_true, ↓reduceIte, List.cons.injEq] at single
        obtain ⟨rfl, -⟩ := single
        simp [signatureOf]
      · simp only [List.filter_cons, same, decide_false] at single
        have different : index ≠ key := fun equal => same equal.symm
        simp only [signatureOf, different, ↓reduceIte]
        exact signatureOf_of_filter_single index rest row single

theorem lookupRows_kernel {rows : List Row} (unique : Unique rows) (index : Nat) :
    (lookupRows rows index = .absent ∧ signatureOf rows index = none) ∨
      ∃ declaration, lookupRows rows index = .present declaration ∧
        signatureOf rows index = some declaration := by
  have bounded := unique index
  unfold lookupRows
  split
  · next empty => exact .inl ⟨rfl, signatureOf_of_filter_nil index rows empty⟩
  · next row single => exact .inr ⟨row.2, rfl, signatureOf_of_filter_single index rows row single⟩
  · next first second rest many => rw [many] at bounded; simp at bounded

/-- **On a table with unique keys, inference over rows is the kernel's
typing.** -/
theorem inferRows_eq_kernel {rows : List Row} (unique : Unique rows) (context : Context) :
    ∀ expression, inferRows rows context expression =
      ofKernel (Preterm.infer (signatureOf rows) context expression)
  | .var index => by
      cases lookup : context[index]? <;> simp [inferRows, Preterm.infer, lookup, ofKernel]
  | .term index => by
      rcases lookupRows_kernel unique index with ⟨absent, none⟩ | ⟨declaration, present, some⟩
      · simp [inferRows, Preterm.infer, absent, none, ofKernel]
      · simp [inferRows, Preterm.infer, present, some, ofKernel]
  | .app function argument => by
      have functionEq := inferRows_eq_kernel unique context function
      have argumentEq := inferRows_eq_kernel unique context argument
      simp only [inferRows, Preterm.infer, functionEq]
      cases functionResult : Preterm.infer (signatureOf rows) context function with
      | none => simp [ofKernel]
      | some type =>
          obtain ⟨arguments, result⟩ := type
          cases arguments with
          | nil => simp [ofKernel]
          | cons binder remaining =>
              cases binder with
              | bound sort =>
                  by_cases bound : Preterm.boundSort? context argument = some sort <;>
                    simp [ofKernel, bound]
              | regular sort dependencies =>
                  simp only [ofKernel, argumentEq]
                  cases argumentResult : Preterm.infer (signatureOf rows) context argument with
                  | none => simp
                  | some argumentType =>
                      by_cases typed : argumentType = ([], sort) <;> simp [typed]

/-! ## The service -/

/-- The abstract service state. -/
structure Service where
  session : Nat
  tables : Handle → List Row
  cache : Table Key Inferred
  checking : Bool

/-- The readings of a service: the rows behind every handle. -/
def environment (service : Service) : RevisionEnvironment Handle (List Row) :=
  ⟨service.tables⟩

/-- **The authorized inference** of a key in an environment. -/
def authorized (live : RevisionEnvironment Handle (List Row)) (key : Key) : Inferred :=
  inferRows (live.current key.1) key.2.1 key.2.2

/-- An inference consults the table behind its handle. -/
def consults (_ : RevisionEnvironment Handle (List Row)) (key : Key) : List Handle := [key.1]

theorem authorized_determined : ReadsDetermine authorized consults := by
  intro captured live key agrees
  have same := agrees key.1 (by simp [consults])
  simp only [authorized, same]

/-- The service commands. -/
inductive Command where
  | start (session : Nat)
  | submit
  | check (key : Key)
  | publish (handle : Handle) (row : Row)

/-- Remember an inference after a miss. -/
def remember (service : Service) (key : Key) : Table Key Inferred :=
  match service.cache key with
  | some _ => service.cache
  | none => store id (authorized (environment service)) service.cache key

/-- Append a row when its index is fresh. -/
def publishRow (rows : List Row) (row : Row) : List Row :=
  if fresh rows row.1 then rows ++ [row] else rows

/-- The service transitions. -/
def run (service : Service) : Command → Service
  | .start session => ⟨session, fun _ => [], Table.empty, false⟩
  | .submit => { service with cache := Table.empty, checking := true }
  | .check key => if service.checking then { service with cache := remember service key } else service
  | .publish handle row =>
      { service with
        tables := Function.update service.tables handle (publishRow (service.tables handle) row)
        checking := false }

def runAll (service : Service) (commands : List Command) : Service :=
  commands.foldl run service

/-- The answer of an inference call. -/
def answer (service : Service) (key : Key) : Inferred :=
  lookupOrCompute id (authorized (environment service)) service.cache key

/-- While checks run, the cache is coherent. -/
def Good (service : Service) : Prop :=
  service.checking = true → EpochCoherent environment authorized service service.cache

theorem good_run (service : Service) (good : Good service) (command : Command) :
    Good (run service command) := by
  cases command with
  | start session => intro checking; cases checking
  | submit => intro _; exact coherent_empty _ _
  | check key =>
      intro checking
      by_cases running : service.checking = true
      · have coherent := good running
        have remembered : Coherent id (authorized (environment service)) (remember service key) := by
          unfold remember
          split
          · exact coherent
          · exact epochCoherent_step authorized_determined
              (EpochStep.record (consults := consults) service service.cache key) coherent
        simp only [run, running, ↓reduceIte]
        exact remembered
      · simp [run, running] at checking
  | publish handle row => intro checking; cases checking

theorem run_good (service : Service) (good : Good service) (commands : List Command) :
    Good (runAll service commands) := by
  induction commands generalizing service with
  | nil => exact good
  | cons command rest ih => exact ih (run service command) (good_run service good command)

/-- **While checks run, every cached inference is the authorized
inference.** -/
theorem checking_answer_authorized (service : Service) (good : Good service)
    (commands : List Command) (key : Key)
    (running : (runAll service commands).checking = true) :
    answer (runAll service commands) key =
      authorized (environment (runAll service commands)) key :=
  epoch_lookup (run_good service good commands running) key

/-- A started service is good. -/
theorem good_start (session : Nat) (service : Service) : Good (run service (.start session)) := by
  intro checking
  cases checking

/-- Fresh admission keeps lookups unique. -/
theorem publishRow_unique {rows : List Row} (unique : Unique rows) (row : Row) :
    Unique (publishRow rows row) := by
  unfold publishRow
  split
  · next isFresh =>
      intro index
      rw [List.filter_append]
      by_cases same : row.1 = index
      · have empty : rows.filter (fun row => row.1 = index) = [] := by
          rw [← same]
          simpa [fresh] using isFresh
        simp [empty, same]
      · simpa [same] using unique index
  · exact unique

/-! ## A concrete realization interface -/

/-- **A concrete service state** (for example, a PeTTa state of named spaces
and source primitives) realizes the model when its projection commutes with
every command and its inference answer is the model's answer while checks
run. -/
structure Realization (Concrete : Type) where
  abstract : Concrete → Service
  step : Concrete → Command → Concrete
  answer : Concrete → Key → Inferred
  step_refines : ∀ concrete command, abstract (step concrete command) = run (abstract concrete) command
  answer_refines : ∀ concrete key, (abstract concrete).checking = true →
    answer concrete key = ServiceInferenceCache.answer (abstract concrete) key

namespace Realization

variable {Concrete : Type} (realization : Realization Concrete)

def runAll (concrete : Concrete) (commands : List Command) : Concrete :=
  commands.foldl realization.step concrete

theorem abstract_runAll (concrete : Concrete) (commands : List Command) :
    realization.abstract (realization.runAll concrete commands) =
      ServiceInferenceCache.runAll (realization.abstract concrete) commands := by
  induction commands generalizing concrete with
  | nil => rfl
  | cons command rest ih =>
      simp only [runAll, List.foldl_cons, ServiceInferenceCache.runAll] at ih ⊢
      rw [ih, realization.step_refines]

/-- **The concrete answers are authorized** while checks run. -/
theorem answer_authorized (concrete : Concrete) (good : Good (realization.abstract concrete))
    (commands : List Command) (key : Key)
    (running : (realization.abstract (realization.runAll concrete commands)).checking = true) :
    realization.answer (realization.runAll concrete commands) key =
      authorized (environment (realization.abstract (realization.runAll concrete commands))) key := by
  rw [realization.answer_refines _ key running, realization.abstract_runAll]
  rw [realization.abstract_runAll] at running
  exact checking_answer_authorized _ good commands key running

end Realization

/-- The model realizes itself. -/
def selfRealization : Realization Service where
  abstract := id
  step := run
  answer := answer
  step_refines := fun _ _ => rfl
  answer_refines := fun _ _ _ => rfl

/-! ## Controls -/

namespace Controls

/-- A constant term of sort zero. -/
def constant : TermDecl := ⟨[], 0, ∅⟩

/-- Another declaration for the same index. -/
def otherConstant : TermDecl := ⟨[], 1, ∅⟩

def emptyTables : Handle → List Row := fun _ => []

def withConstant : Handle → List Row := fun handle => if handle = 0 then [(0, constant)] else []

def serviceWith (tables : Handle → List Row) : Service := ⟨0, tables, Table.empty, true⟩

/-- The key of the constant in the empty context. -/
def constantKey : Key := (0, [], .term 0)

/-! ### 1. A live handle is not a frozen signature -/

def liveHandle : NonTrivialFiber (fun point : Service × Key => point.2)
    (fun point => authorized (environment point.1) point.2) where
  left := (serviceWith emptyTables, constantKey)
  right := (serviceWith withConstant, constantKey)
  sameShadow := rfl
  differentValue := by decide

theorem live_handle_not_frozen_signature :
    ¬ SoundKey (fun point : Service × Key => point.2)
      (fun point => authorized (environment point.1) point.2) :=
  fun sound => liveHandle.differentValue (sound _ _ liveHandle.sameShadow)

/-! ### 2. The context belongs to the key -/

def contextFree : NonTrivialFiber (fun key : Key => (key.1, key.2.2))
    (authorized (environment (serviceWith emptyTables))) where
  left := (0, [.regular 0 ∅], .var 0)
  right := (0, [.regular 1 ∅], .var 0)
  sameShadow := rfl
  differentValue := by decide

theorem context_belongs_to_key :
    ¬ SoundKey (fun key : Key => (key.1, key.2.2))
      (authorized (environment (serviceWith emptyTables))) :=
  fun sound => contextFree.differentValue (sound _ _ contextFree.sameShadow)

/-! ### 3. A cached refusal and a later admission -/

/-- The faulty protocol: submission does not clear the cache. -/
def runNoClear (service : Service) : Command → Service
  | .submit => { service with checking := true }
  | command => run service command

/-- Check the constant, admit it, submit the next declaration, check again. -/
def admission : List Command :=
  [.start 0, .submit, .check constantKey, .publish 0 (0, constant), .submit, .check constantKey]

/-- **A cached refusal is stale after admission unless the cache is
cleared.** -/
theorem cached_refusal_stale_after_admission :
    answer (admission.foldl runNoClear (serviceWith emptyTables)) constantKey = .refused ∧
      authorized (environment (admission.foldl runNoClear (serviceWith emptyTables)))
        constantKey = .typed ([], 0) ∧
      answer (runAll (serviceWith emptyTables) admission) constantKey = .typed ([], 0) := by
  decide

/-! ### 4. Saved evidence is scoped to its theory -/

section Saved

open Mettapedia.GSLT.LanguageDef.Authored.Contract
open Mettapedia.GSLT.Dynamics.CacheCoherenceContract
open Mettapedia.Languages.MM0.Presentation.InstantiationComputation

/-- A saved instantiation keyed without its theory. -/
abbrev SavedKey := Context × Context × List Preterm × Preterm

/-- The theory behind handle zero, as signature-table readings. -/
def theoryScope (live : RevisionEnvironment Handle SignatureTable) (key : SavedKey) : Query :=
  ⟨live.current 0, key.1, key.2.1, key.2.2.1, key.2.2.2⟩

def theoryConsults (_ : RevisionEnvironment Handle SignatureTable) (_ : SavedKey) :
    List Handle := [0]

theorem theoryScope_determined : ReadsDetermine theoryScope theoryConsults := by
  intro captured live key agrees
  have same := agrees 0 (by simp [theoryConsults])
  simp only [theoryScope, same]

def declaring : RevisionEnvironment Handle SignatureTable :=
  ⟨fun handle => if handle = 0 then Mettapedia.Languages.MM0.Presentation.InstantiationComputation.withConstant
    else []⟩

def otherScope : RevisionEnvironment Handle SignatureTable := ⟨fun _ => []⟩

def savedEntry : KeyedEntry SavedKey Preterm :=
  ⟨withoutTheory recorded, .term 0, .replayed⟩

/-- **Saved evidence is authorized in its theory and not in another theory or
session.** -/
theorem saved_evidence_scoped_to_theory :
    Authorized authored theoryScope declaring [savedEntry] ∧
      ¬ Authorized authored theoryScope otherScope [savedEntry] := by
  constructor
  · exact authorized_replay authored (authorized_nil authored theoryScope declaring)
      (key := withoutTheory recorded) (answer := .term 0) recorded_instantiates
  · intro holds
    exact asked_refused (holds _ List.mem_cons_self).1

/-- Positive: within a frozen theory the evidence stays authorized and a lookup
returns a related answer. -/
theorem saved_evidence_within_theory :
    authored.relation (theoryScope declaring (withoutTheory recorded)) (.term 0) := by
  apply lookupKey_authorized authored (cache := [savedEntry])
  · have run : Relation.ReflTransGen
        (Mettapedia.GSLT.Dynamics.CacheCoherenceContract.EpochStep authored (fun live => live) theoryScope theoryConsults)
        (declaring, []) (declaring, [savedEntry]) :=
      Relation.ReflTransGen.single
        (.replay declaring [] (withoutTheory recorded) (Preterm.term 0) recorded_instantiates)
    exact authorized_of_reflTransGen authored theoryScope_determined run
      (authorized_nil authored theoryScope declaring)
  · simp [lookupKey, savedEntry]

open Mettapedia.GSLT.LanguageDef.DeterministicEquations in
/-- **Exhaustion is not refusal**: the recorded instantiation exhausts fuel
zero, yet it is answerable, so no run refuses it at any fuel. -/
theorem exhaustion_is_not_refusal :
    apply authored.program authored.host 0 authored.head (authored.encodeQuery recorded) =
        .exhausted ∧
      ¬ Applies authored.program authored.host authored.head (authored.encodeQuery recorded)
        (authored.encodeAnswer none) :=
  ⟨rfl, answerable_has_no_refusal authored recorded_instantiates⟩

/-- Positive: with enough fuel the same query runs to its answer. -/
theorem enough_fuel_answers : ∃ fuel, authored.runs ⟨recorded, .term 0, fuel⟩ = true := by
  obtain ⟨fuel, enough⟩ := authored.runs_of_relation recorded_instantiates
  exact ⟨fuel, enough fuel le_rfl⟩

end Saved

/-! ### 5. A second matching row -/

def duplicated : Handle → List Row :=
  fun handle => if handle = 0 then [(0, constant), (0, otherConstant)] else []

/-- **A second matching row turns a unique lookup into a malformed one.** -/
theorem second_row_malformed :
    authorized (environment (serviceWith withConstant)) constantKey = .typed ([], 0) ∧
      authorized (environment (serviceWith duplicated)) constantKey = .malformed := by
  decide

/-- Positive: fresh admission refuses the second row. -/
theorem fresh_admission_refuses_duplicate :
    publishRow [(0, constant)] (0, otherConstant) = [(0, constant)] := rfl

/-- Positive: on unique rows, inference is the kernel's typing. -/
theorem constant_kernel_typing :
    authorized (environment (serviceWith withConstant)) constantKey =
      ofKernel (Preterm.infer (signatureOf [(0, constant)]) [] (.term 0)) := by
  decide

end Controls

#print axioms inferRows_eq_kernel
#print axioms authorized_determined
#print axioms run_good
#print axioms checking_answer_authorized
#print axioms publishRow_unique
#print axioms Realization.answer_authorized
#print axioms Controls.live_handle_not_frozen_signature
#print axioms Controls.context_belongs_to_key
#print axioms Controls.cached_refusal_stale_after_admission
#print axioms Controls.saved_evidence_scoped_to_theory
#print axioms Controls.saved_evidence_within_theory
#print axioms Controls.exhaustion_is_not_refusal
#print axioms Controls.enough_fuel_answers
#print axioms Controls.second_row_malformed
#print axioms Controls.fresh_admission_refuses_duplicate
#print axioms Controls.constant_kernel_typing

end Mettapedia.Languages.MM0.ServiceInferenceCache
