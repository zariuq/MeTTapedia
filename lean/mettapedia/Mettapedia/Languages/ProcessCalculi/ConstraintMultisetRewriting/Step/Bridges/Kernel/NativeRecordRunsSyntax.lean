import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.Kernel.NativeReceivedFrame

/-!
# A constrained-information queue profile for native record runs

The five axes are: store: bag; commit: one match; guards: after firing's own
tells; rules: fixed; one store.

This named profile is a different source-run representation from the
prepared-certificate program. Each rule consumes one explicit input request,
including a state-neutral request. Its fresh locals retain every solution of
the actual case, result and fixed-permission constraints. No first-success
selection, prepared-certificate replacement, native effect producer or native
consumer implementation is supplied here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeRecordRuns

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.Languages.HOLLight
open NativeClauseData NativeFieldSchema InterpretedFrames

universe u v w

attribute [local irreducible] NativeClauseData.signature

abbrev Event (ops : Operations) (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :=
  (signature ops).Record model × (signature ops).State model

inductive AtomData (Cell : Field → Type u) (Event : Type v) : Type (max u v)
  | field (name : Field) (value : Cell name)
  | pending (cursor : Nat) (events : List Event)
  | proposition (value : Prop)

abbrev Atom (ops : Operations) (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) :=
  AtomData (fun name => HOL.Ty.denote.{0,w+1} model.Carrier (name.type ops)) (Event ops model)

inductive Occurrence where
  | field (name : Field) (generation : Nat)
  | request (cursor : Nat)
  deriving DecidableEq, Repr

structure LocalData (Valuation : Type u) (Effect : Type v) (Event : Type w) where
  cursor : Nat
  tail : List Event
  values : Valuation
  effect : Effect

abbrev Local {ops : Operations} (table : Fin 29 → Syntax ops)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol) (index : Fin 29) :=
  LocalData (model.Valuation ((table index).locals.map Ty.toHOL)) ((signature ops).State model) (Event ops model)

structure QueueClause (Cell : Field → Type u) (Record : Type u) (Effect : Frame.{u}) where
  witness : Frame.{u}
  before : (name : Field) → witness.Carrier → Cell name
  after : (name : Field) → witness.Carrier → Cell name
  record : witness.Carrier → Record
  guard : witness.Carrier → Effect.Carrier → Prop
  writes : List Field
  writes_distinct : writes.Nodup
  unchanged : ∀ name, name ∉ writes → ∀ values, after name values = before name values

namespace QueueClause

variable {Cell : Field → Type u} {Record : Type u} {Effect : Frame.{u}}
    (clause : QueueClause Cell Record Effect)

def localFrame : Frame.{u} where
  Carrier := LocalData clause.witness.Carrier Effect.Carrier (Record × Effect.Carrier)
  nonempty := by
    obtain ⟨values⟩ := clause.witness.nonempty
    obtain ⟨effect⟩ := Effect.nonempty
    exact ⟨⟨0, [], values, effect⟩⟩

def beforeTerm (name : Field) : Terms (AtomData Cell (Record × Effect.Carrier)) clause.localFrame :=
  fun locals => .field name (clause.before name locals.values)

def afterTerm (name : Field) : Terms (AtomData Cell (Record × Effect.Carrier)) clause.localFrame :=
  fun locals => .field name (clause.after name locals.values)

def pendingTerm : Terms (AtomData Cell (Record × Effect.Carrier)) clause.localFrame :=
  fun locals => .pending locals.cursor ((clause.record locals.values, locals.effect) :: locals.tail)

def residualTerm : Terms (AtomData Cell (Record × Effect.Carrier)) clause.localFrame :=
  fun locals => .pending (locals.cursor + 1) locals.tail

def guardTerm : Terms (AtomData Cell (Record × Effect.Carrier)) clause.localFrame :=
  fun locals => .proposition (clause.guard locals.values locals.effect)

def truthTerm : Terms (AtomData Cell (Record × Effect.Carrier)) clause.localFrame :=
  fun _ => .proposition True

/-- The native adapter and the independent mechanism controls instantiate
this same finite schematic construction. -/
def rule : RuleSyntax.Rule (Terms (AtomData Cell (Record × Effect.Carrier))) where
  locals := clause.localFrame
  body := {
    take := clause.pendingTerm :: clause.writes.map clause.beforeTerm
    read := (Field.all.filter (fun name => name ∉ clause.writes)).map clause.beforeTerm
    tell := [(clause.guardTerm, clause.truthTerm)]
    checks := [.equal clause.guardTerm clause.truthTerm]
    produce := clause.residualTerm :: clause.writes.map clause.afterTerm }
  collect := []

end QueueClause

noncomputable section

variable {ops : Operations} (table : Fin 29 → Syntax ops)
    (model : HOL.HenkinModel.{0,0,w+1} AtomicTy Symbol)
    (domains : model.InhabitedDomains)
    (contract : NativeInstanceReadback.Signature (signature ops))
    (allow : NativeInstanceReadback.Signature.Allow (native := signature ops) model)

def localFrame (index : Fin 29) : Frame.{w+1} where
  Carrier := Local table model index
  nonempty := ⟨⟨0, [], (fun {type} _ => domains.witness type),
    domains.witness (signature ops).state⟩⟩

def beforeState (index : Fin 29) (values : model.Valuation ((table index).locals.map Ty.toHOL)) :
    (signature ops).State model :=
  model.denote (pack ops (table index).before) values

def afterState (index : Fin 29) (values : model.Valuation ((table index).locals.map Ty.toHOL)) :
    (signature ops).State model :=
  model.denote (pack ops (table index).after) values

def recordValue (index : Fin 29) (values : model.Valuation ((table index).locals.map Ty.toHOL)) :
    (signature ops).Record model :=
  model.denote (table index).record values

/-- The source guard, actual result equality and one fixed explicit permission
are all constraints on the same source valuation and effect. -/
def obligation (index : Fin 29) (values : model.Valuation ((table index).locals.map Ty.toHOL))
    (effect : (signature ops).State model) : Prop :=
  (model.denote (table index).guard values).down ∧
    afterState table model index values = contract.resultValue model
      (beforeState table model index values) (recordValue table model index values) effect ∧
    (allow (beforeState table model index values) (recordValue table model index values) effect).down

def fieldTerm (index : Fin 29)
    (fields : (field : Field) → HOL.Term Symbol ((table index).locals.map Ty.toHOL) (field.type ops))
    (field : Field) : Terms (Atom ops model) (localFrame table model domains index) :=
  fun locals => .field field (model.denote (fields field) locals.values)

def pendingTerm (index : Fin 29) : Terms (Atom ops model) (localFrame table model domains index) :=
  fun locals => .pending locals.cursor
    ((recordValue table model index locals.values, locals.effect) :: locals.tail)

def residualTerm (index : Fin 29) : Terms (Atom ops model) (localFrame table model domains index) :=
  fun locals => .pending (locals.cursor + 1) locals.tail

def obligationTerm (index : Fin 29) : Terms (Atom ops model) (localFrame table model domains index) :=
  fun locals => .proposition (obligation table model contract allow index locals.values locals.effect)

def truthTerm (index : Fin 29) : Terms (Atom ops model) (localFrame table model domains index) :=
  fun _ => .proposition True

def effectFrame : Frame.{w+1} :=
  ⟨(signature ops).State model, ⟨domains.witness (signature ops).state⟩⟩

def nativeClause (index : Fin 29) :
    QueueClause (fun name => HOL.Ty.denote.{0,w+1} model.Carrier (name.type ops))
      ((signature ops).Record model) (effectFrame (ops := ops) model domains) where
  witness := NativeFieldSchema.localFrame table model domains index
  before name values := model.denote ((table index).before name) values
  after name values := model.denote ((table index).after name) values
  record := recordValue table model index
  guard := obligation table model contract allow index
  writes := (table index).writes
  writes_distinct := (table index).writes_distinct
  unchanged name missing values := congrArg (fun term => model.denote term values)
    ((table index).unchanged name missing)

/-- A schematic clause adds its explicit source constraint to the actual
information and asks the same equality after its own tells. -/
def rule (index : Fin 29) : RuleSyntax.Rule (Terms (Atom ops model)) :=
  (nativeClause table model domains contract allow index).rule

theorem rule_unfold (index : Fin 29) : rule table model domains contract allow index = {
  locals := localFrame table model domains index
  body := {
    take := pendingTerm table model domains index ::
      (table index).writes.map (fieldTerm table model domains index (table index).before)
    read := (table index).reads.map (fieldTerm table model domains index (table index).before)
    tell := [(obligationTerm table model domains contract allow index, truthTerm table model domains index)]
    checks := [.equal (obligationTerm table model domains contract allow index) (truthTerm table model domains index)]
    produce := residualTerm table model domains index ::
      (table index).writes.map (fieldTerm table model domains index (table index).after) }
  collect := [] } := rfl

theorem nativeClause_guard (index : Fin 29)
    (values : model.Valuation ((table index).locals.map Ty.toHOL))
    (effect : (signature ops).State model) :
    (nativeClause table model domains contract allow index).guard values effect =
      ((model.denote (table index).guard values).down ∧
        afterState table model index values = contract.resultValue model
          (beforeState table model index values) (recordValue table model index values) effect ∧
        (allow (beforeState table model index values) (recordValue table model index values) effect).down) := rfl

def program : RuleSyntax.Program (Terms (Atom ops model)) :=
  Set.range (rule table model domains contract allow)

theorem program_finite : (program table model domains contract allow).Finite := Set.finite_range _

theorem rule_member (index : Fin 29) :
    rule table model domains contract allow index ∈ program table model domains contract allow := ⟨index, rfl⟩

def row (generation : Field → Nat) (field : Field) : Occurrence := .field field (generation field)

def nextRow (generation : Field → Nat) (field : Field) : Occurrence := .field field (generation field + 1)

def nextGeneration (index : Fin 29) (generation : Field → Nat) (field : Field) : Nat :=
  if field ∈ (table index).writes then generation field + 1 else generation field

theorem row_injective (generation : Field → Nat) : Function.Injective (row generation) := by
  intro first second same
  exact (Occurrence.field.inj same).1

theorem nextRow_injective (generation : Field → Nat) : Function.Injective (nextRow generation) := by
  intro first second same
  exact (Occurrence.field.inj same).1

def selection (index : Fin 29) (generation : Field → Nat) (cursor : Nat) : Selection Occurrence where
  taken := .request cursor :: (table index).writes.map (row generation)
  read := (table index).reads.map (row generation)
  made := .request (cursor+1) :: (table index).writes.map (nextRow generation)

def firing {old : Frame.{w+1}} (index : Fin 29) (generation : Field → Nat) (cursor : Nat) :
    RuleSyntax.Firing Occurrence extensions (program table model domains contract allow) old :=
  canonical (rule table model domains contract allow index) (rule_member table model domains contract allow index)
    (selection table index generation cursor)

theorem firing_fresh (state : RuleSyntax.State (Terms (Atom ops model)) Occurrence)
    (index : Fin 29) (generation : Field → Nat) (cursor : Nat) :
    (firing table model domains contract allow (old := state.frame) index generation cursor).Fresh
      (frames (Atom ops model)) state :=
  canonical_fresh state (rule table model domains contract allow index)
    (rule_member table model domains contract allow index) _

/-- A layout records actual live identities, independently of their spelling.
Arbitrary reflected firings may allocate any fresh made identities. -/
structure Layout where
  request : Occurrence
  field : Field → Occurrence
  field_injective : Function.Injective field
  request_not_field : ∀ name, request ≠ field name

def Layout.support (layout : Layout) : Finset Occurrence :=
  insert layout.request (Field.all.toFinset.image layout.field)

def canonicalLayout (generation : Field → Nat) (cursor : Nat) : Layout where
  request := .request cursor
  field := row generation
  field_injective := row_injective generation
  request_not_field := by intro name same; cases same

/-- The entire live store consists of these ten fields and one pending row.
No additional field or request occurrence can bypass the stated input word.
Knowledge satisfaction is supplied for this environment, never by default. -/
structure ViewData {Cell : Field → Type u} {Event : Type v}
    (state : RuleSyntax.State (Terms (AtomData Cell Event)) Occurrence) (layout : Layout)
    (environment : state.frame.Carrier) (fields : (name : Field) → Cell name)
    (cursor : Nat) (pending : List Event) : Prop where
  exact : state.present = layout.support
  solved : Satisfies state.knowledge environment
  field : ∀ name, state.label (layout.field name) environment = .field name (fields name)
  request : state.label layout.request environment = .pending cursor pending

abbrev View (state : RuleSyntax.State (Terms (Atom ops model)) Occurrence) (layout : Layout)
    (environment : state.frame.Carrier) (fields : NativeFieldPacking.Fields ops model)
    (cursor : Nat) (pending : List (Event ops model)) :=
  ViewData state layout environment fields cursor pending

/-- Only the named starting state has empty knowledge. Every later state is
the actual result of its preceding firing. -/
def initial (fields : NativeFieldPacking.Fields ops model) (events : List (Event ops model))
    (generation : Field → Nat) (cursor : Nat) : RuleSyntax.State (Terms (Atom ops model)) Occurrence where
  frame := ground.{w+1}
  knowledge := []
  present := (canonicalLayout generation cursor).support
  label occurrence _ := match occurrence with
    | .field name _ => .field name (fields name)
    | .request _ => .pending cursor events

theorem initial_view (fields : NativeFieldPacking.Fields ops model) (events : List (Event ops model))
    (generation : Field → Nat) (cursor : Nat) :
    View model (initial model fields events generation cursor) (canonicalLayout generation cursor)
      PUnit.unit fields cursor events := by
  refine ⟨rfl, ?_, fun _ => rfl, rfl⟩
  intro equation member
  cases member

theorem denied_obligation (index : Fin 29) (values : model.Valuation ((table index).locals.map Ty.toHOL))
    (effect : (signature ops).State model)
    (denied : ¬ (allow (beforeState table model index values) (recordValue table model index values) effect).down) :
    ¬ obligation table model contract allow index values effect := fun valid => denied valid.2.2

theorem wrong_result_obligation (index : Fin 29) (values : model.Valuation ((table index).locals.map Ty.toHOL))
    (effect : (signature ops).State model)
    (different : afterState table model index values ≠ contract.resultValue model
      (beforeState table model index values) (recordValue table model index values) effect) :
    ¬ obligation table model contract allow index values effect := fun valid => different valid.2.1

end

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Kernel.NativeRecordRuns
