import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQuerySource
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.Protocol

/-!
# Occurrence-wise typed-call overlay over the Destination source owner

The existing Destination scope driver evaluates producers, retains alternatives,
threads the shared world and performs source unification. This adapter adds
call-row demand and type-store continuations. A produced argument occurrence
is guarded before its next argument or body starts; refusal resumes the saved
producer/row frontier without replaying its effects.

Declaration selection and ordered guard delivery are explicit services.
The guard service is tied to the existing Protocol kernel by an exact bag
law; its ordering and native reader remain separate qualification obligations.
This is not a replacement body evaluator or an assertion of complete native
PeTTa conformance.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaOccurrenceOverlay

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open Mettapedia.GSLT.Distinction.ProductiveBlocks

abbrev DControl := EagerDFS.Destination.Control
abbrev Goal := EagerDFS.Destination.Goal
abbrev Store := List (Eqn CallVar)

structure Row where
  parameters : List (Ty String)
  range : Ty String
  deriving DecidableEq

def Row.asType (row : Row) : Ty String := arrow row.parameters row.range

def Row.ofType (type : Ty String) : Option Row :=
  (arrowSplit type).map fun (parameters, range) => ⟨parameters, range⟩

def normalizeRows (rows : List Row) : List Row :=
  (dedupAlpha (rows.map Row.asType)).filterMap Row.ofType

theorem row_type_roundtrip (row : Row) : Row.ofType row.asType = some row := by
  cases row
  simp [Row.ofType, Row.asType]

theorem normalizeRows_repeated (rows : List Row) (row : Row)
    (repeated : ∃ earlier ∈ rows, AlphaEq earlier.asType row.asType) :
    normalizeRows (rows ++ [row]) = normalizeRows rows := by
  unfold normalizeRows
  rw [List.map_append]
  simp only [List.map_cons, List.map_nil]
  rw [dedupAlpha_append_alpha]
  obtain ⟨earlier, member, same⟩ := repeated
  exact ⟨earlier.asType, List.mem_map.mpr ⟨earlier, member, rfl⟩, same⟩

theorem normalizeRows_single (row : Row) : normalizeRows [row] = [row] := by
  simp [normalizeRows, dedupAlpha, row_type_roundtrip]

/-- Reading normalized records back as arrows gives exactly the existing
Protocol's alpha-idempotent row sequence; decoding loses no row or order. -/
theorem normalizeRows_types (rows : List Row) :
    (normalizeRows rows).map Row.asType = dedupAlpha (rows.map Row.asType) := by
  have decode : ∀ types : List (Ty String), (∀ type ∈ types, ∃ row : Row, type = row.asType) →
      (types.filterMap Row.ofType).map Row.asType = types := by
    intro types represented
    induction types with
    | nil => rfl
    | cons type rest ih =>
      obtain ⟨row, rfl⟩ := represented type (by simp)
      simp only [List.filterMap_cons, row_type_roundtrip, List.map_cons]
      congr 1
      exact ih fun type member => represented type (List.mem_cons_of_mem _ member)
  apply decode
  intro type member
  obtain ⟨row, _member, same⟩ := List.mem_map.mp (dedupAlpha_subset _ type member)
  exact ⟨row, same.symm⟩

inductive RowLookup where
  | untyped
  | typed (rows : List Row)
  | unserved

structure Services (User : Type) where
  rows : EagerDFS.World → User → String → List Atom → RowLookup
  declarations : EagerDFS.World → Decls
  kind : EagerDFS.World → Atom → String
  userSupport : User → Finset String
  orderedGuard : EagerDFS.World → Nat → Store → Ty String → Atom → Option (List Store)
  guard_exact : ∀ world index store expected value stores,
    orderedGuard world index store expected value = some stores →
      (stores : Multiset Store) = guard (atGuard index) store (expected.map Sum.inl)
        (info (declarations world) value) (kind world value)

inductive Phase where
  | nextArgument
  | argument (formal : Ty String) (slot : Atom)
  | body
  deriving DecidableEq

structure CallFrame where
  head : String
  row : Row
  remaining : List (Ty String × Atom)
  ready : List Atom
  index : Nat
  store : Store
  callerGoals : List Goal
  callerDestination : Atom
  callerCutBoundary : Nat
  callDestination : Atom
  scopeDepth : Nat
  phase : Phase

structure Context (User : Type) where
  user : User
  calls : List CallFrame := []

abbrev State (User : Type) := EagerDFS.Destination.ScopedCursor (Context User)
abbrev Work (User : Type) := EagerDFS.Destination.CollectionWork (Context User)
abbrev Scope (User : Type) := EagerDFS.Destination.CollectionScope (Context User)

inductive Request where
  | source (request : EagerDFS.Destination.ScopeBoundary)
  | rows (head : String) (arguments : List Atom)
  | arity (head : String) (arguments : List Atom) (rows : List Row)
  | guard (head : String) (index : Nat) (expected : Ty String) (value : Atom)
  | invalidTypedState

abbrev Step (User : Type) := Transition (State User) EagerDFS.Destination.CollectedAnswer (State User) Request

def liftSource {User : Type} :
    Transition (State User) EagerDFS.Destination.CollectedAnswer (State User) EagerDFS.Destination.ScopeBoundary → Step User
  | .silent next => .silent next
  | .publish events next => .publish events next
  | .finish final => .finish final
  | .call request retained => .call (.source request) retained
  | .fail reasons => .fail reasons

def CallFrame.atoms (frame : CallFrame) : List Atom :=
  frame.callerDestination :: frame.callDestination ::
    frame.remaining.map Prod.snd ++ frame.ready ++ frame.callerGoals.flatMap EagerDFS.Destination.Goal.atoms

def contextSupport {User : Type} (services : Services User) (context : Context User) : Finset String :=
  services.userSupport context.user ∪
    EagerDFS.Destination.operandSupport (context.calls.flatMap CallFrame.atoms)

def protect {User : Type} (services : Services User) (source : State User) (control : DControl)
    (context : Context User) : DControl :=
  { control with reserved := control.reserved ∪ contextSupport services context ∪
      EagerDFS.Destination.collectionSupport source.2 }

/-- Only the reached head is replaced. Neither the world nor older source
alternatives are restored from a captured call record. -/
def install {User : Type} (source : State User) (scope : Scope User) (parents : List (Scope User))
    (work pending : List (Work User)) : State User :=
  (source.1, ⟨source.2.world, { scope with frontier := work ++ pending } :: parents⟩)

def rowWork {User : Type} (control : DControl) (context : Context User) (origins : List Nat)
    (depth : Nat) (head : String) (arguments : List Atom) (destination : Atom)
    (older : List Goal) (row : Row) (occurrence : Nat) : Work User :=
  let frame : CallFrame :=
    ⟨head, row, row.parameters.zip arguments, [], 0, [], older, control.destination,
      control.cutBoundary, destination, depth, .nextArgument⟩
  ({ control with goals := [], destination }, { context with calls := frame :: context.calls }, origins ++ [occurrence])

def enterRows {User : Type} (services : Services User) (source : State User)
    (scope : Scope User) (parents : List (Scope User)) (control : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (head : String) (arguments : List Atom) (destination : Atom) (older : List Goal) : Step User :=
  match services.rows source.2.world context.user head arguments with
  | .unserved => .call (.rows head arguments) source
  | .untyped => .call (.rows head arguments) source
  | .typed rows =>
      let rows := normalizeRows rows
      if rows.all (fun row => row.parameters.length == arguments.length) then
        let work := rows.zipIdx.map fun (row, occurrence) =>
          let next := rowWork control context origins source.2.scopes.length head arguments destination older row occurrence
          (protect services source next.1 next.2.1, next.2)
        .silent (install source scope parents work pending)
      else .call (.arity head arguments rows) source

def nextArgument {User : Type} (services : Services User) (source : State User)
    (scope : Scope User) (parents : List (Scope User)) (control : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) : Step User :=
  match frame.remaining with
  | [] =>
      let next := { control with
        goals := [.invoke frame.head frame.ready frame.callDestination]
        destination := frame.callDestination }
      let context := { context with calls := { frame with phase := .body } :: outside }
      .silent (install source scope parents [(protect services source next context, context, origins)] pending)
  | (formal, argument) :: remaining =>
      if demand formal = .raw then
        let advanced := { frame with remaining, ready := frame.ready ++ [argument], index := frame.index + 1 }
        let context := { context with calls := advanced :: outside }
        .silent (install source scope parents [(protect services source control context, context, origins)] pending)
      else
        let prepared := protect services source control context
        let slot := Atom.var (EagerDFS.Destination.freshName prepared 0)
        let next := { prepared with goals := [.evaluate argument slot], destination := slot }
        let context := { context with calls := { frame with remaining, phase := .argument formal slot } :: outside }
        .silent (install source scope parents [(protect services source next context, context, origins)] pending)

def guardResult {User : Type} (services : Services User) (world : EagerDFS.World)
    (frame : CallFrame) (formal : Ty String) (value : Atom) (check : Bool) : Option (List Store) :=
  if check then services.orderedGuard world frame.index frame.store formal value else some [frame.store]

def argumentContinuations {User : Type} (services : Services User) (source : State User)
    (control : DControl) (context : Context User) (origins : List Nat)
    (frame : CallFrame) (outside : List CallFrame) (slot : Atom) (stores : List Store) : List (Work User) :=
  stores.zipIdx.map fun (store, occurrence) =>
    let advanced := { frame with
      ready := frame.ready ++ [slot]
      store
      index := frame.index + 1
      phase := .nextArgument }
    let context := { context with calls := advanced :: outside }
    (protect services source control context, context, origins ++ [occurrence])

def consumeArgument {User : Type} (services : Services User) (source : State User)
    (scope : Scope User) (parents : List (Scope User)) (control : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (formal : Ty String) (slot value : Atom) : Step User :=
  match guardResult services source.2.world frame formal value (demand formal == .guarded) with
  | none => .call (.guard frame.head frame.index formal value) source
  | some stores =>
      .silent (install source scope parents
        (argumentContinuations services source control context origins frame outside slot stores) pending)

def resumeCaller (control : DControl) (frame : CallFrame) : DControl :=
  { control with
    goals := frame.callerGoals
    destination := frame.callerDestination
    cutBoundary := frame.callerCutBoundary }

def consumeBody {User : Type} (services : Services User) (source : State User)
    (scope : Scope User) (parents : List (Scope User)) (control : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User))
    (frame : CallFrame) (outside : List CallFrame) (value : Atom) : Step User :=
  match guardResult services source.2.world frame frame.row.range value (decide (ResultGuarded frame.row.range)) with
  | none => .call (.guard frame.head frame.index frame.row.range value) source
  | some stores =>
      let context := { context with calls := outside }
      let resumed := resumeCaller control frame
      let work := stores.zipIdx.map fun (_, occurrence) =>
        (protect services source resumed context, context, origins ++ [occurrence])
      .silent (install source scope parents work pending)

/-- These forms retain the existing source control rules even when a program
also contains an equation or declaration with the same head spelling. -/
def sourceOwned (expression : Atom) : Bool :=
  EagerDFS.eagerControlForm expression || match expression with
    | .expression [.symbol "cut"] | .expression [.symbol "once", _] => true
    | .expression [.symbol "match", _, _, _] => true
    | _ => false

def delegate {User : Type} (services : Services User) (policy : EagerDFS.Destination.Policy)
    (program : SpaceSemantics.Program) (source : State User)
    (scope : Scope User) (parents : List (Scope User)) (control : DControl)
    (context : Context User) (origins : List Nat) (pending : List (Work User)) : Step User :=
  match control.goals with
  | .evaluate (.expression (.symbol head :: arguments)) destination :: older =>
      if !sourceOwned (.expression (.symbol head :: arguments)) &&
          EagerDFS.Destination.callable program head then
        match services.rows source.2.world context.user head arguments with
        | .untyped => liftSource (Bridges.ScopedQuerySource.ownedStep policy program source)
        | _ => enterRows services source scope parents control context origins pending head arguments destination older
      else liftSource (Bridges.ScopedQuerySource.ownedStep policy program source)
  | _ => liftSource (Bridges.ScopedQuerySource.ownedStep policy program source)

/-- The outer driver retains its usual occurrence frontier. A type-frame
terminal is consumed only at its own scope depth, not inside an inner collapse. -/
def step {User : Type} (services : Services User) (policy : EagerDFS.Destination.Policy)
    (program : SpaceSemantics.Program) (source : State User) : Step User :=
  match source.2.scopes with
  | [] => liftSource (Bridges.ScopedQuerySource.ownedStep policy program source)
  | scope :: parents =>
      match scope.frontier with
      | [] => liftSource (Bridges.ScopedQuerySource.ownedStep policy program source)
      | (control, context, origins) :: pending =>
          match context.calls with
          | [] => delegate services policy program source scope parents control context origins pending
          | frame :: outside =>
              if frame.scopeDepth = source.2.scopes.length then
                match frame.phase with
                | .nextArgument => nextArgument services source scope parents control context origins pending frame outside
                | .argument _ _ | .body =>
                    if control.goals.isEmpty then
                      match EagerDFS.Destination.resolve control.bindings with
                      | none => .call (.source (.branch .invalidEnvironment)) source
                      | some environment =>
                          let value := EagerDFS.Destination.read environment control.destination
                          match frame.phase with
                          | .argument formal slot => consumeArgument services source scope parents control context origins pending frame outside formal slot value
                          | .body => consumeBody services source scope parents control context origins pending frame outside value
                          | .nextArgument => .call .invalidTypedState source
                    else delegate services policy program source scope parents control context origins pending
              else delegate services policy program source scope parents control context origins pending

def machine {User : Type} (services : Services User)
    (policy : EagerDFS.Destination.Policy) (program : SpaceSemantics.Program) :
    Machine (State User) EagerDFS.Destination.CollectedAnswer (State User) Request where
  step source := some (step services policy program source)

/-! ## Local occurrence and residual laws

The premises below are one delivered guard request, never an assumed equality
of a whole source run. Producer execution and its reached state remain owned
by the existing `ScopedQuerySource.ownedStep` surface adapter and Destination
scheduler. Primitive match remains data-producing; surface queries schedule
their retained template recipe.
-/

theorem install_world {User : Type} (source : State User) (scope : Scope User)
    (parents : List (Scope User)) (work pending : List (Work User)) :
    (install source scope parents work pending).2.world = source.2.world := rfl

theorem install_residual {User : Type} (source : State User) (scope : Scope User)
    (parents : List (Scope User)) (work pending : List (Work User)) :
    (install source scope parents work pending).2.scopes =
      { scope with frontier := work ++ pending } :: parents := rfl

theorem protect_bindings {User : Type} (services : Services User) (source : State User)
    (control : DControl) (context : Context User) :
    (protect services source control context).bindings = control.bindings := rfl

theorem guarded_argument_refuses_only_current {User : Type} (services : Services User)
    (source : State User) (scope : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat)
    (pending : List (Work User)) (frame : CallFrame) (outside : List CallFrame)
    (formal : Ty String) (slot value : Atom) (checked : demand formal = .guarded)
    (refused : services.orderedGuard source.2.world frame.index frame.store formal value = some []) :
    consumeArgument services source scope parents control context origins pending frame outside formal slot value =
      .silent (source.1, ⟨source.2.world, {scope with frontier := pending} :: parents⟩) := by
  simp [consumeArgument, guardResult, checked, refused, install, argumentContinuations]

theorem missing_argument_guard_retains_everything {User : Type} (services : Services User)
    (source : State User) (scope : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat)
    (pending : List (Work User)) (frame : CallFrame) (outside : List CallFrame)
    (formal : Ty String) (slot value : Atom) (checked : demand formal = .guarded)
    (missing : services.orderedGuard source.2.world frame.index frame.store formal value = none) :
    consumeArgument services source scope parents control context origins pending frame outside formal slot value =
      .call (.guard frame.head frame.index formal value) source := by
  simp [consumeArgument, guardResult, checked, missing]

theorem argument_guard_exact {User : Type} (services : Services User)
    (world : EagerDFS.World) (frame : CallFrame) (formal : Ty String) (value : Atom)
    (stores : List Store) (checked : demand formal = .guarded)
    (served : guardResult services world frame formal value (demand formal == .guarded) = some stores) :
    (stores : Multiset Store) = guard (atGuard frame.index) frame.store (formal.map Sum.inl)
      (info (services.declarations world) value) (services.kind world value) := by
  apply services.guard_exact
  simpa [guardResult, checked] using served

theorem argument_guard_multiplicity {User : Type} (services : Services User)
    (world : EagerDFS.World) (frame : CallFrame) (formal : Ty String) (value : Atom)
    (stores : List Store) (checked : demand formal = .guarded)
    (served : guardResult services world frame formal value (demand formal == .guarded) = some stores) :
    stores.length = Multiset.card (guard (atGuard frame.index) frame.store (formal.map Sum.inl)
      (info (services.declarations world) value) (services.kind world value)) := by
  rw [← argument_guard_exact services world frame formal value stores checked served]
  rfl

theorem unchecked_argument_keeps_store {User : Type} (services : Services User)
    (world : EagerDFS.World) (frame : CallFrame) (formal : Ty String) (value : Atom)
    (unchecked : demand formal ≠ .guarded) :
    guardResult services world frame formal value (demand formal == .guarded) = some [frame.store] := by
  simp [guardResult, unchecked]

theorem result_guard_exact {User : Type} (services : Services User)
    (world : EagerDFS.World) (frame : CallFrame) (value : Atom) (stores : List Store)
    (checked : ResultGuarded frame.row.range)
    (served : guardResult services world frame frame.row.range value
      (decide (ResultGuarded frame.row.range)) = some stores) :
    (stores : Multiset Store) = guard (atGuard frame.index) frame.store
      (frame.row.range.map Sum.inl) (info (services.declarations world) value)
      (services.kind world value) := by
  apply services.guard_exact
  simpa [guardResult, checked] using served

theorem unchecked_result_keeps_entry_store {User : Type} (services : Services User)
    (world : EagerDFS.World) (frame : CallFrame) (value : Atom)
    (unchecked : ¬ ResultGuarded frame.row.range) :
    guardResult services world frame frame.row.range value
      (decide (ResultGuarded frame.row.range)) = some [frame.store] := by
  simp [guardResult, unchecked]

theorem guarded_result_refuses_only_current {User : Type} (services : Services User)
    (source : State User) (scope : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat)
    (pending : List (Work User)) (frame : CallFrame) (outside : List CallFrame)
    (value : Atom) (checked : ResultGuarded frame.row.range)
    (refused : services.orderedGuard source.2.world frame.index frame.store frame.row.range value = some []) :
    consumeBody services source scope parents control context origins pending frame outside value =
      .silent (source.1, ⟨source.2.world, {scope with frontier := pending} :: parents⟩) := by
  simp [consumeBody, guardResult, checked, refused, install]

theorem source_owned_delegates {User : Type} (services : Services User)
    (policy : EagerDFS.Destination.Policy) (program : SpaceSemantics.Program)
    (source : State User) (scope : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat)
    (pending : List (Work User)) (head : String) (arguments : List Atom)
    (destination : Atom) (older : List Goal)
    (goals : control.goals = .evaluate (.expression (.symbol head :: arguments)) destination :: older)
    (owned : sourceOwned (.expression (.symbol head :: arguments)) = true) :
    delegate services policy program source scope parents control context origins pending =
      liftSource (Bridges.ScopedQuerySource.ownedStep policy program source) := by
  simp [delegate, goals, owned]

theorem argument_continuations_length {User : Type} (services : Services User)
    (source : State User) (control : DControl) (context : Context User) (origins : List Nat)
    (frame : CallFrame) (outside : List CallFrame) (slot : Atom) (stores : List Store) :
    (argumentContinuations services source control context origins frame outside slot stores).length =
      stores.length := by
  simp [argumentContinuations]

/-- Every successful guard occurrence retains the producer's actual equations,
one new type store, and the saved argument recipe. The next continuation is
the next argument, not a restart of the producer. -/
theorem argument_continuations_records {User : Type} (services : Services User)
    (source : State User) (control : DControl) (context : Context User) (origins : List Nat)
    (frame : CallFrame) (outside : List CallFrame) (slot : Atom) (stores : List Store) :
    (argumentContinuations services source control context origins frame outside slot stores).map
      (fun work => (work.1.bindings, work.2.1.calls.head?.map
        (fun saved => (saved.store, saved.ready, saved.phase)), work.2.2)) =
      stores.zipIdx.map (fun (store, occurrence) =>
        (control.bindings, some (store, frame.ready ++ [slot], Phase.nextArgument), origins ++ [occurrence])) := by
  simp [argumentContinuations, List.map_map, protect]

theorem resumed_caller_keeps_reached_bindings (control : DControl) (frame : CallFrame) :
    (resumeCaller control frame).bindings = control.bindings := rfl

theorem resumed_caller_restores_only_continuation (control : DControl) (frame : CallFrame) :
    (resumeCaller control frame).goals = frame.callerGoals ∧
      (resumeCaller control frame).destination = frame.callerDestination ∧
      (resumeCaller control frame).cutBoundary = frame.callerCutBoundary := ⟨rfl, rfl, rfl⟩

theorem operand_support_contains (atom : Atom) (atoms : List Atom) (member : atom ∈ atoms) :
    (EagerDFS.Destination.encode atom).freeVars ⊆ EagerDFS.Destination.operandSupport atoms := by
  induction atoms with
  | nil => cases member
  | cons first rest ih =>
      rcases List.mem_cons.mp member with rfl | later
      · exact Finset.subset_union_left
      · exact Finset.Subset.trans (ih later) Finset.subset_union_right

theorem saved_name_is_protected {User : Type} (services : Services User)
    (source : State User) (control : DControl) (context : Context User)
    (frame : CallFrame) (retained : frame ∈ context.calls) (atom : Atom)
    (saved : atom ∈ frame.atoms) (name : String)
    (occurs : name ∈ (EagerDFS.Destination.encode atom).freeVars) :
    name ∈ (protect services source control context).support := by
  apply Finset.mem_union_left
  apply Finset.mem_union_left
  apply Finset.mem_union_right
  apply Finset.mem_union_right
  exact operand_support_contains atom _ (List.mem_flatMap.mpr ⟨frame, retained, saved⟩) occurs

/-- Fresh source slots and fresh source clause instances cannot capture a
variable held only in the suspended typed caller. -/
theorem fresh_slot_avoids_saved_caller {User : Type} (services : Services User)
    (source : State User) (control : DControl) (context : Context User)
    (frame : CallFrame) (retained : frame ∈ context.calls) (atom : Atom)
    (saved : atom ∈ frame.atoms) (index : Nat) :
    EagerDFS.Destination.freshName (protect services source control context) index ∉
      (EagerDFS.Destination.encode atom).freeVars := by
  intro occurs
  exact EagerDFS.Destination.freshName_not_mem _ _
    (saved_name_is_protected services source control context frame retained atom saved _ occurs)

/-- The actual source solver earns transport of an argument recipe through
later source constraints. No value-only callee oracle is used. -/
theorem saved_argument_read_transport
    (before after : EagerDFS.Destination.Equations)
    (initial final : EagerDFS.Destination.Environment)
    (resolved : EagerDFS.Destination.resolve before = some initial)
    (extension : ∀ candidate, EagerDFS.Destination.Solves candidate after →
      EagerDFS.Destination.Solves candidate before)
    (solved : EagerDFS.Destination.Solves final after) (slot : Atom) :
    EagerDFS.Destination.read final (EagerDFS.Destination.read initial slot) =
      EagerDFS.Destination.read final slot :=
  EagerDFS.Destination.resolve_read_preserved_by_extension resolved extension final solved slot

/-- The actual scope-driver step consumes a resolved producer occurrence
before the source collector can publish it. Its ordered guard continuations
are installed in front of, not after, the saved producer/row alternatives. -/
theorem terminal_argument_step {User : Type} (services : Services User)
    (policy : EagerDFS.Destination.Policy) (program : SpaceSemantics.Program)
    (source : State User) (scope : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat)
    (pending : List (Work User)) (frame : CallFrame) (outside : List CallFrame)
    (formal : Ty String) (slot : Atom) (environment : EagerDFS.Destination.Environment)
    (stores : List Store)
    (scopes : source.2.scopes = scope :: parents)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (calls : context.calls = frame :: outside)
    (depth : frame.scopeDepth = source.2.scopes.length)
    (phase : frame.phase = .argument formal slot) (terminal : control.goals = [])
    (resolved : EagerDFS.Destination.resolve control.bindings = some environment)
    (served : guardResult services source.2.world frame formal
      (EagerDFS.Destination.read environment control.destination) (demand formal == .guarded) = some stores) :
    step services policy program source = .silent (install source scope parents
      (argumentContinuations services source control context origins frame outside slot stores) pending) := by
  have depth' : frame.scopeDepth = (scope :: parents).length := by simpa only [scopes] using depth
  simp only [step, scopes, frontier, calls, if_pos depth', phase, terminal,
    List.isEmpty_nil, ↓reduceIte, resolved, consumeArgument, served]

/-- Return checking precedes restoration of the caller's continuation. The
control used on success is the reached body control, with its real bindings. -/
theorem terminal_body_step {User : Type} (services : Services User)
    (policy : EagerDFS.Destination.Policy) (program : SpaceSemantics.Program)
    (source : State User) (scope : Scope User) (parents : List (Scope User))
    (control : DControl) (context : Context User) (origins : List Nat)
    (pending : List (Work User)) (frame : CallFrame) (outside : List CallFrame)
    (environment : EagerDFS.Destination.Environment)
    (scopes : source.2.scopes = scope :: parents)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (calls : context.calls = frame :: outside)
    (depth : frame.scopeDepth = source.2.scopes.length)
    (phase : frame.phase = .body) (terminal : control.goals = [])
    (resolved : EagerDFS.Destination.resolve control.bindings = some environment) :
    step services policy program source = consumeBody services source scope parents control context
      origins pending frame outside (EagerDFS.Destination.read environment control.destination) := by
  have depth' : frame.scopeDepth = (scope :: parents).length := by simpa only [scopes] using depth
  simp only [step, scopes, frontier, calls, if_pos depth', phase, terminal,
    List.isEmpty_nil, ↓reduceIte, resolved]

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaOccurrenceOverlay
