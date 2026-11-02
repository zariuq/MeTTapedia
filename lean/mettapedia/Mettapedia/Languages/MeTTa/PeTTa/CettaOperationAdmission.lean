import Mettapedia.Languages.MeTTa.PeTTa.EagerDFS
import Mettapedia.Languages.MeTTa.PeTTa.ExplicitEvaluation
import Mettapedia.GSLT.LanguageDef.PolicyFamilyAdmission

/-!
# Occurrence and profile checks for CeTTa eager source replay

This is preparation for an oracle comparison or producer qualification. It
does not change language evaluation: an unknown constructor remains data.
The input is a finite set of requested source occurrences and a separately
supplied inventory of native dispatch facts. Missing or ambiguous facts
refuse preparation; absence from a sparse table is not evidence of passivity.

Source addresses, captured call/data roles, profile visibility, equation
policy and named service dependencies remain in the inventory. A data
occurrence compiled before a later import retains its captured role. Native
operation/equation mixtures and native-only operations are outside this replay
profile. Successful checking preserves the order and multiplicity of both
occurrences and service requirements.

The theorems concern this executable finite check, its selected dependency
view, actual eager source dispatch, and the existing occurrence compiler.
Extraction of a complete inventory from C, source-address coverage, argument
demand/arity admission, primitive implementations, foreign services, parser
correctness and compiled execution refinement are independent obligations.
In particular, a named service dependency is retained metadata, not a proof
that the service implements the Lean primitive or preserves authority.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.CettaOperationAdmission

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.GSLT.Core (PolicyFamily)
open Mettapedia.GSLT.LanguageDef.OperationalAdmission (DependencySystem)
open SpaceSemantics (Program)

/-- The class selected by the actual source grammar and dispatch priority.
Class agreement alone is not agreement of primitive results or effects. -/
inductive Class where
  | value
  | passive
  | control
  | inputOutput
  | primitive
  | authored
  deriving DecidableEq, Repr

def headClass (program : Program) (head : String) : Class :=
  if Eval.ioHead head then .inputOutput
  else if StdLib.known head then .primitive
  else if program.equations.any (·.head == head) then .authored
  else .passive

/-- Reuse the independent source grammar's exact control-form predicate.
Malformed control-shaped applications are not silently classified as forms. -/
def modelClass (program : Program) (expression : Atom) : Class :=
  if DeclarativeSpec.controlForm expression then .control
  else match expression with
    | .expression (.symbol head :: _) => headClass program head
    | .expression _ => .passive
    | _ => .value

/-- The document/request identity and a path of child indices. Distinct source
occurrences may carry equal expressions or equal returned payloads. -/
structure Address where
  source : Nat
  path : List Nat
  deriving DecidableEq, Repr

structure Request where
  address : Address
  expression : Atom
  deriving DecidableEq, Repr

inductive Profile where
  | plain
  | extended
  deriving DecidableEq, Repr

inductive CapturedRole where
  | value
  | data
  | call
  | dynamic
  deriving DecidableEq, Repr

inductive Route where
  | classified : Class → Route
  | nativeOnly
  | mixedEquations
  | protectedDefinition
  | dynamic
  deriving DecidableEq, Repr

/-- Identifies what a host receipt must establish and retain. These names do
not introduce axioms or confer logical authority on a native service. -/
inductive DependencyKind where
  | reader
  | compiledRole
  | callability
  | operationRegistry
  | equationPolicy
  | primitive
  | foreignService
  | authority
  deriving DecidableEq, Repr

structure ServiceDependency where
  kind : DependencyKind
  name : String
  identity : String
  deriving DecidableEq, Repr

/-- A supplied fact for one exact occurrence and compile context. Visible and
hidden routes include the host's equation/override policy at this occurrence's
arity. Captured DATA and VALUE roles take precedence over later registry
changes. The list of dependencies retains repetitions. -/
structure NativeFact where
  address : Address
  expression : Atom
  role : CapturedRole
  visibleIn : List Profile
  visible : Route
  hidden : Route
  dependencies : List ServiceDependency
  deriving DecidableEq, Repr

def NativeFact.resolve (fact : NativeFact) (profile : Profile) : Route :=
  match fact.role with
  | .value => .classified .value
  | .data => .classified .passive
  | .dynamic => .dynamic
  | .call => if profile ∈ fact.visibleIn then fact.visible else fact.hidden

structure Snapshot where
  profile : Profile
  facts : List NativeFact
  deriving DecidableEq, Repr

def Snapshot.read (snapshot : Snapshot) (address : Address) : List NativeFact :=
  snapshot.facts.filter (fun fact => decide (fact.address = address))

structure Requirement where
  address : Address
  expression : Atom
  selection : Class
  capturedRole : CapturedRole
  dependencies : List ServiceDependency
  deriving DecidableEq, Repr

def Requirement.ofFact (program : Program) (request : Request)
    (fact : NativeFact) : Requirement :=
  ⟨request.address, request.expression, modelClass program request.expression,
    fact.role, fact.dependencies⟩

inductive Refusal where
  | missing : Address → Refusal
  | ambiguous : Address → Refusal
  | sourceChanged : Address → Refusal
  | collision : Address → Class → Class → Refusal
  | nativeOnly : Address → Refusal
  | mixedEquations : Address → Refusal
  | protectedDefinition : Address → Refusal
  | dynamic : Address → Refusal
  deriving DecidableEq, Repr

/-- Check only a supplied occurrence read. The expression comparison binds
the read's captured role to the requested source syntax. -/
def checkRead (program : Program) (request : Request) (profile : Profile)
    (facts : List NativeFact) : Except Refusal Requirement :=
  match facts with
  | [] => .error (.missing request.address)
  | [fact] =>
      if fact.expression = request.expression then
        match fact.resolve profile with
        | .classified selected =>
            if selected = modelClass program request.expression then
              .ok (Requirement.ofFact program request fact)
            else .error (.collision request.address
              (modelClass program request.expression) selected)
        | .nativeOnly => .error (.nativeOnly request.address)
        | .mixedEquations => .error (.mixedEquations request.address)
        | .protectedDefinition => .error (.protectedDefinition request.address)
        | .dynamic => .error (.dynamic request.address)
      else .error (.sourceChanged request.address)
  | _ => .error (.ambiguous request.address)

def checkOne (program : Program) (snapshot : Snapshot) (request : Request) :
    Except Refusal Requirement :=
  checkRead program request snapshot.profile (snapshot.read request.address)

/-- Traverse in source-request order. A second occurrence of the same service
remains a second requirement. Refusal stops at the first offending occurrence.
It does not run or discard the computation being prepared. -/
def checkManifest (program : Program) (snapshot : Snapshot) :
    List Request → Except Refusal (List Requirement)
  | [] => .ok []
  | request :: rest =>
      match checkOne program snapshot request with
      | .error refusal => .error refusal
      | .ok first =>
          match checkManifest program snapshot rest with
          | .error refusal => .error refusal
          | .ok following => .ok (first :: following)

theorem checkRead_ok_iff (program : Program) (request : Request)
    (profile : Profile) (facts : List NativeFact) (requirement : Requirement) :
    checkRead program request profile facts = .ok requirement ↔
      ∃ fact, facts = [fact] ∧ fact.expression = request.expression ∧
        fact.resolve profile = .classified (modelClass program request.expression) ∧
        requirement = Requirement.ofFact program request fact := by
  cases facts with
  | nil => simp [checkRead]
  | cons fact rest =>
      cases rest with
      | cons next rest => simp [checkRead]
      | nil =>
          by_cases same : fact.expression = request.expression
          · cases resolved : fact.resolve profile with
            | classified selected =>
                by_cases agrees : selected = modelClass program request.expression
                · simp [checkRead, same, resolved, agrees, eq_comm]
                · simp [checkRead, same, resolved, agrees]
            | nativeOnly | mixedEquations | protectedDefinition | dynamic =>
                simp [checkRead, same, resolved]
          · simp [checkRead, same]

theorem checkOne_ok_iff (program : Program) (snapshot : Snapshot)
    (request : Request) (requirement : Requirement) :
    checkOne program snapshot request = .ok requirement ↔
      ∃ fact, snapshot.read request.address = [fact] ∧
        fact.expression = request.expression ∧
        fact.resolve snapshot.profile = .classified (modelClass program request.expression) ∧
        requirement = Requirement.ofFact program request fact :=
  checkRead_ok_iff program request snapshot.profile _ requirement

/-- This relation retains source order and duplicate requests, rather than
asserting only membership in an unordered support set. -/
theorem checkManifest_ok_iff (program : Program) (snapshot : Snapshot)
    (requests : List Request) (requirements : List Requirement) :
    checkManifest program snapshot requests = .ok requirements ↔
      List.Forall₂ (fun request requirement =>
        checkOne program snapshot request = .ok requirement) requests requirements := by
  induction requests generalizing requirements with
  | nil => cases requirements <;> simp [checkManifest]
  | cons request rest ih =>
      cases checked : checkOne program snapshot request with
      | error refusal =>
          cases requirements <;> simp [checkManifest, checked]
      | ok first =>
          cases following : checkManifest program snapshot rest with
          | error refusal =>
              cases requirements with
              | nil => simp [checkManifest, checked, following]
              | cons requirement tail =>
                  have invalid : ¬ List.Forall₂ (fun request requirement =>
                      checkOne program snapshot request = .ok requirement) rest tail := by
                    intro related
                    have := (ih tail).mpr related
                    simp [following] at this
                  simp [checkManifest, checked, following, invalid]
          | ok tail =>
              cases requirements with
              | nil => simp [checkManifest, checked, following]
              | cons requirement remaining =>
                  simp [checkManifest, checked, following, ← ih remaining]

theorem checkManifest_length (program : Program) (snapshot : Snapshot)
    (requests : List Request) (requirements : List Requirement)
    (accepted : checkManifest program snapshot requests = .ok requirements) :
    requirements.length = requests.length :=
  ((checkManifest_ok_iff program snapshot requests requirements).mp accepted).length_eq.symm

theorem checkManifest_append (program : Program) (snapshot : Snapshot)
    (first second : List Request) :
    checkManifest program snapshot (first ++ second) = do
      let before ← checkManifest program snapshot first
      let after ← checkManifest program snapshot second
      return before ++ after := by
  induction first with
  | nil =>
      simp only [List.nil_append, checkManifest]
      cases checkManifest program snapshot second <;> rfl
  | cons request rest ih =>
      simp only [List.cons_append, checkManifest, ih]
      cases checkOne program snapshot request <;>
        cases checkManifest program snapshot rest <;>
        cases checkManifest program snapshot second <;> rfl

/-- Only the requested occurrence reads are selected. Each read includes the
profile, captured role, source syntax, equation policy and service identities.
There is no global revision equality requirement. -/
def dependencies (requests : List Request) : DependencySystem where
  Revision := Snapshot
  Dependency := { address : Address // address ∈ requests.map Request.address }
  Value := Profile × List NativeFact
  read := fun snapshot address => (snapshot.profile, snapshot.read address.1)

theorem checkManifest_congr (program : Program) (first second : Snapshot)
    (requests : List Request)
    (same : ∀ request ∈ requests, checkOne program first request = checkOne program second request) :
    checkManifest program first requests = checkManifest program second requests := by
  induction requests with
  | nil => rfl
  | cons request rest ih =>
      simp only [checkManifest]
      rw [same request (List.mem_cons_self ..), ih (fun row member =>
        same row (List.mem_cons_of_mem request member))]

/-- Transport the metadata check with its source program and request population
fixed. A changed authored program requires a separate source-policy check. -/
theorem checkManifest_transport (program : Program) (requests : List Request)
    (first second : Snapshot)
    (same : (dependencies requests).SameDependencies first second) :
    checkManifest program first requests = checkManifest program second requests := by
  apply checkManifest_congr
  intro request member
  have read := same ⟨request.address, List.mem_map.mpr ⟨request, member, rfl⟩⟩
  have profile := congrArg Prod.fst read
  have occurrence := congrArg Prod.snd read
  simp only [dependencies] at profile occurrence
  simp only [checkOne, profile, occurrence]

theorem unrelated_append_current (requests : List Request) (snapshot : Snapshot)
    (added : List NativeFact)
    (unrelated : ∀ fact ∈ added, fact.address ∉ requests.map Request.address) :
    (dependencies requests).SameDependencies snapshot
      { snapshot with facts := snapshot.facts ++ added } := by
  intro address
  have absent : added.filter (fun fact => decide (fact.address = address.1)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro fact member
    rw [decide_eq_true_eq]
    intro equal
    exact unrelated fact member (equal ▸ address.2)
  simp only [dependencies, Snapshot.read, List.filter_append, absent, List.append_nil]

theorem checkManifest_unrelated_append (program : Program) (requests : List Request)
    (snapshot : Snapshot) (added : List NativeFact)
    (unrelated : ∀ fact ∈ added, fact.address ∉ requests.map Request.address) :
    checkManifest program snapshot requests =
      checkManifest program { snapshot with facts := snapshot.facts ++ added } requests :=
  checkManifest_transport program requests _ _ (unrelated_append_current requests snapshot added unrelated)

/-- An actual policy family, useful for detecting an insufficient compressed
inventory. It observes individual occurrence decisions including refusals. -/
def policyFamily (program : Program) (requests : List Request) : PolicyFamily Snapshot where
  Policy := { request : Request // request ∈ requests }
  Result := fun _ => Except Refusal Requirement
  decide := fun request snapshot => checkOne program snapshot request.1

/-- A deliberately lossy view retaining registry routes while dropping each
occurrence's captured role. The controls below show why it is insufficient. -/
def forgetCapturedRoles (snapshot : Snapshot) : Profile × List NativeFact :=
  (snapshot.profile, snapshot.facts.map fun fact => { fact with role := .call })

/-! ## Source-occurrence roles and the existing compiler -/

/-- A finite role check over the existing source-occurrence representation.
It checks each captured decision against classification in the selected
program, without evaluating or identifying its alternative choices. -/
def rolesAligned (program : ValueOccurrences.Program) : ExplicitEvaluation.Term → Bool
  | .value _ => true
  | .application captured children =>
      decide (captured = program.isCall (ExplicitEvaluation.Term.syntax.syntaxList children)) &&
        childrenAligned program children
where
  childrenAligned (program : ValueOccurrences.Program) : List ExplicitEvaluation.Term → Bool
    | [] => true
    | child :: rest => rolesAligned program child && childrenAligned program rest

/-- A successful finite role check makes source compilation and current-code
classification generate the same actual construction/application instructions.
This concerns the existing finite first-order occurrence compiler, whose
effects, recursive source equations and error handlers are outside its scope. -/
theorem compile_source_eq_code_of_rolesAligned (program : ValueOccurrences.Program)
    (term : ExplicitEvaluation.Term) (aligned : rolesAligned program term = true) :
    ExplicitEvaluation.compile program .source term =
      ExplicitEvaluation.compile program .code term := by
  match term with
  | .value value => rfl
  | .application captured children =>
      have both := aligned
      simp only [rolesAligned, Bool.and_eq_true, decide_eq_true_eq] at both
      have compiled := list program children both.2
        (fun child _ aligned => compile_source_eq_code_of_rolesAligned program child aligned)
      simp only [ExplicitEvaluation.compile, ExplicitEvaluation.childMode,
        ExplicitEvaluation.isCall, compiled, both.1]
      rfl
termination_by sizeOf term
where
  list (program : ValueOccurrences.Program) (children : List ExplicitEvaluation.Term)
      (aligned : rolesAligned.childrenAligned program children = true)
      (ih : ∀ child ∈ children, rolesAligned program child = true →
        ExplicitEvaluation.compile program .source child =
          ExplicitEvaluation.compile program .code child) :
      ExplicitEvaluation.compile.compileList program .source children =
        ExplicitEvaluation.compile.compileList program .code children := by
    induction children with
    | nil => rfl
    | cons child rest tail =>
        simp only [rolesAligned.childrenAligned, Bool.and_eq_true] at aligned
        simp only [ExplicitEvaluation.compile.compileList]
        rw [ih child (List.mem_cons_self ..) aligned.1,
          tail aligned.2 (fun row member => ih row (List.mem_cons_of_mem child member))]

/-- Compiler adequacy supplies exact ordered answers after the independent
role-alignment check. It grants no equality with separately chosen runs. -/
theorem source_answers_eq_code_of_rolesAligned (program : ValueOccurrences.Program)
    (term : ExplicitEvaluation.Term) (aligned : rolesAligned program term = true) :
    ExplicitEvaluation.evaluate program .source term =
      ExplicitEvaluation.evaluate program .code term := by
  rw [← ExplicitEvaluation.execute_compile program .source term,
    ← ExplicitEvaluation.execute_compile program .code term,
    compile_source_eq_code_of_rolesAligned program term aligned]

/-! ## Actual eager source dispatch -/

theorem headClass_passive_iff (program : Program) (head : String) :
    headClass program head = .passive ↔
      Eval.ioHead head = false ∧ StdLib.known head = false ∧
        program.equations.any (·.head == head) = false := by
  cases io : Eval.ioHead head <;> cases primitive : StdLib.known head <;>
    cases authored : program.equations.any (·.head == head) <;>
    simp [headClass, io, primitive, authored]

theorem headClass_authored_iff (program : Program) (head : String) :
    headClass program head = .authored ↔
      Eval.ioHead head = false ∧ StdLib.known head = false ∧
        program.equations.any (·.head == head) = true := by
  cases io : Eval.ioHead head <;> cases primitive : StdLib.known head <;>
    cases authored : program.equations.any (·.head == head) <;>
    simp [headClass, io, primitive, authored]

theorem headClass_primitive_iff (program : Program) (head : String) :
    headClass program head = .primitive ↔
      Eval.ioHead head = false ∧ StdLib.known head = true := by
  cases io : Eval.ioHead head <;> cases primitive : StdLib.known head <;>
    cases authored : program.equations.any (·.head == head) <;>
    simp [headClass, io, primitive, authored]

theorem modelClass_literal_of_noncontrol (program : Program) (head : String)
    (arguments : List Atom)
    (ordinary : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false) :
    modelClass program (.expression (.symbol head :: arguments)) = headClass program head := by
  simp [modelClass, ordinary]

/-- Derive source-class agreement from the check, rather than accepting
agreement as a premise with a native-semantics name. -/
theorem checkOne_selection (program : Program) (snapshot : Snapshot)
    (request : Request) (requirement : Requirement)
    (accepted : checkOne program snapshot request = .ok requirement) :
    requirement.selection = modelClass program request.expression := by
  obtain ⟨fact, _, _, _, equal⟩ :=
    (checkOne_ok_iff program snapshot request requirement).mp accepted
  rw [equal]
  rfl

theorem checkOne_retained_fact (program : Program) (snapshot : Snapshot)
    (request : Request) (requirement : Requirement)
    (accepted : checkOne program snapshot request = .ok requirement) :
    ∃ fact, fact ∈ snapshot.facts ∧ fact.address = request.address ∧
      fact.expression = request.expression ∧
      fact.resolve snapshot.profile = .classified requirement.selection ∧
      requirement.address = request.address ∧ requirement.expression = request.expression ∧
      requirement.capturedRole = fact.role ∧ requirement.dependencies = fact.dependencies := by
  obtain ⟨fact, read, source, selected, equal⟩ :=
    (checkOne_ok_iff program snapshot request requirement).mp accepted
  have member : fact ∈ snapshot.read request.address := by rw [read]; simp
  obtain ⟨inSnapshot, address⟩ := List.mem_filter.mp member
  simp only [decide_eq_true_eq] at address
  refine ⟨fact, inSnapshot, address, source, ?_, ?_⟩
  · simpa only [equal, Requirement.ofFact] using selected
  · simp only [equal, Requirement.ofFact, and_self]

theorem checkManifest_addresses (program : Program) (snapshot : Snapshot)
    (requests : List Request) (requirements : List Requirement)
    (accepted : checkManifest program snapshot requests = .ok requirements) :
    requirements.map Requirement.address = requests.map Request.address := by
  have related := (checkManifest_ok_iff program snapshot requests requirements).mp accepted
  induction related with
  | nil => rfl
  | @cons request requirement rest following checked related ih =>
      obtain ⟨fact, _, _, _, _, address, _⟩ :=
        checkOne_retained_fact program snapshot request requirement checked
      have tail := ih ((checkManifest_ok_iff program snapshot rest following).mpr related)
      simp only [List.map_cons, address, tail]

def Snapshot.readDependencies (snapshot : Snapshot) (address : Address) : List ServiceDependency :=
  (snapshot.read address).flatMap NativeFact.dependencies

/-- This exact list equality retains dependency positions and repetitions,
including negative registry/role reads supplied for passive occurrences. -/
theorem checkManifest_retains_dependencies (program : Program) (snapshot : Snapshot)
    (requests : List Request) (requirements : List Requirement)
    (accepted : checkManifest program snapshot requests = .ok requirements) :
    requirements.flatMap Requirement.dependencies =
      requests.flatMap (fun request => snapshot.readDependencies request.address) := by
  have related := (checkManifest_ok_iff program snapshot requests requirements).mp accepted
  induction related with
  | nil => rfl
  | @cons request requirement rest following checked related ih =>
      obtain ⟨fact, read, _, _, equal⟩ :=
        (checkOne_ok_iff program snapshot request requirement).mp checked
      have tail := ih ((checkManifest_ok_iff program snapshot rest following).mpr related)
      have readDependencies : snapshot.readDependencies request.address = fact.dependencies := by
        simp [Snapshot.readDependencies, read]
      simp only [List.flatMap_cons, equal, Requirement.ofFact, readDependencies, tail]

theorem modelClass_literal_not_control (program : Program) (head : String)
    (arguments : List Atom) (selected : Class)
    (classification : modelClass program (.expression (.symbol head :: arguments)) = selected)
    (notControl : selected ≠ .control) :
    DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false ∧
      headClass program head = selected := by
  have ordinary : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false := by
    cases chosen : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments))
    · rfl
    · have same : selected = .control := by
        simpa only [modelClass, chosen, if_true] using classification.symm
      exact False.elim (notControl same)
  exact ⟨ordinary, (modelClass_literal_of_noncontrol program head arguments ordinary).symm.trans classification⟩

/-- Every control form of the eager driver is a control form of the
declarative rules, so an expression that is not one there is not one in the
driver either. -/
private theorem eager_not_control {atom : Atom}
    (notControl : DeclarativeSpec.controlForm atom = false) :
    EagerDFS.eagerControlForm atom = false := by
  revert notControl
  unfold EagerDFS.eagerControlForm
  split <;> simp [DeclarativeSpec.controlForm]

theorem passive_source_transition (program : Program) (world : EagerDFS.World)
    (bindings : Subst) (head : String) (arguments : List Atom)
    (frames : List EagerDFS.Frame)
    (passive : modelClass program (.expression (.symbol head :: arguments)) = .passive) :
    EagerDFS.LocalTransition program world
      ⟨.evaluate bindings (.expression (.symbol head :: arguments)), frames⟩
      world (.next ⟨.arguments bindings .data (.symbol head :: arguments) [] 0, frames⟩) := by
  have ordinary : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments)) = false := by
    cases selected : DeclarativeSpec.controlForm (.expression (.symbol head :: arguments))
    · rfl
    · simp [modelClass, selected] at passive
  rw [modelClass_literal_of_noncontrol program head arguments ordinary] at passive
  obtain ⟨io, primitive, authored⟩ := (headClass_passive_iff program head).mp passive
  exact .data_enter (eager_not_control ordinary) (by simp [io, primitive, authored])

/-- Successful passive admission enters the actual data branch of the driver.
No unknown application is turned into a language error by this bridge. -/
theorem admitted_passive_localStep (program : Program) (snapshot : Snapshot)
    (address : Address) (world : EagerDFS.World) (bindings : Subst)
    (head : String) (arguments : List Atom) (frames : List EagerDFS.Frame)
    (requirement : Requirement)
    (accepted : checkOne program snapshot
      ⟨address, .expression (.symbol head :: arguments)⟩ = .ok requirement)
    (passive : requirement.selection = .passive) :
    EagerDFS.localStep program world
      ⟨.evaluate bindings (.expression (.symbol head :: arguments)), frames⟩ =
      some (world, .next ⟨.arguments bindings .data (.symbol head :: arguments) [] 0, frames⟩) := by
  have selected := checkOne_selection program snapshot
    ⟨address, .expression (.symbol head :: arguments)⟩ requirement accepted
  exact EagerDFS.local_transition_step
    (passive_source_transition program world bindings head arguments frames (selected.symm.trans passive))

/-- The primitive response is the actual shared primitive call and post-state.
This theorem does not supply the separate host primitive correspondence. -/
theorem primitive_source_response (program : Program) (world : EagerDFS.World)
    (bindings : Subst) (head : String) (values : List Atom) (index : Nat)
    (frames : List EagerDFS.Frame) (after : Effects.State) (answers : List Atom)
    (primitive : headClass program head = .primitive)
    (called : StdLib.apply world.state head values = .ok (after, answers)) :
    EagerDFS.localStep program world
      ⟨.arguments bindings (.function head) [] values index, frames⟩ =
      some ({ world with state := after },
        .alternatives (EagerDFS.returnedBranches answers frames)) := by
  obtain ⟨ordinary, known⟩ := (headClass_primitive_iff program head).mp primitive
  exact EagerDFS.local_transition_step (.primitive ordinary known called)

/-- Authored dispatch uses the actual ordered equation selection. A native
mixed builtin/equation route is refused instead of licensed by this theorem. -/
theorem authored_source_response (program : Program) (world : EagerDFS.World)
    (bindings : Subst) (head : String) (values : List Atom) (index : Nat)
    (frames : List EagerDFS.Frame)
    (authored : headClass program head = .authored) :
    EagerDFS.localStep program world
      ⟨.arguments bindings (.function head) [] values index, frames⟩ =
      some (world, .alternatives (EagerDFS.equationBranches program head values frames)) := by
  obtain ⟨ordinary, unknown, _⟩ := (headClass_authored_iff program head).mp authored
  exact EagerDFS.local_transition_step (.equations ordinary unknown)

theorem admitted_authored_localStep (program : Program) (snapshot : Snapshot)
    (address : Address) (world : EagerDFS.World) (bindings : Subst)
    (head : String) (arguments : List Atom) (frames : List EagerDFS.Frame)
    (requirement : Requirement)
    (accepted : checkOne program snapshot
      ⟨address, .expression (.symbol head :: arguments)⟩ = .ok requirement)
    (authored : requirement.selection = .authored) :
    EagerDFS.localStep program world
      ⟨.evaluate bindings (.expression (.symbol head :: arguments)), frames⟩ =
      some (world, .next ⟨.arguments bindings (.function head) arguments [] 0, frames⟩) := by
  have selected := checkOne_selection program snapshot
    ⟨address, .expression (.symbol head :: arguments)⟩ requirement accepted
  obtain ⟨notControl, classification⟩ := modelClass_literal_not_control program head arguments .authored
    (selected.symm.trans authored) (by decide)
  obtain ⟨io, primitive, callable⟩ := (headClass_authored_iff program head).mp classification
  exact EagerDFS.local_transition_step
    (.call_enter (eager_not_control notControl) (by simp only [io, primitive, callable, Bool.false_or]))

theorem admitted_primitive_source_response (program : Program) (snapshot : Snapshot)
    (address : Address) (world : EagerDFS.World) (bindings : Subst)
    (head : String) (values : List Atom) (index : Nat) (frames : List EagerDFS.Frame)
    (after : Effects.State) (answers : List Atom) (requirement : Requirement)
    (accepted : checkOne program snapshot
      ⟨address, .expression (.symbol head :: values)⟩ = .ok requirement)
    (primitive : requirement.selection = .primitive)
    (called : StdLib.apply world.state head values = .ok (after, answers)) :
    EagerDFS.localStep program world
      ⟨.arguments bindings (.function head) [] values index, frames⟩ =
      some ({ world with state := after },
        .alternatives (EagerDFS.returnedBranches answers frames)) := by
  have selected := checkOne_selection program snapshot
    ⟨address, .expression (.symbol head :: values)⟩ requirement accepted
  have classification := (modelClass_literal_not_control program head values .primitive
    (selected.symm.trans primitive) (by decide)).2
  exact primitive_source_response program world bindings head values index frames after answers classification called

namespace Controls

def emptyProgram : Program := { equations := [], declarations := [] }

def firstAddress : Address := ⟨0, []⟩
def otherAddress : Address := ⟨1, [0]⟩

def unknown : Request := ⟨firstAddress, .expression [.symbol "Uninterpreted", .symbol "a", .symbol "b"]⟩
def ordering : Request := ⟨firstAddress, .expression [.symbol "@<", .symbol "a", .symbol "b"]⟩
def lengthCall : Request := ⟨firstAddress, .expression [.symbol "length", .expression [.symbol "a", .symbol "b"]]⟩

def registryDependency : ServiceDependency := ⟨.operationRegistry, "literal-heads", "registry-v1"⟩
def roleDependency : ServiceDependency := ⟨.compiledRole, "body-occurrence", "role-v1"⟩
def primitiveDependency : ServiceDependency := ⟨.primitive, "+", "integer-service-v1"⟩

def passiveFact (request : Request) : NativeFact :=
  ⟨request.address, request.expression, .data, [], .nativeOnly, .nativeOnly,
    [registryDependency, roleDependency]⟩

def orderingFact : NativeFact :=
  ⟨ordering.address, ordering.expression, .call, [.extended], .nativeOnly,
    .classified .passive, [registryDependency, roleDependency]⟩

def plainOrdering : Snapshot := ⟨.plain, [orderingFact]⟩
def extendedOrdering : Snapshot := ⟨.extended, [orderingFact]⟩

theorem unknown_constructor_admitted :
    checkOne emptyProgram ⟨.extended, [passiveFact unknown]⟩ unknown =
      .ok (Requirement.ofFact emptyProgram unknown (passiveFact unknown)) := by decide

theorem hidden_operation_admitted_as_data :
    checkOne emptyProgram plainOrdering ordering =
      .ok (Requirement.ofFact emptyProgram ordering orderingFact) := by decide

theorem visible_native_operation_refused :
    checkOne emptyProgram extendedOrdering ordering = .error (.nativeOnly firstAddress) := by decide

theorem always_active_native_operation_refused :
    checkOne emptyProgram ⟨.plain,
      [⟨lengthCall.address, lengthCall.expression, .call, [.plain, .extended],
        .nativeOnly, .nativeOnly, [registryDependency]⟩]⟩ lengthCall =
      .error (.nativeOnly firstAddress) := by decide

theorem missing_inventory_is_not_passivity :
    checkOne emptyProgram ⟨.plain, []⟩ unknown = .error (.missing firstAddress) := by decide

theorem duplicate_inventory_refused :
    checkOne emptyProgram ⟨.plain, [passiveFact unknown, passiveFact unknown]⟩ unknown =
      .error (.ambiguous firstAddress) := by decide

theorem changed_source_refused :
    checkOne emptyProgram ⟨.plain, [passiveFact unknown]⟩ ordering =
      .error (.sourceChanged firstAddress) := by decide

theorem dynamic_operation_refused :
    checkOne emptyProgram ⟨.plain, [{ orderingFact with role := .dynamic }]⟩ ordering =
      .error (.dynamic firstAddress) := by decide

def addition : Request :=
  ⟨firstAddress, .expression [.symbol "+", .grounded (.int 1), .grounded (.int 2)]⟩

def additionFact : NativeFact :=
  ⟨addition.address, addition.expression, .call, [.plain, .extended],
    .classified .primitive, .classified .primitive, [primitiveDependency, primitiveDependency]⟩

def additionSnapshot : Snapshot := ⟨.extended, [additionFact]⟩

theorem primitive_admitted_with_retained_requirements :
    checkOne emptyProgram additionSnapshot addition =
      .ok (Requirement.ofFact emptyProgram addition additionFact) := by decide

theorem primitive_admission_uses_actual_integer_service (world : EagerDFS.World)
    (bindings : Subst) (frames : List EagerDFS.Frame) :
    EagerDFS.localStep emptyProgram world
      ⟨.arguments bindings (.function "+") [] [.grounded (.int 1), .grounded (.int 2)] 2, frames⟩ =
      some (world, .alternatives [⟨.returned (.grounded (.int 3)), frames⟩]) := by
  have called := StdLib.integer_addition world.state 1 2
  have stepped := admitted_primitive_source_response emptyProgram additionSnapshot firstAddress world
    bindings "+" [.grounded (.int 1), .grounded (.int 2)] 2 frames world.state
      [.grounded (.int 3)] _ primitive_admitted_with_retained_requirements rfl called
  simpa only [EagerDFS.returnedBranches, List.map_cons, List.map_nil] using stepped

def mixedProgram : Program :=
  { equations := [⟨"+", [.var "x", .var "y"], .symbol "authored"⟩], declarations := [] }

theorem extended_builtin_equation_mixture_refused :
    checkOne mixedProgram ⟨.extended,
      [{ additionFact with visible := .mixedEquations }]⟩ addition =
      .error (.mixedEquations firstAddress) := by decide

theorem protected_builtin_definition_refused :
    checkOne mixedProgram ⟨.plain,
      [{ additionFact with visible := .protectedDefinition }]⟩ addition =
      .error (.protectedDefinition firstAddress) := by decide

theorem ordered_occurrence_and_service_duplicates_retained :
    checkManifest emptyProgram additionSnapshot [addition, addition] = .ok
      [Requirement.ofFact emptyProgram addition additionFact,
        Requirement.ofFact emptyProgram addition additionFact] ∧
    ([Requirement.ofFact emptyProgram addition additionFact,
      Requirement.ofFact emptyProgram addition additionFact].flatMap Requirement.dependencies) =
        [primitiveDependency, primitiveDependency, primitiveDependency, primitiveDependency] := by decide

theorem inventory_order_does_not_reorder_requests :
    let second := { addition with address := otherAddress }
    let secondFact := { additionFact with address := otherAddress }
    checkManifest emptyProgram ⟨.extended, [secondFact, additionFact]⟩ [addition, second] =
      .ok [Requirement.ofFact emptyProgram addition additionFact,
        Requirement.ofFact emptyProgram second secondFact] := by decide

theorem passive_admission_enters_actual_data_branch (world : EagerDFS.World)
    (bindings : Subst) (frames : List EagerDFS.Frame) :
    EagerDFS.localStep emptyProgram world
      ⟨.evaluate bindings unknown.expression, frames⟩ =
      some (world, .next ⟨.arguments bindings .data
        [.symbol "Uninterpreted", .symbol "a", .symbol "b"] [] 0, frames⟩) :=
  admitted_passive_localStep emptyProgram ⟨.extended, [passiveFact unknown]⟩ firstAddress world
    bindings "Uninterpreted" [.symbol "a", .symbol "b"] frames _ unknown_constructor_admitted rfl

def laterProgram : Program :=
  { equations := [⟨"early", [], .expression [.symbol "later"]⟩,
    ⟨"later", [], .symbol "result"⟩], declarations := [] }

def laterOccurrence : Request := ⟨⟨0, [0]⟩, .expression [.symbol "later"]⟩

def laterFact : NativeFact :=
  ⟨laterOccurrence.address, laterOccurrence.expression, .data, [.plain, .extended],
    .classified .authored, .classified .authored, [roleDependency, registryDependency]⟩

theorem previously_captured_data_ignores_new_callability :
    laterFact.resolve .extended = .classified .passive := by decide

theorem imported_later_head_collision_refused :
    checkOne laterProgram ⟨.extended, [laterFact]⟩ laterOccurrence =
      .error (.collision laterOccurrence.address .authored .passive) := by decide

theorem predeclared_later_head_admitted :
    checkOne laterProgram ⟨.extended, [{ laterFact with role := .call }]⟩ laterOccurrence =
      .ok (Requirement.ofFact laterProgram laterOccurrence { laterFact with role := .call }) := by decide

theorem captured_role_erasure_cannot_support_dispatch :
    ¬ (policyFamily laterProgram [laterOccurrence]).SupportsReadout forgetCapturedRoles := by
  intro supported
  have compatible := (policyFamily laterProgram [laterOccurrence]).supportsReadout_implies_compatible
    forgetCapturedRoles supported
  have same := compatible ⟨.extended, [laterFact]⟩ ⟨.extended, [{ laterFact with role := .call }]⟩ rfl
    ⟨laterOccurrence, List.mem_cons_self ..⟩
  change checkOne laterProgram ⟨.extended, [laterFact]⟩ laterOccurrence =
    checkOne laterProgram ⟨.extended, [{ laterFact with role := .call }]⟩ laterOccurrence at same
  rw [imported_later_head_collision_refused, predeclared_later_head_admitted] at same
  cases same

theorem authored_admission_enters_actual_function_branch (world : EagerDFS.World)
    (bindings : Subst) (frames : List EagerDFS.Frame) :
    EagerDFS.localStep laterProgram world
      ⟨.evaluate bindings laterOccurrence.expression, frames⟩ =
      some (world, .next ⟨.arguments bindings (.function "later") [] [] 0, frames⟩) :=
  admitted_authored_localStep laterProgram ⟨.extended, [{ laterFact with role := .call }]⟩
    laterOccurrence.address world bindings "later" [] frames _ predeclared_later_head_admitted rfl

theorem profile_erasure_cannot_support_dispatch :
    ¬ (policyFamily emptyProgram [ordering]).SupportsReadout Snapshot.facts := by
  intro supported
  have compatible := (policyFamily emptyProgram [ordering]).supportsReadout_implies_compatible
    Snapshot.facts supported
  have same := compatible plainOrdering extendedOrdering rfl
    ⟨ordering, List.mem_cons_self ..⟩
  change checkOne emptyProgram plainOrdering ordering =
    checkOne emptyProgram extendedOrdering ordering at same
  rw [hidden_operation_admitted_as_data, visible_native_operation_refused] at same
  cases same

theorem selected_profile_change_is_not_current :
    ¬ (dependencies [ordering]).SameDependencies plainOrdering extendedOrdering := by
  intro same
  have changed := congrArg Prod.fst
    (same ⟨firstAddress, List.mem_cons_self ..⟩)
  change Profile.plain = Profile.extended at changed
  cases changed

def replacedPrimitiveFact : NativeFact :=
  { additionFact with dependencies := [{ primitiveDependency with identity := "integer-service-v2" }] }

theorem selected_service_change_is_not_current :
    ¬ (dependencies [addition]).SameDependencies additionSnapshot
      ⟨.extended, [replacedPrimitiveFact]⟩ := by
  intro same
  have read := congrArg Prod.snd (same ⟨firstAddress, List.mem_cons_self ..⟩)
  change [additionFact] = [replacedPrimitiveFact] at read
  have facts := List.cons.inj read
  have services := congrArg NativeFact.dependencies facts.1
  have different : additionFact.dependencies ≠ replacedPrimitiveFact.dependencies := by decide
  exact different services

theorem unrelated_inventory_addition_preserves_manifest :
    checkManifest emptyProgram plainOrdering [ordering] =
      checkManifest emptyProgram
        { plainOrdering with facts := plainOrdering.facts ++
          [{ passiveFact unknown with address := otherAddress }] } [ordering] := by
  apply checkManifest_unrelated_append
  intro fact member
  simp only [List.mem_singleton] at member
  subst fact
  decide

theorem source_role_collision_fails_alignment :
    rolesAligned ExplicitEvaluation.Examples.current ExplicitEvaluation.Examples.late = false := by decide

theorem old_source_role_and_current_code_have_different_answers :
    ExplicitEvaluation.evaluate ExplicitEvaluation.Examples.current .source ExplicitEvaluation.Examples.late ≠
      ExplicitEvaluation.evaluate ExplicitEvaluation.Examples.current .code ExplicitEvaluation.Examples.late := by decide

def predeclaredLater : ExplicitEvaluation.Term :=
  .application true [.value (.symbol "late")]

theorem current_source_roles_pass_alignment :
    rolesAligned ExplicitEvaluation.Examples.current predeclaredLater = true := by decide

theorem aligned_source_compiler_preserves_duplicate_answers :
    ExplicitEvaluation.execute ExplicitEvaluation.Examples.current
      (ExplicitEvaluation.compile ExplicitEvaluation.Examples.current .source predeclaredLater) =
      [.symbol "answer", .symbol "answer"] := by decide

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.CettaOperationAdmission
