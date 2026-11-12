import Mettapedia.GSLT.LanguageDef.OwnershipRefinement

/-!
# Composition of separately admitted ownership interfaces

The checker resolves the ordered external-definition records, retains native
and unchecked calls as open obligations, and closes a call only with an admitted
body and a compatible contract. Prototype, callback and layout keys are ordinary
canonical declaration data, not a model of C execution. Source projection,
actual linker selection and compiler fidelity remain separate boundaries.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Ownership.Composition

open Mettapedia.Machines.CMemory.Borrowing
open Mettapedia.Machines.CMemory.PermissionFlow
open Refinement

structure Contract where
  signature : Signature
  prototype : String
  callbacks : String
  records : List (String × String)
  deriving DecidableEq, Repr

def recordsAgree (left right : List (String × String)) : Bool :=
  left.all fun a => right.all fun b => a.1 != b.1 || a.2 == b.2

theorem recordsAgree_iff (left right : List (String × String)) :
    recordsAgree left right = true ↔
      ∀ a ∈ left, ∀ b ∈ right, a.1 = b.1 → a.2 = b.2 := by
  simp only [recordsAgree, List.all_eq_true, Bool.or_eq_true_iff, bne_iff_ne, beq_iff_eq]
  constructor
  · intro accepted a present b member same
    exact (accepted a present b member).resolve_left (not_not_intro same)
  · intro accepted a present b member
    by_cases same : a.1 = b.1
    · exact Or.inr (accepted a present b member same)
    · exact Or.inl same

def satisfies (provided expected : Contract) : Bool :=
  signatureRefines provided.signature expected.signature &&
    decide (provided.prototype = expected.prototype) &&
    decide (provided.callbacks = expected.callbacks) && recordsAgree expected.records provided.records

theorem satisfies_signature {provided expected : Contract}
    (accepted : satisfies provided expected = true) :
    signatureRefines provided.signature expected.signature = true := by
  simp only [satisfies, Bool.and_eq_true] at accepted
  exact accepted.1.1.1

structure CheckedBody where
  unit : Module
  admitted : admit unit = true
  fn : Function
  member : fn ∈ unit.functions

theorem CheckedBody.checked (body : CheckedBody) : admitFunction body.unit.callables body.fn = true := by
  have accepted := body.admitted
  simp only [admit, Bool.and_eq_true] at accepted
  exact List.all_eq_true.mp accepted.2 body.fn body.member

structure Definition where
  name : String
  contract : Contract
  checked : Bool
  body : Option CheckedBody
  obligation : String

structure Assumption where
  name : String
  contract : Contract
  obligation : String
  deriving DecidableEq, Repr

def certified (definition : Definition) : Bool :=
  match definition.body with
  | none => false
  | some body => body.fn.name == definition.name &&
      decide (body.fn.signature = definition.contract.signature)

theorem certified_body {definition : Definition} (accepted : certified definition = true) :
    ∃ body, definition.body = some body ∧ body.fn.name = definition.name ∧
      body.fn.signature = definition.contract.signature := by
  cases stored : definition.body with
  | none => simp [certified, stored] at accepted
  | some body =>
      simp only [certified, stored, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at accepted
      exact ⟨body, rfl, accepted.1, accepted.2⟩

def select (definitions : List Definition) (name : String) : Option Definition :=
  definitions.find? fun definition => definition.name == name

inductive Resolution where
  | closed (definition : Definition)
  | unchecked (isMatch : Bool)
  | native

def classify (definitions : List Definition) (assumption : Assumption) : Option Resolution :=
  match select definitions assumption.name with
  | none => some .native
  | some definition =>
      if definition.checked then
        if certified definition && satisfies definition.contract assumption.contract then
          some (.closed definition)
        else none
      else if definition.obligation.isEmpty then none
      else some (.unchecked (satisfies definition.contract assumption.contract))

theorem closed_has_evidence {definitions : List Definition} {assumption : Assumption}
    {definition : Definition}
    (accepted : classify definitions assumption = some (.closed definition)) :
    select definitions assumption.name = some definition ∧ definition.checked = true ∧
      certified definition = true ∧ satisfies definition.contract assumption.contract = true := by
  unfold classify at accepted
  split at accepted
  · cases Option.some.inj accepted
  · rename_i selected found
    split at accepted
    · rename_i checked
      split at accepted
      · rename_i compatible
        cases Option.some.inj accepted
        have facts := Bool.and_eq_true_iff.mp compatible
        exact ⟨found, checked, facts.1, facts.2⟩
      · contradiction
    · split at accepted
      · contradiction
      · cases Option.some.inj accepted

def invokeResolution (assumption : Assumption) (resolution : Resolution)
    (state : State) (arguments : List Argument) : Option State :=
  match resolution with
  | .closed definition => invoke definition.contract.signature state arguments
  | .unchecked _ | .native => invoke assumption.contract.signature state arguments

theorem resolution_preserves_invocation {definitions : List Definition} {assumption : Assumption}
    {resolution : Resolution} (accepted : classify definitions assumption = some resolution)
    (state : State) (arguments : List Argument) :
    invokeResolution assumption resolution state arguments = invoke assumption.contract.signature state arguments := by
  cases resolution with
  | native => rfl
  | unchecked isMatch => rfl
  | closed definition =>
      exact signatureRefines_invocation
        (satisfies_signature (closed_has_evidence accepted).2.2.2) state arguments

theorem closed_return_respects_caller {definitions : List Definition} {assumption : Assumption}
    {definition : Definition} (accepted : classify definitions assumption = some (.closed definition))
    {body : CheckedBody} (stored : definition.body = some body) {outcome : Exit State}
    (execution : Execution (enabled body.unit.callables body.fn) body.fn.body initial outcome)
    (returned : outcome.kind = .returned) :
    ∃ result, instantiateResult body.fn.inputs assumption.contract.signature.result = some result ∧
      returnAllowed result outcome.state = true := by
  obtain ⟨_, _, certifiedDefinition, compatible⟩ := closed_has_evidence accepted
  have typed := certifiedDefinition
  simp only [certified, stored, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at typed
  have admitted := body.checked
  have instantiates : expectedResult body.fn = some body.fn.result := by
    simp only [admitFunction, Bool.and_eq_true, decide_eq_true_eq] at admitted
    exact admitted.1.1.2
  have refined := signatureRefines_result (satisfies_signature compatible)
  rw [← typed.2] at refined
  obtain ⟨result, instantiated, implication⟩ := instantiate_refinement refined instantiates
  exact ⟨result, instantiated, resultRefines_preserves_return implication outcome.state
    (admitted_return_contract body.checked execution returned)⟩

def classifyAll (definitions : List Definition) : List Assumption → Option (List Resolution)
  | [] => some []
  | first :: rest => do
      let resolved ← classify definitions first
      let remaining ← classifyAll definitions rest
      pure (resolved :: remaining)

theorem classifyAll_sound {definitions : List Definition} {assumptions : List Assumption}
    {resolutions : List Resolution} (accepted : classifyAll definitions assumptions = some resolutions) :
    List.Forall₂ (fun assumption resolution => classify definitions assumption = some resolution)
      assumptions resolutions := by
  induction assumptions generalizing resolutions with
  | nil => simp [classifyAll] at accepted; subst resolutions; exact .nil
  | cons first rest ih =>
      obtain ⟨resolved, firstAccepted, remainder⟩ := Option.bind_eq_some_iff.mp accepted
      obtain ⟨remaining, restAccepted, same⟩ := Option.bind_eq_some_iff.mp remainder
      cases Option.some.inj same
      exact .cons firstAccepted (ih restAccepted)

structure Program where
  targets : List (String × Bool)
  definitions : List Definition
  assumptions : List Assumption

def targetsAgree : List (String × Bool) → Bool
  | [] => true
  | first :: rest => rest.all (· == first)

def check (program : Program) : Option (List Resolution) := do
  require (targetsAgree program.targets)
  classifyAll program.definitions program.assumptions

theorem check_sound {program : Program} {resolutions : List Resolution}
    (accepted : check program = some resolutions) :
    targetsAgree program.targets = true ∧
      List.Forall₂ (fun assumption resolution =>
        classify program.definitions assumption = some resolution) program.assumptions resolutions := by
  obtain ⟨_, target, classified⟩ := Option.bind_eq_some_iff.mp accepted
  exact ⟨by simpa [require] using target, classifyAll_sound classified⟩

theorem classified_closed_cannot_lack_body {definitions : List Definition} {assumption : Assumption}
    {definition : Definition} (accepted : classify definitions assumption = some (.closed definition)) :
    definition.body ≠ none := by
  obtain ⟨body, stored, _, _⟩ := certified_body (closed_has_evidence accepted).2.2.1
  simp [stored]

namespace Controls

private def signature : Signature := ⟨[], false, .value, [], []⟩
private def contract : Contract := ⟨signature, "int(void)", "()", []⟩
private def caller : Assumption := ⟨"value", contract, "The definition meets its declared interface."⟩
private def unresolved : Definition := ⟨"value", contract, true, none, ""⟩
private def nativeBody : Definition := ⟨"value", contract, false, none, "Native implementation."⟩
private def function : Function := ⟨"value", signature, [], [], .value, .ret⟩
private def fixture : Module := ⟨[], [function]⟩
private def body : CheckedBody := ⟨fixture, by decide, function, by simp [fixture]⟩
private def provider : Definition := { unresolved with body := some body }

theorem admitted_definition_closes_call : classify [provider] caller = some (.closed provider) := by rfl

theorem checked_flag_without_admission_refused : classify [unresolved] caller = none := by decide
theorem native_dependency_is_open : classify [] caller = some .native := by rfl
theorem unchecked_dependency_is_open :
    classify [nativeBody] caller = some (.unchecked true) := by rfl
theorem mismatched_unchecked_is_open :
    classify [{ nativeBody with contract := { contract with prototype := "long(void)" } }] caller =
      some (.unchecked false) := by rfl
theorem shared_complete_layout_mismatch_refused :
    recordsAgree [("struct R", "size=8")] [("struct R", "size=16")] = false := by decide
theorem opaque_layout_does_not_invent_a_layout :
    recordsAgree [] [("struct R", "size=16")] = true := by rfl
theorem target_mismatch_refused :
    targetsAgree [("x86-sysv", true), ("aarch64", true)] = false := by decide
theorem char_signedness_mismatch_refused :
    targetsAgree [("x86-sysv", true), ("x86-sysv", false)] = false := by decide

end Controls

#print axioms closed_return_respects_caller
#print axioms resolution_preserves_invocation
#print axioms check_sound

end Mettapedia.GSLT.LanguageDef.Ownership.Composition
