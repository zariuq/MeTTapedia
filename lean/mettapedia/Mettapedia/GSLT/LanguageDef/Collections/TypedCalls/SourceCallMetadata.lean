import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SourceContractReturns
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.BoundaryProtocol
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingRetainedFrames

/-!
# Source call receipts and the separate typed boundary

`PeTTa.Unifying` implements argument demand and body/head unification, not
declaration entry/result guards. Those guards remain the existing
`BoundaryProtocol.pettaRow`. This module composes earned raw source receipts
with that boundary and distinguishes conservative unknown-call flags from
known ground-polymorphic results. It does not identify raw source dispatch
with a complete typed native call.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SourceCallMetadata

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi
open Mettapedia.Machines.TypedBoundary
open UnifyingFrames SourceCallAliasTransport SourceGroundEntryFacts SourceContractReturns

def unknownFlags : ContractBindingFacts.ValueFlags := ⟨⟨false, false⟩, false⟩

/-- Unknown completed replies make no groundness or uninterpretedness claim.
This is deliberately weaker than a type or purity certificate. -/
theorem unknown_reply_faithful (decls : Decls) (answer : Unifying.Answer) :
    GroundUninterpretedVersions.Faithful decls (answer.value, readBindings answer.bindings) unknownFlags := by
  exact ⟨rfl, fun impossible => by cases impossible⟩

theorem unknown_reply_strict (decls : Decls) (answer : Unifying.Answer) :
    ContractBindingFacts.ValueFaithful decls (readBindings answer.bindings) answer.value unknownFlags := by
  constructor <;> intro impossible <;> cases impossible

theorem protected_reply_strict {decls : Decls} (answer : Unifying.Answer)
    (earned : GroundUninterpretedVersions.Faithful decls
      (answer.value, readBindings answer.bindings) protectedFlags) :
    ContractBindingFacts.ValueFaithful decls (readBindings answer.bindings) answer.value protectedFlags := by
  exact ⟨fun _ => (earned.2 rfl).1, fun _ => (earned.2 rfl).2 rfl⟩

theorem unknown_call_flags (arguments : List ContractBindingFacts.ValueFlags)
    (reached : GroundUninterpretedVersions.anyBottom arguments = false) :
    GroundUninterpretedVersions.keptValue arguments = unknownFlags := by
  simp [GroundUninterpretedVersions.keptValue, reached, unknownFlags]

theorem unknown_reply_does_not_admit_ground_version :
    GroundUninterpretedVersions.meets .ground [.uninterpreted] [unknownFlags] = false := by
  decide +kernel

/-- A single polymorphic row enters the actual row boundary once on an
uninterpreted value. Unrelated declaration overloads are allowed. -/
theorem polymorphic_entry_once {decls : Decls} (kind : Atom → String) (value : Atom)
    (clean : Uninterp decls value) :
    ((BoundaryProtocol.pettaRow decls kind [.var "a"] (.var "a")).enter [value]).card = 1 := by
  obtain ⟨derivation, _, typed, _, equations, _⟩ :=
    UninterpretedLocalMultiplicity.struct_clean Atom.var value (fun _ => trivial) clean
  have demanded : demand (Ty.var "a" : Ty String) = .guarded := by decide +kernel
  simp only [BoundaryProtocol.pettaRow, Multiset.card_map, guards, demanded, if_true]
  rw [guard_var_uninterp StoreOK.nil typed equations]
  simp

/-- The source-derived ground result certificate discharges the separately
modeled typed boundary. The body receipt is not an assumed output oracle. -/
theorem known_body_boundary {registry : SpaceSemantics.Program} {decls : Decls}
    (bindings : MORK.Subst) (valid : Unifying.Idempotent bindings) (name : String)
    (expression : Atom) (inspectionFuel : Nat)
    (checked : Unifying.checksReturnVariable name inspectionFuel expression = true)
    (state : Effects.State) (input output : List Atom) (use : Nat)
    (entry : GroundData decls (Unifying.resolve bindings (.var name)))
    {fuel : Nat} {after : Effects.State} {values remaining printed : List Atom}
    (completed : Unifying.run registry fuel
      { state, control := .evaluate bindings expression, input, output, uses := use } =
        .complete after values remaining printed) (kind : Atom → String) :
    ((BoundaryProtocol.pettaRow decls kind [.var "a"] (.var "a")).enter
      [Unifying.resolve bindings (.var name)]).card = 1 ∧
    (BoundaryProtocol.pettaRow decls kind [.var "a"] (.var "a")).run
      (fun _ => (values : Multiset Atom)) [Unifying.resolve bindings (.var name)] = (values : Multiset Atom) := by
  refine ⟨polymorphic_entry_once kind _ entry.2, ?_⟩
  rw [BoundaryProtocol.petta_row_run decls kind [.var "a"] (.var "a")
    (fun _ => (values : Multiset Atom)) [Unifying.resolve bindings (.var name)]]
  exact checked_source_guard_exact bindings valid name expression inspectionFuel checked
    state input output use entry completed kind

/-- The same actual body receipt reaches its answer packets above an
arbitrary retained caller. No sibling-frame refinement is presumed. -/
theorem known_body_above_caller {registry : SpaceSemantics.Program} {decls : Decls}
    (bindings : MORK.Subst) (valid : Unifying.Idempotent bindings) (name : String)
    (expression : Atom) (returns : Unifying.ReturnsVariable name expression)
    (state : Effects.State) (input output : List Atom) (use : Nat)
    (entry : GroundData decls (Unifying.resolve bindings (.var name)))
    {fuel : Nat} {after : Effects.State} {values remaining printed : List Atom}
    (completed : Unifying.run registry fuel
      { state, control := .evaluate bindings expression, input, output, uses := use } =
        .complete after values remaining printed) (suffix : List Unifying.Frame) :
    ∃ final answers,
      Relation.ReflTransGen (Unifying.Transition registry)
        { state, control := .evaluate bindings expression, frames := suffix, input, output, uses := use } final ∧
      final.control = .returned answers ∧ final.frames = suffix ∧
      final.state = after ∧ final.input = remaining ∧ final.output = printed ∧
      values = List.replicate answers.length (Unifying.resolve bindings (.var name)) ∧
      ∀ answer ∈ answers, GroundUninterpretedVersions.Faithful decls
        (answer.value, readBindings answer.bindings) protectedFlags := by
  obtain ⟨final, answers, steps, returned, frames, finalState, finalInput, finalOutput, packets, counted⟩ :=
    Unifying.completed_protected_return bindings valid name expression returns state input output use
      (source_ground_of_support _ entry.1) completed
  refine ⟨Unifying.appendFrames final suffix, answers, Unifying.steps_append_frames steps suffix, returned,
    by simp [Unifying.appendFrames, frames], finalState, finalInput, finalOutput, counted, ?_⟩
  intro answer present
  rw [packets answer present]
  exact protected_value_faithful answer.bindings _ entry

namespace Controls

def num (n : Int) : Atom := .grounded (.int n)
def str (text : String) : Atom := .grounded (.string text)

def wrongRange : SpaceSemantics.Program where
  equations := [⟨"bad", [.var "x"], str "a"⟩]
  declarations := [.expression [.symbol ":", .symbol "bad", .expression [.symbol "->", .var "t", .var "t"]]]
  layout := [.equation, .declaration]

/-- Raw source dispatch does not perform the declared range guard. -/
theorem raw_dispatch_does_not_check_range :
    Unifying.observed (Unifying.run wrongRange 100 (Unifying.start (Effects.loaded wrongRange)
      (.expression [.symbol "bad", num 1]))) = .answers [str "a"] := by decide +kernel

theorem separate_row_boundary_rejects_wrong_range :
    (BoundaryProtocol.pettaRow TypedCalls.Controls.decls TypedCalls.Controls.probeKind
      [.var "t"] (.var "t")).run (fun _ => ({str "a"} : Multiset Atom)) [num 1] = 0 := by
  rw [BoundaryProtocol.petta_row_run TypedCalls.Controls.decls TypedCalls.Controls.probeKind
    [.var "t"] (.var "t") (fun _ => ({str "a"} : Multiset Atom)) [num 1]]
  exact TypedCalls.Controls.shared_variable_checks_result

/-- A closed type guard can accept an open logic variable. Its success
therefore does not justify a native ground-value flag. -/
theorem closed_range_check_does_not_imply_ground (decls : Decls) (grounded : String → Bool) :
    guardCount (info decls (.var "open")) (.sym "Number") (metatype grounded (.var "open")) = 1 ∧
      MORK.isGroundAtom (.var "open") = false := by
  refine ⟨?_, rfl⟩
  rw [guardCount_of_not_meta (by decide +kernel), count_var]

theorem separate_closed_boundary_keeps_open_reply (decls : Decls) (grounded : String → Bool) :
    (BoundaryProtocol.pettaRow decls (metatype grounded) [] (.sym "Number")).run
      (fun _ => ({.var "open"} : Multiset Atom)) [] = {.var "open"} := by
  have factors := BoundaryProtocol.petta_closed_factors decls (metatype grounded) [] (.sym "Number")
    (fun _ => ({.var "open"} : Multiset Atom)) []
  have counted := (closed_range_check_does_not_imply_ground decls grounded).1
  simpa [argCount, ResultGuarded, Unchecked, Ty.lift, counted, one_nsmul] using factors

def declared : Decls := fun name => if name = "Known" then [.sym "Tag"] else []
def openClaim : ContractBindingFacts.ValueFlags := ⟨⟨false, true⟩, false⟩

/-- The older certificate only protects ground claims. It cannot by itself
justify a dynamic-head rule that tests an open uninterpreted flag alone. -/
theorem ground_faithful_is_not_a_dynamic_head_certificate :
    GroundUninterpretedVersions.Faithful declared (.symbol "Known", readBindings []) openClaim ∧
      ¬ ContractBindingFacts.ValueFaithful declared (readBindings []) (.symbol "Known") openClaim := by
  refine ⟨⟨rfl, fun impossible => by cases impossible⟩, ?_⟩
  intro strict
  have impossible := strict.2 rfl
  simp [Uninterp, Safe, substA, declared] at impossible

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.SourceCallMetadata
