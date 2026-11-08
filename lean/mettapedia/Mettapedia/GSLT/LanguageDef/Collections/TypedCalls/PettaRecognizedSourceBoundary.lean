import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaGroundSourceBoundary

/-!
# Source delivery from a recognized private input/result pair

The native-shaped metadata test earns the shared input/result variable;
the instantiated-row codec earns the two actual caller reads. The protected
source-return checker and real source run then earn the delivered values and
their concrete intrinsic return checks. Other nonconstant requests retain
their reached values. CONSTANT exclusions keep their separate effective
query and residual-instance obligations; this module does not erase them.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaRecognizedSourceBoundary

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi
open Mettapedia.Logic.LP (Subst)
open IntrinsicTypeFacts (TypeTerm signature Declaration)
open IndependentTypeOutput (Path)
open StableGroundTypeQueries (GroundUninterpreted)
open PettaContractRowIsolation (Parameter recognizes)
open PettaRowTypeCodec (encode)
open PettaPrivateGroundBoundary (entered)

variable (V : Type) [DecidableEq V] [BEq V] [LawfulBEq V]

/-- A decoded row and its actual instantiation/caller coordinates. The
recognition field is the computed occurrence test, not an assumed guard law.
Native plan/heap decoding must produce these fields before using the bridge. -/
structure Frame where
  before : List (Parameter V)
  current : Parameter V
  after : List (Parameter V)
  authoredRange : Ty String
  resolvedRange : Ty V
  name : V
  recognized : recognizes before current after authoredRange resolvedRange = some name
  sourceNames : String → Nat
  residualNames : V → Nat
  injective : Function.Injective residualNames
  instance_ : String → Ty V
  caller : Subst signature
  reads : ∀ variableName, caller (sourceNames variableName) = encode residualNames (instance_ variableName)
  resolved : ∀ parameter ∈ before ++ current :: after,
    parameter.authored.bind instance_ = parameter.resolved
  rangeResolved : authoredRange.bind instance_ = resolvedRange

variable {V}

def Frame.inputRequest (frame : Frame V) : TypeTerm := encode frame.sourceNames frame.current.authored
def Frame.resultRequest (frame : Frame V) : TypeTerm := encode frame.sourceNames frame.authoredRange

omit [LawfulBEq V] in
theorem Frame.input_read (frame : Frame V) :
    frame.caller.applyTerm frame.inputRequest = .var (frame.residualNames frame.name) := by
  have fields := PettaContractRowIsolation.recognition_fields frame.before frame.current frame.after
    frame.authoredRange frame.resolvedRange frame.name frame.recognized
  rw [Frame.inputRequest, PettaRowTypeCodec.encoded_instantiation _ _ _ _ frame.reads,
    frame.resolved frame.current (by simp), fields.2.2.2.2.1, encode]

omit [LawfulBEq V] in
theorem Frame.result_read (frame : Frame V) :
    frame.caller.applyTerm frame.resultRequest = .var (frame.residualNames frame.name) := by
  have fields := PettaContractRowIsolation.recognition_fields frame.before frame.current frame.after
    frame.authoredRange frame.resolvedRange frame.name frame.recognized
  rw [Frame.resultRequest, PettaRowTypeCodec.encoded_instantiation _ _ _ _ frame.reads,
    frame.rangeResolved, fields.1, encode]

theorem Frame.other_requests_unchanged (frame : Frame V) (subject : TypeTerm) :
    ∀ parameter ∈ frame.before ++ frame.after, parameter.constant = false →
      (entered frame.caller (frame.residualNames frame.name) subject).applyTerm
        (encode frame.sourceNames parameter.authored) =
      frame.caller.applyTerm (encode frame.sourceNames parameter.authored) := by
  apply PettaRowTypeCodec.recognized_pair_preserves_source_requests frame.before frame.current frame.after
    frame.authoredRange frame.resolvedRange frame.name frame.recognized frame.sourceNames
    frame.residualNames frame.injective frame.instance_ frame.caller frame.reads
  intro parameter member _
  apply frame.resolved parameter
  simpa only [List.mem_append, List.mem_cons] using
    (show parameter ∈ frame.before ∨ parameter = frame.current ∨ parameter ∈ frame.after from
      (List.mem_append.mp member).elim Or.inl (fun tail => Or.inr (Or.inr tail)))

/-- Named end-to-end body/delivery boundary: neither the input's unknown
type variable nor the body's returned value is an admission premise.
They follow from the instantiated row and checked source program. -/
theorem recognized_source_delivery (frame : Frame V) {program : SpaceSemantics.Program}
    (bindings : MORK.Subst) (valid : Unifying.Idempotent bindings) (parameter : String)
    (body : Atom) (inspectionFuel : Nat)
    (checked : Unifying.checksReturnVariable parameter inspectionFuel body = true)
    (state : Effects.State) (input output : List Atom) (use : Nat)
    (representation : TypeTerm)
    (encoded : PettaGroundSourceBoundary.encodeGround (Unifying.resolve bindings (.var parameter)) = some representation)
    (library : List Declaration) (queryFuel : Nat) (path : Path)
    (admitted : GroundUninterpreted library representation) (enough : representation.size ≤ queryFuel)
    {fuel : Nat} {after : Effects.State} {values remaining printed : List Atom}
    (completed : Unifying.run program fuel
      { state, control := .evaluate bindings body, input, output, uses := use } =
        .complete after values remaining printed) :
    StableGroundGuardDischarge.check library queryFuel path frame.caller representation frame.inputRequest =
        some [entered frame.caller (frame.residualNames frame.name) representation] ∧
    (∀ other ∈ frame.before ++ frame.after, other.constant = false →
      (entered frame.caller (frame.residualNames frame.name) representation).applyTerm
        (encode frame.sourceNames other.authored) =
      frame.caller.applyTerm (encode frame.sourceNames other.authored)) ∧
    ∃ final answers,
      Relation.ReflTransGen (Unifying.Transition program)
        { state, control := .evaluate bindings body, input, output, uses := use } final ∧
      final.control = .returned answers ∧ final.frames = [] ∧
      final.state = after ∧ final.input = remaining ∧ final.output = printed ∧
      values = List.replicate answers.length (Unifying.resolve bindings (.var parameter)) ∧
      (∀ answer ∈ answers, Unifying.BindingRefines bindings answer.bindings) ∧
      (∀ answer ∈ answers, PettaGroundSourceBoundary.encodeGround
        (Unifying.resolve answer.bindings answer.value) = some representation) ∧
      (∀ refinements : Unifying.Answer → Subst signature,
        answers.map (fun answer => StableGroundGuardDischarge.check library queryFuel path
          (Subst.comp (refinements answer) (entered frame.caller (frame.residualNames frame.name) representation))
          representation frame.resultRequest) =
        answers.map (fun answer => some [Subst.comp (refinements answer)
          (entered frame.caller (frame.residualNames frame.name) representation)])) := by
  have source := PettaGroundSourceBoundary.checked_source_delivers_readonly_guards bindings valid parameter
    body inspectionFuel checked state input output use representation encoded library queryFuel path
    frame.caller frame.inputRequest frame.resultRequest (frame.residualNames frame.name)
    frame.input_read frame.result_read admitted enough completed
  exact ⟨source.1, frame.other_requests_unchanged representation, source.2⟩

namespace Controls

def sourceName (name : String) : Nat := if name = "a" then 0 else 1

def frame : Frame Nat where
  before := [⟨.sym "Number", .sym "Number", false⟩]
  current := ⟨.var "a", .var 0, false⟩
  after := []
  authoredRange := .var "a"
  resolvedRange := .var 0
  name := 0
  recognized := by decide +kernel
  sourceNames := sourceName
  residualNames := id
  injective := Function.injective_id
  instance_ := fun name => .var (sourceName name)
  caller := Subst.id signature
  reads := fun name => by simp [Subst.id, encode]
  resolved := by
    intro parameter present
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl <;> simp [sourceName]
  rangeResolved := by simp [sourceName]

theorem recognized_real_row_reads_one_private_variable :
    frame.caller.applyTerm frame.inputRequest = .var 0 ∧
      frame.caller.applyTerm frame.resultRequest = .var 0 :=
  ⟨frame.input_read, frame.result_read⟩

theorem computed_row_admits_one_actual_input :
    StableGroundGuardDischarge.check [] 1 [] frame.caller (.const (.number "7")) frame.inputRequest =
      some [entered frame.caller 0 (.const (.number "7"))] := by
  exact StableGroundGuardDischarge.input_guard_single_refinement [] 1 [] frame.caller
    (.const (.number "7")) frame.inputRequest 0 frame.input_read (by trivial) (by decide +kernel)

end Controls

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaRecognizedSourceBoundary
