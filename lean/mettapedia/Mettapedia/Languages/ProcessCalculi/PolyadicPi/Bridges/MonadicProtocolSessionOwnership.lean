import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolCapabilities
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedActiveFrontier

/-!
# Administrative phases retain the publicly selected tuple

The source binary communication commits at the public rendezvous. Its three
remaining private communications retain that selected tuple and continuation;
their exact endpoints and three-to-zero communication potential are derived
from the actual unary rules. Private occurrence keys identify selected atoms
without identifying equal values or imposing a public partner ordering.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.Ownership

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.Capabilities
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedActiveFrontier

/-- This data is obtained from the selected public input and output. -/
structure Call (Γ : Ctx sig) where
  first : Name Γ
  second : Name Γ
  body : Proc (.nm :: .nm :: Γ)

def Call.rename {Γ Δ : Ctx sig} (call : Call Γ) (environment : Ren sig Γ Δ) : Call Δ where
  first := Mettapedia.OSLF.Binding.rename environment call.first
  second := Mettapedia.OSLF.Binding.rename environment call.second
  body := Mettapedia.OSLF.Binding.rename (liftRen environment [.nm, .nm]) call.body

inductive Phase where
  | callback
  | first
  | second
  deriving DecidableEq

def Phase.remaining : Phase → Nat
  | .callback => 3
  | .first => 2
  | .second => 1

def Phase.remainingAfter : Phase → Nat
  | .callback => 2
  | .first => 1
  | .second => 0

/-- A real private communication consumes one unit of the remaining
administrative work, independently of the source continuation's future work. -/
theorem Phase.account (phase : Phase) : phase.remaining = 1 + phase.remainingAfter := by
  cases phase <;> rfl

def readback {Γ : Ctx sig} (call : Call Γ) : Proc Γ :=
  openPair call.body call.first call.second

/-- The two private binders are callback, then session, then source names. -/
def contents {Γ : Ctx sig} (phase : Phase) (call : Call Γ) :
    Proc (.nm :: .nm :: Γ) :=
  match phase with
  | .callback => par
      (par (out1 (.var (.succ .zero)) (.var .zero))
        (weaken (sendFields call.first call.second)))
      (receiveFields call.body)
  | .first => par
      (par (out1 (.var .zero) (weaken (weaken call.first))) (receiveFields call.body))
      (out1 (.var (.succ .zero)) (weaken (weaken call.second)))
  | .second => par
      (out1 (.var (.succ .zero)) (weaken (weaken call.second)))
      (inp1 (.var (.succ .zero)) (secondBody call.first call.body))

/-- Actual raw reducts retain the ordering supplied by COMM. -/
def contractum {Γ : Ctx sig} (phase : Phase) (call : Call Γ) :
    Proc (.nm :: .nm :: Γ) :=
  match phase with
  | .callback => par
      (par (out1 (.var .zero) (weaken (weaken call.first)))
        (out1 (.var (.succ .zero)) (weaken (weaken call.second))))
      (receiveFields call.body)
  | .first => par
      (inp1 (.var (.succ .zero)) (secondBody call.first call.body))
      (out1 (.var (.succ .zero)) (weaken (weaken call.second)))
  | .second => weaken (weaken (readback call))

def nextContents {Γ : Ctx sig} (phase : Phase) (call : Call Γ) :
    Proc (.nm :: .nm :: Γ) :=
  match phase with
  | .callback => contents .first call
  | .first => contents .second call
  | .second => weaken (weaken (readback call))

private theorem nu_injective {Γ : Ctx sig} {first second : Proc (.nm :: Γ)}
    (same : nu first = nu second) : first = second :=
  (Args.cons.inj (eq_of_heq (Term.op.inj same).2)).1

/-- Every raw firing of a private phase has the supplied tuple's exact reduct;
the continuation is neither replaced nor obtained from another invocation. -/
theorem contents_step_iff {Γ : Ctx sig} (phase : Phase) (call : Call Γ)
    (endpoint : Proc (.nm :: .nm :: Γ)) :
    Step (contents phase call) endpoint ↔ endpoint = contractum phase call := by
  cases phase with
  | callback =>
      constructor
      · intro step
        have same := (callbackState_raw_endpoint_iff call.first call.second call.body
          (nu (nu endpoint))).1 (.nu (.nu step))
        exact nu_injective (nu_injective same)
      · rintro rfl
        have step := (callbackState_raw_endpoint_iff call.first call.second call.body
          (callbackContractum call.first call.second call.body)).2 rfl
        cases step with
        | nu outer => cases outer with
          | nu inner => exact inner
  | first =>
      constructor
      · intro step
        have same := (fieldsState_raw_endpoint_iff call.first call.second call.body
          (nu (nu endpoint))).1 (.nu (.nu step))
        exact nu_injective (nu_injective same)
      · rintro rfl
        have step := (fieldsState_raw_endpoint_iff call.first call.second call.body
          (firstFieldContractum call.first call.second call.body)).2 rfl
        cases step with
        | nu outer => cases outer with
          | nu inner => exact inner
  | second =>
      constructor
      · intro step
        have same := (secondState_endpoint_iff call.first call.second call.body
          (nu (nu endpoint))).1 (.nu (.nu step))
        exact nu_injective (nu_injective same)
      · rintro rfl
        have step := (secondState_endpoint_iff call.first call.second call.body
          (nu (nu (weaken (weaken (readback call)))))).2 rfl
        cases step with
        | nu outer => cases outer with
          | nu inner => exact inner

theorem contractum_next {Γ : Ctx sig} (phase : Phase) (call : Call Γ) :
    StructuralEq (contractum phase call) (nextContents phase call) := by
  cases phase with
  | callback =>
      exact .trans (.parAssoc _ _ _)
        (.trans (.par (.refl _) (.parComm _ _)) (.symm (.parAssoc _ _ _)))
  | first => exact .parComm _ _
  | second => exact .refl _

def placed {Γ : Ctx sig} (n : Nat) (owner : Fin n) (phase : Phase) (call : Call Γ) :
    Proc (World n Γ) := rename (placement n owner) (contents phase call)

theorem placed_extend {Γ : Ctx sig} (n : Nat) (owner : Fin n)
    (phase : Phase) (call : Call Γ) :
    placed (n + 1) owner.succ phase call =
      weaken (t := Srt.nm) (weaken (t := Srt.nm) (placed n owner phase call)) :=
  placement_term_extend n owner (contents phase call)

theorem callback_contents_natural {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (call : Call Γ) :
    rename (liftRen environment [.nm, .nm]) (contents .callback call) =
      contents .callback (call.rename environment) := by
  simp only [contents, Call.rename, rename_par, rename_out1]
  have sender : rename (liftRen environment [.nm, .nm])
      (weaken (sendFields call.first call.second)) =
      weaken (sendFields (rename environment call.first) (rename environment call.second)) := by
    rw [← liftRen_two environment Srt.nm Srt.nm,
      rename_weaken (S := sig) (fresh := Srt.nm) (liftRen environment [.nm]),
      sendFields_rename]
  rw [sender, receiveFields_rename]
  rfl

/-- An actual newly committed pair uses the new private positions; every
previous occurrence is weakened by `placed_extend`. No callback is allocated
outside the public input guard. -/
theorem fresh_public_commitment {Γ : Ctx sig} (n : Nat) (channel : Name Γ) (call : Call Γ) :
    StepModulo (invocation (rename (ambient n) channel)
      (rename (ambient n) call.first) (rename (ambient n) call.second)
      (rename (liftRen (ambient n) [.nm, .nm]) call.body))
      (nu (nu (placed (n + 1) ⟨0, Nat.succ_pos n⟩ .callback call))) := by
  have step := session_fires (rename (ambient n) channel)
    (rename (ambient n) call.first) (rename (ambient n) call.second)
    (rename (liftRen (ambient n) [.nm, .nm]) call.body)
  change StepModulo _ (nu (nu (contents .callback (call.rename (ambient n))))) at step
  have same : placed (n + 1) ⟨0, Nat.succ_pos n⟩ .callback call =
      contents .callback (call.rename (ambient n)) := by
    unfold placed
    rw [placement_new]
    exact callback_contents_natural (ambient n) call
  have closed := congrArg (fun body : Proc (.nm :: .nm :: World n Γ) => nu (nu body)) same
  exact closed.symm ▸ step

/-- Placement carries actual firing inversion, including its endpoint, into
any finite common private world. -/
theorem placed_step_iff {Γ : Ctx sig} (n : Nat) (owner : Fin n)
    (phase : Phase) (call : Call Γ) (endpoint : Proc (World n Γ)) :
    Step (placed n owner phase call) endpoint ↔
      endpoint = rename (placement n owner) (contractum phase call) := by
  constructor
  · intro step
    obtain ⟨canonical, fired, same⟩ := placement_actual_step n owner _ step
    rw [(contents_step_iff phase call canonical).1 fired] at same
    exact same.symm
  · rintro rfl
    exact ((contents_step_iff phase call _).2 rfl).rename (placement n owner)

/-- Actual endpoints relate to the next phase by existing static equations. -/
theorem placed_actual_endpoint {Γ : Ctx sig} (n : Nat) (owner : Fin n)
    (phase : Phase) (call : Call Γ) {endpoint : Proc (World n Γ)}
    (step : Step (placed n owner phase call) endpoint) :
    StructuralEq endpoint (rename (placement n owner) (nextContents phase call)) := by
  rw [(placed_step_iff n owner phase call endpoint).1 step]
  exact (contractum_next phase call).rename (placement n owner)

/-- Neither transport key survives in the released source continuation. -/
theorem placed_release {Γ : Ctx sig} (n : Nat) (owner : Fin n) (call : Call Γ) :
    rename (placement n owner) (nextContents .second call) =
      rename (ambient n) (readback call) := by
  simp only [nextContents, weaken, rename_comp]
  rfl

theorem released_has_no_private {Γ : Ctx sig} (n : Nat) (owner other : Fin n)
    (port : Port) (call : Call Γ) :
    countVar (key n other port)
      (rename (placement n owner) (nextContents .second call)) = 0 := by
  rw [placed_release]
  exact ambient_has_no_private n other port (readback call)

/-- The genuine source COMM commits at the first public rendezvous. The
remaining private phases are associated with its already opened continuation. -/
theorem public_commitment {Γ : Ctx sig} (channel : Name Γ) (call : Call Γ)
    {endpoint : Proc Γ}
    (step : Step (rendezvousState channel call.first call.second call.body) endpoint) :
    Step (par (out2 channel call.first call.second) (inp2 channel call.body))
      (readback call) ∧
    StructuralEq endpoint (nu (nu (contents .callback call))) :=
  ⟨.comm2 _ _ _ _, rendezvous_actual_endpoint _ _ _ _ step⟩

inductive OutputKind where
  | reply
  | first
  | second
  deriving DecidableEq

inductive InputKind where
  | callback
  | first
  | second
  deriving DecidableEq

def OutputKind.port : OutputKind → Port
  | .reply => .session
  | .first => .callback
  | .second => .session

def InputKind.port : InputKind → Port
  | .callback => .session
  | .first => .callback
  | .second => .session

def OutputKind.live : Phase → OutputKind → Prop
  | .callback, kind => kind = .reply
  | .first, kind => kind = .first ∨ kind = .second
  | .second, kind => kind = .second

def InputKind.live : Phase → InputKind → Prop
  | .callback, kind => kind = .callback ∨ kind = .first
  | .first, kind => kind = .first
  | .second, kind => kind = .second

def Phase.selectedOutput : Phase → OutputKind
  | .callback => .reply
  | .first => .first
  | .second => .second

def Phase.selectedInput : Phase → InputKind
  | .callback => .callback
  | .first => .first
  | .second => .second

private def canonicalChannel {Γ : Ctx sig} : Port → Name (.nm :: .nm :: Γ)
  | .callback => .var .zero
  | .session => .var (.succ .zero)

def outputTemplate {Γ : Ctx sig} (kind : OutputKind) (call : Call Γ) :
    Proc (.nm :: .nm :: Γ) :=
  match kind with
  | .reply => out1 (.var (.succ .zero)) (.var .zero)
  | .first => out1 (.var .zero) (weaken (weaken call.first))
  | .second => out1 (.var (.succ .zero)) (weaken (weaken call.second))

def inputBody {Γ : Ctx sig} (kind : InputKind) (call : Call Γ) :
    Proc (.nm :: .nm :: .nm :: Γ) :=
  match kind with
  | .callback =>
      rename (liftRen (fun (sort : Srt) (name : Var (.nm :: Γ) sort) => .succ name) [.nm])
        (par (out1 (.var .zero) (weaken (weaken call.first)))
          (out1 (.var (.succ .zero)) (weaken (weaken call.second))))
  | .first => inp1 (.var (.succ (.succ .zero))) (rename receiveBodyRen call.body)
  | .second => secondBody call.first call.body

def inputTemplate {Γ : Ctx sig} (kind : InputKind) (call : Call Γ) :
    Proc (.nm :: .nm :: Γ) := inp1 (canonicalChannel kind.port) (inputBody kind call)

def placedOutput {Γ : Ctx sig} (n : Nat) (owner : Fin n)
    (kind : OutputKind) (call : Call Γ) : Proc (World n Γ) :=
  rename (placement n owner) (outputTemplate kind call)

def placedInput {Γ : Ctx sig} (n : Nat) (owner : Fin n)
    (kind : InputKind) (call : Call Γ) : Proc (World n Γ) :=
  rename (placement n owner) (inputTemplate kind call)

def placedDatum {Γ : Ctx sig} (n : Nat) (owner : Fin n)
    (kind : OutputKind) (call : Call Γ) : Name (World n Γ) :=
  match kind with
  | .reply => keyName n owner .callback
  | .first => rename (ambient n) call.first
  | .second => rename (ambient n) call.second

theorem output_header {Γ : Ctx sig} (n : Nat) (owner : Fin n)
    (kind : OutputKind) (call : Call Γ) :
    placedOutput n owner kind call = out1 (keyName n owner kind.port)
      (placedDatum n owner kind call) := by
  cases kind <;>
    simp only [placedOutput, outputTemplate, rename_out1, placedDatum, weaken, rename_comp]
  all_goals rfl

theorem input_header {Γ : Ctx sig} (n : Nat) (owner : Fin n)
    (kind : InputKind) (call : Call Γ) :
    placedInput n owner kind call = inp1 (keyName n owner kind.port)
      (rename (liftRen (placement n owner) [.nm]) (inputBody kind call)) := by
  cases kind <;> rfl

/-- A registry assigns one currently live phase to each committed occurrence.
Its private name positions are computed rather than supplied with an
injectivity assumption. -/
structure Session (Γ : Ctx sig) where
  call : Call Γ
  phase : Phase

/-- Any actual private atom firing in a finite committed registry chooses
one occurrence and the uniquely enabled pair at its present phase. Equal
values, shared public channels and another session's phase cannot mix fields. -/
theorem private_selection {Γ : Ctx sig} {n : Nat}
    (registry : Fin n → Session Γ) (sender receiver : Fin n)
    (output : OutputKind) (input : InputKind)
    (outputLive : output.live (registry sender).phase)
    (inputLive : input.live (registry receiver).phase)
    {endpoint : Proc (World n Γ)}
    (step : Step (par
      (placedOutput n sender output (registry sender).call)
      (placedInput n receiver input (registry receiver).call)) endpoint) :
    sender = receiver ∧ output = (registry sender).phase.selectedOutput ∧
      input = (registry sender).phase.selectedInput := by
  rw [output_header, input_header] at step
  obtain ⟨sameOwner, samePort, _⟩ :=
    (private_communication_iff n sender receiver output.port input.port _ _ endpoint).1 step
  subst receiver
  refine ⟨rfl, ?_⟩
  cases phase : (registry sender).phase <;>
    cases output <;> cases input <;>
    simp_all [OutputKind.live, InputKind.live, OutputKind.port, InputKind.port,
      Phase.selectedOutput, Phase.selectedInput]

def selectedPair {Γ : Ctx sig} (phase : Phase) (call : Call Γ) :
    Proc (.nm :: .nm :: Γ) :=
  par (outputTemplate phase.selectedOutput call) (inputTemplate phase.selectedInput call)

def selectedReduct {Γ : Ctx sig} (phase : Phase) (call : Call Γ) :
    Proc (.nm :: .nm :: Γ) :=
  match phase with
  | .callback => par (outputTemplate .first call) (outputTemplate .second call)
  | .first => inputTemplate .second call
  | .second => weaken (weaken (readback call))

def untouched {Γ : Ctx sig} (phase : Phase) (call : Call Γ) :
    Proc (.nm :: .nm :: Γ) :=
  match phase with
  | .callback => inputTemplate .first call
  | .first => outputTemplate .second call
  | .second => nil

theorem contents_selected {Γ : Ctx sig} (phase : Phase) (call : Call Γ) :
    StructuralEq (contents phase call) (par (selectedPair phase call) (untouched phase call)) := by
  cases phase with
  | callback => exact .refl _
  | first => exact .refl _
  | second => exact .symm (.parUnit _)

/-- The remainder of this occurrence is retained exactly, including the
guarded receiver before its first field and the pending second output. -/
theorem selected_remainder {Γ : Ctx sig} (phase : Phase) (call : Call Γ) :
    StructuralEq (par (selectedReduct phase call) (untouched phase call))
      (nextContents phase call) := by
  cases phase with
  | callback => exact contractum_next .callback call
  | first => exact contractum_next .first call
  | second => exact .parUnit _

/-- The selected atoms open the actual supplied handler, in the source's
original field order, for every continuation. -/
theorem selected_step_iff {Γ : Ctx sig} (phase : Phase) (call : Call Γ)
    (endpoint : Proc (.nm :: .nm :: Γ)) :
    Step (selectedPair phase call) endpoint ↔ endpoint = selectedReduct phase call := by
  cases phase with
  | callback =>
      rw [show selectedPair .callback call = par
        (out1 (.var (.succ .zero)) (.var .zero))
        (inp1 (.var (.succ .zero)) (inputBody .callback call)) from rfl,
        unary_communication_iff, inputBody, sender_callback_endpoint]
      rfl
  | first =>
      rw [show selectedPair .first call = par
        (out1 (.var .zero) (weaken (weaken call.first)))
        (inp1 (.var .zero) (inputBody .first call)) from rfl,
        unary_communication_iff, inputBody, first_field_endpoint]
      rfl
  | second =>
      rw [show selectedPair .second call = par
        (out1 (.var (.succ .zero)) (weaken (weaken call.second)))
        (inp1 (.var (.succ .zero)) (inputBody .second call)) from rfl,
        unary_communication_iff, inputBody, second_field_endpoint]
      rfl

/-- The selected output, input and actual endpoint all come from the same
committed tuple. The conclusion concerns the supplied firing, not a separately
constructed successful schedule. -/
theorem private_selected_endpoint {Γ : Ctx sig} {n : Nat}
    (registry : Fin n → Session Γ) (sender receiver : Fin n)
    (output : OutputKind) (input : InputKind)
    (outputLive : output.live (registry sender).phase)
    (inputLive : input.live (registry receiver).phase)
    {endpoint : Proc (World n Γ)}
    (step : Step (par
      (placedOutput n sender output (registry sender).call)
      (placedInput n receiver input (registry receiver).call)) endpoint) :
    sender = receiver ∧
      endpoint = rename (placement n sender)
        (selectedReduct (registry sender).phase (registry sender).call) := by
  obtain ⟨rfl, outputSelected, inputSelected⟩ :=
    private_selection registry sender receiver output input outputLive inputLive step
  rw [outputSelected, inputSelected] at step
  obtain ⟨canonical, fired, exactEndpoint⟩ := placement_actual_step n sender
    (selectedPair (registry sender).phase (registry sender).call) step
  rw [(selected_step_iff (registry sender).phase (registry sender).call canonical).1 fired]
    at exactEndpoint
  exact ⟨rfl, exactEndpoint.symm⟩

inductive AtomKind where
  | output (kind : OutputKind)
  | input (kind : InputKind)
  deriving DecidableEq

/-- The list records actual active occurrences, including their multiplicity.
The second receiver stays guarded until the first receiver has fired. -/
def atoms : Phase → List AtomKind
  | .callback => [.output .reply, .input .callback, .input .first]
  | .first => [.output .first, .input .first, .output .second]
  | .second => [.output .second, .input .second]

def atomTemplate {Γ : Ctx sig} (kind : AtomKind) (call : Call Γ) :
    Proc (.nm :: .nm :: Γ) :=
  match kind with
  | .output kind => outputTemplate kind call
  | .input kind => inputTemplate kind call

theorem output_atom_live (phase : Phase) (kind : OutputKind)
    (present : AtomKind.output kind ∈ atoms phase) : kind.live phase := by
  cases phase <;> cases kind <;> simp_all [atoms, OutputKind.live]

theorem input_atom_live (phase : Phase) (kind : InputKind)
    (present : AtomKind.input kind ∈ atoms phase) : kind.live phase := by
  cases phase <;> cases kind <;> simp_all [atoms, InputKind.live]

/-- The generated atom list is an actual structural representative of each
committed phase. There is no new rewrite authority in this list. -/
theorem contents_atoms {Γ : Ctx sig} (phase : Phase) (call : Call Γ) :
    StructuralEq (contents phase call)
      (parallel ((atoms phase).map (fun kind => atomTemplate kind call))) := by
  cases phase with
  | callback =>
      exact .trans (.parAssoc _ _ _)
        (.par (.refl _) (.par (.refl _) (.symm (.parUnit _))))
  | first =>
      exact .trans (.parAssoc _ _ _)
        (.par (.refl _) (.par (.refl _) (.symm (.parUnit _))))
  | second => exact .par (.refl _) (.symm (.parUnit _))

/-- Occurrence selection from the actual generated frontier discharges the
phase liveness obligations used by `private_selected_endpoint`. -/
theorem registry_atom_endpoint {Γ : Ctx sig} {n : Nat}
    (registry : Fin n → Session Γ) (sender receiver : Fin n)
    (output : OutputKind) (input : InputKind)
    (outputPresent : AtomKind.output output ∈ atoms (registry sender).phase)
    (inputPresent : AtomKind.input input ∈ atoms (registry receiver).phase)
    {endpoint : Proc (World n Γ)}
    (step : Step (par
      (placedOutput n sender output (registry sender).call)
      (placedInput n receiver input (registry receiver).call)) endpoint) :
    sender = receiver ∧
      endpoint = rename (placement n sender)
        (selectedReduct (registry sender).phase (registry sender).call) :=
  private_selected_endpoint registry sender receiver output input
    (output_atom_live _ output outputPresent) (input_atom_live _ input inputPresent) step

/-- The supplied selected endpoint and this occurrence's untouched atoms
reassemble into the next actual phase. An arbitrary parallel frame is retained;
this does not assert that every additional frame firing is administrative. -/
theorem selected_frame_endpoint {Γ : Ctx sig} (n : Nat) (owner : Fin n)
    (phase : Phase) (call : Call Γ) (frame : Proc (World n Γ))
    {endpoint : Proc (World n Γ)}
    (step : Step (par
      (placedOutput n owner phase.selectedOutput call)
      (placedInput n owner phase.selectedInput call)) endpoint) :
    StructuralEq
      (par (par endpoint (rename (placement n owner) (untouched phase call))) frame)
      (par (rename (placement n owner) (nextContents phase call)) frame) := by
  obtain ⟨canonical, fired, supplied⟩ :=
    placement_actual_step n owner (selectedPair phase call) step
  rw [(selected_step_iff phase call canonical).1 fired] at supplied
  rw [← supplied]
  exact .par ((selected_remainder phase call).rename (placement n owner)) (.refl frame)

/-- The one-step administrative update uses a genuine COMM under the
retained frame, with only the existing before/after structural equations. -/
theorem phase_step_with_frame {Γ : Ctx sig} (n : Nat) (owner : Fin n)
    (phase : Phase) (call : Call Γ) (frame : Proc (World n Γ)) :
    StepModulo (par (placed n owner phase call) frame)
      (par (rename (placement n owner) (nextContents phase call)) frame) := by
  have selected := ((selected_step_iff phase call _).2 rfl).rename (placement n owner)
  exact ⟨par (par (rename (placement n owner) (selectedPair phase call))
      (rename (placement n owner) (untouched phase call))) frame,
    par (par (rename (placement n owner) (selectedReduct phase call))
      (rename (placement n owner) (untouched phase call))) frame,
    .par ((contents_selected phase call).rename (placement n owner)) (.refl frame),
    .parL frame (.parL _ selected),
    .par ((selected_remainder phase call).rename (placement n owner)) (.refl frame)⟩

/-- Source-authored binary bodies use the existing lowering/binder law at
release, so the retained continuation really is the source's COMM reduct. -/
theorem lowered_release {Γ : Ctx sig} (n : Nat) (owner : Fin n)
    (first second : Name Γ) (body : Proc (.nm :: .nm :: Γ)) :
    rename (placement n owner)
      (nextContents .second ⟨first, second, lower body⟩) =
        rename (ambient n) (lower (openPair body first second)) := by
  rw [placed_release]
  exact congrArg (rename (ambient n)) (lower_openPair body first second).symm

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.Ownership
