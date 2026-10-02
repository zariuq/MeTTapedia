import Mettapedia.Languages.VibeITP.Spec.ProtocolInvariant
import Mettapedia.Languages.VibeITP.Presentation.SignatureExtensionDerivation

/-! Preservation of admitted theories through actual protocol allocation. -/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Spec.ProtocolAdmission

open Mettapedia.Languages.VibeITP.Presentation

theorem hosted_signature_extension {source : Theory} {allocated : Nat}
    (hosted : Hosted source allocated) (target : Sig) (targetAllocated : Nat)
    (extension : SigExt source.sig target)
    (fresh : ∀ identity, (target (.fresh identity)).isSome = true ↔ identity < targetAllocated)
    (fvars : FvarsBindNothing target) :
    Hosted { source with sig := target } targetAllocated := by
  constructor
  · exact builtinsFixed_sigExt extension hosted.builtin
  · exact fresh
  · exact fvars
  · intro statement member
    obtain ⟨formed, closed⟩ := hosted.axiomsWf statement member
    exact ⟨wellFormed_true_sigExt extension formed,
      (depth_sigExt extension statement (wellFormed_termShape source.sig statement formed)).trans closed⟩
  · intro definition member
    obtain ⟨signature, formed, hints, admitted⟩ := hosted.definitionsOk definition member
    have known := definitionAdmissible_parameters_known source.sig definition.fvars hints
      definition.value admitted
    have shape := wellFormed_termShape source.sig definition.value formed
    refine ⟨?_, wellFormed_true_sigExt extension formed, hints, ?_⟩
    · rw [definitionInfo_sigExt extension definition.fvars known]
      exact extension definition.symbol _ signature
    · rw [definitionAdmissible_sigExt extension definition.fvars hints definition.value known shape]
      exact admitted

theorem allocate_sig_extension (state : State) (info : SymInfo)
    (hosted : Hosted state.theory state.nextFresh) :
    SigExt state.sig (state.allocate info).2.sig := by
  intro symbol prior present
  cases symbol with
  | builtin builtin => simpa [State.sig, State.allocate, sigOf] using present
  | fresh identity =>
    have old : identity < state.nextFresh := (hosted.fresh identity).mp (by
      simpa [State.theory, State.sig] using congrArg Option.isSome present)
    simpa [State.sig, State.allocate, sigOf, setSlot, Nat.ne_of_lt old] using present

theorem allocate_fresh_range (state : State) (info : SymInfo)
    (hosted : Hosted state.theory state.nextFresh) (identity : Nat) :
    ((state.allocate info).2.sig (.fresh identity)).isSome = true ↔
      identity < (state.allocate info).2.nextFresh := by
  by_cases newest : identity = state.nextFresh
  · simp [State.sig, State.allocate, sigOf, setSlot, newest]
  · have previous := hosted.fresh identity
    simp only [State.theory, State.sig, sigOf] at previous
    simp only [State.allocate, State.sig, sigOf, setSlot, if_neg newest]
    rw [previous]
    omega

theorem allocate_fvar_binders (state : State) (info : SymInfo)
    (hosted : Hosted state.theory state.nextFresh)
    (newBinders : info.kind = .fvar → ∀ binder ∈ info.binders, binder = 0) :
    FvarsBindNothing (state.allocate info).2.sig := by
  intro symbol data present free binder member
  cases symbol with
  | builtin builtin =>
    have same : data = builtin.info := by
      simpa [State.sig, State.allocate, sigOf] using present.symm
    subst data
    cases free
  | fresh identity =>
    by_cases newest : identity = state.nextFresh
    · have same : data = info := by
        simpa [State.sig, State.allocate, sigOf, setSlot, newest] using present.symm
      subst data
      exact newBinders free binder member
    · have previous : state.theory.sig (.fresh identity) = some data := by
        simpa [State.theory, State.sig, State.allocate, sigOf, setSlot, newest] using present
      exact hosted.fvarBinders (.fresh identity) data previous free binder member

theorem allocate_hosted (state : State) (info : SymInfo)
    (hosted : Hosted state.theory state.nextFresh)
    (newBinders : info.kind = .fvar → ∀ binder ∈ info.binders, binder = 0) :
    Hosted (state.allocate info).2.theory (state.allocate info).2.nextFresh :=
  hosted_signature_extension hosted (state.allocate info).2.sig (state.allocate info).2.nextFresh
    (allocate_sig_extension state info hosted) (allocate_fresh_range state info hosted)
    (allocate_fvar_binders state info hosted newBinders)

theorem allocate_fvar_hosted (state : State) (arity : Nat)
    (hosted : Hosted state.theory state.nextFresh) :
    Hosted (state.allocate (SymInfo.fvarOf arity)).2.theory
      (state.allocate (SymInfo.fvarOf arity)).2.nextFresh := by
  apply allocate_hosted state _ hosted
  intro _ binder member
  simpa [SymInfo.fvarOf] using (List.eq_of_mem_replicate member)

theorem allocate_constant_hosted (state : State) (binders : List Nat)
    (hosted : Hosted state.theory state.nextFresh) :
    Hosted (state.allocate ⟨.constant, binders⟩).2.theory
      (state.allocate ⟨.constant, binders⟩).2.nextFresh := by
  apply allocate_hosted state _ hosted
  intro impossible
  cases impossible

theorem admit_axiom_hosted (state : State) (statement : Term)
    (hosted : Hosted state.theory state.nextFresh)
    (formed : WellFormed state.sig statement = true) (closed : depth state.sig statement = 0) :
    Hosted ({ state with axioms := state.axioms ++ [statement] } : State).theory state.nextFresh := by
  constructor
  · exact hosted.builtin
  · exact hosted.fresh
  · exact hosted.fvarBinders
  · intro term member
    rcases List.mem_append.mp member with previous | newest
    · exact hosted.axiomsWf term previous
    · have same : term = statement := by simpa using newest
      subst term
      exact ⟨formed, closed⟩
  · exact hosted.definitionsOk

theorem allocate_theory_extension (state : State) (info : SymInfo)
    (hosted : Hosted state.theory state.nextFresh) :
    TheoryExt state.theory (state.allocate info).2.theory :=
  ⟨allocate_sig_extension state info hosted, fun _ member => member, fun _ member => member⟩

theorem allocate_definition_hosted (state : State) (parameters : List SymId)
    (hints : List Nat) (value : Term) (hosted : Hosted state.theory state.nextFresh)
    (formed : WellFormed state.sig value = true)
    (admitted : definitionAdmissible state.sig parameters hints value = true) :
    let allocated := (state.allocate (definitionInfo state.sig parameters)).2
    let definition : Definition := ⟨.fresh state.nextFresh, parameters, value⟩
    Hosted ({ allocated with definitions := allocated.definitions ++ [definition] } : State).theory
      allocated.nextFresh := by
  dsimp only
  have prior := allocate_constant_hosted state
    (parameters.map fun parameter => symArity state.sig parameter) hosted
  have extension := allocate_sig_extension state (definitionInfo state.sig parameters) hosted
  have known := definitionAdmissible_parameters_known state.sig parameters hints value admitted
  have shape := wellFormed_termShape state.sig value formed
  constructor
  · exact prior.builtin
  · exact prior.fresh
  · exact prior.fvarBinders
  · exact prior.axiomsWf
  · intro definition member
    rcases List.mem_append.mp member with previous | newest
    · exact prior.definitionsOk definition previous
    · have same : definition = ⟨.fresh state.nextFresh, parameters, value⟩ := by
        simpa using newest
      subst definition
      refine ⟨?_, wellFormed_true_sigExt extension formed, hints, ?_⟩
      · change (state.allocate (definitionInfo state.sig parameters)).2.sig (.fresh state.nextFresh) =
          some (definitionInfo (state.allocate (definitionInfo state.sig parameters)).2.sig parameters)
        rw [definitionInfo_sigExt extension parameters known]
        simp [State.sig, State.allocate, sigOf, setSlot]
      · change definitionAdmissible (state.allocate (definitionInfo state.sig parameters)).2.sig
          parameters hints value = true
        rw [definitionAdmissible_sigExt extension parameters hints value known shape]
        exact admitted

end Mettapedia.Languages.VibeITP.Spec.ProtocolAdmission
