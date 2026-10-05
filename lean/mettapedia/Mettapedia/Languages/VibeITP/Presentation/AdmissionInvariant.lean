import Mettapedia.Languages.VibeITP.Presentation.AdmissionState

/-!
# Reached theories from static declaration admission

The invariant is derived from the actual initial builtin theory and every
admitted transition. Allocation and definition publication are transported to
the existing protocol operations. No caller-supplied theory invariant is
needed for a run starting at the initial state.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalAdmission

open ComputationalShift ComputationalProofs

theorem protocol_theory (state : AdmissionState) (fixed : BuiltinsFixed state.theory.sig) :
    state.protocol.theory = state.theory := by
  have signatures : state.protocol.sig = state.theory.sig := by
    funext symbol
    cases symbol with
    | builtin builtin => exact (fixed builtin).symm
    | fresh identity => rfl
  unfold Spec.State.theory AdmissionState.theory
  rw [signatures]
  rfl

theorem protocol_allocate (state : AdmissionState) (info : Spec.SymInfo) :
    (state.allocate info).protocol = (state.protocol.allocate info).2 := by
  have fresh : (fun identity => signatureOf ((.fresh state.nextFresh, info) :: state.table) (.fresh identity)) =
      Spec.setSlot (fun identity => signatureOf state.table (.fresh identity)) state.nextFresh (some info) := by
    funext identity
    simp [signatureOf, Spec.setSlot]
  simp only [AdmissionState.protocol, AdmissionState.allocate, Spec.State.allocate]
  rw [fresh]

theorem allocation_builtins (state : AdmissionState) (info : Spec.SymInfo)
    (fixed : BuiltinsFixed state.theory.sig) : BuiltinsFixed (state.allocate info).theory.sig := by
  intro builtin
  simpa [AdmissionState.theory, AdmissionState.allocate, theoryOf, signatureOf] using fixed builtin

theorem allocate_hosted (state : AdmissionState) (info : Spec.SymInfo)
    (hosted : Hosted state.theory state.nextFresh)
    (binders : info.kind = .fvar → ∀ binder ∈ info.binders, binder = 0) :
    Hosted (state.allocate info).theory (state.allocate info).nextFresh := by
  have previous : Hosted state.protocol.theory state.protocol.nextFresh := by
    rw [protocol_theory state hosted.builtin]
    exact hosted
  have next := Spec.ProtocolAdmission.allocate_hosted state.protocol info previous binders
  rw [← protocol_allocate] at next
  rw [protocol_theory _ (allocation_builtins state info hosted.builtin)] at next
  exact next

theorem addAxiom_hosted (state : AdmissionState) (statement : Spec.Term)
    (hosted : Hosted state.theory state.nextFresh)
    (formed : Spec.WellFormed state.theory.sig statement = true)
    (closed : Spec.depth state.theory.sig statement = 0) :
    Hosted (state.addAxiom statement).theory (state.addAxiom statement).nextFresh := by
  have previous : Hosted state.protocol.theory state.protocol.nextFresh := by
    rw [protocol_theory state hosted.builtin]
    exact hosted
  have signature : state.protocol.sig = state.theory.sig :=
    congrArg Spec.Theory.sig (protocol_theory state hosted.builtin)
  have next := Spec.ProtocolAdmission.admit_axiom_hosted state.protocol statement previous
    (by rw [signature]; exact formed) (by rw [signature]; exact closed)
  change Hosted ⟨state.protocol.sig, state.axioms ++ [statement], state.definitions⟩ state.nextFresh at next
  rw [signature] at next
  exact next

theorem define_hosted (state : AdmissionState) (parameters : List Spec.SymId) (hints : List Nat)
    (body : Spec.Term) (hosted : Hosted state.theory state.nextFresh)
    (formed : Spec.WellFormed state.theory.sig body = true)
    (admitted : Spec.definitionAdmissible state.theory.sig parameters hints body = true) :
    Hosted (state.define parameters body).theory (state.define parameters body).nextFresh := by
  have previous : Hosted state.protocol.theory state.protocol.nextFresh := by
    rw [protocol_theory state hosted.builtin]
    exact hosted
  have signature : state.protocol.sig = state.theory.sig :=
    congrArg Spec.Theory.sig (protocol_theory state hosted.builtin)
  have next := Spec.ProtocolAdmission.allocate_definition_hosted state.protocol parameters hints body previous
    (by rw [signature]; exact formed) (by rw [signature]; exact admitted)
  dsimp only at next
  rw [signature, ← protocol_allocate] at next
  change Hosted ⟨(state.allocate (Spec.definitionInfo state.theory.sig parameters)).protocol.sig,
    state.axioms, state.definitions ++ [⟨.fresh state.nextFresh, parameters, body⟩]⟩
    (state.nextFresh + 1) at next
  have allocated : (state.allocate (Spec.definitionInfo state.theory.sig parameters)).protocol.sig =
      (state.allocate (Spec.definitionInfo state.theory.sig parameters)).theory.sig :=
    congrArg Spec.Theory.sig (protocol_theory _
      (allocation_builtins state (Spec.definitionInfo state.theory.sig parameters) hosted.builtin))
  rw [allocated] at next
  exact next

theorem initialAdmission_hosted : Hosted initialAdmission.theory initialAdmission.nextFresh := by
  have initial := Spec.ProtocolInvariant.initial_hosted
  have theory : initialAdmission.theory = Spec.initialState.theory :=
    theoryOf_allocatedSnapshot initial
  rw [theory]
  exact initial

theorem Admits.hosted {before after : AdmissionState} {declaration : Declaration}
    (admitted : Admits before declaration after) (hosted : Hosted before.theory before.nextFresh) :
    Hosted after.theory after.nextFresh := by
  cases admitted with
  | fvar arity =>
      apply allocate_hosted before _ hosted
      intro _ binder member
      simpa [Spec.SymInfo.fvarOf] using List.eq_of_mem_replicate member
  | constant binders =>
      apply allocate_hosted before _ hosted
      intro impossible
      cases impossible
  | «axiom» _ formed closed => exact addAxiom_hosted _ _ hosted formed closed
  | definition formed admitted => exact define_hosted _ _ _ _ hosted formed admitted
  | enterProofs => exact hosted

theorem AdmissionRun.hosted {before after : AdmissionState} {declarations : List Declaration}
    (run : AdmissionRun before declarations after) (hosted : Hosted before.theory before.nextFresh) :
    Hosted after.theory after.nextFresh := by
  induction run with
  | nil => exact hosted
  | cons step _ ih => exact ih (step.hosted hosted)

theorem admitted_run_hosted {declarations : List Declaration} {after : AdmissionState}
    (run : admitRun initialAdmission declarations = some after) : Hosted after.theory after.nextFresh :=
  ((admitRun_eq_some_iff _ _ _).mp run).hosted initialAdmission_hosted

theorem allocation_fresh (state : AdmissionState) (info : Spec.SymInfo)
    (hosted : Hosted state.theory state.nextFresh) :
    state.theory.sig (.fresh state.nextFresh) = none ∧
      (state.allocate info).theory.sig (.fresh state.nextFresh) = some info := by
  have absent : (state.theory.sig (.fresh state.nextFresh)).isSome = false := by
    have range := hosted.fresh state.nextFresh
    cases value : state.theory.sig (.fresh state.nextFresh) <;> simp_all
  constructor
  · cases value : state.theory.sig (.fresh state.nextFresh) <;> simp_all
  · simp [AdmissionState.theory, AdmissionState.allocate, theoryOf, signatureOf]

theorem Admits.theory_extension {before after : AdmissionState} {declaration : Declaration}
    (admitted : Admits before declaration after) (hosted : Hosted before.theory before.nextFresh) :
    TheoryExt before.theory after.theory := by
  have allocation (state : AdmissionState) (info : Spec.SymInfo)
      (prior : Hosted state.theory state.nextFresh) : TheoryExt state.theory (state.allocate info).theory := by
    have previous : Hosted state.protocol.theory state.protocol.nextFresh := by
      rw [protocol_theory state prior.builtin]
      exact prior
    have extended := Spec.ProtocolAdmission.allocate_theory_extension state.protocol info previous
    rw [← protocol_allocate, protocol_theory state prior.builtin,
      protocol_theory _ (allocation_builtins state info prior.builtin)] at extended
    exact extended
  cases admitted with
  | fvar arity => exact allocation before _ hosted
  | constant binders => exact allocation before _ hosted
  | «axiom» => exact ⟨SigExt.refl _, fun _ member => List.mem_append_left _ member, fun _ member => member⟩
  | @definition parameters hints body _ _ =>
      have extended := allocation before (Spec.definitionInfo before.theory.sig parameters) hosted
      exact ⟨extended.sig, extended.axioms, fun _ member => List.mem_append_left _ member⟩
  | enterProofs => exact TheoryExt.refl _

theorem AdmissionRun.theory_extension {before after : AdmissionState} {declarations : List Declaration}
    (run : AdmissionRun before declarations after) (hosted : Hosted before.theory before.nextFresh) :
    TheoryExt before.theory after.theory := by
  induction run with
  | nil => exact TheoryExt.refl _
  | cons step tail ih => exact (step.theory_extension hosted).trans (ih (step.hosted hosted))

end Mettapedia.Languages.VibeITP.Presentation.ComputationalAdmission
