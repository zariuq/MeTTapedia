import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveSubjectBinaryFiring

/-!
# Recovering the physical fields of a unique binary offer

When an opened boundary has one binary output and an output-free frame,
every selected binary communication through arbitrary static equations uses
that output's actual subject and ordered fields. Fresh scopes are read by a
separate key, so observing an old ambient name recovers that name exactly.
Together with linearity on the subject this determines the supplied endpoint.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveBinaryBoundary

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open ActiveMarking ActiveHeaderInvariant ScopedActiveFrontier ScopedCommunicationInversion

universe u v

/-- Every retained header observation comes from an active constructor in
the supplied original syntax. -/
theorem observed_visible {Label : Type u} {Key : Type v} (binderKey : Label → Key)
    {Γ : Ctx sig} {marked : ActiveMarking.Tree Label} {process : Proc Γ}
    (fits : Fits marked process) (environment : ActiveMarkedNames.Environment Key Γ)
    (observation : ActiveMarkedNames.Observation Label Key)
    (member : observation ∈ ActiveMarkedNames.observe binderKey marked process environment) :
    visible observation.header process = true := by
  induction fits with
  | var => simp [ActiveMarkedNames.observe] at member
  | nil => simp [ActiveMarkedNames.observe, nil] at member
  | par first second firstIH secondIH =>
      simp only [ActiveMarkedNames.observe, par, Set.mem_union] at member
      simp only [par, visible]
      rcases member with member | member
      · rw [firstIH environment member, Bool.true_or]
      · rw [secondIH environment member, Bool.or_true]
  | inp1 origin channel =>
      simp only [inp1, ActiveMarkedNames.observe, Set.mem_singleton_iff] at member
      rw [member]
      simp [inp1, visible]
  | inp2 origin channel =>
      simp only [inp2, ActiveMarkedNames.observe, Set.mem_singleton_iff] at member
      rw [member]
      simp [inp2, visible]
  | out1 origin channel datum =>
      simp only [out1, ActiveMarkedNames.observe, Set.mem_singleton_iff] at member
      rw [member]
      simp [out1, visible]
  | out2 origin channel first second =>
      simp only [out2, ActiveMarkedNames.observe, Set.mem_singleton_iff] at member
      rw [member]
      simp [out2, visible]
  | nu origin _ ih =>
      simp only [nu, ActiveMarkedNames.observe] at member
      simpa only [nu, visible] using ih (ActiveMarkedNames.extend (binderKey origin) environment) member
  | rep _ ih =>
      simp only [rep, ActiveMarkedNames.observe] at member
      simpa only [rep, visible] using ih environment member

theorem constant_scope_environment {Label : Type u} {Ω : Ctx sig} (fresh : Var Ω Srt.nm) :
    ∀ {Γ Δ : Ctx sig} {scope : Scope Γ Δ} (binders : ScopeMarks Label scope)
      (environment : Ren sig Γ Ω),
      ActiveMarkedNames.scopeEnvironment (fun _ : Label => fresh) binders (environment Srt.nm) =
        (ActiveSubjectFiring.scopeEnvironment fresh scope environment) Srt.nm
  | _, _, _, .nil, _ => rfl
  | _, _, _, .bind origin rest, environment => by
      change ActiveMarkedNames.scopeEnvironment (fun _ : Label => fresh) rest
        (ActiveMarkedNames.extend fresh (environment Srt.nm)) =
          (ActiveSubjectFiring.scopeEnvironment fresh _ (prependRen fresh environment)) Srt.nm
      have named : ActiveMarkedNames.extend fresh (environment Srt.nm) =
          prependRen fresh environment Srt.nm := by
        funext name
        cases name <;> rfl
      rw [named]
      exact constant_scope_environment fresh rest (prependRen fresh environment)

/-- An observed active prefix on the selected actual subject contributes
to the physical offer count. Suspended bodies contribute no offers. -/
theorem observed_positive {Label : Type u} {Ω : Ctx sig} (fresh subject : Var Ω Srt.nm)
    {Γ : Ctx sig} {marked : ActiveMarking.Tree Label} {process : Proc Γ}
    (fits : Fits marked process) (environment : Ren sig Γ Ω)
    (observation : ActiveMarkedNames.Observation Label (Var Ω Srt.nm))
    (member : observation ∈ ActiveMarkedNames.observe (fun _ : Label => fresh) marked process (environment Srt.nm))
    (same : observation.channel = subject) :
    0 < ActiveSubjectResidual.count fresh subject environment process := by
  induction fits with
  | var => simp [ActiveMarkedNames.observe] at member
  | nil => simp [ActiveMarkedNames.observe, nil] at member
  | par first second firstIH secondIH =>
      simp only [ActiveMarkedNames.observe, par, Set.mem_union] at member
      simp only [par, ActiveSubjectResidual.count]
      rcases member with member | member
      · have positive := firstIH environment member
        omega
      · have positive := secondIH environment member
        omega
  | inp1 origin channel =>
      simp only [inp1, ActiveMarkedNames.observe, Set.mem_singleton_iff] at member
      rw [member] at same
      change ActiveMarkedNames.nameKey (environment Srt.nm) channel = subject at same
      simp only [inp1, ActiveSubjectResidual.count, ActiveSubjectResidual.onSubject, same, decide_true, ite_true]
      omega
  | inp2 origin channel =>
      simp only [inp2, ActiveMarkedNames.observe, Set.mem_singleton_iff] at member
      rw [member] at same
      change ActiveMarkedNames.nameKey (environment Srt.nm) channel = subject at same
      simp only [inp2, ActiveSubjectResidual.count, ActiveSubjectResidual.onSubject, same, decide_true, ite_true]
      omega
  | out1 origin channel datum =>
      simp only [out1, ActiveMarkedNames.observe, Set.mem_singleton_iff] at member
      rw [member] at same
      change ActiveMarkedNames.nameKey (environment Srt.nm) channel = subject at same
      simp only [out1, ActiveSubjectResidual.count, ActiveSubjectResidual.onSubject, same, decide_true, ite_true]
      omega
  | out2 origin channel first second =>
      simp only [out2, ActiveMarkedNames.observe, Set.mem_singleton_iff] at member
      rw [member] at same
      change ActiveMarkedNames.nameKey (environment Srt.nm) channel = subject at same
      simp only [out2, ActiveSubjectResidual.count, ActiveSubjectResidual.onSubject, same, decide_true, ite_true]
      omega
  | nu origin _ ih =>
      simp only [nu, ActiveMarkedNames.observe] at member
      have named : ActiveMarkedNames.extend fresh (environment Srt.nm) =
          prependRen fresh environment Srt.nm := by
        funext name
        cases name <;> rfl
      rw [named] at member
      simpa only [nu, ActiveSubjectResidual.count] using ih (prependRen fresh environment) member
  | rep _ ih =>
      simp only [rep, ActiveMarkedNames.observe] at member
      simpa only [rep, ActiveSubjectResidual.count] using ih environment member

/-- A unique binary input identifies the subject even when the frame has
other binary calls. Subject exclusion then identifies the exact selected
sender and recovers its original ordered ambient fields. -/
theorem selected_fields_linear {Γ : Ctx sig} (channel first second : Var Γ Srt.nm)
    (guard : Proc (Srt.nm :: Srt.nm :: Γ)) (frame : Proc Γ)
    (guardMarks frameMarks : ActiveMarking.Tree Unit)
    (guardFits : Fits guardMarks guard) (frameFits : Fits frameMarks frame)
    (noInput : visible .input2 frame = false)
    (quiet : ActiveSubjectResidual.count (.zero : Var (Srt.nm :: Γ) Srt.nm) (.succ channel)
      (fun _ name => .succ name) frame = 0) {target : Proc Γ}
    (exposure : Exposure
      (par (out2 (.var channel) (.var first) (.var second)) (par (inp2 (.var channel) guard) frame)) target)
    (binary : inputHeader exposure.selected = .input2) :
    ActiveSubjectBinaryFiring.SelectedBinary (.zero : Var (Srt.nm :: Γ) Srt.nm) (.succ channel)
      (fun _ name => .succ name) (.var first) (.var second) exposure := by
  let marked : ActiveMarking.Tree Unit := .par (.out2 ()) (.par (.inp2 () guardMarks) frameMarks)
  have fits : Fits marked
      (par (out2 (.var channel) (.var first) (.var second)) (par (inp2 (.var channel) guard) frame)) :=
    .par (.out2 () _ _ _) (.par (.inp2 () _ guardFits) frameFits)
  obtain ⟨traced⟩ := tracedExposure_exists () fits exposure
  have input := ActiveMarkedNames.traced_input_observed
    (fun _ : Unit => (.zero : Var (Srt.nm :: Γ) Srt.nm)) traced (fun name => .succ name)
  have output := ActiveMarkedNames.traced_output_observed
    (fun _ : Unit => (.zero : Var (Srt.nm :: Γ) Srt.nm)) traced (fun name => .succ name)
  rcases exposure with ⟨world, scope, redex, reduct, selected, rest, before, after⟩
  rcases traced with ⟨binders, redexMarks, frameMarks', continuation, restFits, fitted, transport, originalInput, originalOutput⟩
  cases selected with
  | unary => cases binary
  | binary actualChannel actualFirst actualSecond body =>
      cases continuation with
      | binary _ _ _ _ inputOrigin outputOrigin continuation continuationFits =>
          simp only [marked, par, out2, inp2, ActiveMarkedNames.observe, Set.mem_union, Set.mem_singleton_iff,
            ActiveMarkedNames.inputObservation] at input
          have subject : ActiveMarkedNames.nameKey
              (ActiveMarkedNames.scopeEnvironment (fun _ : Unit => (.zero : Var (Srt.nm :: Γ) Srt.nm))
                binders (fun name => .succ name)) actualChannel = .succ channel := by
            rcases input with output | input | framed
            · have headers := congrArg ActiveMarkedNames.Observation.header output
              cases headers
            · exact congrArg ActiveMarkedNames.Observation.channel input
            · have existsInput := observed_visible (fun _ : Unit => (.zero : Var (Srt.nm :: Γ) Srt.nm))
                frameFits (fun name => .succ name) _ framed
              rw [noInput] at existsInput
              cases existsInput
          simp only [marked, par, out2, inp2, ActiveMarkedNames.observe, Set.mem_union, Set.mem_singleton_iff,
            ActiveMarkedNames.outputObservation] at output
          rcases output with original | input | framed
          · have fields := congrArg ActiveMarkedNames.Observation.fields original
            simp only [List.cons.injEq, and_true] at fields
            have named := constant_scope_environment (.zero : Var (Srt.nm :: Γ) Srt.nm)
              binders (fun _ name => .succ name : Ren sig Γ (Srt.nm :: Γ))
            rw [named] at fields subject
            have firstBack := ActiveSubjectFiring.scope_names_back
              (.zero : Var (Srt.nm :: Γ) Srt.nm) (.succ first) (by intro impossible; cases impossible)
              scope (fun _ name => .succ name) first
              (fun name equal => Var.succ.inj equal) actualFirst fields.1
            have secondBack := ActiveSubjectFiring.scope_names_back
              (.zero : Var (Srt.nm :: Γ) Srt.nm) (.succ second) (by intro impossible; cases impossible)
              scope (fun _ name => .succ name) second
              (fun name equal => Var.succ.inj equal) actualSecond fields.2
            simp only [ActiveSubjectBinaryFiring.SelectedBinary, ActiveSubjectBinaryFiring.BinaryChoice]
            exact ⟨by simp only [ActiveSubjectResidual.onSubject, subject, decide_true], firstBack, secondBack⟩
          · have headers := congrArg ActiveMarkedNames.Observation.header input
            cases headers
          · have positive := observed_positive (.zero : Var (Srt.nm :: Γ) Srt.nm) (.succ channel)
              frameFits (fun _ name => .succ name) _ framed subject
            rw [quiet] at positive
            omega

/-- Static exposure of the unique binary sender recovers its actual two
ambient fields. The frame may have arbitrary unary behavior and persistence. -/
theorem selected_fields {Γ : Ctx sig} (channel first second : Var Γ Srt.nm)
    (guard : Proc (Srt.nm :: Srt.nm :: Γ)) (frame : Proc Γ)
    (guardMarks frameMarks : ActiveMarking.Tree Unit)
    (guardFits : Fits guardMarks guard) (frameFits : Fits frameMarks frame)
    (noOutput : visible .output2 frame = false) {target : Proc Γ}
    (exposure : Exposure
      (par (out2 (.var channel) (.var first) (.var second)) (par (inp2 (.var channel) guard) frame)) target)
    (binary : inputHeader exposure.selected = .input2) :
    ActiveSubjectBinaryFiring.SelectedBinary (.zero : Var (Srt.nm :: Γ) Srt.nm) (.succ channel)
      (fun _ name => .succ name) (.var first) (.var second) exposure := by
  let marked : ActiveMarking.Tree Unit := .par (.out2 ()) (.par (.inp2 () guardMarks) frameMarks)
  have fits : Fits marked
      (par (out2 (.var channel) (.var first) (.var second)) (par (inp2 (.var channel) guard) frame)) :=
    .par (.out2 () _ _ _) (.par (.inp2 () _ guardFits) frameFits)
  obtain ⟨traced⟩ := tracedExposure_exists () fits exposure
  have output := ActiveMarkedNames.traced_output_observed (fun _ : Unit => (.zero : Var (Srt.nm :: Γ) Srt.nm))
    traced (fun name => .succ name)
  rcases exposure with ⟨world, scope, redex, reduct, selected, rest, before, after⟩
  rcases traced with ⟨binders, redexMarks, frameMarks', continuation, restFits, fitted, transport, originalInput, originalOutput⟩
  cases selected with
  | unary => cases binary
  | binary actualChannel actualFirst actualSecond body =>
      cases continuation with
      | binary _ _ _ _ inputOrigin outputOrigin continuation continuationFits =>
          simp only [marked, par, out2, inp2, ActiveMarkedNames.observe, Set.mem_union, Set.mem_singleton_iff,
            ActiveMarkedNames.outputObservation] at output
          rcases output with original | input | framed
          · have fields := congrArg ActiveMarkedNames.Observation.fields original
            have subject := congrArg ActiveMarkedNames.Observation.channel original
            simp only [List.cons.injEq, and_true] at fields
            change ActiveMarkedNames.nameKey
              (ActiveMarkedNames.scopeEnvironment (fun _ : Unit => (.zero : Var (Srt.nm :: Γ) Srt.nm))
                binders (fun name => .succ name)) actualChannel = .succ channel at subject
            have named := constant_scope_environment (.zero : Var (Srt.nm :: Γ) Srt.nm)
              binders (fun _ name => .succ name : Ren sig Γ (Srt.nm :: Γ))
            rw [named] at fields subject
            have firstBack := ActiveSubjectFiring.scope_names_back
              (.zero : Var (Srt.nm :: Γ) Srt.nm) (.succ first) (by intro impossible; cases impossible)
              scope (fun _ name => .succ name) first
              (fun name equal => Var.succ.inj equal) actualFirst fields.1
            have secondBack := ActiveSubjectFiring.scope_names_back
              (.zero : Var (Srt.nm :: Γ) Srt.nm) (.succ second) (by intro impossible; cases impossible)
              scope (fun _ name => .succ name) second
              (fun name equal => Var.succ.inj equal) actualSecond fields.2
            simp only [ActiveSubjectBinaryFiring.SelectedBinary, ActiveSubjectBinaryFiring.BinaryChoice]
            exact ⟨by simp only [ActiveSubjectResidual.onSubject, subject, decide_true], firstBack, secondBack⟩
          · have headers := congrArg ActiveMarkedNames.Observation.header input
            cases headers
          · have existsOutput := observed_visible (fun _ : Unit => (.zero : Var (Srt.nm :: Γ) Srt.nm))
              frameFits (fun name => .succ name) _ framed
            rw [noOutput] at existsOutput
            cases existsOutput

private theorem pair_endpoint_selected {Γ : Ctx sig} (channel first second : Var Γ Srt.nm)
    (guard : Proc (Srt.nm :: Srt.nm :: Γ)) (frame : Proc Γ)
    (quiet : ActiveSubjectResidual.count (.zero : Var (Srt.nm :: Γ) Srt.nm) (.succ channel)
      (fun _ name => .succ name) frame = 0) {target : Proc Γ}
    (exposure : Exposure
      (par (out2 (.var channel) (.var first) (.var second)) (par (inp2 (.var channel) guard) frame)) target)
    (received : ActiveSubjectBinaryFiring.SelectedBinary (.zero : Var (Srt.nm :: Γ) Srt.nm) (.succ channel)
      (fun _ name => .succ name) (.var first) (.var second) exposure) :
    StructuralEq (par (openPair guard (.var first) (.var second)) frame) target := by
  have safeFrame := ActiveSubjectResidual.repFree_of_count_zero
    (.zero : Var (Srt.nm :: Γ) Srt.nm) (.succ channel) (fun _ name => .succ name) frame quiet
  have safe : ActiveSubjectResidual.repFree (.zero : Var (Srt.nm :: Γ) Srt.nm) (.succ channel)
      (fun _ name => .succ name)
      (par (out2 (.var channel) (.var first) (.var second)) (par (inp2 (.var channel) guard) frame)) := by
    simpa only [ActiveSubjectResidual.repFree, par, out2, inp2, true_and] using safeFrame
  have unique : ActiveSubjectResidual.count (.zero : Var (Srt.nm :: Γ) Srt.nm) (.succ channel)
      (fun _ name => .succ name)
      (par (out2 (.var channel) (.var first) (.var second)) (par (inp2 (.var channel) guard) frame)) ≤ 2 := by
    simp only [par, out2, inp2, ActiveSubjectResidual.count, ActiveSubjectResidual.onSubject,
      ActiveMarkedNames.nameKey, decide_true, ite_true, quiet]
    omega
  have updated := ActiveSubjectBinaryFiring.supplied_binary_endpoint
    (.zero : Var (Srt.nm :: Γ) Srt.nm) (.succ channel) (fun _ name => .succ name)
    (.var first) (.var second) exposure safe unique received
  have untouched := ActiveSubjectBinaryFiring.releasePair_of_count_zero
    (.zero : Var (Srt.nm :: Γ) Srt.nm) (.succ channel) (fun _ name => .succ name)
    (.var first) (.var second) frame quiet
  simp only [par, out2, inp2, ActiveSubjectBinaryFiring.releasePair,
    ActiveSubjectResidual.onSubject, ActiveMarkedNames.nameKey, decide_true, ite_true, untouched] at updated
  exact .trans (.symm (.trans (.parComm _ _) (.parUnit _))) updated

/-- The unique physical pair determines the actual endpoint of every
selected binary communication. Unary activity in the untouched frame is
allowed; it must avoid this pair's linear subject. -/
theorem pair_endpoint {Γ : Ctx sig} (channel first second : Var Γ Srt.nm)
    (guard : Proc (Srt.nm :: Srt.nm :: Γ)) (frame : Proc Γ)
    (guardMarks frameMarks : ActiveMarking.Tree Unit)
    (guardFits : Fits guardMarks guard) (frameFits : Fits frameMarks frame)
    (noOutput : visible .output2 frame = false)
    (quiet : ActiveSubjectResidual.count (.zero : Var (Srt.nm :: Γ) Srt.nm) (.succ channel)
      (fun _ name => .succ name) frame = 0) {target : Proc Γ}
    (exposure : Exposure
      (par (out2 (.var channel) (.var first) (.var second)) (par (inp2 (.var channel) guard) frame)) target)
    (binary : inputHeader exposure.selected = .input2) :
    StructuralEq (par (openPair guard (.var first) (.var second)) frame) target :=
  pair_endpoint_selected channel first second guard frame quiet exposure
    (selected_fields channel first second guard frame guardMarks frameMarks guardFits frameFits noOutput exposure binary)

/-- Other pending binary calls on different subjects do not interfere with
the actual supplied endpoint of this call. Only the input is unique. -/
theorem pair_endpoint_linear {Γ : Ctx sig} (channel first second : Var Γ Srt.nm)
    (guard : Proc (Srt.nm :: Srt.nm :: Γ)) (frame : Proc Γ)
    (guardMarks frameMarks : ActiveMarking.Tree Unit)
    (guardFits : Fits guardMarks guard) (frameFits : Fits frameMarks frame)
    (noInput : visible .input2 frame = false)
    (quiet : ActiveSubjectResidual.count (.zero : Var (Srt.nm :: Γ) Srt.nm) (.succ channel)
      (fun _ name => .succ name) frame = 0) {target : Proc Γ}
    (exposure : Exposure
      (par (out2 (.var channel) (.var first) (.var second)) (par (inp2 (.var channel) guard) frame)) target)
    (binary : inputHeader exposure.selected = .input2) :
    StructuralEq (par (openPair guard (.var first) (.var second)) frame) target :=
  pair_endpoint_selected channel first second guard frame quiet exposure
    (selected_fields_linear channel first second guard frame guardMarks frameMarks guardFits frameFits noInput quiet exposure binary)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveBinaryBoundary
