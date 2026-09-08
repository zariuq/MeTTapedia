import Mettapedia.Languages.Megalodon.EnvironmentDependencyCheck

/-!
# Dependency-local framing for native Megalodon proof checking

The native checker consults only a dependency-closed finite part of its
environment. Agreement on that part preserves its returned result,
including rejection and normalization failure. Declarations outside the support
may be added, removed, or changed. These results concern the actual full native
syntax and do not require a monomorphic interpretation or logical soundness
assumptions on the supplied declarations. Equal results at an unchanged fuel
bound do not imply equal execution cost or identical lookup traces.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.NativeProofEnvironment

open MathdataKernel NativeSupport EnvironmentDependency

/-- Every assumption in a native proof context uses only the selected support. -/
def ContextSupported (support : Support) (context : List Tm) : Prop :=
  ∀ proposition ∈ context, termSupport proposition ⊆ support

theorem contextSupported_nil (support : Support) : ContextSupported support [] := by
  simp [ContextSupported]

theorem ContextSupported.cons {support : Support} {context : List Tm} {proposition : Tm}
    (contextSupported : ContextSupported support context)
    (propositionSupported : termSupport proposition ⊆ support) :
    ContextSupported support (proposition :: context) := by
  intro term membership
  rcases List.mem_cons.mp membership with rfl | membership
  · exact propositionSupported
  · exact contextSupported term membership

theorem ContextSupported.shift {support : Support} {context : List Tm}
    (contextSupported : ContextSupported support context) (cutoff amount : Nat) :
    ContextSupported support (context.map (Tm.shift cutoff amount)) := by
  intro proposition membership
  obtain ⟨original, member, rfl⟩ := List.mem_map.mp membership
  simpa using contextSupported original member

/-- A successfully inferred proposition has no dependencies outside the closed
support of the proof and its assumptions. This includes known propositions,
definition unfolding, term instantiation, and prefix type instantiation. -/
theorem inferProof_support {environment : Environment} {support : Support}
    (closed : Closed environment support) {fuel typeDepth : Nat}
    {termContext : List Tp} {proofContext : List Tm} {proof : Pf} {result : Tm}
    (contextSupported : ContextSupported support proofContext)
    (supported : proofSupport proof ⊆ support)
    (success : inferProof environment fuel typeDepth termContext proofContext proof =
      some result) : termSupport result ⊆ support := by
  induction proof generalizing typeDepth termContext proofContext result with
  | gpa name => simp [inferProof] at success
  | hyp index =>
      exact contextSupported result (List.mem_of_getElem? success)
  | known name =>
      have member : Dependency.knownName name ∈ support := by
        simpa [proofSupport] using supported
      cases lookup : environment.lookupKnown? name with
      | none => simp [inferProof, lookup] at success
      | some proposition =>
          exact normalize_support closed (closed.known member lookup)
            (by simpa [inferProof, lookup] using success)
  | termApp function argument functionIH =>
      obtain ⟨functionSupported, argumentSupported⟩ :=
        Finset.union_subset_iff.mp supported
      cases functionResult : inferProof environment fuel typeDepth termContext
          proofContext function with
      | none => simp [inferProof, functionResult] at success
      | some proposition =>
          have propositionSupported := functionIH contextSupported functionSupported functionResult
          cases proposition <;> try simp [inferProof, functionResult] at success
          case all domain body =>
            cases argumentType : inferTerm environment typeDepth termContext argument with
            | none => simp [argumentType] at success
            | some actual =>
                by_cases same : actual = domain
                · cases normalizedArgument : deltaNormalize environment fuel argument with
                  | none =>
                      simp [argumentType, same, normalizedArgument] at success
                  | some argumentValue =>
                      have argumentValueSupported :=
                        deltaNormalize_support closed argumentSupported normalizedArgument
                      have bodySupported : termSupport body ⊆ support := propositionSupported
                      have instantiatedSupported :=
                        (termSupport_instantiate_subset argumentValue body).trans
                          (Finset.union_subset argumentValueSupported bodySupported)
                      exact normalize_support closed instantiatedSupported
                        (by simpa [inferProof, functionResult, argumentType, same,
                          normalizedArgument] using success)
                · simp [argumentType, same] at success
  | proofApp function argument functionIH _argumentIH =>
      obtain ⟨functionSupported, _argumentSupported⟩ :=
        Finset.union_subset_iff.mp supported
      cases functionResult : inferProof environment fuel typeDepth termContext
          proofContext function with
      | none => simp [inferProof, functionResult] at success
      | some proposition =>
          have propositionSupported := functionIH contextSupported functionSupported functionResult
          cases proposition <;> try simp [inferProof, functionResult] at success
          case imp domain codomain =>
            cases argumentResult : inferProof environment fuel typeDepth termContext
                proofContext argument with
            | none => simp [argumentResult] at success
            | some actual =>
                by_cases same : actual = domain
                · have resultEqual : codomain = result := by
                    simpa [inferProof, functionResult, argumentResult, same] using success
                  subst result
                  exact (Finset.union_subset_iff.mp propositionSupported).2
                · simp [argumentResult, same] at success
  | proofLam proposition body bodyIH =>
      obtain ⟨propositionSupported, bodySupported⟩ :=
        Finset.union_subset_iff.mp supported
      cases propositionType : inferTerm environment typeDepth termContext proposition with
      | none => simp [inferProof, propositionType] at success
      | some actual =>
          by_cases isProp : actual = .prop
          · cases normalized : MathdataKernel.normalize environment fuel proposition with
            | none => simp [inferProof, propositionType, isProp, normalized] at success
            | some propositionValue =>
                have valueSupported := normalize_support closed propositionSupported normalized
                cases bodyResult : inferProof environment fuel typeDepth termContext
                    (propositionValue :: proofContext) body with
                | none =>
                    simp [inferProof, propositionType, isProp, normalized, bodyResult] at success
                | some bodyValue =>
                    have resultEqual : .imp propositionValue bodyValue = result := by
                      simpa [inferProof, propositionType, isProp, normalized, bodyResult] using success
                    subst result
                    exact Finset.union_subset valueSupported
                      (bodyIH (contextSupported.cons valueSupported) bodySupported bodyResult)
          · simp [inferProof, propositionType, isProp] at success
  | termLam type body bodyIH =>
      cases wellFormed : type.plainWellFormed typeDepth with
      | false => simp [inferProof, wellFormed] at success
      | true =>
          cases bodyResult : inferProof environment fuel typeDepth (type :: termContext)
              (proofContext.map (Tm.shift 0 1)) body with
          | none => simp [inferProof, wellFormed, bodyResult] at success
          | some bodyValue =>
              have resultEqual : .all type bodyValue = result := by
                simpa [inferProof, wellFormed, bodyResult] using success
              subst result
              change termSupport bodyValue ⊆ support
              exact bodyIH (contextSupported.shift 0 1) supported bodyResult
  | typeApp function type functionIH =>
      cases functionResult : inferProof environment fuel typeDepth termContext
          proofContext function with
      | none => simp [inferProof, functionResult] at success
      | some proposition =>
          have propositionSupported := functionIH contextSupported supported functionResult
          cases proposition <;> try simp [inferProof, functionResult] at success
          case typeAll body =>
            have resultEqual : Tm.typeInstantiate type body = result := by
              simpa [inferProof, functionResult] using success
            subst result
            simpa [termSupport] using propositionSupported
  | typeLam body bodyIH =>
      cases termContext with
      | cons type termContext => simp [inferProof] at success
      | nil =>
          cases proofContext with
          | cons proposition proofContext => simp [inferProof] at success
          | nil =>
              cases bodyResult : inferProof environment fuel (typeDepth + 1) [] [] body with
              | none => simp [inferProof, bodyResult] at success
              | some bodyValue =>
                  have resultEqual : .typeAll bodyValue = result := by
                    simpa [inferProof, bodyResult] using success
                  subst result
                  change termSupport bodyValue ⊆ support
                  exact bodyIH (contextSupported_nil support) supported bodyResult

/-- Exact native proof inference is local to a dependency-closed support.
No relation is required between declarations outside that support. -/
theorem inferProof_frame {source target : Environment} {support : Support}
    (agreement : Agreement source target support) (closed : Closed source support)
    {fuel typeDepth : Nat} {termContext : List Tp} {proofContext : List Tm} {proof : Pf}
    (contextSupported : ContextSupported support proofContext)
    (supported : proofSupport proof ⊆ support) :
    inferProof target fuel typeDepth termContext proofContext proof =
      inferProof source fuel typeDepth termContext proofContext proof := by
  induction proof generalizing typeDepth termContext proofContext with
  | gpa name => rfl
  | hyp index => rfl
  | known name =>
      have member : Dependency.knownName name ∈ support := by
        simpa [proofSupport] using supported
      simp only [inferProof]
      rw [agreement.known member]
      cases lookup : source.lookupKnown? name with
      | none => rfl
      | some proposition =>
          exact normalize_frame agreement closed (closed.known member lookup)
  | termApp function argument functionIH =>
      obtain ⟨functionSupported, argumentSupported⟩ :=
        Finset.union_subset_iff.mp supported
      simp only [inferProof]
      rw [functionIH contextSupported functionSupported,
        inferTerm_frame agreement argumentSupported,
        deltaNormalize_frame agreement closed argumentSupported]
      cases functionResult : inferProof source fuel typeDepth termContext
          proofContext function with
      | none => rfl
      | some proposition =>
          cases proposition <;> try rfl
          case all domain body =>
            cases argumentType : inferTerm source typeDepth termContext argument with
            | none => rfl
            | some actual =>
                by_cases same : actual = domain
                · simp only [same]
                  cases normalizedArgument : deltaNormalize source fuel argument with
                  | none => rfl
                  | some argumentValue =>
                      have argumentValueSupported :=
                        deltaNormalize_support closed argumentSupported normalizedArgument
                      have bodySupported : termSupport body ⊆ support :=
                        by simpa [termSupport] using
                          inferProof_support closed contextSupported functionSupported functionResult
                      simpa using normalize_frame agreement closed (fuel := fuel)
                        ((termSupport_instantiate_subset argumentValue body).trans
                          (Finset.union_subset argumentValueSupported bodySupported))
                · simp [same]
  | proofApp function argument functionIH argumentIH =>
      obtain ⟨functionSupported, argumentSupported⟩ :=
        Finset.union_subset_iff.mp supported
      simp only [inferProof]
      rw [functionIH contextSupported functionSupported,
        argumentIH contextSupported argumentSupported]
  | proofLam proposition body bodyIH =>
      obtain ⟨propositionSupported, bodySupported⟩ :=
        Finset.union_subset_iff.mp supported
      simp only [inferProof]
      rw [inferTerm_frame agreement propositionSupported,
        normalize_frame agreement closed propositionSupported]
      cases propositionType : inferTerm source typeDepth termContext proposition with
      | none => rfl
      | some actual =>
          by_cases isProp : actual = .prop
          · subst actual
            cases normalized : MathdataKernel.normalize source fuel proposition with
            | none => rfl
            | some propositionValue =>
                have valueSupported := normalize_support closed propositionSupported normalized
                simp [bodyIH (contextSupported.cons valueSupported) bodySupported]
          · simp [isProp]
  | termLam type body bodyIH =>
      simp only [inferProof]
      rw [bodyIH (contextSupported.shift 0 1) supported]
  | typeApp function type functionIH =>
      simp only [inferProof]
      rw [functionIH contextSupported supported]
  | typeLam body bodyIH =>
      simp only [inferProof]
      rw [bodyIH (contextSupported_nil support) supported]

/-- Checking an already-normalized goal requires support only for the proof
and assumptions: comparing the goal itself performs no environmental lookup. -/
theorem checkNormalizedProof_frame {source target : Environment} {support : Support}
    (agreement : Agreement source target support) (closed : Closed source support)
    {fuel typeDepth : Nat} {termContext : List Tp} {proofContext : List Tm}
    {proof : Pf} (proposition : Tm)
    (contextSupported : ContextSupported support proofContext)
    (supported : proofSupport proof ⊆ support) :
    checkNormalizedProof target fuel typeDepth termContext proofContext proof proposition =
      checkNormalizedProof source fuel typeDepth termContext proofContext proof proposition := by
  unfold checkNormalizedProof
  rw [inferProof_frame agreement closed contextSupported supported]

/-- Native source-level checking is unchanged, including both proof failure
and fuel exhaustion while normalizing the declared goal. -/
theorem checkProof_frame {source target : Environment} {support : Support}
    (agreement : Agreement source target support) (closed : Closed source support)
    {fuel typeDepth : Nat} {termContext : List Tp} {proofContext : List Tm}
    {proof : Pf} {proposition : Tm}
    (contextSupported : ContextSupported support proofContext)
    (proofSupported : proofSupport proof ⊆ support)
    (propositionSupported : termSupport proposition ⊆ support) :
    checkProof target fuel typeDepth termContext proofContext proof proposition =
      checkProof source fuel typeDepth termContext proofContext proof proposition := by
  unfold checkProof
  rw [normalize_frame agreement closed propositionSupported]
  cases normalization : MathdataKernel.normalize source fuel proposition with
  | none => rfl
  | some normalized =>
      exact checkNormalizedProof_frame agreement closed normalized contextSupported proofSupported

#print axioms inferProof_support
#print axioms inferProof_frame
#print axioms checkNormalizedProof_frame
#print axioms checkProof_frame

/-! ## Executable admission of a complete proof request -/

/-- A finite check of the environmental and syntactic support conditions for
reusing a native source-level proof verdict after an environment revision. -/
def proofFrameCheck (source target : Environment) (support : Support)
    (proofContext : List Tm) (proof : Pf) (proposition : Tm) : Bool :=
  EnvironmentDependencyCheck.frameCheck source target support &&
    proofContext.all (fun assumption => decide (termSupport assumption ⊆ support)) &&
    decide (proofSupport proof ⊆ support) && decide (termSupport proposition ⊆ support)

/-- The executable check discharges exactly the declared manifest conditions;
it does not itself run or assert acceptance of the submitted proof. -/
theorem proofFrameCheck_iff {source target : Environment} {support : Support}
    {proofContext : List Tm} {proof : Pf} {proposition : Tm} :
    proofFrameCheck source target support proofContext proof proposition = true ↔
      Agreement source target support ∧ Closed source support ∧
        ContextSupported support proofContext ∧ proofSupport proof ⊆ support ∧
          termSupport proposition ⊆ support := by
  simp [proofFrameCheck, EnvironmentDependencyCheck.frameCheck_iff,
    ContextSupported, List.all_eq_true, and_assoc]

/-- One successful finite manifest check licenses exact verdict reuse for every
fuel, type-variable depth and term context. The reusable verdict may be false. -/
theorem checkProof_frame_of_check {source target : Environment} {support : Support}
    {proofContext : List Tm} {proof : Pf} {proposition : Tm}
    (accepted : proofFrameCheck source target support proofContext proof proposition = true)
    (fuel typeDepth : Nat) (termContext : List Tp) :
    checkProof target fuel typeDepth termContext proofContext proof proposition =
      checkProof source fuel typeDepth termContext proofContext proof proposition := by
  obtain ⟨agreement, closed, contextSupported, proofSupported, propositionSupported⟩ :=
    proofFrameCheck_iff.mp accepted
  exact checkProof_frame agreement closed contextSupported proofSupported propositionSupported

#print axioms proofFrameCheck_iff
#print axioms checkProof_frame_of_check

end Mettapedia.Languages.Megalodon.NativeProofEnvironment
