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

/-! ## Computed least manifests for complete proof requests -/

/-- All environment names occurring in the submitted proof, goal and assumptions. -/
def requestSupport (proofContext : List Tm) (proof : Pf) (proposition : Tm) : Support :=
  proofSupport proof ∪ termSupport proposition ∪ proofContext.toFinset.biUnion termSupport

theorem requestSupport_contains (proofContext : List Tm) (proof : Pf) (proposition : Tm) :
    ContextSupported (requestSupport proofContext proof proposition) proofContext ∧
      proofSupport proof ⊆ requestSupport proofContext proof proposition ∧
      termSupport proposition ⊆ requestSupport proofContext proof proposition := by
  refine ⟨?_, Finset.subset_union_left.trans Finset.subset_union_left,
    Finset.subset_union_right.trans Finset.subset_union_left⟩
  intro assumption member dependency depends
  exact Finset.mem_union_right _
    (Finset.mem_biUnion.mpr ⟨assumption, List.mem_toFinset.mpr member, depends⟩)

theorem requestSupport_subset {support : Support} {proofContext : List Tm}
    {proof : Pf} {proposition : Tm}
    (context : ContextSupported support proofContext)
    (proofSupported : proofSupport proof ⊆ support)
    (propositionSupported : termSupport proposition ⊆ support) :
    requestSupport proofContext proof proposition ⊆ support := by
  apply Finset.union_subset (Finset.union_subset proofSupported propositionSupported)
  intro dependency member
  obtain ⟨assumption, member, depends⟩ := Finset.mem_biUnion.mp member
  exact context assumption (List.mem_toFinset.mp member) depends

/-- No manifest is supplied by the caller: follow the actual selected native
lookups transitively from the request's syntactic support. -/
def requestClosure (environment : Environment) (proofContext : List Tm)
    (proof : Pf) (proposition : Tm) : Support :=
  EnvironmentDependencyCheck.dependencyClosure environment
    (requestSupport proofContext proof proposition)

/-- Leastness is relative to the syntactic closure condition, not a claim that
every dependency will be queried in each execution of the checker. -/
theorem requestClosure_least {environment : Environment} {support : Support}
    {proofContext : List Tm} {proof : Pf} {proposition : Tm}
    (closed : Closed environment support) (context : ContextSupported support proofContext)
    (proofSupported : proofSupport proof ⊆ support)
    (propositionSupported : termSupport proposition ⊆ support) :
    requestClosure environment proofContext proof proposition ⊆ support :=
  EnvironmentDependencyCheck.dependencyClosure_least _ _ _
    (requestSupport_subset context proofSupported propositionSupported) closed

/-- Compare only the computed dependency manifest. This is a sufficient test
for verdict reuse, not a test that the proof or either theory is sound. -/
def requestFrameCheck (source target : Environment) (proofContext : List Tm)
    (proof : Pf) (proposition : Tm) : Bool :=
  EnvironmentDependencyCheck.agreementCheck source target
    (requestClosure source proofContext proof proposition)

/-- Computing the manifest discharges all support and closure obligations of
the original executable manifest checker. -/
theorem requestFrameCheck_eq_proofFrameCheck (source target : Environment)
    (proofContext : List Tm) (proof : Pf) (proposition : Tm) :
    requestFrameCheck source target proofContext proof proposition =
      proofFrameCheck source target (requestClosure source proofContext proof proposition)
        proofContext proof proposition := by
  obtain ⟨context, proofSupported, propositionSupported⟩ :=
    requestSupport_contains proofContext proof proposition
  have contains := EnvironmentDependencyCheck.subset_dependencyClosure source
    (requestSupport proofContext proof proposition)
  have context' : ContextSupported (requestClosure source proofContext proof proposition)
      proofContext := fun assumption member => (context assumption member).trans contains
  have proof' := proofSupported.trans contains
  have proposition' := propositionSupported.trans contains
  apply Bool.eq_iff_iff.mpr
  rw [proofFrameCheck_iff]
  simp only [requestFrameCheck, EnvironmentDependencyCheck.agreementCheck_iff]
  constructor
  · intro agreement
    exact ⟨agreement, EnvironmentDependencyCheck.dependencyClosure_closed _ _,
      context', proof', proposition'⟩
  · exact fun valid => valid.1

/-- A successful comparison of a computed manifest preserves the actual full
native checker for every fuel bound, including its false verdicts. -/
theorem checkProof_eq_of_requestFrameCheck {source target : Environment}
    {proofContext : List Tm} {proof : Pf} {proposition : Tm}
    (checked : requestFrameCheck source target proofContext proof proposition = true)
    (fuel typeDepth : Nat) (termContext : List Tp) :
    checkProof target fuel typeDepth termContext proofContext proof proposition =
      checkProof source fuel typeDepth termContext proofContext proof proposition := by
  apply checkProof_frame_of_check
  rwa [← requestFrameCheck_eq_proofFrameCheck]

/-- Computing the least manifest loses no revision accepted by the existing
manifest discipline. A larger closed manifest cannot repair a failed comparison
on the least one. This is not completeness for observational checker equality. -/
theorem requestFrameCheck_iff_exists_manifest (source target : Environment)
    (proofContext : List Tm) (proof : Pf) (proposition : Tm) :
    requestFrameCheck source target proofContext proof proposition = true ↔
      ∃ support, proofFrameCheck source target support proofContext proof proposition = true := by
  constructor
  · intro checked
    exact ⟨requestClosure source proofContext proof proposition,
      (requestFrameCheck_eq_proofFrameCheck _ _ _ _ _).symm ▸ checked⟩
  · rintro ⟨support, checked⟩
    obtain ⟨agreement, closed, context, proofSupported, propositionSupported⟩ :=
      proofFrameCheck_iff.mp checked
    exact (EnvironmentDependencyCheck.agreementCheck_iff _ _ _).mpr
      (agreement.mono (requestClosure_least closed context proofSupported propositionSupported))

namespace ComputedControls

open EnvironmentDependencyCheck

def source : Environment where
  terms := [⟨"x", .prop, some (.named "y")⟩, ⟨"y", .prop, none⟩,
    ⟨"unused", .prop, some (.named "outside")⟩]
  known := [⟨"k", .named "x"⟩]

def changedUnused : Environment :=
  { source with terms := source.terms ++ [⟨"outside", .prop, none⟩] }

theorem exact_request : requestClosure source [] (.known "k") (.named "y") =
    {.knownName "k", .termName "x", .termName "y"} := by decide

/-- The overapproximation rejects this revision; the computed closed manifest
licenses reuse without changing the checker or its fuel. -/
theorem unnecessary_invalidation_removed :
    frameCheck source changedUnused
      (conservativeSupport source (requestSupport [] (.known "k") (.named "y"))) = false ∧
    requestFrameCheck source changedUnused [] (.known "k") (.named "y") = true := by decide

theorem hidden_dependency_change_rejected :
    requestFrameCheck source { source with terms := [⟨"x", .prop, none⟩] }
      [] (.known "k") (.named "y") = false := by decide

theorem absent_dependency_retained :
    requestFrameCheck source changedUnused [] (.hyp 0) (.named "outside") = false := by decide

theorem framed_checker (fuel : Nat) :
    checkProof changedUnused fuel 0 [] [] (.known "k") (.named "y") =
      checkProof source fuel 0 [] [] (.known "k") (.named "y") :=
  checkProof_eq_of_requestFrameCheck (by decide) fuel 0 []

theorem accepted_and_exhausted :
    checkProof source 8 0 [] [] (.known "k") (.named "y") = true ∧
      checkProof source 0 0 [] [] (.known "k") (.named "y") = false := by
  simp [source, checkProof, checkNormalizedProof, inferProof, normalize, deltaNormalize,
    Tm.normalize, Tm.normalizeOne, Environment.lookupTerm?, lookupTermList?,
    Environment.lookupKnown?, lookupKnownList?]

end ComputedControls

#print axioms EnvironmentDependencyCheck.dependencyClosure_eq_of_agreement
#print axioms requestClosure_least
#print axioms checkProof_eq_of_requestFrameCheck
#print axioms requestFrameCheck_iff_exists_manifest
#print axioms ComputedControls.unnecessary_invalidation_removed
#print axioms ComputedControls.framed_checker

end Mettapedia.Languages.Megalodon.NativeProofEnvironment
