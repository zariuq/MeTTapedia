import Mettapedia.Languages.MeTTa.HE.LeaTTaMatcherCongruence

/-!
# Operational completion of the HE matcher/merge kernel

This module closes the remaining existence interfaces in
`LeaTTaMatcherCongruence`.  Structural recursion is indexed by translated
atom size; the independent Robinson index is used only for genuine live
class-value merge-back.  Neither index is inferred from binding-list order or
representative chronology.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaBridge

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.DeclMergeSpec
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-! ## Embedding expression-frontier certificates -/

/-- Once the normalized residual part of an expression frontier is admitted
by an ambient trace, original-constraint coverage supplies the other half of
the frontier certificate.  This is the exact provenance split used by the
recursive matcher kernel: raw pointwise constraints are structural, while
Robinson residuals are operational. -/
theorem HEExpressionResidualFrontier.certificateTrace_subset_of_covered
    {trace : List (String × Metta.Atom)}
    {fuel : Nat} {left right : List Atom} {result : Metta.Subst}
    (h : HEExpressionResidualFrontier fuel left right result)
    (hcoverage : HEOriginalListConstraintCoverage trace left right)
    (hresidual : ∀ entry ∈ h.residualTrace, entry ∈ trace) :
    ∀ entry ∈ h.certificateTrace, entry ∈ trace := by
  intro entry hentry
  rcases List.mem_append.mp hentry with horiginal | hnormalized
  · exact hcoverage h.originalConstraints
      h.decomposeList_top_eq_originalConstraints entry horiginal
  · exact hresidual entry hnormalized

/-- Trace inclusion transports the undirected alias reachability induced by
an expression-frontier certificate into the ambient equality graph. -/
theorem HEExpressionResidualFrontier.certificateAllowed_mono_of_trace_subset
    {trace : List (String × Metta.Atom)}
    {fuel : Nat} {left right : List Atom} {result : Metta.Subst}
    (h : HEExpressionResidualFrontier fuel left right result)
    (hsubset : ∀ entry ∈ h.certificateTrace, entry ∈ trace) :
    ∀ {start finish : String},
      (EqualityClosure.edgeGraph h.certificateAllowed).Reachable start finish →
        (EqualityClosure.edgeGraph
          (eliminationTraceAliases trace)).Reachable start finish := by
  intro start finish hreach
  apply hreach.mono
  intro first second hadj
  rw [EqualityClosure.edgeGraph_adj_iff] at hadj ⊢
  rcases hadj with ⟨hne, hforward | hreverse⟩
  · refine ⟨hne, Or.inl ?_⟩
    unfold HEExpressionResidualFrontier.certificateAllowed at hforward
    rw [mem_eliminationTraceAliases_iff] at hforward ⊢
    exact hsubset _ hforward
  · refine ⟨hne, Or.inr ?_⟩
    unfold HEExpressionResidualFrontier.certificateAllowed at hreverse
    rw [mem_eliminationTraceAliases_iff] at hreverse ⊢
    exact hsubset _ hreverse

/-- Combined ambient embedding principle for a complete expression-frontier
certificate.  Downstream recursion therefore has only one genuine transport
obligation: inclusion of the normalized residual trace. -/
theorem HEExpressionResidualFrontier.certificate_embeds_of_covered
    {trace : List (String × Metta.Atom)}
    {fuel : Nat} {left right : List Atom} {result : Metta.Subst}
    (h : HEExpressionResidualFrontier fuel left right result)
    (hcoverage : HEOriginalListConstraintCoverage trace left right)
    (hresidual : ∀ entry ∈ h.residualTrace, entry ∈ trace) :
    (∀ entry ∈ h.certificateTrace, entry ∈ trace) ∧
      ∀ {start finish : String},
        (EqualityClosure.edgeGraph h.certificateAllowed).Reachable start finish →
          (EqualityClosure.edgeGraph
            (eliminationTraceAliases trace)).Reachable start finish := by
  have hsubset := h.certificateTrace_subset_of_covered hcoverage hresidual
  exact ⟨hsubset, h.certificateAllowed_mono_of_trace_subset hsubset⟩

/-- Transport a completed original expression matcher from its exact local
frontier certificate into an ambient reconciliation trace.  Its output,
declarative matcher derivation, and solution theory are unchanged. -/
def HEExpressionResidualFrontier.embedSolutionMatch_of_covered
    {trace : List (String × Metta.Atom)}
    {fuel : Nat} {left right : List Atom} {result : Metta.Subst}
    (h : HEExpressionResidualFrontier fuel left right result)
    (matched : HEMatchSolutionCertified
      h.certificateTrace h.certificateAllowed
      (.expression left) (.expression right) result)
    (hcoverage : HEOriginalListConstraintCoverage trace left right)
    (hresidual : ∀ entry ∈ h.residualTrace, entry ∈ trace) :
    HEMatchSolutionCertified trace (eliminationTraceAliases trace)
      (.expression left) (.expression right) result := by
  obtain ⟨htrace, hallowed⟩ :=
    h.certificate_embeds_of_covered hcoverage hresidual
  exact matched.mono htrace hallowed

/-- Solution-certified live merges are monotone in their ambient provenance
and equality certificates.  The selected executable merge and its exact
post-merge solution theory do not depend on those presentations. -/
def HELiveMergeSolutionCertified.mono
    {smallTrace largeTrace : List (String × Metta.Atom)}
    {smallAllowed largeAllowed : List (String × String)}
    {seed right : Bindings} {subst : Metta.Subst}
    (h : HELiveMergeSolutionCertified
      smallTrace smallAllowed seed right subst)
    (htrace : ∀ entry ∈ smallTrace, entry ∈ largeTrace)
    (hallowed : ∀ {start finish : String},
      (EqualityClosure.edgeGraph smallAllowed).Reachable start finish →
        (EqualityClosure.edgeGraph largeAllowed).Reachable start finish) :
    HELiveMergeSolutionCertified
      largeTrace largeAllowed seed right subst := {
  toHELiveMergeCertified := h.toHELiveMergeCertified.mono htrace hallowed
  solutions := h.solutions
}

/-- Compose an independently certified original atom matcher with the actual
live merge selected for its output.  This is the operational factorization
used by every expression and class-conflict branch: the matcher never sees
the live seed, and the external merge alone changes the accumulator. -/
def HEMatchSolutionCertified.withCoreLiveMergeResidual
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {left right : Atom} {matchedSubst liveSubst : Metta.Subst}
    {seed : Bindings}
    (matched : HEMatchSolutionCertified trace allowed
      left right matchedSubst)
    (live : HELiveMergeSolutionCertified trace allowed
      seed matched.out liveSubst)
    (hseed : LeaEliminationTraceAssignmentsSound seed trace) :
    HELiveMatchMergeCoreResidualCertified trace allowed
      left right seed liveSubst := {
  toHELiveMatchMergeCoreSolutionCertified := {
    toHELiveMatchMergeCoreCertified :=
      matched.toHEMatchCertified.withCoreLiveMerge
        live.toHELiveMergeCertified
    solutions := live.solutions
  }
  afterAssignmentsSound :=
    mergeRel_assignmentsSound_of_traceSound
      live.traceSound hseed matched.assignmentsSound
}

/-- Accumulator-threaded matching only extends the seed's observable
assignments and equality classes.  Each child is merged into the current
accumulator, so this follows directly from merge observation extension and
composition along the tail. -/
theorem matchListAccRel_observationExtension
    {left right : List Atom} {seed out : Bindings}
    (h : DeclMatchSpec.MatchListAccRel left right seed out) :
    HEBindingObservationExtension seed out := by
  let AtomMotive := fun (_left _right : Atom) (_out : Bindings)
      (_h : DeclMatchSpec.MatchRel _left _right _out) => True
  let ListMotive := fun (_left _right : List Atom)
      (listSeed listOut : Bindings)
      (_h : DeclMatchSpec.MatchListAccRel
        _left _right listSeed listOut) =>
    HEBindingObservationExtension listSeed listOut
  exact DeclMatchSpec.MatchListAccRel.rec
    (motive_1 := AtomMotive) (motive_2 := ListMotive)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by intros; trivial)
    (by exact HEBindingObservationExtension.refl _)
    (by
      intro headLeft headRight tailLeft tailRight listSeed matched next
        listOut fuel hhead hmerge htail _headIH tailIH
      exact (mergeBindings_observationExtension hmerge).trans tailIH)
    h

/-- A matcher's final equality-closure upper bound reconstructs the complete
derivation-local equality certificate for that concrete atom/list matcher.
Every head matcher and intermediate merge embeds into the final list output;
therefore no MGU orientation or intermediate representative choice is part
of the premise. -/
theorem matchEqualityClosureBoundSound_of_outputBound
    {allowed : List (String × String)}
    {left right : Atom} {out : Bindings}
    (hmatch : DeclMatchSpec.MatchRel left right out)
    (hout : HEEqualityClosureBound out allowed) :
    MatchEqualityClosureBoundSound allowed hmatch := by
  let AtomMotive := fun (atomLeft atomRight : Atom) (matched : Bindings)
      (h : DeclMatchSpec.MatchRel atomLeft atomRight matched) =>
    HEEqualityClosureBound matched allowed →
      MatchEqualityClosureBoundSound allowed h
  let ListMotive := fun (lefts rights : List Atom)
      (seed result : Bindings)
      (h : DeclMatchSpec.MatchListAccRel lefts rights seed result) =>
    HEEqualityClosureBound result allowed →
      MatchListEqualityClosureBoundSound allowed h
  exact DeclMatchSpec.MatchRel.rec
    (motive_1 := AtomMotive) (motive_2 := ListMotive)
    (fun name _hbound => MatchEqualityClosureBoundSound.symSym)
    (fun first second hbound =>
      MatchEqualityClosureBoundSound.varVar
        (hbound.edge (by simp)))
    (fun hnonvar _hbound =>
      MatchEqualityClosureBoundSound.varNonVar (hnonvar := hnonvar))
    (fun hnonvar _hbound =>
      MatchEqualityClosureBoundSound.nonVarVar (hnonvar := hnonvar))
    (fun value _hbound => MatchEqualityClosureBoundSound.grounded)
    (fun hlist ih hbound =>
      MatchEqualityClosureBoundSound.expr (ih hbound))
    (by
      intro _seed _hbound
      exact MatchListEqualityClosureBoundSound.nil)
    (by
      intro atomLeft atomRight lefts rights seed matched next result fuel
        hhead hmerge htail ihhead ihtail hbound
      have hnextBound : HEEqualityClosureBound next allowed := by
        intro start finish hclass
        exact hbound start finish
          ((matchListAccRel_observationExtension htail).classes hclass)
      have hmatchedBound : HEEqualityClosureBound matched allowed := by
        intro start finish hclass
        exact hnextBound start finish
          (mergeBindings_right_eqClass_mono hmerge hclass)
      exact MatchListEqualityClosureBoundSound.cons
        (hmerge := hmerge)
        (ihhead hmatchedBound)
        (mergeEqualityClosureBoundSound_of_outputBound
          (mergeBindings_sound hmerge) hnextBound)
        (ihtail hbound))
    hmatch hout

/-- List companion of `matchEqualityClosureBoundSound_of_outputBound`. -/
theorem matchListEqualityClosureBoundSound_of_outputBound
    {allowed : List (String × String)} {left right : List Atom}
    {seed out : Bindings}
    (hmatch : DeclMatchSpec.MatchListAccRel left right seed out)
    (hout : HEEqualityClosureBound out allowed) :
    MatchListEqualityClosureBoundSound allowed hmatch := by
  let AtomMotive := fun (atomLeft atomRight : Atom) (matched : Bindings)
      (h : DeclMatchSpec.MatchRel atomLeft atomRight matched) =>
    HEEqualityClosureBound matched allowed →
      MatchEqualityClosureBoundSound allowed h
  let ListMotive := fun (lefts rights : List Atom)
      (listSeed result : Bindings)
      (h : DeclMatchSpec.MatchListAccRel lefts rights listSeed result) =>
    HEEqualityClosureBound result allowed →
      MatchListEqualityClosureBoundSound allowed h
  exact DeclMatchSpec.MatchListAccRel.rec
    (motive_1 := AtomMotive) (motive_2 := ListMotive)
    (fun name _hbound => MatchEqualityClosureBoundSound.symSym)
    (fun first second hbound =>
      MatchEqualityClosureBoundSound.varVar
        (hbound.edge (by simp)))
    (fun hnonvar _hbound =>
      MatchEqualityClosureBoundSound.varNonVar (hnonvar := hnonvar))
    (fun hnonvar _hbound =>
      MatchEqualityClosureBoundSound.nonVarVar (hnonvar := hnonvar))
    (fun value _hbound => MatchEqualityClosureBoundSound.grounded)
    (fun hlist ih hbound =>
      MatchEqualityClosureBoundSound.expr (ih hbound))
    (by
      intro _seed _hbound
      exact MatchListEqualityClosureBoundSound.nil)
    (by
      intro atomLeft atomRight lefts rights listSeed matched next result fuel
        hhead hmerge htail ihhead ihtail hbound
      have hnextBound : HEEqualityClosureBound next allowed := by
        intro start finish hclass
        exact hbound start finish
          ((matchListAccRel_observationExtension htail).classes hclass)
      have hmatchedBound : HEEqualityClosureBound matched allowed := by
        intro start finish hclass
        exact hnextBound start finish
          (mergeBindings_right_eqClass_mono hmerge hclass)
      exact MatchListEqualityClosureBoundSound.cons
        (hmerge := hmerge)
        (ihhead hmatchedBound)
        (mergeEqualityClosureBoundSound_of_outputBound
          (mergeBindings_sound hmerge) hnextBound)
        (ihtail hbound))
    hmatch hout

/-! ## Live-only hidden matcher boundary -/

/-- A hidden conflict matcher need not have standalone provenance in the
ambient Robinson trace.  Its actual external merge does: that is the exact
certificate consumed by the enclosing live conflict constructor. -/
structure HELiveHiddenMatchResidualCertified
    (trace : List (String × Metta.Atom))
    (allowed : List (String × String))
    (left right : Atom) (seed : Bindings) (subst : Metta.Subst) where
  matched : Bindings
  matchRel : DeclMatchSpec.MatchRel left right matched
  matchEqualitySound : MatchEqualityClosureBoundSound allowed matchRel
  liveMerge : HELiveMergeSolutionCertified trace allowed seed matched subst
  afterAssignmentsSound :
    LeaEliminationTraceAssignmentsSound liveMerge.after trace

/-- Pointwise-list companion of `HELiveHiddenMatchResidualCertified`. -/
structure HELiveHiddenListMatchResidualCertified
    (trace : List (String × Metta.Atom))
    (allowed : List (String × String))
    (left right : List Atom) (seed : Bindings) (subst : Metta.Subst) where
  matched : Bindings
  matchRel : DeclMatchSpec.MatchListAccRel
    left right Bindings.empty matched
  matchEqualitySound : MatchListEqualityClosureBoundSound allowed matchRel
  liveMerge : HELiveMergeSolutionCertified trace allowed seed matched subst
  afterAssignmentsSound :
    LeaEliminationTraceAssignmentsSound liveMerge.after trace

/-- Enlarge the ambient trace and equality carrier of a hidden atom conflict
without exposing a standalone trace certificate for its from-empty matcher.
The selected matcher, live merge, exact solution theory, and reached
accumulator are unchanged. -/
def HELiveHiddenMatchResidualCertified.mono
    {smallTrace largeTrace : List (String × Metta.Atom)}
    {smallAllowed largeAllowed : List (String × String)}
    {left right : Atom} {seed : Bindings} {subst : Metta.Subst}
    (h : HELiveHiddenMatchResidualCertified
      smallTrace smallAllowed left right seed subst)
    (htrace : ∀ entry ∈ smallTrace, entry ∈ largeTrace)
    (hallowed : ∀ {start finish : String},
      (EqualityClosure.edgeGraph smallAllowed).Reachable start finish →
        (EqualityClosure.edgeGraph largeAllowed).Reachable start finish) :
    HELiveHiddenMatchResidualCertified
      largeTrace largeAllowed left right seed subst := {
  matched := h.matched
  matchRel := h.matchRel
  matchEqualitySound := h.matchEqualitySound.mono hallowed
  liveMerge := h.liveMerge.mono htrace hallowed
  afterAssignmentsSound :=
    h.afterAssignmentsSound.of_trace_subset htrace
}

/-- Pointwise-list companion of hidden-conflict ambient transport. -/
def HELiveHiddenListMatchResidualCertified.mono
    {smallTrace largeTrace : List (String × Metta.Atom)}
    {smallAllowed largeAllowed : List (String × String)}
    {left right : List Atom} {seed : Bindings} {subst : Metta.Subst}
    (h : HELiveHiddenListMatchResidualCertified
      smallTrace smallAllowed left right seed subst)
    (htrace : ∀ entry ∈ smallTrace, entry ∈ largeTrace)
    (hallowed : ∀ {start finish : String},
      (EqualityClosure.edgeGraph smallAllowed).Reachable start finish →
        (EqualityClosure.edgeGraph largeAllowed).Reachable start finish) :
    HELiveHiddenListMatchResidualCertified
      largeTrace largeAllowed left right seed subst := {
  matched := h.matched
  matchRel := h.matchRel
  matchEqualitySound := h.matchEqualitySound.mono hallowed
  liveMerge := h.liveMerge.mono htrace hallowed
  afterAssignmentsSound :=
    h.afterAssignmentsSound.of_trace_subset htrace
}

/-- Smart constructor: the matcher equality certificate is reconstructed
from the selected output's semantic closure bound. -/
def HELiveHiddenMatchResidualCertified.ofOutputBound
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {left right : Atom}
    {seed matched : Bindings} {subst : Metta.Subst}
    (hmatch : DeclMatchSpec.MatchRel left right matched)
    (hmatchedBound : HEEqualityClosureBound matched allowed)
    (hlive : HELiveMergeSolutionCertified trace allowed seed matched subst)
    (hafter : LeaEliminationTraceAssignmentsSound hlive.after trace) :
    HELiveHiddenMatchResidualCertified
      trace allowed left right seed subst := {
  matched := matched
  matchRel := hmatch
  matchEqualitySound :=
    matchEqualityClosureBoundSound_of_outputBound hmatch hmatchedBound
  liveMerge := hlive
  afterAssignmentsSound := hafter
}

/-- Pointwise-list smart constructor with the same final-output boundary. -/
def HELiveHiddenListMatchResidualCertified.ofOutputBound
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {left right : List Atom}
    {seed matched : Bindings} {subst : Metta.Subst}
    (hmatch : DeclMatchSpec.MatchListAccRel
      left right Bindings.empty matched)
    (hmatchedBound : HEEqualityClosureBound matched allowed)
    (hlive : HELiveMergeSolutionCertified trace allowed seed matched subst)
    (hafter : LeaEliminationTraceAssignmentsSound hlive.after trace) :
    HELiveHiddenListMatchResidualCertified
      trace allowed left right seed subst := {
  matched := matched
  matchRel := hmatch
  matchEqualitySound :=
    matchListEqualityClosureBoundSound_of_outputBound hmatch hmatchedBound
  liveMerge := hlive
  afterAssignmentsSound := hafter
}

/-- Observation-first constructor for a hidden atom matcher.  The child
matcher need not be transported from a local alias graph: its equality
classes embed into the actual external merge output, whose ambient bound is
already certified by the live merge. -/
def HELiveHiddenMatchResidualCertified.ofLiveMerge
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {left right : Atom}
    {seed matched : Bindings} {subst : Metta.Subst}
    (hmatch : DeclMatchSpec.MatchRel left right matched)
    (hseedBound : HEEqualityClosureBound seed allowed)
    (hlive : HELiveMergeSolutionCertified trace allowed seed matched subst)
    (hafter : LeaEliminationTraceAssignmentsSound hlive.after trace) :
    HELiveHiddenMatchResidualCertified
      trace allowed left right seed subst := by
  have hafterBound : HEEqualityClosureBound hlive.after allowed :=
    hlive.equalitySound.preserves hseedBound
  have hmatchedBound : HEEqualityClosureBound matched allowed := by
    intro start finish hclass
    exact hafterBound start finish
      (mergeBindings_right_eqClass_mono hlive.merge_mem hclass)
  exact .ofOutputBound hmatch hmatchedBound hlive hafter

/-- Pointwise-list companion of the observation-first hidden constructor. -/
def HELiveHiddenListMatchResidualCertified.ofLiveMerge
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {left right : List Atom}
    {seed matched : Bindings} {subst : Metta.Subst}
    (hmatch : DeclMatchSpec.MatchListAccRel
      left right Bindings.empty matched)
    (hseedBound : HEEqualityClosureBound seed allowed)
    (hlive : HELiveMergeSolutionCertified trace allowed seed matched subst)
    (hafter : LeaEliminationTraceAssignmentsSound hlive.after trace) :
    HELiveHiddenListMatchResidualCertified
      trace allowed left right seed subst := by
  have hafterBound : HEEqualityClosureBound hlive.after allowed :=
    hlive.equalitySound.preserves hseedBound
  have hmatchedBound : HEEqualityClosureBound matched allowed := by
    intro start finish hclass
    exact hafterBound start finish
      (mergeBindings_right_eqClass_mono hlive.merge_mem hclass)
  exact .ofOutputBound hmatch hmatchedBound hlive hafter

/-- Attach the exact projected head solution theory to any certified live
merge whose right operand has, under the live seed, precisely the exposed
original head's solution set.  This is the common semantic boundary for all
four hidden class-value conflict forms. -/
noncomputable def
    HEProjectedTailHeadResidualSolutionPackage.liveMergeWithHeadTheory
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    {s : HEProjectedCertifiedListResidualSolutionState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed}
    {nextLeft : Atom} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage s nextLeft leftRest)
    {liveSeed matched : Bindings}
    (hlive : HELiveMergeCertified trace allowed liveSeed matched)
    (hmatchedTheory : ∀ valuation,
      (HEBindingSatisfied valuation liveSeed ∧
          HEBindingSatisfied valuation matched) ↔
        (HEBindingSatisfied valuation seed ∧
          MettaEquationSatisfied valuation
            (toLeaTTaAtom nextLeft, toLeaTTaAtom p.nextRight))) :
    HELiveMergeSolutionCertified trace allowed liveSeed matched p.nextSubst := by
  have hheadWorkImage : LeaEquationsInHEImage p.headWork := by
    intro equation hmem
    apply s.work_inHEImage equation
    rw [p.work_eq]
    exact List.mem_append_left _ hmem
  have hcurrentFresh : UnifyStateFresh
      (p.headWork ++ p.untouchedTailWork) subst := by
    have hfresh := s.projection.stateFresh s.outerStateFresh
    rw [p.work_eq] at hfresh
    exact hfresh
  have hheadFresh : UnifyStateFresh p.headWork subst := by
    intro key hkey hmem
    exact hcurrentFresh key hkey (by
      simp only [mettaEquationVars, List.flatMap_append,
        List.mem_append]
      exact Or.inl hmem)
  have hseedConstraints : ∀ valuation,
      HEBindingSatisfied valuation seed ↔
        MettaConstraintsSatisfied valuation subst := by
    intro valuation
    exact (s.seedSolutions valuation).trans
      (leaOfSubst_solution_iff valuation subst)
  refine {
    toHELiveMergeCertified := hlive
    solutions := ?_
  }
  intro valuation
  have hrun := unifyRounds_solution_iff valuation
    hheadWorkImage.noFloat hheadFresh p.nextSplit.front_run
  calc
    HEBindingSatisfied valuation hlive.after ↔
        HEBindingSatisfied valuation liveSeed ∧
          HEBindingSatisfied valuation matched :=
      mergeBindings_solution_iff hlive.merge_mem valuation
    _ ↔ HEBindingSatisfied valuation seed ∧
          MettaEquationSatisfied valuation
            (toLeaTTaAtom nextLeft, toLeaTTaAtom p.nextRight) :=
      hmatchedTheory valuation
    _ ↔ MettaEquationsSatisfied valuation p.headWork ∧
          HEBindingSatisfied valuation seed :=
      (p.headTheory valuation).symm
    _ ↔ MettaEquationsSatisfied valuation p.headWork ∧
          MettaConstraintsSatisfied valuation subst :=
      and_congr Iff.rfl (hseedConstraints valuation)
    _ ↔ MettaConstraintsSatisfied valuation p.nextSubst := hrun.symm
    _ ↔ LeaBindingSatisfied valuation
          (Metta.Bindings.ofSubst p.nextSubst) :=
      (leaOfSubst_solution_iff valuation p.nextSubst).symm

/-- Attach the exact projected head solution theory directly to an actual
external live merge.  Hidden conflict matchers deliberately expose no
standalone ambient trace certificate, so this adapter uses only their
declarative relation and the executable merge selected for its output. -/
noncomputable def
    HEProjectedTailHeadResidualSolutionPackage.liveMergeWithSolutions
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    {s : HEProjectedCertifiedListResidualSolutionState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed}
    {nextLeft : Atom} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage s nextLeft leftRest)
    {matched : Bindings}
    (hmatch : DeclMatchSpec.MatchRel nextLeft p.nextRight matched)
    (hlive : HELiveMergeCertified trace allowed seed matched) :
    HELiveMergeSolutionCertified trace allowed seed matched p.nextSubst := by
  let hexec := DeclMatchSpec.matchAtoms_complete hmatch
  let matchFuel := Classical.choose hexec
  have hmatchMem : matched ∈
      matchAtoms nextLeft p.nextRight matchFuel :=
    Classical.choose_spec hexec
  apply p.liveMergeWithHeadTheory hlive
  intro valuation
  exact and_congr Iff.rfl (matchAtoms_solution_iff hmatchMem valuation)

/-- A live merge of the actual stored/proposed class-value match has exactly
the exposed variable/non-variable head's solution theory.  The proof uses
only class membership: every satisfying seed interprets the stored value as
the queried variable, independently of representative choice or class-value
order. -/
noncomputable def
    HEProjectedTailHeadResidualSolutionPackage.assignmentConflictLiveMerge
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    {s : HEProjectedCertifiedListResidualSolutionState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed}
    {key : String} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      s (.var key) leftRest)
    {value first : Atom} {rest : List Atom} {matched : Bindings}
    (hright : p.nextRight = value)
    (hclass : seed.classValues key = first :: rest)
    (hmatch : DeclMatchSpec.MatchRel first value matched)
    (hlive : HELiveMergeCertified trace allowed seed matched) :
    HELiveMergeSolutionCertified trace allowed seed matched p.nextSubst := by
  let hexec := DeclMatchSpec.matchAtoms_complete hmatch
  let matchFuel := Classical.choose hexec
  have hmatchMem : matched ∈ matchAtoms first value matchFuel :=
    Classical.choose_spec hexec
  apply p.liveMergeWithHeadTheory hlive
  intro valuation
  constructor
  · rintro ⟨hseed, hmatched⟩
    have hfirstMem : first ∈ seed.classValues key := by
      rw [hclass]
      simp
    have hstored :=
      hseed.eq_applyClassSolution_of_mem_classValues hfirstMem
    have hinner := (matchAtoms_solution_iff hmatchMem valuation).mp hmatched
    refine ⟨hseed, ?_⟩
    rw [hright]
    simpa [MettaEquationSatisfied, toLeaTTaAtom,
      applyClassSolution] using hstored.trans hinner
  · rintro ⟨hseed, hhead⟩
    have hfirstMem : first ∈ seed.classValues key := by
      rw [hclass]
      simp
    have hstored :=
      hseed.eq_applyClassSolution_of_mem_classValues hfirstMem
    rw [hright] at hhead
    have hheadEq : valuation key =
        applyClassSolution valuation (toLeaTTaAtom value) := by
      simpa [MettaEquationSatisfied, toLeaTTaAtom,
        applyClassSolution] using hhead
    have hinner : MettaEquationSatisfied valuation
        (toLeaTTaAtom first, toLeaTTaAtom value) := by
      simpa [MettaEquationSatisfied, toLeaTTaAtom,
        applyClassSolution] using hstored.symm.trans hheadEq
    exact ⟨hseed, (matchAtoms_solution_iff hmatchMem valuation).mpr hinner⟩

/-- In a two-value equality conflict, the candidate edge already presents
the original variable/variable head, and its two joined class values are
co-satisfied.  Matching those values therefore preserves exactly the
candidate's solution set. -/
noncomputable def
    HEProjectedTailHeadResidualSolutionPackage.equalityPairConflictLiveMerge
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {leftAtoms rightAtoms : List Atom}
    {seed : Bindings}
    {s : HEProjectedCertifiedListResidualSolutionState trace allowed
      outerFuel front outerSubst fuel work subst result
        leftAtoms rightAtoms seed}
    {left : String} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      s (.var left) leftRest)
    {right : String} {first second : Atom} {matched : Bindings}
    (hright : p.nextRight = .var right)
    (hvalues : (seed.addEquality left right).classValues left =
      [first, second])
    (hmatch : DeclMatchSpec.MatchRel first second matched)
    (hlive : HELiveMergeCertified trace allowed
      (seed.addEquality left right) matched) :
    HELiveMergeSolutionCertified trace allowed
      (seed.addEquality left right) matched p.nextSubst := by
  let hexec := DeclMatchSpec.matchAtoms_complete hmatch
  let matchFuel := Classical.choose hexec
  have hmatchMem : matched ∈ matchAtoms first second matchFuel :=
    Classical.choose_spec hexec
  apply p.liveMergeWithHeadTheory hlive
  intro valuation
  constructor
  · rintro ⟨hcandidate, _hmatched⟩
    obtain ⟨hseed, hequality⟩ :=
      (heBindingSatisfied_addEquality_iff
        valuation seed left right).mp hcandidate
    refine ⟨hseed, ?_⟩
    rw [hright]
    simpa [MettaEquationSatisfied, toLeaTTaAtom,
      applyClassSolution] using hequality
  · rintro ⟨hseed, hhead⟩
    rw [hright] at hhead
    have hequality : valuation left = valuation right := by
      simpa [MettaEquationSatisfied, toLeaTTaAtom,
        applyClassSolution] using hhead
    have hcandidate : HEBindingSatisfied valuation
        (seed.addEquality left right) :=
      (heBindingSatisfied_addEquality_iff
        valuation seed left right).mpr ⟨hseed, hequality⟩
    have hfirst : first ∈
        (seed.addEquality left right).classValues left := by
      rw [hvalues]
      simp
    have hsecond : second ∈
        (seed.addEquality left right).classValues left := by
      rw [hvalues]
      simp
    have hinner :=
      classValues_equationSatisfied hcandidate hfirst hsecond
    exact ⟨hcandidate,
      (matchAtoms_solution_iff hmatchMem valuation).mpr hinner⟩

/-- Symmetric non-variable/variable form of
`assignmentConflictLiveMerge`.  The hidden matcher retains HE's runtime
orientation `first` against `value`, while the exposed original head reads
`value = $key`; equality symmetry is confined to this semantic adapter. -/
noncomputable def
    HEProjectedTailHeadResidualSolutionPackage.nonVarVarConflictLiveMerge
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    {s : HEProjectedCertifiedListResidualSolutionState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed}
    {value : Atom} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage s value leftRest)
    {key : String} {first : Atom} {rest : List Atom} {matched : Bindings}
    (hright : p.nextRight = .var key)
    (hclass : seed.classValues key = first :: rest)
    (hmatch : DeclMatchSpec.MatchRel first value matched)
    (hlive : HELiveMergeCertified trace allowed seed matched) :
    HELiveMergeSolutionCertified trace allowed seed matched p.nextSubst := by
  let hexec := DeclMatchSpec.matchAtoms_complete hmatch
  let matchFuel := Classical.choose hexec
  have hmatchMem : matched ∈ matchAtoms first value matchFuel :=
    Classical.choose_spec hexec
  apply p.liveMergeWithHeadTheory hlive
  intro valuation
  constructor
  · rintro ⟨hseed, hmatched⟩
    have hfirstMem : first ∈ seed.classValues key := by
      rw [hclass]
      simp
    have hstored :=
      hseed.eq_applyClassSolution_of_mem_classValues hfirstMem
    have hinner := (matchAtoms_solution_iff hmatchMem valuation).mp hmatched
    refine ⟨hseed, ?_⟩
    rw [hright]
    simpa [MettaEquationSatisfied, toLeaTTaAtom,
      applyClassSolution] using hinner.symm.trans hstored.symm
  · rintro ⟨hseed, hhead⟩
    have hfirstMem : first ∈ seed.classValues key := by
      rw [hclass]
      simp
    have hstored :=
      hseed.eq_applyClassSolution_of_mem_classValues hfirstMem
    rw [hright] at hhead
    have hheadEq :
        applyClassSolution valuation (toLeaTTaAtom value) =
          valuation key := by
      simpa [MettaEquationSatisfied, toLeaTTaAtom,
        applyClassSolution] using hhead
    have hinner : MettaEquationSatisfied valuation
        (toLeaTTaAtom first, toLeaTTaAtom value) := by
      simpa [MettaEquationSatisfied, toLeaTTaAtom,
        applyClassSolution] using hstored.symm.trans hheadEq.symm
    exact ⟨hseed, (matchAtoms_solution_iff hmatchMem valuation).mpr hinner⟩

/-- The final pair of HE's class-reconciliation list is the selected class
value against the proposed value.  Hence pointwise satisfaction of the
whole replicate/append presentation exposes that scalar equation. -/
theorem reconcileList_satisfied_implies_last
    (valuation : String → Metta.Atom)
    (first value : Atom) (rest : List Atom)
    (h : MettaAtomListsSatisfied valuation
      (toLeaTTaAtoms (List.replicate (rest.length + 1) first))
      (toLeaTTaAtoms (rest ++ [value]))) :
    applyClassSolution valuation (toLeaTTaAtom first) =
      applyClassSolution valuation (toLeaTTaAtom value) := by
  have hreplicate : ∀ n,
      toLeaTTaAtoms (List.replicate n first) =
        List.replicate n (toLeaTTaAtom first) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, ih]
  unfold MettaAtomListsSatisfied at h
  rw [hreplicate, toLeaTTaAtoms_append] at h
  simp only [toLeaTTaAtoms_cons, toLeaTTaAtoms_nil,
    List.map_replicate, List.map_append, List.map_cons,
    List.map_nil] at h
  have hlast := congrArg List.getLast? h
  simpa [List.getLast?_replicate] using hlast

/-- Class-wide assignment reconciliation has the same solution theory as
the exposed variable/non-variable head.  The full runtime list is used in
the reverse direction; only its final selected pair is needed forward. -/
noncomputable def
    HEProjectedTailHeadResidualSolutionPackage.assignmentReconcileLiveMerge
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    {s : HEProjectedCertifiedListResidualSolutionState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed}
    {key : String} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      s (.var key) leftRest)
    {value first : Atom} {rest : List Atom} {matched : Bindings}
    (hright : p.nextRight = value)
    (hclass : seed.classValues key = first :: rest)
    (hmatch : DeclMatchSpec.MatchListAccRel
      (List.replicate (rest.length + 1) first) (rest ++ [value])
      Bindings.empty matched)
    (hlive : HELiveMergeCertified trace allowed seed matched) :
    HELiveMergeSolutionCertified trace allowed seed matched p.nextSubst := by
  let hexpr : DeclMatchSpec.MatchRel
      (.expression (List.replicate (rest.length + 1) first))
      (.expression (rest ++ [value])) matched := .expr hmatch
  let hexec := DeclMatchSpec.matchAtoms_complete hexpr
  let matchFuel := Classical.choose hexec
  have hmatchMem : matched ∈
      matchAtoms
        (.expression (List.replicate (rest.length + 1) first))
        (.expression (rest ++ [value])) matchFuel :=
    Classical.choose_spec hexec
  apply p.liveMergeWithHeadTheory hlive
  intro valuation
  constructor
  · rintro ⟨hseed, hmatched⟩
    have hmatchedEquation :=
      (matchAtoms_solution_iff hmatchMem valuation).mp hmatched
    have hlists : MettaAtomListsSatisfied valuation
        (toLeaTTaAtoms (List.replicate (rest.length + 1) first))
        (toLeaTTaAtoms (rest ++ [value])) := by
      simpa [MettaEquationSatisfied, toLeaTTaAtom,
        applyClassSolution, MettaAtomListsSatisfied] using hmatchedEquation
    have hlast :=
      reconcileList_satisfied_implies_last valuation first value rest hlists
    have hfirstMem : first ∈ seed.classValues key := by
      rw [hclass]
      simp
    have hstored :=
      hseed.eq_applyClassSolution_of_mem_classValues hfirstMem
    refine ⟨hseed, ?_⟩
    rw [hright]
    simpa [MettaEquationSatisfied, toLeaTTaAtom,
      applyClassSolution] using hstored.trans hlast
  · rintro ⟨hseed, hhead⟩
    rw [hright] at hhead
    have hheadEq : valuation key =
        applyClassSolution valuation (toLeaTTaAtom value) := by
      simpa [MettaEquationSatisfied, toLeaTTaAtom,
        applyClassSolution] using hhead
    have hlists :=
      classValues_reconcileList_satisfied hseed hclass hheadEq
    have hmatchedEquation : MettaEquationSatisfied valuation
        (toLeaTTaAtom
            (.expression (List.replicate (rest.length + 1) first)),
          toLeaTTaAtom (.expression (rest ++ [value]))) := by
      simpa [MettaEquationSatisfied, toLeaTTaAtom,
        applyClassSolution, MettaAtomListsSatisfied] using hlists
    exact ⟨hseed,
      (matchAtoms_solution_iff hmatchMem valuation).mpr hmatchedEquation⟩

/-- Symmetric class-wide non-variable/variable reconciliation.  The hidden
runtime matcher keeps HE's stored-value/proposed-value orientation; equality
symmetry appears only when its solution theory is compared with the exposed
`value = $key` head. -/
noncomputable def
    HEProjectedTailHeadResidualSolutionPackage.nonVarVarReconcileLiveMerge
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    {s : HEProjectedCertifiedListResidualSolutionState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed}
    {value : Atom} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage s value leftRest)
    {key : String} {first : Atom} {rest : List Atom} {matched : Bindings}
    (hright : p.nextRight = .var key)
    (hclass : seed.classValues key = first :: rest)
    (hmatch : DeclMatchSpec.MatchListAccRel
      (List.replicate (rest.length + 1) first) (rest ++ [value])
      Bindings.empty matched)
    (hlive : HELiveMergeCertified trace allowed seed matched) :
    HELiveMergeSolutionCertified trace allowed seed matched p.nextSubst := by
  let hexpr : DeclMatchSpec.MatchRel
      (.expression (List.replicate (rest.length + 1) first))
      (.expression (rest ++ [value])) matched := .expr hmatch
  let hexec := DeclMatchSpec.matchAtoms_complete hexpr
  let matchFuel := Classical.choose hexec
  have hmatchMem : matched ∈
      matchAtoms
        (.expression (List.replicate (rest.length + 1) first))
        (.expression (rest ++ [value])) matchFuel :=
    Classical.choose_spec hexec
  apply p.liveMergeWithHeadTheory hlive
  intro valuation
  constructor
  · rintro ⟨hseed, hmatched⟩
    have hmatchedEquation :=
      (matchAtoms_solution_iff hmatchMem valuation).mp hmatched
    have hlists : MettaAtomListsSatisfied valuation
        (toLeaTTaAtoms (List.replicate (rest.length + 1) first))
        (toLeaTTaAtoms (rest ++ [value])) := by
      simpa [MettaEquationSatisfied, toLeaTTaAtom,
        applyClassSolution, MettaAtomListsSatisfied] using hmatchedEquation
    have hlast :=
      reconcileList_satisfied_implies_last valuation first value rest hlists
    have hfirstMem : first ∈ seed.classValues key := by
      rw [hclass]
      simp
    have hstored :=
      hseed.eq_applyClassSolution_of_mem_classValues hfirstMem
    refine ⟨hseed, ?_⟩
    rw [hright]
    simpa [MettaEquationSatisfied, toLeaTTaAtom,
      applyClassSolution] using hlast.symm.trans hstored.symm
  · rintro ⟨hseed, hhead⟩
    rw [hright] at hhead
    have hheadEq :
        applyClassSolution valuation (toLeaTTaAtom value) =
          valuation key := by
      simpa [MettaEquationSatisfied, toLeaTTaAtom,
        applyClassSolution] using hhead
    have hlists :=
      classValues_reconcileList_satisfied hseed hclass hheadEq.symm
    have hmatchedEquation : MettaEquationSatisfied valuation
        (toLeaTTaAtom
            (.expression (List.replicate (rest.length + 1) first)),
          toLeaTTaAtom (.expression (rest ++ [value]))) := by
      simpa [MettaEquationSatisfied, toLeaTTaAtom,
        applyClassSolution, MettaAtomListsSatisfied] using hlists
    exact ⟨hseed,
      (matchAtoms_solution_iff hmatchMem valuation).mpr hmatchedEquation⟩

/-- Whole joined-class equality reconciliation adds no solutions beyond the
candidate equality edge.  A satisfying candidate makes every stored class
value equal, so the runtime replicate/tail matcher is semantically redundant;
conversely the candidate alone already presents the exposed variable pair. -/
noncomputable def
    HEProjectedTailHeadResidualSolutionPackage.equalityClassConflictLiveMerge
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {leftAtoms rightAtoms : List Atom}
    {seed : Bindings}
    {s : HEProjectedCertifiedListResidualSolutionState trace allowed
      outerFuel front outerSubst fuel work subst result
        leftAtoms rightAtoms seed}
    {left : String} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      s (.var left) leftRest)
    {right : String} {first second third : Atom} {rest : List Atom}
    {matched : Bindings}
    (hright : p.nextRight = .var right)
    (hvalues : (seed.addEquality left right).classValues left =
      first :: second :: third :: rest)
    (hmatch : DeclMatchSpec.MatchListAccRel
      (List.replicate (rest.length + 2) first)
      (second :: third :: rest) Bindings.empty matched)
    (hlive : HELiveMergeCertified trace allowed
      (seed.addEquality left right) matched) :
    HELiveMergeSolutionCertified trace allowed
      (seed.addEquality left right) matched p.nextSubst := by
  let hexpr : DeclMatchSpec.MatchRel
      (.expression (List.replicate (rest.length + 2) first))
      (.expression (second :: third :: rest)) matched := .expr hmatch
  let hexec := DeclMatchSpec.matchAtoms_complete hexpr
  let matchFuel := Classical.choose hexec
  have hmatchMem : matched ∈
      matchAtoms
        (.expression (List.replicate (rest.length + 2) first))
        (.expression (second :: third :: rest)) matchFuel :=
    Classical.choose_spec hexec
  apply p.liveMergeWithHeadTheory hlive
  intro valuation
  constructor
  · rintro ⟨hcandidate, _hmatched⟩
    obtain ⟨hseed, hequality⟩ :=
      (heBindingSatisfied_addEquality_iff
        valuation seed left right).mp hcandidate
    refine ⟨hseed, ?_⟩
    rw [hright]
    simpa [MettaEquationSatisfied, toLeaTTaAtom,
      applyClassSolution] using hequality
  · rintro ⟨hseed, hhead⟩
    rw [hright] at hhead
    have hequality : valuation left = valuation right := by
      simpa [MettaEquationSatisfied, toLeaTTaAtom,
        applyClassSolution] using hhead
    have hcandidate : HEBindingSatisfied valuation
        (seed.addEquality left right) :=
      (heBindingSatisfied_addEquality_iff
        valuation seed left right).mpr ⟨hseed, hequality⟩
    have hlists := classValues_replicateTail_satisfied hcandidate hvalues
    have hmatchedEquation : MettaEquationSatisfied valuation
        (toLeaTTaAtom
            (.expression (List.replicate (rest.length + 2) first)),
          toLeaTTaAtom (.expression (second :: third :: rest))) := by
      simpa [MettaEquationSatisfied, toLeaTTaAtom, applyClassSolution,
        MettaAtomListsSatisfied, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hlists
    exact ⟨hcandidate,
      (matchAtoms_solution_iff hmatchMem valuation).mpr hmatchedEquation⟩

/-- Equality insertion changes no direct HE value.  Consequently the
class-indexed value relation is monotone under an added HE edge even when that
edge is intentionally absent from the relation list on the LeaTTa side.  This
is the weak structural fact needed by solved-alias intermediate states. -/
theorem LeaClassValueRelEquiv.addEquality_he
    {b : Bindings} {lb : Metta.Bindings}
    (h : LeaClassValueRelEquiv b lb) (left right : String) :
    LeaClassValueRelEquiv (b.addEquality left right) lb := by
  let hext : HEBindingObservationExtension b (b.addEquality left right) :=
    HEBindingObservationExtension.addEquality b left right
  constructor
  · intro key value hvalue
    have hold : (key, value) ∈ b.assignments := by
      simpa [Bindings.addEquality] using hvalue
    obtain ⟨leaKey, leaValue, hleaValue, hclass, hatom⟩ := h.1 key value hold
    exact ⟨leaKey, leaValue, hleaValue, hext.classes hclass,
      HELeaAtomClassRel.mono hext.classes hatom⟩
  · intro leaKey leaValue hleaValue
    obtain ⟨key, value, hvalue, hclass, hatom⟩ := h.2 leaKey leaValue hleaValue
    exact ⟨key, value, hext.assignments key value hvalue,
      hext.classes hclass, HELeaAtomClassRel.mono hext.classes hatom⟩

/-- Class-value correspondence alone is the exact input needed to recover
ambient Robinson assignment provenance from a reached substitution.  Equality
closure agreement is deliberately absent: a solved explicit alias may extend
the HE class graph while leaving the normalized substitution unchanged. -/
theorem LeaClassValueRelEquiv.assignmentsSound_of_ofSubst_subset
    {b : Bindings} {subst : Metta.Subst}
    (h : LeaClassValueRelEquiv b (Metta.Bindings.ofSubst subst))
    {trace : List (String × Metta.Atom)}
    (hsubset : ∀ entry ∈ subst, entry ∈ trace) :
    LeaEliminationTraceAssignmentsSound b trace := by
  intro heKey heValue hassignment
  obtain ⟨key, value, hvalue, hclass, hatom⟩ :=
    h.1 heKey heValue hassignment
  obtain ⟨hsubst, hnonvar⟩ := val_mem_ofSubst_iff.mp hvalue
  exact ⟨key, value, hsubset (key, value) hsubst,
    hnonvar, hclass, hatom⟩

/-- Substitution provenance is stable under a live HE equality insertion.
The operation changes no assignment payload, while every class-relative
witness remains valid in the enlarged equality closure. -/
theorem LeaSubstClassValueRel.addEquality_he
    {b : Bindings} {subst : Metta.Subst}
    (h : LeaSubstClassValueRel b subst) (left right : String) :
    LeaSubstClassValueRel (b.addEquality left right) subst := by
  apply leaClassValueRelEquiv_ofSubst_iff_substClassValueRel.mp
  exact (leaClassValueRelEquiv_ofSubst_iff_substClassValueRel.mpr h).addEquality_he
    left right

/-- A non-variable entry present in a substitution-provenance certificate is
already an observable HE trace value.  No equality-closure agreement with the
raw substitution is needed for this direction. -/
theorem LeaSubstClassValueRel.traceEntryRealized_of_nonvar
    {b : Bindings} {subst : Metta.Subst}
    (h : LeaSubstClassValueRel b subst)
    {key : String} {value : Metta.Atom}
    (hentry : (key, value) ∈ subst)
    (hnonvar : ∀ target, value ≠ .var target) :
    LeaEliminationTraceEntryRealized b (key, value) := by
  cases value with
  | var target => exact (hnonvar target rfl).elim
  | sym symbol | gnd symbol | expr symbol =>
      exact h.2 key _ hentry (by intro target hfalse; cases hfalse)

/-- Translation preserves the variable/non-variable distinction used by the
HE matcher. -/
theorem toLeaTTaAtom_ne_var_of_isVarB_false
    {value : Atom}
    (hnonvar : DeclMatchSpec.Atom.isVarB value = false)
    (target : String) :
    toLeaTTaAtom value ≠ .var target := by
  cases value <;>
    simp [DeclMatchSpec.Atom.isVarB, toLeaTTaAtom] at hnonvar ⊢

/-- Successful association-list lookup exposes the corresponding stored
assignment. -/
theorem assignment_mem_of_lookup_eq_some_public
    {assignments : List (String × Atom)} {key : String} {value : Atom}
    (hlookup : List.lookup key assignments = some value) :
    (key, value) ∈ assignments := by
  induction assignments with
  | nil => simp at hlookup
  | cons binding assignments ih =>
      rcases binding with ⟨storedKey, storedValue⟩
      by_cases hkey : key = storedKey
      · subst storedKey
        simp at hlookup
        subst storedValue
        simp
      · have hbeq : (key == storedKey) = false := by simp [hkey]
        simp only [List.lookup_cons, hbeq] at hlookup
        exact List.mem_cons_of_mem _ (ih hlookup)

/-- Compatibility specialization for the former bundled structural carrier. -/
theorem LeaBindingStructuralCongruence.assignmentsSound_of_ofSubst_subset
    {b : Bindings} {subst : Metta.Subst}
    (h : LeaBindingStructuralCongruence b
      (Metta.Bindings.ofSubst subst))
    {trace : List (String × Metta.Atom)}
    (hsubset : ∀ entry ∈ subst, entry ∈ trace) :
    LeaEliminationTraceAssignmentsSound b trace :=
  h.classValues.assignmentsSound_of_ofSubst_subset hsubset

/-- Structural congruence with repaired LeaTTa's `ofSubst` presentation
already bounds every HE equality-class connection by the substitution's
undirected alias graph.  The proof compares closures only; it does not expose
edge order, orientation, or representative choice. -/
theorem LeaBindingStructuralCongruence.equalityClosureBound_of_ofSubst
    {b : Bindings} {subst : Metta.Subst}
    (h : LeaBindingStructuralCongruence b
      (Metta.Bindings.ofSubst subst)) :
    HEEqualityClosureBound b (eliminationTraceAliases subst) := by
  intro start finish hclass
  have hleaClass := (h.classes start finish).mp hclass
  rw [mem_leaEqClass_iff_reachable,
    leaEqualityEdges_ofSubst_eq_eliminationTraceAliases] at hleaClass
  exact hleaClass

/-- The substitution reached after one exposed projected head is a literal
subsequence of the ambient successful solve trace.  This is the reusable
provenance fact needed to turn structural class-value correspondence at the
post-state into `LeaEliminationTraceAssignmentsSound`. -/
theorem HEProjectedTailHeadResidualSolutionPackage.nextSubst_subset_trace
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    {s : HEProjectedCertifiedListResidualSolutionState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed}
    {nextLeft : Atom} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage s nextLeft leftRest) :
    ∀ entry ∈ p.nextSubst, entry ∈ trace := by
  have hcurrentFresh : UnifyStateFresh work subst :=
    s.projection.stateFresh s.outerStateFresh
  have hheadFresh : UnifyStateFresh p.headWork subst := by
    intro key hkey hmem
    exact hcurrentFresh key hkey (by
      rw [p.work_eq]
      simp only [mettaEquationVars, List.flatMap_append,
        List.mem_append]
      exact Or.inl hmem)
  have hcurrentTraceEq :
      unificationEliminationTrace fuel work =
        unificationEliminationTrace fuel p.headWork ++
          unificationEliminationTrace p.nextRemainingFuel
            p.nextTailWork := by
    exact (congrArg (unificationEliminationTrace fuel) p.work_eq).trans
      p.nextSplit.trace_append
  have hheadTraceSubset : ∀ entry ∈
      unificationEliminationTrace fuel p.headWork,
      entry ∈ trace := by
    intro entry hentry
    apply s.localTrace_subset entry
    rw [hcurrentTraceEq]
    exact List.mem_append_left _ hentry
  have hsubstSubset : ∀ entry ∈ subst, entry ∈ trace := by
    have hresultEq :=
      unifyRounds_result_eq_eliminationTrace_reverse_append
        hcurrentFresh s.run
    intro entry hentry
    apply s.result_subset_trace entry
    rw [hresultEq]
    exact List.mem_append_right _ hentry
  have hnextEq :=
    unifyRounds_result_eq_eliminationTrace_reverse_append
      hheadFresh p.nextSplit.front_run
  intro entry hentry
  rw [hnextEq] at hentry
  rcases List.mem_append.mp hentry with htrace | hsubst
  · apply hheadTraceSubset entry
    simpa only [List.mem_reverse] using htrace
  · exact hsubstSubset entry hsubst

/-! ## Class-value lift of hidden live conflicts

The hidden matcher boundary intentionally omits standalone trace provenance
for the child result.  The recursive invariant needed at that boundary is
class-indexed value provenance for the accumulator reached after the actual
external merge.  Full equality-closure agreement with the raw substitution is
strictly stronger: a solved explicit alias can enlarge the HE class graph while
disappearing from the normalized substitution. -/

/-- Atom hidden conflict together with the class-value part of its reached
post-state correspondence.  Solution theory and derivation-local certificates
remain in `operational`; no equality-list presentation is compared. -/
structure HELiveHiddenMatchValueCertified
    (trace : List (String × Metta.Atom))
    (allowed : List (String × String))
    (left right : Atom) (seed : Bindings) (subst : Metta.Subst) where
  operational : HELiveHiddenMatchResidualCertified
    trace allowed left right seed subst
  classValues : LeaSubstClassValueRel operational.liveMerge.after subst

/-- Pointwise-list companion of `HELiveHiddenMatchValueCertified`. -/
structure HELiveHiddenListMatchValueCertified
    (trace : List (String × Metta.Atom))
    (allowed : List (String × String))
    (left right : List Atom) (seed : Bindings) (subst : Metta.Subst) where
  operational : HELiveHiddenListMatchResidualCertified
    trace allowed left right seed subst
  classValues : LeaSubstClassValueRel operational.liveMerge.after subst

/-- Hidden atom value provenance is independent of the ambient trace and
equality carrier; only the operational certificates require transport. -/
def HELiveHiddenMatchValueCertified.mono
    {smallTrace largeTrace : List (String × Metta.Atom)}
    {smallAllowed largeAllowed : List (String × String)}
    {left right : Atom} {seed : Bindings} {subst : Metta.Subst}
    (h : HELiveHiddenMatchValueCertified
      smallTrace smallAllowed left right seed subst)
    (htrace : ∀ entry ∈ smallTrace, entry ∈ largeTrace)
    (hallowed : ∀ {start finish : String},
      (EqualityClosure.edgeGraph smallAllowed).Reachable start finish →
        (EqualityClosure.edgeGraph largeAllowed).Reachable start finish) :
    HELiveHiddenMatchValueCertified
      largeTrace largeAllowed left right seed subst := {
  operational := h.operational.mono htrace hallowed
  classValues := h.classValues
}

/-- Pointwise-list hidden value provenance has the same transport law. -/
def HELiveHiddenListMatchValueCertified.mono
    {smallTrace largeTrace : List (String × Metta.Atom)}
    {smallAllowed largeAllowed : List (String × String)}
    {left right : List Atom} {seed : Bindings} {subst : Metta.Subst}
    (h : HELiveHiddenListMatchValueCertified
      smallTrace smallAllowed left right seed subst)
    (htrace : ∀ entry ∈ smallTrace, entry ∈ largeTrace)
    (hallowed : ∀ {start finish : String},
      (EqualityClosure.edgeGraph smallAllowed).Reachable start finish →
        (EqualityClosure.edgeGraph largeAllowed).Reachable start finish) :
    HELiveHiddenListMatchValueCertified
      largeTrace largeAllowed left right seed subst := {
  operational := h.operational.mono htrace hallowed
  classValues := h.classValues
}

/-- A selected non-variable substitution entry is realized in the reached
hidden atom accumulator. -/
theorem HELiveHiddenMatchValueCertified.traceEntryRealized_of_nonvar
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {left right : Atom} {seed : Bindings} {subst : Metta.Subst}
    (h : HELiveHiddenMatchValueCertified
      trace allowed left right seed subst)
    {key : String} {value : Metta.Atom}
    (hentry : (key, value) ∈ subst)
    (hnonvar : ∀ target, value ≠ .var target) :
    LeaEliminationTraceEntryRealized h.operational.liveMerge.after
      (key, value) :=
  h.classValues.traceEntryRealized_of_nonvar hentry hnonvar

/-- List counterpart of selected non-variable realization. -/
theorem HELiveHiddenListMatchValueCertified.traceEntryRealized_of_nonvar
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {left right : List Atom} {seed : Bindings} {subst : Metta.Subst}
    (h : HELiveHiddenListMatchValueCertified
      trace allowed left right seed subst)
    {key : String} {value : Metta.Atom}
    (hentry : (key, value) ∈ subst)
    (hnonvar : ∀ target, value ≠ .var target) :
    LeaEliminationTraceEntryRealized h.operational.liveMerge.after
      (key, value) :=
  h.classValues.traceEntryRealized_of_nonvar hentry hnonvar

/-- Any obligation already realized by the live seed remains realized after
the hidden atom merge. -/
theorem HELiveHiddenMatchValueCertified.traceEntryRealized_of_seed
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {left right : Atom} {seed : Bindings} {subst : Metta.Subst}
    (h : HELiveHiddenMatchValueCertified
      trace allowed left right seed subst)
    {entry : String × Metta.Atom}
    (hseed : LeaEliminationTraceEntryRealized seed entry) :
    LeaEliminationTraceEntryRealized h.operational.liveMerge.after entry :=
  hseed.mono (mergeBindings_observationExtension
    h.operational.liveMerge.merge_mem)

/-- Pointwise-list counterpart of preservation from the live seed. -/
theorem HELiveHiddenListMatchValueCertified.traceEntryRealized_of_seed
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {left right : List Atom} {seed : Bindings} {subst : Metta.Subst}
    (h : HELiveHiddenListMatchValueCertified
      trace allowed left right seed subst)
    {entry : String × Metta.Atom}
    (hseed : LeaEliminationTraceEntryRealized seed entry) :
    LeaEliminationTraceEntryRealized h.operational.liveMerge.after entry :=
  hseed.mono (mergeBindings_observationExtension
    h.operational.liveMerge.merge_mem)

/-- Exact local hidden atom result together with the selected substitution
entry and its inclusion in the ambient solve trace.  Class-value provenance,
rather than raw equality-closure agreement, is the recursive invariant. -/
structure HELiveHiddenMatchValueProgressCertified
    (trace : List (String × Metta.Atom))
    (allowed : List (String × String))
    (left right : Atom) (seed : Bindings)
    (entry : String × Metta.Atom) where
  subst : Metta.Subst
  live : HELiveHiddenMatchValueCertified
    trace allowed left right seed subst
  entry_mem : entry ∈ subst
  subst_subset_trace : ∀ localEntry ∈ subst, localEntry ∈ trace

/-- Pointwise-list counterpart of the weak hidden progress package. -/
structure HELiveHiddenListMatchValueProgressCertified
    (trace : List (String × Metta.Atom))
    (allowed : List (String × String))
    (left right : List Atom) (seed : Bindings)
    (entry : String × Metta.Atom) where
  subst : Metta.Subst
  live : HELiveHiddenListMatchValueCertified
    trace allowed left right seed subst
  entry_mem : entry ∈ subst
  subst_subset_trace : ∀ localEntry ∈ subst, localEntry ∈ trace

/-- A non-variable selected entry is realized by a weak hidden atom result. -/
theorem HELiveHiddenMatchValueProgressCertified.realized_of_nonvar
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {left right : Atom} {seed : Bindings}
    {key : String} {value : Metta.Atom}
    (h : HELiveHiddenMatchValueProgressCertified
      trace allowed left right seed (key, value))
    (hnonvar : ∀ target, value ≠ .var target) :
    LeaEliminationTraceEntryRealized
      h.live.operational.liveMerge.after (key, value) :=
  h.live.traceEntryRealized_of_nonvar h.entry_mem hnonvar

/-- Pointwise-list counterpart of non-variable realization. -/
theorem HELiveHiddenListMatchValueProgressCertified.realized_of_nonvar
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {left right : List Atom} {seed : Bindings}
    {key : String} {value : Metta.Atom}
    (h : HELiveHiddenListMatchValueProgressCertified
      trace allowed left right seed (key, value))
    (hnonvar : ∀ target, value ≠ .var target) :
    LeaEliminationTraceEntryRealized
      h.live.operational.liveMerge.after (key, value) :=
  h.live.traceEntryRealized_of_nonvar h.entry_mem hnonvar

/-- An entry already realized by the live atom seed remains realized in a
weak hidden progress result. -/
theorem HELiveHiddenMatchValueProgressCertified.realized_of_seed
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {left right : Atom} {seed : Bindings}
    {entry : String × Metta.Atom}
    (h : HELiveHiddenMatchValueProgressCertified
      trace allowed left right seed entry)
    (hseed : LeaEliminationTraceEntryRealized seed entry) :
    LeaEliminationTraceEntryRealized
      h.live.operational.liveMerge.after entry :=
  h.live.traceEntryRealized_of_seed hseed

/-- Pointwise-list counterpart of seed-realization preservation. -/
theorem HELiveHiddenListMatchValueProgressCertified.realized_of_seed
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {left right : List Atom} {seed : Bindings}
    {entry : String × Metta.Atom}
    (h : HELiveHiddenListMatchValueProgressCertified
      trace allowed left right seed entry)
    (hseed : LeaEliminationTraceEntryRealized seed entry) :
    LeaEliminationTraceEntryRealized
      h.live.operational.liveMerge.after entry :=
  h.live.traceEntryRealized_of_seed hseed

/-! ## Compatibility structural lift of hidden live conflicts

The stronger packages below remain useful in branches where complete
structural congruence is independently available.  They are not the general
recursive invariant: explicit solved aliases make that stronger claim false
against a raw normalized substitution. -/

/-- Atom hidden conflict together with the structural part of its reached
post-state congruence. -/
structure HELiveHiddenMatchStructuralCertified
    (trace : List (String × Metta.Atom))
    (allowed : List (String × String))
    (left right : Atom) (seed : Bindings) (subst : Metta.Subst) where
  operational : HELiveHiddenMatchResidualCertified
    trace allowed left right seed subst
  structural : LeaBindingStructuralCongruence
    operational.liveMerge.after (Metta.Bindings.ofSubst subst)

/-- Pointwise-list hidden conflict with the same post-state-only structural
certificate. -/
structure HELiveHiddenListMatchStructuralCertified
    (trace : List (String × Metta.Atom))
    (allowed : List (String × String))
    (left right : List Atom) (seed : Bindings) (subst : Metta.Subst) where
  operational : HELiveHiddenListMatchResidualCertified
    trace allowed left right seed subst
  structural : LeaBindingStructuralCongruence
    operational.liveMerge.after (Metta.Bindings.ofSubst subst)

/-- Structural hidden atom conflicts inherit ambient certificate transport;
the post-state correspondence itself is independent of either carrier. -/
def HELiveHiddenMatchStructuralCertified.mono
    {smallTrace largeTrace : List (String × Metta.Atom)}
    {smallAllowed largeAllowed : List (String × String)}
    {left right : Atom} {seed : Bindings} {subst : Metta.Subst}
    (h : HELiveHiddenMatchStructuralCertified
      smallTrace smallAllowed left right seed subst)
    (htrace : ∀ entry ∈ smallTrace, entry ∈ largeTrace)
    (hallowed : ∀ {start finish : String},
      (EqualityClosure.edgeGraph smallAllowed).Reachable start finish →
        (EqualityClosure.edgeGraph largeAllowed).Reachable start finish) :
    HELiveHiddenMatchStructuralCertified
      largeTrace largeAllowed left right seed subst := {
  operational := h.operational.mono htrace hallowed
  structural := h.structural
}

/-- Pointwise-list structural hidden transport. -/
def HELiveHiddenListMatchStructuralCertified.mono
    {smallTrace largeTrace : List (String × Metta.Atom)}
    {smallAllowed largeAllowed : List (String × String)}
    {left right : List Atom} {seed : Bindings} {subst : Metta.Subst}
    (h : HELiveHiddenListMatchStructuralCertified
      smallTrace smallAllowed left right seed subst)
    (htrace : ∀ entry ∈ smallTrace, entry ∈ largeTrace)
    (hallowed : ∀ {start finish : String},
      (EqualityClosure.edgeGraph smallAllowed).Reachable start finish →
        (EqualityClosure.edgeGraph largeAllowed).Reachable start finish) :
    HELiveHiddenListMatchStructuralCertified
      largeTrace largeAllowed left right seed subst := {
  operational := h.operational.mono htrace hallowed
  structural := h.structural
}

/-- Embed a structurally solved hidden atom conflict from one exact local
expression frontier into an ambient reconciliation carrier.  Original
constraint coverage and normalized residual inclusion are the only bridge;
the local matcher and reached accumulator are not reconstructed. -/
def HEExpressionResidualFrontier.embedHiddenStructural_of_covered
    {trace : List (String × Metta.Atom)}
    {fuel : Nat} {left right : List Atom} {result : Metta.Subst}
    (h : HEExpressionResidualFrontier fuel left right result)
    {atomLeft atomRight : Atom} {seed : Bindings} {subst : Metta.Subst}
    (inner : HELiveHiddenMatchStructuralCertified
      h.certificateTrace h.certificateAllowed
      atomLeft atomRight seed subst)
    (hcoverage : HEOriginalListConstraintCoverage trace left right)
    (hresidual : ∀ entry ∈ h.residualTrace, entry ∈ trace) :
    HELiveHiddenMatchStructuralCertified trace
      (eliminationTraceAliases trace) atomLeft atomRight seed subst := by
  obtain ⟨htrace, hallowed⟩ :=
    h.certificate_embeds_of_covered hcoverage hresidual
  exact inner.mono htrace hallowed

/-- Pointwise-list form of local-frontier hidden structural embedding. -/
def HEExpressionResidualFrontier.embedHiddenListStructural_of_covered
    {trace : List (String × Metta.Atom)}
    {fuel : Nat} {left right : List Atom} {result : Metta.Subst}
    (h : HEExpressionResidualFrontier fuel left right result)
    {innerLeft innerRight : List Atom} {seed : Bindings}
    {subst : Metta.Subst}
    (inner : HELiveHiddenListMatchStructuralCertified
      h.certificateTrace h.certificateAllowed
      innerLeft innerRight seed subst)
    (hcoverage : HEOriginalListConstraintCoverage trace left right)
    (hresidual : ∀ entry ∈ h.residualTrace, entry ∈ trace) :
    HELiveHiddenListMatchStructuralCertified trace
      (eliminationTraceAliases trace) innerLeft innerRight seed subst := by
  obtain ⟨htrace, hallowed⟩ :=
    h.certificate_embeds_of_covered hcoverage hresidual
  exact inner.mono htrace hallowed

/-- The semantic field of a hidden atom post-state is independent of its
structural certificate. -/
def HELiveHiddenMatchStructuralCertified.congruence
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {left right : Atom}
    {seed : Bindings} {subst : Metta.Subst}
    (h : HELiveHiddenMatchStructuralCertified
      trace allowed left right seed subst) :
    LeaBindingCongruence h.operational.liveMerge.after
      (Metta.Bindings.ofSubst subst) :=
  h.structural.withSolutions h.operational.liveMerge.solutions

/-- List form of `HELiveHiddenMatchStructuralCertified.congruence`. -/
def HELiveHiddenListMatchStructuralCertified.congruence
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {left right : List Atom}
    {seed : Bindings} {subst : Metta.Subst}
    (h : HELiveHiddenListMatchStructuralCertified
      trace allowed left right seed subst) :
    LeaBindingCongruence h.operational.liveMerge.after
      (Metta.Bindings.ofSubst subst) :=
  h.structural.withSolutions h.operational.liveMerge.solutions

/-- Attach the structural post-state invariant to a full atom residual
package.  The already-proved solution characterization supplies the only
extensional field of the resulting congruence. -/
def HELiveMatchMergeCoreResidualCertified.toCoreCongruent_of_structural
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {left right : Atom}
    {seed : Bindings} {subst : Metta.Subst}
    (h : HELiveMatchMergeCoreResidualCertified
      trace allowed left right seed subst)
    (hstruct : LeaBindingStructuralCongruence
      h.liveMerge.after (Metta.Bindings.ofSubst subst)) :
    HELiveMatchMergeCoreCongruentCertified
      trace allowed left right seed subst := {
  toHELiveMatchMergeCoreCertified := h.toHELiveMatchMergeCoreCertified
  congruence := hstruct.withSolutions h.solutions
}

/-- A structurally solved hidden atom post-state also carries the exact
equality-closure upper bound of its target substitution. -/
theorem HELiveHiddenMatchStructuralCertified.equalityClosureBound
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {left right : Atom}
    {seed : Bindings} {subst : Metta.Subst}
    (h : HELiveHiddenMatchStructuralCertified
      trace allowed left right seed subst) :
    HEEqualityClosureBound h.operational.liveMerge.after
      (eliminationTraceAliases subst) :=
  h.structural.equalityClosureBound_of_ofSubst

/-- List form of the structural post-state equality bound. -/
theorem HELiveHiddenListMatchStructuralCertified.equalityClosureBound
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {left right : List Atom}
    {seed : Bindings} {subst : Metta.Subst}
    (h : HELiveHiddenListMatchStructuralCertified
      trace allowed left right seed subst) :
    HEEqualityClosureBound h.operational.liveMerge.after
      (eliminationTraceAliases subst) :=
  h.structural.equalityClosureBound_of_ofSubst

/-- Reindex only the displayed right atom of a congruent core head. -/
def HELiveMatchMergeCoreCongruentCertified.reindexRight
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {left right right' : Atom}
    {seed : Bindings} {subst : Metta.Subst}
    (h : HELiveMatchMergeCoreCongruentCertified
      trace allowed left right seed subst)
    (hright : right = right') :
    HELiveMatchMergeCoreCongruentCertified
      trace allowed left right' seed subst := by
  cases hright
  exact h

/-- A solved no-change variable/non-variable head preserves the exact strong
projected-state congruence.  The executable merge still traverses its
singleton assignment record; only the post-state observation is unchanged. -/
theorem HEProjectedTailHeadResidualPackage.exists_coreLiveVarNonVar_same_congruent
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    {s : HEProjectedCertifiedListResidualState trace allowed outerFuel
      front outerSubst fuel work subst result left right seed}
    {key : String} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualPackage s (.var key) leftRest)
    {value first : Atom} {rest : List Atom}
    (hright : p.nextRight = value)
    (hnonvar : DeclMatchSpec.Atom.isVarB value = false)
    (hclass : seed.classValues key = first :: rest)
    (hconsistent : Bindings.valuesConsistent (first :: rest) = true)
    (hsame : first = value)
    (hsolved : Metta.Unify.decomposeAll p.headWork = some []) :
    Nonempty (HELiveMatchMergeCoreCongruentCertified trace allowed
      (.var key) p.nextRight seed p.nextSubst) := by
  have hnext := p.nextSubst_eq_of_headWorkDecompose_nil hsolved
  obtain ⟨hmerge⟩ :=
    HELiveMergeCongruentCertified.exists_sameAssignment
      (trace := trace) (allowed := allowed) s.seed_congruence
      hclass hconsistent hsame (congrArg Metta.Bindings.ofSubst hnext)
  let hcore : HELiveMatchMergeCoreCongruentCertified trace allowed
      (.var key) value seed p.nextSubst := {
    toHELiveMatchMergeCoreCertified :=
      hmerge.toSolutionCertified.toHELiveMergeCertified
        |>.withCoreVarNonVarMatch hnonvar
    congruence := hmerge.congruence
  }
  exact ⟨by simpa only [hright] using hcore⟩

/-- Symmetric solved no-change assignment head at the same strong boundary. -/
theorem HEProjectedTailHeadResidualPackage.exists_coreLiveNonVarVar_same_congruent
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    {s : HEProjectedCertifiedListResidualState trace allowed outerFuel
      front outerSubst fuel work subst result left right seed}
    {value : Atom} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualPackage s value leftRest)
    {key : String} {first : Atom} {rest : List Atom}
    (hright : p.nextRight = .var key)
    (hnonvar : DeclMatchSpec.Atom.isVarB value = false)
    (hclass : seed.classValues key = first :: rest)
    (hconsistent : Bindings.valuesConsistent (first :: rest) = true)
    (hsame : first = value)
    (hsolved : Metta.Unify.decomposeAll p.headWork = some []) :
    Nonempty (HELiveMatchMergeCoreCongruentCertified trace allowed
      value p.nextRight seed p.nextSubst) := by
  have hnext := p.nextSubst_eq_of_headWorkDecompose_nil hsolved
  obtain ⟨hmerge⟩ :=
    HELiveMergeCongruentCertified.exists_sameAssignment
      (trace := trace) (allowed := allowed) s.seed_congruence
      hclass hconsistent hsame (congrArg Metta.Bindings.ofSubst hnext)
  let hcore : HELiveMatchMergeCoreCongruentCertified trace allowed
      value (.var key) seed p.nextSubst := {
    toHELiveMatchMergeCoreCertified :=
      hmerge.toSolutionCertified.toHELiveMergeCertified
        |>.withCoreNonVarVarMatch hnonvar
    congruence := hmerge.congruence
  }
  exact ⟨by simpa only [hright] using hcore⟩

/-- A congruent first head supplies the residual assignment certificate
required by the weak projected transport.  The reached substitution is
already embedded in the ambient trace by the stored prefix split. -/
def HEProjectedTailHeadResidualSolutionPackage.coreResidualOfCoreCongruent
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    {s : HEProjectedCertifiedListResidualSolutionState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed}
    {nextLeft : Atom} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage s nextLeft leftRest)
    (hhead : HELiveMatchMergeCoreCongruentCertified trace allowed
      nextLeft p.nextRight seed p.nextSubst) :
    HELiveMatchMergeCoreResidualCertified trace allowed
      nextLeft p.nextRight seed p.nextSubst := {
  toHELiveMatchMergeCoreSolutionCertified := {
    toHELiveMatchMergeCoreCertified :=
      hhead.toHELiveMatchMergeCoreCertified
    solutions := hhead.congruence.semantic.solutions
  }
  afterAssignmentsSound :=
    hhead.congruence.structural.assignmentsSound_of_ofSubst_subset
      p.nextSubst_subset_trace
}

/-- Bootstrap the strong residual invariant after the first exposed head.
The incoming projected state needs only solution equivalence; exact
post-merge congruence for that head supplies the stronger seed presentation
required by the existing sibling fold.  All trace and equality certificates
are inherited from the concrete weak tail handoff. -/
def HEProjectedTailHeadResidualSolutionPackage.toCertifiedStrongTailStateCore
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    {s : HEProjectedCertifiedListResidualSolutionState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed}
    {nextLeft : Atom} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage s nextLeft leftRest)
    (hhead : HELiveMatchMergeCoreCongruentCertified trace allowed
      nextLeft p.nextRight seed p.nextSubst) :
    HECertifiedListResidualState trace allowed
      p.nextRemainingFuel p.nextTailWork p.nextSubst result
      leftRest p.rightRest hhead.liveMerge.after := by
  let hresidual := p.coreResidualOfCoreCongruent hhead
  let weak := p.toCertifiedTailResidualStateCore hresidual
  exact {
    run := weak.run
    work_inHEImage := weak.work_inHEImage
    subst_inHEImage := weak.subst_inHEImage
    seed_congruence := hhead.congruence
    length_eq := weak.length_eq
    work_nil_of_left_nil := weak.work_nil_of_left_nil
    solutionTheory := weak.solutionTheory
    localTrace_subset := weak.localTrace_subset
    localAllowed_mono := weak.localAllowed_mono
    result_subset_trace := weak.result_subset_trace
    seed_assignmentsSound := weak.seed_assignmentsSound
    seed_equalityBound := weak.seed_equalityBound
  }

/-- Projected form of the first-head bootstrap.  It preserves the exact
original-prefix split while upgrading only the reached seed from solution
equivalence to full binding congruence. -/
def HEProjectedTailHeadResidualSolutionPackage.toProjectedStrongTailStateCore
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    {s : HEProjectedCertifiedListResidualSolutionState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed}
    {nextLeft : Atom} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage s nextLeft leftRest)
    (hhead : HELiveMatchMergeCoreCongruentCertified trace allowed
      nextLeft p.nextRight seed p.nextSubst) :
    HEProjectedCertifiedListResidualState trace allowed outerFuel
      (front ++ [(toLeaTTaAtom nextLeft,
        toLeaTTaAtom p.nextRight)]) outerSubst
      p.nextRemainingFuel p.nextTailWork p.nextSubst result
      leftRest p.rightRest hhead.liveMerge.after := by
  let hresidual := p.coreResidualOfCoreCongruent hhead
  let weak := p.toProjectedTailStateCore hresidual
  exact {
    toHECertifiedListResidualState :=
      p.toCertifiedStrongTailStateCore hhead
    projection := weak.projection
    front_inHEImage := weak.front_inHEImage
    outerSubst_inHEImage := weak.outerSubst_inHEImage
    outerStateFresh := weak.outerStateFresh
    front_decomposes := weak.front_decomposes
  }

/-- Strong sibling fold with the raw original-constraint carrier retained.
The live accumulator is already congruent at entry, so the nil branch is
genuine and every later head may be selected through the weak covered view
without losing the stronger seed invariant. -/
theorem HEProjectedCertifiedListResidualState.exists_matchListAccCongruent_of_coveredCoreLiveHead
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    (headBuilder : ∀
      {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
      {outerSubst : Metta.Subst}
      {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
      {subst result : Metta.Subst} {left right : List Atom}
      {seed : Bindings}
      (covered : HEOriginalConstraintCoveredProjectedListState trace allowed
        outerFuel front outerSubst fuel work subst result left right seed)
      {nextLeft : Atom} {leftRest : List Atom}
      (head : HEProjectedTailHeadResidualSolutionPackage
        covered.state nextLeft leftRest),
      Nonempty (HELiveMatchMergeCoreCongruentCertified trace allowed
        nextLeft head.nextRight seed head.nextSubst)) :
    ∀ {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
      {outerSubst : Metta.Subst}
      {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
      {subst result : Metta.Subst} {left right : List Atom}
      {seed : Bindings},
      (state : HEProjectedCertifiedListResidualState trace allowed
        outerFuel front outerSubst fuel work subst result left right seed) →
      HEOriginalListConstraintCoverage trace left right →
      Nonempty (HEMatchListAccCongruentCertified trace allowed
        left right seed result) := by
  intro outerFuel front outerSubst fuel work subst result left
  induction left generalizing outerFuel front outerSubst fuel work subst
      result with
  | nil =>
      intro right seed state _coverage
      exact state.exists_nilMatch rfl
  | cons nextLeft leftRest ih =>
      intro right seed state hcoverage
      let covered : HEOriginalConstraintCoveredProjectedListState trace allowed
          outerFuel front outerSubst fuel work subst result
          (nextLeft :: leftRest) right seed := {
        state := state.toSolutionState
        originalCoverage := hcoverage
      }
      obtain ⟨strongHead⟩ :=
        state.exists_tailHeadResidualPackage
          (nextLeft := nextLeft) (leftRest := leftRest) rfl
      let head := strongHead.toSolutionPackage
      obtain ⟨headLive⟩ := headBuilder covered head
      let residual := head.coreResidualOfCoreCongruent headLive
      let weakTail := head.toCoveredProjectedTailStateCore covered residual
      let tailState := head.toProjectedStrongTailStateCore headLive
      obtain ⟨tailMatch⟩ := ih tailState weakTail.originalCoverage
      exact ⟨{
        out := tailMatch.out
        matchRel := by
          simpa only [HELiveMatchMergeCoreCertified.cons,
            head.right_eq] using
            (headLive.toHELiveMatchMergeCoreCertified.cons
              tailMatch.toHEMatchListAccCertified).matchRel
        traceSound := by
          simpa only [HELiveMatchMergeCoreCertified.cons,
            head.right_eq] using
            (headLive.toHELiveMatchMergeCoreCertified.cons
              tailMatch.toHEMatchListAccCertified).traceSound
        equalitySound := by
          simpa only [HELiveMatchMergeCoreCertified.cons,
            head.right_eq] using
            (headLive.toHELiveMatchMergeCoreCertified.cons
              tailMatch.toHEMatchListAccCertified).equalitySound
        congruence := tailMatch.congruence
      }⟩

/-- Strong-state sibling fold that does not erase the incoming accumulator
congruence before invoking the head builder.  Original-constraint coverage is
passed separately, while the builder receives the exact strong projected
state and its strong head package.  This is the induction-facing form used
after the first divergence has bootstrapped structural congruence. -/
theorem HEProjectedCertifiedListResidualState.exists_matchListAccCongruent_of_strongCoveredHead
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    (headBuilder : ∀
      {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
      {outerSubst : Metta.Subst}
      {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
      {subst result : Metta.Subst} {left right : List Atom}
      {seed : Bindings}
      (state : HEProjectedCertifiedListResidualState trace allowed
        outerFuel front outerSubst fuel work subst result left right seed)
      (_coverage : HEOriginalListConstraintCoverage trace left right)
      {nextLeft : Atom} {leftRest : List Atom}
      (head : HEProjectedTailHeadResidualPackage
        state nextLeft leftRest),
      Nonempty (HELiveMatchMergeCoreCongruentCertified trace allowed
        nextLeft head.nextRight seed head.nextSubst)) :
    ∀ {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
      {outerSubst : Metta.Subst}
      {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
      {subst result : Metta.Subst} {left right : List Atom}
      {seed : Bindings},
      (state : HEProjectedCertifiedListResidualState trace allowed
        outerFuel front outerSubst fuel work subst result left right seed) →
      HEOriginalListConstraintCoverage trace left right →
      Nonempty (HEMatchListAccCongruentCertified trace allowed
        left right seed result) := by
  intro outerFuel front outerSubst fuel work subst result left
  induction left generalizing outerFuel front outerSubst fuel work subst
      result with
  | nil =>
      intro right seed state _coverage
      exact state.exists_nilMatch rfl
  | cons nextLeft leftRest ih =>
      intro right seed state hcoverage
      obtain ⟨strongHead⟩ :=
        state.exists_tailHeadResidualPackage
          (nextLeft := nextLeft) (leftRest := leftRest) rfl
      obtain ⟨headLive⟩ := headBuilder state hcoverage strongHead
      let head := strongHead.toSolutionPackage
      let covered : HEOriginalConstraintCoveredProjectedListState trace allowed
          outerFuel front outerSubst fuel work subst result
          (nextLeft :: leftRest) right seed := {
        state := state.toSolutionState
        originalCoverage := hcoverage
      }
      let residual := head.coreResidualOfCoreCongruent headLive
      let weakTail := head.toCoveredProjectedTailStateCore covered residual
      let tailState := strongHead.toProjectedTailStateCore headLive
      obtain ⟨tailMatch⟩ := ih tailState weakTail.originalCoverage
      exact ⟨{
        out := tailMatch.out
        matchRel := by
          simpa only [HELiveMatchMergeCoreCertified.cons,
            strongHead.right_eq] using
            (headLive.toHELiveMatchMergeCoreCertified.cons
              tailMatch.toHEMatchListAccCertified).matchRel
        traceSound := by
          simpa only [HELiveMatchMergeCoreCertified.cons,
            strongHead.right_eq] using
            (headLive.toHELiveMatchMergeCoreCertified.cons
              tailMatch.toHEMatchListAccCertified).traceSound
        equalitySound := by
          simpa only [HELiveMatchMergeCoreCertified.cons,
            strongHead.right_eq] using
            (headLive.toHELiveMatchMergeCoreCertified.cons
              tailMatch.toHEMatchListAccCertified).equalitySound
        congruence := tailMatch.congruence
      }⟩

/-- Strong-state head callbacks after the four leaf/mismatch cases have been
factored out.  The selected package retains the incoming accumulator
congruence; original-constraint coverage is passed separately for the direct
fresh branches. -/
structure HEProjectedStrongHeadCallbacks
    (trace : List (String × Metta.Atom))
    (allowed : List (String × String)) where
  assignment : ∀
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    (state : HEProjectedCertifiedListResidualState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed)
    (_coverage : HEOriginalListConstraintCoverage trace left right)
    {key : String} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualPackage state (.var key) leftRest)
    {value : Atom},
    p.nextRight = value →
    DeclMatchSpec.Atom.isVarB value = false →
    Nonempty (HELiveMatchMergeCoreCongruentCertified trace allowed
      (.var key) p.nextRight seed p.nextSubst)
  nonVarVar : ∀
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    (state : HEProjectedCertifiedListResidualState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed)
    (_coverage : HEOriginalListConstraintCoverage trace left right)
    {value : Atom} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualPackage state value leftRest)
    {key : String},
    p.nextRight = .var key →
    DeclMatchSpec.Atom.isVarB value = false →
    Nonempty (HELiveMatchMergeCoreCongruentCertified trace allowed
      value p.nextRight seed p.nextSubst)
  equality : ∀
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    (state : HEProjectedCertifiedListResidualState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed)
    (_coverage : HEOriginalListConstraintCoverage trace left right)
    {leftKey : String} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualPackage state (.var leftKey) leftRest)
    {rightKey : String},
    p.nextRight = .var rightKey →
    (EqualityClosure.edgeGraph allowed).Reachable leftKey rightKey →
    Nonempty (HELiveMatchMergeCoreCongruentCertified trace allowed
      (.var leftKey) p.nextRight seed p.nextSubst)
  expression : ∀
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    (state : HEProjectedCertifiedListResidualState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed)
    (_coverage : HEOriginalListConstraintCoverage trace left right)
    {leftAtoms : List Atom} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualPackage
      state (.expression leftAtoms) leftRest)
    {rightAtoms : List Atom},
    p.nextRight = .expression rightAtoms →
    Nonempty (HELiveMatchMergeCoreCongruentCertified trace allowed
      (.expression leftAtoms) p.nextRight seed p.nextSubst)

/-- Exhaustive strong-state head dispatcher.  Satisfiability eliminates all
constructor clashes, identical symbols/grounded atoms use the direct strong
leaf lemmas, and only assignment, equality, and nested-expression behavior is
delegated to the exact-state callbacks. -/
theorem HEProjectedTailHeadResidualPackage.exists_coreLiveHead_of_strongCallbacks
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    (valuation : String → Metta.Atom)
    (htrace : MettaConstraintsSatisfied valuation trace)
    (haliases : HETraceAliasesAllowed trace allowed)
    (callbacks : HEProjectedStrongHeadCallbacks trace allowed)
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    {state : HEProjectedCertifiedListResidualState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed}
    (coverage : HEOriginalListConstraintCoverage trace left right)
    {nextLeft : Atom} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualPackage state nextLeft leftRest) :
    Nonempty (HELiveMatchMergeCoreCongruentCertified trace allowed
      nextLeft p.nextRight seed p.nextSubst) := by
  let weak := p.toSolutionPackage
  have hequation : MettaEquationSatisfied valuation
      (toLeaTTaAtom nextLeft, toLeaTTaAtom p.nextRight) := by
    simpa [weak, HEProjectedTailHeadResidualPackage.toSolutionPackage] using
      (weak.headSatisfied_of_trace valuation htrace).2
  cases nextLeft with
  | symbol leftName =>
      cases hright : p.nextRight with
      | symbol rightName =>
          rw [hright] at hequation
          have hname : leftName = rightName := by
            simpa [MettaEquationSatisfied, toLeaTTaAtom,
              applyClassSolution] using hequation
          subst rightName
          simpa only [hright] using p.exists_coreLiveSymbol_congruent hright
      | var rightName =>
          simpa only [hright] using
            callbacks.nonVarVar state coverage p hright rfl
      | grounded rightGround =>
          simp [MettaEquationSatisfied, toLeaTTaAtom,
            applyClassSolution, hright] at hequation
      | expression rightAtoms =>
          simp [MettaEquationSatisfied, toLeaTTaAtom,
            applyClassSolution, hright] at hequation
  | var leftName =>
      cases hright : p.nextRight with
      | symbol rightName =>
          simpa only [hright] using
            callbacks.assignment state coverage p hright rfl
      | var rightName =>
          have hallowed := weak.varVarAllowed_of_originalCoverage
            coverage haliases hright
          simpa only [hright] using
            callbacks.equality state coverage p hright hallowed
      | grounded rightGround =>
          simpa only [hright] using
            callbacks.assignment state coverage p hright rfl
      | expression rightAtoms =>
          simpa only [hright] using
            callbacks.assignment state coverage p hright rfl
  | grounded leftGround =>
      cases hright : p.nextRight with
      | symbol rightName =>
          simp [MettaEquationSatisfied, toLeaTTaAtom,
            applyClassSolution, hright] at hequation
      | var rightName =>
          simpa only [hright] using
            callbacks.nonVarVar state coverage p hright rfl
      | grounded rightGround =>
          rw [hright] at hequation
          have hatom :
              toLeaTTaAtom (.grounded leftGround) =
                toLeaTTaAtom (.grounded rightGround) := by
            simpa [MettaEquationSatisfied, toLeaTTaAtom,
              applyClassSolution] using hequation
          have hground : leftGround = rightGround := by
            have heq := toLeaTTaAtom_injective hatom
            injection heq
          subst rightGround
          simpa only [hright] using p.exists_coreLiveGrounded_congruent hright
      | expression rightAtoms =>
          simp [MettaEquationSatisfied, toLeaTTaAtom,
            applyClassSolution, hright] at hequation
  | expression leftAtoms =>
      cases hright : p.nextRight with
      | symbol rightName =>
          simp [MettaEquationSatisfied, toLeaTTaAtom,
            applyClassSolution, hright] at hequation
      | var rightName =>
          simpa only [hright] using
            callbacks.nonVarVar state coverage p hright rfl
      | grounded rightGround =>
          simp [MettaEquationSatisfied, toLeaTTaAtom,
            applyClassSolution, hright] at hequation
      | expression rightAtoms =>
          simpa only [hright] using
            callbacks.expression state coverage p hright

/-- Bootstrap full list congruence from a solution-only covered state.  The
list must be nonempty because its first live head is exactly what establishes
the strong accumulator invariant; the remaining siblings then use the
strong covered fold above. -/
theorem HEOriginalConstraintCoveredProjectedListState.exists_matchListAccCongruent_of_nonemptyCoreLiveHead
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    (headBuilder : ∀
      {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
      {outerSubst : Metta.Subst}
      {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
      {subst result : Metta.Subst} {left right : List Atom}
      {seed : Bindings}
      (covered : HEOriginalConstraintCoveredProjectedListState trace allowed
        outerFuel front outerSubst fuel work subst result left right seed)
      {nextLeft : Atom} {leftRest : List Atom}
      (head : HEProjectedTailHeadResidualSolutionPackage
        covered.state nextLeft leftRest),
      Nonempty (HELiveMatchMergeCoreCongruentCertified trace allowed
        nextLeft head.nextRight seed head.nextSubst))
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    (covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed)
    (hnonempty : left ≠ []) :
    Nonempty (HEMatchListAccCongruentCertified trace allowed
      left right seed result) := by
  cases left with
  | nil => exact False.elim (hnonempty rfl)
  | cons nextLeft leftRest =>
      obtain ⟨head⟩ :=
        covered.state.exists_tailHeadResidualPackage
          (nextLeft := nextLeft) (leftRest := leftRest) rfl
      obtain ⟨headLive⟩ := headBuilder covered head
      let residual := head.coreResidualOfCoreCongruent headLive
      let weakTail := head.toCoveredProjectedTailStateCore covered residual
      let tailState := head.toProjectedStrongTailStateCore headLive
      obtain ⟨tailMatch⟩ :=
        tailState.exists_matchListAccCongruent_of_coveredCoreLiveHead
          headBuilder weakTail.originalCoverage
      exact ⟨{
        out := tailMatch.out
        matchRel := by
          simpa only [HELiveMatchMergeCoreCertified.cons,
            head.right_eq] using
            (headLive.toHELiveMatchMergeCoreCertified.cons
              tailMatch.toHEMatchListAccCertified).matchRel
        traceSound := by
          simpa only [HELiveMatchMergeCoreCertified.cons,
            head.right_eq] using
            (headLive.toHELiveMatchMergeCoreCertified.cons
              tailMatch.toHEMatchListAccCertified).traceSound
        equalitySound := by
          simpa only [HELiveMatchMergeCoreCertified.cons,
            head.right_eq] using
            (headLive.toHELiveMatchMergeCoreCertified.cons
              tailMatch.toHEMatchListAccCertified).equalitySound
        congruence := tailMatch.congruence
      }⟩


/-- Forget precisely the standalone matcher-trace certificate that hidden
live conflict wrappers never inspect. -/
def HELiveMatchMergeCoreResidualCertified.toHidden
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {left right : Atom}
    {seed : Bindings} {subst : Metta.Subst}
    (h : HELiveMatchMergeCoreResidualCertified
      trace allowed left right seed subst) :
    HELiveHiddenMatchResidualCertified
      trace allowed left right seed subst := {
  matched := h.matcher.out
  matchRel := h.matcher.matchRel
  matchEqualitySound := h.matcher.equalitySound
  liveMerge := {
    toHELiveMergeCertified := h.liveMerge
    solutions := h.solutions
  }
  afterAssignmentsSound := h.afterAssignmentsSound
}

/-- List form of the same exact weakening. -/
def HELiveListMatchMergeCoreResidualCertified.toHidden
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {left right : List Atom}
    {seed : Bindings} {subst : Metta.Subst}
    (h : HELiveListMatchMergeCoreResidualCertified
      trace allowed left right seed subst) :
    HELiveHiddenListMatchResidualCertified
      trace allowed left right seed subst := {
  matched := h.matcher.out
  matchRel := h.matcher.matchRel
  matchEqualitySound := h.matcher.equalitySound
  liveMerge := {
    toHELiveMergeCertified := h.liveMerge
    solutions := h.solutions
  }
  afterAssignmentsSound := h.afterAssignmentsSound
}

/-- The direct assignment-conflict wrapper consumes only the hidden matcher
relation and the certified live merge.  No standalone matcher provenance is
smuggled into the ambient trace. -/
theorem HELiveHiddenMatchResidualCertified.toAssignmentConflictMergeLive
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {seed : Bindings}
    {subst : Metta.Subst} {key : String} {value first : Atom}
    {rest : List Atom}
    (h : HELiveHiddenMatchResidualCertified
      trace allowed first value seed subst)
    (hclass : seed.classValues key = first :: rest)
    (hconsistent : Bindings.valuesConsistent (first :: rest) = true)
    (hdifferent : first ≠ value) :
    ∃ hout : HELiveMergeSolutionCertified trace allowed seed
        (Bindings.empty.assign key value) subst,
      hout.after = h.liveMerge.after := by
  let hadd : AddVarBindingRel seed key value h.liveMerge.after :=
    AddVarBindingRel.conflict hclass hconsistent hdifferent
      h.matchRel (mergeBindings_sound h.liveMerge.merge_mem)
  let hassignments : MergeAssignsRel seed [(key, value)]
      h.liveMerge.after :=
    MergeAssignsRel.cons hadd
      (MergeAssignsRel.nil (acc := h.liveMerge.after))
  let hraw : MergeRel seed (⟨[(key, value)], []⟩ : Bindings)
      h.liveMerge.after :=
    MergeRel.mk hassignments
      (MergeEqsRel.nil (acc := h.liveMerge.after))
  have hright : Bindings.empty.assign key value =
      (⟨[(key, value)], []⟩ : Bindings) := by
    simp [Bindings.empty, Bindings.assign, Bindings.isBound,
      Bindings.lookup]
  have hrel : MergeRel seed (Bindings.empty.assign key value)
      h.liveMerge.after := by
    simpa only [hright] using hraw
  have htrace : MergeTraceSound trace hrel := by
    let haddSound : AddVarBindingTraceSound trace hadd :=
      AddVarBindingTraceSound.conflictLive
        (hclass := hclass) (hconsistent := hconsistent)
        (hdifferent := hdifferent) (hmatch := h.matchRel)
        (hmerge := mergeBindings_sound h.liveMerge.merge_mem)
        h.afterAssignmentsSound h.liveMerge.traceSound
    let hrawSound : MergeTraceSound trace hraw :=
      MergeTraceSound.mk
        (MergeAssignsTraceSound.cons haddSound
          MergeAssignsTraceSound.nil)
        MergeEqsTraceSound.nil
    simpa [Bindings.empty, Bindings.assign, Bindings.isBound,
      Bindings.lookup, Subsingleton.elim hraw hrel] using hrawSound
  have hbound : MergeEqualityClosureBoundSound allowed hrel := by
    let haddBound : AddVarBindingEqualityClosureBoundSound allowed hadd :=
      AddVarBindingEqualityClosureBoundSound.conflict
        (hclass := hclass) (hconsistent := hconsistent)
        (hdifferent := hdifferent) (hmatch := h.matchRel)
        (hmerge := mergeBindings_sound h.liveMerge.merge_mem)
        h.matchEqualitySound.bound h.liveMerge.equalitySound
    let hrawBound : MergeEqualityClosureBoundSound allowed hraw :=
      MergeEqualityClosureBoundSound.mk
        (MergeAssignsEqualityClosureBoundSound.cons haddBound
          MergeAssignsEqualityClosureBoundSound.nil)
        MergeEqsEqualityClosureBoundSound.nil
    simpa [Bindings.empty, Bindings.assign, Bindings.isBound,
      Bindings.lookup, Subsingleton.elim hraw hrel] using hrawBound
  obtain ⟨mergeFuel, hmerge⟩ := mergeBindings_complete hrel
  exact ⟨{
    after := h.liveMerge.after
    mergeFuel := mergeFuel
    merge_mem := hmerge
    traceSound := by
      simpa only [Subsingleton.elim (mergeBindings_sound hmerge) hrel]
        using htrace
    equalitySound := by
      simpa only [Subsingleton.elim (mergeBindings_sound hmerge) hrel]
        using hbound
    solutions := h.liveMerge.solutions
  }, rfl⟩

/-- Class-wide assignment reconciliation has the same live-only boundary. -/
theorem HELiveHiddenListMatchResidualCertified.toAssignmentReconcileMergeLive
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {seed : Bindings}
    {subst : Metta.Subst} {key : String} {value first : Atom}
    {rest : List Atom}
    (h : HELiveHiddenListMatchResidualCertified trace allowed
      (List.replicate (rest.length + 1) first) (rest ++ [value])
      seed subst)
    (hclass : seed.classValues key = first :: rest)
    (hinconsistent : Bindings.valuesConsistent (first :: rest) = false) :
    ∃ hout : HELiveMergeSolutionCertified trace allowed seed
        (Bindings.empty.assign key value) subst,
      hout.after = h.liveMerge.after := by
  let hadd : AddVarBindingRel seed key value h.liveMerge.after :=
    AddVarBindingRel.reconcile hclass hinconsistent
      h.matchRel (mergeBindings_sound h.liveMerge.merge_mem)
  let hassignments : MergeAssignsRel seed [(key, value)]
      h.liveMerge.after :=
    MergeAssignsRel.cons hadd
      (MergeAssignsRel.nil (acc := h.liveMerge.after))
  let hraw : MergeRel seed (⟨[(key, value)], []⟩ : Bindings)
      h.liveMerge.after :=
    MergeRel.mk hassignments
      (MergeEqsRel.nil (acc := h.liveMerge.after))
  have hrel : MergeRel seed (Bindings.empty.assign key value)
      h.liveMerge.after := by
    simpa [Bindings.empty, Bindings.assign, Bindings.isBound,
      Bindings.lookup] using hraw
  have htrace : MergeTraceSound trace hrel := by
    let haddSound : AddVarBindingTraceSound trace hadd :=
      AddVarBindingTraceSound.reconcileLive
        (hclass := hclass) (hinconsistent := hinconsistent)
        (hmatch := h.matchRel)
        (hmerge := mergeBindings_sound h.liveMerge.merge_mem)
        h.afterAssignmentsSound h.liveMerge.traceSound
    let hrawSound : MergeTraceSound trace hraw :=
      MergeTraceSound.mk
        (MergeAssignsTraceSound.cons haddSound
          MergeAssignsTraceSound.nil)
        MergeEqsTraceSound.nil
    simpa [Bindings.empty, Bindings.assign, Bindings.isBound,
      Bindings.lookup, Subsingleton.elim hraw hrel] using hrawSound
  have hbound : MergeEqualityClosureBoundSound allowed hrel := by
    let haddBound : AddVarBindingEqualityClosureBoundSound allowed hadd :=
      AddVarBindingEqualityClosureBoundSound.reconcile
        (hclass := hclass) (hinconsistent := hinconsistent)
        (hmatch := h.matchRel)
        (hmerge := mergeBindings_sound h.liveMerge.merge_mem)
        (h.matchEqualitySound.preserves
          (HEEqualityClosureBound.empty allowed))
        h.liveMerge.equalitySound
    let hrawBound : MergeEqualityClosureBoundSound allowed hraw :=
      MergeEqualityClosureBoundSound.mk
        (MergeAssignsEqualityClosureBoundSound.cons haddBound
          MergeAssignsEqualityClosureBoundSound.nil)
        MergeEqsEqualityClosureBoundSound.nil
    simpa [Bindings.empty, Bindings.assign, Bindings.isBound,
      Bindings.lookup, Subsingleton.elim hraw hrel] using hrawBound
  obtain ⟨mergeFuel, hmerge⟩ := mergeBindings_complete hrel
  exact ⟨{
    after := h.liveMerge.after
    mergeFuel := mergeFuel
    merge_mem := hmerge
    traceSound := by
      simpa only [Subsingleton.elim (mergeBindings_sound hmerge) hrel]
        using htrace
    equalitySound := by
      simpa only [Subsingleton.elim (mergeBindings_sound hmerge) hrel]
        using hbound
    solutions := h.liveMerge.solutions
  }, rfl⟩

/-- Two-value equality reconciliation likewise needs no standalone hidden
matcher trace certificate. -/
theorem HELiveHiddenMatchResidualCertified.toEqualityPairConflictMergeLive
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {seed : Bindings}
    {subst : Metta.Subst} {left right : String} {first second : Atom}
    (h : HELiveHiddenMatchResidualCertified trace allowed first second
      (seed.addEquality left right) subst)
    (hvalues : (seed.addEquality left right).classValues left =
      [first, second])
    (hinconsistent : Bindings.valuesConsistent [first, second] = false)
    (hallowed :
      (EqualityClosure.edgeGraph allowed).Reachable left right) :
    ∃ hout : HELiveMergeSolutionCertified trace allowed seed
        (Bindings.empty.addEquality left right) subst,
      hout.after = h.liveMerge.after := by
  let hadd : AddVarEqualityRel seed left right h.liveMerge.after :=
    AddVarEqualityRel.pairConflict hvalues hinconsistent
      h.matchRel (mergeBindings_sound h.liveMerge.merge_mem)
  let hequalities : MergeEqsRel seed [(left, right)]
      h.liveMerge.after :=
    MergeEqsRel.cons hadd
      (MergeEqsRel.nil (acc := h.liveMerge.after))
  let hraw : MergeRel seed (⟨[], [(left, right)]⟩ : Bindings)
      h.liveMerge.after :=
    MergeRel.mk (MergeAssignsRel.nil (acc := seed)) hequalities
  have hrel : MergeRel seed
      (Bindings.empty.addEquality left right) h.liveMerge.after := by
    simpa [Bindings.empty, Bindings.addEquality] using hraw
  have htrace : MergeTraceSound trace hrel := by
    let haddSound : AddVarEqualityTraceSound trace hadd :=
      AddVarEqualityTraceSound.pairConflictLive
        (hvalues := hvalues) (hinconsistent := hinconsistent)
        (hmatch := h.matchRel)
        (hmerge := mergeBindings_sound h.liveMerge.merge_mem)
        h.afterAssignmentsSound h.liveMerge.traceSound
    let hrawSound : MergeTraceSound trace hraw :=
      MergeTraceSound.mk MergeAssignsTraceSound.nil
        (MergeEqsTraceSound.cons haddSound MergeEqsTraceSound.nil)
    simpa [Bindings.empty, Bindings.addEquality,
      Subsingleton.elim hraw hrel] using hrawSound
  have hbound : MergeEqualityClosureBoundSound allowed hrel := by
    let haddBound : AddVarEqualityEqualityClosureBoundSound allowed hadd :=
      AddVarEqualityEqualityClosureBoundSound.pairConflict
        (hvalues := hvalues) (hinconsistent := hinconsistent)
        (hmatch := h.matchRel)
        (hmerge := mergeBindings_sound h.liveMerge.merge_mem)
        hallowed h.matchEqualitySound.bound
        h.liveMerge.equalitySound
    let hrawBound : MergeEqualityClosureBoundSound allowed hraw :=
      MergeEqualityClosureBoundSound.mk
        MergeAssignsEqualityClosureBoundSound.nil
        (MergeEqsEqualityClosureBoundSound.cons haddBound
          MergeEqsEqualityClosureBoundSound.nil)
    simpa [Bindings.empty, Bindings.addEquality,
      Subsingleton.elim hraw hrel] using hrawBound
  obtain ⟨mergeFuel, hmerge⟩ := mergeBindings_complete hrel
  exact ⟨{
    after := h.liveMerge.after
    mergeFuel := mergeFuel
    merge_mem := hmerge
    traceSound := by
      simpa only [Subsingleton.elim (mergeBindings_sound hmerge) hrel]
        using htrace
    equalitySound := by
      simpa only [Subsingleton.elim (mergeBindings_sound hmerge) hrel]
        using hbound
    solutions := h.liveMerge.solutions
  }, rfl⟩

/-- Whole-class equality reconciliation also closes at the live-only
boundary. -/
theorem HELiveHiddenListMatchResidualCertified.toEqualityClassConflictMergeLive
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {seed : Bindings}
    {subst : Metta.Subst} {left right : String}
    {first second third : Atom} {rest : List Atom}
    (h : HELiveHiddenListMatchResidualCertified trace allowed
      (List.replicate (rest.length + 2) first)
      (second :: third :: rest) (seed.addEquality left right) subst)
    (hvalues : (seed.addEquality left right).classValues left =
      first :: second :: third :: rest)
    (hinconsistent : Bindings.valuesConsistent
      (first :: second :: third :: rest) = false)
    (hallowed :
      (EqualityClosure.edgeGraph allowed).Reachable left right) :
    ∃ hout : HELiveMergeSolutionCertified trace allowed seed
        (Bindings.empty.addEquality left right) subst,
      hout.after = h.liveMerge.after := by
  let hadd : AddVarEqualityRel seed left right h.liveMerge.after :=
    AddVarEqualityRel.classConflict hvalues hinconsistent
      h.matchRel (mergeBindings_sound h.liveMerge.merge_mem)
  let hequalities : MergeEqsRel seed [(left, right)]
      h.liveMerge.after :=
    MergeEqsRel.cons hadd
      (MergeEqsRel.nil (acc := h.liveMerge.after))
  let hraw : MergeRel seed (⟨[], [(left, right)]⟩ : Bindings)
      h.liveMerge.after :=
    MergeRel.mk (MergeAssignsRel.nil (acc := seed)) hequalities
  have hrel : MergeRel seed
      (Bindings.empty.addEquality left right) h.liveMerge.after := by
    simpa [Bindings.empty, Bindings.addEquality] using hraw
  have htrace : MergeTraceSound trace hrel := by
    let haddSound : AddVarEqualityTraceSound trace hadd :=
      AddVarEqualityTraceSound.classConflictLive
        (hvalues := hvalues) (hinconsistent := hinconsistent)
        (hmatch := h.matchRel)
        (hmerge := mergeBindings_sound h.liveMerge.merge_mem)
        h.afterAssignmentsSound h.liveMerge.traceSound
    let hrawSound : MergeTraceSound trace hraw :=
      MergeTraceSound.mk MergeAssignsTraceSound.nil
        (MergeEqsTraceSound.cons haddSound MergeEqsTraceSound.nil)
    simpa [Bindings.empty, Bindings.addEquality,
      Subsingleton.elim hraw hrel] using hrawSound
  have hbound : MergeEqualityClosureBoundSound allowed hrel := by
    let haddBound : AddVarEqualityEqualityClosureBoundSound allowed hadd :=
      AddVarEqualityEqualityClosureBoundSound.classConflict
        (hvalues := hvalues) (hinconsistent := hinconsistent)
        (hmatch := h.matchRel)
        (hmerge := mergeBindings_sound h.liveMerge.merge_mem)
        hallowed
        (h.matchEqualitySound.preserves
          (HEEqualityClosureBound.empty allowed))
        h.liveMerge.equalitySound
    let hrawBound : MergeEqualityClosureBoundSound allowed hraw :=
      MergeEqualityClosureBoundSound.mk
        MergeAssignsEqualityClosureBoundSound.nil
        (MergeEqsEqualityClosureBoundSound.cons haddBound
          MergeEqsEqualityClosureBoundSound.nil)
    simpa [Bindings.empty, Bindings.addEquality,
      Subsingleton.elim hraw hrel] using hrawBound
  obtain ⟨mergeFuel, hmerge⟩ := mergeBindings_complete hrel
  exact ⟨{
    after := h.liveMerge.after
    mergeFuel := mergeFuel
    merge_mem := hmerge
    traceSound := by
      simpa only [Subsingleton.elim (mergeBindings_sound hmerge) hrel]
        using htrace
    equalitySound := by
      simpa only [Subsingleton.elim (mergeBindings_sound hmerge) hrel]
        using hbound
    solutions := h.liveMerge.solutions
  }, rfl⟩

/-! ## Weak hidden progress reconstruction -/

/-- Reconstruct the original variable/non-variable head from a weak hidden
scalar conflict.  The selected value is realized from class-value provenance;
the outer wrapper supplies the standalone trace certificate required by the
public progress package. -/
theorem
    HELiveHiddenMatchValueProgressCertified.toAssignmentConflictSolutionProgress
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {seed : Bindings}
    {key : String} {value first : Atom} {rest : List Atom}
    (h : HELiveHiddenMatchValueProgressCertified trace allowed
      first value seed (key, toLeaTTaAtom value))
    (hclass : seed.classValues key = first :: rest)
    (hconsistent : Bindings.valuesConsistent (first :: rest) = true)
    (hdifferent : first ≠ value)
    (hnonvar : DeclMatchSpec.Atom.isVarB value = false) :
    Nonempty (HELiveMatchMergeSolutionProgressCertified trace allowed
      (.var key) value seed (key, toLeaTTaAtom value)) := by
  obtain ⟨hmerge, hafter⟩ :=
    h.live.operational.toAssignmentConflictMergeLive
      hclass hconsistent hdifferent
  let houter := hmerge.withVarNonVarMatch hnonvar
    (h.subst_subset_trace _ h.entry_mem)
  exact ⟨{
    subst := h.subst
    live := houter
    entry_mem := h.entry_mem
    subst_subset_trace := h.subst_subset_trace
    realized_after := by
      change LeaEliminationTraceEntryRealized hmerge.after
        (key, toLeaTTaAtom value)
      rw [hafter]
      exact h.realized_of_nonvar
        (toLeaTTaAtom_ne_var_of_isVarB_false hnonvar)
    assignmentsSound := by
      change LeaEliminationTraceAssignmentsSound hmerge.after trace
      rw [hafter]
      exact h.live.operational.afterAssignmentsSound
  }⟩

/-- Class-wide assignment reconciliation has the same weak reconstruction
law. -/
theorem
    HELiveHiddenListMatchValueProgressCertified.toAssignmentReconcileSolutionProgress
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {seed : Bindings}
    {key : String} {value first : Atom} {rest : List Atom}
    (h : HELiveHiddenListMatchValueProgressCertified trace allowed
      (List.replicate (rest.length + 1) first) (rest ++ [value])
      seed (key, toLeaTTaAtom value))
    (hclass : seed.classValues key = first :: rest)
    (hinconsistent : Bindings.valuesConsistent (first :: rest) = false)
    (hnonvar : DeclMatchSpec.Atom.isVarB value = false) :
    Nonempty (HELiveMatchMergeSolutionProgressCertified trace allowed
      (.var key) value seed (key, toLeaTTaAtom value)) := by
  obtain ⟨hmerge, hafter⟩ :=
    h.live.operational.toAssignmentReconcileMergeLive
      hclass hinconsistent
  let houter := hmerge.withVarNonVarMatch hnonvar
    (h.subst_subset_trace _ h.entry_mem)
  exact ⟨{
    subst := h.subst
    live := houter
    entry_mem := h.entry_mem
    subst_subset_trace := h.subst_subset_trace
    realized_after := by
      change LeaEliminationTraceEntryRealized hmerge.after
        (key, toLeaTTaAtom value)
      rw [hafter]
      exact h.realized_of_nonvar
        (toLeaTTaAtom_ne_var_of_isVarB_false hnonvar)
    assignmentsSound := by
      change LeaEliminationTraceAssignmentsSound hmerge.after trace
      rw [hafter]
      exact h.live.operational.afterAssignmentsSound
  }⟩

/-- Reconstruct an original variable/variable head from a weak hidden
two-value reconciliation.  Its selected alias is already realized by the
inner live seed, so the external merge preserves it independently of the raw
substitution's alias presentation. -/
theorem
    HELiveHiddenMatchValueProgressCertified.toEqualityPairSolutionProgress
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {seed : Bindings}
    {left right : String} {first second : Atom}
    (h : HELiveHiddenMatchValueProgressCertified trace allowed
      first second (seed.addEquality left right) (left, .var right))
    (hvalues : (seed.addEquality left right).classValues left =
      [first, second])
    (hinconsistent : Bindings.valuesConsistent [first, second] = false)
    (hallowed :
      (EqualityClosure.edgeGraph allowed).Reachable left right) :
    Nonempty (HELiveMatchMergeSolutionProgressCertified trace allowed
      (.var left) (.var right) seed (left, .var right)) := by
  obtain ⟨hmerge, hafter⟩ :=
    h.live.operational.toEqualityPairConflictMergeLive
      hvalues hinconsistent hallowed
  let houter := hmerge.withVarVarMatch hallowed
  have hseedRealized : LeaEliminationTraceEntryRealized
      (seed.addEquality left right) (left, .var right) := by
    change right ∈ (seed.addEquality left right).eqClass left
    rw [EqualityClosure.mem_eqClass_iff_reachable]
    by_cases hsame : left = right
    · subst right
      exact .rfl
    · exact (show
          (EqualityClosure.edgeGraph
            (seed.addEquality left right).equalities).Adj left right by
          rw [EqualityClosure.edgeGraph_adj_iff]
          exact ⟨hsame, Or.inl (by simp [Bindings.addEquality])⟩).reachable
  exact ⟨{
    subst := h.subst
    live := houter
    entry_mem := h.entry_mem
    subst_subset_trace := h.subst_subset_trace
    realized_after := by
      change LeaEliminationTraceEntryRealized hmerge.after
        (left, .var right)
      rw [hafter]
      exact h.realized_of_seed hseedRealized
    assignmentsSound := by
      change LeaEliminationTraceAssignmentsSound hmerge.after trace
      rw [hafter]
      exact h.live.operational.afterAssignmentsSound
  }⟩

/-- Whole-class equality reconciliation has the same alias-safe weak
reconstruction law. -/
theorem
    HELiveHiddenListMatchValueProgressCertified.toEqualityClassSolutionProgress
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {seed : Bindings}
    {left right : String} {first second third : Atom} {rest : List Atom}
    (h : HELiveHiddenListMatchValueProgressCertified trace allowed
      (List.replicate (rest.length + 2) first) (second :: third :: rest)
      (seed.addEquality left right) (left, .var right))
    (hvalues : (seed.addEquality left right).classValues left =
      first :: second :: third :: rest)
    (hinconsistent : Bindings.valuesConsistent
      (first :: second :: third :: rest) = false)
    (hallowed :
      (EqualityClosure.edgeGraph allowed).Reachable left right) :
    Nonempty (HELiveMatchMergeSolutionProgressCertified trace allowed
      (.var left) (.var right) seed (left, .var right)) := by
  obtain ⟨hmerge, hafter⟩ :=
    h.live.operational.toEqualityClassConflictMergeLive
      hvalues hinconsistent hallowed
  let houter := hmerge.withVarVarMatch hallowed
  have hseedRealized : LeaEliminationTraceEntryRealized
      (seed.addEquality left right) (left, .var right) := by
    change right ∈ (seed.addEquality left right).eqClass left
    rw [EqualityClosure.mem_eqClass_iff_reachable]
    by_cases hsame : left = right
    · subst right
      exact .rfl
    · exact (show
          (EqualityClosure.edgeGraph
            (seed.addEquality left right).equalities).Adj left right by
          rw [EqualityClosure.edgeGraph_adj_iff]
          exact ⟨hsame, Or.inl (by simp [Bindings.addEquality])⟩).reachable
  exact ⟨{
    subst := h.subst
    live := houter
    entry_mem := h.entry_mem
    subst_subset_trace := h.subst_subset_trace
    realized_after := by
      change LeaEliminationTraceEntryRealized hmerge.after
        (left, .var right)
      rw [hafter]
      exact h.realized_of_seed hseedRealized
    assignmentsSound := by
      change LeaEliminationTraceAssignmentsSound hmerge.after trace
      rw [hafter]
      exact h.live.operational.afterAssignmentsSound
  }⟩

/-- Feed weak hidden value-conflict results into the established certified
outer progress adapter.  The only strengthening performed is reconstruction
of the original variable/non-variable head. -/
theorem certifiedValueConflictProgress_of_hidden_value_inner
    {trace : List (String × Metta.Atom)} {before : Bindings}
    {key : String} {value first : Atom} {leaValue : Metta.Atom}
    {rest : List Atom}
    (hvalue : toLeaTTaAtom value = leaValue)
    (hvalueNonvar : DeclMatchSpec.Atom.isVarB value = false)
    (hclass : before.classValues key = first :: rest)
    (hentry : (key, leaValue) ∈ trace)
    (hpending : ¬ LeaEliminationTraceEntryRealized before
      (key, leaValue))
    (hatom : Bindings.valuesConsistent (first :: rest) = true →
      first ≠ value →
      Nonempty (HELiveHiddenMatchValueProgressCertified trace
        (eliminationTraceAliases trace) first value before
        (key, leaValue)))
    (hlist : Bindings.valuesConsistent (first :: rest) = false →
      Nonempty (HELiveHiddenListMatchValueProgressCertified trace
        (eliminationTraceAliases trace)
        (List.replicate (rest.length + 1) first) (rest ++ [value])
        before (key, leaValue))) :
    ∃ after, Nonempty (HECertifiedEliminationTraceProgressStep trace
      (eliminationTraceAliases trace) before after) := by
  have hsolution : ∀ valuation,
      HEBindingSatisfied valuation before →
      MettaConstraintsSatisfied valuation trace →
      MettaEquationSatisfied valuation
        (toLeaTTaAtom (.var key), toLeaTTaAtom value) := by
    intro valuation _hbefore htrace
    have hconstraint := htrace (key, leaValue) hentry
    simpa [hvalue, MettaEquationSatisfied, applyClassSolution] using
      hconstraint
  cases hconsistent : Bindings.valuesConsistent (first :: rest) with
  | false =>
      obtain ⟨hinner⟩ := hlist hconsistent
      have hinner' : HELiveHiddenListMatchValueProgressCertified trace
          (eliminationTraceAliases trace)
          (List.replicate (rest.length + 1) first) (rest ++ [value])
          before (key, toLeaTTaAtom value) := by
        simpa only [hvalue] using hinner
      obtain ⟨hprogress⟩ :=
        hinner'.toAssignmentReconcileSolutionProgress
          hclass hconsistent hvalueNonvar
      have hprogress' : HELiveMatchMergeSolutionProgressCertified trace
          (eliminationTraceAliases trace) (.var key) value before
          (key, leaValue) := by
        simpa only [hvalue] using hprogress
      exact ⟨hprogress'.live.after, ⟨
        hprogress'.toCertifiedProgressStep hentry hpending hsolution⟩⟩
  | true =>
      have hdifferent : first ≠ value := by
        intro hsame
        subst first
        apply hpending
        rw [← hvalue]
        have hstored : value ∈ before.classValues key := by
          rw [hclass]
          simp
        unfold Bindings.classValues at hstored
        obtain ⟨storedKey, hordered, hlookup⟩ :=
          List.mem_filterMap.mp hstored
        have hassignment : (storedKey, value) ∈ before.assignments :=
          assignment_mem_of_lookup_eq_some_public (by
            simpa [Bindings.lookup] using hlookup)
        have hclassForward : storedKey ∈ before.eqClass key :=
          EqualityClosure.mem_eqClassOrdered_iff.mp hordered
        have hclassReverse : key ∈ before.eqClass storedKey := by
          apply EqualityClosure.mem_eqClass_iff_reachable.mpr
          exact (EqualityClosure.mem_eqClass_iff_reachable.mp
            hclassForward).symm
        cases value with
        | var target =>
            simp [DeclMatchSpec.Atom.isVarB] at hvalueNonvar
        | symbol name | grounded name | expression name =>
            exact ⟨storedKey, _, hassignment, hclassReverse,
              HELeaAtomClassRel.translation before _⟩
      obtain ⟨hinner⟩ := hatom hconsistent hdifferent
      have hinner' : HELiveHiddenMatchValueProgressCertified trace
          (eliminationTraceAliases trace) first value before
          (key, toLeaTTaAtom value) := by
        simpa only [hvalue] using hinner
      obtain ⟨hprogress⟩ :=
        hinner'.toAssignmentConflictSolutionProgress
          hclass hconsistent hdifferent hvalueNonvar
      have hprogress' : HELiveMatchMergeSolutionProgressCertified trace
          (eliminationTraceAliases trace) (.var key) value before
          (key, leaValue) := by
        simpa only [hvalue] using hprogress
      exact ⟨hprogress'.live.after, ⟨
        hprogress'.toCertifiedProgressStep hentry hpending hsolution⟩⟩

/-- Alias-conflict counterpart of the weak hidden adapter.  Realization of
the selected alias comes from the explicit equality already present in the
inner live seed, not from the normalized substitution. -/
theorem certifiedAliasConflictProgress_of_hidden_value_inner
    {trace : List (String × Metta.Atom)} {before : Bindings}
    {left right : String}
    (hinconsistent : Bindings.valuesConsistent
      ((before.addEquality left right).classValues left) = false)
    (hentry : (left, .var right) ∈ trace)
    (hpending : ¬ LeaEliminationTraceEntryRealized before
      (left, .var right))
    (hatom : ∀ {first second : Atom},
      (before.addEquality left right).classValues left = [first, second] →
      Nonempty (HELiveHiddenMatchValueProgressCertified trace
        (eliminationTraceAliases trace) first second
        (before.addEquality left right) (left, .var right)))
    (hlist : ∀ {first second third : Atom} {rest : List Atom},
      (before.addEquality left right).classValues left =
        first :: second :: third :: rest →
      Nonempty (HELiveHiddenListMatchValueProgressCertified trace
        (eliminationTraceAliases trace)
        (List.replicate (rest.length + 2) first)
        (second :: third :: rest) (before.addEquality left right)
        (left, .var right))) :
    ∃ after, Nonempty (HECertifiedEliminationTraceProgressStep trace
      (eliminationTraceAliases trace) before after) := by
  have hallowed :
      (EqualityClosure.edgeGraph
        (eliminationTraceAliases trace)).Reachable left right := by
    by_cases hsame : left = right
    · subst right
      exact .rfl
    · exact (show
          (EqualityClosure.edgeGraph
            (eliminationTraceAliases trace)).Adj left right by
          rw [EqualityClosure.edgeGraph_adj_iff]
          exact ⟨hsame, Or.inl
            (mem_eliminationTraceAliases_iff.mpr hentry)⟩).reachable
  have hsolution : ∀ valuation,
      HEBindingSatisfied valuation before →
      MettaConstraintsSatisfied valuation trace →
      MettaEquationSatisfied valuation
        (toLeaTTaAtom (.var left), toLeaTTaAtom (.var right)) := by
    intro valuation _hbefore htrace
    have hconstraint := htrace (left, .var right) hentry
    simpa [MettaEquationSatisfied, applyClassSolution] using hconstraint
  cases hvaluesEq :
      (before.addEquality left right).classValues left with
  | nil =>
      rw [hvaluesEq] at hinconsistent
      simp [Bindings.valuesConsistent] at hinconsistent
  | cons first restValues =>
      cases restValues with
      | nil =>
          rw [hvaluesEq] at hinconsistent
          simp [Bindings.valuesConsistent] at hinconsistent
      | cons second tailValues =>
          cases tailValues with
          | nil =>
              have hvalues :
                  (before.addEquality left right).classValues left =
                    [first, second] := by
                simpa using hvaluesEq
              obtain ⟨hinner⟩ := hatom hvalues
              obtain ⟨hprogress⟩ :=
                hinner.toEqualityPairSolutionProgress hvalues
                  (by simpa [hvalues] using hinconsistent) hallowed
              exact ⟨hprogress.live.after, ⟨
                hprogress.toCertifiedProgressStep
                  hentry hpending hsolution⟩⟩
          | cons third rest =>
              have hvalues :
                  (before.addEquality left right).classValues left =
                    first :: second :: third :: rest := by
                simpa using hvaluesEq
              obtain ⟨hinner⟩ := hlist hvalues
              obtain ⟨hprogress⟩ :=
                hinner.toEqualityClassSolutionProgress hvalues
                  (by simpa [hvalues] using hinconsistent) hallowed
              exact ⟨hprogress.live.after, ⟨
                hprogress.toCertifiedProgressStep
                  hentry hpending hsolution⟩⟩

/-- Complete the outer pending-cardinality recursion from weak hidden
class-value progress callbacks.  This is the alias-safe recursive boundary:
solution theory, trace soundness, and equality bounds are retained by the
operational package, while raw-substitution equality closure is never
assumed. -/
theorem exists_completeSatisfiedCertifiedMatcherMergeChain_of_hidden_value_inner
    {trace : List (String × Metta.Atom)}
    {valuation : String → Metta.Atom}
    (himage : ∀ key term, (key, term) ∈ trace →
      ∃ atom : Atom, toLeaTTaAtom atom = term)
    (htraceSatisfied : MettaConstraintsSatisfied valuation trace)
    (hvalueInner : ∀
      (before : Bindings) (key : String) (value : Atom)
      (leaValue : Metta.Atom) (first : Atom) (rest : List Atom),
      HEAssignmentsNonVariable before →
      LeaEliminationTraceAssignmentsSound before trace →
      HEEqualityClosureBound before (eliminationTraceAliases trace) →
      HEBindingSatisfied valuation before →
      toLeaTTaAtom value = leaValue →
      DeclMatchSpec.Atom.isVarB value = false →
      before.classValues key = first :: rest →
      (key, leaValue) ∈ trace →
      ¬ LeaEliminationTraceEntryRealized before (key, leaValue) →
      BothExpressions first value →
      (∀ {stored other : Atom},
        stored ∈ before.classValues key →
        other ∈ before.classValues key →
        stored ≠ other → BothExpressions stored other) →
      ((Bindings.valuesConsistent (first :: rest) = true →
          first ≠ value →
          Nonempty (HELiveHiddenMatchValueProgressCertified trace
            (eliminationTraceAliases trace) first value before
            (key, leaValue))) ∧
        (Bindings.valuesConsistent (first :: rest) = false →
          Nonempty (HELiveHiddenListMatchValueProgressCertified trace
            (eliminationTraceAliases trace)
            (List.replicate (rest.length + 1) first) (rest ++ [value])
            before (key, leaValue)))))
    (haliasInner : ∀
      (before : Bindings) (left right : String),
      HEAssignmentsNonVariable before →
      LeaEliminationTraceAssignmentsSound before trace →
      HEEqualityClosureBound before (eliminationTraceAliases trace) →
      HEBindingSatisfied valuation before →
      Bindings.valuesConsistent
          ((before.addEquality left right).classValues left) = false →
      (left, .var right) ∈ trace →
      ¬ LeaEliminationTraceEntryRealized before (left, .var right) →
      (∀ {first second : Atom},
        first ∈ (before.addEquality left right).classValues left →
        second ∈ (before.addEquality left right).classValues left →
        first ≠ second → BothExpressions first second) →
      ((∀ {first second : Atom},
          (before.addEquality left right).classValues left =
            [first, second] →
          Nonempty (HELiveHiddenMatchValueProgressCertified trace
            (eliminationTraceAliases trace) first second
            (before.addEquality left right) (left, .var right))) ∧
        (∀ {first second third : Atom} {rest : List Atom},
          (before.addEquality left right).classValues left =
            first :: second :: third :: rest →
          Nonempty (HELiveHiddenListMatchValueProgressCertified trace
            (eliminationTraceAliases trace)
            (List.replicate (rest.length + 2) first)
            (second :: third :: rest) (before.addEquality left right)
            (left, .var right))))) :
    ∃ out,
      HECertifiedMatcherMergeChain trace
          (eliminationTraceAliases trace) Bindings.empty out ∧
        HEAssignmentsNonVariable out ∧
          LeaEliminationTraceStructuralRel out trace ∧
            HEEqualityClosureBound out (eliminationTraceAliases trace) ∧
              HEBindingSatisfied valuation out := by
  apply exists_completeSatisfiedCertifiedMatcherMergeChain_of_conflict_progress
    himage htraceSatisfied
  · intro before key value leaValue first rest hnonvar hsound hbound
      hbefore hvalue hvalueNonvar hclass hentry hpending hexpressions
      hallExpressions
    obtain ⟨hatom, hlist⟩ :=
      hvalueInner before key value leaValue first rest
        hnonvar hsound hbound hbefore hvalue hvalueNonvar hclass hentry
        hpending hexpressions hallExpressions
    exact certifiedValueConflictProgress_of_hidden_value_inner hvalue
      hvalueNonvar hclass hentry hpending hatom hlist
  · intro before left right hnonvar hsound hbound hbefore hinconsistent
      hentry hpending hallExpressions
    obtain ⟨hatom, hlist⟩ :=
      haliasInner before left right hnonvar hsound hbound hbefore
        hinconsistent hentry hpending hallExpressions
    exact certifiedAliasConflictProgress_of_hidden_value_inner
      hinconsistent hentry hpending hatom hlist

/-! ## Strong outer-head reconstruction from hidden post-states -/

/-- A hidden scalar assignment conflict, once structurally solved at its
actual post-state, reconstructs the original variable/non-variable head. -/
theorem HELiveHiddenMatchStructuralCertified.toAssignmentConflictCoreCongruent
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {seed : Bindings}
    {subst : Metta.Subst} {key : String} {value first : Atom}
    {rest : List Atom}
    (h : HELiveHiddenMatchStructuralCertified
      trace allowed first value seed subst)
    (hclass : seed.classValues key = first :: rest)
    (hconsistent : Bindings.valuesConsistent (first :: rest) = true)
    (hdifferent : first ≠ value)
    (hnonvar : DeclMatchSpec.Atom.isVarB value = false) :
    Nonempty (HELiveMatchMergeCoreCongruentCertified trace allowed
      (.var key) value seed subst) := by
  obtain ⟨hmerge, hafter⟩ :=
    h.operational.toAssignmentConflictMergeLive
      hclass hconsistent hdifferent
  let hcore := hmerge.toHELiveMergeCertified.withCoreVarNonVarMatch hnonvar
  exact ⟨{
    toHELiveMatchMergeCoreCertified := hcore
    congruence := by
      change LeaBindingCongruence hmerge.after
        (Metta.Bindings.ofSubst subst)
      rw [hafter]
      exact h.congruence
  }⟩

/-- A hidden class-wide assignment reconciliation reconstructs the same
outer assignment head. -/
theorem HELiveHiddenListMatchStructuralCertified.toAssignmentReconcileCoreCongruent
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {seed : Bindings}
    {subst : Metta.Subst} {key : String} {value first : Atom}
    {rest : List Atom}
    (h : HELiveHiddenListMatchStructuralCertified trace allowed
      (List.replicate (rest.length + 1) first) (rest ++ [value])
      seed subst)
    (hclass : seed.classValues key = first :: rest)
    (hinconsistent : Bindings.valuesConsistent (first :: rest) = false)
    (hnonvar : DeclMatchSpec.Atom.isVarB value = false) :
    Nonempty (HELiveMatchMergeCoreCongruentCertified trace allowed
      (.var key) value seed subst) := by
  obtain ⟨hmerge, hafter⟩ :=
    h.operational.toAssignmentReconcileMergeLive hclass hinconsistent
  let hcore := hmerge.toHELiveMergeCertified.withCoreVarNonVarMatch hnonvar
  exact ⟨{
    toHELiveMatchMergeCoreCertified := hcore
    congruence := by
      change LeaBindingCongruence hmerge.after
        (Metta.Bindings.ofSubst subst)
      rw [hafter]
      exact h.congruence
  }⟩

/-- Symmetric scalar assignment conflict. -/
theorem HELiveHiddenMatchStructuralCertified.toNonVarVarConflictCoreCongruent
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {seed : Bindings}
    {subst : Metta.Subst} {key : String} {value first : Atom}
    {rest : List Atom}
    (h : HELiveHiddenMatchStructuralCertified
      trace allowed first value seed subst)
    (hclass : seed.classValues key = first :: rest)
    (hconsistent : Bindings.valuesConsistent (first :: rest) = true)
    (hdifferent : first ≠ value)
    (hnonvar : DeclMatchSpec.Atom.isVarB value = false) :
    Nonempty (HELiveMatchMergeCoreCongruentCertified trace allowed
      value (.var key) seed subst) := by
  obtain ⟨hmerge, hafter⟩ :=
    h.operational.toAssignmentConflictMergeLive
      hclass hconsistent hdifferent
  let hcore := hmerge.toHELiveMergeCertified.withCoreNonVarVarMatch hnonvar
  exact ⟨{
    toHELiveMatchMergeCoreCertified := hcore
    congruence := by
      change LeaBindingCongruence hmerge.after
        (Metta.Bindings.ofSubst subst)
      rw [hafter]
      exact h.congruence
  }⟩

/-- Symmetric class-wide assignment reconciliation. -/
theorem HELiveHiddenListMatchStructuralCertified.toNonVarVarReconcileCoreCongruent
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {seed : Bindings}
    {subst : Metta.Subst} {key : String} {value first : Atom}
    {rest : List Atom}
    (h : HELiveHiddenListMatchStructuralCertified trace allowed
      (List.replicate (rest.length + 1) first) (rest ++ [value])
      seed subst)
    (hclass : seed.classValues key = first :: rest)
    (hinconsistent : Bindings.valuesConsistent (first :: rest) = false)
    (hnonvar : DeclMatchSpec.Atom.isVarB value = false) :
    Nonempty (HELiveMatchMergeCoreCongruentCertified trace allowed
      value (.var key) seed subst) := by
  obtain ⟨hmerge, hafter⟩ :=
    h.operational.toAssignmentReconcileMergeLive hclass hinconsistent
  let hcore := hmerge.toHELiveMergeCertified.withCoreNonVarVarMatch hnonvar
  exact ⟨{
    toHELiveMatchMergeCoreCertified := hcore
    congruence := by
      change LeaBindingCongruence hmerge.after
        (Metta.Bindings.ofSubst subst)
      rw [hafter]
      exact h.congruence
  }⟩

/-- A two-value hidden equality conflict reconstructs the original equality
head after structural congruence is known for the reached accumulator. -/
theorem HELiveHiddenMatchStructuralCertified.toEqualityPairConflictCoreCongruent
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {seed : Bindings}
    {subst : Metta.Subst} {left right : String} {first second : Atom}
    (h : HELiveHiddenMatchStructuralCertified trace allowed first second
      (seed.addEquality left right) subst)
    (hvalues : (seed.addEquality left right).classValues left =
      [first, second])
    (hinconsistent : Bindings.valuesConsistent [first, second] = false)
    (hallowed :
      (EqualityClosure.edgeGraph allowed).Reachable left right) :
    Nonempty (HELiveMatchMergeCoreCongruentCertified trace allowed
      (.var left) (.var right) seed subst) := by
  obtain ⟨hmerge, hafter⟩ :=
    h.operational.toEqualityPairConflictMergeLive
      hvalues hinconsistent hallowed
  let hcore := hmerge.toHELiveMergeCertified.withCoreVarVarMatch hallowed
  exact ⟨{
    toHELiveMatchMergeCoreCertified := hcore
    congruence := by
      change LeaBindingCongruence hmerge.after
        (Metta.Bindings.ofSubst subst)
      rw [hafter]
      exact h.congruence
  }⟩

/-- Whole-class hidden equality reconciliation reconstructs the original
equality head at the same structural boundary. -/
theorem HELiveHiddenListMatchStructuralCertified.toEqualityClassConflictCoreCongruent
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {seed : Bindings}
    {subst : Metta.Subst} {left right : String}
    {first second third : Atom} {rest : List Atom}
    (h : HELiveHiddenListMatchStructuralCertified trace allowed
      (List.replicate (rest.length + 2) first)
      (second :: third :: rest) (seed.addEquality left right) subst)
    (hvalues : (seed.addEquality left right).classValues left =
      first :: second :: third :: rest)
    (hinconsistent : Bindings.valuesConsistent
      (first :: second :: third :: rest) = false)
    (hallowed :
      (EqualityClosure.edgeGraph allowed).Reachable left right) :
    Nonempty (HELiveMatchMergeCoreCongruentCertified trace allowed
      (.var left) (.var right) seed subst) := by
  obtain ⟨hmerge, hafter⟩ :=
    h.operational.toEqualityClassConflictMergeLive
      hvalues hinconsistent hallowed
  let hcore := hmerge.toHELiveMergeCertified.withCoreVarVarMatch hallowed
  exact ⟨{
    toHELiveMatchMergeCoreCertified := hcore
    congruence := by
      change LeaBindingCongruence hmerge.after
        (Metta.Bindings.ofSubst subst)
      rw [hafter]
      exact h.congruence
  }⟩

/-- Strong variable/non-variable head closure split exactly along the
projected Robinson dichotomy.  A strict residual is delegated to the fuel
recursion.  At a solved residual only the genuinely fresh case remains
external; no-change and both conflict forms are reconstructed here. -/
theorem HEProjectedTailHeadResidualPackage.exists_coreLiveVarNonVar_congruent_of_split
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    {state : HEProjectedCertifiedListResidualState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed}
    {key : String} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualPackage state (.var key) leftRest)
    {value : Atom} (hright : p.nextRight = value)
    (hnonvar : DeclMatchSpec.Atom.isVarB value = false)
    (hstrict : p.nextRemainingFuel < fuel →
      Nonempty (HELiveMatchMergeCoreCongruentCertified trace allowed
        (.var key) p.nextRight seed p.nextSubst))
    (hfreshSolved : seed.classValues key = [] →
      Metta.Unify.decomposeAll p.headWork = some [] →
      Nonempty (HELiveMatchMergeCoreCongruentCertified trace allowed
        (.var key) p.nextRight seed p.nextSubst))
    (hconflict : ∀ {first : Atom} {rest : List Atom},
      seed.classValues key = first :: rest →
      Bindings.valuesConsistent (first :: rest) = true →
      first ≠ value →
      Nonempty (HELiveHiddenMatchStructuralCertified trace allowed
        first value seed p.nextSubst))
    (hreconcile : ∀ {first : Atom} {rest : List Atom},
      seed.classValues key = first :: rest →
      Bindings.valuesConsistent (first :: rest) = false →
      Nonempty (HELiveHiddenListMatchStructuralCertified trace allowed
        (List.replicate (rest.length + 1) first) (rest ++ [value])
        seed p.nextSubst)) :
    Nonempty (HELiveMatchMergeCoreCongruentCertified trace allowed
      (.var key) p.nextRight seed p.nextSubst) := by
  rcases p.headSolved_or_strictResidual with hsolved | hlt
  · cases hclass : seed.classValues key with
    | nil => exact hfreshSolved hclass hsolved.1
    | cons first rest =>
        cases hconsistent : Bindings.valuesConsistent (first :: rest) with
        | false =>
            obtain ⟨inner⟩ := hreconcile hclass hconsistent
            exact (inner.toAssignmentReconcileCoreCongruent
              hclass hconsistent hnonvar).map
                (fun h => h.reindexRight hright.symm)
        | true =>
            by_cases hsame : first = value
            · exact p.exists_coreLiveVarNonVar_same_congruent hright hnonvar
                hclass hconsistent hsame hsolved.1
            · obtain ⟨inner⟩ := hconflict hclass hconsistent hsame
              exact (inner.toAssignmentConflictCoreCongruent
                hclass hconsistent hsame hnonvar).map
                  (fun h => h.reindexRight hright.symm)
  · exact hstrict hlt

/-- Symmetric non-variable/variable split closure. -/
theorem HEProjectedTailHeadResidualPackage.exists_coreLiveNonVarVar_congruent_of_split
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    {state : HEProjectedCertifiedListResidualState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed}
    {value : Atom} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualPackage state value leftRest)
    {key : String} (hright : p.nextRight = .var key)
    (hnonvar : DeclMatchSpec.Atom.isVarB value = false)
    (hstrict : p.nextRemainingFuel < fuel →
      Nonempty (HELiveMatchMergeCoreCongruentCertified trace allowed
        value p.nextRight seed p.nextSubst))
    (hfreshSolved : seed.classValues key = [] →
      Metta.Unify.decomposeAll p.headWork = some [] →
      Nonempty (HELiveMatchMergeCoreCongruentCertified trace allowed
        value p.nextRight seed p.nextSubst))
    (hconflict : ∀ {first : Atom} {rest : List Atom},
      seed.classValues key = first :: rest →
      Bindings.valuesConsistent (first :: rest) = true →
      first ≠ value →
      Nonempty (HELiveHiddenMatchStructuralCertified trace allowed
        first value seed p.nextSubst))
    (hreconcile : ∀ {first : Atom} {rest : List Atom},
      seed.classValues key = first :: rest →
      Bindings.valuesConsistent (first :: rest) = false →
      Nonempty (HELiveHiddenListMatchStructuralCertified trace allowed
        (List.replicate (rest.length + 1) first) (rest ++ [value])
        seed p.nextSubst)) :
    Nonempty (HELiveMatchMergeCoreCongruentCertified trace allowed
      value p.nextRight seed p.nextSubst) := by
  rcases p.headSolved_or_strictResidual with hsolved | hlt
  · cases hclass : seed.classValues key with
    | nil => exact hfreshSolved hclass hsolved.1
    | cons first rest =>
        cases hconsistent : Bindings.valuesConsistent (first :: rest) with
        | false =>
            obtain ⟨inner⟩ := hreconcile hclass hconsistent
            exact (inner.toNonVarVarReconcileCoreCongruent
              hclass hconsistent hnonvar).map
                (fun h => h.reindexRight hright.symm)
        | true =>
            by_cases hsame : first = value
            · exact p.exists_coreLiveNonVarVar_same_congruent hright hnonvar
                hclass hconsistent hsame hsolved.1
            · obtain ⟨inner⟩ := hconflict hclass hconsistent hsame
              exact (inner.toNonVarVarConflictCoreCongruent
                hclass hconsistent hsame hnonvar).map
                  (fun h => h.reindexRight hright.symm)
  · exact hstrict hlt

/-- Strong variable/equality closure with the same exact split.  Reflexive
and already-connected solved aliases are discharged locally.  A solved but
new consistent edge is exposed as the sole direct equality obligation; the
two inconsistent joined-class forms use hidden structural post-states. -/
theorem HEProjectedTailHeadResidualPackage.exists_coreLiveVarVar_congruent_of_split
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {leftAtoms rightAtoms : List Atom}
    {seed : Bindings}
    {state : HEProjectedCertifiedListResidualState trace allowed
      outerFuel front outerSubst fuel work subst result
        leftAtoms rightAtoms seed}
    {left : String} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualPackage state (.var left) leftRest)
    {right : String} (hright : p.nextRight = .var right)
    (hallowed :
      (EqualityClosure.edgeGraph allowed).Reachable left right)
    (hstrict : p.nextRemainingFuel < fuel →
      Nonempty (HELiveMatchMergeCoreCongruentCertified trace allowed
        (.var left) p.nextRight seed p.nextSubst))
    (hnewSolved : left ≠ right → right ∉ seed.eqClass left →
      Bindings.valuesConsistent
          ((seed.addEquality left right).classValues left) = true →
      Metta.Unify.decomposeAll p.headWork = some [] →
      Nonempty (HELiveMatchMergeCoreCongruentCertified trace allowed
        (.var left) p.nextRight seed p.nextSubst))
    (hpair : ∀ {first second : Atom},
      (seed.addEquality left right).classValues left = [first, second] →
      Bindings.valuesConsistent [first, second] = false →
      Nonempty (HELiveHiddenMatchStructuralCertified trace allowed
        first second (seed.addEquality left right) p.nextSubst))
    (hclass : ∀ {first second third : Atom} {rest : List Atom},
      (seed.addEquality left right).classValues left =
        first :: second :: third :: rest →
      Bindings.valuesConsistent
          (first :: second :: third :: rest) = false →
      Nonempty (HELiveHiddenListMatchStructuralCertified trace allowed
        (List.replicate (rest.length + 2) first)
        (second :: third :: rest) (seed.addEquality left right)
        p.nextSubst)) :
    Nonempty (HELiveMatchMergeCoreCongruentCertified trace allowed
      (.var left) p.nextRight seed p.nextSubst) := by
  rcases p.headSolved_or_strictResidual with hsolved | hlt
  · cases hconsistent : Bindings.valuesConsistent
        ((seed.addEquality left right).classValues left) with
    | true =>
        by_cases heq : left = right
        · subst right
          exact p.exists_coreLiveVarVar_reflexive_congruent
            hright hconsistent
        · by_cases hconnected : right ∈ seed.eqClass left
          · exact p.exists_coreLiveVarVar_connected_congruent
              hright hconnected hconsistent hallowed hsolved.1
          · exact hnewSolved heq hconnected hconsistent hsolved.1
    | false =>
        cases hvalues : (seed.addEquality left right).classValues left with
        | nil =>
            rw [hvalues] at hconsistent
            simp [Bindings.valuesConsistent] at hconsistent
        | cons first rest =>
            cases rest with
            | nil =>
                rw [hvalues] at hconsistent
                simp [Bindings.valuesConsistent] at hconsistent
            | cons second tail =>
                cases tail with
                | nil =>
                    rw [hvalues] at hconsistent
                    obtain ⟨inner⟩ := hpair hvalues hconsistent
                    exact (inner.toEqualityPairConflictCoreCongruent
                      hvalues hconsistent hallowed).map
                        (fun h => h.reindexRight hright.symm)
                | cons third rest =>
                    rw [hvalues] at hconsistent
                    obtain ⟨inner⟩ := hclass hvalues hconsistent
                    exact (inner.toEqualityClassConflictCoreCongruent
                      hvalues hconsistent hallowed).map
                        (fun h => h.reindexRight hright.symm)
  · exact hstrict hlt

/-! ## Hidden post-states as reverse merge realizations -/

/-- The structurally solved scalar assignment conflict is already the exact
reverse merge realization needed by the enclosing LeaTTa matcher branch. -/
theorem HELiveHiddenMatchStructuralCertified.toAssignmentConflictMergeRealization
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {seed : Bindings}
    {subst : Metta.Subst} {key : String} {value first : Atom}
    {rest : List Atom}
    (h : HELiveHiddenMatchStructuralCertified
      trace allowed first value seed subst)
    (hclass : seed.classValues key = first :: rest)
    (hconsistent : Bindings.valuesConsistent (first :: rest) = true)
    (hdifferent : first ≠ value) :
    LeaMergeCongruenceRealization seed
      (Bindings.empty.assign key value) (Metta.Bindings.ofSubst subst) := by
  obtain ⟨hlive, hafter⟩ :=
    h.operational.toAssignmentConflictMergeLive
      hclass hconsistent hdifferent
  refine ⟨hlive.after, hlive.mergeFuel, hlive.merge_mem, ?_⟩
  rw [hafter]
  exact h.congruence

/-- Class-wide assignment reconciliation companion. -/
theorem HELiveHiddenListMatchStructuralCertified.toAssignmentReconcileMergeRealization
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {seed : Bindings}
    {subst : Metta.Subst} {key : String} {value first : Atom}
    {rest : List Atom}
    (h : HELiveHiddenListMatchStructuralCertified trace allowed
      (List.replicate (rest.length + 1) first) (rest ++ [value])
      seed subst)
    (hclass : seed.classValues key = first :: rest)
    (hinconsistent : Bindings.valuesConsistent (first :: rest) = false) :
    LeaMergeCongruenceRealization seed
      (Bindings.empty.assign key value) (Metta.Bindings.ofSubst subst) := by
  obtain ⟨hlive, hafter⟩ :=
    h.operational.toAssignmentReconcileMergeLive hclass hinconsistent
  refine ⟨hlive.after, hlive.mergeFuel, hlive.merge_mem, ?_⟩
  rw [hafter]
  exact h.congruence

/-- Two-value equality-conflict companion. -/
theorem HELiveHiddenMatchStructuralCertified.toEqualityPairMergeRealization
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {seed : Bindings}
    {subst : Metta.Subst} {left right : String} {first second : Atom}
    (h : HELiveHiddenMatchStructuralCertified trace allowed first second
      (seed.addEquality left right) subst)
    (hvalues : (seed.addEquality left right).classValues left =
      [first, second])
    (hinconsistent : Bindings.valuesConsistent [first, second] = false)
    (hallowed :
      (EqualityClosure.edgeGraph allowed).Reachable left right) :
    LeaMergeCongruenceRealization seed
      (Bindings.empty.addEquality left right)
      (Metta.Bindings.ofSubst subst) := by
  obtain ⟨hlive, hafter⟩ :=
    h.operational.toEqualityPairConflictMergeLive
      hvalues hinconsistent hallowed
  refine ⟨hlive.after, hlive.mergeFuel, hlive.merge_mem, ?_⟩
  rw [hafter]
  exact h.congruence

/-- Whole-class equality-reconciliation companion. -/
theorem HELiveHiddenListMatchStructuralCertified.toEqualityClassMergeRealization
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {seed : Bindings}
    {subst : Metta.Subst} {left right : String}
    {first second third : Atom} {rest : List Atom}
    (h : HELiveHiddenListMatchStructuralCertified trace allowed
      (List.replicate (rest.length + 2) first)
      (second :: third :: rest) (seed.addEquality left right) subst)
    (hvalues : (seed.addEquality left right).classValues left =
      first :: second :: third :: rest)
    (hinconsistent : Bindings.valuesConsistent
      (first :: second :: third :: rest) = false)
    (hallowed :
      (EqualityClosure.edgeGraph allowed).Reachable left right) :
    LeaMergeCongruenceRealization seed
      (Bindings.empty.addEquality left right)
      (Metta.Bindings.ofSubst subst) := by
  obtain ⟨hlive, hafter⟩ :=
    h.operational.toEqualityClassConflictMergeLive
      hvalues hinconsistent hallowed
  refine ⟨hlive.after, hlive.mergeFuel, hlive.merge_mem, ?_⟩
  rw [hafter]
  exact h.congruence

/-- Variable/non-variable projected-head closure through the weakest hidden
conflict interface. -/
theorem HEProjectedTailHeadResidualSolutionPackage.exists_coreResidualVarNonVar_of_hiddenLiveConflicts
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    (covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed)
    {key : String} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state (.var key) leftRest)
    {value : Atom} (hright : p.nextRight = value)
    (hnonvar : DeclMatchSpec.Atom.isVarB value = false)
    (hconflict : ∀ {first : Atom} {rest : List Atom},
      seed.classValues key = first :: rest →
      Bindings.valuesConsistent (first :: rest) = true →
      first ≠ value →
      Nonempty (HELiveHiddenMatchResidualCertified trace allowed
        first value seed p.nextSubst))
    (hreconcile : ∀ {first : Atom} {rest : List Atom},
      seed.classValues key = first :: rest →
      Bindings.valuesConsistent (first :: rest) = false →
      Nonempty (HELiveHiddenListMatchResidualCertified trace allowed
        (List.replicate (rest.length + 1) first) (rest ++ [value])
        seed p.nextSubst)) :
    Nonempty (HELiveMatchMergeCoreResidualCertified trace allowed
      (.var key) p.nextRight seed p.nextSubst) := by
  cases hclass : seed.classValues key with
  | nil =>
      exact p.exists_coreResidualVarNonVar_fresh hright hnonvar
        (p.freshAssignmentEntry_of_originalCoverage
          covered.originalCoverage hright hnonvar) hclass
  | cons first rest =>
      cases hconsistent : Bindings.valuesConsistent (first :: rest) with
      | false =>
          obtain ⟨inner⟩ := hreconcile hclass hconsistent
          obtain ⟨hmerge, hafter⟩ :=
            inner.toAssignmentReconcileMergeLive hclass hconsistent
          let hcore : HELiveMatchMergeCoreCertified trace allowed
              (.var key) p.nextRight seed :=
            (hmerge.withCoreVarNonVarMatch hnonvar).reindexRight hright.symm
          exact ⟨{
            toHELiveMatchMergeCoreSolutionCertified :=
              hcore.withProjectedHeadSolutions p
            afterAssignmentsSound := by
              change LeaEliminationTraceAssignmentsSound
                hcore.liveMerge.after trace
              have hcoreAfter : hcore.liveMerge.after = hmerge.after :=
                HELiveMatchMergeCoreCertified.reindexRight_liveAfter
                  (hmerge.withCoreVarNonVarMatch hnonvar) hright.symm
              rw [hcoreAfter, hafter]
              exact inner.afterAssignmentsSound
          }⟩
      | true =>
          by_cases hsame : first = value
          · exact p.exists_coreResidualVarNonVar_same hright hnonvar
              hclass hconsistent hsame
          · obtain ⟨inner⟩ := hconflict hclass hconsistent hsame
            obtain ⟨hmerge, hafter⟩ :=
              inner.toAssignmentConflictMergeLive
                hclass hconsistent hsame
            let hcore : HELiveMatchMergeCoreCertified trace allowed
                (.var key) p.nextRight seed :=
              (hmerge.withCoreVarNonVarMatch hnonvar).reindexRight
                hright.symm
            exact ⟨{
              toHELiveMatchMergeCoreSolutionCertified :=
                hcore.withProjectedHeadSolutions p
              afterAssignmentsSound := by
                change LeaEliminationTraceAssignmentsSound
                  hcore.liveMerge.after trace
                have hcoreAfter : hcore.liveMerge.after = hmerge.after :=
                  HELiveMatchMergeCoreCertified.reindexRight_liveAfter
                    (hmerge.withCoreVarNonVarMatch hnonvar) hright.symm
                rw [hcoreAfter, hafter]
                exact inner.afterAssignmentsSound
            }⟩

/-- Symmetric non-variable/variable closure through the hidden interface. -/
theorem HEProjectedTailHeadResidualSolutionPackage.exists_coreResidualNonVarVar_of_hiddenLiveConflicts
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    (covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed)
    {value : Atom} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state value leftRest)
    {key : String} (hright : p.nextRight = .var key)
    (hnonvar : DeclMatchSpec.Atom.isVarB value = false)
    (hconflict : ∀ {first : Atom} {rest : List Atom},
      seed.classValues key = first :: rest →
      Bindings.valuesConsistent (first :: rest) = true →
      first ≠ value →
      Nonempty (HELiveHiddenMatchResidualCertified trace allowed
        first value seed p.nextSubst))
    (hreconcile : ∀ {first : Atom} {rest : List Atom},
      seed.classValues key = first :: rest →
      Bindings.valuesConsistent (first :: rest) = false →
      Nonempty (HELiveHiddenListMatchResidualCertified trace allowed
        (List.replicate (rest.length + 1) first) (rest ++ [value])
        seed p.nextSubst)) :
    Nonempty (HELiveMatchMergeCoreResidualCertified trace allowed
      value p.nextRight seed p.nextSubst) := by
  cases hclass : seed.classValues key with
  | nil =>
      exact p.exists_coreResidualNonVarVar_fresh hright hnonvar
        (p.freshNonVarVarEntry_of_originalCoverage
          covered.originalCoverage hright hnonvar) hclass
  | cons first rest =>
      cases hconsistent : Bindings.valuesConsistent (first :: rest) with
      | false =>
          obtain ⟨inner⟩ := hreconcile hclass hconsistent
          obtain ⟨hmerge, hafter⟩ :=
            inner.toAssignmentReconcileMergeLive hclass hconsistent
          let hcore : HELiveMatchMergeCoreCertified trace allowed
              value p.nextRight seed :=
            (hmerge.withCoreNonVarVarMatch hnonvar).reindexRight hright.symm
          exact ⟨{
            toHELiveMatchMergeCoreSolutionCertified :=
              hcore.withProjectedHeadSolutions p
            afterAssignmentsSound := by
              change LeaEliminationTraceAssignmentsSound
                hcore.liveMerge.after trace
              have hcoreAfter : hcore.liveMerge.after = hmerge.after :=
                HELiveMatchMergeCoreCertified.reindexRight_liveAfter
                  (hmerge.withCoreNonVarVarMatch hnonvar) hright.symm
              rw [hcoreAfter, hafter]
              exact inner.afterAssignmentsSound
          }⟩
      | true =>
          by_cases hsame : first = value
          · exact p.exists_coreResidualNonVarVar_same hright hnonvar
              hclass hconsistent hsame
          · obtain ⟨inner⟩ := hconflict hclass hconsistent hsame
            obtain ⟨hmerge, hafter⟩ :=
              inner.toAssignmentConflictMergeLive
                hclass hconsistent hsame
            let hcore : HELiveMatchMergeCoreCertified trace allowed
                value p.nextRight seed :=
              (hmerge.withCoreNonVarVarMatch hnonvar).reindexRight
                hright.symm
            exact ⟨{
              toHELiveMatchMergeCoreSolutionCertified :=
                hcore.withProjectedHeadSolutions p
              afterAssignmentsSound := by
                change LeaEliminationTraceAssignmentsSound
                  hcore.liveMerge.after trace
                have hcoreAfter : hcore.liveMerge.after = hmerge.after :=
                  HELiveMatchMergeCoreCertified.reindexRight_liveAfter
                    (hmerge.withCoreNonVarVarMatch hnonvar) hright.symm
                rw [hcoreAfter, hafter]
                exact inner.afterAssignmentsSound
            }⟩

/-- Variable/variable projected-head closure through hidden pair/class
reconciliation callbacks. -/
theorem HEProjectedTailHeadResidualSolutionPackage.exists_coreResidualVarVar_of_hiddenLiveConflicts
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {leftAtoms rightAtoms : List Atom}
    {seed : Bindings}
    (covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result
        leftAtoms rightAtoms seed)
    {left : String} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state (.var left) leftRest)
    {right : String} (hright : p.nextRight = .var right)
    (hallowed :
      (EqualityClosure.edgeGraph allowed).Reachable left right)
    (hpair : ∀ {first second : Atom},
      (seed.addEquality left right).classValues left = [first, second] →
      Bindings.valuesConsistent [first, second] = false →
      Nonempty (HELiveHiddenMatchResidualCertified trace allowed
        first second (seed.addEquality left right) p.nextSubst))
    (hclass : ∀ {first second third : Atom} {rest : List Atom},
      (seed.addEquality left right).classValues left =
        first :: second :: third :: rest →
      Bindings.valuesConsistent
        (first :: second :: third :: rest) = false →
      Nonempty (HELiveHiddenListMatchResidualCertified trace allowed
        (List.replicate (rest.length + 2) first)
        (second :: third :: rest) (seed.addEquality left right)
        p.nextSubst)) :
    Nonempty (HELiveMatchMergeCoreResidualCertified trace allowed
      (.var left) p.nextRight seed p.nextSubst) := by
  cases hconsistent : Bindings.valuesConsistent
      ((seed.addEquality left right).classValues left) with
  | true =>
      exact p.exists_coreResidualVarVar_consistent
        hright hconsistent hallowed
  | false =>
      cases hvalues : (seed.addEquality left right).classValues left with
      | nil =>
          rw [hvalues] at hconsistent
          simp [Bindings.valuesConsistent] at hconsistent
      | cons first rest =>
          cases rest with
          | nil =>
              rw [hvalues] at hconsistent
              simp [Bindings.valuesConsistent] at hconsistent
          | cons second tail =>
              cases tail with
              | nil =>
                  rw [hvalues] at hconsistent
                  obtain ⟨inner⟩ := hpair hvalues hconsistent
                  obtain ⟨hmerge, hafter⟩ :=
                    inner.toEqualityPairConflictMergeLive
                      hvalues hconsistent hallowed
                  let hcore : HELiveMatchMergeCoreCertified trace allowed
                      (.var left) p.nextRight seed :=
                    (hmerge.withCoreVarVarMatch hallowed).reindexRight
                      hright.symm
                  exact ⟨{
                    toHELiveMatchMergeCoreSolutionCertified :=
                      hcore.withProjectedHeadSolutions p
                    afterAssignmentsSound := by
                      change LeaEliminationTraceAssignmentsSound
                        hcore.liveMerge.after trace
                      have hcoreAfter : hcore.liveMerge.after = hmerge.after :=
                        HELiveMatchMergeCoreCertified.reindexRight_liveAfter
                          (hmerge.withCoreVarVarMatch hallowed) hright.symm
                      rw [hcoreAfter, hafter]
                      exact inner.afterAssignmentsSound
                  }⟩
              | cons third rest =>
                  rw [hvalues] at hconsistent
                  obtain ⟨inner⟩ := hclass hvalues hconsistent
                  obtain ⟨hmerge, hafter⟩ :=
                    inner.toEqualityClassConflictMergeLive
                      hvalues hconsistent hallowed
                  let hcore : HELiveMatchMergeCoreCertified trace allowed
                      (.var left) p.nextRight seed :=
                    (hmerge.withCoreVarVarMatch hallowed).reindexRight
                      hright.symm
                  exact ⟨{
                    toHELiveMatchMergeCoreSolutionCertified :=
                      hcore.withProjectedHeadSolutions p
                    afterAssignmentsSound := by
                      change LeaEliminationTraceAssignmentsSound
                        hcore.liveMerge.after trace
                      have hcoreAfter : hcore.liveMerge.after = hmerge.after :=
                        HELiveMatchMergeCoreCertified.reindexRight_liveAfter
                          (hmerge.withCoreVarVarMatch hallowed) hright.symm
                      rw [hcoreAfter, hafter]
                      exact inner.afterAssignmentsSound
                  }⟩

/-! ## Semantic-size matcher/merge kernel -/

/-- One certified value insertion, including the state invariants needed by
the next runtime-ordered insertion.  The certificates are indexed by the
actual selected `AddVarBindingRel`; no global matcher hypothesis appears. -/
structure HESatisfiedAddBindingCertified
    (valuation : String → Metta.Atom)
    (trace : List (String × Metta.Atom))
    (allowed : List (String × String))
    (seed : Bindings) (key : String) (value : Atom) where
  after : Bindings
  addRel : AddVarBindingRel seed key value after
  traceSound : AddVarBindingTraceSound trace addRel
  equalitySound : AddVarBindingEqualityClosureBoundSound allowed addRel
  satisfied : HEBindingSatisfied valuation after
  assignmentsNonVariable : HEAssignmentsNonVariable after
  equalityBound : HEEqualityClosureBound after allowed

/-- Equality-insertion companion of `HESatisfiedAddBindingCertified`. -/
structure HESatisfiedAddEqualityCertified
    (valuation : String → Metta.Atom)
    (trace : List (String × Metta.Atom))
    (allowed : List (String × String))
    (seed : Bindings) (left right : String) where
  after : Bindings
  addRel : AddVarEqualityRel seed left right after
  traceSound : AddVarEqualityTraceSound trace addRel
  equalitySound : AddVarEqualityEqualityClosureBoundSound allowed addRel
  satisfied : HEBindingSatisfied valuation after
  assignmentsNonVariable : HEAssignmentsNonVariable after
  equalityBound : HEEqualityClosureBound after allowed

/-- Certified result of one complete assignment-then-equality HE merge.
Besides the concrete relation and its two derivation-local certificates, the
reached state retains exactly the invariants consumed by a subsequent live
merge. -/
structure HESatisfiedMergeCertified
    (valuation : String → Metta.Atom)
    (trace : List (String × Metta.Atom))
    (allowed : List (String × String))
    (seed right : Bindings) where
  after : Bindings
  mergeRel : MergeRel seed right after
  traceSound : MergeTraceSound trace mergeRel
  equalitySound : MergeEqualityClosureBoundSound allowed mergeRel
  satisfied : HEBindingSatisfied valuation after
  assignmentsNonVariable : HEAssignmentsNonVariable after
  assignmentsSound : LeaEliminationTraceAssignmentsSound after trace
  equalityBound : HEEqualityClosureBound after allowed

/-- Convert a relational certified merge into the executable live package
without changing the selected output or either certificate. -/
noncomputable def HESatisfiedMergeCertified.toLive
    {valuation : String → Metta.Atom}
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {seed right : Bindings}
    (h : HESatisfiedMergeCertified valuation trace allowed seed right) :
    HELiveMergeCertified trace allowed seed right := by
  let hexec := mergeBindings_complete h.mergeRel
  let fuel := Classical.choose hexec
  have hmem : h.after ∈ mergeBindings seed right fuel :=
    Classical.choose_spec hexec
  exact {
    after := h.after
    mergeFuel := fuel
    merge_mem := hmem
    traceSound := by
      simpa only [Subsingleton.elim
        (mergeBindings_sound hmem) h.mergeRel] using h.traceSound
    equalitySound := by
      simpa only [Subsingleton.elim
        (mergeBindings_sound hmem) h.mergeRel] using h.equalitySound
  }

/-- Fold certified insertion callbacks in the exact runtime order prescribed
by `MergeRel`.  This is the certificate-preserving analogue of
`satisfiedMergeRelCompleteBelow_of_adds`: it performs no matching itself and
therefore isolates all genuine recursion in the two insertion callbacks. -/
theorem exists_satisfiedMergeCertified_of_adds
    {valuation : String → Metta.Atom}
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {bound : Nat}
    (haddValue : ∀ {seed : Bindings} {key : String} {value : Atom},
      HEBindingSatisfied valuation seed →
      HEAssignmentsNonVariable seed →
      HEEqualityClosureBound seed allowed →
      DeclMatchSpec.Atom.isVarB value = false →
      valuation key = applyClassSolution valuation (toLeaTTaAtom value) →
      (valuation key).size < bound →
      HESolutionAtomSize valuation value < bound →
      Nonempty (HESatisfiedAddBindingCertified
        valuation trace allowed seed key value))
    (haddEquality : ∀ {seed : Bindings} {left right : String},
      HEBindingSatisfied valuation seed →
      HEAssignmentsNonVariable seed →
      HEEqualityClosureBound seed allowed →
      (EqualityClosure.edgeGraph allowed).Reachable left right →
      valuation left = valuation right →
      (valuation left).size < bound →
      (valuation right).size < bound →
      Nonempty (HESatisfiedAddEqualityCertified
        valuation trace allowed seed left right))
    {seed right : Bindings}
    (hseed : HEBindingSatisfied valuation seed)
    (hseedNonvar : HEAssignmentsNonVariable seed)
    (hseedSound : LeaEliminationTraceAssignmentsSound seed trace)
    (hseedBound : HEEqualityClosureBound seed allowed)
    (hright : HEBindingSatisfied valuation right)
    (hrightNonvar : HEAssignmentsNonVariable right)
    (hrightSound : LeaEliminationTraceAssignmentsSound right trace)
    (hrightEqualityBound : HEEqualityClosureBound right allowed)
    (hrightBound : HEBindingSolutionSizeBound valuation right bound) :
    Nonempty (HESatisfiedMergeCertified
      valuation trace allowed seed right) := by
  have foldAssignments : ∀
      (assignments : List (String × Atom)) (before : Bindings),
      HEBindingSatisfied valuation before →
      HEAssignmentsNonVariable before →
      HEEqualityClosureBound before allowed →
      (∀ key value, (key, value) ∈ assignments →
        valuation key =
          applyClassSolution valuation (toLeaTTaAtom value)) →
      (∀ key value, (key, value) ∈ assignments →
        DeclMatchSpec.Atom.isVarB value = false) →
      (∀ key value, (key, value) ∈ assignments →
        (valuation key).size < bound ∧
          HESolutionAtomSize valuation value < bound) →
      ∃ after, ∃ hfold : MergeAssignsRel before assignments after,
        MergeAssignsTraceSound trace hfold ∧
          MergeAssignsEqualityClosureBoundSound allowed hfold ∧
            HEBindingSatisfied valuation after ∧
              HEAssignmentsNonVariable after ∧
                HEEqualityClosureBound after allowed := by
    intro assignments
    induction assignments with
    | nil =>
        intro before hbefore hnonvar hequality _ _ _
        exact ⟨before, .nil, .nil, .nil, hbefore, hnonvar,
          hequality⟩
    | cons assignment rest ih =>
        rcases assignment with ⟨key, value⟩
        intro before hbefore hnonvar hequality hsat hvalues hbounds
        obtain ⟨head⟩ := haddValue hbefore hnonvar hequality
          (hvalues key value (by simp))
          (hsat key value (by simp))
          (hbounds key value (by simp)).1
          (hbounds key value (by simp)).2
        have hrestSat : ∀ restKey restValue,
            (restKey, restValue) ∈ rest →
            valuation restKey = applyClassSolution valuation
              (toLeaTTaAtom restValue) := by
          intro restKey restValue hmem
          exact hsat restKey restValue (by simp [hmem])
        have hrestValues : ∀ restKey restValue,
            (restKey, restValue) ∈ rest →
            DeclMatchSpec.Atom.isVarB restValue = false := by
          intro restKey restValue hmem
          exact hvalues restKey restValue (by simp [hmem])
        have hrestBounds : ∀ restKey restValue,
            (restKey, restValue) ∈ rest →
            (valuation restKey).size < bound ∧
              HESolutionAtomSize valuation restValue < bound := by
          intro restKey restValue hmem
          exact hbounds restKey restValue (by simp [hmem])
        obtain ⟨after, htail, htailTrace, htailEquality,
            hafterSat, hafterNonvar, hafterBound⟩ :=
          ih head.after head.satisfied head.assignmentsNonVariable
            head.equalityBound hrestSat hrestValues hrestBounds
        exact ⟨after, .cons head.addRel htail,
          .cons head.traceSound htailTrace,
          .cons head.equalitySound htailEquality,
          hafterSat, hafterNonvar, hafterBound⟩
  have foldEqualities : ∀
      (equalities : List (String × String)) (before : Bindings),
      HEBindingSatisfied valuation before →
      HEAssignmentsNonVariable before →
      HEEqualityClosureBound before allowed →
      (∀ left right, (left, right) ∈ equalities →
        (EqualityClosure.edgeGraph allowed).Reachable left right) →
      (∀ left right, (left, right) ∈ equalities →
        valuation left = valuation right) →
      (∀ left right, (left, right) ∈ equalities →
        (valuation left).size < bound ∧
          (valuation right).size < bound) →
      ∃ after, ∃ hfold : MergeEqsRel before equalities after,
        MergeEqsTraceSound trace hfold ∧
          MergeEqsEqualityClosureBoundSound allowed hfold ∧
            HEBindingSatisfied valuation after ∧
              HEAssignmentsNonVariable after ∧
                HEEqualityClosureBound after allowed := by
    intro equalities
    induction equalities with
    | nil =>
        intro before hbefore hnonvar hequality _ _ _
        exact ⟨before, .nil, .nil, .nil, hbefore, hnonvar,
          hequality⟩
    | cons equality rest ih =>
        rcases equality with ⟨left, rightKey⟩
        intro before hbefore hnonvar hequality hallowed hsat hbounds
        obtain ⟨head⟩ := haddEquality hbefore hnonvar hequality
          (hallowed left rightKey (by simp))
          (hsat left rightKey (by simp))
          (hbounds left rightKey (by simp)).1
          (hbounds left rightKey (by simp)).2
        have hrestSat : ∀ restLeft restRight,
            (restLeft, restRight) ∈ rest →
            valuation restLeft = valuation restRight := by
          intro restLeft restRight hmem
          exact hsat restLeft restRight (by simp [hmem])
        have hrestAllowed : ∀ restLeft restRight,
            (restLeft, restRight) ∈ rest →
            (EqualityClosure.edgeGraph allowed).Reachable
              restLeft restRight := by
          intro restLeft restRight hmem
          exact hallowed restLeft restRight (by simp [hmem])
        have hrestBounds : ∀ restLeft restRight,
            (restLeft, restRight) ∈ rest →
            (valuation restLeft).size < bound ∧
              (valuation restRight).size < bound := by
          intro restLeft restRight hmem
          exact hbounds restLeft restRight (by simp [hmem])
        obtain ⟨after, htail, htailTrace, htailEquality,
            hafterSat, hafterNonvar, hafterBound⟩ :=
          ih head.after head.satisfied head.assignmentsNonVariable
            head.equalityBound hrestAllowed hrestSat hrestBounds
        exact ⟨after, .cons head.addRel htail,
          .cons head.traceSound htailTrace,
          .cons head.equalitySound htailEquality,
          hafterSat, hafterNonvar, hafterBound⟩
  obtain ⟨middle, hassignments, hassignmentsTrace, hassignmentsEquality,
      hmiddleSat, hmiddleNonvar, hmiddleBound⟩ :=
    foldAssignments right.assignments seed hseed hseedNonvar
      hseedBound
      (fun key value hmem => hright.1 key value hmem)
      (fun key value hmem =>
        hrightNonvar.isVarB_eq_false_of_assignment hmem)
      (fun key value hmem => hrightBound.1 key value hmem)
  obtain ⟨after, hequalities, hequalitiesTrace, hequalitiesEquality,
      hafterSat, hafterNonvar, hafterBound⟩ :=
    foldEqualities right.equalities middle hmiddleSat hmiddleNonvar
      hmiddleBound
      (fun left rightKey hmem => hrightEqualityBound.edge hmem)
      (fun left rightKey hmem => hright.2 left rightKey hmem)
      (fun left rightKey hmem => hrightBound.2 left rightKey hmem)
  let hmerge : MergeRel seed right after :=
    .mk hassignments hequalities
  let htrace : MergeTraceSound trace hmerge :=
    .mk hassignmentsTrace hequalitiesTrace
  exact ⟨{
    after := after
    mergeRel := hmerge
    traceSound := htrace
    equalitySound := .mk hassignmentsEquality hequalitiesEquality
    satisfied := hafterSat
    assignmentsNonVariable := hafterNonvar
    assignmentsSound :=
      mergeRel_assignmentsSound_of_traceSound
        htrace hseedSound hrightSound
    equalityBound := hafterBound
  }⟩

/-- Completeness of merging one semantically bounded right record into an
arbitrary satisfying live seed.  Only the right record is bounded: unrelated
payloads already present in the seed cannot participate in a conflict unless
they lie in the class of a bounded right-hand key. -/
def HESatisfiedMergeRelCompleteBelow
    (valuation : String → Metta.Atom) (bound : Nat) : Prop :=
  ∀ {seed right : Bindings},
    HEBindingSatisfied valuation seed →
    HEAssignmentsNonVariable seed →
    HEBindingSatisfied valuation right →
    HEAssignmentsNonVariable right →
    HEBindingSolutionSizeBound valuation right bound →
    ∃ out, MergeRel seed right out ∧
      HEBindingSatisfied valuation out ∧
        HEAssignmentsNonVariable out

private theorem matchRel_satisfied_of_equation
    {valuation : String → Metta.Atom} {left right : Atom} {out : Bindings}
    (hmatch : DeclMatchSpec.MatchRel left right out)
    (hequation : HEAtomEquationSatisfied valuation left right) :
    HEBindingSatisfied valuation out := by
  obtain ⟨fuel, hmem⟩ := DeclMatchSpec.matchAtoms_complete hmatch
  apply (matchAtoms_solution_iff hmem valuation).mpr
  simpa [HEAtomEquationSatisfied, MettaEquationSatisfied] using hequation

/-- Bounded matcher/list-matcher completeness, assuming only bounded merge
completeness at the same ceiling.  The simultaneous structural recursion is
the exact shape of `MatchRel.expr` and `MatchListAccRel.cons`: every child is
matched from empty and merged separately into the live accumulator. -/
private theorem boundedMatcherPack
    {valuation : String → Metta.Atom} {bound : Nat}
    (hmerge : HESatisfiedMergeRelCompleteBelow valuation bound) :
    (∀ {left right : Atom},
      HEAtomEquationSatisfied valuation left right →
      HESolutionAtomSize valuation left < bound →
      HESolutionAtomSize valuation right < bound →
      ∃ out, DeclMatchSpec.MatchRel left right out ∧
        HEBindingSatisfied valuation out ∧
          HEAssignmentsNonVariable out ∧
            HEBindingSolutionSizeBound valuation out bound) ∧
    (∀ {lefts rights : List Atom} {seed : Bindings},
      HEBindingSatisfied valuation seed →
      HEAssignmentsNonVariable seed →
      HEBindingSolutionSizeBound valuation seed bound →
      MettaAtomListsSatisfied valuation
        (toLeaTTaAtoms lefts) (toLeaTTaAtoms rights) →
      HESolutionAtomsSizeBound valuation lefts bound →
      HESolutionAtomsSizeBound valuation rights bound →
      ∃ out, DeclMatchSpec.MatchListAccRel lefts rights seed out ∧
        HEBindingSatisfied valuation out ∧
          HEAssignmentsNonVariable out ∧
            HEBindingSolutionSizeBound valuation out bound) := by
  let AtomGoal : Atom → Prop := fun left =>
    ∀ {right : Atom},
      HEAtomEquationSatisfied valuation left right →
      HESolutionAtomSize valuation left < bound →
      HESolutionAtomSize valuation right < bound →
      ∃ out, DeclMatchSpec.MatchRel left right out ∧
        HEBindingSatisfied valuation out ∧
          HEAssignmentsNonVariable out ∧
            HEBindingSolutionSizeBound valuation out bound
  let ListGoal : List Atom → Prop := fun lefts =>
    ∀ {rights : List Atom} {seed : Bindings},
      HEBindingSatisfied valuation seed →
      HEAssignmentsNonVariable seed →
      HEBindingSolutionSizeBound valuation seed bound →
      MettaAtomListsSatisfied valuation
        (toLeaTTaAtoms lefts) (toLeaTTaAtoms rights) →
      HESolutionAtomsSizeBound valuation lefts bound →
      HESolutionAtomsSizeBound valuation rights bound →
      ∃ out, DeclMatchSpec.MatchListAccRel lefts rights seed out ∧
        HEBindingSatisfied valuation out ∧
          HEAssignmentsNonVariable out ∧
            HEBindingSolutionSizeBound valuation out bound
  have leaf : ∀ {left right : Atom},
      HEAtomEquationSatisfied valuation left right →
      ¬ BothExpressions left right →
      HESolutionAtomSize valuation left < bound →
      HESolutionAtomSize valuation right < bound →
      ∃ out, DeclMatchSpec.MatchRel left right out ∧
        HEBindingSatisfied valuation out ∧
          HEAssignmentsNonVariable out ∧
            HEBindingSolutionSizeBound valuation out bound := by
    intro left right hequation hleaf hleft hright
    obtain ⟨out, hmatch⟩ :=
      exists_matchRel_of_solution_leaf ⟨valuation, hequation⟩ hleaf
    exact ⟨out, hmatch,
      matchRel_satisfied_of_equation hmatch hequation,
      heAssignmentsNonVariable_of_matchRel hmatch,
      matchRel_solutionSizeBound hmatch hleft hright⟩
  have hrec : ∀ left, AtomGoal left := by
    apply Atom.rec (motive_1 := AtomGoal) (motive_2 := ListGoal)
    · intro symbol right hequation hleft hright
      exact leaf hequation (by simp [BothExpressions]) hleft hright
    · intro name right hequation hleft hright
      exact leaf hequation (by simp [BothExpressions]) hleft hright
    · intro ground right hequation hleft hright
      exact leaf hequation (by simp [BothExpressions]) hleft hright
    · intro lefts hlefts right hequation hleft hright
      cases right with
      | symbol symbol =>
          exact leaf hequation (by simp [BothExpressions]) hleft hright
      | var name =>
          exact leaf hequation (by simp [BothExpressions]) hleft hright
      | grounded ground =>
          exact leaf hequation (by simp [BothExpressions]) hleft hright
      | expression rights =>
          have hlists : MettaAtomListsSatisfied valuation
              (toLeaTTaAtoms lefts) (toLeaTTaAtoms rights) := by
            simpa [HEAtomEquationSatisfied, MettaAtomListsSatisfied,
              toLeaTTaAtom, applyClassSolution] using hequation
          obtain ⟨out, hlist, houtSat, houtNonvar, houtBound⟩ :=
            hlefts (seed := Bindings.empty)
              ((hesat_empty_iff valuation).mpr trivial)
              (by simp [HEAssignmentsNonVariable, Bindings.empty])
              (heBindingSolutionSizeBound_empty valuation bound)
              hlists
              (heSolutionAtomsSizeBound_of_expression_lt valuation hleft)
              (heSolutionAtomsSizeBound_of_expression_lt valuation hright)
          exact ⟨out, .expr hlist, houtSat, houtNonvar, houtBound⟩
    · intro rights seed hseed hseedNonvar hseedBound hlists
        hleftsBound hrightsBound
      cases rights with
      | nil =>
          exact ⟨seed, .nil, hseed, hseedNonvar, hseedBound⟩
      | cons right rights =>
          simp [MettaAtomListsSatisfied, toLeaTTaAtoms] at hlists
    · intro left lefts hleft hlefts rights seed hseed hseedNonvar
        hseedBound hlists hleftsBound hrightsBound
      cases rights with
      | nil =>
          simp [MettaAtomListsSatisfied, toLeaTTaAtoms] at hlists
      | cons right rights =>
          have hequations :
              HEAtomEquationSatisfied valuation left right ∧
                MettaAtomListsSatisfied valuation
                  (toLeaTTaAtoms lefts) (toLeaTTaAtoms rights) := by
            simpa [HEAtomEquationSatisfied, MettaAtomListsSatisfied,
              toLeaTTaAtoms] using hlists
          obtain ⟨matched, hmatched, hmatchedSat, hmatchedNonvar,
              hmatchedBound⟩ :=
            hleft hequations.1 hleftsBound.head hrightsBound.head
          obtain ⟨next, hmergeRel, hnextSat, hnextNonvar⟩ :=
            hmerge hseed hseedNonvar hmatchedSat hmatchedNonvar
              hmatchedBound
          obtain ⟨mergeFuel, hmergeMem⟩ :=
            mergeBindings_complete hmergeRel
          have hnextBound :
              HEBindingSolutionSizeBound valuation next bound :=
            mergeRel_solutionSizeBound hmergeRel hseedBound hmatchedBound
          obtain ⟨out, htail, houtSat, houtNonvar, houtBound⟩ :=
            hlefts hnextSat hnextNonvar hnextBound hequations.2
              hleftsBound.tail hrightsBound.tail
          exact ⟨out, .cons hmatched hmergeMem htail,
            houtSat, houtNonvar, houtBound⟩
  refine ⟨?_, ?_⟩
  · intro left right hequation hleft hright
    exact hrec left hequation hleft hright
  · intro lefts rights seed hseed hseedNonvar hseedBound hlists
      hleftsBound hrightsBound
    induction lefts generalizing rights seed with
    | nil =>
        cases rights with
        | nil => exact ⟨seed, .nil, hseed, hseedNonvar, hseedBound⟩
        | cons right rights =>
            simp [MettaAtomListsSatisfied, toLeaTTaAtoms] at hlists
    | cons left lefts ih =>
        cases rights with
        | nil =>
            simp [MettaAtomListsSatisfied, toLeaTTaAtoms] at hlists
        | cons right rights =>
            have hequations :
                HEAtomEquationSatisfied valuation left right ∧
                  MettaAtomListsSatisfied valuation
                    (toLeaTTaAtoms lefts) (toLeaTTaAtoms rights) := by
              simpa [HEAtomEquationSatisfied, MettaAtomListsSatisfied,
                toLeaTTaAtoms] using hlists
            obtain ⟨matched, hmatched, hmatchedSat, hmatchedNonvar,
                hmatchedBound⟩ :=
              hrec left hequations.1 hleftsBound.head hrightsBound.head
            obtain ⟨next, hmergeRel, hnextSat, hnextNonvar⟩ :=
              hmerge hseed hseedNonvar hmatchedSat hmatchedNonvar
                hmatchedBound
            obtain ⟨mergeFuel, hmergeMem⟩ :=
              mergeBindings_complete hmergeRel
            have hnextBound :
                HEBindingSolutionSizeBound valuation next bound :=
              mergeRel_solutionSizeBound hmergeRel hseedBound hmatchedBound
            obtain ⟨out, htail, houtSat, houtNonvar, houtBound⟩ :=
              ih (rights := rights) (seed := next) hnextSat hnextNonvar
                hnextBound hequations.2 hleftsBound.tail hrightsBound.tail
            exact ⟨out, .cons hmatched hmergeMem htail,
              houtSat, houtNonvar, houtBound⟩

/-- Expression-root specialization.  The root itself may sit exactly at the
ceiling; every child is strictly smaller, so the produced binding record is
strictly bounded by the semantic size of the interpreted expression. -/
theorem exists_expressionMatchRel_solutionSizeBound
    {valuation : String → Metta.Atom} {lefts rights : List Atom}
    {bound : Nat}
    (hmerge : HESatisfiedMergeRelCompleteBelow valuation bound)
    (hequation : HEAtomEquationSatisfied valuation
      (.expression lefts) (.expression rights))
    (hleftSize : HESolutionAtomSize valuation (.expression lefts) = bound)
    (hrightSize : HESolutionAtomSize valuation (.expression rights) = bound) :
    ∃ out, DeclMatchSpec.MatchRel (.expression lefts) (.expression rights) out ∧
      HEBindingSatisfied valuation out ∧
        HEAssignmentsNonVariable out ∧
          HEBindingSolutionSizeBound valuation out bound := by
  have hlists : MettaAtomListsSatisfied valuation
      (toLeaTTaAtoms lefts) (toLeaTTaAtoms rights) := by
    simpa [HEAtomEquationSatisfied, MettaAtomListsSatisfied,
      toLeaTTaAtom, applyClassSolution] using hequation
  have hleftBound : HESolutionAtomsSizeBound valuation lefts bound := by
    intro atom hmem
    rw [← hleftSize]
    exact heSolutionAtomSize_lt_expression_of_mem valuation hmem
  have hrightBound : HESolutionAtomsSizeBound valuation rights bound := by
    intro atom hmem
    rw [← hrightSize]
    exact heSolutionAtomSize_lt_expression_of_mem valuation hmem
  obtain ⟨out, hlist, houtSat, houtNonvar, houtBound⟩ :=
    (boundedMatcherPack hmerge).2
      ((hesat_empty_iff valuation).mpr trivial)
      (by simp [HEAssignmentsNonVariable, Bindings.empty])
      (heBindingSolutionSizeBound_empty valuation bound)
      hlists hleftBound hrightBound
  exact ⟨out, .expr hlist, houtSat, houtNonvar, houtBound⟩

private theorem addVarBindingRel_satisfied
    {valuation : String → Metta.Atom} {seed out : Bindings}
    {key : String} {value : Atom}
    (hadd : AddVarBindingRel seed key value out)
    (hseed : HEBindingSatisfied valuation seed)
    (hvalue : valuation key =
      applyClassSolution valuation (toLeaTTaAtom value)) :
    HEBindingSatisfied valuation out := by
  obtain ⟨fuel, hmem⟩ := addVarBinding_complete hadd
  exact (addVarBinding_solution_iff hmem valuation).mpr ⟨hseed, hvalue⟩

private theorem addVarEqualityRel_satisfied
    {valuation : String → Metta.Atom} {seed out : Bindings}
    {left right : String}
    (hadd : AddVarEqualityRel seed left right out)
    (hseed : HEBindingSatisfied valuation seed)
    (hequality : valuation left = valuation right) :
    HEBindingSatisfied valuation out := by
  obtain ⟨fuel, hmem⟩ := addVarEquality_complete hadd
  exact (addVarEquality_solution_iff hmem valuation).mpr
    ⟨hseed, hequality⟩

/-- Certified nonrecursive fresh-assignment branch. -/
def HESatisfiedAddBindingCertified.fresh
    {valuation : String → Metta.Atom}
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {seed : Bindings}
    {key : String} {value : Atom}
    (hclass : seed.classValues key = [])
    (hseed : HEBindingSatisfied valuation seed)
    (hseedNonvar : HEAssignmentsNonVariable seed)
    (hseedBound : HEEqualityClosureBound seed allowed)
    (hvalueNonvar : DeclMatchSpec.Atom.isVarB value = false)
    (hvalue : valuation key =
      applyClassSolution valuation (toLeaTTaAtom value)) :
    HESatisfiedAddBindingCertified
      valuation trace allowed seed key value := by
  let hadd : AddVarBindingRel seed key value (seed.assign key value) :=
    .fresh hclass
  exact {
    after := seed.assign key value
    addRel := hadd
    traceSound := by
      simpa only [Subsingleton.elim
        (AddVarBindingRel.fresh hclass) hadd] using
          (AddVarBindingTraceSound.fresh
            (trace := trace) (hclass := hclass))
    equalitySound := by
      simpa only [Subsingleton.elim
        (AddVarBindingRel.fresh hclass) hadd] using
          (AddVarBindingEqualityClosureBoundSound.fresh
            (allowed := allowed) (hclass := hclass))
    satisfied := addVarBindingRel_satisfied hadd hseed hvalue
    assignmentsNonVariable := hseedNonvar.assign hvalueNonvar
    equalityBound := hseedBound.assign key value
  }

/-- Certified nonrecursive already-present assignment branch. -/
def HESatisfiedAddBindingCertified.same
    {valuation : String → Metta.Atom}
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {seed : Bindings}
    {key : String} {value first : Atom} {rest : List Atom}
    (hclass : seed.classValues key = first :: rest)
    (hconsistent : Bindings.valuesConsistent (first :: rest) = true)
    (hsame : first = value)
    (hseed : HEBindingSatisfied valuation seed)
    (hseedNonvar : HEAssignmentsNonVariable seed)
    (hseedBound : HEEqualityClosureBound seed allowed) :
    HESatisfiedAddBindingCertified
      valuation trace allowed seed key value := by
  let hadd : AddVarBindingRel seed key value seed :=
    .same hclass hconsistent hsame
  exact {
    after := seed
    addRel := hadd
    traceSound := by
      simpa only [Subsingleton.elim
        (AddVarBindingRel.same hclass hconsistent hsame) hadd] using
          (AddVarBindingTraceSound.same
            (trace := trace) (hclass := hclass)
            (hconsistent := hconsistent) (hsame := hsame))
    equalitySound := by
      simpa only [Subsingleton.elim
        (AddVarBindingRel.same hclass hconsistent hsame) hadd] using
          (AddVarBindingEqualityClosureBoundSound.same
            (allowed := allowed) (hclass := hclass)
            (hconsistent := hconsistent) (hsame := hsame))
    satisfied := hseed
    assignmentsNonVariable := hseedNonvar
    equalityBound := hseedBound
  }

/-- Certified nonrecursive consistent-equality branch. -/
def HESatisfiedAddEqualityCertified.consistent
    {valuation : String → Metta.Atom}
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {seed : Bindings}
    {left right : String}
    (hconsistent : Bindings.valuesConsistent
      ((seed.addEquality left right).classValues left) = true)
    (hseed : HEBindingSatisfied valuation seed)
    (hseedNonvar : HEAssignmentsNonVariable seed)
    (hseedBound : HEEqualityClosureBound seed allowed)
    (hallowed :
      (EqualityClosure.edgeGraph allowed).Reachable left right)
    (hequality : valuation left = valuation right) :
    HESatisfiedAddEqualityCertified
      valuation trace allowed seed left right := by
  let hadd : AddVarEqualityRel seed left right
      (seed.addEquality left right) := .consistent hconsistent
  exact {
    after := seed.addEquality left right
    addRel := hadd
    traceSound := by
      simpa only [Subsingleton.elim
        (AddVarEqualityRel.consistent hconsistent) hadd] using
          (AddVarEqualityTraceSound.consistent
            (trace := trace) (hconsistent := hconsistent))
    equalitySound := by
      simpa only [Subsingleton.elim
        (AddVarEqualityRel.consistent hconsistent) hadd] using
          (AddVarEqualityEqualityClosureBoundSound.consistent
            (allowed := allowed) (hconsistent := hconsistent) hallowed)
    satisfied := addVarEqualityRel_satisfied hadd hseed hequality
    assignmentsNonVariable := hseedNonvar.addEquality left right
    equalityBound := hseedBound.addEquality hallowed
  }

/-- A live merge with a singleton assignment on the right is precisely one
certified value insertion.  The two merge certificates are inverted onto the
same proof-irrelevant `AddVarBindingRel`; no binding presentation is compared. -/
theorem HESatisfiedAddBindingCertified.nonempty_ofLiveSingleton
    {valuation : String → Metta.Atom}
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {seed : Bindings}
    {key : String} {value : Atom}
    (h : HELiveMergeCertified trace allowed seed
      (Bindings.empty.assign key value))
    (hseed : HEBindingSatisfied valuation seed)
    (hseedNonvar : HEAssignmentsNonVariable seed)
    (hseedBound : HEEqualityClosureBound seed allowed)
    (hvalueNonvar : DeclMatchSpec.Atom.isVarB value = false)
    (hvalue : valuation key =
      applyClassSolution valuation (toLeaTTaAtom value)) :
    Nonempty (HESatisfiedAddBindingCertified
      valuation trace allowed seed key value) := by
  obtain ⟨hadd, haddTrace⟩ :=
    mergeTraceSound_singleAssignment_inv h.traceSound
  obtain ⟨hadd', haddEquality⟩ :=
    mergeEqualityClosureBoundSound_singleAssignment_inv h.equalitySound
  have haddEquality' :
      AddVarBindingEqualityClosureBoundSound allowed hadd := by
    simpa only [Subsingleton.elim hadd' hadd] using haddEquality
  have hemptyNonvar : HEAssignmentsNonVariable Bindings.empty := by
    simp [HEAssignmentsNonVariable, Bindings.empty]
  exact ⟨{
    after := h.after
    addRel := hadd
    traceSound := haddTrace
    equalitySound := haddEquality'
    satisfied := addVarBindingRel_satisfied hadd hseed hvalue
    assignmentsNonVariable :=
      mergeBindings_assignmentsNonVariable h.merge_mem hseedNonvar
        (hemptyNonvar.assign hvalueNonvar)
    equalityBound := h.equalitySound.preserves hseedBound
  }⟩

/-- Equality companion of
`HESatisfiedAddBindingCertified.nonempty_ofLiveSingleton`. -/
theorem HESatisfiedAddEqualityCertified.nonempty_ofLiveSingleton
    {valuation : String → Metta.Atom}
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {seed : Bindings}
    {left right : String}
    (h : HELiveMergeCertified trace allowed seed
      (Bindings.empty.addEquality left right))
    (hseed : HEBindingSatisfied valuation seed)
    (hseedNonvar : HEAssignmentsNonVariable seed)
    (hseedBound : HEEqualityClosureBound seed allowed)
    (hequality : valuation left = valuation right) :
    Nonempty (HESatisfiedAddEqualityCertified
      valuation trace allowed seed left right) := by
  obtain ⟨hadd, haddTrace⟩ :=
    mergeTraceSound_singleEquality_inv h.traceSound
  obtain ⟨hadd', haddEquality⟩ :=
    mergeEqualityClosureBoundSound_singleEquality_inv h.equalitySound
  have haddEquality' :
      AddVarEqualityEqualityClosureBoundSound allowed hadd := by
    simpa only [Subsingleton.elim hadd' hadd] using haddEquality
  have hemptyNonvar : HEAssignmentsNonVariable Bindings.empty := by
    simp [HEAssignmentsNonVariable, Bindings.empty]
  exact ⟨{
    after := h.after
    addRel := hadd
    traceSound := haddTrace
    equalitySound := haddEquality'
    satisfied := addVarEqualityRel_satisfied hadd hseed hequality
    assignmentsNonVariable :=
      mergeBindings_assignmentsNonVariable h.merge_mem hseedNonvar
        (hemptyNonvar.addEquality left right)
    equalityBound := h.equalitySound.preserves hseedBound
  }⟩

/-- Package the scalar hidden conflict as the certified add callback consumed
by the runtime-ordered merge fold. -/
theorem HELiveHiddenMatchResidualCertified.nonempty_satisfiedAddBinding_of_conflict
    {valuation : String → Metta.Atom}
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {seed : Bindings}
    {subst : Metta.Subst} {key : String} {value first : Atom}
    {rest : List Atom}
    (h : HELiveHiddenMatchResidualCertified
      trace allowed first value seed subst)
    (hclass : seed.classValues key = first :: rest)
    (hconsistent : Bindings.valuesConsistent (first :: rest) = true)
    (hdifferent : first ≠ value)
    (hseed : HEBindingSatisfied valuation seed)
    (hseedNonvar : HEAssignmentsNonVariable seed)
    (hseedBound : HEEqualityClosureBound seed allowed)
    (hvalueNonvar : DeclMatchSpec.Atom.isVarB value = false)
    (hvalue : valuation key =
      applyClassSolution valuation (toLeaTTaAtom value)) :
    Nonempty (HESatisfiedAddBindingCertified
      valuation trace allowed seed key value) := by
  obtain ⟨hmerge, _hafter⟩ :=
    h.toAssignmentConflictMergeLive hclass hconsistent hdifferent
  exact HESatisfiedAddBindingCertified.nonempty_ofLiveSingleton
    hmerge.toHELiveMergeCertified hseed hseedNonvar hseedBound
      hvalueNonvar hvalue

/-- Class-wide assignment reconciliation companion of the scalar adapter. -/
theorem HELiveHiddenListMatchResidualCertified.nonempty_satisfiedAddBinding_of_reconcile
    {valuation : String → Metta.Atom}
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {seed : Bindings}
    {subst : Metta.Subst} {key : String} {value first : Atom}
    {rest : List Atom}
    (h : HELiveHiddenListMatchResidualCertified trace allowed
      (List.replicate (rest.length + 1) first) (rest ++ [value])
      seed subst)
    (hclass : seed.classValues key = first :: rest)
    (hinconsistent : Bindings.valuesConsistent (first :: rest) = false)
    (hseed : HEBindingSatisfied valuation seed)
    (hseedNonvar : HEAssignmentsNonVariable seed)
    (hseedBound : HEEqualityClosureBound seed allowed)
    (hvalueNonvar : DeclMatchSpec.Atom.isVarB value = false)
    (hvalue : valuation key =
      applyClassSolution valuation (toLeaTTaAtom value)) :
    Nonempty (HESatisfiedAddBindingCertified
      valuation trace allowed seed key value) := by
  obtain ⟨hmerge, _hafter⟩ :=
    h.toAssignmentReconcileMergeLive hclass hinconsistent
  exact HESatisfiedAddBindingCertified.nonempty_ofLiveSingleton
    hmerge.toHELiveMergeCertified hseed hseedNonvar hseedBound
      hvalueNonvar hvalue

/-- Package the two-value hidden equality conflict as a certified equality
insertion for the outer merge fold. -/
theorem HELiveHiddenMatchResidualCertified.nonempty_satisfiedAddEquality_of_pairConflict
    {valuation : String → Metta.Atom}
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {seed : Bindings}
    {subst : Metta.Subst} {left right : String} {first second : Atom}
    (h : HELiveHiddenMatchResidualCertified trace allowed first second
      (seed.addEquality left right) subst)
    (hvalues : (seed.addEquality left right).classValues left =
      [first, second])
    (hinconsistent : Bindings.valuesConsistent [first, second] = false)
    (hallowed :
      (EqualityClosure.edgeGraph allowed).Reachable left right)
    (hseed : HEBindingSatisfied valuation seed)
    (hseedNonvar : HEAssignmentsNonVariable seed)
    (hseedBound : HEEqualityClosureBound seed allowed)
    (hequality : valuation left = valuation right) :
    Nonempty (HESatisfiedAddEqualityCertified
      valuation trace allowed seed left right) := by
  obtain ⟨hmerge, _hafter⟩ :=
    h.toEqualityPairConflictMergeLive hvalues hinconsistent hallowed
  exact HESatisfiedAddEqualityCertified.nonempty_ofLiveSingleton
    hmerge.toHELiveMergeCertified hseed hseedNonvar hseedBound hequality

/-- Whole-class hidden equality reconciliation companion of the pair adapter. -/
theorem HELiveHiddenListMatchResidualCertified.nonempty_satisfiedAddEquality_of_classConflict
    {valuation : String → Metta.Atom}
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {seed : Bindings}
    {subst : Metta.Subst} {left right : String}
    {first second third : Atom} {rest : List Atom}
    (h : HELiveHiddenListMatchResidualCertified trace allowed
      (List.replicate (rest.length + 2) first)
      (second :: third :: rest) (seed.addEquality left right) subst)
    (hvalues : (seed.addEquality left right).classValues left =
      first :: second :: third :: rest)
    (hinconsistent : Bindings.valuesConsistent
      (first :: second :: third :: rest) = false)
    (hallowed :
      (EqualityClosure.edgeGraph allowed).Reachable left right)
    (hseed : HEBindingSatisfied valuation seed)
    (hseedNonvar : HEAssignmentsNonVariable seed)
    (hseedBound : HEEqualityClosureBound seed allowed)
    (hequality : valuation left = valuation right) :
    Nonempty (HESatisfiedAddEqualityCertified
      valuation trace allowed seed left right) := by
  obtain ⟨hmerge, _hafter⟩ :=
    h.toEqualityClassConflictMergeLive hvalues hinconsistent hallowed
  exact HESatisfiedAddEqualityCertified.nonempty_ofLiveSingleton
    hmerge.toHELiveMergeCertified hseed hseedNonvar hseedBound hequality

/-- The four genuinely recursive insertion branches at one semantic ceiling.
The runtime dispatcher, the nonrecursive constructors, and the complete
assignment-then-equality fold are deliberately absent from this interface. -/
structure HESatisfiedConflictAddCallbacks
    (valuation : String → Metta.Atom)
    (trace : List (String × Metta.Atom))
    (allowed : List (String × String)) (bound : Nat) where
  assignmentConflict : ∀
    {seed : Bindings} {key : String} {value first : Atom}
    {rest : List Atom},
    HEBindingSatisfied valuation seed →
    HEAssignmentsNonVariable seed →
    HEEqualityClosureBound seed allowed →
    DeclMatchSpec.Atom.isVarB value = false →
    valuation key = applyClassSolution valuation (toLeaTTaAtom value) →
    (valuation key).size < bound →
    HESolutionAtomSize valuation value < bound →
    seed.classValues key = first :: rest →
    Bindings.valuesConsistent (first :: rest) = true →
    first ≠ value →
    Nonempty (HESatisfiedAddBindingCertified
      valuation trace allowed seed key value)
  assignmentReconcile : ∀
    {seed : Bindings} {key : String} {value first : Atom}
    {rest : List Atom},
    HEBindingSatisfied valuation seed →
    HEAssignmentsNonVariable seed →
    HEEqualityClosureBound seed allowed →
    DeclMatchSpec.Atom.isVarB value = false →
    valuation key = applyClassSolution valuation (toLeaTTaAtom value) →
    (valuation key).size < bound →
    HESolutionAtomSize valuation value < bound →
    seed.classValues key = first :: rest →
    Bindings.valuesConsistent (first :: rest) = false →
    Nonempty (HESatisfiedAddBindingCertified
      valuation trace allowed seed key value)
  equalityPair : ∀
    {seed : Bindings} {left right : String} {first second : Atom},
    HEBindingSatisfied valuation seed →
    HEAssignmentsNonVariable seed →
    HEEqualityClosureBound seed allowed →
    (EqualityClosure.edgeGraph allowed).Reachable left right →
    valuation left = valuation right →
    (valuation left).size < bound →
    (valuation right).size < bound →
    (seed.addEquality left right).classValues left = [first, second] →
    Bindings.valuesConsistent [first, second] = false →
    Nonempty (HESatisfiedAddEqualityCertified
      valuation trace allowed seed left right)
  equalityClass : ∀
    {seed : Bindings} {left right : String}
    {first second third : Atom} {rest : List Atom},
    HEBindingSatisfied valuation seed →
    HEAssignmentsNonVariable seed →
    HEEqualityClosureBound seed allowed →
    (EqualityClosure.edgeGraph allowed).Reachable left right →
    valuation left = valuation right →
    (valuation left).size < bound →
    (valuation right).size < bound →
    (seed.addEquality left right).classValues left =
      first :: second :: third :: rest →
    Bindings.valuesConsistent (first :: second :: third :: rest) = false →
    Nonempty (HESatisfiedAddEqualityCertified
      valuation trace allowed seed left right)

/-- Dispatch the concrete HE insertion branches, using callbacks only for
the four recursive reconciliation cases, then run the certified merge fold.
This is the certificate-preserving analogue of the dispatcher inside
`satisfiedMergeRelCompleteBelow`. -/
theorem HESatisfiedConflictAddCallbacks.merge
    {valuation : String → Metta.Atom}
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {bound : Nat}
    (callbacks : HESatisfiedConflictAddCallbacks
      valuation trace allowed bound)
    {seed right : Bindings}
    (hseed : HEBindingSatisfied valuation seed)
    (hseedNonvar : HEAssignmentsNonVariable seed)
    (hseedSound : LeaEliminationTraceAssignmentsSound seed trace)
    (hseedBound : HEEqualityClosureBound seed allowed)
    (hright : HEBindingSatisfied valuation right)
    (hrightNonvar : HEAssignmentsNonVariable right)
    (hrightSound : LeaEliminationTraceAssignmentsSound right trace)
    (hrightEqualityBound : HEEqualityClosureBound right allowed)
    (hrightBound : HEBindingSolutionSizeBound valuation right bound) :
    Nonempty (HESatisfiedMergeCertified
      valuation trace allowed seed right) := by
  apply exists_satisfiedMergeCertified_of_adds
      (valuation := valuation) (bound := bound)
      (trace := trace) (allowed := allowed)
      (seed := seed) (right := right)
      (hseed := hseed) (hseedNonvar := hseedNonvar)
      (hseedSound := hseedSound) (hseedBound := hseedBound)
      (hright := hright) (hrightNonvar := hrightNonvar)
      (hrightSound := hrightSound)
      (hrightEqualityBound := hrightEqualityBound)
      (hrightBound := hrightBound)
  · intro current key value hcurrent hcurrentNonvar hcurrentBound
      hvalueNonvar hvalue hkeySize hvalueSize
    cases hclass : current.classValues key with
    | nil =>
        exact ⟨HESatisfiedAddBindingCertified.fresh hclass hcurrent
          hcurrentNonvar hcurrentBound hvalueNonvar hvalue⟩
    | cons first rest =>
        cases hconsistent :
            Bindings.valuesConsistent (first :: rest) with
        | true =>
            by_cases hsame : first = value
            · exact ⟨HESatisfiedAddBindingCertified.same hclass
                hconsistent hsame hcurrent hcurrentNonvar hcurrentBound⟩
            · exact callbacks.assignmentConflict hcurrent
                hcurrentNonvar hcurrentBound hvalueNonvar hvalue
                hkeySize hvalueSize hclass hconsistent hsame
        | false =>
            exact callbacks.assignmentReconcile hcurrent
              hcurrentNonvar hcurrentBound hvalueNonvar hvalue
              hkeySize hvalueSize hclass hconsistent
  · intro current left rightKey hcurrent hcurrentNonvar hcurrentBound
      hallowed hequality hleftSize hrightSize
    cases hconsistent : Bindings.valuesConsistent
        ((current.addEquality left rightKey).classValues left) with
    | true =>
        exact ⟨HESatisfiedAddEqualityCertified.consistent hconsistent
          hcurrent hcurrentNonvar hcurrentBound hallowed hequality⟩
    | false =>
        cases hvalues :
            (current.addEquality left rightKey).classValues left with
        | nil =>
            rw [hvalues] at hconsistent
            simp [Bindings.valuesConsistent] at hconsistent
        | cons first rest =>
            cases rest with
            | nil =>
                rw [hvalues] at hconsistent
                simp [Bindings.valuesConsistent] at hconsistent
            | cons second tail =>
                cases tail with
                | nil =>
                    have hpairInconsistent :
                        Bindings.valuesConsistent [first, second] = false := by
                      simpa [hvalues] using hconsistent
                    exact callbacks.equalityPair hcurrent
                      hcurrentNonvar hcurrentBound hallowed hequality
                      hleftSize hrightSize hvalues hpairInconsistent
                | cons third rest =>
                    have hclassInconsistent : Bindings.valuesConsistent
                        (first :: second :: third :: rest) = false := by
                      simpa [hvalues] using hconsistent
                    exact callbacks.equalityClass hcurrent
                      hcurrentNonvar hcurrentBound hallowed hequality
                      hleftSize hrightSize hvalues hclassInconsistent

/-- A co-satisfied pair of non-variable atoms at one semantic size either is
a reflexive leaf match or is an expression match whose bindings lie strictly
below that size. -/
private theorem exists_nonvariableMatchRel_at_solutionSize
    {valuation : String → Metta.Atom} {bound : Nat}
    (hmerge : HESatisfiedMergeRelCompleteBelow valuation bound)
    {left right : Atom}
    (hequation : HEAtomEquationSatisfied valuation left right)
    (hleftNonvar : DeclMatchSpec.Atom.isVarB left = false)
    (hrightNonvar : DeclMatchSpec.Atom.isVarB right = false)
    (hleftSize : HESolutionAtomSize valuation left = bound)
    (hrightSize : HESolutionAtomSize valuation right = bound) :
    ∃ out, DeclMatchSpec.MatchRel left right out ∧
      HEBindingSatisfied valuation out ∧
        HEAssignmentsNonVariable out ∧
          HEBindingSolutionSizeBound valuation out bound := by
  by_cases hexpressions : BothExpressions left right
  · rcases hexpressions with ⟨lefts, rights, rfl, rfl⟩
    exact exists_expressionMatchRel_solutionSizeBound hmerge hequation
      hleftSize hrightSize
  · obtain ⟨out, hmatch⟩ :=
      exists_matchRel_of_solution_leaf ⟨valuation, hequation⟩ hexpressions
    have houtBound :
        HEBindingSolutionSizeBound valuation out bound := by
      cases hmatch with
      | symSym => exact heBindingSolutionSizeBound_empty valuation bound
      | varVar => simp [DeclMatchSpec.Atom.isVarB] at hleftNonvar
      | varNonVar => simp [DeclMatchSpec.Atom.isVarB] at hleftNonvar
      | nonVarVar => simp [DeclMatchSpec.Atom.isVarB] at hrightNonvar
      | grounded => exact heBindingSolutionSizeBound_empty valuation bound
      | expr => exact (hexpressions (by simp [BothExpressions])).elim
    exact ⟨out, hmatch,
      matchRel_satisfied_of_equation hmatch hequation,
      heAssignmentsNonVariable_of_matchRel hmatch,
      houtBound⟩

/-- Pointwise reconciliation for class values at one semantic size.  Equal
leaf pairs contribute no bindings; expression pairs contribute only strict
semantic subterms.  Each resulting child record is merged into the live
accumulator through the same bounded merge hypothesis. -/
private theorem exists_nonvariableMatchListAccRel_at_solutionSize
    {valuation : String → Metta.Atom} {bound : Nat}
    (hmerge : HESatisfiedMergeRelCompleteBelow valuation bound) :
    ∀ {lefts rights : List Atom} {seed : Bindings},
      HEBindingSatisfied valuation seed →
      HEAssignmentsNonVariable seed →
      HEBindingSolutionSizeBound valuation seed bound →
      MettaAtomListsSatisfied valuation
        (toLeaTTaAtoms lefts) (toLeaTTaAtoms rights) →
      (∀ atom ∈ lefts,
        DeclMatchSpec.Atom.isVarB atom = false ∧
          HESolutionAtomSize valuation atom = bound) →
      (∀ atom ∈ rights,
        DeclMatchSpec.Atom.isVarB atom = false ∧
          HESolutionAtomSize valuation atom = bound) →
      ∃ out, DeclMatchSpec.MatchListAccRel lefts rights seed out ∧
        HEBindingSatisfied valuation out ∧
          HEAssignmentsNonVariable out ∧
            HEBindingSolutionSizeBound valuation out bound := by
  intro lefts
  induction lefts with
  | nil =>
      intro rights seed hseed hseedNonvar hseedBound hlists _ _
      cases rights with
      | nil => exact ⟨seed, .nil, hseed, hseedNonvar, hseedBound⟩
      | cons right rights =>
          simp [MettaAtomListsSatisfied, toLeaTTaAtoms] at hlists
  | cons left lefts ih =>
      intro rights seed hseed hseedNonvar hseedBound hlists hlefts hrights
      cases rights with
      | nil =>
          simp [MettaAtomListsSatisfied, toLeaTTaAtoms] at hlists
      | cons right rights =>
          have hequations :
              HEAtomEquationSatisfied valuation left right ∧
                MettaAtomListsSatisfied valuation
                  (toLeaTTaAtoms lefts) (toLeaTTaAtoms rights) := by
            simpa [HEAtomEquationSatisfied, MettaAtomListsSatisfied,
              toLeaTTaAtoms] using hlists
          have hleft := hlefts left (by simp)
          have hright := hrights right (by simp)
          obtain ⟨matched, hmatched, hmatchedSat, hmatchedNonvar,
              hmatchedBound⟩ :=
            exists_nonvariableMatchRel_at_solutionSize hmerge
              hequations.1 hleft.1 hright.1 hleft.2 hright.2
          obtain ⟨next, hmergeRel, hnextSat, hnextNonvar⟩ :=
            hmerge hseed hseedNonvar hmatchedSat hmatchedNonvar
              hmatchedBound
          obtain ⟨mergeFuel, hmergeMem⟩ :=
            mergeBindings_complete hmergeRel
          have hnextBound :
              HEBindingSolutionSizeBound valuation next bound :=
            mergeRel_solutionSizeBound hmergeRel hseedBound hmatchedBound
          have hleftTail : ∀ atom ∈ lefts,
              DeclMatchSpec.Atom.isVarB atom = false ∧
                HESolutionAtomSize valuation atom = bound := by
            intro atom hmem
            exact hlefts atom (by simp [hmem])
          have hrightTail : ∀ atom ∈ rights,
              DeclMatchSpec.Atom.isVarB atom = false ∧
                HESolutionAtomSize valuation atom = bound := by
            intro atom hmem
            exact hrights atom (by simp [hmem])
          obtain ⟨out, htail, houtSat, houtNonvar, houtBound⟩ :=
            ih hnextSat hnextNonvar hnextBound hequations.2
              hleftTail hrightTail
          exact ⟨out, .cons hmatched hmergeMem htail,
            houtSat, houtNonvar, houtBound⟩

/-- Fold bounded value/equality insertion callbacks into the exact
assignment-then-equality `MergeRel` prescribed by HE. -/
private theorem satisfiedMergeRelCompleteBelow_of_adds
    {valuation : String → Metta.Atom} {bound : Nat}
    (haddValue : ∀ {seed : Bindings} {key : String} {value : Atom},
      HEBindingSatisfied valuation seed →
      HEAssignmentsNonVariable seed →
      DeclMatchSpec.Atom.isVarB value = false →
      valuation key = applyClassSolution valuation (toLeaTTaAtom value) →
      (valuation key).size < bound →
      HESolutionAtomSize valuation value < bound →
      ∃ out, AddVarBindingRel seed key value out ∧
        HEBindingSatisfied valuation out ∧
          HEAssignmentsNonVariable out)
    (haddEquality : ∀ {seed : Bindings} {left right : String},
      HEBindingSatisfied valuation seed →
      HEAssignmentsNonVariable seed →
      valuation left = valuation right →
      (valuation left).size < bound →
      (valuation right).size < bound →
      ∃ out, AddVarEqualityRel seed left right out ∧
        HEBindingSatisfied valuation out ∧
          HEAssignmentsNonVariable out) :
    HESatisfiedMergeRelCompleteBelow valuation bound := by
  intro seed right hseed hseedNonvar hright hrightNonvar hrightBound
  have foldAssignments : ∀
      (assignments : List (String × Atom)) (before : Bindings),
      HEBindingSatisfied valuation before →
      HEAssignmentsNonVariable before →
      (∀ key value, (key, value) ∈ assignments →
        valuation key =
          applyClassSolution valuation (toLeaTTaAtom value)) →
      (∀ key value, (key, value) ∈ assignments →
        DeclMatchSpec.Atom.isVarB value = false) →
      (∀ key value, (key, value) ∈ assignments →
        (valuation key).size < bound ∧
          HESolutionAtomSize valuation value < bound) →
      ∃ after, MergeAssignsRel before assignments after ∧
        HEBindingSatisfied valuation after ∧
          HEAssignmentsNonVariable after := by
    intro assignments
    induction assignments with
    | nil =>
        intro before hbefore hnonvar _ _ _
        exact ⟨before, .nil, hbefore, hnonvar⟩
    | cons assignment rest ih =>
        rcases assignment with ⟨key, value⟩
        intro before hbefore hnonvar hsat hvalues hbounds
        obtain ⟨next, hadd, hnextSat, hnextNonvar⟩ :=
          haddValue hbefore hnonvar
            (hvalues key value (by simp))
            (hsat key value (by simp))
            (hbounds key value (by simp)).1
            (hbounds key value (by simp)).2
        have hrestSat : ∀ restKey restValue,
            (restKey, restValue) ∈ rest →
            valuation restKey = applyClassSolution valuation
              (toLeaTTaAtom restValue) := by
          intro restKey restValue hmem
          exact hsat restKey restValue (by simp [hmem])
        have hrestValues : ∀ restKey restValue,
            (restKey, restValue) ∈ rest →
            DeclMatchSpec.Atom.isVarB restValue = false := by
          intro restKey restValue hmem
          exact hvalues restKey restValue (by simp [hmem])
        have hrestBounds : ∀ restKey restValue,
            (restKey, restValue) ∈ rest →
            (valuation restKey).size < bound ∧
              HESolutionAtomSize valuation restValue < bound := by
          intro restKey restValue hmem
          exact hbounds restKey restValue (by simp [hmem])
        obtain ⟨after, htail, hafterSat, hafterNonvar⟩ :=
          ih next hnextSat hnextNonvar hrestSat hrestValues hrestBounds
        exact ⟨after, .cons hadd htail, hafterSat, hafterNonvar⟩
  have foldEqualities : ∀
      (equalities : List (String × String)) (before : Bindings),
      HEBindingSatisfied valuation before →
      HEAssignmentsNonVariable before →
      (∀ left right, (left, right) ∈ equalities →
        valuation left = valuation right) →
      (∀ left right, (left, right) ∈ equalities →
        (valuation left).size < bound ∧
          (valuation right).size < bound) →
      ∃ after, MergeEqsRel before equalities after ∧
        HEBindingSatisfied valuation after ∧
          HEAssignmentsNonVariable after := by
    intro equalities
    induction equalities with
    | nil =>
        intro before hbefore hnonvar _ _
        exact ⟨before, .nil, hbefore, hnonvar⟩
    | cons equality rest ih =>
        rcases equality with ⟨left, right⟩
        intro before hbefore hnonvar hsat hbounds
        obtain ⟨next, hadd, hnextSat, hnextNonvar⟩ :=
          haddEquality hbefore hnonvar
            (hsat left right (by simp))
            (hbounds left right (by simp)).1
            (hbounds left right (by simp)).2
        have hrestSat : ∀ restLeft restRight,
            (restLeft, restRight) ∈ rest →
            valuation restLeft = valuation restRight := by
          intro restLeft restRight hmem
          exact hsat restLeft restRight (by simp [hmem])
        have hrestBounds : ∀ restLeft restRight,
            (restLeft, restRight) ∈ rest →
            (valuation restLeft).size < bound ∧
              (valuation restRight).size < bound := by
          intro restLeft restRight hmem
          exact hbounds restLeft restRight (by simp [hmem])
        obtain ⟨after, htail, hafterSat, hafterNonvar⟩ :=
          ih next hnextSat hnextNonvar hrestSat hrestBounds
        exact ⟨after, .cons hadd htail, hafterSat, hafterNonvar⟩
  obtain ⟨middle, hassignments, hmiddleSat, hmiddleNonvar⟩ :=
    foldAssignments right.assignments seed hseed hseedNonvar
      (fun key value hmem => hright.1 key value hmem)
      (fun key value hmem =>
        hrightNonvar.isVarB_eq_false_of_assignment hmem)
      (fun key value hmem => hrightBound.1 key value hmem)
  obtain ⟨out, hequalities, houtSat, houtNonvar⟩ :=
    foldEqualities right.equalities middle hmiddleSat hmiddleNonvar
      (fun left right hmem => hright.2 left right hmem)
      (fun left right hmem => hrightBound.2 left right hmem)
  exact ⟨out, .mk hassignments hequalities, houtSat, houtNonvar⟩

/-- The operational keystone.  Strong induction is on the semantic ceiling of
the right record.  A value/equality insertion at key size `k < bound` invokes
the original HE matcher at size `k`; expression matching emits only bindings
strictly below `k`, so its live merge is supplied by the induction hypothesis
at `k`.  The seed is never measured. -/
theorem satisfiedMergeRelCompleteBelow
    (valuation : String → Metta.Atom) :
    ∀ bound, HESatisfiedMergeRelCompleteBelow valuation bound := by
  intro bound
  induction bound using Nat.strong_induction_on with
  | h bound ih =>
      apply satisfiedMergeRelCompleteBelow_of_adds
      · intro seed key value hseed hseedNonvar hvalueNonvar hvalue
          hkeyBound hvalueBound
        cases hclass : seed.classValues key with
        | nil =>
            let hadd : AddVarBindingRel seed key value
                (seed.assign key value) := .fresh hclass
            exact ⟨seed.assign key value, hadd,
              addVarBindingRel_satisfied hadd hseed hvalue,
              hseedNonvar.assign hvalueNonvar⟩
        | cons first rest =>
            cases hconsistent :
                Bindings.valuesConsistent (first :: rest) with
            | true =>
                by_cases hequal : first = value
                · let hadd : AddVarBindingRel seed key value seed :=
                    .same hclass hconsistent hequal
                  exact ⟨seed, hadd,
                    addVarBindingRel_satisfied hadd hseed hvalue,
                    hseedNonvar⟩
                · have hfirstMem : first ∈ seed.classValues key := by
                    rw [hclass]
                    exact List.mem_cons_self ..
                  have hfirstEquation : HEAtomEquationSatisfied valuation
                      first value :=
                    (hseed.eq_applyClassSolution_of_mem_classValues
                      hfirstMem).symm.trans hvalue
                  have hfirstSize : HESolutionAtomSize valuation first =
                      (valuation key).size :=
                    hseed.solutionAtomSize_classValue hfirstMem
                  have hvalueSize : HESolutionAtomSize valuation value =
                      (valuation key).size := by
                    exact congrArg Metta.Atom.size hvalue.symm
                  obtain ⟨lefts, rights, hfirstExpr, hvalueExpr⟩ :=
                    bothExpressions_of_ne_classValue_coSatisfied
                      hseed hseedNonvar hclass hvalueNonvar hvalue hequal
                  subst first
                  subst value
                  obtain ⟨matched, hmatch, hmatchedSat, hmatchedNonvar,
                      hmatchedBound⟩ :=
                    exists_expressionMatchRel_solutionSizeBound
                      (ih _ hkeyBound) hfirstEquation hfirstSize hvalueSize
                  obtain ⟨out, hmerge, _houtSat, houtNonvar⟩ :=
                    ih _ hkeyBound hseed hseedNonvar hmatchedSat
                      hmatchedNonvar hmatchedBound
                  let hadd : AddVarBindingRel seed key
                      (.expression rights) out :=
                    .conflict hclass hconsistent hequal hmatch hmerge
                  exact ⟨out, hadd,
                    addVarBindingRel_satisfied hadd hseed hvalue,
                    houtNonvar⟩
            | false =>
                have hfirstMem : first ∈ seed.classValues key := by
                  rw [hclass]
                  exact List.mem_cons_self ..
                have hfirstSize : HESolutionAtomSize valuation first =
                    (valuation key).size :=
                  hseed.solutionAtomSize_classValue hfirstMem
                have hvalueSize : HESolutionAtomSize valuation value =
                    (valuation key).size := by
                  exact congrArg Metta.Atom.size hvalue.symm
                have hfirstNonvar :
                    DeclMatchSpec.Atom.isVarB first = false :=
                  hseedNonvar.isVarB_eq_false_of_classValue hfirstMem
                have hlists := classValues_reconcileList_satisfied
                  hseed hclass hvalue
                have hleftData : ∀ atom ∈
                    List.replicate (rest.length + 1) first,
                    DeclMatchSpec.Atom.isVarB atom = false ∧
                      HESolutionAtomSize valuation atom =
                        (valuation key).size := by
                  intro atom hmem
                  have hatom : atom = first := List.eq_of_mem_replicate hmem
                  subst atom
                  exact ⟨hfirstNonvar, hfirstSize⟩
                have hrightData : ∀ atom ∈ rest ++ [value],
                    DeclMatchSpec.Atom.isVarB atom = false ∧
                      HESolutionAtomSize valuation atom =
                        (valuation key).size := by
                  intro atom hmem
                  rcases List.mem_append.mp hmem with hrest | hlast
                  · have hclassMem : atom ∈ seed.classValues key := by
                      rw [hclass]
                      exact List.mem_cons_of_mem first hrest
                    exact ⟨
                      hseedNonvar.isVarB_eq_false_of_classValue hclassMem,
                      hseed.solutionAtomSize_classValue hclassMem⟩
                  · simp only [List.mem_singleton] at hlast
                    subst atom
                    exact ⟨hvalueNonvar, hvalueSize⟩
                obtain ⟨matched, hmatch, hmatchedSat, hmatchedNonvar,
                    hmatchedBound⟩ :=
                  exists_nonvariableMatchListAccRel_at_solutionSize
                    (ih _ hkeyBound)
                    ((hesat_empty_iff valuation).mpr trivial)
                    (by simp [HEAssignmentsNonVariable, Bindings.empty])
                    (heBindingSolutionSizeBound_empty valuation
                      (valuation key).size)
                    hlists hleftData hrightData
                obtain ⟨out, hmerge, _houtSat, houtNonvar⟩ :=
                  ih _ hkeyBound hseed hseedNonvar hmatchedSat
                    hmatchedNonvar hmatchedBound
                let hadd : AddVarBindingRel seed key value out :=
                  .reconcile hclass hconsistent hmatch hmerge
                exact ⟨out, hadd,
                  addVarBindingRel_satisfied hadd hseed hvalue,
                  houtNonvar⟩
      · intro seed left right hseed hseedNonvar hequality hleftBound
          hrightBound
        have hcandidateSat : HEBindingSatisfied valuation
            (seed.addEquality left right) :=
          (heBindingSatisfied_addEquality_iff valuation seed left right).mpr
            ⟨hseed, hequality⟩
        have hcandidateNonvar :
            HEAssignmentsNonVariable (seed.addEquality left right) :=
          hseedNonvar.addEquality left right
        cases hconsistent : Bindings.valuesConsistent
            ((seed.addEquality left right).classValues left) with
        | true =>
            let hadd : AddVarEqualityRel seed left right
                (seed.addEquality left right) := .consistent hconsistent
            exact ⟨seed.addEquality left right, hadd,
              addVarEqualityRel_satisfied hadd hseed hequality,
              hcandidateNonvar⟩
        | false =>
            cases hvalues :
                (seed.addEquality left right).classValues left with
            | nil =>
                rw [hvalues] at hconsistent
                simp [Bindings.valuesConsistent] at hconsistent
            | cons first rest =>
                cases rest with
                | nil =>
                    rw [hvalues] at hconsistent
                    simp [Bindings.valuesConsistent] at hconsistent
                | cons second tail =>
                    cases tail with
                    | nil =>
                        have hfirstMem : first ∈
                            (seed.addEquality left right).classValues left := by
                          rw [hvalues]
                          simp
                        have hsecondMem : second ∈
                            (seed.addEquality left right).classValues left := by
                          rw [hvalues]
                          simp
                        have hequation : HEAtomEquationSatisfied valuation
                            first second :=
                          classValues_equationSatisfied hcandidateSat
                            hfirstMem hsecondMem
                        have hfirstSize :
                            HESolutionAtomSize valuation first =
                              (valuation left).size :=
                          hcandidateSat.solutionAtomSize_classValue hfirstMem
                        have hsecondSize :
                            HESolutionAtomSize valuation second =
                              (valuation left).size :=
                          hcandidateSat.solutionAtomSize_classValue hsecondMem
                        obtain ⟨matched, hmatch, hmatchedSat,
                            hmatchedNonvar, hmatchedBound⟩ :=
                          exists_nonvariableMatchRel_at_solutionSize
                            (ih _ hleftBound) hequation
                            (hcandidateNonvar.isVarB_eq_false_of_classValue
                              hfirstMem)
                            (hcandidateNonvar.isVarB_eq_false_of_classValue
                              hsecondMem)
                            hfirstSize hsecondSize
                        obtain ⟨out, hmerge, _houtSat, houtNonvar⟩ :=
                          ih _ hleftBound hcandidateSat hcandidateNonvar
                            hmatchedSat hmatchedNonvar hmatchedBound
                        have hpairInconsistent :
                            Bindings.valuesConsistent [first, second] = false := by
                          simpa [hvalues] using hconsistent
                        let hadd : AddVarEqualityRel seed left right out :=
                          .pairConflict hvalues hpairInconsistent hmatch hmerge
                        exact ⟨out, hadd,
                          addVarEqualityRel_satisfied hadd hseed hequality,
                          houtNonvar⟩

                    | cons third rest =>
                        have hfirstMem : first ∈
                            (seed.addEquality left right).classValues left := by
                          rw [hvalues]
                          simp
                        have hfirstSize :
                            HESolutionAtomSize valuation first =
                              (valuation left).size :=
                          hcandidateSat.solutionAtomSize_classValue hfirstMem
                        have hfirstNonvar :
                            DeclMatchSpec.Atom.isVarB first = false :=
                          hcandidateNonvar.isVarB_eq_false_of_classValue
                            hfirstMem
                        have hlists : MettaAtomListsSatisfied valuation
                            (toLeaTTaAtoms
                              (List.replicate (rest.length + 2) first))
                            (toLeaTTaAtoms (second :: third :: rest)) := by
                          have h := classValues_replicateTail_satisfied
                            hcandidateSat hvalues
                          simpa using h
                        have hleftData : ∀ atom ∈
                            List.replicate (rest.length + 2) first,
                            DeclMatchSpec.Atom.isVarB atom = false ∧
                              HESolutionAtomSize valuation atom =
                                (valuation left).size := by
                          intro atom hmem
                          have hatom : atom = first :=
                            List.eq_of_mem_replicate hmem
                          subst atom
                          exact ⟨hfirstNonvar, hfirstSize⟩
                        have hrightData : ∀ atom ∈ second :: third :: rest,
                            DeclMatchSpec.Atom.isVarB atom = false ∧
                              HESolutionAtomSize valuation atom =
                                (valuation left).size := by
                          intro atom hmem
                          have hclassMem : atom ∈
                              (seed.addEquality left right).classValues left := by
                            rw [hvalues]
                            exact List.mem_cons_of_mem first hmem
                          exact ⟨
                            hcandidateNonvar.isVarB_eq_false_of_classValue
                              hclassMem,
                            hcandidateSat.solutionAtomSize_classValue
                              hclassMem⟩
                        obtain ⟨matched, hmatch, hmatchedSat,
                            hmatchedNonvar, hmatchedBound⟩ :=
                          exists_nonvariableMatchListAccRel_at_solutionSize
                            (ih _ hleftBound)
                            ((hesat_empty_iff valuation).mpr trivial)
                            (by
                              simp [HEAssignmentsNonVariable, Bindings.empty])
                            (heBindingSolutionSizeBound_empty valuation
                              (valuation left).size)
                            hlists hleftData hrightData
                        obtain ⟨out, hmerge, _houtSat, houtNonvar⟩ :=
                          ih _ hleftBound hcandidateSat hcandidateNonvar
                            hmatchedSat hmatchedNonvar hmatchedBound
                        have hclassInconsistent : Bindings.valuesConsistent
                            (first :: second :: third :: rest) = false := by
                          simpa [hvalues] using hconsistent
                        let hadd : AddVarEqualityRel seed left right out :=
                          .classConflict hvalues hclassInconsistent hmatch hmerge
                        exact ⟨out, hadd,
                          addVarEqualityRel_satisfied hadd hseed hequality,
                          houtNonvar⟩

/-- Satisfiable merge-back for every actual HE matcher result.  The finite
ceiling is obtained from the two source atoms; the matcher size theorem then
certifies the right record required by `satisfiedMergeRelCompleteBelow`. -/
theorem heSatisfiedMatcherMergeRelExists_solutionSize :
    HESatisfiedMatcherMergeRelExists := by
  intro valuation seed matched left right hmatch hseed hseedNonvar hmatched
  let bound := max
      (HESolutionAtomSize valuation left)
      (HESolutionAtomSize valuation right) + 1
  have hleftBound : HESolutionAtomSize valuation left < bound := by
    exact (Nat.le_max_left _ _).trans_lt (Nat.lt_succ_self _)
  have hrightBound : HESolutionAtomSize valuation right < bound := by
    exact (Nat.le_max_right _ _).trans_lt (Nat.lt_succ_self _)
  have hmatchedBound :
      HEBindingSolutionSizeBound valuation matched bound :=
    matchRel_solutionSizeBound hmatch hleftBound hrightBound
  obtain ⟨out, hmerge, _houtSat, _houtNonvar⟩ :=
    satisfiedMergeRelCompleteBelow valuation bound
      hseed hseedNonvar hmatched
      (heAssignmentsNonVariable_of_matchRel hmatch) hmatchedBound
  exact ⟨out, hmerge⟩

/-- Packed form consumed by the existing matcher-completeness and conformance
ladder. -/
theorem heSatisfiedMatcherMergeRelComplete_solutionSize :
    HESatisfiedMatcherMergeRelComplete :=
  heSatisfiedMatcherMergeRelComplete_of_exists
    heSatisfiedMatcherMergeRelExists_solutionSize

/-- Assumption-free semantic completeness of the declarative HE matcher.
The recursive expression/list proof is the existing representation-free
construction; semantic-size merge-back supplies its former local premise. -/
theorem exists_matchRel_of_solution_solutionSize
    {left right : Atom} {valuation : String → Metta.Atom}
    (hequation : HEAtomEquationSatisfied valuation left right) :
    ∃ out, DeclMatchSpec.MatchRel left right out :=
  exists_matchRel_of_solution_of_merge
    heSatisfiedMatcherMergeRelComplete_solutionSize hequation

/-- Executable finite-fuel form of assumption-free semantic matcher
completeness. -/
theorem exists_matchAtoms_of_solution_solutionSize
    {left right : Atom} {valuation : String → Metta.Atom}
    (hequation : HEAtomEquationSatisfied valuation left right) :
    ∃ out fuel, out ∈ matchAtoms left right fuel :=
  exists_matchAtoms_of_solution_of_merge
    heSatisfiedMatcherMergeRelComplete_solutionSize hequation

/-- A stored/proposed class-value pair from successful repaired-LeaTTa
reconciliation is an actual HE matcher success, with no abstract merge
completeness argument left at the call site. -/
theorem exists_matchAtoms_classValue_of_reconciliation_solutionSize
    {b : Bindings} {source : Metta.Bindings}
    {key : String} {stored proposed : Atom} {result : Metta.Subst}
    (hbase : LeaBindingCongruence b source)
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hreconcile : wholeBindingReconciliation source
      [(.var key, toLeaTTaAtom proposed)] = some result)
    (hstored : stored ∈ b.classValues key) :
    ∃ out fuel, out ∈ matchAtoms stored proposed fuel :=
  exists_matchAtoms_classValue_of_reconciliation_of_merge
    heSatisfiedMatcherMergeRelComplete_solutionSize
      hbase hsourceNoFloat hreconcile hstored

/-- Joined-class counterpart of the preceding assumption-free operational
matcher witness. -/
theorem exists_matchAtoms_joinedClassValues_of_reconciliation_solutionSize
    {b : Bindings} {source : Metta.Bindings}
    {left right : String} {first second : Atom} {result : Metta.Subst}
    (hbase : LeaBindingCongruence b source)
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hreconcile : wholeBindingReconciliation source
      [(.var left, .var right)] = some result)
    (hfirst : first ∈ (b.addEquality left right).classValues left)
    (hsecond : second ∈ (b.addEquality left right).classValues left) :
    ∃ out fuel, out ∈ matchAtoms first second fuel :=
  exists_matchAtoms_joinedClassValues_of_reconciliation_of_merge
    heSatisfiedMatcherMergeRelComplete_solutionSize
      hbase hsourceNoFloat hreconcile hfirst hsecond

/-- Assumption-free reconciliation alias merge obtained from the semantic-size
matcher/merge theorem.  This is the concrete operational instance of
`HEReconciliationMatcherCongruenceWitness.exists_liveAliasMerge`; downstream
reverse-transport proofs no longer need to quantify over the former
merge-completeness interface. -/
theorem HEReconciliationMatcherCongruenceWitness.exists_liveAliasMerge_solutionSize
    {b : Bindings} {source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (w : HEReconciliationMatcherCongruenceWitness source extra result)
    (hbase : LeaBindingCongruence b source)
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hextraNoFloat : ∀ equation ∈ extra,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2)
    (hreconcile : wholeBindingReconciliation source extra = some result) :
    ∃ aliasRecord merged left right matchFuel mergeFuel,
      LeaAliasTraceReplay Bindings.empty
          (Metta.Bindings.reconciliationAliases source extra result)
          aliasRecord ∧
        aliasRecord ∈
          matchAtoms (.expression left) (.expression right) matchFuel ∧
        merged ∈ mergeBindings w.mid aliasRecord mergeFuel ∧
        HEMatcherMergeChain w.mid merged ∧
        HEAssignmentsNonVariable merged ∧
        LeaBindingSolutionTheoryEquiv merged
          (Metta.Bindings.rebuildFromReconciliation
            source source extra result) :=
  w.exists_liveAliasMerge heSatisfiedMatcherMergeRelComplete_solutionSize
    hbase hsourceNoFloat hextraNoFloat hreconcile

/-- Any one certified live merge of the repaired alias replay has full
binding congruence.  Unlike the semantic existence theorem above, this
statement lets the derivation-local mutual kernel choose its own concrete
matcher and merge outputs.  Their solution theory is reconstructed from the
actual merge and the alias replay, so no MGU presentation or representative
chronology enters the certificate boundary. -/
theorem HEReconciliationMatcherCongruenceWitness.liveAliasMergeCongruence_of_certificates
    {b : Bindings} {source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (w : HEReconciliationMatcherCongruenceWitness source extra result)
    (hbase : LeaBindingCongruence b source)
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hextraNoFloat : ∀ equation ∈ extra,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2)
    (hreconcile : wholeBindingReconciliation source extra = some result)
    {aliasRecord merged : Bindings} {mergeFuel : Nat}
    (halias : LeaAliasTraceReplay Bindings.empty
      (Metta.Bindings.reconciliationAliases source extra result)
      aliasRecord)
    (hmerge : merged ∈ mergeBindings w.mid aliasRecord mergeFuel)
    (htraceSound : MergeTraceSound
      (unificationEliminationTrace
        (Metta.Bindings.equationFuel
          (Metta.Bindings.equations source ++ extra))
        (Metta.Bindings.equations source ++ extra))
      (mergeBindings_sound hmerge))
    (hboundSound : MergeEqualityClosureBoundSound
      (Metta.Bindings.reconciliationAliases source extra result)
      (mergeBindings_sound hmerge)) :
    LeaBindingCongruence merged
      (Metta.Bindings.rebuildFromReconciliation
        source source extra result) := by
  have hheTheory : ∀ solution,
      HEBindingSatisfied solution merged ↔
        HEBindingSatisfied solution b ∧
          MettaEquationsSatisfied solution extra := by
    intro solution
    rw [mergeBindings_solution_iff hmerge solution]
    constructor
    · rintro ⟨hmid, _haliasRecord⟩
      have hresultSolution : MettaConstraintsSatisfied solution result :=
        (leaOfSubst_solution_iff solution result).mp
          ((w.midResultCongruence.semantic.solutions solution).mp hmid)
      have hsourceExtra :=
        (wholeBindingReconciliation_solution_iff solution
          hsourceNoFloat hextraNoFloat hreconcile).mp hresultSolution
      exact ⟨(hbase.semantic.solutions solution).mpr hsourceExtra.1,
        hsourceExtra.2⟩
    · rintro ⟨hb, hextra⟩
      have hsource : LeaBindingSatisfied solution source :=
        (hbase.semantic.solutions solution).mp hb
      have hresultSolution : MettaConstraintsSatisfied solution result :=
        (wholeBindingReconciliation_solution_iff solution
          hsourceNoFloat hextraNoFloat hreconcile).mpr ⟨hsource, hextra⟩
      have hmid : HEBindingSatisfied solution w.mid :=
        (w.midResultCongruence.semantic.solutions solution).mpr
          ((leaOfSubst_solution_iff solution result).mpr hresultSolution)
      have haliasRecord : HEBindingSatisfied solution aliasRecord := by
        apply (halias.satisfaction_iff solution).mpr
        intro edge hedge
        exact wholeBindingReconciliation_aliases_satisfied solution
          hsourceNoFloat hextraNoFloat hreconcile hresultSolution edge hedge
      exact ⟨hmid, haliasRecord⟩
  exact w.liveAliasMergeCongruence hbase hsourceNoFloat
    hextraNoFloat hreconcile halias hmerge htraceSound hboundSound hheTheory

/-- The semantic-size live-alias witness upgrades to full repaired-LeaTTa
congruence once the two certificates belonging to its *actual* merge
derivation are supplied.  This packages the already-proved operational
existence and solution theory without imposing a global matcher hypothesis:
the remaining obligations are precisely trace provenance and equality-closure
soundness for the returned `MergeRel`. -/
theorem HEReconciliationMatcherCongruenceWitness.exists_liveAliasMergeCongruent_solutionSize
    {b : Bindings} {source : Metta.Bindings}
    {extra : List (Metta.Atom × Metta.Atom)} {result : Metta.Subst}
    (w : HEReconciliationMatcherCongruenceWitness source extra result)
    (hbase : LeaBindingCongruence b source)
    (hsourceNoFloat : LeaBindingsNoFloat source)
    (hextraNoFloat : ∀ equation ∈ extra,
      MettaAtomNoFloat equation.1 ∧ MettaAtomNoFloat equation.2)
    (hreconcile : wholeBindingReconciliation source extra = some result)
    (hcert : ∀ {aliasRecord merged : Bindings} {mergeFuel : Nat},
      LeaAliasTraceReplay Bindings.empty
          (Metta.Bindings.reconciliationAliases source extra result)
          aliasRecord →
      (hmerge : merged ∈ mergeBindings w.mid aliasRecord mergeFuel) →
        MergeTraceSound
            (unificationEliminationTrace
              (Metta.Bindings.equationFuel
                (Metta.Bindings.equations source ++ extra))
              (Metta.Bindings.equations source ++ extra))
            (mergeBindings_sound hmerge) ∧
          MergeEqualityClosureBoundSound
            (Metta.Bindings.reconciliationAliases source extra result)
            (mergeBindings_sound hmerge)) :
    ∃ aliasRecord merged left right matchFuel mergeFuel,
      LeaAliasTraceReplay Bindings.empty
          (Metta.Bindings.reconciliationAliases source extra result)
          aliasRecord ∧
        aliasRecord ∈
          matchAtoms (.expression left) (.expression right) matchFuel ∧
        merged ∈ mergeBindings w.mid aliasRecord mergeFuel ∧
        HEMatcherMergeChain w.mid merged ∧
        HEAssignmentsNonVariable merged ∧
        LeaBindingCongruence merged
          (Metta.Bindings.rebuildFromReconciliation
            source source extra result) := by
  obtain ⟨aliasRecord, merged, left, right, matchFuel, mergeFuel,
      halias, hmatch, hmerge, hchain, hnonVariable,
      hsolutionTheory⟩ :=
    w.exists_liveAliasMerge_solutionSize hbase hsourceNoFloat
      hextraNoFloat hreconcile
  obtain ⟨htraceSound, hboundSound⟩ := hcert halias hmerge
  have hheTheory : ∀ valuation,
      HEBindingSatisfied valuation merged ↔
        HEBindingSatisfied valuation b ∧
          MettaEquationsSatisfied valuation extra := by
    intro valuation
    rw [hsolutionTheory valuation,
      rebuildFromReconciliation_solution_iff valuation
        hsourceNoFloat hextraNoFloat hreconcile,
      rebuildBindingsFromUnifier_solution_iff valuation
        hsourceNoFloat hextraNoFloat hreconcile,
      ← hbase.semantic.solutions valuation]
  refine ⟨aliasRecord, merged, left, right, matchFuel, mergeFuel,
    halias, hmatch, hmerge, hchain, hnonVariable, ?_⟩
  exact w.liveAliasMergeCongruence hbase hsourceNoFloat
    hextraNoFloat hreconcile halias hmerge htraceSound hboundSound hheTheory

/-- Size-indexed form of the structural residual sibling fold.  Besides
constructing the existing certified result, it separates the decreasing
atom bound from the fixed global bound on live assignment payloads.  The
head callback therefore receives strict bounds for both original head atoms
and the independent invariant on the live seed.

The invariant is recovered from the actual child `MatchRel` and actual live
`mergeBindings` witness after every head; no semantic-to-operational
inference is used.  The inequality between the two bounds is needed only to
show that a child matcher result is also admissible to the global live seed;
recursive expression descent decreases `atomBound` while leaving
`assignmentBound` unchanged. -/
theorem HEProjectedCertifiedListResidualSolutionState.exists_matchListAcc_of_coreLiveHead_bounded
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {atomBound assignmentBound : Nat}
    (hbound : atomBound ≤ assignmentBound)
    (headBuilder : ∀
      {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
      {outerSubst : Metta.Subst}
      {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
      {subst result : Metta.Subst} {left right : List Atom}
      {seed : Bindings}
      (state : HEProjectedCertifiedListResidualSolutionState
        trace allowed outerFuel front outerSubst fuel work subst result
          left right seed)
      {nextLeft : Atom} {leftRest : List Atom}
      (head : HEProjectedTailHeadResidualSolutionPackage
        state nextLeft leftRest),
      HEAtomSize nextLeft < atomBound →
      HEAtomSize head.nextRight < atomBound →
      HEAssignmentsSizeBound seed assignmentBound →
      Nonempty (HELiveMatchMergeCoreResidualCertified trace allowed
        nextLeft head.nextRight seed head.nextSubst)) :
    ∀ {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
      {outerSubst : Metta.Subst}
      {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
      {subst result : Metta.Subst} {left right : List Atom}
      {seed : Bindings},
      (state : HEProjectedCertifiedListResidualSolutionState
        trace allowed outerFuel front outerSubst fuel work subst result
          left right seed) →
      HEAtomsSizeBound left atomBound →
      HEAtomsSizeBound right atomBound →
      HEAssignmentsSizeBound seed assignmentBound →
      Nonempty (HEMatchListAccSolutionCertified trace allowed
        left right seed result) := by
  intro outerFuel front outerSubst fuel work subst result left
  induction left generalizing outerFuel front outerSubst fuel work subst
      result with
  | nil =>
      intro right seed state _ _ _
      exact state.exists_nilMatch rfl
  | cons nextLeft leftRest ih =>
      intro right seed state hleft hright hseed
      obtain ⟨head⟩ :=
        state.exists_tailHeadResidualPackage
          (nextLeft := nextLeft) (leftRest := leftRest) rfl
      have hrightCons :
          HEAtomsSizeBound (head.nextRight :: head.rightRest) atomBound := by
        simpa only [head.right_eq] using hright
      obtain ⟨headLive⟩ := headBuilder state head
        hleft.head hrightCons.head hseed
      have hmatchedBound :
          HEAssignmentsSizeBound headLive.matcher.out assignmentBound :=
        matchRel_assignmentsSizeBound headLive.matcher.matchRel
          (hleft.head.trans_le hbound) (hrightCons.head.trans_le hbound)
      have hafterBound :
          HEAssignmentsSizeBound headLive.liveMerge.after assignmentBound :=
        mergeBindings_assignmentsSizeBound
          headLive.liveMerge.merge_mem hseed hmatchedBound
      let tailState := head.toProjectedTailStateCore headLive
      obtain ⟨tailMatch⟩ := ih tailState
        hleft.tail hrightCons.tail hafterBound
      exact ⟨{
        out := tailMatch.out
        matchRel := by
          simpa only [HELiveMatchMergeCoreCertified.cons, head.right_eq] using
            (headLive.toHELiveMatchMergeCoreCertified.cons
              tailMatch.toHEMatchListAccCertified).matchRel
        traceSound := by
          simpa only [HELiveMatchMergeCoreCertified.cons, head.right_eq] using
            (headLive.toHELiveMatchMergeCoreCertified.cons
              tailMatch.toHEMatchListAccCertified).traceSound
        equalitySound := by
          simpa only [HELiveMatchMergeCoreCertified.cons, head.right_eq] using
            (headLive.toHELiveMatchMergeCoreCertified.cons
              tailMatch.toHEMatchListAccCertified).equalitySound
        assignmentsSound := tailMatch.assignmentsSound
        solutions := tailMatch.solutions
      }⟩

/-- Covered companion of the two-bound structural sibling fold.  The raw
original-constraint carrier is threaded unchanged so the exhaustive head
dispatcher can close all direct branches from the actual source equation.
The decreasing atom bound and the fixed live-assignment bound remain
independent exactly as in the solution-state theorem above. -/
theorem HEOriginalConstraintCoveredProjectedListState.exists_matchListAcc_of_coreLiveHead_bounded
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {atomBound assignmentBound : Nat}
    (hbound : atomBound ≤ assignmentBound)
    (headBuilder : ∀
      {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
      {outerSubst : Metta.Subst}
      {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
      {subst result : Metta.Subst} {left right : List Atom}
      {seed : Bindings}
      (covered : HEOriginalConstraintCoveredProjectedListState trace allowed
        outerFuel front outerSubst fuel work subst result left right seed)
      {nextLeft : Atom} {leftRest : List Atom}
      (head : HEProjectedTailHeadResidualSolutionPackage
        covered.state nextLeft leftRest),
      HEAtomSize nextLeft < atomBound →
      HEAtomSize head.nextRight < atomBound →
      HEAssignmentsSizeBound seed assignmentBound →
      Nonempty (HELiveMatchMergeCoreResidualCertified trace allowed
        nextLeft head.nextRight seed head.nextSubst)) :
    ∀ {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
      {outerSubst : Metta.Subst}
      {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
      {subst result : Metta.Subst} {left right : List Atom}
      {seed : Bindings},
      (covered : HEOriginalConstraintCoveredProjectedListState trace allowed
        outerFuel front outerSubst fuel work subst result left right seed) →
      HEAtomsSizeBound left atomBound →
      HEAtomsSizeBound right atomBound →
      HEAssignmentsSizeBound seed assignmentBound →
      Nonempty (HEMatchListAccSolutionCertified trace allowed
        left right seed result) := by
  intro outerFuel front outerSubst fuel work subst result left
  induction left generalizing outerFuel front outerSubst fuel work subst
      result with
  | nil =>
      intro right seed covered _ _ _
      exact covered.state.exists_nilMatch rfl
  | cons nextLeft leftRest ih =>
      intro right seed covered hleft hright hseed
      obtain ⟨head⟩ :=
        covered.state.exists_tailHeadResidualPackage
          (nextLeft := nextLeft) (leftRest := leftRest) rfl
      have hrightCons :
          HEAtomsSizeBound (head.nextRight :: head.rightRest) atomBound := by
        simpa only [head.right_eq] using hright
      obtain ⟨headLive⟩ := headBuilder covered head
        hleft.head hrightCons.head hseed
      have hmatchedBound :
          HEAssignmentsSizeBound headLive.matcher.out assignmentBound :=
        matchRel_assignmentsSizeBound headLive.matcher.matchRel
          (hleft.head.trans_le hbound) (hrightCons.head.trans_le hbound)
      have hafterBound :
          HEAssignmentsSizeBound headLive.liveMerge.after assignmentBound :=
        mergeBindings_assignmentsSizeBound
          headLive.liveMerge.merge_mem hseed hmatchedBound
      let tailCovered := head.toCoveredProjectedTailStateCore
        covered headLive
      obtain ⟨tailMatch⟩ := ih tailCovered
        hleft.tail hrightCons.tail hafterBound
      exact ⟨{
        out := tailMatch.out
        matchRel := by
          simpa only [HELiveMatchMergeCoreCertified.cons, head.right_eq] using
            (headLive.toHELiveMatchMergeCoreCertified.cons
              tailMatch.toHEMatchListAccCertified).matchRel
        traceSound := by
          simpa only [HELiveMatchMergeCoreCertified.cons, head.right_eq] using
            (headLive.toHELiveMatchMergeCoreCertified.cons
              tailMatch.toHEMatchListAccCertified).traceSound
        equalitySound := by
          simpa only [HELiveMatchMergeCoreCertified.cons, head.right_eq] using
            (headLive.toHELiveMatchMergeCoreCertified.cons
              tailMatch.toHEMatchListAccCertified).equalitySound
        assignmentsSound := tailMatch.assignmentsSound
        solutions := tailMatch.solutions
      }⟩

/-- One finite common ceiling for the literal atoms and live accumulator of
a covered projected state. -/
structure HECoveredProjectedStateSizeBound
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    (covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed)
    (bound : Nat) : Prop where
  left : HEAtomsSizeBound left bound
  right : HEAtomsSizeBound right bound
  seed : HEAssignmentsSizeBound seed bound

/-- Every covered projected state admits a finite common size ceiling. -/
theorem HECoveredProjectedStateSizeBound.exists
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    (covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed) :
    ∃ bound, HECoveredProjectedStateSizeBound covered bound := by
  obtain ⟨leftBound, hleft⟩ := exists_heAtomsSizeBound left
  obtain ⟨rightBound, hright⟩ := exists_heAtomsSizeBound right
  obtain ⟨seedBound, hseed⟩ := exists_heAssignmentsSizeBound seed
  let bound := max leftBound (max rightBound seedBound)
  refine ⟨bound, ?_⟩
  exact {
    left := hleft.mono (Nat.le_max_left _ _)
    right := hright.mono
      ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))
    seed := hseed.mono
      ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
  }

theorem HECoveredProjectedStateSizeBound.nextLeft
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings} {bound : Nat}
    {covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed}
    (h : HECoveredProjectedStateSizeBound covered bound)
    {nextLeft : Atom} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state nextLeft leftRest) :
    HEAtomSize nextLeft < bound := by
  apply h.left nextLeft
  rw [p.left_eq]
  simp

theorem HECoveredProjectedStateSizeBound.nextRight
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings} {bound : Nat}
    {covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed}
    (h : HECoveredProjectedStateSizeBound covered bound)
    {nextLeft : Atom} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state nextLeft leftRest) :
    HEAtomSize p.nextRight < bound := by
  apply h.right p.nextRight
  simpa only [p.right_eq] using
    (show p.nextRight ∈ p.nextRight :: p.rightRest by simp)

/-- Every value visible through a live equality class inherits the current
state's assignment-payload ceiling. -/
theorem HECoveredProjectedStateSizeBound.classValues
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings} {bound : Nat}
    {covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed}
    (h : HECoveredProjectedStateSizeBound covered bound)
    (key : String) :
    HEAtomsSizeBound (seed.classValues key) bound := by
  intro value hvalue
  exact h.seed.classValue hvalue

/-- Joining two equality classes changes no assignment payload, so every
candidate class value remains under the same ceiling. -/
theorem HECoveredProjectedStateSizeBound.addEqualityClassValues
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings} {bound : Nat}
    {covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed}
    (h : HECoveredProjectedStateSizeBound covered bound)
    (leftKey rightKey : String) :
    HEAtomsSizeBound
      ((seed.addEquality leftKey rightKey).classValues leftKey) bound := by
  intro value hvalue
  exact (h.seed.addEquality leftKey rightKey).classValue hvalue

/-- The literal atom pair selected by a value conflict lies under the
current common state ceiling. -/
theorem HECoveredProjectedStateSizeBound.assignmentConflictPair
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings} {bound : Nat}
    {covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed}
    (h : HECoveredProjectedStateSizeBound covered bound)
    {key : String} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state (.var key) leftRest)
    {value first : Atom} {rest : List Atom}
    (hright : p.nextRight = value)
    (hclass : seed.classValues key = first :: rest) :
    HEAtomSize first < bound ∧ HEAtomSize value < bound := by
  constructor
  · apply (h.classValues key) first
    rw [hclass]
    simp
  · simpa only [hright] using h.nextRight p

/-- Both pointwise lists used by class-wide value reconciliation remain
under the current common state ceiling. -/
theorem HECoveredProjectedStateSizeBound.assignmentReconcileLists
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings} {bound : Nat}
    {covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed}
    (h : HECoveredProjectedStateSizeBound covered bound)
    {key : String} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state (.var key) leftRest)
    {value first : Atom} {rest : List Atom}
    (hright : p.nextRight = value)
    (hclass : seed.classValues key = first :: rest) :
    HEAtomsSizeBound (List.replicate (rest.length + 1) first) bound ∧
      HEAtomsSizeBound (rest ++ [value]) bound := by
  have hclassBound : HEAtomsSizeBound (first :: rest) bound := by
    simpa only [hclass] using h.classValues key
  constructor
  · exact HEAtomsSizeBound.replicate hclassBound.head
  · exact hclassBound.tail.append (by
      intro atom hmem
      simp only [List.mem_singleton] at hmem
      subst atom
      simpa only [hright] using h.nextRight p)

/-- The two values selected by the equality-pair conflict remain bounded
after the candidate edge is added. -/
theorem HECoveredProjectedStateSizeBound.equalityConflictPair
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings} {bound : Nat}
    {covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed}
    (h : HECoveredProjectedStateSizeBound covered bound)
    (leftKey rightKey : String) {first second : Atom}
    (hvalues : (seed.addEquality leftKey rightKey).classValues leftKey =
      [first, second]) :
    HEAtomSize first < bound ∧ HEAtomSize second < bound := by
  have hall : HEAtomsSizeBound [first, second] bound := by
    simpa only [hvalues] using h.addEqualityClassValues leftKey rightKey
  exact ⟨hall.head, hall.tail.head⟩

/-- Both pointwise lists used by class-wide equality reconciliation remain
under the same candidate-state ceiling. -/
theorem HECoveredProjectedStateSizeBound.equalityReconcileLists
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings} {bound : Nat}
    {covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed}
    (h : HECoveredProjectedStateSizeBound covered bound)
    (leftKey rightKey : String) {first second third : Atom}
    {rest : List Atom}
    (hvalues : (seed.addEquality leftKey rightKey).classValues leftKey =
      first :: second :: third :: rest) :
    HEAtomsSizeBound (List.replicate (rest.length + 2) first) bound ∧
      HEAtomsSizeBound (second :: third :: rest) bound := by
  have hall : HEAtomsSizeBound (first :: second :: third :: rest) bound := by
    simpa only [hvalues] using h.addEqualityClassValues leftKey rightKey
  exact ⟨HEAtomsSizeBound.replicate hall.head, hall.tail⟩

/-! ### State-local semantic-size descent

The structural ceiling above is intentionally retained for sibling folds,
but it cannot be the recursive conflict measure: a live class value can tie
the raw syntax size of the expression that exposed it.  Under the common
valuation carried by a successful projected state, every stored value in the
selected class instead denotes exactly the variable occurrence at that
position.  The following lighter carrier bounds only the current literal
atoms; unrelated assignments already present in the live seed are not
measured. -/

/-- Common-solution ceiling for the literal atoms of one covered projected
state.  The live seed is deliberately omitted: only class values selected by
one bounded literal variable may participate in its conflict. -/
structure HECoveredProjectedStateSolutionSizeBound
    (valuation : String → Metta.Atom)
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    (covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed)
    (bound : Nat) : Prop where
  left : HESolutionAtomsSizeBound valuation left bound
  right : HESolutionAtomsSizeBound valuation right bound

/-- Finiteness of the two literal lists supplies a semantic ceiling at every
covered state; no bound on unrelated live-seed assignments is needed. -/
theorem exists_HECoveredProjectedStateSolutionSizeBound
    (valuation : String → Metta.Atom)
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    (covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed) :
    ∃ bound,
      HECoveredProjectedStateSolutionSizeBound valuation covered bound := by
  obtain ⟨leftBound, hleft⟩ :=
    exists_heSolutionAtomsSizeBound valuation left
  obtain ⟨rightBound, hright⟩ :=
    exists_heSolutionAtomsSizeBound valuation right
  refine ⟨max leftBound rightBound, ?_⟩
  exact {
    left := hleft.mono (Nat.le_max_left _ _)
    right := hright.mono (Nat.le_max_right _ _)
  }

theorem HECoveredProjectedStateSolutionSizeBound.nextLeft
    {valuation : String → Metta.Atom}
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings} {bound : Nat}
    {covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed}
    (h : HECoveredProjectedStateSolutionSizeBound valuation covered bound)
    {nextLeft : Atom} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state nextLeft leftRest) :
    HESolutionAtomSize valuation nextLeft < bound := by
  apply h.left nextLeft
  rw [p.left_eq]
  simp

theorem HECoveredProjectedStateSolutionSizeBound.nextRight
    {valuation : String → Metta.Atom}
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings} {bound : Nat}
    {covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed}
    (h : HECoveredProjectedStateSolutionSizeBound valuation covered bound)
    {nextLeft : Atom} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state nextLeft leftRest) :
    HESolutionAtomSize valuation p.nextRight < bound := by
  apply h.right p.nextRight
  simpa only [p.right_eq] using
    (show p.nextRight ∈ p.nextRight :: p.rightRest by simp)

/-- In a satisfying variable/non-variable head, the selected stored class
value and the proposed literal have the same semantic size; hence both are
strictly below the current literal ceiling. -/
theorem HECoveredProjectedStateSolutionSizeBound.assignmentConflictPair
    {valuation : String → Metta.Atom}
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings} {bound : Nat}
    {covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed}
    (h : HECoveredProjectedStateSolutionSizeBound valuation covered bound)
    (htrace : MettaConstraintsSatisfied valuation trace)
    {key : String} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state (.var key) leftRest)
    {value first : Atom} {rest : List Atom}
    (hright : p.nextRight = value)
    (hclass : seed.classValues key = first :: rest) :
    HESolutionAtomSize valuation first < bound ∧
      HESolutionAtomSize valuation value < bound := by
  have hhead := p.headSatisfied_of_trace valuation htrace
  have hfirstMem : first ∈ seed.classValues key := by
    rw [hclass]
    simp
  have hfirstSize : HESolutionAtomSize valuation first =
      (valuation key).size :=
    hhead.1.solutionAtomSize_classValue hfirstMem
  have hvalueEq : valuation key =
      applyClassSolution valuation (toLeaTTaAtom value) := by
    have hequation := hhead.2
    rw [hright] at hequation
    simpa [MettaEquationSatisfied, applyClassSolution] using hequation
  have hvalueSize : HESolutionAtomSize valuation value =
      (valuation key).size := by
    exact congrArg Metta.Atom.size hvalueEq.symm
  have hproposed : HESolutionAtomSize valuation value < bound := by
    simpa only [hright] using h.nextRight p
  exact ⟨by simpa only [hfirstSize, hvalueSize] using hproposed,
    hproposed⟩

/-- Class-wide assignment reconciliation inherits the same strict semantic
ceiling pointwise on both literal runtime lists. -/
theorem HECoveredProjectedStateSolutionSizeBound.assignmentReconcileLists
    {valuation : String → Metta.Atom}
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings} {bound : Nat}
    {covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed}
    (h : HECoveredProjectedStateSolutionSizeBound valuation covered bound)
    (htrace : MettaConstraintsSatisfied valuation trace)
    {key : String} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state (.var key) leftRest)
    {value first : Atom} {rest : List Atom}
    (hright : p.nextRight = value)
    (hclass : seed.classValues key = first :: rest) :
    HESolutionAtomsSizeBound valuation
        (List.replicate (rest.length + 1) first) bound ∧
      HESolutionAtomsSizeBound valuation (rest ++ [value]) bound := by
  have hhead := p.headSatisfied_of_trace valuation htrace
  have hproposed := (h.assignmentConflictPair htrace p hright hclass).2
  have hall : HESolutionAtomsSizeBound valuation (first :: rest) bound := by
    intro atom hmem
    have hclassMem : atom ∈ seed.classValues key := by
      rw [hclass]
      exact hmem
    have hatomSize : HESolutionAtomSize valuation atom =
        (valuation key).size :=
      hhead.1.solutionAtomSize_classValue hclassMem
    have hvalueEq : valuation key =
        applyClassSolution valuation (toLeaTTaAtom value) := by
      have hequation := hhead.2
      rw [hright] at hequation
      simpa [MettaEquationSatisfied, applyClassSolution] using hequation
    have hvalueSize : HESolutionAtomSize valuation value =
        (valuation key).size :=
      congrArg Metta.Atom.size hvalueEq.symm
    simpa only [hatomSize, hvalueSize] using hproposed
  refine ⟨HESolutionAtomsSizeBound.replicate hall.head,
    hall.tail.append ?_⟩
  intro atom hmem
  simp only [List.mem_singleton] at hmem
  subst atom
  exact hproposed

/-- Symmetric non-variable/variable conflict pair.  The proposed left atom
and every stored value in the right variable's class denote the same term. -/
theorem HECoveredProjectedStateSolutionSizeBound.nonVarVarConflictPair
    {valuation : String → Metta.Atom}
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings} {bound : Nat}
    {covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed}
    (h : HECoveredProjectedStateSolutionSizeBound valuation covered bound)
    (htrace : MettaConstraintsSatisfied valuation trace)
    {value : Atom} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state value leftRest)
    {key : String} {first : Atom} {rest : List Atom}
    (hright : p.nextRight = .var key)
    (hclass : seed.classValues key = first :: rest) :
    HESolutionAtomSize valuation first < bound ∧
      HESolutionAtomSize valuation value < bound := by
  have hhead := p.headSatisfied_of_trace valuation htrace
  have hfirstMem : first ∈ seed.classValues key := by
    rw [hclass]
    simp
  have hfirstSize : HESolutionAtomSize valuation first =
      (valuation key).size :=
    hhead.1.solutionAtomSize_classValue hfirstMem
  have hvalueEq : valuation key =
      applyClassSolution valuation (toLeaTTaAtom value) := by
    have hequation := hhead.2
    rw [hright] at hequation
    simpa [MettaEquationSatisfied, applyClassSolution] using hequation.symm
  have hvalueSize : HESolutionAtomSize valuation value =
      (valuation key).size :=
    congrArg Metta.Atom.size hvalueEq.symm
  have hproposed : HESolutionAtomSize valuation value < bound :=
    h.nextLeft p
  exact ⟨by simpa only [hfirstSize, hvalueSize] using hproposed,
    hproposed⟩

/-- Symmetric class-wide reconciliation list bound. -/
theorem HECoveredProjectedStateSolutionSizeBound.nonVarVarReconcileLists
    {valuation : String → Metta.Atom}
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings} {bound : Nat}
    {covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed}
    (h : HECoveredProjectedStateSolutionSizeBound valuation covered bound)
    (htrace : MettaConstraintsSatisfied valuation trace)
    {value : Atom} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state value leftRest)
    {key : String} {first : Atom} {rest : List Atom}
    (hright : p.nextRight = .var key)
    (hclass : seed.classValues key = first :: rest) :
    HESolutionAtomsSizeBound valuation
        (List.replicate (rest.length + 1) first) bound ∧
      HESolutionAtomsSizeBound valuation (rest ++ [value]) bound := by
  have hhead := p.headSatisfied_of_trace valuation htrace
  have hproposed := (h.nonVarVarConflictPair htrace p hright hclass).2
  have hall : HESolutionAtomsSizeBound valuation (first :: rest) bound := by
    intro atom hmem
    have hclassMem : atom ∈ seed.classValues key := by
      rw [hclass]
      exact hmem
    have hatomSize : HESolutionAtomSize valuation atom =
        (valuation key).size :=
      hhead.1.solutionAtomSize_classValue hclassMem
    have hvalueEq : valuation key =
        applyClassSolution valuation (toLeaTTaAtom value) := by
      have hequation := hhead.2
      rw [hright] at hequation
      simpa [MettaEquationSatisfied, applyClassSolution] using
        hequation.symm
    have hvalueSize : HESolutionAtomSize valuation value =
        (valuation key).size :=
      congrArg Metta.Atom.size hvalueEq.symm
    simpa only [hatomSize, hvalueSize] using hproposed
  refine ⟨HESolutionAtomsSizeBound.replicate hall.head,
    hall.tail.append ?_⟩
  intro atom hmem
  simp only [List.mem_singleton] at hmem
  subst atom
  exact hproposed

/-- The two selected values of an inconsistent joined equality class are
strictly below the current variable/variable literal ceiling. -/
theorem HECoveredProjectedStateSolutionSizeBound.equalityConflictPair
    {valuation : String → Metta.Atom}
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {leftAtoms rightAtoms : List Atom}
    {seed : Bindings} {bound : Nat}
    {covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result
        leftAtoms rightAtoms seed}
    (h : HECoveredProjectedStateSolutionSizeBound valuation covered bound)
    (htrace : MettaConstraintsSatisfied valuation trace)
    {left : String} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state (.var left) leftRest)
    {right : String} {first second : Atom}
    (hright : p.nextRight = .var right)
    (hvalues : (seed.addEquality left right).classValues left =
      [first, second]) :
    HESolutionAtomSize valuation first < bound ∧
      HESolutionAtomSize valuation second < bound := by
  have hhead := p.headSatisfied_of_trace valuation htrace
  have hequality : valuation left = valuation right := by
    have hequation := hhead.2
    rw [hright] at hequation
    simpa [MettaEquationSatisfied, applyClassSolution] using hequation
  have hcandidate : HEBindingSatisfied valuation
      (seed.addEquality left right) :=
    (heBindingSatisfied_addEquality_iff valuation seed left right).mpr
      ⟨hhead.1, hequality⟩
  have hleftBound : (valuation left).size < bound := by
    simpa only [heSolutionAtomSize_var] using h.nextLeft p
  constructor
  · have hmem : first ∈
        (seed.addEquality left right).classValues left := by
      rw [hvalues]
      simp
    simpa only [hcandidate.solutionAtomSize_classValue hmem] using
      hleftBound
  · have hmem : second ∈
        (seed.addEquality left right).classValues left := by
      rw [hvalues]
      simp
    simpa only [hcandidate.solutionAtomSize_classValue hmem] using
      hleftBound

/-- Whole joined-class reconciliation is pointwise strictly bounded on both
literal lists, independently of their runtime ordering. -/
theorem HECoveredProjectedStateSolutionSizeBound.equalityReconcileLists
    {valuation : String → Metta.Atom}
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {leftAtoms rightAtoms : List Atom}
    {seed : Bindings} {bound : Nat}
    {covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result
        leftAtoms rightAtoms seed}
    (h : HECoveredProjectedStateSolutionSizeBound valuation covered bound)
    (htrace : MettaConstraintsSatisfied valuation trace)
    {left : String} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state (.var left) leftRest)
    {right : String} {first second third : Atom} {rest : List Atom}
    (hright : p.nextRight = .var right)
    (hvalues : (seed.addEquality left right).classValues left =
      first :: second :: third :: rest) :
    HESolutionAtomsSizeBound valuation
        (List.replicate (rest.length + 2) first) bound ∧
      HESolutionAtomsSizeBound valuation (second :: third :: rest) bound := by
  have hhead := p.headSatisfied_of_trace valuation htrace
  have hequality : valuation left = valuation right := by
    have hequation := hhead.2
    rw [hright] at hequation
    simpa [MettaEquationSatisfied, applyClassSolution] using hequation
  have hcandidate : HEBindingSatisfied valuation
      (seed.addEquality left right) :=
    (heBindingSatisfied_addEquality_iff valuation seed left right).mpr
      ⟨hhead.1, hequality⟩
  have hleftBound : (valuation left).size < bound := by
    simpa only [heSolutionAtomSize_var] using h.nextLeft p
  have hall : HESolutionAtomsSizeBound valuation
      (first :: second :: third :: rest) bound := by
    intro atom hmem
    have hclassMem : atom ∈
        (seed.addEquality left right).classValues left := by
      rw [hvalues]
      exact hmem
    simpa only [hcandidate.solutionAtomSize_classValue hclassMem] using
      hleftBound
  exact ⟨HESolutionAtomsSizeBound.replicate hall.head, hall.tail⟩

/-- Retargeting an original expression head to its literal child lists
strictly lowers the common-solution ceiling while retaining the exact ambient
trace, equality graph, Robinson projection, and original-constraint
coverage.  The new ceiling is presentation-independent: it is the maximum of
the two interpreted expression roots. -/
theorem HECoveredProjectedStateSolutionSizeBound.nestedExpression
    {valuation : String → Metta.Atom}
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings} {bound : Nat}
    {covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed}
    (h : HECoveredProjectedStateSolutionSizeBound valuation covered bound)
    {nextLeft : Atom} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state nextLeft leftRest)
    {leftAtoms rightAtoms : List Atom}
    (hleft : nextLeft = .expression leftAtoms)
    (hright : p.nextRight = .expression rightAtoms) :
    ∃ childBound, childBound < bound ∧
      HECoveredProjectedStateSolutionSizeBound valuation
        (p.toCoveredProjectedNestedState covered hleft hright) childBound := by
  let leftRoot := HESolutionAtomSize valuation (.expression leftAtoms)
  let rightRoot := HESolutionAtomSize valuation (.expression rightAtoms)
  let childBound := max leftRoot rightRoot
  have hleftRoot : leftRoot < bound := by
    simpa only [leftRoot, hleft] using h.nextLeft p
  have hrightRoot : rightRoot < bound := by
    simpa only [rightRoot, hright] using h.nextRight p
  refine ⟨childBound, Nat.max_lt.mpr ⟨hleftRoot, hrightRoot⟩, ?_⟩
  constructor
  · intro atom hmem
    exact (heSolutionAtomSize_lt_expression_of_mem valuation hmem).trans_le
      (Nat.le_max_left leftRoot rightRoot)
  · intro atom hmem
    exact (heSolutionAtomSize_lt_expression_of_mem valuation hmem).trans_le
      (Nat.le_max_right leftRoot rightRoot)

/-- Semantic-size-indexed covered sibling fold.  The fixed ceiling belongs
only to the literal atom lists.  Each actual live merge may enlarge or expose
the accumulator arbitrarily; the remaining original siblings retain their
pointwise bounds definitionally. -/
theorem HEOriginalConstraintCoveredProjectedListState.exists_matchListAcc_of_coreLiveHead_solutionSizeBounded
    {valuation : String → Metta.Atom}
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {bound : Nat}
    (headBuilder : ∀
      {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
      {outerSubst : Metta.Subst}
      {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
      {subst result : Metta.Subst} {left right : List Atom}
      {seed : Bindings}
      (covered : HEOriginalConstraintCoveredProjectedListState trace allowed
        outerFuel front outerSubst fuel work subst result left right seed)
      {nextLeft : Atom} {leftRest : List Atom}
      (head : HEProjectedTailHeadResidualSolutionPackage
        covered.state nextLeft leftRest),
      HESolutionAtomSize valuation nextLeft < bound →
      HESolutionAtomSize valuation head.nextRight < bound →
      Nonempty (HELiveMatchMergeCoreResidualCertified trace allowed
        nextLeft head.nextRight seed head.nextSubst)) :
    ∀ {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
      {outerSubst : Metta.Subst}
      {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
      {subst result : Metta.Subst} {left right : List Atom}
      {seed : Bindings},
      (covered : HEOriginalConstraintCoveredProjectedListState trace allowed
        outerFuel front outerSubst fuel work subst result left right seed) →
      HESolutionAtomsSizeBound valuation left bound →
      HESolutionAtomsSizeBound valuation right bound →
      Nonempty (HEMatchListAccSolutionCertified trace allowed
        left right seed result) := by
  intro outerFuel front outerSubst fuel work subst result left
  induction left generalizing outerFuel front outerSubst fuel work subst
      result with
  | nil =>
      intro right seed covered _ _
      exact covered.state.exists_nilMatch rfl
  | cons nextLeft leftRest ih =>
      intro right seed covered hleft hright
      obtain ⟨head⟩ :=
        covered.state.exists_tailHeadResidualPackage
          (nextLeft := nextLeft) (leftRest := leftRest) rfl
      have hrightCons : HESolutionAtomsSizeBound valuation
          (head.nextRight :: head.rightRest) bound := by
        simpa only [head.right_eq] using hright
      obtain ⟨headLive⟩ := headBuilder covered head
        hleft.head hrightCons.head
      let tailCovered := head.toCoveredProjectedTailStateCore
        covered headLive
      obtain ⟨tailMatch⟩ := ih tailCovered hleft.tail hrightCons.tail
      exact ⟨{
        out := tailMatch.out
        matchRel := by
          simpa only [HELiveMatchMergeCoreCertified.cons, head.right_eq] using
            (headLive.toHELiveMatchMergeCoreCertified.cons
              tailMatch.toHEMatchListAccCertified).matchRel
        traceSound := by
          simpa only [HELiveMatchMergeCoreCertified.cons, head.right_eq] using
            (headLive.toHELiveMatchMergeCoreCertified.cons
              tailMatch.toHEMatchListAccCertified).traceSound
        equalitySound := by
          simpa only [HELiveMatchMergeCoreCertified.cons, head.right_eq] using
            (headLive.toHELiveMatchMergeCoreCertified.cons
              tailMatch.toHEMatchListAccCertified).equalitySound
        assignmentsSound := tailMatch.assignmentsSound
        solutions := tailMatch.solutions
      }⟩

/-- Exhaustive projected-head kernel at one common-solution ceiling.  This is
the semantic replacement for the older branchwise raw-size kernel: it bounds
only the two literal atoms selected from the original constraint carrier and
places no restriction on unrelated payloads already present in the live
accumulator. -/
structure HESolutionSizeBoundedProjectedHeadKernel
    (valuation : String → Metta.Atom)
    (trace : List (String × Metta.Atom))
    (allowed : List (String × String)) (bound : Nat) where
  head : ∀
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    (covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed)
    {nextLeft : Atom} {leftRest : List Atom}
    (selected : HEProjectedTailHeadResidualSolutionPackage
      covered.state nextLeft leftRest),
    HECoveredProjectedStateSolutionSizeBound valuation covered bound →
    Nonempty (HELiveMatchMergeCoreResidualCertified trace allowed
      nextLeft selected.nextRight seed selected.nextSubst)

/-- A semantic-size head kernel closes the complete sibling traversal at the
same ceiling.  The proof is the datatype's accumulator-threaded list
recursion; no fuel alignment or seed-extraction law is involved. -/
theorem HESolutionSizeBoundedProjectedHeadKernel.matchListAcc
    {valuation : String → Metta.Atom}
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {bound : Nat}
    (kernel : HESolutionSizeBoundedProjectedHeadKernel
      valuation trace allowed bound) :
    ∀ {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
      {outerSubst : Metta.Subst}
      {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
      {subst result : Metta.Subst} {left right : List Atom}
      {seed : Bindings},
      (covered : HEOriginalConstraintCoveredProjectedListState trace allowed
        outerFuel front outerSubst fuel work subst result left right seed) →
      HESolutionAtomsSizeBound valuation left bound →
      HESolutionAtomsSizeBound valuation right bound →
      Nonempty (HEMatchListAccSolutionCertified trace allowed
        left right seed result) := by
  intro outerFuel front outerSubst fuel work subst result left
  induction left generalizing outerFuel front outerSubst fuel work subst
      result with
  | nil =>
      intro right seed covered _ _
      exact covered.state.exists_nilMatch rfl
  | cons nextLeft leftRest ih =>
      intro right seed covered hleft hright
      obtain ⟨selected⟩ :=
        covered.state.exists_tailHeadResidualPackage
          (nextLeft := nextLeft) (leftRest := leftRest) rfl
      have hrightCons : HESolutionAtomsSizeBound valuation
          (selected.nextRight :: selected.rightRest) bound := by
        simpa only [selected.right_eq] using hright
      obtain ⟨headLive⟩ := kernel.head covered selected ⟨hleft, hright⟩
      let tailCovered := selected.toCoveredProjectedTailStateCore
        covered headLive
      obtain ⟨tailMatch⟩ := ih tailCovered hleft.tail hrightCons.tail
      exact ⟨{
        out := tailMatch.out
        matchRel := by
          simpa only [HELiveMatchMergeCoreCertified.cons,
            selected.right_eq] using
            (headLive.toHELiveMatchMergeCoreCertified.cons
              tailMatch.toHEMatchListAccCertified).matchRel
        traceSound := by
          simpa only [HELiveMatchMergeCoreCertified.cons,
            selected.right_eq] using
            (headLive.toHELiveMatchMergeCoreCertified.cons
              tailMatch.toHEMatchListAccCertified).traceSound
        equalitySound := by
          simpa only [HELiveMatchMergeCoreCertified.cons,
            selected.right_eq] using
            (headLive.toHELiveMatchMergeCoreCertified.cons
              tailMatch.toHEMatchListAccCertified).equalitySound
        assignmentsSound := tailMatch.assignmentsSound
        solutions := tailMatch.solutions
      }⟩

/-- The semantically minimal seven recursive callbacks at one projected
state.  Hidden class-value matchers expose no standalone ambient trace
certificate; the original nested-expression branch retains the full package
needed by `MatchTraceSound.expr`. -/
structure HEProjectedHiddenLiveConflictCallbacksAt
    (trace : List (String × Metta.Atom))
    (allowed : List (String × String))
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    (covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed) where
  assignmentConflict : ∀ {key : String} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state (.var key) leftRest)
    {value first : Atom} {rest : List Atom},
    p.nextRight = value →
    DeclMatchSpec.Atom.isVarB value = false →
    seed.classValues key = first :: rest →
    Bindings.valuesConsistent (first :: rest) = true →
    first ≠ value →
    Nonempty (HELiveHiddenMatchResidualCertified trace allowed
      first value seed p.nextSubst)
  assignmentReconcile : ∀ {key : String} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state (.var key) leftRest)
    {value first : Atom} {rest : List Atom},
    p.nextRight = value →
    DeclMatchSpec.Atom.isVarB value = false →
    seed.classValues key = first :: rest →
    Bindings.valuesConsistent (first :: rest) = false →
    Nonempty (HELiveHiddenListMatchResidualCertified trace allowed
      (List.replicate (rest.length + 1) first) (rest ++ [value])
      seed p.nextSubst)
  nonVarVarConflict : ∀ {value : Atom} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state value leftRest)
    {key : String} {first : Atom} {rest : List Atom},
    p.nextRight = .var key →
    DeclMatchSpec.Atom.isVarB value = false →
    seed.classValues key = first :: rest →
    Bindings.valuesConsistent (first :: rest) = true →
    first ≠ value →
    Nonempty (HELiveHiddenMatchResidualCertified trace allowed
      first value seed p.nextSubst)
  nonVarVarReconcile : ∀ {value : Atom} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state value leftRest)
    {key : String} {first : Atom} {rest : List Atom},
    p.nextRight = .var key →
    DeclMatchSpec.Atom.isVarB value = false →
    seed.classValues key = first :: rest →
    Bindings.valuesConsistent (first :: rest) = false →
    Nonempty (HELiveHiddenListMatchResidualCertified trace allowed
      (List.replicate (rest.length + 1) first) (rest ++ [value])
      seed p.nextSubst)
  equalityPair : ∀ {leftKey : String} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state (.var leftKey) leftRest)
    {rightKey : String} {first second : Atom},
    p.nextRight = .var rightKey →
    (EqualityClosure.edgeGraph allowed).Reachable leftKey rightKey →
    (seed.addEquality leftKey rightKey).classValues leftKey =
      [first, second] →
    Bindings.valuesConsistent [first, second] = false →
    Nonempty (HELiveHiddenMatchResidualCertified trace allowed
      first second (seed.addEquality leftKey rightKey) p.nextSubst)
  equalityClass : ∀ {leftKey : String} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state (.var leftKey) leftRest)
    {rightKey : String} {first second third : Atom} {rest : List Atom},
    p.nextRight = .var rightKey →
    (EqualityClosure.edgeGraph allowed).Reachable leftKey rightKey →
    (seed.addEquality leftKey rightKey).classValues leftKey =
      first :: second :: third :: rest →
    Bindings.valuesConsistent (first :: second :: third :: rest) = false →
    Nonempty (HELiveHiddenListMatchResidualCertified trace allowed
      (List.replicate (rest.length + 2) first)
      (second :: third :: rest) (seed.addEquality leftKey rightKey)
      p.nextSubst)
  expression : ∀ {leftAtoms : List Atom} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state (.expression leftAtoms) leftRest)
    {rightAtoms : List Atom},
    p.nextRight = .expression rightAtoms →
    Nonempty (HELiveMatchMergeCoreResidualCertified trace allowed
      (.expression leftAtoms) p.nextRight seed p.nextSubst)

/-- Exhaustive original-head dispatcher using only the minimal hidden
conflict callbacks. -/
theorem HEProjectedTailHeadResidualSolutionPackage.exists_coreResidualHead_of_hiddenCallbacks
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    (valuation : String → Metta.Atom)
    (htrace : MettaConstraintsSatisfied valuation trace)
    (haliases : HETraceAliasesAllowed trace allowed)
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    (covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed)
    (callbacks : HEProjectedHiddenLiveConflictCallbacksAt
      trace allowed covered)
    {nextLeft : Atom} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state nextLeft leftRest) :
    Nonempty (HELiveMatchMergeCoreResidualCertified trace allowed
      nextLeft p.nextRight seed p.nextSubst) := by
  have hequation := (p.headSatisfied_of_trace valuation htrace).2
  cases nextLeft with
  | symbol leftName =>
      cases hright : p.nextRight with
      | symbol rightName =>
          rw [hright] at hequation
          have hname : leftName = rightName := by
            simpa [MettaEquationSatisfied, toLeaTTaAtom,
              applyClassSolution] using hequation
          subst rightName
          simpa only [hright] using p.exists_coreResidualSymbol hright
      | var rightName =>
          simpa only [hright] using
            p.exists_coreResidualNonVarVar_of_hiddenLiveConflicts
              covered hright rfl
              (fun {first rest} hclass hconsistent hdifferent =>
                callbacks.nonVarVarConflict p hright rfl
                  hclass hconsistent hdifferent)
              (fun {first rest} hclass hinconsistent =>
                callbacks.nonVarVarReconcile p hright rfl
                  hclass hinconsistent)
      | grounded rightGround =>
          simp [MettaEquationSatisfied, toLeaTTaAtom,
            applyClassSolution, hright] at hequation
      | expression rightAtoms =>
          simp [MettaEquationSatisfied, toLeaTTaAtom,
            applyClassSolution, hright] at hequation
  | var leftName =>
      cases hright : p.nextRight with
      | symbol rightName =>
          simpa only [hright] using
            p.exists_coreResidualVarNonVar_of_hiddenLiveConflicts
              covered hright rfl
              (fun {first rest} hclass hconsistent hdifferent =>
                callbacks.assignmentConflict p hright rfl
                  hclass hconsistent hdifferent)
              (fun {first rest} hclass hinconsistent =>
                callbacks.assignmentReconcile p hright rfl
                  hclass hinconsistent)
      | var rightName =>
          have hallowed := p.varVarAllowed_of_originalCoverage
            covered.originalCoverage haliases hright
          simpa only [hright] using
            p.exists_coreResidualVarVar_of_hiddenLiveConflicts
              covered hright hallowed
              (fun {first second} hvalues hinconsistent =>
                callbacks.equalityPair p hright hallowed
                  hvalues hinconsistent)
              (fun {first second third rest} hvalues hinconsistent =>
                callbacks.equalityClass p hright hallowed
                  hvalues hinconsistent)
      | grounded rightGround =>
          simpa only [hright] using
            p.exists_coreResidualVarNonVar_of_hiddenLiveConflicts
              covered hright rfl
              (fun {first rest} hclass hconsistent hdifferent =>
                callbacks.assignmentConflict p hright rfl
                  hclass hconsistent hdifferent)
              (fun {first rest} hclass hinconsistent =>
                callbacks.assignmentReconcile p hright rfl
                  hclass hinconsistent)
      | expression rightAtoms =>
          simpa only [hright] using
            p.exists_coreResidualVarNonVar_of_hiddenLiveConflicts
              covered hright rfl
              (fun {first rest} hclass hconsistent hdifferent =>
                callbacks.assignmentConflict p hright rfl
                  hclass hconsistent hdifferent)
              (fun {first rest} hclass hinconsistent =>
                callbacks.assignmentReconcile p hright rfl
                  hclass hinconsistent)
  | grounded leftGround =>
      cases hright : p.nextRight with
      | symbol rightName =>
          simp [MettaEquationSatisfied, toLeaTTaAtom,
            applyClassSolution, hright] at hequation
      | var rightName =>
          simpa only [hright] using
            p.exists_coreResidualNonVarVar_of_hiddenLiveConflicts
              covered hright rfl
              (fun {first rest} hclass hconsistent hdifferent =>
                callbacks.nonVarVarConflict p hright rfl
                  hclass hconsistent hdifferent)
              (fun {first rest} hclass hinconsistent =>
                callbacks.nonVarVarReconcile p hright rfl
                  hclass hinconsistent)
      | grounded rightGround =>
          rw [hright] at hequation
          have hatom :
              toLeaTTaAtom (.grounded leftGround) =
                toLeaTTaAtom (.grounded rightGround) := by
            simpa [MettaEquationSatisfied, toLeaTTaAtom,
              applyClassSolution] using hequation
          have hground : leftGround = rightGround := by
            have heq := toLeaTTaAtom_injective hatom
            injection heq
          subst rightGround
          simpa only [hright] using p.exists_coreResidualGrounded hright
      | expression rightAtoms =>
          simp [MettaEquationSatisfied, toLeaTTaAtom,
            applyClassSolution, hright] at hequation
  | expression leftAtoms =>
      cases hright : p.nextRight with
      | symbol rightName =>
          simp [MettaEquationSatisfied, toLeaTTaAtom,
            applyClassSolution, hright] at hequation
      | var rightName =>
          simpa only [hright] using
            p.exists_coreResidualNonVarVar_of_hiddenLiveConflicts
              covered hright rfl
              (fun {first rest} hclass hconsistent hdifferent =>
                callbacks.nonVarVarConflict p hright rfl
                  hclass hconsistent hdifferent)
              (fun {first rest} hclass hinconsistent =>
                callbacks.nonVarVarReconcile p hright rfl
                  hclass hinconsistent)
      | grounded rightGround =>
          simp [MettaEquationSatisfied, toLeaTTaAtom,
            applyClassSolution, hright] at hequation
      | expression rightAtoms =>
          simpa only [hright] using callbacks.expression p hright

/-- The seven genuinely recursive callbacks at one exact projected state.
Factoring the state indices out of the fields lets the semantic kernel thread
one common-solution bound without restating the full Robinson state at every
branch. -/
structure HEProjectedLiveConflictCallbacksAt
    (trace : List (String × Metta.Atom))
    (allowed : List (String × String))
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    (covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed) where
  assignmentConflict : ∀ {key : String} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state (.var key) leftRest)
    {value first : Atom} {rest : List Atom},
    p.nextRight = value →
    DeclMatchSpec.Atom.isVarB value = false →
    seed.classValues key = first :: rest →
    Bindings.valuesConsistent (first :: rest) = true →
    first ≠ value →
    Nonempty (HELiveMatchMergeCoreResidualCertified trace allowed
      first value seed p.nextSubst)
  assignmentReconcile : ∀ {key : String} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state (.var key) leftRest)
    {value first : Atom} {rest : List Atom},
    p.nextRight = value →
    DeclMatchSpec.Atom.isVarB value = false →
    seed.classValues key = first :: rest →
    Bindings.valuesConsistent (first :: rest) = false →
    Nonempty (HELiveListMatchMergeCoreResidualCertified trace allowed
      (List.replicate (rest.length + 1) first) (rest ++ [value])
      seed p.nextSubst)
  nonVarVarConflict : ∀ {value : Atom} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state value leftRest)
    {key : String} {first : Atom} {rest : List Atom},
    p.nextRight = .var key →
    DeclMatchSpec.Atom.isVarB value = false →
    seed.classValues key = first :: rest →
    Bindings.valuesConsistent (first :: rest) = true →
    first ≠ value →
    Nonempty (HELiveMatchMergeCoreResidualCertified trace allowed
      first value seed p.nextSubst)
  nonVarVarReconcile : ∀ {value : Atom} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state value leftRest)
    {key : String} {first : Atom} {rest : List Atom},
    p.nextRight = .var key →
    DeclMatchSpec.Atom.isVarB value = false →
    seed.classValues key = first :: rest →
    Bindings.valuesConsistent (first :: rest) = false →
    Nonempty (HELiveListMatchMergeCoreResidualCertified trace allowed
      (List.replicate (rest.length + 1) first) (rest ++ [value])
      seed p.nextSubst)
  equalityPair : ∀ {leftKey : String} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state (.var leftKey) leftRest)
    {rightKey : String} {first second : Atom},
    p.nextRight = .var rightKey →
    (EqualityClosure.edgeGraph allowed).Reachable leftKey rightKey →
    (seed.addEquality leftKey rightKey).classValues leftKey =
      [first, second] →
    Bindings.valuesConsistent [first, second] = false →
    Nonempty (HELiveMatchMergeCoreResidualCertified trace allowed
      first second (seed.addEquality leftKey rightKey) p.nextSubst)
  equalityClass : ∀ {leftKey : String} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state (.var leftKey) leftRest)
    {rightKey : String} {first second third : Atom} {rest : List Atom},
    p.nextRight = .var rightKey →
    (EqualityClosure.edgeGraph allowed).Reachable leftKey rightKey →
    (seed.addEquality leftKey rightKey).classValues leftKey =
      first :: second :: third :: rest →
    Bindings.valuesConsistent (first :: second :: third :: rest) = false →
    Nonempty (HELiveListMatchMergeCoreResidualCertified trace allowed
      (List.replicate (rest.length + 2) first)
      (second :: third :: rest) (seed.addEquality leftKey rightKey)
      p.nextSubst)
  expression : ∀ {leftAtoms : List Atom} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state (.expression leftAtoms) leftRest)
    {rightAtoms : List Atom},
    p.nextRight = .expression rightAtoms →
    Nonempty (HELiveMatchMergeCoreResidualCertified trace allowed
      (.expression leftAtoms) p.nextRight seed p.nextSubst)

/-- Induction-facing version of the projected callback family.  Recursive
class-value calls return only a hidden matcher plus structural congruence of
its actual live post-state.  The enclosing head is reconstructed afterward;
the child matcher is never required to possess standalone ambient trace
provenance. -/
structure HEProjectedHiddenStructuralConflictCallbacksAt
    (trace : List (String × Metta.Atom))
    (allowed : List (String × String))
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    (covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed) where
  assignmentConflict : ∀ {key : String} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state (.var key) leftRest)
    {value first : Atom} {rest : List Atom},
    p.nextRight = value →
    DeclMatchSpec.Atom.isVarB value = false →
    seed.classValues key = first :: rest →
    Bindings.valuesConsistent (first :: rest) = true →
    first ≠ value →
    Nonempty (HELiveHiddenMatchStructuralCertified trace allowed
      first value seed p.nextSubst)
  assignmentReconcile : ∀ {key : String} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state (.var key) leftRest)
    {value first : Atom} {rest : List Atom},
    p.nextRight = value →
    DeclMatchSpec.Atom.isVarB value = false →
    seed.classValues key = first :: rest →
    Bindings.valuesConsistent (first :: rest) = false →
    Nonempty (HELiveHiddenListMatchStructuralCertified trace allowed
      (List.replicate (rest.length + 1) first) (rest ++ [value])
      seed p.nextSubst)
  nonVarVarConflict : ∀ {value : Atom} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state value leftRest)
    {key : String} {first : Atom} {rest : List Atom},
    p.nextRight = .var key →
    DeclMatchSpec.Atom.isVarB value = false →
    seed.classValues key = first :: rest →
    Bindings.valuesConsistent (first :: rest) = true →
    first ≠ value →
    Nonempty (HELiveHiddenMatchStructuralCertified trace allowed
      first value seed p.nextSubst)
  nonVarVarReconcile : ∀ {value : Atom} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state value leftRest)
    {key : String} {first : Atom} {rest : List Atom},
    p.nextRight = .var key →
    DeclMatchSpec.Atom.isVarB value = false →
    seed.classValues key = first :: rest →
    Bindings.valuesConsistent (first :: rest) = false →
    Nonempty (HELiveHiddenListMatchStructuralCertified trace allowed
      (List.replicate (rest.length + 1) first) (rest ++ [value])
      seed p.nextSubst)
  equalityPair : ∀ {leftKey : String} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state (.var leftKey) leftRest)
    {rightKey : String} {first second : Atom},
    p.nextRight = .var rightKey →
    (EqualityClosure.edgeGraph allowed).Reachable leftKey rightKey →
    (seed.addEquality leftKey rightKey).classValues leftKey =
      [first, second] →
    Bindings.valuesConsistent [first, second] = false →
    Nonempty (HELiveHiddenMatchStructuralCertified trace allowed
      first second (seed.addEquality leftKey rightKey) p.nextSubst)
  equalityClass : ∀ {leftKey : String} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state (.var leftKey) leftRest)
    {rightKey : String} {first second third : Atom} {rest : List Atom},
    p.nextRight = .var rightKey →
    (EqualityClosure.edgeGraph allowed).Reachable leftKey rightKey →
    (seed.addEquality leftKey rightKey).classValues leftKey =
      first :: second :: third :: rest →
    Bindings.valuesConsistent (first :: second :: third :: rest) = false →
    Nonempty (HELiveHiddenListMatchStructuralCertified trace allowed
      (List.replicate (rest.length + 2) first)
      (second :: third :: rest) (seed.addEquality leftKey rightKey)
      p.nextSubst)
  expression : ∀ {leftAtoms : List Atom} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state (.expression leftAtoms) leftRest)
    {rightAtoms : List Atom},
    p.nextRight = .expression rightAtoms →
    Nonempty (HELiveMatchMergeCoreCongruentCertified trace allowed
      (.expression leftAtoms) p.nextRight seed p.nextSubst)

/-- Forget only the post-state structural field.  This projection feeds the
existing hidden-inner head dispatcher; reconstruction of the original
projected head remains at that outer layer. -/
def HEProjectedHiddenStructuralConflictCallbacksAt.toHidden
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    {covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed}
    (callbacks : HEProjectedHiddenStructuralConflictCallbacksAt
      trace allowed covered) :
    HEProjectedHiddenLiveConflictCallbacksAt trace allowed covered where
  assignmentConflict := by
    intro key leftRest p value first rest hright hnonvar hclass hconsistent hne
    exact (callbacks.assignmentConflict p hright hnonvar
      hclass hconsistent hne).map
        HELiveHiddenMatchStructuralCertified.operational
  assignmentReconcile := by
    intro key leftRest p value first rest hright hnonvar hclass hinconsistent
    exact (callbacks.assignmentReconcile p hright hnonvar
      hclass hinconsistent).map
        HELiveHiddenListMatchStructuralCertified.operational
  nonVarVarConflict := by
    intro value leftRest p key first rest hright hnonvar hclass hconsistent hne
    exact (callbacks.nonVarVarConflict p hright hnonvar
      hclass hconsistent hne).map
        HELiveHiddenMatchStructuralCertified.operational
  nonVarVarReconcile := by
    intro value leftRest p key first rest hright hnonvar hclass hinconsistent
    exact (callbacks.nonVarVarReconcile p hright hnonvar
      hclass hinconsistent).map
        HELiveHiddenListMatchStructuralCertified.operational
  equalityPair := by
    intro leftKey leftRest p rightKey first second hright hallowed hvalues
      hinconsistent
    exact (callbacks.equalityPair p hright hallowed
      hvalues hinconsistent).map
        HELiveHiddenMatchStructuralCertified.operational
  equalityClass := by
    intro leftKey leftRest p rightKey first second third rest hright hallowed
      hvalues hinconsistent
    exact (callbacks.equalityClass p hright hallowed
      hvalues hinconsistent).map
        HELiveHiddenListMatchStructuralCertified.operational
  expression := by
    intro leftAtoms leftRest p rightAtoms hright
    exact (callbacks.expression p hright).map p.coreResidualOfCoreCongruent

/-- Semantic-size-indexed family at the minimal hidden callback boundary. -/
structure HESolutionSizeBoundedProjectedHiddenLiveConflictKernel
    (valuation : String → Metta.Atom)
    (trace : List (String × Metta.Atom))
    (allowed : List (String × String)) where
  callbacks : ∀
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    (covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed)
    {bound : Nat},
    HECoveredProjectedStateSolutionSizeBound valuation covered bound →
    HEProjectedHiddenLiveConflictCallbacksAt trace allowed covered

/-- Exact paired-recursion target: every covered state at one semantic
ceiling receives hidden conflict post-states with structural congruence.  The
semantic field of those post-states remains supplied independently by their
certified live merges. -/
structure HESolutionSizeBoundedProjectedHiddenStructuralConflictKernel
    (valuation : String → Metta.Atom)
    (trace : List (String × Metta.Atom))
    (allowed : List (String × String)) where
  callbacks : ∀
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    (covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed)
    {bound : Nat},
    HECoveredProjectedStateSolutionSizeBound valuation covered bound →
    HEProjectedHiddenStructuralConflictCallbacksAt trace allowed covered

/-- Forget structural post-state evidence only after the paired recursion has
constructed it.  All concrete matchers, merges, traces, and equality bounds
are preserved. -/
def HESolutionSizeBoundedProjectedHiddenStructuralConflictKernel.toHidden
    {valuation : String → Metta.Atom}
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    (kernel : HESolutionSizeBoundedProjectedHiddenStructuralConflictKernel
      valuation trace allowed) :
    HESolutionSizeBoundedProjectedHiddenLiveConflictKernel
      valuation trace allowed where
  callbacks covered _bound hbound :=
    (kernel.callbacks covered hbound).toHidden

/-- Every former full callback package projects to the minimal interface.
This is a one-way compatibility theorem: the new recursion may target the
weaker boundary without invalidating any already-certified full kernel. -/
def HEProjectedLiveConflictCallbacksAt.toHidden
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    {covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed}
    (callbacks : HEProjectedLiveConflictCallbacksAt trace allowed covered) :
    HEProjectedHiddenLiveConflictCallbacksAt trace allowed covered where
  assignmentConflict := by
    intro key leftRest p value first rest hright hnonvar hclass hconsistent hne
    exact (callbacks.assignmentConflict p hright hnonvar hclass hconsistent hne).map
      HELiveMatchMergeCoreResidualCertified.toHidden
  assignmentReconcile := by
    intro key leftRest p value first rest hright hnonvar hclass hinconsistent
    exact (callbacks.assignmentReconcile p hright hnonvar hclass hinconsistent).map
      HELiveListMatchMergeCoreResidualCertified.toHidden
  nonVarVarConflict := by
    intro value leftRest p key first rest hright hnonvar hclass hconsistent hne
    exact (callbacks.nonVarVarConflict p hright hnonvar hclass hconsistent hne).map
      HELiveMatchMergeCoreResidualCertified.toHidden
  nonVarVarReconcile := by
    intro value leftRest p key first rest hright hnonvar hclass hinconsistent
    exact (callbacks.nonVarVarReconcile p hright hnonvar hclass hinconsistent).map
      HELiveListMatchMergeCoreResidualCertified.toHidden
  equalityPair := by
    intro leftKey leftRest p rightKey first second hright hallowed hvalues hinconsistent
    exact (callbacks.equalityPair p hright hallowed hvalues hinconsistent).map
      HELiveMatchMergeCoreResidualCertified.toHidden
  equalityClass := by
    intro leftKey leftRest p rightKey first second third rest
      hright hallowed hvalues hinconsistent
    exact (callbacks.equalityClass p hright hallowed hvalues hinconsistent).map
      HELiveListMatchMergeCoreResidualCertified.toHidden
  expression := by
    intro leftAtoms leftRest p rightAtoms hright
    exact callbacks.expression p hright

/-- The minimal callback family closes the original semantic head kernel
directly; no upgrade to the over-strong hidden matcher trace interface is
required. -/
def HESolutionSizeBoundedProjectedHiddenLiveConflictKernel.toHeadKernel
    {valuation : String → Metta.Atom}
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    (kernel : HESolutionSizeBoundedProjectedHiddenLiveConflictKernel
      valuation trace allowed)
    (htrace : MettaConstraintsSatisfied valuation trace)
    (haliases : HETraceAliasesAllowed trace allowed)
    (bound : Nat) :
    HESolutionSizeBoundedProjectedHeadKernel
      valuation trace allowed bound where
  head covered _nextLeft _leftRest selected hbound :=
    selected.exists_coreResidualHead_of_hiddenCallbacks
      valuation htrace haliases covered (kernel.callbacks covered hbound)

/-- Direct sibling-fold consumer for the minimal callback family. -/
theorem HESolutionSizeBoundedProjectedHiddenLiveConflictKernel.matchListAcc
    {valuation : String → Metta.Atom}
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {bound : Nat}
    (kernel : HESolutionSizeBoundedProjectedHiddenLiveConflictKernel
      valuation trace allowed)
    (htrace : MettaConstraintsSatisfied valuation trace)
    (haliases : HETraceAliasesAllowed trace allowed) :
    ∀ {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
      {outerSubst : Metta.Subst}
      {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
      {subst result : Metta.Subst} {left right : List Atom}
      {seed : Bindings},
      (covered : HEOriginalConstraintCoveredProjectedListState trace allowed
        outerFuel front outerSubst fuel work subst result left right seed) →
      HESolutionAtomsSizeBound valuation left bound →
      HESolutionAtomsSizeBound valuation right bound →
      Nonempty (HEMatchListAccSolutionCertified trace allowed
        left right seed result) :=
  (kernel.toHeadKernel htrace haliases bound).matchListAcc

/-- A live-conflict kernel indexed by the common-solution size of the exact
projected state.  Its callbacks are constructed together at that state, so
the semantic bound cannot be detached from the Robinson residual that
justifies it. -/
structure HESolutionSizeBoundedProjectedLiveConflictKernel
    (valuation : String → Metta.Atom)
    (trace : List (String × Metta.Atom))
    (allowed : List (String × String)) where
  callbacks : ∀
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    (covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed)
    {bound : Nat},
    HECoveredProjectedStateSolutionSizeBound valuation covered bound →
    HEProjectedLiveConflictCallbacksAt trace allowed covered

/-- Family-level compatibility projection. -/
def HESolutionSizeBoundedProjectedLiveConflictKernel.toHidden
    {valuation : String → Metta.Atom}
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    (kernel : HESolutionSizeBoundedProjectedLiveConflictKernel
      valuation trace allowed) :
    HESolutionSizeBoundedProjectedHiddenLiveConflictKernel
      valuation trace allowed where
  callbacks covered _bound hbound :=
    (kernel.callbacks covered hbound).toHidden

/-- Erase the state-local semantic ceiling.  Each projected state obtains a
fresh finite bound for its literal lists; the callbacks remain tied to that
same state, so this choice introduces no global maximum and no constraint on
the live seed. -/
def HESolutionSizeBoundedProjectedLiveConflictKernel.toLiveConflictKernel
    {valuation : String → Metta.Atom}
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    (kernel : HESolutionSizeBoundedProjectedLiveConflictKernel
      valuation trace allowed) :
    HEProjectedLiveConflictKernel trace allowed where
  assignmentConflict covered _key _leftRest p _value _first _rest
      hright hnonvar hclass hconsistent hne := by
    obtain ⟨bound, hbound⟩ :=
      exists_HECoveredProjectedStateSolutionSizeBound valuation covered
    exact (kernel.callbacks covered hbound).assignmentConflict p
      hright hnonvar hclass hconsistent hne
  assignmentReconcile covered _key _leftRest p _value _first _rest
      hright hnonvar hclass hinconsistent := by
    obtain ⟨bound, hbound⟩ :=
      exists_HECoveredProjectedStateSolutionSizeBound valuation covered
    exact (kernel.callbacks covered hbound).assignmentReconcile p
      hright hnonvar hclass hinconsistent
  nonVarVarConflict covered _value _leftRest p _key _first _rest
      hright hnonvar hclass hconsistent hne := by
    obtain ⟨bound, hbound⟩ :=
      exists_HECoveredProjectedStateSolutionSizeBound valuation covered
    exact (kernel.callbacks covered hbound).nonVarVarConflict p
      hright hnonvar hclass hconsistent hne
  nonVarVarReconcile covered _value _leftRest p _key _first _rest
      hright hnonvar hclass hinconsistent := by
    obtain ⟨bound, hbound⟩ :=
      exists_HECoveredProjectedStateSolutionSizeBound valuation covered
    exact (kernel.callbacks covered hbound).nonVarVarReconcile p
      hright hnonvar hclass hinconsistent
  equalityPair covered _leftKey _leftRest p _rightKey _first _second
      hright hallowed hvalues hinconsistent := by
    obtain ⟨bound, hbound⟩ :=
      exists_HECoveredProjectedStateSolutionSizeBound valuation covered
    exact (kernel.callbacks covered hbound).equalityPair p
      hright hallowed hvalues hinconsistent
  equalityClass covered _leftKey _leftRest p _rightKey _first _second
      _third _rest hright hallowed hvalues hinconsistent := by
    obtain ⟨bound, hbound⟩ :=
      exists_HECoveredProjectedStateSolutionSizeBound valuation covered
    exact (kernel.callbacks covered hbound).equalityClass p
      hright hallowed hvalues hinconsistent
  expression covered _leftAtoms _leftRest p _rightAtoms hright := by
    obtain ⟨bound, hbound⟩ :=
      exists_HECoveredProjectedStateSolutionSizeBound valuation covered
    exact (kernel.callbacks covered hbound).expression p hright

/-- The bounded live-conflict family induces the exhaustive semantic head
kernel through the existing original-head dispatcher. -/
def HESolutionSizeBoundedProjectedLiveConflictKernel.toHeadKernel
    {valuation : String → Metta.Atom}
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    (kernel : HESolutionSizeBoundedProjectedLiveConflictKernel
      valuation trace allowed)
    (htrace : MettaConstraintsSatisfied valuation trace)
    (haliases : HETraceAliasesAllowed trace allowed)
    (bound : Nat) :
    HESolutionSizeBoundedProjectedHeadKernel
      valuation trace allowed bound where
  head covered _nextLeft _leftRest selected _hbound :=
    selected.exists_coreResidualHead_of_coveredLiveKernel
      valuation htrace haliases kernel.toLiveConflictKernel covered

/-- Size-indexed form of the exact projected live conflict kernel.  Each
callback may use one common finite bound for the current literal state and
live accumulator.  Quantifying over the bound exposes the induction index;
the operational conclusions are identical to the unbounded kernel. -/
structure HEProjectedLiveConflictKernelBounded
    (trace : List (String × Metta.Atom))
    (allowed : List (String × String)) where
  assignmentConflict : ∀
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    (covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed)
    {key : String} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state (.var key) leftRest)
    {bound : Nat},
    HECoveredProjectedStateSizeBound covered bound →
    ∀ {value first : Atom} {rest : List Atom},
    p.nextRight = value →
    DeclMatchSpec.Atom.isVarB value = false →
    seed.classValues key = first :: rest →
    Bindings.valuesConsistent (first :: rest) = true →
    first ≠ value →
    Nonempty (HELiveMatchMergeCoreResidualCertified trace allowed
      first value seed p.nextSubst)
  assignmentReconcile : ∀
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    (covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed)
    {key : String} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state (.var key) leftRest)
    {bound : Nat},
    HECoveredProjectedStateSizeBound covered bound →
    ∀ {value first : Atom} {rest : List Atom},
    p.nextRight = value →
    DeclMatchSpec.Atom.isVarB value = false →
    seed.classValues key = first :: rest →
    Bindings.valuesConsistent (first :: rest) = false →
    Nonempty (HELiveListMatchMergeCoreResidualCertified trace allowed
      (List.replicate (rest.length + 1) first) (rest ++ [value])
      seed p.nextSubst)
  nonVarVarConflict : ∀
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    (covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed)
    {value : Atom} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state value leftRest)
    {bound : Nat},
    HECoveredProjectedStateSizeBound covered bound →
    ∀ {key : String} {first : Atom} {rest : List Atom},
    p.nextRight = .var key →
    DeclMatchSpec.Atom.isVarB value = false →
    seed.classValues key = first :: rest →
    Bindings.valuesConsistent (first :: rest) = true →
    first ≠ value →
    Nonempty (HELiveMatchMergeCoreResidualCertified trace allowed
      first value seed p.nextSubst)
  nonVarVarReconcile : ∀
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    (covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed)
    {value : Atom} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state value leftRest)
    {bound : Nat},
    HECoveredProjectedStateSizeBound covered bound →
    ∀ {key : String} {first : Atom} {rest : List Atom},
    p.nextRight = .var key →
    DeclMatchSpec.Atom.isVarB value = false →
    seed.classValues key = first :: rest →
    Bindings.valuesConsistent (first :: rest) = false →
    Nonempty (HELiveListMatchMergeCoreResidualCertified trace allowed
      (List.replicate (rest.length + 1) first) (rest ++ [value])
      seed p.nextSubst)
  equalityPair : ∀
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    (covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed)
    {leftKey : String} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state (.var leftKey) leftRest)
    {bound : Nat},
    HECoveredProjectedStateSizeBound covered bound →
    ∀ {rightKey : String} {first second : Atom},
    p.nextRight = .var rightKey →
    (EqualityClosure.edgeGraph allowed).Reachable leftKey rightKey →
    (seed.addEquality leftKey rightKey).classValues leftKey =
      [first, second] →
    Bindings.valuesConsistent [first, second] = false →
    Nonempty (HELiveMatchMergeCoreResidualCertified trace allowed
      first second (seed.addEquality leftKey rightKey) p.nextSubst)
  equalityClass : ∀
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    (covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed)
    {leftKey : String} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state (.var leftKey) leftRest)
    {bound : Nat},
    HECoveredProjectedStateSizeBound covered bound →
    ∀ {rightKey : String} {first second third : Atom} {rest : List Atom},
    p.nextRight = .var rightKey →
    (EqualityClosure.edgeGraph allowed).Reachable leftKey rightKey →
    (seed.addEquality leftKey rightKey).classValues leftKey =
      first :: second :: third :: rest →
    Bindings.valuesConsistent
      (first :: second :: third :: rest) = false →
    Nonempty (HELiveListMatchMergeCoreResidualCertified trace allowed
      (List.replicate (rest.length + 2) first)
      (second :: third :: rest) (seed.addEquality leftKey rightKey)
      p.nextSubst)
  expression : ∀
    {outerFuel : Nat} {front : List (Metta.Atom × Metta.Atom)}
    {outerSubst : Metta.Subst}
    {fuel : Nat} {work : List (Metta.Atom × Metta.Atom)}
    {subst result : Metta.Subst} {left right : List Atom}
    {seed : Bindings}
    (covered : HEOriginalConstraintCoveredProjectedListState trace allowed
      outerFuel front outerSubst fuel work subst result left right seed)
    {leftAtoms : List Atom} {leftRest : List Atom}
    (p : HEProjectedTailHeadResidualSolutionPackage
      covered.state (.expression leftAtoms) leftRest)
    {bound : Nat},
    HECoveredProjectedStateSizeBound covered bound →
    ∀ {rightAtoms : List Atom},
    p.nextRight = .expression rightAtoms →
    Nonempty (HELiveMatchMergeCoreResidualCertified trace allowed
      (.expression leftAtoms) p.nextRight seed p.nextSubst)

/-- Forget the explicit finite ceiling.  Finiteness of the current literal
state supplies a bound independently at every callback, so this erasure does
not assume a global maximum and does not compare binding presentations. -/
def HEProjectedLiveConflictKernelBounded.toLiveConflictKernel
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)}
    (kernel : HEProjectedLiveConflictKernelBounded trace allowed) :
    HEProjectedLiveConflictKernel trace allowed where
  assignmentConflict covered key leftRest p value first rest hright hnonvar
      hclass hconsistent hne := by
    obtain ⟨bound, hbound⟩ := HECoveredProjectedStateSizeBound.exists covered
    exact kernel.assignmentConflict covered p hbound hright hnonvar
      hclass hconsistent hne
  assignmentReconcile covered key leftRest p value first rest hright hnonvar
      hclass hinconsistent := by
    obtain ⟨bound, hbound⟩ := HECoveredProjectedStateSizeBound.exists covered
    exact kernel.assignmentReconcile covered p hbound hright hnonvar
      hclass hinconsistent
  nonVarVarConflict covered value leftRest p key first rest hright hnonvar
      hclass hconsistent hne := by
    obtain ⟨bound, hbound⟩ := HECoveredProjectedStateSizeBound.exists covered
    exact kernel.nonVarVarConflict covered p hbound hright hnonvar
      hclass hconsistent hne
  nonVarVarReconcile covered value leftRest p key first rest hright hnonvar
      hclass hinconsistent := by
    obtain ⟨bound, hbound⟩ := HECoveredProjectedStateSizeBound.exists covered
    exact kernel.nonVarVarReconcile covered p hbound hright hnonvar
      hclass hinconsistent
  equalityPair covered leftKey leftRest p rightKey first second hright
      hallowed hvalues hinconsistent := by
    obtain ⟨bound, hbound⟩ := HECoveredProjectedStateSizeBound.exists covered
    exact kernel.equalityPair covered p hbound hright hallowed
      hvalues hinconsistent
  equalityClass covered leftKey leftRest p rightKey first second third rest
      hright hallowed hvalues hinconsistent := by
    obtain ⟨bound, hbound⟩ := HECoveredProjectedStateSizeBound.exists covered
    exact kernel.equalityClass covered p hbound hright hallowed
      hvalues hinconsistent
  expression covered leftAtoms leftRest p rightAtoms hright := by
    obtain ⟨bound, hbound⟩ := HECoveredProjectedStateSizeBound.exists covered
    exact kernel.expression covered p hbound hright

/-! ## Structural-measure regression oracle -/

/-! ### Solved explicit aliases are not raw-substitution congruences

An earlier candidate induction invariant required every intermediate HE
accumulator to be structurally congruent to the current Robinson
`ofSubst` presentation.  The following paired oracle records why that is
too strong.  Two variables may already normalize to the same value, so a
later explicit equality is Robinson-solved even though the raw substitution
does not connect their equality classes.  HE must still retain the explicit
edge, and repaired LeaTTa retains it in the reconciliation rebuild. -/

private def solvedAliasSeed : Bindings := {
  assignments := [("x", .symbol "a"), ("y", .symbol "a")]
  equalities := []
}

private def solvedAliasSubst : Metta.Subst :=
  [("x", .sym "a"), ("y", .sym "a")]

private def solvedAliasSource : Metta.Bindings :=
  [Metta.BindingRel.val "x" (.sym "a"),
   Metta.BindingRel.val "y" (.sym "a")]

private theorem solvedAliasSeed_congruence :
    LeaBindingCongruence solvedAliasSeed
      (Metta.Bindings.ofSubst solvedAliasSubst) := by
  apply LeaBindingCongruence.of_rel
  constructor
  · intro key value
    simp [solvedAliasSeed, solvedAliasSubst, Metta.Bindings.ofSubst]
    aesop
  · intro first second
    simp [solvedAliasSeed, solvedAliasSubst, Metta.Bindings.ofSubst]

/-- NEGATIVE: a solved variable equality may add a live class edge that is
absent from the raw Robinson substitution, despite exact congruence before
the equality is processed.  Intermediate raw-`ofSubst` congruence is
therefore not a valid invariant for the alias fold. -/
theorem solvedAlias_rawSubst_not_liveEqualityTarget :
    LeaBindingCongruence solvedAliasSeed
        (Metta.Bindings.ofSubst solvedAliasSubst) ∧
      Metta.Unify.decomposeAll
          [(Metta.Subst.apply solvedAliasSubst (.var "x"),
            Metta.Subst.apply solvedAliasSubst (.var "y"))] = some [] ∧
      ¬ LeaBindingStructuralCongruence
        (solvedAliasSeed.addEquality "x" "y")
        (Metta.Bindings.ofSubst solvedAliasSubst) := by
  refine ⟨solvedAliasSeed_congruence, ?_, ?_⟩
  · simp [solvedAliasSubst, Metta.Subst.apply, Metta.Subst.lookup,
      Metta.Unify.decomposeAll, Metta.Unify.decomposeEq]
  · intro h
    have hxy : "y" ∈
        (solvedAliasSeed.addEquality "x" "y").eqClass "x" := by
      decide
    have hraw := (h.classes "x" "y").mp hxy
    simp [solvedAliasSubst, Metta.Bindings.ofSubst,
      Metta.Bindings.eqClass, Metta.Bindings.eqClassAux,
      Metta.Bindings.eqStep] at hraw

/-- POSITIVE: the same solved equality preserves the exact class-indexed value
provenance needed by the recursive tail, and therefore preserves Robinson-trace
assignment soundness.  Only equality-closure agreement must be deferred to the
alias-aware repaired target. -/
theorem solvedAlias_liveEquality_preserves_valueProvenance :
    LeaClassValueRelEquiv (solvedAliasSeed.addEquality "x" "y")
        (Metta.Bindings.ofSubst solvedAliasSubst) ∧
      LeaEliminationTraceAssignmentsSound
        (solvedAliasSeed.addEquality "x" "y") solvedAliasSubst := by
  have hvalues : LeaClassValueRelEquiv
      (solvedAliasSeed.addEquality "x" "y")
      (Metta.Bindings.ofSubst solvedAliasSubst) :=
    solvedAliasSeed_congruence.classValues.addEquality_he "x" "y"
  exact ⟨hvalues,
    hvalues.assignmentsSound_of_ofSubst_subset (by
      intro entry hentry
      exact hentry)⟩

/-- POSITIVE: the repaired reconciliation target retains the explicit edge
that the normalized substitution alone omits.  This is the alias-aware
target consumed by the final congruence crown. -/
theorem solvedAlias_repairedRebuild_retains_explicitEquality :
    "y" ∈ Metta.Bindings.eqClass
      (Metta.Bindings.rebuildFromReconciliation
        (Metta.Bindings.addEqRaw solvedAliasSource "x" "y")
        solvedAliasSource [(.var "x", .var "y")] solvedAliasSubst) "x" := by
  apply rebuildFromReconciliation_preserves_class
  decide

private def sameSizeExternalConflictSeed : Bindings :=
  { assignments :=
      [("y", .expression [.symbol "g", .var "u"]),
       ("z", .expression [.symbol "g", .var "v"])]
    equalities := [] }

private def sameSizeExternalConflictValuation : String → Metta.Atom :=
  fun name =>
    if name = "u" then .sym "a"
    else if name = "v" then .sym "a"
    else if name = "y" then .expr [.sym "g", .sym "a"]
    else if name = "z" then .expr [.sym "g", .sym "a"]
    else .var name

/-- POSITIVE: the structural-tie oracle is not an unsatisfiable artifact;
the seed and the original `f(y) = f(z)` equation have a common valuation. -/
theorem externalLiveConflict_structuralTie_satisfiable :
    HEBindingSatisfied sameSizeExternalConflictValuation
        sameSizeExternalConflictSeed ∧
      MettaEquationSatisfied sameSizeExternalConflictValuation
        (toLeaTTaAtom (.expression [.symbol "f", .var "y"]),
         toLeaTTaAtom (.expression [.symbol "f", .var "z"])) := by
  constructor
  · constructor
    · intro key value hmem
      simp [sameSizeExternalConflictSeed] at hmem
      rcases hmem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        simp [sameSizeExternalConflictValuation, toLeaTTaAtom,
          toLeaTTaAtoms, applyClassSolution]
    · intro left right hmem
      simp [sameSizeExternalConflictSeed] at hmem
  · simp [sameSizeExternalConflictValuation, MettaEquationSatisfied,
      toLeaTTaAtom, toLeaTTaAtoms, applyClassSolution]

/-- POSITIVE: the common-solution size sees through the raw tie.  The live
class value `g(u)` denotes exactly `y`'s semantic term, which is a strict
child of the interpreted `f(y)` expression. -/
theorem externalLiveConflict_solutionSize_strictlyDescends :
    HESolutionAtomSize sameSizeExternalConflictValuation
        (.expression [.symbol "g", .var "u"]) <
      HESolutionAtomSize sameSizeExternalConflictValuation
        (.expression [.symbol "f", .var "y"]) := by
  have hvalue : (.expression [.symbol "g", .var "u"] : Atom) ∈
      sameSizeExternalConflictSeed.classValues "y" := by
    decide
  have hclassSize :=
    externalLiveConflict_structuralTie_satisfiable.1
      |>.solutionAtomSize_classValue hvalue
  calc
    HESolutionAtomSize sameSizeExternalConflictValuation
        (.expression [.symbol "g", .var "u"]) =
        (sameSizeExternalConflictValuation "y").size := hclassSize
    _ = HESolutionAtomSize sameSizeExternalConflictValuation
        (.var "y") := by
      simp [HESolutionAtomSize, sameSizeExternalConflictValuation,
        toLeaTTaAtom, applyClassSolution]
    _ < HESolutionAtomSize sameSizeExternalConflictValuation
        (.expression [.symbol "f", .var "y"]) :=
      heSolutionAtomSize_lt_expression_of_mem _ (by simp)

set_option maxRecDepth 10000 in
/-- NEGATIVE: structural size alone cannot justify recursion through an
external live merge.  Matching `f(y)` with `f(z)` emits the real alias
`y = z`; adding that alias to the live seed exposes `g(u)`/`g(v)`, whose
translated size ties the original pair.  The eventual proof must consume an
exact projected Robinson descent for this branch, not assert strict syntax
descent. -/
theorem externalLiveConflict_not_strictStructuralDescent :
    matchAtoms
        (.expression [.symbol "f", .var "y"])
        (.expression [.symbol "f", .var "z"]) 10 =
      [Bindings.empty.addEquality "y" "z"] ∧
    (sameSizeExternalConflictSeed.addEquality "y" "z").classValues "y" =
      [.expression [.symbol "g", .var "u"],
       .expression [.symbol "g", .var "v"]] ∧
    Bindings.valuesConsistent
        ((sameSizeExternalConflictSeed.addEquality "y" "z").classValues
          "y") = false ∧
    HEAtomSize (.expression [.symbol "f", .var "y"]) =
      HEAtomSize (.expression [.symbol "g", .var "u"]) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  simp [HEAtomSize, toLeaTTaAtom, toLeaTTaAtoms, Metta.Atom.size]

/-- Bounded companion of the certified pending-cardinality recursion.  The
finite deficit remains the sole recursion index at this layer; the atom-size
invariant is merely threaded through each actual progress step and made
available to the local conflict constructor.  This separation prevents the
Robinson deficit from being reused as a matcher structural measure. -/
theorem exists_completeSatisfiedCertifiedMatcherMergeChain_of_local_progress_bounded
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {start : Bindings}
    {valuation : String → Metta.Atom} {bound : Nat}
    (htraceSatisfied : MettaConstraintsSatisfied valuation trace)
    (hstartNonVariable : HEAssignmentsNonVariable start)
    (hstartSound : LeaEliminationTraceAssignmentsSound start trace)
    (hstartEqualityBound : HEEqualityClosureBound start allowed)
    (hstartSatisfied : HEBindingSatisfied valuation start)
    (hstartSizeBound : HEAssignmentsSizeBound start bound)
    (hprogress : ∀ before,
      HEAssignmentsNonVariable before →
      LeaEliminationTraceAssignmentsSound before trace →
      HEEqualityClosureBound before allowed →
      HEBindingSatisfied valuation before →
      HEAssignmentsSizeBound before bound →
      pendingEliminationTraceEntries before trace ≠ ∅ →
      ∃ after,
        Nonempty (HECertifiedEliminationTraceProgressStep
          trace allowed before after) ∧
        HEAssignmentsSizeBound after bound) :
    ∃ out,
      HECertifiedMatcherMergeChain trace allowed start out ∧
        HEAssignmentsNonVariable out ∧
          LeaEliminationTraceStructuralRel out trace ∧
            HEEqualityClosureBound out allowed ∧
              HEBindingSatisfied valuation out ∧
                HEAssignmentsSizeBound out bound := by
  classical
  have go : ∀ deficit before,
      (pendingEliminationTraceEntries before trace).card = deficit →
      HEAssignmentsNonVariable before →
      LeaEliminationTraceAssignmentsSound before trace →
      HEEqualityClosureBound before allowed →
      HEBindingSatisfied valuation before →
      HEAssignmentsSizeBound before bound →
      ∃ out,
        HECertifiedMatcherMergeChain trace allowed before out ∧
          HEAssignmentsNonVariable out ∧
            LeaEliminationTraceStructuralRel out trace ∧
              HEEqualityClosureBound out allowed ∧
                HEBindingSatisfied valuation out ∧
                  HEAssignmentsSizeBound out bound := by
    intro deficit
    induction deficit using Nat.strong_induction_on with
    | h deficit ih =>
        intro before hcard hnonvar hsound hequality hsatisfied hsize
        by_cases hempty : pendingEliminationTraceEntries before trace = ∅
        · exact ⟨before, .nil before, hnonvar,
            eliminationTraceStructuralRel_iff_sound_pending_empty.mpr
              ⟨hsound, hempty⟩,
            hequality, hsatisfied, hsize⟩
        · obtain ⟨after, ⟨hstep⟩, hafterSize⟩ :=
            hprogress before hnonvar hsound hequality hsatisfied hsize hempty
          have hlt :
              (pendingEliminationTraceEntries after trace).card < deficit := by
            rw [← hcard]
            exact hstep.progress.card_lt
          have hmatchedNonvar :
              HEAssignmentsNonVariable hstep.progress.matched :=
            heAssignmentsNonVariable_of_matchAtoms
              hstep.progress.match_mem
          have hafterNonvar : HEAssignmentsNonVariable after :=
            mergeBindings_assignmentsNonVariable
              hstep.progress.merge_mem hnonvar hmatchedNonvar
          have hafterEquality : HEEqualityClosureBound after allowed :=
            hstep.mergeEqualityClosureBoundSound.preserves hequality
          have hafterSatisfied : HEBindingSatisfied valuation after :=
            hstep.progress.afterSatisfied hsatisfied htraceSatisfied
          obtain ⟨out, hchain, houtNonvar, houtStructural,
              houtEquality, houtSatisfied, houtSize⟩ :=
            ih _ hlt after rfl hafterNonvar
              hstep.progress.assignmentsSound hafterEquality
              hafterSatisfied hafterSize
          exact ⟨out, .cons hstep hchain, houtNonvar, houtStructural,
            houtEquality, houtSatisfied, houtSize⟩
  exact go _ start rfl hstartNonVariable hstartSound hstartEqualityBound
    hstartSatisfied hstartSizeBound

/-- Semantic-size-bounded companion of the certified pending-cardinality
recursion.  Pending trace entries remain the well-founded index of the live
merge, while the common-solution size bound is preserved for recursive
matcher calls made by each local progress step. -/
theorem exists_completeSatisfiedCertifiedMatcherMergeChain_of_local_progress_solutionSizeBounded
    {trace : List (String × Metta.Atom)}
    {allowed : List (String × String)} {start : Bindings}
    {valuation : String → Metta.Atom} {bound : Nat}
    (htraceSatisfied : MettaConstraintsSatisfied valuation trace)
    (hstartNonVariable : HEAssignmentsNonVariable start)
    (hstartSound : LeaEliminationTraceAssignmentsSound start trace)
    (hstartEqualityBound : HEEqualityClosureBound start allowed)
    (hstartSatisfied : HEBindingSatisfied valuation start)
    (hstartSizeBound : HEBindingSolutionSizeBound valuation start bound)
    (hprogress : ∀ before,
      HEAssignmentsNonVariable before →
      LeaEliminationTraceAssignmentsSound before trace →
      HEEqualityClosureBound before allowed →
      HEBindingSatisfied valuation before →
      HEBindingSolutionSizeBound valuation before bound →
      pendingEliminationTraceEntries before trace ≠ ∅ →
      ∃ after,
        Nonempty (HECertifiedEliminationTraceProgressStep
          trace allowed before after) ∧
        HEBindingSolutionSizeBound valuation after bound) :
    ∃ out,
      HECertifiedMatcherMergeChain trace allowed start out ∧
        HEAssignmentsNonVariable out ∧
          LeaEliminationTraceStructuralRel out trace ∧
            HEEqualityClosureBound out allowed ∧
              HEBindingSatisfied valuation out ∧
                HEBindingSolutionSizeBound valuation out bound := by
  classical
  have go : ∀ deficit before,
      (pendingEliminationTraceEntries before trace).card = deficit →
      HEAssignmentsNonVariable before →
      LeaEliminationTraceAssignmentsSound before trace →
      HEEqualityClosureBound before allowed →
      HEBindingSatisfied valuation before →
      HEBindingSolutionSizeBound valuation before bound →
      ∃ out,
        HECertifiedMatcherMergeChain trace allowed before out ∧
          HEAssignmentsNonVariable out ∧
            LeaEliminationTraceStructuralRel out trace ∧
              HEEqualityClosureBound out allowed ∧
                HEBindingSatisfied valuation out ∧
                  HEBindingSolutionSizeBound valuation out bound := by
    intro deficit
    induction deficit using Nat.strong_induction_on with
    | h deficit ih =>
        intro before hcard hnonvar hsound hequality hsatisfied hsize
        by_cases hempty : pendingEliminationTraceEntries before trace = ∅
        · exact ⟨before, .nil before, hnonvar,
            eliminationTraceStructuralRel_iff_sound_pending_empty.mpr
              ⟨hsound, hempty⟩,
            hequality, hsatisfied, hsize⟩
        · obtain ⟨after, ⟨hstep⟩, hafterSize⟩ :=
            hprogress before hnonvar hsound hequality hsatisfied hsize hempty
          have hlt :
              (pendingEliminationTraceEntries after trace).card < deficit := by
            rw [← hcard]
            exact hstep.progress.card_lt
          have hmatchedNonvar :
              HEAssignmentsNonVariable hstep.progress.matched :=
            heAssignmentsNonVariable_of_matchAtoms
              hstep.progress.match_mem
          have hafterNonvar : HEAssignmentsNonVariable after :=
            mergeBindings_assignmentsNonVariable
              hstep.progress.merge_mem hnonvar hmatchedNonvar
          have hafterEquality : HEEqualityClosureBound after allowed :=
            hstep.mergeEqualityClosureBoundSound.preserves hequality
          have hafterSatisfied : HEBindingSatisfied valuation after :=
            hstep.progress.afterSatisfied hsatisfied htraceSatisfied
          obtain ⟨out, hchain, houtNonvar, houtStructural,
              houtEquality, houtSatisfied, houtSize⟩ :=
            ih _ hlt after rfl hafterNonvar
              hstep.progress.assignmentsSound hafterEquality
              hafterSatisfied hafterSize
          exact ⟨out, .cons hstep hchain, houtNonvar, houtStructural,
            houtEquality, houtSatisfied, houtSize⟩
  exact go _ start rfl hstartNonVariable hstartSound hstartEqualityBound
    hstartSatisfied hstartSizeBound

/-! ## Repaired-fork oracle: transient collision aliases

A live HE conflict merge recursively matches conflicting compound values and
therefore records their inner alias.  Repaired LeaTTa reconciliation retains
the same class connection even when seeded ground equations would normalize
the compound collision away in the primary Robinson trace. -/

private def transientAliasProbe : Metta.Bindings :=
  [Metta.BindingRel.val "x" (.expr [.sym "f", .var "u"]),
   Metta.BindingRel.val "u" (.sym "a"),
   Metta.BindingRel.val "y" (.expr [.sym "f", .var "v"]),
   Metta.BindingRel.val "v" (.sym "a")]

private def transientAliasProbeHE : Bindings :=
  { assignments :=
      [("x", .expression [.symbol "f", .var "u"]),
       ("u", .symbol "a"),
       ("y", .expression [.symbol "f", .var "v"]),
       ("v", .symbol "a")]
    equalities := [] }

private def transientAliasRightHE : Bindings :=
  Bindings.empty.addEquality "x" "y"

private def transientAliasRightLea : Metta.Bindings :=
  [Metta.BindingRel.eq "y" "x"]

private def transientAliasProbeLeaOut : Metta.Bindings :=
  [Metta.BindingRel.eq "u" "v",
   Metta.BindingRel.eq "y" "x",
   Metta.BindingRel.val "v" (.sym "a"),
   Metta.BindingRel.val "y" (.expr [.sym "f", .var "v"]),
   Metta.BindingRel.val "u" (.sym "a"),
   Metta.BindingRel.val "x" (.expr [.sym "f", .var "u"])]

private theorem transient_inner_match_connects
    {out : Bindings}
    (hmatch : DeclMatchSpec.MatchRel
      (.expression [.symbol "f", .var "u"])
      (.expression [.symbol "f", .var "v"]) out) :
    "v" ∈ out.eqClass "u" := by
  cases hmatch with
  | expr hlist =>
      cases hlist with
      | cons hsymbol hmergeSymbol htail =>
          cases htail with
          | cons hvariables hmergeVariables hnil =>
              cases hnil
              have hright : "v" ∈
                  (Bindings.empty.addEquality "u" "v").eqClass "u" := by
                rw [EqualityClosure.mem_eqClass_iff_reachable]
                exact (show
                    (EqualityClosure.edgeGraph
                      (Bindings.empty.addEquality "u" "v").equalities).Adj
                        "u" "v" by
                  rw [EqualityClosure.edgeGraph_adj_iff]
                  simp [Bindings.empty, Bindings.addEquality]).reachable
              have hvariablesOut : _ =
                  (Bindings.empty.addEquality "u" "v") :=
                DeclMatchSpec.matchRel_varVar_inv hvariables
              rw [hvariablesOut] at hmergeVariables
              exact mergeBindings_right_eqClass_mono
                hmergeVariables hright

private theorem transient_addEquality_connects
    {out : Bindings}
    (hadd : DeclMergeSpec.AddVarEqualityRel
      transientAliasProbeHE "x" "y" out) :
    "v" ∈ out.eqClass "u" := by
  have hclassValues :
      (transientAliasProbeHE.addEquality "x" "y").classValues "x" =
        [.expression [.symbol "f", .var "u"],
         .expression [.symbol "f", .var "v"]] := by
    decide
  cases hadd with
  | consistent hconsistent =>
      rw [hclassValues] at hconsistent
      simp [Bindings.valuesConsistent] at hconsistent
  | pairConflict hvalues hinconsistent hmatch hmerge =>
      rw [hclassValues] at hvalues
      rcases hvalues with ⟨rfl, rfl⟩
      have hmatchedClass := transient_inner_match_connects hmatch
      exact mergeRel_right_eqClass_mono hmerge hmatchedClass
  | classConflict hvalues hinconsistent hmatch hmerge =>
      rw [hclassValues] at hvalues
      simp at hvalues

private theorem transient_merge_connects
    {out : Bindings} {fuel : Nat}
    (hmerge : out ∈ mergeBindings
      transientAliasProbeHE transientAliasRightHE fuel) :
    "v" ∈ out.eqClass "u" := by
  have hrel : DeclMergeSpec.MergeRel transientAliasProbeHE
      ({ assignments := [], equalities := [("x", "y")] } : Bindings) out := by
    simpa [transientAliasRightHE, Bindings.empty,
      Bindings.addEquality] using
        DeclMergeSpec.mergeBindings_sound hmerge
  cases hrel with
  | mk hassignments hequalities =>
      cases hassignments
      cases hequalities with
      | cons hadd htail =>
          cases htail
          exact transient_addEquality_connects hadd

private theorem transient_left_congruence :
    LeaBindingCongruence transientAliasProbeHE transientAliasProbe := by
  apply LeaBindingCongruence.of_rel
  constructor
  · intro key value
    simp [transientAliasProbeHE, transientAliasProbe]
    aesop
  · intro first second
    simp [transientAliasProbeHE, transientAliasProbe]

private theorem transient_right_congruence :
    LeaBindingCongruence transientAliasRightHE transientAliasRightLea := by
  apply LeaBindingCongruence.of_rel
  constructor
  · intro key value
    simp [transientAliasRightHE, transientAliasRightLea,
      Bindings.empty, Bindings.addEquality]
  · intro first second
    simp [transientAliasRightHE,
      transientAliasRightLea, Bindings.empty, Bindings.addEquality]
    aesop

private theorem transient_lea_merge_eq :
    Metta.Bindings.merge transientAliasProbe transientAliasRightLea =
      [transientAliasProbeLeaOut] := by
  have hunify : Metta.Bindings.unifyValues
      (Metta.Bindings.classValues
        (Metta.Bindings.addEqRaw transientAliasProbe "y" "x") "y") =
      some [("u", .var "v")] := by
    simp [transientAliasProbe, Metta.Bindings.addEqRaw,
      Metta.Bindings.classValues, Metta.Bindings.eqClassOrdered,
      Metta.Bindings.eqVarsInOrder, Metta.Bindings.eqClass,
      Metta.Bindings.eqClassAux, Metta.Bindings.eqStep,
      Metta.Bindings.lookupVal, Metta.Bindings.unifyValues,
      Metta.Unify.unifyRounds, Metta.Unify.decomposeAll,
      Metta.Unify.decomposeEq, Metta.Unify.decomposeList,
      Metta.Subst.occurs, Metta.Subst.apply, Metta.Subst.lookup,
      Metta.Subst.extend, Metta.Subst.erase, Metta.Atom.size]
  have hreconcile : Metta.Bindings.reconcileAll transientAliasProbe
      [(.var "y", .var "x")] =
      some [("v", .sym "a"),
        ("y", .expr [.sym "f", .var "v"]),
        ("u", .sym "a"),
        ("x", .expr [.sym "f", .var "u"])] := by
    simp [transientAliasProbe, Metta.Bindings.reconcileAll,
      Metta.Bindings.equations, Metta.Bindings.relationEquation,
      Metta.Bindings.equationFuel, Metta.Unify.unifyRounds,
      Metta.Unify.decomposeAll, Metta.Unify.decomposeEq,
      Metta.Unify.decomposeList, Metta.Subst.occurs,
      Metta.Subst.apply, Metta.Subst.lookup, Metta.Subst.extend,
      Metta.Subst.erase, Metta.Atom.size]
  simp [transientAliasRightLea, Metta.Bindings.merge,
    Metta.Bindings.mergeOne, Metta.Bindings.addVarEquality]
  rw [hunify, hreconcile]
  simp [transientAliasProbe, transientAliasProbeLeaOut,
    Metta.Bindings.rebuildFromReconciliation,
    Metta.Bindings.rebuildFromSubst, Metta.Bindings.reconciliationAliases,
    Metta.Bindings.restoreAlias, Metta.Bindings.equations,
    Metta.Bindings.relationEquation, Metta.Bindings.equationFuel,
    Metta.Unify.aliasTrace, Metta.Unify.decomposeAll,
    Metta.Unify.decomposeEq, Metta.Unify.decomposeList,
    Metta.Unify.aliasConstraints, Metta.Subst.occurs,
    Metta.Subst.apply, Metta.Subst.lookup, Metta.Atom.size,
    Metta.Bindings.equalitySkeleton, Metta.Bindings.ofSubst,
    Metta.Bindings.addEqRaw, Metta.Bindings.eqClass,
    Metta.Bindings.eqClassAux, Metta.Bindings.eqStep]

/-- POSITIVE: every HE result for the transient collision and LeaTTa's repaired
result both retain the inner `u = v` class connection.  This is the observable
whose absence previously refuted the class-extensional merge obligation. -/
theorem transientAlias_repaired_innerAlias_agrees
    {heOut : Bindings} {fuel : Nat}
    (hmerge : heOut ∈ mergeBindings
      transientAliasProbeHE transientAliasRightHE fuel) :
    Metta.Bindings.merge transientAliasProbe transientAliasRightLea =
        [transientAliasProbeLeaOut] ∧
      "v" ∈ heOut.eqClass "u" ∧
        "v" ∈ Metta.Bindings.eqClass transientAliasProbeLeaOut "u" := by
  refine ⟨transient_lea_merge_eq, transient_merge_connects hmerge, ?_⟩
  set_option maxRecDepth 100000 in
    decide

end Mettapedia.Languages.MeTTa.HE.LeaTTaBridge
