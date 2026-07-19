import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Bridge
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Path

/-!
# Executable path refinement to declarative funded steps

The occurrence-bearing runtime path chooses concrete source and purse
occurrences.  This module transports every chosen runtime candidate to its
declarative `CostStep` witness and records the structural seam between the
normalized executable successor and that declarative target.  Keeping the
seam explicit is essential: static rho normalization is not definitional
equality of cost syntax.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedPresentationSyntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefGSLT
open Mettapedia.GSLT
open Mettapedia.GSLT.Meredith.RhoExample

/-- A traced runtime configuration is a sorted list of normalized top-level
components. -/
structure TraceComponentsCanonical (state : List RawTraceComponent) : Prop where
  terms : (state.map RawTraceComponent.term).Forall
    RawCostTerm.IsComponent
  normalized : (state.map RawTraceComponent.term).Forall
    RawCostTerm.Normalized
  ordered : KeySorted RawCostTerm.key
    (state.map RawTraceComponent.term)

namespace TraceComponentsCanonical

/-- Forgetting provenance from a canonical traced state gives the canonical
raw-configuration invariant used by the executable/declarative bridge. -/
theorem rawConfig {components : List RawTraceComponent}
    (canonical : TraceComponentsCanonical components) :
    RawCostConfig.Canonical (components.map RawTraceComponent.term) :=
  ⟨canonical.normalized, canonical.ordered⟩

end TraceComponentsCanonical

private theorem retainedTrace_terms
    (components : List RawTraceComponent) (indices : List Nat) :
    (((components.zipIdx.filter fun entry => decide (entry.2 ∉ indices)).map
      Prod.fst).map RawTraceComponent.term) =
      eraseIndices (components.map RawTraceComponent.term) indices := by
  unfold eraseIndices
  rw [List.zipIdx_map]
  have mapFilter : ∀ entries : List (RawTraceComponent × Nat),
      ((entries.filter fun entry => decide (entry.2 ∉ indices)).map
          Prod.fst).map RawTraceComponent.term =
        ((entries.map (Prod.map RawTraceComponent.term id)).filter fun entry =>
          decide (entry.2 ∉ indices)).map Prod.fst := by
    intro entries
    induction entries with
    | nil => rfl
    | cons head tail induction =>
        simp only [List.filter_cons, List.map_cons]
        split <;> simp_all [Function.comp_def]
  exact mapFilter components.zipIdx

private theorem map_stableInsertBy {Alpha Beta : Type}
    (f : Alpha → Beta) (key : Beta → String) (item : Alpha) :
    ∀ items : List Alpha,
      (stableInsertBy
        (fun left right => decide (key (f left) < key (f right))) item items).map f =
      stableInsertBy (fun left right => decide (key left < key right))
        (f item) (items.map f) := by
  intro items
  induction items with
  | nil => rfl
  | cons head tail induction =>
      simp only [stableInsertBy, List.map_cons]
      split <;> simp_all

private theorem map_foldl_stableInsertBy {Alpha Beta : Type}
    (f : Alpha → Beta) (key : Beta → String) :
    ∀ (source accumulator : List Alpha),
      (source.foldl (fun sorted item => stableInsertBy
        (fun left right => decide (key (f left) < key (f right))) item sorted)
        accumulator).map f =
      (source.map f).foldl (fun sorted item => stableInsertBy
        (fun left right => decide (key left < key right)) item sorted)
        (accumulator.map f) := by
  intro source
  induction source with
  | nil => intro accumulator; rfl
  | cons head tail induction =>
      intro accumulator
      simp only [List.foldl_cons, List.map_cons]
      rw [induction, map_stableInsertBy]

private theorem map_stableKeySort {Alpha Beta : Type}
    (f : Alpha → Beta) (key : Beta → String) (items : List Alpha) :
    (stableKeySort (fun item => key (f item)) items).map f =
      stableKeySort key (items.map f) := by
  unfold stableKeySort stableSortBy
  simpa using map_foldl_stableInsertBy f key items []

/-- Removing provenance after a traced firing yields the same canonical raw
component list as sorting the occurrence-preserving residual ingredients. -/
theorem applyTracedStep_terms (components : List RawTraceComponent)
    (step : RawRuntimeStep) (eventId : Nat) :
    (applyTracedStep components step eventId).map RawTraceComponent.term =
      stableKeySort RawCostTerm.key
        (eraseIndices (components.map RawTraceComponent.term)
            (step.participantIndices ++
              step.selectedPurses.map RawIndexedPurse.index) ++
          step.contractum.normalize.components ++
          step.selectedPurses.map fun purse =>
            RawCostTerm.purse purse.surface purse.tail) := by
  unfold applyTracedStep sortTraceComponents
  rw [map_stableKeySort]
  simp only [List.map_append]
  rw [retainedTrace_terms]
  simp [List.map_map, Function.comp_def]

/-- The initial traced presentation is canonical by construction. -/
theorem initialTraceComponents_canonical (term : RawCostTerm) :
    TraceComponentsCanonical (initialTraceComponents term) := by
  have terms :
      (initialTraceComponents term).map RawTraceComponent.term =
        term.normalizeConfig := by
    simp [initialTraceComponents, Function.comp_def]
  constructor
  · rw [terms]
    apply stableKeySort_forall
    exact RawCostTerm.components_forall_isComponent term.normalize
  · rw [terms]
    exact RawCostTerm.normalizeConfig_forall_Normalized term
  · rw [terms]
    exact RawCostTerm.normalizeConfig_keySorted term

/-- Canonical traced states remain canonical after an enabled occurrence-level
runtime firing. -/
theorem applyTracedStep_canonical
    {components : List RawTraceComponent} {step : RawRuntimeStep}
    (canonical : TraceComponentsCanonical components)
    (enabled : step ∈ runtimeCostCandidatesFromConfig
      (components.map RawTraceComponent.term)) (eventId : Nat) :
    TraceComponentsCanonical (applyTracedStep components step eventId) := by
  let source := components.map RawTraceComponent.term
  let consumed := step.participantIndices ++
    step.selectedPurses.map RawIndexedPurse.index
  let retained := eraseIndices source consumed
  let contractum := step.contractum.normalize.components
  let tails := step.selectedPurses.map fun purse =>
    RawCostTerm.purse purse.surface purse.tail
  let items := retained ++ contractum ++ tails
  have retainedComponents : retained.Forall RawCostTerm.IsComponent :=
    eraseIndices_forall canonical.terms consumed
  have retainedNormalized : retained.Forall RawCostTerm.Normalized :=
    eraseIndices_forall canonical.normalized consumed
  have contractumComponents : contractum.Forall RawCostTerm.IsComponent :=
    RawCostTerm.components_forall_isComponent _
  have contractumNormalized : contractum.Forall RawCostTerm.Normalized :=
    (RawCostTerm.normalizationResult step.contractum).components_fixed
  have funding := runtimeCostCandidatesFromConfig_funding_valid enabled
  have selectedNormalized := selectedPurses_forall_normalized
    canonical.rawConfig funding.selected_from_config
  have tailsComponents : tails.Forall RawCostTerm.IsComponent := by
    rw [List.forall_iff_forall_mem]
    intro term member
    obtain ⟨purse, _purseMember, rfl⟩ := List.mem_map.mp member
    simp [RawCostTerm.IsComponent]
  have tailsNormalized : tails.Forall RawCostTerm.Normalized := by
    rw [List.forall_iff_forall_mem]
    intro term member
    obtain ⟨purse, purseMember, rfl⟩ := List.mem_map.mp member
    have purseNormalized := List.forall_iff_forall_mem.mp selectedNormalized
      purse purseMember
    simp [RawCostTerm.Normalized, RawCostTerm.normalize,
      purseNormalized.surface, purseNormalized.tail]
  have itemsComponents : items.Forall RawCostTerm.IsComponent := by
    simp only [items, List.forall_append]
    exact ⟨⟨retainedComponents, contractumComponents⟩, tailsComponents⟩
  have itemsNormalized : items.Forall RawCostTerm.Normalized := by
    simp only [items, List.forall_append]
    exact ⟨⟨retainedNormalized, contractumNormalized⟩, tailsNormalized⟩
  constructor
  · rw [applyTracedStep_terms]
    exact stableKeySort_forall _ itemsComponents
  · rw [applyTracedStep_terms]
    exact stableKeySort_forall _ itemsNormalized
  · rw [applyTracedStep_terms]
    exact stableKeySort_keySorted RawCostTerm.key items

/-- The provenance-preserving successor and the runtime step's public
normalized residual contain exactly the same raw component multiset. -/
theorem applyTracedStep_toMultiset
    {components : List RawTraceComponent} {step : RawRuntimeStep}
    (canonical : TraceComponentsCanonical components)
    (enabled : step ∈ runtimeCostCandidatesFromConfig
      (components.map RawTraceComponent.term)) (eventId : Nat) :
    (((applyTracedStep components step eventId).map RawTraceComponent.term :
        List RawCostTerm) : Multiset RawCostTerm) =
      (step.residual.normalizeConfig : Multiset RawCostTerm) := by
  let source := components.map RawTraceComponent.term
  let consumed := step.participantIndices ++
    step.selectedPurses.map RawIndexedPurse.index
  let retained := eraseIndices source consumed
  let contractum := step.contractum.normalize.components
  let tails := step.selectedPurses.map fun purse =>
    RawCostTerm.purse purse.surface purse.tail
  let items := retained ++ contractum ++ tails
  have itemsComponents : items.Forall RawCostTerm.IsComponent := by
    have funding := runtimeCostCandidatesFromConfig_funding_valid enabled
    have selectedNormalized := selectedPurses_forall_normalized
      canonical.rawConfig funding.selected_from_config
    simp only [items, List.forall_append]
    refine ⟨⟨eraseIndices_forall canonical.terms consumed,
      RawCostTerm.components_forall_isComponent _⟩, ?_⟩
    rw [List.forall_iff_forall_mem]
    intro term member
    obtain ⟨purse, _purseMember, rfl⟩ := List.mem_map.mp member
    simp [RawCostTerm.IsComponent]
  have itemsNormalized : items.Forall RawCostTerm.Normalized := by
    have funding := runtimeCostCandidatesFromConfig_funding_valid enabled
    have selectedNormalized := selectedPurses_forall_normalized
      canonical.rawConfig funding.selected_from_config
    simp only [items, List.forall_append]
    refine ⟨⟨eraseIndices_forall canonical.normalized consumed,
      (RawCostTerm.normalizationResult step.contractum).components_fixed⟩, ?_⟩
    rw [List.forall_iff_forall_mem]
    intro term member
    obtain ⟨purse, purseMember, rfl⟩ := List.mem_map.mp member
    have purseNormalized := List.forall_iff_forall_mem.mp selectedNormalized
      purse purseMember
    simp [RawCostTerm.Normalized, RawCostTerm.normalize,
      purseNormalized.surface, purseNormalized.tail]
  rw [applyTracedStep_terms]
  rw [stableKeySort_toMultiset]
  have frame := runtimeCostCandidatesFromConfig_frameExact enabled
  unfold RawRuntimeStep.FrameExactFor at frame
  rw [frame]
  unfold residualFor RawCostTerm.normalizeConfig
  rw [stableKeySort_toMultiset]
  simp only [RawCostTerm.normalize_idempotent]
  exact (RawCostTerm.normalize_fromComponents_toMultiset
    items itemsComponents itemsNormalized).symm

/-- A compositional declarative reading of an occurrence-bearing runtime
path.  Adjacent declarative steps are connected by explicit structural
representation witnesses rather than by an unsound syntactic equality. -/
inductive DeclarativeCostTrace :
    List RawTraceComponent → List RawTraceComponent → Nat → Prop where
  | done (components : List RawTraceComponent) :
      DeclarativeCostTrace components components 0
  | fire {source next final : List RawTraceComponent}
      {length : Nat}
      {channel : CostName String} {demand : CostSig String}
      {target : CostConfig String}
      (step : CostStep
        (decodeRawConfig (source.map RawTraceComponent.term))
        channel demand target)
      (successor :
        RawCostConfig.StructurallyRepresents
          (next.map RawTraceComponent.term) target)
      (successorErasure :
        ∀ (signatureName : SignatureNameEncoding String)
            (signaturePure : ∀ signature,
              Canonical.HashSetFree (signatureName signature)),
          StructuralCongruence
            (CostConfig.eraseCanonical signatureName signaturePure
              (decodeRawConfig (next.map RawTraceComponent.term)))
            (CostConfig.eraseCanonical signatureName signaturePure target))
      (successorSafe :
        (decodeRawConfig (next.map RawTraceComponent.term)).BinderSafe)
      (rest : DeclarativeCostTrace next final length) :
      DeclarativeCostTrace source final (length + 1)

namespace CostPath

/-- Every occurrence-bearing executable path has a compositional sequence of
declarative `CostStep` witnesses, with every normalization seam exposed and
with exactly one declarative witness per runtime firing. -/
theorem refinesDeclarativeTrace :
    ∀ {nextId components finalId finalComponents}
      (path : CostPath nextId components finalId finalComponents),
      TraceComponentsCanonical components →
      (decodeRawConfig (components.map RawTraceComponent.term)).BinderSafe →
      DeclarativeCostTrace components finalComponents path.depth := by
  intro nextId components finalId finalComponents path
  induction path with
  | done supported bounded =>
      intro _canonical _sourceSafe
      exact .done _
  | @fire nextId components finalId finalComponents supported bounded step enabled rest induction =>
      intro canonical sourceSafe
      obtain ⟨target, declarative, represented, erasure, scopePreservation⟩ :=
        costStep_sound_runtime canonical.rawConfig supported.toConfig enabled
      have successorMultiset := applyTracedStep_toMultiset canonical enabled nextId
      have successorRepresents :
        RawCostConfig.StructurallyRepresents
            ((applyTracedStep components step nextId).map
              RawTraceComponent.term) target := by
        unfold RawCostConfig.StructurallyRepresents at represented ⊢
        rw [successorMultiset]
        exact represented
      have successorDecoded :
          decodeRawConfig
              ((applyTracedStep components step nextId).map
                RawTraceComponent.term) =
            decodeRawConfig step.residual.normalizeConfig := by
        unfold decodeRawConfig
        exact congrArg (Multiset.map decodeCostTerm) successorMultiset
      have successorErasure :
          ∀ (signatureName : SignatureNameEncoding String)
              (signaturePure : ∀ signature,
                Canonical.HashSetFree (signatureName signature)),
            StructuralCongruence
              (CostConfig.eraseCanonical signatureName signaturePure
                (decodeRawConfig
                  ((applyTracedStep components step nextId).map
                    RawTraceComponent.term)))
              (CostConfig.eraseCanonical signatureName signaturePure target) := by
        intro signatureName signaturePure
        rw [successorDecoded]
        exact erasure signatureName signaturePure
      have successorSafe :
          (decodeRawConfig
            ((applyTracedStep components step nextId).map
              RawTraceComponent.term)).BinderSafe := by
        rw [successorDecoded]
        exact scopePreservation sourceSafe
      exact .fire declarative successorRepresents successorErasure successorSafe
        (induction (applyTracedStep_canonical canonical enabled nextId)
          successorSafe)

end CostPath

namespace DeclarativeCostTrace

/-- The explicit successor-scope witnesses in a declarative runtime trace
cover its final normalized state. -/
theorem preserves_binderSafe
    {source final length}
    (trace : DeclarativeCostTrace source final length)
    (sourceSafe :
      (decodeRawConfig (source.map RawTraceComponent.term)).BinderSafe) :
    (decodeRawConfig (final.map RawTraceComponent.term)).BinderSafe := by
  induction trace with
  | done => exact sourceSafe
  | fire _step _successor _successorErasure successorSafe _rest induction =>
      exact induction successorSafe

/-- A scope-safe declarative reading of a runtime trace yields a same-length
path in the committed pure-rho GSLT.  Each executable firing contributes
exactly one COMM step; structural normalization is transported only on the
target. -/
theorem exists_eraseCanonical_rhoRewritePath
    {signatureName : SignatureNameEncoding String}
    {free : FreeSortContext} (signatureTyped : signatureName.WellSorted free)
    {source final length}
    (trace : DeclarativeCostTrace source final length)
    (sourceSafe :
      (decodeRawConfig (source.map RawTraceComponent.term)).BinderSafe) :
    ∃ path : rhoGSLT.RewritePath
        (CostConfig.eraseCanonical signatureName signatureTyped.hashSetFree
          (decodeRawConfig (source.map RawTraceComponent.term)))
        (CostConfig.eraseCanonical signatureName signatureTyped.hashSetFree
          (decodeRawConfig (final.map RawTraceComponent.term))),
      path.length = length := by
  induction trace with
  | done =>
      exact ⟨.nil _, rfl⟩
  | fire step _successor successorErasure successorSafe rest induction =>
      obtain ⟨tail, tailLength⟩ := induction successorSafe
      refine ⟨.cons
        (rhoRewrites_resp_right
          (step.eraseCanonical_rhoGSLTStep signatureTyped sourceSafe)
          (StructuralCongruence.symm _ _
            (successorErasure signatureName signatureTyped.hashSetFree)))
        tail, ?_⟩
      simp [GSLT.RewritePath.length, tailLength, Nat.add_comm]

/-- A scope-safe declarative runtime trace has an erasure to the one-root GSLT
derived from `rhoCalc`.  Structural normalization between executable firings
is transported through the derived process equations, and the path length is
the runtime firing count. -/
theorem exists_eraseCanonical_rhoLanguageDefRewritePath
    {signatureName : SignatureNameEncoding String}
    (signatureClosed : signatureName.MapsToClosedRhoNames)
    {source final length}
    (trace : DeclarativeCostTrace source final length)
    (sourceSafe :
      (decodeRawConfig (source.map RawTraceComponent.term)).BinderSafe) :
    ∃ finalSafe :
        (decodeRawConfig (final.map RawTraceComponent.term)).BinderSafe,
      ∃ purePath : rhoLanguageDefGSLT.RewritePath
        ((decodeRawConfig (source.map RawTraceComponent.term))
          |>.eraseCanonicalProcess signatureClosed sourceSafe)
        ((decodeRawConfig (final.map RawTraceComponent.term))
          |>.eraseCanonicalProcess signatureClosed finalSafe),
        purePath.length = length := by
  induction trace with
  | done =>
      exact ⟨sourceSafe, .nil _, rfl⟩
  | @fire source next final length channel demand target step successor
      successorErasure successorSafe rest induction =>
      obtain ⟨finalSafe, tail, tailLength⟩ := induction successorSafe
      have targetToSuccessor : rhoProcessEquations.r
          (target.eraseCanonicalProcess signatureClosed
            (step.preserves_binderSafe sourceSafe))
          ((decodeRawConfig (next.map RawTraceComponent.term))
            |>.eraseCanonicalProcess signatureClosed successorSafe) :=
        (rhoProcessEquations_iff_structuralCongruence _ _).mpr
          (StructuralCongruence.symm _ _
            (successorErasure signatureName
              signatureClosed.wellSorted.hashSetFree))
      refine ⟨finalSafe,
        .cons
          (rhoProcessRewrites_resp_right
            (step.eraseCanonical_rhoLanguageDefGSLTStep
              signatureClosed sourceSafe)
            targetToSuccessor)
          tail, ?_⟩
      simp [GSLT.RewritePath.length, tailLength, Nat.add_comm]

end DeclarativeCostTrace

namespace CostPath

/-- Every scope-safe occurrence-bearing runtime path erases compositionally to
the pure rho GSLT, with exactly one pure COMM step per executable firing.

The intermediate declarative targets need only agree with the next normalized
runtime state through the proved structural seam; `DeclarativeCostTrace`
performs that transport before this theorem hides the intermediate witnesses.
-/
theorem exists_eraseCanonical_rhoRewritePath
    {signatureName : SignatureNameEncoding String}
    {free : FreeSortContext} (signatureTyped : signatureName.WellSorted free)
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents)
    (canonical : TraceComponentsCanonical components)
    (sourceSafe :
      (decodeRawConfig (components.map RawTraceComponent.term)).BinderSafe) :
    ∃ purePath : rhoGSLT.RewritePath
        (CostConfig.eraseCanonical signatureName signatureTyped.hashSetFree
          (decodeRawConfig (components.map RawTraceComponent.term)))
        (CostConfig.eraseCanonical signatureName signatureTyped.hashSetFree
          (decodeRawConfig (finalComponents.map RawTraceComponent.term))),
      purePath.length = path.depth := by
  exact (path.refinesDeclarativeTrace canonical sourceSafe)
    |>.exists_eraseCanonical_rhoRewritePath signatureTyped sourceSafe

/-- Every scope-safe occurrence-bearing runtime path erases compositionally
to the pure rho GSLT derived from `rhoCalc`, with exactly one derived COMM
step per executable firing. -/
theorem exists_eraseCanonical_rhoLanguageDefRewritePath
    {signatureName : SignatureNameEncoding String}
    (signatureClosed : signatureName.MapsToClosedRhoNames)
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents)
    (canonical : TraceComponentsCanonical components)
    (sourceSafe :
      (decodeRawConfig (components.map RawTraceComponent.term)).BinderSafe) :
    ∃ finalSafe :
        (decodeRawConfig
          (finalComponents.map RawTraceComponent.term)).BinderSafe,
      ∃ purePath : rhoLanguageDefGSLT.RewritePath
          ((decodeRawConfig (components.map RawTraceComponent.term))
            |>.eraseCanonicalProcess signatureClosed sourceSafe)
          ((decodeRawConfig (finalComponents.map RawTraceComponent.term))
            |>.eraseCanonicalProcess signatureClosed finalSafe),
        purePath.length = path.depth := by
  exact (path.refinesDeclarativeTrace canonical sourceSafe)
    |>.exists_eraseCanonical_rhoLanguageDefRewritePath
      signatureClosed sourceSafe

end CostPath

/-- The canonical initial traced presentation decodes to a binder-safe cost
configuration whenever the admitted source passes the executable scope
check. -/
theorem initialTraceComponents_binderSafe {term : RawCostTerm}
    (safe : term.binderSafe = true) :
    (decodeRawConfig
      ((initialTraceComponents term).map RawTraceComponent.term)).BinderSafe := by
  apply (RawCostConfig.binderSafe_iff_decode _).mp
  simpa [initialTraceComponents, Function.comp_def] using
    RawCostTerm.normalizeConfig_forall_binderSafe safe

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
