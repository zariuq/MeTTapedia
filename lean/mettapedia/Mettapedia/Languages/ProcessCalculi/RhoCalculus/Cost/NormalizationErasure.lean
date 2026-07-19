import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RawConfig
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Normalization
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ScopedRefinement

/-!
# Pure erasure is invariant under raw cost normalization

The executable normalizer flattens and orders parallel components and applies
the static quote/drop name equation.  These presentation changes preserve the
pure rho process up to the established structural congruence.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PureBoundary

universe u

private theorem structuralApplyOne {function : String} {left right : Pattern}
    (component : StructuralCongruence left right) :
    StructuralCongruence (.apply function [left]) (.apply function [right]) := by
  refine StructuralCongruence.apply_cong function [left] [right] rfl ?_
  intro index leftBound rightBound
  have bound : index < 1 := by simpa using leftBound
  have indexZero : index = 0 := by omega
  subst indexZero
  simpa using component

private theorem structuralApplyTwo {function : String}
    {left₁ left₂ right₁ right₂ : Pattern}
    (first : StructuralCongruence left₁ right₁)
    (second : StructuralCongruence left₂ right₂) :
    StructuralCongruence
      (.apply function [left₁, left₂])
      (.apply function [right₁, right₂]) := by
  refine StructuralCongruence.apply_cong function
    [left₁, left₂] [right₁, right₂] rfl ?_
  intro index leftBound rightBound
  have bound : index < 2 := by simpa using leftBound
  have cases : index = 0 ∨ index = 1 := by omega
  rcases cases with rfl | rfl
  · simpa using first
  · simpa using second

private theorem structuralParallelTwo
    {left₁ left₂ right₁ right₂ : Pattern}
    (first : StructuralCongruence left₁ right₁)
    (second : StructuralCongruence left₂ right₂) :
    StructuralCongruence
      (.collection .hashBag [left₁, left₂] none)
      (.collection .hashBag [right₁, right₂] none) := by
  refine StructuralCongruence.par_cong
    [left₁, left₂] [right₁, right₂] rfl ?_
  intro index leftBound rightBound
  have bound : index < 2 := by simpa using leftBound
  have cases : index = 0 ∨ index = 1 := by omega
  rcases cases with rfl | rfl
  · simpa using first
  · simpa using second

/-- Structural congruence of both summands lifts through canonical
configuration erasure. -/
theorem CostConfig.eraseCanonical_add_congr_structural
    {Ground : Type u} (signatureName : SignatureNameEncoding Ground)
    (signaturePure : ∀ signature, HashSetFree (signatureName signature))
    {left₁ left₂ right₁ right₂ : CostConfig Ground}
    (left : StructuralCongruence
      (CostConfig.eraseCanonical signatureName signaturePure left₁)
      (CostConfig.eraseCanonical signatureName signaturePure left₂))
    (right : StructuralCongruence
      (CostConfig.eraseCanonical signatureName signaturePure right₁)
      (CostConfig.eraseCanonical signatureName signaturePure right₂)) :
    StructuralCongruence
      (CostConfig.eraseCanonical signatureName signaturePure (left₁ + right₁))
      (CostConfig.eraseCanonical signatureName signaturePure (left₂ + right₂)) := by
  exact StructuralCongruence.trans _ _ _
    (CostConfig.eraseCanonical_add_structural signatureName signaturePure
      left₁ right₁)
    (StructuralCongruence.trans _ _ _
      (structuralParallelTwo left right)
      (StructuralCongruence.symm _ _
        (CostConfig.eraseCanonical_add_structural signatureName signaturePure
          left₂ right₂)))

private theorem parallelPair_structural_append (left right : List Pattern) :
    StructuralCongruence
      (.collection .hashBag
        [.collection .hashBag left none,
         .collection .hashBag right none] none)
      (.collection .hashBag (left ++ right) none) := by
  let leftBag : Pattern := .collection .hashBag left none
  let rightBag : Pattern := .collection .hashBag right none
  have swap : StructuralCongruence
      (.collection .hashBag [leftBag, rightBag] none)
      (.collection .hashBag [rightBag, leftBag] none) :=
    StructuralCongruence.par_perm _ _ (by simp [List.Perm.swap])
  have flattenLeft : StructuralCongruence
      (.collection .hashBag [rightBag, leftBag] none)
      (.collection .hashBag (rightBag :: left) none) := by
    simpa [leftBag] using StructuralCongruence.par_flatten [rightBag] left
  have moveRight : StructuralCongruence
      (.collection .hashBag (rightBag :: left) none)
      (.collection .hashBag (left ++ [rightBag]) none) :=
    StructuralCongruence.par_perm _ _ (by
      simpa using (List.perm_append_comm (l₁ := [rightBag]) (l₂ := left)))
  have flattenRight : StructuralCongruence
      (.collection .hashBag (left ++ [rightBag]) none)
      (.collection .hashBag (left ++ right) none) := by
    simpa [rightBag] using StructuralCongruence.par_flatten left right
  exact StructuralCongruence.trans _ _ _ swap
    (StructuralCongruence.trans _ _ _ flattenLeft
      (StructuralCongruence.trans _ _ _ moveRight flattenRight))

private theorem stableKeySort_erase_perm {Alpha : Type}
    (key : Alpha → String) (erase : Alpha → Pattern) (items : List Alpha) :
    (stableKeySort key items).map erase |>.Perm (items.map erase) := by
  apply List.Perm.map erase
  exact Multiset.coe_eq_coe.mp (stableKeySort_toMultiset key items)

private theorem RawCostProc.erase_decode_components_structural
    (signatureName : SignatureNameEncoding String) :
    ∀ process : RawCostProc,
      StructuralCongruence
        ((decodeCostProc process).erase signatureName)
        (.collection .hashBag
          (process.components.map fun component =>
            (decodeCostProc component).erase signatureName) none)
  | .nil => StructuralCongruence.refl _
  | .par left right => by
      have components := structuralParallelTwo
        (RawCostProc.erase_decode_components_structural signatureName left)
        (RawCostProc.erase_decode_components_structural signatureName right)
      exact StructuralCongruence.trans _ _ _ components (by
        simpa [RawCostProc.components, List.map_append] using
          parallelPair_structural_append
          (left.components.map fun component =>
            (decodeCostProc component).erase signatureName)
          (right.components.map fun component =>
            (decodeCostProc component).erase signatureName))
  | .send channel payload =>
      StructuralCongruence.symm _ _ (StructuralCongruence.par_singleton _)
  | .recv channel body =>
      StructuralCongruence.symm _ _ (StructuralCongruence.par_singleton _)

private theorem RawCostTerm.erase_decode_components_structural
    (signatureName : SignatureNameEncoding String) :
    ∀ term : RawCostTerm,
      StructuralCongruence
        ((decodeCostTerm term).erase signatureName)
        (.collection .hashBag
          (term.components.map fun component =>
            (decodeCostTerm component).erase signatureName) none)
  | .nil => StructuralCongruence.refl _
  | .par left right => by
      have components := structuralParallelTwo
        (RawCostTerm.erase_decode_components_structural signatureName left)
        (RawCostTerm.erase_decode_components_structural signatureName right)
      exact StructuralCongruence.trans _ _ _ components (by
        simpa [RawCostTerm.components, List.map_append] using
          parallelPair_structural_append
          (left.components.map fun component =>
            (decodeCostTerm component).erase signatureName)
          (right.components.map fun component =>
            (decodeCostTerm component).erase signatureName))
  | .signed process signature =>
      StructuralCongruence.symm _ _ (StructuralCongruence.par_singleton _)
  | .drop name =>
      StructuralCongruence.symm _ _ (StructuralCongruence.par_singleton _)
  | .purse surface stack =>
      StructuralCongruence.symm _ _ (StructuralCongruence.par_singleton _)

mutual
  /-- Normalizing a raw name preserves its decoded pure-rho meaning. -/
  theorem RawCostName.erase_decode_normalize_structural
      (signatureName : SignatureNameEncoding String) :
      ∀ name : RawCostName,
        StructuralCongruence
          ((decodeCostName name.normalize).erase signatureName)
          ((decodeCostName name).erase signatureName)
    | .bvar index => StructuralCongruence.refl _
    | .signature signature => by
        apply StructuralCongruence.alpha
        exact congrArg signatureName
          (RawCostSig.normalize_toMultiset signature)
    | .quote term => by
        have termCongruence :=
          RawCostTerm.erase_decode_normalize_structural signatureName term
        generalize normalizedEq : term.normalize = normalized at termCongruence ⊢
        cases normalized with
        | nil =>
            simpa [RawCostName.normalize, normalizedEq, decodeCostName,
              CostName.erase] using
              structuralApplyOne (function := "NQuote") termCongruence
        | signed process signature =>
            simpa [RawCostName.normalize, normalizedEq, decodeCostName,
              CostName.erase] using
              structuralApplyOne (function := "NQuote") termCongruence
        | par left right =>
            simpa [RawCostName.normalize, normalizedEq, decodeCostName,
              CostName.erase] using
              structuralApplyOne (function := "NQuote") termCongruence
        | drop name =>
            have expose : StructuralCongruence
                ((decodeCostName name).erase signatureName)
                (.apply "NQuote"
                  [.apply "PDrop"
                    [(decodeCostName name).erase signatureName]]) :=
              StructuralCongruence.symm _ _
                (StructuralCongruence.quote_drop _)
            have underQuote := structuralApplyOne
              (function := "NQuote") termCongruence
            simpa [RawCostName.normalize, normalizedEq, decodeCostName,
              CostName.erase, CostTerm.erase] using
              StructuralCongruence.trans _ _ _ expose underQuote
        | purse surface stack =>
            simpa [RawCostName.normalize, normalizedEq, decodeCostName,
              CostName.erase] using
              structuralApplyOne (function := "NQuote") termCongruence

  /-- Normalizing a raw process preserves its decoded pure-rho meaning. -/
  theorem RawCostProc.erase_decode_normalize_structural
      (signatureName : SignatureNameEncoding String) :
      ∀ process : RawCostProc,
        StructuralCongruence
          ((decodeCostProc process.normalize).erase signatureName)
          ((decodeCostProc process).erase signatureName)
    | .nil => StructuralCongruence.refl _
    | .send channel payload => by
        simpa [RawCostProc.normalize, decodeCostProc, CostProc.erase] using
          structuralApplyTwo (function := "POutput")
            (RawCostName.erase_decode_normalize_structural signatureName channel)
            (RawCostTerm.erase_decode_normalize_structural signatureName payload)
    | .recv channel body => by
        have bodyCongruence :=
          RawCostTerm.erase_decode_normalize_structural signatureName body
        have bodyLambda := StructuralCongruence.lambda_cong none _ _
          bodyCongruence
        simpa [RawCostProc.normalize, decodeCostProc, CostProc.erase] using
          structuralApplyTwo (function := "PInput")
            (RawCostName.erase_decode_normalize_structural signatureName channel)
            bodyLambda
    | .par left right => by
        let items := left.normalize.components ++ right.normalize.components
        let sorted := stableKeySort RawCostProc.key items
        have itemComponents : items.Forall RawCostProc.IsComponent := by
          simp only [items, List.forall_append]
          exact ⟨RawCostProc.components_forall_isComponent _,
            RawCostProc.components_forall_isComponent _⟩
        have sortedComponents : sorted.Forall RawCostProc.IsComponent :=
          stableKeySort_forall RawCostProc.key itemComponents
        have normalizedComponents :
            (RawCostProc.fromComponents sorted).components = sorted :=
          RawCostProc.components_fromComponents sorted sortedComponents
        have exposeNormalized :=
          RawCostProc.erase_decode_components_structural signatureName
            (RawCostProc.fromComponents sorted)
        rw [normalizedComponents] at exposeNormalized
        have reorder : StructuralCongruence
            (.collection .hashBag
              (sorted.map fun component =>
                (decodeCostProc component).erase signatureName) none)
            (.collection .hashBag
              (items.map fun component =>
                (decodeCostProc component).erase signatureName) none) :=
          StructuralCongruence.par_perm _ _
            (stableKeySort_erase_perm RawCostProc.key
              (fun component =>
                (decodeCostProc component).erase signatureName) items)
        have regroup : StructuralCongruence
            (.collection .hashBag
              (items.map fun component =>
                (decodeCostProc component).erase signatureName) none)
            (.collection .hashBag
              [((decodeCostProc left.normalize).erase signatureName),
               ((decodeCostProc right.normalize).erase signatureName)] none) := by
          have pair := StructuralCongruence.symm _ _
            (parallelPair_structural_append
              (left.normalize.components.map fun component =>
                (decodeCostProc component).erase signatureName)
              (right.normalize.components.map fun component =>
                (decodeCostProc component).erase signatureName))
          have collapse := structuralParallelTwo
            (StructuralCongruence.symm _ _
              (RawCostProc.erase_decode_components_structural signatureName
                left.normalize))
            (StructuralCongruence.symm _ _
              (RawCostProc.erase_decode_components_structural signatureName
                right.normalize))
          simpa [items, List.map_append] using
            StructuralCongruence.trans _ _ _ pair collapse
        have children := structuralParallelTwo
          (RawCostProc.erase_decode_normalize_structural signatureName left)
          (RawCostProc.erase_decode_normalize_structural signatureName right)
        simpa [RawCostProc.normalize, items, sorted, decodeCostProc,
          CostProc.erase] using
          StructuralCongruence.trans _ _ _ exposeNormalized
            (StructuralCongruence.trans _ _ _ reorder
              (StructuralCongruence.trans _ _ _ regroup children))

  /-- Normalizing a raw term preserves its decoded pure-rho meaning. -/
  theorem RawCostTerm.erase_decode_normalize_structural
      (signatureName : SignatureNameEncoding String) :
      ∀ term : RawCostTerm,
        StructuralCongruence
          ((decodeCostTerm term.normalize).erase signatureName)
          ((decodeCostTerm term).erase signatureName)
    | .nil => StructuralCongruence.refl _
    | .signed process signature => by
        simpa [RawCostTerm.normalize, decodeCostTerm, CostTerm.erase] using
          RawCostProc.erase_decode_normalize_structural signatureName process
    | .drop name => by
        simpa [RawCostTerm.normalize, decodeCostTerm, CostTerm.erase] using
          structuralApplyOne (function := "PDrop")
            (RawCostName.erase_decode_normalize_structural signatureName name)
    | .purse surface stack => StructuralCongruence.refl _
    | .par left right => by
        let items := left.normalize.components ++ right.normalize.components
        let sorted := stableKeySort RawCostTerm.key items
        have itemComponents : items.Forall RawCostTerm.IsComponent := by
          simp only [items, List.forall_append]
          exact ⟨RawCostTerm.components_forall_isComponent _,
            RawCostTerm.components_forall_isComponent _⟩
        have sortedComponents : sorted.Forall RawCostTerm.IsComponent :=
          stableKeySort_forall RawCostTerm.key itemComponents
        have normalizedComponents :
            (RawCostTerm.fromComponents sorted).components = sorted :=
          RawCostTerm.components_fromComponents sorted sortedComponents
        have exposeNormalized :=
          RawCostTerm.erase_decode_components_structural signatureName
            (RawCostTerm.fromComponents sorted)
        rw [normalizedComponents] at exposeNormalized
        have reorder : StructuralCongruence
            (.collection .hashBag
              (sorted.map fun component =>
                (decodeCostTerm component).erase signatureName) none)
            (.collection .hashBag
              (items.map fun component =>
                (decodeCostTerm component).erase signatureName) none) :=
          StructuralCongruence.par_perm _ _
            (stableKeySort_erase_perm RawCostTerm.key
              (fun component =>
                (decodeCostTerm component).erase signatureName) items)
        have regroup : StructuralCongruence
            (.collection .hashBag
              (items.map fun component =>
                (decodeCostTerm component).erase signatureName) none)
            (.collection .hashBag
              [((decodeCostTerm left.normalize).erase signatureName),
               ((decodeCostTerm right.normalize).erase signatureName)] none) := by
          have pair := StructuralCongruence.symm _ _
            (parallelPair_structural_append
              (left.normalize.components.map fun component =>
                (decodeCostTerm component).erase signatureName)
              (right.normalize.components.map fun component =>
                (decodeCostTerm component).erase signatureName))
          have collapse := structuralParallelTwo
            (StructuralCongruence.symm _ _
              (RawCostTerm.erase_decode_components_structural signatureName
                left.normalize))
            (StructuralCongruence.symm _ _
              (RawCostTerm.erase_decode_components_structural signatureName
                right.normalize))
          simpa [items, List.map_append] using
            StructuralCongruence.trans _ _ _ pair collapse
        have children := structuralParallelTwo
          (RawCostTerm.erase_decode_normalize_structural signatureName left)
          (RawCostTerm.erase_decode_normalize_structural signatureName right)
        simpa [RawCostTerm.normalize, items, sorted, decodeCostTerm,
          CostTerm.erase] using
          StructuralCongruence.trans _ _ _ exposeNormalized
            (StructuralCongruence.trans _ _ _ reorder
              (StructuralCongruence.trans _ _ _ regroup children))
end

/-- Replacing one raw term's component presentation by the components of its
normal form preserves canonical pure-rho erasure. -/
theorem RawCostTerm.eraseCanonical_decode_normalizedComponents_structural
    (signatureName : SignatureNameEncoding String)
    (signaturePure : ∀ signature, HashSetFree (signatureName signature))
    (term : RawCostTerm) :
    StructuralCongruence
      (CostConfig.eraseCanonical signatureName signaturePure
        (decodeRawConfig term.normalize.components))
      (CostConfig.eraseCanonical signatureName signaturePure
        (decodeRawConfig term.components)) := by
  rw [decodeRawConfig_components, decodeRawConfig_components]
  exact StructuralCongruence.trans _ _ _
    (CostTerm.eraseCanonical_components_structural signatureName signaturePure
      (decodeCostTerm term.normalize))
    (StructuralCongruence.trans _ _ _
      (RawCostTerm.erase_decode_normalize_structural signatureName term)
      (StructuralCongruence.symm _ _
        (CostTerm.eraseCanonical_components_structural signatureName
          signaturePure (decodeCostTerm term))))

/-- Reassociating an arbitrary raw component list with `fromComponents`, then
flattening it again, preserves canonical pure-rho erasure.  The list need not
already satisfy the executable component invariant. -/
theorem RawCostTerm.eraseCanonical_decode_fromComponents_structural
    (signatureName : SignatureNameEncoding String)
    (signaturePure : ∀ signature, HashSetFree (signatureName signature)) :
    ∀ items : List RawCostTerm,
      StructuralCongruence
        (CostConfig.eraseCanonical signatureName signaturePure
          (decodeRawConfig (RawCostTerm.fromComponents items).components))
        (CostConfig.eraseCanonical signatureName signaturePure
          (decodeRawConfig items))
  | [] => StructuralCongruence.refl _
  | [term] => by
      change StructuralCongruence
        (CostConfig.eraseCanonical signatureName signaturePure
          (decodeRawConfig term.components))
        (CostConfig.eraseCanonical signatureName signaturePure
          (decodeRawConfig [term]))
      rw [decodeRawConfig_components]
      simpa [decodeRawConfig] using
        StructuralCongruence.trans _ _ _
          (CostTerm.eraseCanonical_components_structural signatureName
            signaturePure (decodeCostTerm term))
          (StructuralCongruence.symm _ _
            (CostConfig.eraseCanonical_singleton_structural signatureName
              signaturePure (decodeCostTerm term)))
  | term :: next :: rest => by
      have head : StructuralCongruence
          (CostConfig.eraseCanonical signatureName signaturePure
            (decodeCostTerm term).components)
          (CostConfig.eraseCanonical signatureName signaturePure
            ({decodeCostTerm term} : CostConfig String)) :=
        StructuralCongruence.trans _ _ _
          (CostTerm.eraseCanonical_components_structural signatureName
            signaturePure (decodeCostTerm term))
          (StructuralCongruence.symm _ _
            (CostConfig.eraseCanonical_singleton_structural signatureName
              signaturePure (decodeCostTerm term)))
      have tail :=
        RawCostTerm.eraseCanonical_decode_fromComponents_structural
          signatureName signaturePure (next :: rest)
      rw [decodeRawConfig_components] at tail
      have combined := CostConfig.eraseCanonical_add_congr_structural
        signatureName signaturePure head tail
      change StructuralCongruence
        (CostConfig.eraseCanonical signatureName signaturePure
          (decodeRawConfig
            (term.components ++
              (RawCostTerm.fromComponents (next :: rest)).components)))
        (CostConfig.eraseCanonical signatureName signaturePure
          (decodeRawConfig (term :: next :: rest)))
      rw [decodeRawConfig_append, decodeRawConfig_components,
        decodeRawConfig_components]
      simpa [decodeRawConfig] using combined

/-- A normalized executable presentation and its source have the same
canonical pure-rho erasure. -/
theorem RawCostTerm.eraseCanonical_decode_normalizeConfig_structural
    (signatureName : SignatureNameEncoding String)
    (signaturePure : ∀ signature, HashSetFree (signatureName signature))
    (term : RawCostTerm) :
    StructuralCongruence
      (CostConfig.eraseCanonical signatureName signaturePure
        (decodeRawConfig term.normalizeConfig))
      ((decodeCostTerm term).erase signatureName) := by
  have decodedConfig :
      decodeRawConfig term.normalizeConfig =
        (decodeCostTerm term.normalize).components := by
    unfold RawCostTerm.normalizeConfig decodeRawConfig
    change Multiset.map decodeCostTerm
      (stableKeySort RawCostTerm.key term.normalize.components :
        Multiset RawCostTerm) = _
    rw [stableKeySort_toMultiset]
    exact decodeRawConfig_components term.normalize
  rw [decodedConfig]
  exact StructuralCongruence.trans _ _ _
    (CostTerm.eraseCanonical_components_structural signatureName signaturePure
      (decodeCostTerm term.normalize))
      (RawCostTerm.erase_decode_normalize_structural signatureName term)

/-- Decoding a normalized executable configuration forgets only the stable
component order. -/
theorem decodeRawConfig_normalizeConfig (term : RawCostTerm) :
    decodeRawConfig term.normalizeConfig =
      (decodeCostTerm term.normalize).components := by
  unfold RawCostTerm.normalizeConfig decodeRawConfig
  change Multiset.map decodeCostTerm
    (stableKeySort RawCostTerm.key term.normalize.components :
      Multiset RawCostTerm) = _
  rw [stableKeySort_toMultiset]
  exact decodeRawConfig_components term.normalize

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
