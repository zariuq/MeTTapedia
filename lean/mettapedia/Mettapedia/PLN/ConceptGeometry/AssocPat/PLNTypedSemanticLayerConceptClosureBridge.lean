import Mettapedia.PLN.ConceptGeometry.AssocPat.PLNTypedSemanticLayerBridge
import Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge

/-!
# Typed Semantic-Layer Concept-Closure Bridge

This module connects the Chapter-12 semantic-layer gate to the existing
credal formed-concept closure bridge.  Semantic tags choose the already-built
inheritance query channel; lower/upper concept-family transport remains the
one from `CredalConceptFullInheritanceClosureBridge`.
-/

namespace Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryBuilder

open Mettapedia.PLN.WorldModel.PLNWorldModel
open Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel
open scoped ENNReal

variable {Query Obj Attr Q Gate : Type}
variable [Preorder Q] [Fintype Obj] [Fintype Attr]
variable [Fintype Gate] [Nonempty Gate]

private abbrev LowerFormedConcept
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q) :=
  _root_.Mettapedia.KR.ConceptOntology.LowerFormedConcept Γ M

private abbrev UpperFormedConcept
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q) :=
  _root_.Mettapedia.KR.ConceptOntology.UpperFormedConcept Γ M

private abbrev LowerFormedConceptPair
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q) :=
  _root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.LowerFormedConceptPair Γ M

private abbrev UpperFormedConceptPair
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q) :=
  _root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.UpperFormedConceptPair Γ M

/-- Encode robust lower-formed concept inheritance through a semantic-layer
ASSOC/PAT channel.  The layer only selects the typed query sort; it does not
alter the formed-concept closure semantics. -/
def semanticLayerLowerFormedConceptQ
    (layer : SemanticInheritanceLayer) (method : IntensionalMethod)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (enc : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query)
    (subConcept superConcept : LowerFormedConcept Γ M) :
    Sigma (InheritanceQueryFamily Query) :=
  semanticLayerQ layer method enc subConcept superConcept

/-- Encode permissive upper-formed concept inheritance through a semantic-layer
ASSOC/PAT channel. -/
def semanticLayerUpperFormedConceptQ
    (layer : SemanticInheritanceLayer) (method : IntensionalMethod)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (enc : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query)
    (subConcept superConcept : UpperFormedConcept Γ M) :
    Sigma (InheritanceQueryFamily Query) :=
  semanticLayerQ layer method enc subConcept superConcept

omit [Fintype Gate] [Nonempty Gate] in
@[simp] theorem semanticLayerLowerFormedConceptQ_sort
    (layer : SemanticInheritanceLayer) (method : IntensionalMethod)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (enc : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query)
    (subConcept superConcept : LowerFormedConcept Γ M) :
    (semanticLayerLowerFormedConceptQ layer method Γ M enc subConcept superConcept).1 =
      SemanticInheritanceLayer.toInheritanceSort layer method := by
  simp [semanticLayerLowerFormedConceptQ]

omit [Fintype Gate] [Nonempty Gate] in
@[simp] theorem semanticLayerUpperFormedConceptQ_sort
    (layer : SemanticInheritanceLayer) (method : IntensionalMethod)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (enc : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query)
    (subConcept superConcept : UpperFormedConcept Γ M) :
    (semanticLayerUpperFormedConceptQ layer method Γ M enc subConcept superConcept).1 =
      SemanticInheritanceLayer.toInheritanceSort layer method := by
  simp [semanticLayerUpperFormedConceptQ]

omit [Fintype Gate] [Nonempty Gate] in
@[simp] theorem semanticLayerLowerFormedConceptQ_intensional_assoc_sort
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (enc : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query)
    (subConcept superConcept : LowerFormedConcept Γ M) :
    (semanticLayerLowerFormedConceptQ .intensional .assoc Γ M enc subConcept superConcept).1 =
      .intensionalAssoc := by
  simp

omit [Fintype Gate] [Nonempty Gate] in
@[simp] theorem semanticLayerLowerFormedConceptQ_intensional_pat_sort
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (enc : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query)
    (subConcept superConcept : LowerFormedConcept Γ M) :
    (semanticLayerLowerFormedConceptQ .intensional .pat Γ M enc subConcept superConcept).1 =
      .intensionalPAT := by
  simp

omit [Fintype Gate] [Nonempty Gate] in
@[simp] theorem semanticLayerUpperFormedConceptQ_intensional_assoc_sort
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (enc : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query)
    (subConcept superConcept : UpperFormedConcept Γ M) :
    (semanticLayerUpperFormedConceptQ .intensional .assoc Γ M enc subConcept superConcept).1 =
      .intensionalAssoc := by
  simp

omit [Fintype Gate] [Nonempty Gate] in
@[simp] theorem semanticLayerUpperFormedConceptQ_intensional_pat_sort
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (enc : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query)
    (subConcept superConcept : UpperFormedConcept Γ M) :
    (semanticLayerUpperFormedConceptQ .intensional .pat Γ M enc subConcept superConcept).1 =
      .intensionalPAT := by
  simp

omit [Fintype Gate] [Nonempty Gate] in
/-- Positive canary: the extensional formed-concept semantic layer is
method-agnostic for robust lower concepts. -/
theorem semanticLayerLowerFormedConceptQ_extensional_assoc_eq_pat
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (enc : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query)
    (subConcept superConcept : LowerFormedConcept Γ M) :
    semanticLayerLowerFormedConceptQ .extensional .assoc Γ M enc subConcept superConcept =
      semanticLayerLowerFormedConceptQ .extensional .pat Γ M enc subConcept superConcept := by
  simp [semanticLayerLowerFormedConceptQ]

omit [Fintype Gate] [Nonempty Gate] in
/-- Positive canary: the extensional formed-concept semantic layer is
method-agnostic for permissive upper concepts. -/
theorem semanticLayerUpperFormedConceptQ_extensional_assoc_eq_pat
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (enc : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query)
    (subConcept superConcept : UpperFormedConcept Γ M) :
    semanticLayerUpperFormedConceptQ .extensional .assoc Γ M enc subConcept superConcept =
      semanticLayerUpperFormedConceptQ .extensional .pat Γ M enc subConcept superConcept := by
  simp [semanticLayerUpperFormedConceptQ]

omit [Fintype Gate] [Nonempty Gate] in
/-- Positive canary: the mixed formed-concept semantic layer is intentionally
method-agnostic for robust lower concepts.  ASSOC/PAT selection only matters in
the preextensional and intensional layers. -/
theorem semanticLayerLowerFormedConceptQ_mixed_assoc_eq_pat
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (enc : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query)
    (subConcept superConcept : LowerFormedConcept Γ M) :
    semanticLayerLowerFormedConceptQ .mixed .assoc Γ M enc subConcept superConcept =
      semanticLayerLowerFormedConceptQ .mixed .pat Γ M enc subConcept superConcept := by
  simp [semanticLayerLowerFormedConceptQ]

omit [Fintype Gate] [Nonempty Gate] in
/-- Positive canary: the mixed formed-concept semantic layer is intentionally
method-agnostic for permissive upper concepts. -/
theorem semanticLayerUpperFormedConceptQ_mixed_assoc_eq_pat
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (enc : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query)
    (subConcept superConcept : UpperFormedConcept Γ M) :
  semanticLayerUpperFormedConceptQ .mixed .assoc Γ M enc subConcept superConcept =
      semanticLayerUpperFormedConceptQ .mixed .pat Γ M enc subConcept superConcept := by
  simp [semanticLayerUpperFormedConceptQ]

omit [Fintype Gate] [Nonempty Gate] in
/-- Boundary canary: at the current query-channel level, preextensional formed
concepts reuse the corresponding intensional ASSOC/PAT channel. -/
theorem semanticLayerLowerFormedConceptQ_preextensional_eq_intensional
    (method : IntensionalMethod)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (enc : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query)
    (subConcept superConcept : LowerFormedConcept Γ M) :
    semanticLayerLowerFormedConceptQ .preextensional method Γ M enc subConcept superConcept =
      semanticLayerLowerFormedConceptQ .intensional method Γ M enc subConcept superConcept := by
  cases method <;> rfl

omit [Fintype Gate] [Nonempty Gate] in
/-- Boundary canary: at the current query-channel level, preextensional formed
concepts reuse the corresponding intensional ASSOC/PAT channel. -/
theorem semanticLayerUpperFormedConceptQ_preextensional_eq_intensional
    (method : IntensionalMethod)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (enc : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query)
    (subConcept superConcept : UpperFormedConcept Γ M) :
    semanticLayerUpperFormedConceptQ .preextensional method Γ M enc subConcept superConcept =
      semanticLayerUpperFormedConceptQ .intensional method Γ M enc subConcept superConcept := by
  cases method <;> rfl

omit [Fintype Gate] [Nonempty Gate] in
/-- Negative canary: the preextensional formed-concept semantic-layer gate keeps
ASSOC and PAT as distinct typed channels for robust lower concepts. -/
theorem semanticLayerLowerFormedConceptQ_preextensional_assoc_ne_pat
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (enc : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query)
    (subConcept superConcept : LowerFormedConcept Γ M) :
    semanticLayerLowerFormedConceptQ .preextensional .assoc Γ M enc subConcept superConcept ≠
      semanticLayerLowerFormedConceptQ .preextensional .pat Γ M enc subConcept superConcept := by
  intro h
  have hs := congrArg Sigma.fst h
  simp at hs

omit [Fintype Gate] [Nonempty Gate] in
/-- Negative canary: the preextensional formed-concept semantic-layer gate keeps
ASSOC and PAT as distinct typed channels for permissive upper concepts. -/
theorem semanticLayerUpperFormedConceptQ_preextensional_assoc_ne_pat
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (enc : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query)
    (subConcept superConcept : UpperFormedConcept Γ M) :
    semanticLayerUpperFormedConceptQ .preextensional .assoc Γ M enc subConcept superConcept ≠
      semanticLayerUpperFormedConceptQ .preextensional .pat Γ M enc subConcept superConcept := by
  intro h
  have hs := congrArg Sigma.fst h
  simp at hs

omit [Fintype Gate] [Nonempty Gate] in
/-- Negative canary: the formed-concept semantic-layer gate keeps ASSOC and PAT
as distinct typed channels for robust lower concepts. -/
theorem semanticLayerLowerFormedConceptQ_intensional_assoc_ne_pat
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (enc : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query)
    (subConcept superConcept : LowerFormedConcept Γ M) :
    semanticLayerLowerFormedConceptQ .intensional .assoc Γ M enc subConcept superConcept ≠
      semanticLayerLowerFormedConceptQ .intensional .pat Γ M enc subConcept superConcept := by
  intro h
  have hs := congrArg Sigma.fst h
  simp at hs

omit [Fintype Gate] [Nonempty Gate] in
/-- Negative canary: the formed-concept semantic-layer gate keeps ASSOC and PAT
as distinct typed channels for permissive upper concepts. -/
theorem semanticLayerUpperFormedConceptQ_intensional_assoc_ne_pat
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (enc : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query)
    (subConcept superConcept : UpperFormedConcept Γ M) :
    semanticLayerUpperFormedConceptQ .intensional .assoc Γ M enc subConcept superConcept ≠
      semanticLayerUpperFormedConceptQ .intensional .pat Γ M enc subConcept superConcept := by
  intro h
  have hs := congrArg Sigma.fst h
  simp at hs

omit [Fintype Gate] in
/-- Semantic-layer robust lower seeds embed into semantic-layer permissive
upper seeds whenever the two encoders agree after canonical lower-to-upper
formed-concept transport. -/
theorem lowerFormedConceptSemanticLayerQuerySet_subset_upperFormedConceptSemanticLayerQuerySet_of_liftEncode
    (layer : SemanticInheritanceLayer) (method : IntensionalMethod)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (encLower : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query)
    (encUpper : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query)
    (seed : Set (LowerFormedConceptPair Γ M))
    (hEncode :
      ∀ subConcept superConcept,
        semanticLayerLowerFormedConceptQ layer method Γ M encLower subConcept superConcept =
          semanticLayerUpperFormedConceptQ layer method Γ M encUpper
            (_root_.Mettapedia.KR.ConceptOntology.lowerToUpperFormedConcept Γ M subConcept)
            (_root_.Mettapedia.KR.ConceptOntology.lowerToUpperFormedConcept Γ M superConcept)) :
    _root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.lowerFormedConceptQuerySet
        Γ M (semanticLayerLowerFormedConceptQ layer method Γ M encLower) seed ⊆
      _root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperFormedConceptQuerySet
        Γ M (semanticLayerUpperFormedConceptQ layer method Γ M encUpper)
        (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.lowerSeedAsUpper
          Γ M seed) := by
  intro q hq
  rcases hq with ⟨p, hp, rfl⟩
  refine
    ⟨_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.lowerPairToUpperPair
        Γ M p, ?_, ?_⟩
  · exact ⟨p, hp, rfl⟩
  · exact hEncode p.1 p.2

omit [Fintype Gate] in
/-- The semantic-layer lower-to-upper seed inclusion is preserved by the
existing least WM rule-closure operator. -/
theorem leastRuleClosure_lowerFormedConceptSemanticLayerQuerySet_subset_upperFormedConceptSemanticLayerQuerySet_of_liftEncode
    {State : Type}
    [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
    [BinaryWorldModel State (Sigma (InheritanceQueryFamily Query))]
    (R : _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.RuleSet
      State (Sigma (InheritanceQueryFamily Query)))
    (W : State)
    (layer : SemanticInheritanceLayer) (method : IntensionalMethod)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (encLower : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query)
    (encUpper : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query)
    (seed : Set (LowerFormedConceptPair Γ M))
    (hEncode :
      ∀ subConcept superConcept,
        semanticLayerLowerFormedConceptQ layer method Γ M encLower subConcept superConcept =
          semanticLayerUpperFormedConceptQ layer method Γ M encUpper
            (_root_.Mettapedia.KR.ConceptOntology.lowerToUpperFormedConcept Γ M subConcept)
            (_root_.Mettapedia.KR.ConceptOntology.lowerToUpperFormedConcept Γ M superConcept)) :
    _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.leastRuleClosure
        (State := State) (Query := Sigma (InheritanceQueryFamily Query)) R W
        (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.lowerFormedConceptQuerySet
          Γ M (semanticLayerLowerFormedConceptQ layer method Γ M encLower) seed) ⊆
      _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.leastRuleClosure
        (State := State) (Query := Sigma (InheritanceQueryFamily Query)) R W
        (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperFormedConceptQuerySet
          Γ M (semanticLayerUpperFormedConceptQ layer method Γ M encUpper)
          (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.lowerSeedAsUpper
            Γ M seed)) := by
  exact
    _root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.leastRuleClosure_lowerFormedConceptQuerySet_subset_upperFormedConceptQuerySet_of_liftEncode
      (State := State) (Query := Sigma (InheritanceQueryFamily Query))
      R W Γ M
      (semanticLayerLowerFormedConceptQ layer method Γ M encLower)
      (semanticLayerUpperFormedConceptQ layer method Γ M encUpper)
      seed hEncode

omit [Fintype Gate] [Nonempty Gate] in
/-- Exact full-inheritance threshold validity for robust lower-formed concepts
encoded through a semantic-layer ASSOC/PAT channel. -/
theorem thresholdValid_lowerFormedConceptSemanticLayerQuerySet_of_exactFullInheritanceStrength
    {State : Type}
    [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
    [BinaryWorldModel State (Sigma (InheritanceQueryFamily Query))]
    (layer : SemanticInheritanceLayer) (method : IntensionalMethod)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (W : State) (τ : ℝ≥0∞)
    (encLower : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query)
    (seed : Set (LowerFormedConceptPair Γ M))
    (hEncode :
      ∀ subConcept superConcept,
        BinaryWorldModel.queryStrength
            (State := State) (Query := Sigma (InheritanceQueryFamily Query)) W
            (semanticLayerLowerFormedConceptQ layer method Γ M encLower subConcept superConcept) =
          ENNReal.ofReal
            (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept))
    (hSeed :
      ∀ p : LowerFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
            (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
            p.1 p.2)) :
    _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.thresholdValid
      (State := State) (Query := Sigma (InheritanceQueryFamily Query)) W τ
      (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.lowerFormedConceptQuerySet
        Γ M (semanticLayerLowerFormedConceptQ layer method Γ M encLower) seed) := by
  exact
    _root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.thresholdValid_lowerFormedConceptQuerySet_of_exactFullInheritanceStrength
      (State := State) (Query := Sigma (InheritanceQueryFamily Query))
      Γ M W τ (semanticLayerLowerFormedConceptQ layer method Γ M encLower) seed hEncode hSeed

omit [Fintype Gate] [Nonempty Gate] in
/-- Lower semantic-layer formed-concept obligations remain threshold-valid
after least WM rule closure. -/
theorem leastRuleClosure_thresholdValid_of_lowerSemanticLayerExactFullInheritanceStrength
    {State : Type}
    [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
    [BinaryWorldModel State (Sigma (InheritanceQueryFamily Query))]
    (R : _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.RuleSet
      State (Sigma (InheritanceQueryFamily Query)))
    (layer : SemanticInheritanceLayer) (method : IntensionalMethod)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (W : State) (τ : ℝ≥0∞)
    (encLower : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query)
    (seed : Set (LowerFormedConceptPair Γ M))
    (hEncode :
      ∀ subConcept superConcept,
        BinaryWorldModel.queryStrength
            (State := State) (Query := Sigma (InheritanceQueryFamily Query)) W
            (semanticLayerLowerFormedConceptQ layer method Γ M encLower subConcept superConcept) =
          ENNReal.ofReal
            (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept))
    (hSeed :
      ∀ p : LowerFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
            (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
            p.1 p.2)) :
    _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.thresholdValid
      (State := State) (Query := Sigma (InheritanceQueryFamily Query)) W τ
      (_root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.leastRuleClosure
        (State := State) (Query := Sigma (InheritanceQueryFamily Query)) R W
        (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.lowerFormedConceptQuerySet
          Γ M (semanticLayerLowerFormedConceptQ layer method Γ M encLower) seed)) := by
  exact
    _root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.leastRuleClosure_thresholdValid_of_exactFullInheritanceStrength
      (State := State) (Query := Sigma (InheritanceQueryFamily Query))
      R Γ M W τ (semanticLayerLowerFormedConceptQ layer method Γ M encLower) seed hEncode hSeed

omit [Fintype Gate] [Nonempty Gate] in
/-- If the available semantic-layer region is covered by the least closure of
exact robust lower-formed full-inheritance obligations, every available query
is WM-admissible at threshold `τ`. -/
theorem availableRegionAt_subset_wmAdmissibleRegionAt_of_lowerSemanticLayerExactFullInheritanceStrength
    {State Signal Cost : Type}
    [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
    [BinaryWorldModel State (Sigma (InheritanceQueryFamily Query))]
    [Preorder Cost]
    (P : _root_.Mettapedia.Hyperseed.StatefulPerspective
      State (Sigma (InheritanceQueryFamily Query)) Signal Cost)
    (R : _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.RuleSet
      State (Sigma (InheritanceQueryFamily Query)))
    (layer : SemanticInheritanceLayer) (method : IntensionalMethod)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (W : State) (B : Cost) (guard : Set (Sigma (InheritanceQueryFamily Query))) (τ : ℝ≥0∞)
    (encLower : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query)
    (seed : Set (LowerFormedConceptPair Γ M))
    (hEncode :
      ∀ subConcept superConcept,
        BinaryWorldModel.queryStrength
            (State := State) (Query := Sigma (InheritanceQueryFamily Query)) W
            (semanticLayerLowerFormedConceptQ layer method Γ M encLower subConcept superConcept) =
          ENNReal.ofReal
            (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept))
    (hSeed :
      ∀ p : LowerFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
            (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
            p.1 p.2))
    (hAvail :
      _root_.Mettapedia.Hyperseed.availableRegionAt P W B guard ⊆
        _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.leastRuleClosure
          (State := State) (Query := Sigma (InheritanceQueryFamily Query)) R W
          (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.lowerFormedConceptQuerySet
            Γ M (semanticLayerLowerFormedConceptQ layer method Γ M encLower) seed)) :
    _root_.Mettapedia.Hyperseed.availableRegionAt P W B guard ⊆
      _root_.Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt
        (State := State) (Query := Sigma (InheritanceQueryFamily Query)) P W B guard τ := by
  exact
    _root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.availableRegionAt_subset_wmAdmissibleRegionAt_of_exactFullInheritanceStrength
      (State := State) (Query := Sigma (InheritanceQueryFamily Query))
      P R Γ M W B guard τ (semanticLayerLowerFormedConceptQ layer method Γ M encLower)
      seed hEncode hSeed hAvail

omit [Fintype Gate] [Nonempty Gate] in
/-- If the available semantic-layer region is covered by the least closure of
exact robust lower-formed full-inheritance obligations, WM-admissibility
collapses back to the available region. -/
theorem wmAdmissibleRegionAt_eq_availableRegionAt_of_lowerSemanticLayerExactFullInheritanceStrength
    {State Signal Cost : Type}
    [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
    [BinaryWorldModel State (Sigma (InheritanceQueryFamily Query))]
    [Preorder Cost]
    (P : _root_.Mettapedia.Hyperseed.StatefulPerspective
      State (Sigma (InheritanceQueryFamily Query)) Signal Cost)
    (R : _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.RuleSet
      State (Sigma (InheritanceQueryFamily Query)))
    (layer : SemanticInheritanceLayer) (method : IntensionalMethod)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (W : State) (B : Cost) (guard : Set (Sigma (InheritanceQueryFamily Query))) (τ : ℝ≥0∞)
    (encLower : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query)
    (seed : Set (LowerFormedConceptPair Γ M))
    (hEncode :
      ∀ subConcept superConcept,
        BinaryWorldModel.queryStrength
            (State := State) (Query := Sigma (InheritanceQueryFamily Query)) W
            (semanticLayerLowerFormedConceptQ layer method Γ M encLower subConcept superConcept) =
          ENNReal.ofReal
            (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept))
    (hSeed :
      ∀ p : LowerFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
            (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
            p.1 p.2))
    (hAvail :
      _root_.Mettapedia.Hyperseed.availableRegionAt P W B guard ⊆
        _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.leastRuleClosure
          (State := State) (Query := Sigma (InheritanceQueryFamily Query)) R W
          (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.lowerFormedConceptQuerySet
            Γ M (semanticLayerLowerFormedConceptQ layer method Γ M encLower) seed)) :
    _root_.Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt
        (State := State) (Query := Sigma (InheritanceQueryFamily Query)) P W B guard τ =
      _root_.Mettapedia.Hyperseed.availableRegionAt P W B guard := by
  exact
    _root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.wmAdmissibleRegionAt_eq_availableRegionAt_of_exactFullInheritanceStrength
      (State := State) (Query := Sigma (InheritanceQueryFamily Query))
      P R Γ M W B guard τ (semanticLayerLowerFormedConceptQ layer method Γ M encLower)
      seed hEncode hSeed hAvail

omit [Fintype Gate] [Nonempty Gate] in
/-- Determined permissive upper seeds embed back into robust lower seeds at the
semantic-layer query level. -/
theorem upperFormedConceptSemanticLayerQuerySet_subset_lowerFormedConceptSemanticLayerQuerySet_of_determined_liftEncode
    (layer : SemanticInheritanceLayer) (method : IntensionalMethod)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (encUpper : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query)
    (encLower : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query)
    (seed : Set (UpperFormedConceptPair Γ M))
    (hDet : ∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
      (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.1.1) ∧
      (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.2.1))
    (hEncode : ∀ (p : UpperFormedConceptPair Γ M) (hp : p ∈ seed),
      semanticLayerUpperFormedConceptQ layer method Γ M encUpper p.1 p.2 =
        semanticLayerLowerFormedConceptQ layer method Γ M encLower
          (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperToLowerFormedConceptOfDetermines
            Γ M p.1 (hDet p hp).1)
          (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperToLowerFormedConceptOfDetermines
            Γ M p.2 (hDet p hp).2)) :
    _root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperFormedConceptQuerySet
        Γ M (semanticLayerUpperFormedConceptQ layer method Γ M encUpper) seed ⊆
      _root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.lowerFormedConceptQuerySet
        Γ M (semanticLayerLowerFormedConceptQ layer method Γ M encLower)
        (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.determinedUpperSeedAsLower
          Γ M seed hDet) := by
  intro q hq
  rcases hq with ⟨p, hp, rfl⟩
  refine
    ⟨_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperPairToLowerPairOfDetermines
        Γ M p (hDet p hp).1 (hDet p hp).2, ?_, ?_⟩
  · exact ⟨p, hp, rfl⟩
  · exact hEncode p hp

omit [Fintype Gate] [Nonempty Gate] in
/-- Determined upper-to-lower semantic-layer reclassification is preserved by
least WM rule closure.  This is the ASSOC/PAT typed-channel specialization of
the shared credal concept-closure transport. -/
theorem leastRuleClosure_upperFormedConceptSemanticLayerQuerySet_subset_lowerFormedConceptSemanticLayerQuerySet_of_determined_liftEncode
    {State : Type}
    [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
    [BinaryWorldModel State (Sigma (InheritanceQueryFamily Query))]
    (R : _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.RuleSet
      State (Sigma (InheritanceQueryFamily Query)))
    (W : State)
    (layer : SemanticInheritanceLayer) (method : IntensionalMethod)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (encUpper : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query)
    (encLower : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query)
    (seed : Set (UpperFormedConceptPair Γ M))
    (hDet : ∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
      (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.1.1) ∧
      (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.2.1))
    (hEncode : ∀ (p : UpperFormedConceptPair Γ M) (hp : p ∈ seed),
      semanticLayerUpperFormedConceptQ layer method Γ M encUpper p.1 p.2 =
        semanticLayerLowerFormedConceptQ layer method Γ M encLower
          (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperToLowerFormedConceptOfDetermines
            Γ M p.1 (hDet p hp).1)
          (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperToLowerFormedConceptOfDetermines
            Γ M p.2 (hDet p hp).2)) :
    _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.leastRuleClosure
        (State := State) (Query := Sigma (InheritanceQueryFamily Query)) R W
        (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperFormedConceptQuerySet
          Γ M (semanticLayerUpperFormedConceptQ layer method Γ M encUpper) seed) ⊆
      _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.leastRuleClosure
        (State := State) (Query := Sigma (InheritanceQueryFamily Query)) R W
        (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.lowerFormedConceptQuerySet
          Γ M (semanticLayerLowerFormedConceptQ layer method Γ M encLower)
          (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.determinedUpperSeedAsLower
            Γ M seed hDet)) := by
  exact
    _root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.leastRuleClosure_upperFormedConceptQuerySet_subset_lowerFormedConceptQuerySet_of_determined_liftEncode
      (State := State) (Query := Sigma (InheritanceQueryFamily Query))
      R W Γ M
      (semanticLayerUpperFormedConceptQ layer method Γ M encUpper)
      (semanticLayerLowerFormedConceptQ layer method Γ M encLower)
      seed hDet hEncode

omit [Fintype Gate] [Nonempty Gate] in
/-- Determined permissive upper semantic-layer seeds inherit robust lower
closure validity.  This specializes the shared credal concept-closure theorem
to the ASSOC/PAT typed query channel: the semantic layer selects the query sort,
while the lower robust closure supplies the threshold semantics. -/
theorem leastRuleClosure_thresholdValid_of_determinedUpperSemanticLayerLowerExactFullInheritanceStrength
    {State : Type}
    [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
    [BinaryWorldModel State (Sigma (InheritanceQueryFamily Query))]
    (R : _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.RuleSet
      State (Sigma (InheritanceQueryFamily Query)))
    (W : State)
    (layer : SemanticInheritanceLayer) (method : IntensionalMethod)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (τ : ℝ≥0∞)
    (encUpper : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query)
    (encLower : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query)
    (seed : Set (UpperFormedConceptPair Γ M))
    (hDet : ∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
      (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.1.1) ∧
      (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.2.1))
    (hEncode : ∀ (p : UpperFormedConceptPair Γ M) (hp : p ∈ seed),
      semanticLayerUpperFormedConceptQ layer method Γ M encUpper p.1 p.2 =
        semanticLayerLowerFormedConceptQ layer method Γ M encLower
          (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperToLowerFormedConceptOfDetermines
            Γ M p.1 (hDet p hp).1)
          (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperToLowerFormedConceptOfDetermines
            Γ M p.2 (hDet p hp).2))
    (hLowerEncode :
      ∀ subConcept superConcept,
        BinaryWorldModel.queryStrength
            (State := State) (Query := Sigma (InheritanceQueryFamily Query)) W
            (semanticLayerLowerFormedConceptQ layer method Γ M encLower subConcept superConcept) =
          ENNReal.ofReal
            (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept))
    (hLowerSeed :
      ∀ p : LowerFormedConceptPair Γ M,
        p ∈ _root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.determinedUpperSeedAsLower
          Γ M seed hDet →
          τ ≤ ENNReal.ofReal
            (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              p.1 p.2)) :
    _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.thresholdValid
      (State := State) (Query := Sigma (InheritanceQueryFamily Query)) W τ
      (_root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.leastRuleClosure
        (State := State) (Query := Sigma (InheritanceQueryFamily Query)) R W
        (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperFormedConceptQuerySet
          Γ M (semanticLayerUpperFormedConceptQ layer method Γ M encUpper) seed)) := by
  exact
    _root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.leastRuleClosure_thresholdValid_of_determinedUpperExactFullInheritanceStrength
      (State := State) (Query := Sigma (InheritanceQueryFamily Query))
      R W Γ M τ
      (semanticLayerUpperFormedConceptQ layer method Γ M encUpper)
      (semanticLayerLowerFormedConceptQ layer method Γ M encLower)
      seed hDet hEncode hLowerEncode hLowerSeed

omit [Fintype Gate] [Nonempty Gate] in
/-- If a semantic-layer available region is covered by the determined
permissive-upper closure, the reclassified robust lower exact-strength proof
makes every available query WM-admissible. -/
theorem availableRegionAt_subset_wmAdmissibleRegionAt_of_determinedUpperSemanticLayerLowerExactFullInheritanceStrength
    {State Signal Cost : Type}
    [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
    [BinaryWorldModel State (Sigma (InheritanceQueryFamily Query))]
    [Preorder Cost]
    (P : _root_.Mettapedia.Hyperseed.StatefulPerspective
      State (Sigma (InheritanceQueryFamily Query)) Signal Cost)
    (R : _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.RuleSet
      State (Sigma (InheritanceQueryFamily Query)))
    (W : State) (B : Cost) (guard : Set (Sigma (InheritanceQueryFamily Query)))
    (layer : SemanticInheritanceLayer) (method : IntensionalMethod)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (τ : ℝ≥0∞)
    (encUpper : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query)
    (encLower : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query)
    (seed : Set (UpperFormedConceptPair Γ M))
    (hDet : ∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
      (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.1.1) ∧
      (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.2.1))
    (hEncode : ∀ (p : UpperFormedConceptPair Γ M) (hp : p ∈ seed),
      semanticLayerUpperFormedConceptQ layer method Γ M encUpper p.1 p.2 =
        semanticLayerLowerFormedConceptQ layer method Γ M encLower
          (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperToLowerFormedConceptOfDetermines
            Γ M p.1 (hDet p hp).1)
          (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperToLowerFormedConceptOfDetermines
            Γ M p.2 (hDet p hp).2))
    (hLowerEncode :
      ∀ subConcept superConcept,
        BinaryWorldModel.queryStrength
            (State := State) (Query := Sigma (InheritanceQueryFamily Query)) W
            (semanticLayerLowerFormedConceptQ layer method Γ M encLower subConcept superConcept) =
          ENNReal.ofReal
            (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept))
    (hLowerSeed :
      ∀ p : LowerFormedConceptPair Γ M,
        p ∈ _root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.determinedUpperSeedAsLower
          Γ M seed hDet →
          τ ≤ ENNReal.ofReal
            (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              p.1 p.2))
    (hAvail :
      _root_.Mettapedia.Hyperseed.availableRegionAt P W B guard ⊆
        _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.leastRuleClosure
          (State := State) (Query := Sigma (InheritanceQueryFamily Query)) R W
          (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperFormedConceptQuerySet
            Γ M (semanticLayerUpperFormedConceptQ layer method Γ M encUpper) seed)) :
    _root_.Mettapedia.Hyperseed.availableRegionAt P W B guard ⊆
      _root_.Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt
        (State := State) (Query := Sigma (InheritanceQueryFamily Query)) P W B guard τ := by
  exact
    _root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.availableRegionAt_subset_wmAdmissibleRegionAt_of_determinedUpperExactFullInheritanceStrength
      (State := State) (Query := Sigma (InheritanceQueryFamily Query))
      P R Γ M W B guard τ
      (semanticLayerUpperFormedConceptQ layer method Γ M encUpper)
      (semanticLayerLowerFormedConceptQ layer method Γ M encLower)
      seed hDet hEncode hLowerEncode hLowerSeed hAvail

omit [Fintype Gate] [Nonempty Gate] in
/-- If a semantic-layer available region is covered by the determined
permissive-upper closure, WM-admissibility collapses back to availability by
the same reclassified robust lower exact-strength proof. -/
theorem wmAdmissibleRegionAt_eq_availableRegionAt_of_determinedUpperSemanticLayerLowerExactFullInheritanceStrength
    {State Signal Cost : Type}
    [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
    [BinaryWorldModel State (Sigma (InheritanceQueryFamily Query))]
    [Preorder Cost]
    (P : _root_.Mettapedia.Hyperseed.StatefulPerspective
      State (Sigma (InheritanceQueryFamily Query)) Signal Cost)
    (R : _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.RuleSet
      State (Sigma (InheritanceQueryFamily Query)))
    (W : State) (B : Cost) (guard : Set (Sigma (InheritanceQueryFamily Query)))
    (layer : SemanticInheritanceLayer) (method : IntensionalMethod)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (τ : ℝ≥0∞)
    (encUpper : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query)
    (encLower : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query)
    (seed : Set (UpperFormedConceptPair Γ M))
    (hDet : ∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
      (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.1.1) ∧
      (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
        (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.2.1))
    (hEncode : ∀ (p : UpperFormedConceptPair Γ M) (hp : p ∈ seed),
      semanticLayerUpperFormedConceptQ layer method Γ M encUpper p.1 p.2 =
        semanticLayerLowerFormedConceptQ layer method Γ M encLower
          (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperToLowerFormedConceptOfDetermines
            Γ M p.1 (hDet p hp).1)
          (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperToLowerFormedConceptOfDetermines
            Γ M p.2 (hDet p hp).2))
    (hLowerEncode :
      ∀ subConcept superConcept,
        BinaryWorldModel.queryStrength
            (State := State) (Query := Sigma (InheritanceQueryFamily Query)) W
            (semanticLayerLowerFormedConceptQ layer method Γ M encLower subConcept superConcept) =
          ENNReal.ofReal
            (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept))
    (hLowerSeed :
      ∀ p : LowerFormedConceptPair Γ M,
        p ∈ _root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.determinedUpperSeedAsLower
          Γ M seed hDet →
          τ ≤ ENNReal.ofReal
            (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              p.1 p.2))
    (hAvail :
      _root_.Mettapedia.Hyperseed.availableRegionAt P W B guard ⊆
        _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.leastRuleClosure
          (State := State) (Query := Sigma (InheritanceQueryFamily Query)) R W
          (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperFormedConceptQuerySet
            Γ M (semanticLayerUpperFormedConceptQ layer method Γ M encUpper) seed)) :
    _root_.Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt
        (State := State) (Query := Sigma (InheritanceQueryFamily Query)) P W B guard τ =
      _root_.Mettapedia.Hyperseed.availableRegionAt P W B guard := by
  exact
    _root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.wmAdmissibleRegionAt_eq_availableRegionAt_of_determinedUpperExactFullInheritanceStrength
      (State := State) (Query := Sigma (InheritanceQueryFamily Query))
      P R Γ M W B guard τ
      (semanticLayerUpperFormedConceptQ layer method Γ M encUpper)
      (semanticLayerLowerFormedConceptQ layer method Γ M encLower)
      seed hDet hEncode hLowerEncode hLowerSeed hAvail

omit [Fintype Gate] [Nonempty Gate] in
/-- Exact full-inheritance threshold validity for permissive upper-formed
concepts encoded through a semantic-layer ASSOC/PAT channel. -/
theorem thresholdValid_upperFormedConceptSemanticLayerQuerySet_of_exactFullInheritanceStrength
    {State : Type}
    [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
    [BinaryWorldModel State (Sigma (InheritanceQueryFamily Query))]
    (layer : SemanticInheritanceLayer) (method : IntensionalMethod)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (W : State) (τ : ℝ≥0∞)
    (encUpper : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query)
    (seed : Set (UpperFormedConceptPair Γ M))
    (hEncode :
      ∀ subConcept superConcept,
        BinaryWorldModel.queryStrength
            (State := State) (Query := Sigma (InheritanceQueryFamily Query)) W
            (semanticLayerUpperFormedConceptQ layer method Γ M encUpper subConcept superConcept) =
          ENNReal.ofReal
            (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.upperFormedConceptInterpretation Γ M)
              subConcept superConcept))
    (hSeed :
      ∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
            (_root_.Mettapedia.KR.ConceptOntology.upperFormedConceptInterpretation Γ M)
            p.1 p.2)) :
    _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.thresholdValid
      (State := State) (Query := Sigma (InheritanceQueryFamily Query)) W τ
      (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperFormedConceptQuerySet
        Γ M (semanticLayerUpperFormedConceptQ layer method Γ M encUpper) seed) := by
  exact
    _root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.thresholdValid_upperFormedConceptQuerySet_of_exactFullInheritanceStrength
      (State := State) (Query := Sigma (InheritanceQueryFamily Query))
      Γ M W τ (semanticLayerUpperFormedConceptQ layer method Γ M encUpper) seed hEncode hSeed

omit [Fintype Gate] [Nonempty Gate] in
/-- Upper semantic-layer formed-concept obligations remain threshold-valid
after least WM rule closure. -/
theorem leastRuleClosure_thresholdValid_of_upperSemanticLayerExactFullInheritanceStrength
    {State : Type}
    [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
    [BinaryWorldModel State (Sigma (InheritanceQueryFamily Query))]
    (R : _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.RuleSet
      State (Sigma (InheritanceQueryFamily Query)))
    (layer : SemanticInheritanceLayer) (method : IntensionalMethod)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (W : State) (τ : ℝ≥0∞)
    (encUpper : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query)
    (seed : Set (UpperFormedConceptPair Γ M))
    (hEncode :
      ∀ subConcept superConcept,
        BinaryWorldModel.queryStrength
            (State := State) (Query := Sigma (InheritanceQueryFamily Query)) W
            (semanticLayerUpperFormedConceptQ layer method Γ M encUpper subConcept superConcept) =
          ENNReal.ofReal
            (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.upperFormedConceptInterpretation Γ M)
              subConcept superConcept))
    (hSeed :
      ∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
            (_root_.Mettapedia.KR.ConceptOntology.upperFormedConceptInterpretation Γ M)
            p.1 p.2)) :
    _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.thresholdValid
      (State := State) (Query := Sigma (InheritanceQueryFamily Query)) W τ
      (_root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.leastRuleClosure
        (State := State) (Query := Sigma (InheritanceQueryFamily Query)) R W
        (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperFormedConceptQuerySet
          Γ M (semanticLayerUpperFormedConceptQ layer method Γ M encUpper) seed)) := by
  exact
    _root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.leastRuleClosure_thresholdValid_of_upperExactFullInheritanceStrength
      (State := State) (Query := Sigma (InheritanceQueryFamily Query))
      R Γ M W τ (semanticLayerUpperFormedConceptQ layer method Γ M encUpper) seed hEncode hSeed

omit [Fintype Gate] [Nonempty Gate] in
/-- If the available semantic-layer region is covered by the least closure of
exact permissive upper-formed full-inheritance obligations, every available
query is WM-admissible at threshold `τ`. -/
theorem availableRegionAt_subset_wmAdmissibleRegionAt_of_upperSemanticLayerExactFullInheritanceStrength
    {State Signal Cost : Type}
    [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
    [BinaryWorldModel State (Sigma (InheritanceQueryFamily Query))]
    [Preorder Cost]
    (P : _root_.Mettapedia.Hyperseed.StatefulPerspective
      State (Sigma (InheritanceQueryFamily Query)) Signal Cost)
    (R : _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.RuleSet
      State (Sigma (InheritanceQueryFamily Query)))
    (layer : SemanticInheritanceLayer) (method : IntensionalMethod)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (W : State) (B : Cost) (guard : Set (Sigma (InheritanceQueryFamily Query))) (τ : ℝ≥0∞)
    (encUpper : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query)
    (seed : Set (UpperFormedConceptPair Γ M))
    (hEncode :
      ∀ subConcept superConcept,
        BinaryWorldModel.queryStrength
            (State := State) (Query := Sigma (InheritanceQueryFamily Query)) W
            (semanticLayerUpperFormedConceptQ layer method Γ M encUpper subConcept superConcept) =
          ENNReal.ofReal
            (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.upperFormedConceptInterpretation Γ M)
              subConcept superConcept))
    (hSeed :
      ∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
            (_root_.Mettapedia.KR.ConceptOntology.upperFormedConceptInterpretation Γ M)
            p.1 p.2))
    (hAvail :
      _root_.Mettapedia.Hyperseed.availableRegionAt P W B guard ⊆
        _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.leastRuleClosure
          (State := State) (Query := Sigma (InheritanceQueryFamily Query)) R W
          (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperFormedConceptQuerySet
            Γ M (semanticLayerUpperFormedConceptQ layer method Γ M encUpper) seed)) :
    _root_.Mettapedia.Hyperseed.availableRegionAt P W B guard ⊆
      _root_.Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt
        (State := State) (Query := Sigma (InheritanceQueryFamily Query)) P W B guard τ := by
  exact
    _root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.availableRegionAt_subset_wmAdmissibleRegionAt_of_upperExactFullInheritanceStrength
      (State := State) (Query := Sigma (InheritanceQueryFamily Query))
      P R Γ M W B guard τ (semanticLayerUpperFormedConceptQ layer method Γ M encUpper)
      seed hEncode hSeed hAvail

omit [Fintype Gate] [Nonempty Gate] in
/-- If the available semantic-layer region is covered by the least closure of
exact permissive upper-formed full-inheritance obligations, WM-admissibility
collapses back to the available region. -/
theorem wmAdmissibleRegionAt_eq_availableRegionAt_of_upperSemanticLayerExactFullInheritanceStrength
    {State Signal Cost : Type}
    [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
    [BinaryWorldModel State (Sigma (InheritanceQueryFamily Query))]
    [Preorder Cost]
    (P : _root_.Mettapedia.Hyperseed.StatefulPerspective
      State (Sigma (InheritanceQueryFamily Query)) Signal Cost)
    (R : _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.RuleSet
      State (Sigma (InheritanceQueryFamily Query)))
    (layer : SemanticInheritanceLayer) (method : IntensionalMethod)
    (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) (M : Obj → Attr → Q)
    (W : State) (B : Cost) (guard : Set (Sigma (InheritanceQueryFamily Query))) (τ : ℝ≥0∞)
    (encUpper : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query)
    (seed : Set (UpperFormedConceptPair Γ M))
    (hEncode :
      ∀ subConcept superConcept,
        BinaryWorldModel.queryStrength
            (State := State) (Query := Sigma (InheritanceQueryFamily Query)) W
            (semanticLayerUpperFormedConceptQ layer method Γ M encUpper subConcept superConcept) =
          ENNReal.ofReal
            (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.upperFormedConceptInterpretation Γ M)
              subConcept superConcept))
    (hSeed :
      ∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
            (_root_.Mettapedia.KR.ConceptOntology.upperFormedConceptInterpretation Γ M)
            p.1 p.2))
    (hAvail :
      _root_.Mettapedia.Hyperseed.availableRegionAt P W B guard ⊆
        _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.leastRuleClosure
          (State := State) (Query := Sigma (InheritanceQueryFamily Query)) R W
          (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperFormedConceptQuerySet
            Γ M (semanticLayerUpperFormedConceptQ layer method Γ M encUpper) seed)) :
    _root_.Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt
        (State := State) (Query := Sigma (InheritanceQueryFamily Query)) P W B guard τ =
      _root_.Mettapedia.Hyperseed.availableRegionAt P W B guard := by
  exact
    _root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.wmAdmissibleRegionAt_eq_availableRegionAt_of_upperExactFullInheritanceStrength
      (State := State) (Query := Sigma (InheritanceQueryFamily Query))
      P R Γ M W B guard τ (semanticLayerUpperFormedConceptQ layer method Γ M encUpper)
      seed hEncode hSeed hAvail

/-- Proof-carrying profile for the semantic-layer formed-concept closure
bridge.  It exposes the lower/upper seed transport, threshold-validity, and
WM-admissibility theorems as one Chapter-12 handle instead of adding a long
list of thin truth-index aliases.  The layer-boundary fields record that
extensional and mixed evidence are method-agnostic, preextensional and
intensional evidence keep ASSOC and PAT separate, and the current
preextensional gate reuses the corresponding intensional ASSOC/PAT query
channel rather than introducing a second semantics. -/
structure SemanticLayerConceptClosureBridgeProfile where
  lowerAssocSort :
    ∀ {Query Obj Attr Q Gate : Type} [Preorder Q] [Fintype Obj] [Fintype Attr],
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) →
      (enc : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query) →
      (subConcept : LowerFormedConcept Γ M) →
      (superConcept : LowerFormedConcept Γ M) →
      (semanticLayerLowerFormedConceptQ .intensional .assoc Γ M enc subConcept superConcept).1 =
        .intensionalAssoc
  lowerPATSort :
    ∀ {Query Obj Attr Q Gate : Type} [Preorder Q] [Fintype Obj] [Fintype Attr],
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) →
      (enc : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query) →
      (subConcept : LowerFormedConcept Γ M) →
      (superConcept : LowerFormedConcept Γ M) →
      (semanticLayerLowerFormedConceptQ .intensional .pat Γ M enc subConcept superConcept).1 =
        .intensionalPAT
  upperAssocSort :
    ∀ {Query Obj Attr Q Gate : Type} [Preorder Q] [Fintype Obj] [Fintype Attr],
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) →
      (enc : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query) →
      (subConcept : UpperFormedConcept Γ M) →
      (superConcept : UpperFormedConcept Γ M) →
      (semanticLayerUpperFormedConceptQ .intensional .assoc Γ M enc subConcept superConcept).1 =
        .intensionalAssoc
  upperPATSort :
    ∀ {Query Obj Attr Q Gate : Type} [Preorder Q] [Fintype Obj] [Fintype Attr],
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) →
      (enc : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query) →
      (subConcept : UpperFormedConcept Γ M) →
      (superConcept : UpperFormedConcept Γ M) →
      (semanticLayerUpperFormedConceptQ .intensional .pat Γ M enc subConcept superConcept).1 =
        .intensionalPAT
  lowerExtensionalAssocPATCollapse :
    ∀ {Query Obj Attr Q Gate : Type} [Preorder Q] [Fintype Obj] [Fintype Attr],
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) →
      (enc : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query) →
      (subConcept : LowerFormedConcept Γ M) →
      (superConcept : LowerFormedConcept Γ M) →
      semanticLayerLowerFormedConceptQ .extensional .assoc Γ M enc subConcept superConcept =
        semanticLayerLowerFormedConceptQ .extensional .pat Γ M enc subConcept superConcept
  upperExtensionalAssocPATCollapse :
    ∀ {Query Obj Attr Q Gate : Type} [Preorder Q] [Fintype Obj] [Fintype Attr],
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) →
      (enc : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query) →
      (subConcept : UpperFormedConcept Γ M) →
      (superConcept : UpperFormedConcept Γ M) →
      semanticLayerUpperFormedConceptQ .extensional .assoc Γ M enc subConcept superConcept =
        semanticLayerUpperFormedConceptQ .extensional .pat Γ M enc subConcept superConcept
  lowerMixedAssocPATCollapse :
    ∀ {Query Obj Attr Q Gate : Type} [Preorder Q] [Fintype Obj] [Fintype Attr],
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) →
      (enc : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query) →
      (subConcept : LowerFormedConcept Γ M) →
      (superConcept : LowerFormedConcept Γ M) →
      semanticLayerLowerFormedConceptQ .mixed .assoc Γ M enc subConcept superConcept =
        semanticLayerLowerFormedConceptQ .mixed .pat Γ M enc subConcept superConcept
  upperMixedAssocPATCollapse :
    ∀ {Query Obj Attr Q Gate : Type} [Preorder Q] [Fintype Obj] [Fintype Attr],
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) →
      (enc : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query) →
      (subConcept : UpperFormedConcept Γ M) →
      (superConcept : UpperFormedConcept Γ M) →
      semanticLayerUpperFormedConceptQ .mixed .assoc Γ M enc subConcept superConcept =
        semanticLayerUpperFormedConceptQ .mixed .pat Γ M enc subConcept superConcept
  lowerPreextensionalUsesIntensionalChannel :
    ∀ {Query Obj Attr Q Gate : Type} [Preorder Q] [Fintype Obj] [Fintype Attr],
      (method : IntensionalMethod) →
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) →
      (enc : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query) →
      (subConcept : LowerFormedConcept Γ M) →
      (superConcept : LowerFormedConcept Γ M) →
      semanticLayerLowerFormedConceptQ .preextensional method Γ M enc subConcept superConcept =
        semanticLayerLowerFormedConceptQ .intensional method Γ M enc subConcept superConcept
  upperPreextensionalUsesIntensionalChannel :
    ∀ {Query Obj Attr Q Gate : Type} [Preorder Q] [Fintype Obj] [Fintype Attr],
      (method : IntensionalMethod) →
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) →
      (enc : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query) →
      (subConcept : UpperFormedConcept Γ M) →
      (superConcept : UpperFormedConcept Γ M) →
      semanticLayerUpperFormedConceptQ .preextensional method Γ M enc subConcept superConcept =
        semanticLayerUpperFormedConceptQ .intensional method Γ M enc subConcept superConcept
  lowerPreextensionalAssocPATDoNotCollapse :
    ∀ {Query Obj Attr Q Gate : Type} [Preorder Q] [Fintype Obj] [Fintype Attr],
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) →
      (enc : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query) →
      (subConcept : LowerFormedConcept Γ M) →
      (superConcept : LowerFormedConcept Γ M) →
      semanticLayerLowerFormedConceptQ .preextensional .assoc Γ M enc subConcept superConcept ≠
        semanticLayerLowerFormedConceptQ .preextensional .pat Γ M enc subConcept superConcept
  upperPreextensionalAssocPATDoNotCollapse :
    ∀ {Query Obj Attr Q Gate : Type} [Preorder Q] [Fintype Obj] [Fintype Attr],
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) →
      (enc : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query) →
      (subConcept : UpperFormedConcept Γ M) →
      (superConcept : UpperFormedConcept Γ M) →
      semanticLayerUpperFormedConceptQ .preextensional .assoc Γ M enc subConcept superConcept ≠
        semanticLayerUpperFormedConceptQ .preextensional .pat Γ M enc subConcept superConcept
  lowerAssocPATDoNotCollapse :
    ∀ {Query Obj Attr Q Gate : Type} [Preorder Q] [Fintype Obj] [Fintype Attr],
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) →
      (enc : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query) →
      (subConcept : LowerFormedConcept Γ M) →
      (superConcept : LowerFormedConcept Γ M) →
      semanticLayerLowerFormedConceptQ .intensional .assoc Γ M enc subConcept superConcept ≠
        semanticLayerLowerFormedConceptQ .intensional .pat Γ M enc subConcept superConcept
  upperAssocPATDoNotCollapse :
    ∀ {Query Obj Attr Q Gate : Type} [Preorder Q] [Fintype Obj] [Fintype Attr],
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) →
      (enc : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query) →
      (subConcept : UpperFormedConcept Γ M) →
      (superConcept : UpperFormedConcept Γ M) →
      semanticLayerUpperFormedConceptQ .intensional .assoc Γ M enc subConcept superConcept ≠
        semanticLayerUpperFormedConceptQ .intensional .pat Γ M enc subConcept superConcept
  lowerSeedEmbedsUpper :
    ∀ {Query Obj Attr Q Gate : Type} [Preorder Q] [Fintype Obj] [Fintype Attr] [Nonempty Gate],
      (layer : SemanticInheritanceLayer) → (method : IntensionalMethod) →
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) →
      (encLower : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query) →
      (encUpper : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query) →
      (seed : Set (LowerFormedConceptPair Γ M)) →
      (∀ subConcept superConcept,
        semanticLayerLowerFormedConceptQ layer method Γ M encLower subConcept superConcept =
          semanticLayerUpperFormedConceptQ layer method Γ M encUpper
            (_root_.Mettapedia.KR.ConceptOntology.lowerToUpperFormedConcept Γ M subConcept)
            (_root_.Mettapedia.KR.ConceptOntology.lowerToUpperFormedConcept Γ M superConcept)) →
      _root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.lowerFormedConceptQuerySet
          Γ M (semanticLayerLowerFormedConceptQ layer method Γ M encLower) seed ⊆
        _root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperFormedConceptQuerySet
          Γ M (semanticLayerUpperFormedConceptQ layer method Γ M encUpper)
          (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.lowerSeedAsUpper
            Γ M seed)
  lowerClosureEmbedsUpperClosure :
    ∀ {Query Obj Attr Q Gate : Type} [Preorder Q] [Fintype Obj] [Fintype Attr] [Nonempty Gate]
      {State : Type} [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [BinaryWorldModel State (Sigma (InheritanceQueryFamily Query))],
      (R : _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.RuleSet
        State (Sigma (InheritanceQueryFamily Query))) →
      (W : State) → (layer : SemanticInheritanceLayer) → (method : IntensionalMethod) →
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) →
      (encLower : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query) →
      (encUpper : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query) →
      (seed : Set (LowerFormedConceptPair Γ M)) →
      (∀ subConcept superConcept,
        semanticLayerLowerFormedConceptQ layer method Γ M encLower subConcept superConcept =
          semanticLayerUpperFormedConceptQ layer method Γ M encUpper
            (_root_.Mettapedia.KR.ConceptOntology.lowerToUpperFormedConcept Γ M subConcept)
            (_root_.Mettapedia.KR.ConceptOntology.lowerToUpperFormedConcept Γ M superConcept)) →
      _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.leastRuleClosure
          (State := State) (Query := Sigma (InheritanceQueryFamily Query)) R W
          (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.lowerFormedConceptQuerySet
            Γ M (semanticLayerLowerFormedConceptQ layer method Γ M encLower) seed) ⊆
        _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.leastRuleClosure
          (State := State) (Query := Sigma (InheritanceQueryFamily Query)) R W
          (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperFormedConceptQuerySet
            Γ M (semanticLayerUpperFormedConceptQ layer method Γ M encUpper)
            (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.lowerSeedAsUpper
              Γ M seed))
  determinedUpperSeedEmbedsLower :
    ∀ {Query Obj Attr Q Gate : Type} [Preorder Q] [Fintype Obj] [Fintype Attr],
      (layer : SemanticInheritanceLayer) → (method : IntensionalMethod) →
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) →
      (encUpper : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query) →
      (encLower : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query) →
      (seed : Set (UpperFormedConceptPair Γ M)) →
      (hDet : ∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
        (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
          (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.1.1) ∧
        (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
          (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.2.1)) →
      (∀ (p : UpperFormedConceptPair Γ M) (hp : p ∈ seed),
        semanticLayerUpperFormedConceptQ layer method Γ M encUpper p.1 p.2 =
          semanticLayerLowerFormedConceptQ layer method Γ M encLower
            (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperToLowerFormedConceptOfDetermines
              Γ M p.1 (hDet p hp).1)
            (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperToLowerFormedConceptOfDetermines
              Γ M p.2 (hDet p hp).2)) →
      _root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperFormedConceptQuerySet
          Γ M (semanticLayerUpperFormedConceptQ layer method Γ M encUpper) seed ⊆
        _root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.lowerFormedConceptQuerySet
          Γ M (semanticLayerLowerFormedConceptQ layer method Γ M encLower)
          (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.determinedUpperSeedAsLower
            Γ M seed hDet)
  determinedUpperClosureEmbedsLowerClosure :
    ∀ {Query Obj Attr Q Gate : Type} [Preorder Q] [Fintype Obj] [Fintype Attr]
      {State : Type} [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [BinaryWorldModel State (Sigma (InheritanceQueryFamily Query))],
      (R : _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.RuleSet
        State (Sigma (InheritanceQueryFamily Query))) →
      (W : State) → (layer : SemanticInheritanceLayer) → (method : IntensionalMethod) →
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) →
      (encUpper : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query) →
      (encLower : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query) →
      (seed : Set (UpperFormedConceptPair Γ M)) →
      (hDet : ∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
        (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
          (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.1.1) ∧
        (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
          (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.2.1)) →
      (∀ (p : UpperFormedConceptPair Γ M) (hp : p ∈ seed),
        semanticLayerUpperFormedConceptQ layer method Γ M encUpper p.1 p.2 =
          semanticLayerLowerFormedConceptQ layer method Γ M encLower
            (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperToLowerFormedConceptOfDetermines
              Γ M p.1 (hDet p hp).1)
            (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperToLowerFormedConceptOfDetermines
              Γ M p.2 (hDet p hp).2)) →
      _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.leastRuleClosure
          (State := State) (Query := Sigma (InheritanceQueryFamily Query)) R W
          (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperFormedConceptQuerySet
            Γ M (semanticLayerUpperFormedConceptQ layer method Γ M encUpper) seed) ⊆
      _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.leastRuleClosure
          (State := State) (Query := Sigma (InheritanceQueryFamily Query)) R W
          (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.lowerFormedConceptQuerySet
            Γ M (semanticLayerLowerFormedConceptQ layer method Γ M encLower)
            (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.determinedUpperSeedAsLower
              Γ M seed hDet))
  determinedUpperClosureThresholdValid :
    ∀ {Query Obj Attr Q Gate : Type} [Preorder Q] [Fintype Obj] [Fintype Attr]
      {State : Type} [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [BinaryWorldModel State (Sigma (InheritanceQueryFamily Query))],
      (R : _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.RuleSet
        State (Sigma (InheritanceQueryFamily Query))) →
      (W : State) → (layer : SemanticInheritanceLayer) → (method : IntensionalMethod) →
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) → (τ : ℝ≥0∞) →
      (encUpper : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query) →
      (encLower : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query) →
      (seed : Set (UpperFormedConceptPair Γ M)) →
      (hDet : ∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
        (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
          (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.1.1) ∧
        (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
          (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.2.1)) →
      (∀ (p : UpperFormedConceptPair Γ M) (hp : p ∈ seed),
        semanticLayerUpperFormedConceptQ layer method Γ M encUpper p.1 p.2 =
          semanticLayerLowerFormedConceptQ layer method Γ M encLower
            (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperToLowerFormedConceptOfDetermines
              Γ M p.1 (hDet p hp).1)
            (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperToLowerFormedConceptOfDetermines
              Γ M p.2 (hDet p hp).2)) →
      (∀ subConcept superConcept,
        BinaryWorldModel.queryStrength
            (State := State) (Query := Sigma (InheritanceQueryFamily Query)) W
            (semanticLayerLowerFormedConceptQ layer method Γ M encLower subConcept superConcept) =
          ENNReal.ofReal
            (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept)) →
      (∀ p : LowerFormedConceptPair Γ M,
        p ∈ _root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.determinedUpperSeedAsLower
          Γ M seed hDet →
          τ ≤ ENNReal.ofReal
            (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              p.1 p.2)) →
      _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.thresholdValid
        (State := State) (Query := Sigma (InheritanceQueryFamily Query)) W τ
        (_root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.leastRuleClosure
          (State := State) (Query := Sigma (InheritanceQueryFamily Query)) R W
          (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperFormedConceptQuerySet
            Γ M (semanticLayerUpperFormedConceptQ layer method Γ M encUpper) seed))
  determinedUpperAvailableRegionAdmissible :
    ∀ {Query Obj Attr Q Gate : Type} [Preorder Q] [Fintype Obj] [Fintype Attr]
      {State Signal Cost : Type} [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [BinaryWorldModel State (Sigma (InheritanceQueryFamily Query))] [Preorder Cost],
      (P : _root_.Mettapedia.Hyperseed.StatefulPerspective
        State (Sigma (InheritanceQueryFamily Query)) Signal Cost) →
      (R : _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.RuleSet
        State (Sigma (InheritanceQueryFamily Query))) →
      (W : State) → (B : Cost) → (guard : Set (Sigma (InheritanceQueryFamily Query))) →
      (layer : SemanticInheritanceLayer) → (method : IntensionalMethod) →
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) → (τ : ℝ≥0∞) →
      (encUpper : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query) →
      (encLower : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query) →
      (seed : Set (UpperFormedConceptPair Γ M)) →
      (hDet : ∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
        (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
          (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.1.1) ∧
        (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
          (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.2.1)) →
      (∀ (p : UpperFormedConceptPair Γ M) (hp : p ∈ seed),
        semanticLayerUpperFormedConceptQ layer method Γ M encUpper p.1 p.2 =
          semanticLayerLowerFormedConceptQ layer method Γ M encLower
            (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperToLowerFormedConceptOfDetermines
              Γ M p.1 (hDet p hp).1)
            (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperToLowerFormedConceptOfDetermines
              Γ M p.2 (hDet p hp).2)) →
      (∀ subConcept superConcept,
        BinaryWorldModel.queryStrength
            (State := State) (Query := Sigma (InheritanceQueryFamily Query)) W
            (semanticLayerLowerFormedConceptQ layer method Γ M encLower subConcept superConcept) =
          ENNReal.ofReal
            (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept)) →
      (∀ p : LowerFormedConceptPair Γ M,
        p ∈ _root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.determinedUpperSeedAsLower
          Γ M seed hDet →
          τ ≤ ENNReal.ofReal
            (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              p.1 p.2)) →
      (_root_.Mettapedia.Hyperseed.availableRegionAt P W B guard ⊆
        _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.leastRuleClosure
          (State := State) (Query := Sigma (InheritanceQueryFamily Query)) R W
          (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperFormedConceptQuerySet
            Γ M (semanticLayerUpperFormedConceptQ layer method Γ M encUpper) seed)) →
      _root_.Mettapedia.Hyperseed.availableRegionAt P W B guard ⊆
        _root_.Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt
          (State := State) (Query := Sigma (InheritanceQueryFamily Query)) P W B guard τ
  determinedUpperAdmissibleRegionEqualsAvailable :
    ∀ {Query Obj Attr Q Gate : Type} [Preorder Q] [Fintype Obj] [Fintype Attr]
      {State Signal Cost : Type} [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [BinaryWorldModel State (Sigma (InheritanceQueryFamily Query))] [Preorder Cost],
      (P : _root_.Mettapedia.Hyperseed.StatefulPerspective
        State (Sigma (InheritanceQueryFamily Query)) Signal Cost) →
      (R : _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.RuleSet
        State (Sigma (InheritanceQueryFamily Query))) →
      (W : State) → (B : Cost) → (guard : Set (Sigma (InheritanceQueryFamily Query))) →
      (layer : SemanticInheritanceLayer) → (method : IntensionalMethod) →
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) → (τ : ℝ≥0∞) →
      (encUpper : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query) →
      (encLower : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query) →
      (seed : Set (UpperFormedConceptPair Γ M)) →
      (hDet : ∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
        (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
          (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.1.1) ∧
        (_root_.Mettapedia.KR.ConceptOntology.gateCredalProjectiveSpec (Gate := Gate)).determinesGlobalGamble
          (_root_.Mettapedia.KR.ConceptOntology.conceptFormationGamble Γ M p.2.1)) →
      (∀ (p : UpperFormedConceptPair Γ M) (hp : p ∈ seed),
        semanticLayerUpperFormedConceptQ layer method Γ M encUpper p.1 p.2 =
          semanticLayerLowerFormedConceptQ layer method Γ M encLower
            (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperToLowerFormedConceptOfDetermines
              Γ M p.1 (hDet p hp).1)
            (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperToLowerFormedConceptOfDetermines
              Γ M p.2 (hDet p hp).2)) →
      (∀ subConcept superConcept,
        BinaryWorldModel.queryStrength
            (State := State) (Query := Sigma (InheritanceQueryFamily Query)) W
            (semanticLayerLowerFormedConceptQ layer method Γ M encLower subConcept superConcept) =
          ENNReal.ofReal
            (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept)) →
      (∀ p : LowerFormedConceptPair Γ M,
        p ∈ _root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.determinedUpperSeedAsLower
          Γ M seed hDet →
          τ ≤ ENNReal.ofReal
            (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              p.1 p.2)) →
      (_root_.Mettapedia.Hyperseed.availableRegionAt P W B guard ⊆
        _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.leastRuleClosure
          (State := State) (Query := Sigma (InheritanceQueryFamily Query)) R W
          (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperFormedConceptQuerySet
            Γ M (semanticLayerUpperFormedConceptQ layer method Γ M encUpper) seed)) →
      _root_.Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt
          (State := State) (Query := Sigma (InheritanceQueryFamily Query)) P W B guard τ =
        _root_.Mettapedia.Hyperseed.availableRegionAt P W B guard
  lowerThresholdValid :
    ∀ {Query Obj Attr Q Gate : Type} [Preorder Q] [Fintype Obj] [Fintype Attr] {State : Type}
      [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [BinaryWorldModel State (Sigma (InheritanceQueryFamily Query))],
      (layer : SemanticInheritanceLayer) → (method : IntensionalMethod) →
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) → (W : State) → (τ : ℝ≥0∞) →
      (encLower : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query) →
      (seed : Set (LowerFormedConceptPair Γ M)) →
      (∀ subConcept superConcept,
        BinaryWorldModel.queryStrength
            (State := State) (Query := Sigma (InheritanceQueryFamily Query)) W
            (semanticLayerLowerFormedConceptQ layer method Γ M encLower subConcept superConcept) =
          ENNReal.ofReal
            (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept)) →
      (∀ p : LowerFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
            (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
            p.1 p.2)) →
      _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.thresholdValid
        (State := State) (Query := Sigma (InheritanceQueryFamily Query)) W τ
        (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.lowerFormedConceptQuerySet
          Γ M (semanticLayerLowerFormedConceptQ layer method Γ M encLower) seed)
  upperThresholdValid :
    ∀ {Query Obj Attr Q Gate : Type} [Preorder Q] [Fintype Obj] [Fintype Attr] {State : Type}
      [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [BinaryWorldModel State (Sigma (InheritanceQueryFamily Query))],
      (layer : SemanticInheritanceLayer) → (method : IntensionalMethod) →
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) → (W : State) → (τ : ℝ≥0∞) →
      (encUpper : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query) →
      (seed : Set (UpperFormedConceptPair Γ M)) →
      (∀ subConcept superConcept,
        BinaryWorldModel.queryStrength
            (State := State) (Query := Sigma (InheritanceQueryFamily Query)) W
            (semanticLayerUpperFormedConceptQ layer method Γ M encUpper subConcept superConcept) =
          ENNReal.ofReal
            (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.upperFormedConceptInterpretation Γ M)
              subConcept superConcept)) →
      (∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
            (_root_.Mettapedia.KR.ConceptOntology.upperFormedConceptInterpretation Γ M)
            p.1 p.2)) →
      _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.thresholdValid
        (State := State) (Query := Sigma (InheritanceQueryFamily Query)) W τ
        (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperFormedConceptQuerySet
          Γ M (semanticLayerUpperFormedConceptQ layer method Γ M encUpper) seed)
  lowerClosureThresholdValid :
    ∀ {Query Obj Attr Q Gate : Type} [Preorder Q] [Fintype Obj] [Fintype Attr] {State : Type}
      [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [BinaryWorldModel State (Sigma (InheritanceQueryFamily Query))],
      (R : _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.RuleSet
        State (Sigma (InheritanceQueryFamily Query))) →
      (layer : SemanticInheritanceLayer) → (method : IntensionalMethod) →
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) → (W : State) → (τ : ℝ≥0∞) →
      (encLower : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query) →
      (seed : Set (LowerFormedConceptPair Γ M)) →
      (∀ subConcept superConcept,
        BinaryWorldModel.queryStrength
            (State := State) (Query := Sigma (InheritanceQueryFamily Query)) W
            (semanticLayerLowerFormedConceptQ layer method Γ M encLower subConcept superConcept) =
          ENNReal.ofReal
            (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept)) →
      (∀ p : LowerFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
            (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
            p.1 p.2)) →
      _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.thresholdValid
        (State := State) (Query := Sigma (InheritanceQueryFamily Query)) W τ
        (_root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.leastRuleClosure
          (State := State) (Query := Sigma (InheritanceQueryFamily Query)) R W
          (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.lowerFormedConceptQuerySet
            Γ M (semanticLayerLowerFormedConceptQ layer method Γ M encLower) seed))
  upperClosureThresholdValid :
    ∀ {Query Obj Attr Q Gate : Type} [Preorder Q] [Fintype Obj] [Fintype Attr] {State : Type}
      [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [BinaryWorldModel State (Sigma (InheritanceQueryFamily Query))],
      (R : _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.RuleSet
        State (Sigma (InheritanceQueryFamily Query))) →
      (layer : SemanticInheritanceLayer) → (method : IntensionalMethod) →
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) → (W : State) → (τ : ℝ≥0∞) →
      (encUpper : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query) →
      (seed : Set (UpperFormedConceptPair Γ M)) →
      (∀ subConcept superConcept,
        BinaryWorldModel.queryStrength
            (State := State) (Query := Sigma (InheritanceQueryFamily Query)) W
            (semanticLayerUpperFormedConceptQ layer method Γ M encUpper subConcept superConcept) =
          ENNReal.ofReal
            (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.upperFormedConceptInterpretation Γ M)
              subConcept superConcept)) →
      (∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
            (_root_.Mettapedia.KR.ConceptOntology.upperFormedConceptInterpretation Γ M)
            p.1 p.2)) →
      _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.thresholdValid
        (State := State) (Query := Sigma (InheritanceQueryFamily Query)) W τ
        (_root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.leastRuleClosure
          (State := State) (Query := Sigma (InheritanceQueryFamily Query)) R W
          (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperFormedConceptQuerySet
            Γ M (semanticLayerUpperFormedConceptQ layer method Γ M encUpper) seed))
  lowerAvailableRegionAdmissible :
    ∀ {Query Obj Attr Q Gate : Type} [Preorder Q] [Fintype Obj] [Fintype Attr]
      {State Signal Cost : Type} [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [BinaryWorldModel State (Sigma (InheritanceQueryFamily Query))] [Preorder Cost],
      (P : _root_.Mettapedia.Hyperseed.StatefulPerspective
        State (Sigma (InheritanceQueryFamily Query)) Signal Cost) →
      (R : _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.RuleSet
        State (Sigma (InheritanceQueryFamily Query))) →
      (layer : SemanticInheritanceLayer) → (method : IntensionalMethod) →
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) → (W : State) → (B : Cost) →
      (guard : Set (Sigma (InheritanceQueryFamily Query))) → (τ : ℝ≥0∞) →
      (encLower : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query) →
      (seed : Set (LowerFormedConceptPair Γ M)) →
      (∀ subConcept superConcept,
        BinaryWorldModel.queryStrength
            (State := State) (Query := Sigma (InheritanceQueryFamily Query)) W
            (semanticLayerLowerFormedConceptQ layer method Γ M encLower subConcept superConcept) =
          ENNReal.ofReal
            (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept)) →
      (∀ p : LowerFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
            (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
            p.1 p.2)) →
      (_root_.Mettapedia.Hyperseed.availableRegionAt P W B guard ⊆
        _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.leastRuleClosure
          (State := State) (Query := Sigma (InheritanceQueryFamily Query)) R W
          (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.lowerFormedConceptQuerySet
            Γ M (semanticLayerLowerFormedConceptQ layer method Γ M encLower) seed)) →
      _root_.Mettapedia.Hyperseed.availableRegionAt P W B guard ⊆
        _root_.Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt
          (State := State) (Query := Sigma (InheritanceQueryFamily Query)) P W B guard τ
  lowerAdmissibleRegionEqualsAvailable :
    ∀ {Query Obj Attr Q Gate : Type} [Preorder Q] [Fintype Obj] [Fintype Attr]
      {State Signal Cost : Type} [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [BinaryWorldModel State (Sigma (InheritanceQueryFamily Query))] [Preorder Cost],
      (P : _root_.Mettapedia.Hyperseed.StatefulPerspective
        State (Sigma (InheritanceQueryFamily Query)) Signal Cost) →
      (R : _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.RuleSet
        State (Sigma (InheritanceQueryFamily Query))) →
      (layer : SemanticInheritanceLayer) → (method : IntensionalMethod) →
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) → (W : State) → (B : Cost) →
      (guard : Set (Sigma (InheritanceQueryFamily Query))) → (τ : ℝ≥0∞) →
      (encLower : InheritanceQueryBuilder (LowerFormedConcept Γ M) Query) →
      (seed : Set (LowerFormedConceptPair Γ M)) →
      (∀ subConcept superConcept,
        BinaryWorldModel.queryStrength
            (State := State) (Query := Sigma (InheritanceQueryFamily Query)) W
            (semanticLayerLowerFormedConceptQ layer method Γ M encLower subConcept superConcept) =
          ENNReal.ofReal
            (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
              subConcept superConcept)) →
      (∀ p : LowerFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
            (_root_.Mettapedia.KR.ConceptOntology.lowerFormedConceptInterpretation Γ M)
            p.1 p.2)) →
      (_root_.Mettapedia.Hyperseed.availableRegionAt P W B guard ⊆
        _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.leastRuleClosure
          (State := State) (Query := Sigma (InheritanceQueryFamily Query)) R W
          (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.lowerFormedConceptQuerySet
            Γ M (semanticLayerLowerFormedConceptQ layer method Γ M encLower) seed)) →
      _root_.Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt
          (State := State) (Query := Sigma (InheritanceQueryFamily Query)) P W B guard τ =
        _root_.Mettapedia.Hyperseed.availableRegionAt P W B guard
  upperAvailableRegionAdmissible :
    ∀ {Query Obj Attr Q Gate : Type} [Preorder Q] [Fintype Obj] [Fintype Attr]
      {State Signal Cost : Type} [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [BinaryWorldModel State (Sigma (InheritanceQueryFamily Query))] [Preorder Cost],
      (P : _root_.Mettapedia.Hyperseed.StatefulPerspective
        State (Sigma (InheritanceQueryFamily Query)) Signal Cost) →
      (R : _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.RuleSet
        State (Sigma (InheritanceQueryFamily Query))) →
      (layer : SemanticInheritanceLayer) → (method : IntensionalMethod) →
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) → (W : State) → (B : Cost) →
      (guard : Set (Sigma (InheritanceQueryFamily Query))) → (τ : ℝ≥0∞) →
      (encUpper : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query) →
      (seed : Set (UpperFormedConceptPair Γ M)) →
      (∀ subConcept superConcept,
        BinaryWorldModel.queryStrength
            (State := State) (Query := Sigma (InheritanceQueryFamily Query)) W
            (semanticLayerUpperFormedConceptQ layer method Γ M encUpper subConcept superConcept) =
          ENNReal.ofReal
            (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.upperFormedConceptInterpretation Γ M)
              subConcept superConcept)) →
      (∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
            (_root_.Mettapedia.KR.ConceptOntology.upperFormedConceptInterpretation Γ M)
            p.1 p.2)) →
      (_root_.Mettapedia.Hyperseed.availableRegionAt P W B guard ⊆
        _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.leastRuleClosure
          (State := State) (Query := Sigma (InheritanceQueryFamily Query)) R W
          (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperFormedConceptQuerySet
            Γ M (semanticLayerUpperFormedConceptQ layer method Γ M encUpper) seed)) →
      _root_.Mettapedia.Hyperseed.availableRegionAt P W B guard ⊆
        _root_.Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt
          (State := State) (Query := Sigma (InheritanceQueryFamily Query)) P W B guard τ
  upperAdmissibleRegionEqualsAvailable :
    ∀ {Query Obj Attr Q Gate : Type} [Preorder Q] [Fintype Obj] [Fintype Attr]
      {State Signal Cost : Type} [Mettapedia.PLN.Evidence.EvidenceClass.EvidenceType State]
      [BinaryWorldModel State (Sigma (InheritanceQueryFamily Query))] [Preorder Cost],
      (P : _root_.Mettapedia.Hyperseed.StatefulPerspective
        State (Sigma (InheritanceQueryFamily Query)) Signal Cost) →
      (R : _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.RuleSet
        State (Sigma (InheritanceQueryFamily Query))) →
      (layer : SemanticInheritanceLayer) → (method : IntensionalMethod) →
      (Γ : Gate → _root_.Mettapedia.KR.ConceptOntology.EvidenceGate Q) →
      (M : Obj → Attr → Q) → (W : State) → (B : Cost) →
      (guard : Set (Sigma (InheritanceQueryFamily Query))) → (τ : ℝ≥0∞) →
      (encUpper : InheritanceQueryBuilder (UpperFormedConcept Γ M) Query) →
      (seed : Set (UpperFormedConceptPair Γ M)) →
      (∀ subConcept superConcept,
        BinaryWorldModel.queryStrength
            (State := State) (Query := Sigma (InheritanceQueryFamily Query)) W
            (semanticLayerUpperFormedConceptQ layer method Γ M encUpper subConcept superConcept) =
          ENNReal.ofReal
            (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
              (_root_.Mettapedia.KR.ConceptOntology.upperFormedConceptInterpretation Γ M)
              subConcept superConcept)) →
      (∀ p : UpperFormedConceptPair Γ M, p ∈ seed →
        τ ≤ ENNReal.ofReal
          (_root_.Mettapedia.KR.ConceptGeometry.ExtensionalIntensionalDivergence.fullInheritanceStrength
            (_root_.Mettapedia.KR.ConceptOntology.upperFormedConceptInterpretation Γ M)
            p.1 p.2)) →
      (_root_.Mettapedia.Hyperseed.availableRegionAt P W B guard ⊆
        _root_.Mettapedia.PLN.WorldModel.Fixpoint.PLNWorldModelFixpointClosure.leastRuleClosure
          (State := State) (Query := Sigma (InheritanceQueryFamily Query)) R W
          (_root_.Mettapedia.PLN.Bridges.KR.ConceptClosure.CredalConceptFullInheritanceClosureBridge.upperFormedConceptQuerySet
            Γ M (semanticLayerUpperFormedConceptQ layer method Γ M encUpper) seed)) →
      _root_.Mettapedia.PLN.RuleFamilies.HigherOrder.PLNWorldModelRegimeAdmissibility.wmAdmissibleRegionAt
          (State := State) (Query := Sigma (InheritanceQueryFamily Query)) P W B guard τ =
        _root_.Mettapedia.Hyperseed.availableRegionAt P W B guard

/-- Public profile for the semantic-layer formed-concept closure bridge. -/
def semanticLayerConceptClosureBridgeProfile :
    SemanticLayerConceptClosureBridgeProfile where
  lowerAssocSort :=
    semanticLayerLowerFormedConceptQ_intensional_assoc_sort
  lowerPATSort :=
    semanticLayerLowerFormedConceptQ_intensional_pat_sort
  upperAssocSort :=
    semanticLayerUpperFormedConceptQ_intensional_assoc_sort
  upperPATSort :=
    semanticLayerUpperFormedConceptQ_intensional_pat_sort
  lowerExtensionalAssocPATCollapse :=
    semanticLayerLowerFormedConceptQ_extensional_assoc_eq_pat
  upperExtensionalAssocPATCollapse :=
    semanticLayerUpperFormedConceptQ_extensional_assoc_eq_pat
  lowerMixedAssocPATCollapse :=
    semanticLayerLowerFormedConceptQ_mixed_assoc_eq_pat
  upperMixedAssocPATCollapse :=
    semanticLayerUpperFormedConceptQ_mixed_assoc_eq_pat
  lowerPreextensionalUsesIntensionalChannel :=
    semanticLayerLowerFormedConceptQ_preextensional_eq_intensional
  upperPreextensionalUsesIntensionalChannel :=
    semanticLayerUpperFormedConceptQ_preextensional_eq_intensional
  lowerPreextensionalAssocPATDoNotCollapse :=
    semanticLayerLowerFormedConceptQ_preextensional_assoc_ne_pat
  upperPreextensionalAssocPATDoNotCollapse :=
    semanticLayerUpperFormedConceptQ_preextensional_assoc_ne_pat
  lowerAssocPATDoNotCollapse :=
    semanticLayerLowerFormedConceptQ_intensional_assoc_ne_pat
  upperAssocPATDoNotCollapse :=
    semanticLayerUpperFormedConceptQ_intensional_assoc_ne_pat
  lowerSeedEmbedsUpper :=
    lowerFormedConceptSemanticLayerQuerySet_subset_upperFormedConceptSemanticLayerQuerySet_of_liftEncode
  lowerClosureEmbedsUpperClosure :=
    leastRuleClosure_lowerFormedConceptSemanticLayerQuerySet_subset_upperFormedConceptSemanticLayerQuerySet_of_liftEncode
  determinedUpperSeedEmbedsLower :=
    upperFormedConceptSemanticLayerQuerySet_subset_lowerFormedConceptSemanticLayerQuerySet_of_determined_liftEncode
  determinedUpperClosureEmbedsLowerClosure :=
    leastRuleClosure_upperFormedConceptSemanticLayerQuerySet_subset_lowerFormedConceptSemanticLayerQuerySet_of_determined_liftEncode
  determinedUpperClosureThresholdValid :=
    leastRuleClosure_thresholdValid_of_determinedUpperSemanticLayerLowerExactFullInheritanceStrength
  determinedUpperAvailableRegionAdmissible :=
    availableRegionAt_subset_wmAdmissibleRegionAt_of_determinedUpperSemanticLayerLowerExactFullInheritanceStrength
  determinedUpperAdmissibleRegionEqualsAvailable :=
    wmAdmissibleRegionAt_eq_availableRegionAt_of_determinedUpperSemanticLayerLowerExactFullInheritanceStrength
  lowerThresholdValid :=
    thresholdValid_lowerFormedConceptSemanticLayerQuerySet_of_exactFullInheritanceStrength
  upperThresholdValid :=
    thresholdValid_upperFormedConceptSemanticLayerQuerySet_of_exactFullInheritanceStrength
  lowerClosureThresholdValid :=
    leastRuleClosure_thresholdValid_of_lowerSemanticLayerExactFullInheritanceStrength
  upperClosureThresholdValid :=
    leastRuleClosure_thresholdValid_of_upperSemanticLayerExactFullInheritanceStrength
  lowerAvailableRegionAdmissible :=
    availableRegionAt_subset_wmAdmissibleRegionAt_of_lowerSemanticLayerExactFullInheritanceStrength
  lowerAdmissibleRegionEqualsAvailable :=
    wmAdmissibleRegionAt_eq_availableRegionAt_of_lowerSemanticLayerExactFullInheritanceStrength
  upperAvailableRegionAdmissible :=
    availableRegionAt_subset_wmAdmissibleRegionAt_of_upperSemanticLayerExactFullInheritanceStrength
  upperAdmissibleRegionEqualsAvailable :=
    wmAdmissibleRegionAt_eq_availableRegionAt_of_upperSemanticLayerExactFullInheritanceStrength

end Mettapedia.PLN.ConceptGeometry.AssocPat.PLNIntensionalWorldModel.InheritanceQueryBuilder
