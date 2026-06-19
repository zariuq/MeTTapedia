import Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge
import Mettapedia.Logic.PLNIntensionalWorldModel

/-!
# Higher-Order Predicate ASSOC/PAT Bridge

This module connects the finite higher-order predicate-vocabulary interpretation
to the existing Chapter-12 ASSOC/PAT subset-semantics layer. It does not define
a new higher-order pattern-similarity semantics. Instead, PAT/ASSOC evidence is
given an explicit theorem target: monotonicity over the pure-intensional
inheritance relation already induced by the finite predicate vocabulary.
-/

namespace Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge

open Mettapedia.Logic.HOL
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNIntensionalWorldModel

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Pure-intensional pair-subset relation induced by a finite active
higher-order predicate vocabulary. For an ordered pair `(a,b)` to be below
`(c,d)`, the left endpoint `c` must intensionally inherit from `a`, and the
right endpoint `b` must intensionally inherit from `d`.

This is the relation that ASSOC/PAT subset semantics should consume when the
atoms being compared are finite-vocabulary HOL predicates. -/
def predicateVocabularyIntensionalPairSubsetRel
    {State : Type}
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ) :
    State → Pred → Pred → Pred → Pred → Prop :=
  fun _W a b c d =>
    (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
        (Base := Base) (Const := Const) M σ decode).IntensionalInherits c a ∧
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
        (Base := Base) (Const := Const) M σ decode).IntensionalInherits b d

theorem predicateVocabularyIntensionalPairSubsetRel_iff
    {State : Type}
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (W : State) (a b c d : Pred) :
    predicateVocabularyIntensionalPairSubsetRel
        (Base := Base) (Const := Const) M σ decode W a b c d ↔
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).IntensionalInherits c a ∧
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).IntensionalInherits b d := by
  rfl

/-- Same-intent replacement supplies the pure-intensional pair-subset
relation. This is the small theoremic bridge from pattern/intension equivalence
to the ASSOC/PAT monotonicity interface. -/
theorem predicateVocabularyIntensionalPairSubsetRel_of_sameIntent
    {State : Type}
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (W : State) {a b c d : Pred}
    (hLeft :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode a c)
    (hRight :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode b d) :
    predicateVocabularyIntensionalPairSubsetRel
      (Base := Base) (Const := Const) M σ decode W a b c d := by
  have hLeftMutual :=
    (Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent_iff_mutualIntensional
        (Base := Base) (Const := Const) M σ decode a c).1 hLeft
  have hRightMutual :=
    (Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent_iff_mutualIntensional
        (Base := Base) (Const := Const) M σ decode b d).1 hRight
  exact ⟨hLeftMutual.2, hRightMutual.1⟩

/-- Reduce the concept-to-HOL transport obligation to an explicit intent-map
interface.

`hReflect` says every decoded HO predicate-vocabulary intent item has a
concrete pattern-side attribute image; `hPreserve` says concrete intent facts
transport back to the decoded HO vocabulary. Together they carry intensional
inheritance from the concrete interpretation into the finite predicate
vocabulary. -/
theorem predicateVocabularyIntensionalInherits_of_intentMap
    {Pattern Obj Attr : Type}
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Pattern Obj Attr)
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (code : Pattern → Pred)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → Attr)
    (hReflect : ∀ {p : Pattern} {r : Pred},
      r ∈ ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent →
        attrOf r ∈ (I.meaning p).intent)
    (hPreserve : ∀ {p : Pattern} {r : Pred},
      attrOf r ∈ (I.meaning p).intent →
        r ∈ ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent)
    {p q : Pattern}
    (h : I.IntensionalInherits p q) :
    (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
      (Base := Base) (Const := Const) M σ decode).IntensionalInherits
        (code p) (code q) := by
  intro r hr
  exact hPreserve (p := p) (r := r) (h (hReflect (p := q) (r := r) hr))

/-- A single calibrated-intent equivalence discharges the two map laws needed
to transport concrete Chapter-12 intensional inheritance into the decoded HO
predicate vocabulary.

This is the preferred seam for richer empirical or factor-graph semantics:
prove one iff saying what each decoded finite-vocabulary intent item means in
the concrete interpretation, then reuse the existing abstract-inheritance
machinery unchanged. -/
theorem predicateVocabularyIntensionalInherits_of_intentCalibration
    {Pattern Obj Attr : Type}
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Pattern Obj Attr)
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (code : Pattern → Pred)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → Attr)
    (hCal : ∀ {p : Pattern} {r : Pred},
      r ∈ ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
        attrOf r ∈ (I.meaning p).intent)
    {p q : Pattern}
    (h : I.IntensionalInherits p q) :
    (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
      (Base := Base) (Const := Const) M σ decode).IntensionalInherits
        (code p) (code q) := by
  exact
    predicateVocabularyIntensionalInherits_of_intentMap
      (I := I) (M := M) (σ := σ) (code := code) (decode := decode)
      attrOf
      (fun {p r} hr => (hCal (p := p) (r := r)).1 hr)
      (fun {p r} hr => (hCal (p := p) (r := r)).2 hr)
      h

/-- Transport a concrete abstract-inheritance pair-subset proof into the
finite-vocabulary HO predicate-pair relation.

This is the non-silo seam for Chapter-12 style pattern semantics: a concrete
pattern-side interpretation may feed the HO ASSOC/PAT target once its
intensional-inheritance facts are transported into the decoded finite
predicate vocabulary. -/
theorem predicateVocabularyIntensionalPairSubsetRel_of_interpretationPairSubsetRel
    {State Pattern Obj Attr : Type}
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Pattern Obj Attr)
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (code : Pattern → Pred)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (hTransport : ∀ {p q : Pattern},
      I.IntensionalInherits p q →
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).IntensionalInherits
            (code p) (code q))
    (W : State) {a b c d : Pattern}
    (hRel : I.PairSubsetRel a b c d) :
    predicateVocabularyIntensionalPairSubsetRel
      (Base := Base) (Const := Const) M σ decode W
      (code a) (code b) (code c) (code d) := by
  exact ⟨hTransport hRel.1.2, hTransport hRel.2.2⟩

/-- Transport a concrete pair-subset proof through the explicit intent-map
interface. This is the preferred theorem target for richer Chapter-12 pattern
semantics: discharge `hReflect` and `hPreserve`, then the HO finite-vocabulary
ASSOC/PAT target follows. -/
theorem predicateVocabularyIntensionalPairSubsetRel_of_interpretationPairSubsetRel_viaIntentMap
    {State Pattern Obj Attr : Type}
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Pattern Obj Attr)
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (code : Pattern → Pred)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → Attr)
    (hReflect : ∀ {p : Pattern} {r : Pred},
      r ∈ ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent →
        attrOf r ∈ (I.meaning p).intent)
    (hPreserve : ∀ {p : Pattern} {r : Pred},
      attrOf r ∈ (I.meaning p).intent →
        r ∈ ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent)
    (W : State) {a b c d : Pattern}
    (hRel : I.PairSubsetRel a b c d) :
    predicateVocabularyIntensionalPairSubsetRel
      (Base := Base) (Const := Const) M σ decode W
      (code a) (code b) (code c) (code d) := by
  exact
    predicateVocabularyIntensionalPairSubsetRel_of_interpretationPairSubsetRel
      (I := I) (M := M) (σ := σ) (code := code) (decode := decode)
      (fun {p q} hpq =>
        predicateVocabularyIntensionalInherits_of_intentMap
          (I := I) (M := M) (σ := σ) (code := code) (decode := decode)
          attrOf hReflect hPreserve hpq)
      W hRel

/-- Transport a concrete pair-subset proof through one calibrated-intent
equivalence. This is the same theoremic seam as
`predicateVocabularyIntensionalPairSubsetRel_of_interpretationPairSubsetRel_viaIntentMap`,
but packaged so semantic layers can prove a single iff instead of separate
reflection and preservation lemmas. -/
theorem predicateVocabularyIntensionalPairSubsetRel_of_interpretationPairSubsetRel_viaIntentCalibration
    {State Pattern Obj Attr : Type}
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Pattern Obj Attr)
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (code : Pattern → Pred)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → Attr)
    (hCal : ∀ {p : Pattern} {r : Pred},
      r ∈ ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
        attrOf r ∈ (I.meaning p).intent)
    (W : State) {a b c d : Pattern}
    (hRel : I.PairSubsetRel a b c d) :
    predicateVocabularyIntensionalPairSubsetRel
      (Base := Base) (Const := Const) M σ decode W
      (code a) (code b) (code c) (code d) := by
  exact
    predicateVocabularyIntensionalPairSubsetRel_of_interpretationPairSubsetRel
      (I := I) (M := M) (σ := σ) (code := code) (decode := decode)
      (fun {p q} hpq =>
        predicateVocabularyIntensionalInherits_of_intentCalibration
          (I := I) (M := M) (σ := σ) (code := code) (decode := decode)
          attrOf hCal hpq)
      W hRel

/-- Transport a concrete abstract mutual-inheritance proof into
finite-vocabulary same-intent. This is the equality/similarity companion to
`predicateVocabularyIntensionalPairSubsetRel_of_interpretationPairSubsetRel`. -/
theorem predicateVocabularySameIntent_of_interpretationMutualInherits
    {Pattern Obj Attr : Type}
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Pattern Obj Attr)
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (code : Pattern → Pred)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (hTransport : ∀ {p q : Pattern},
      I.IntensionalInherits p q →
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).IntensionalInherits
            (code p) (code q))
    {p q : Pattern}
    (hMutual : I.MutualInherits p q) :
    Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
      (Base := Base) (Const := Const) M σ decode (code p) (code q) := by
  exact
      (Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent_iff_mutualIntensional
      (Base := Base) (Const := Const) M σ decode (code p) (code q)).2
      ⟨hTransport hMutual.1.2, hTransport hMutual.2.2⟩

/-- Same-intent transport through the explicit intent-map interface. -/
theorem predicateVocabularySameIntent_of_interpretationMutualInherits_viaIntentMap
    {Pattern Obj Attr : Type}
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Pattern Obj Attr)
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (code : Pattern → Pred)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → Attr)
    (hReflect : ∀ {p : Pattern} {r : Pred},
      r ∈ ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent →
        attrOf r ∈ (I.meaning p).intent)
    (hPreserve : ∀ {p : Pattern} {r : Pred},
      attrOf r ∈ (I.meaning p).intent →
        r ∈ ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent)
    {p q : Pattern}
    (hMutual : I.MutualInherits p q) :
    Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
      (Base := Base) (Const := Const) M σ decode (code p) (code q) := by
  exact
    predicateVocabularySameIntent_of_interpretationMutualInherits
      (I := I) (M := M) (σ := σ) (code := code) (decode := decode)
      (fun {p q} hpq =>
        predicateVocabularyIntensionalInherits_of_intentMap
          (I := I) (M := M) (σ := σ) (code := code) (decode := decode)
          attrOf hReflect hPreserve hpq)
      hMutual

/-- Same-intent transport through one calibrated-intent equivalence. -/
theorem predicateVocabularySameIntent_of_interpretationMutualInherits_viaIntentCalibration
    {Pattern Obj Attr : Type}
    (I : Mettapedia.Logic.AbstractInheritance.Interpretation Pattern Obj Attr)
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (code : Pattern → Pred)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → Attr)
    (hCal : ∀ {p : Pattern} {r : Pred},
      r ∈ ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
        attrOf r ∈ (I.meaning p).intent)
    {p q : Pattern}
    (hMutual : I.MutualInherits p q) :
    Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
      (Base := Base) (Const := Const) M σ decode (code p) (code q) := by
  exact
    predicateVocabularySameIntent_of_interpretationMutualInherits
      (I := I) (M := M) (σ := σ) (code := code) (decode := decode)
      (fun {p q} hpq =>
        predicateVocabularyIntensionalInherits_of_intentCalibration
          (I := I) (M := M) (σ := σ) (code := code) (decode := decode)
          attrOf hCal hpq)
      hMutual

/-- Finite-vocabulary intent size for a decoded HOL predicate. This is a
concrete pattern-side score component: it counts how many active vocabulary
items are in the predicate's induced intent. -/
noncomputable def predicateVocabularyIntentCard
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (p : Pred) : ℝ :=
  (((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
      (Base := Base) (Const := Const) M σ decode).meaning p).intent.ncard : ℝ)

/-- Intent deficit relative to the finite active vocabulary. A more general
right-hand predicate has a larger deficit, matching the inheritance-pair
orientation used by ASSOC/PAT subset semantics. -/
noncomputable def predicateVocabularyIntentDeficit
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (p : Pred) : ℝ :=
  (((Set.univ : Set Pred).ncard : ℝ) -
    predicateVocabularyIntentCard (Base := Base) (Const := Const) M σ decode p)

/-- A concrete finite-vocabulary order-rank score for predicate pairs.

The left endpoint contributes its intent size; the right endpoint contributes
its intent deficit. This is nonconstant and monotone in exactly the
`predicateVocabularyIntensionalPairSubsetRel` direction, giving a real
score-level witness for the ASSOC/PAT subset-semantics interface. -/
noncomputable def predicateVocabularyPairOrderRankScore
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (a b : Pred) : ℝ :=
  predicateVocabularyIntentCard (Base := Base) (Const := Const) M σ decode a +
    predicateVocabularyIntentDeficit (Base := Base) (Const := Const) M σ decode b

/-- Weighted finite-vocabulary order-rank score for predicate pairs.

This is the first nontrivial score-family extension of
`predicateVocabularyPairOrderRankScore`: the left endpoint's intent size and
the right endpoint's intent deficit may receive different nonnegative weights.
The nonnegativity hypotheses in the monotonicity theorem below are essential;
negative weights reverse one of the concept-geometry channels. -/
noncomputable def predicateVocabularyWeightedPairOrderRankScore
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (leftWeight rightWeight : ℝ)
    (a b : Pred) : ℝ :=
  leftWeight *
      predicateVocabularyIntentCard (Base := Base) (Const := Const) M σ decode a +
    rightWeight *
      predicateVocabularyIntentDeficit (Base := Base) (Const := Const) M σ decode b

/-- Intent-card scores are nonnegative because they are finite cardinalities. -/
theorem predicateVocabularyIntentCard_nonneg
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (p : Pred) :
    0 ≤ predicateVocabularyIntentCard (Base := Base) (Const := Const) M σ decode p := by
  unfold predicateVocabularyIntentCard
  exact_mod_cast Nat.zero_le _

/-- Intent deficit is nonnegative because every predicate intent sits inside
the active finite vocabulary. -/
theorem predicateVocabularyIntentDeficit_nonneg
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (p : Pred) :
    0 ≤ predicateVocabularyIntentDeficit (Base := Base) (Const := Const) M σ decode p := by
  unfold predicateVocabularyIntentDeficit predicateVocabularyIntentCard
  exact sub_nonneg.mpr (by
    exact_mod_cast
      Set.ncard_le_ncard
        (by intro x _hx; exact Set.mem_univ x)
        (Set.toFinite _))

theorem predicateVocabularyIntentCard_mono_of_intensionalInherits
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    {p q : Pred}
    (h :
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
        (Base := Base) (Const := Const) M σ decode).IntensionalInherits p q) :
    predicateVocabularyIntentCard (Base := Base) (Const := Const) M σ decode q ≤
      predicateVocabularyIntentCard (Base := Base) (Const := Const) M σ decode p := by
  unfold predicateVocabularyIntentCard
  exact_mod_cast Set.ncard_le_ncard h (Set.toFinite _)

theorem predicateVocabularyIntentDeficit_mono_of_reverse_intensionalInherits
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    {p q : Pred}
    (h :
      (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
        (Base := Base) (Const := Const) M σ decode).IntensionalInherits p q) :
    predicateVocabularyIntentDeficit (Base := Base) (Const := Const) M σ decode p ≤
      predicateVocabularyIntentDeficit (Base := Base) (Const := Const) M σ decode q := by
  exact sub_le_sub_left
    (predicateVocabularyIntentCard_mono_of_intensionalInherits
      (Base := Base) (Const := Const) M σ decode h)
    (((Set.univ : Set Pred).ncard : ℝ))

theorem predicateVocabularyPairOrderRankScore_mono
    {State : Type}
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    {W : State} {a b c d : Pred}
    (hRel :
      predicateVocabularyIntensionalPairSubsetRel
        (Base := Base) (Const := Const) M σ decode W a b c d) :
    predicateVocabularyPairOrderRankScore
        (Base := Base) (Const := Const) M σ decode a b ≤
      predicateVocabularyPairOrderRankScore
        (Base := Base) (Const := Const) M σ decode c d := by
  exact add_le_add
    (predicateVocabularyIntentCard_mono_of_intensionalInherits
      (Base := Base) (Const := Const) M σ decode hRel.1)
    (predicateVocabularyIntentDeficit_mono_of_reverse_intensionalInherits
      (Base := Base) (Const := Const) M σ decode hRel.2)

/-- Weighted order-rank scores preserve the HO predicate-pair subset order
when both channels receive nonnegative weights. This theorem is the precise
place where Chapter-12 score design is allowed to vary without leaving the
existing ASSOC/PAT subset-semantics interface. -/
theorem predicateVocabularyWeightedPairOrderRankScore_mono
    {State : Type}
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    {leftWeight rightWeight : ℝ}
    (hLeftWeight : 0 ≤ leftWeight)
    (hRightWeight : 0 ≤ rightWeight)
    {W : State} {a b c d : Pred}
    (hRel :
      predicateVocabularyIntensionalPairSubsetRel
        (Base := Base) (Const := Const) M σ decode W a b c d) :
    predicateVocabularyWeightedPairOrderRankScore
        (Base := Base) (Const := Const) M σ decode leftWeight rightWeight a b ≤
      predicateVocabularyWeightedPairOrderRankScore
        (Base := Base) (Const := Const) M σ decode leftWeight rightWeight c d := by
  unfold predicateVocabularyWeightedPairOrderRankScore
  exact add_le_add
    (mul_le_mul_of_nonneg_left
      (predicateVocabularyIntentCard_mono_of_intensionalInherits
        (Base := Base) (Const := Const) M σ decode hRel.1)
      hLeftWeight)
    (mul_le_mul_of_nonneg_left
      (predicateVocabularyIntentDeficit_mono_of_reverse_intensionalInherits
        (Base := Base) (Const := Const) M σ decode hRel.2)
      hRightWeight)

/-- Unit weights recover the original unweighted finite-vocabulary order-rank
score. This pins the richer score family to the already-tested score surface
instead of creating a parallel ASSOC/PAT channel. -/
theorem predicateVocabularyWeightedPairOrderRankScore_one_one
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (a b : Pred) :
    predicateVocabularyWeightedPairOrderRankScore
        (Base := Base) (Const := Const) M σ decode 1 1 a b =
      predicateVocabularyPairOrderRankScore
        (Base := Base) (Const := Const) M σ decode a b := by
  simp [predicateVocabularyWeightedPairOrderRankScore,
    predicateVocabularyPairOrderRankScore]

/-- If both weights are at least one, the weighted score dominates the original
order-rank score pointwise. Thus the richer score family can be used as a
strictly stronger ASSOC/PAT scoring witness without losing the old signal. -/
theorem predicateVocabularyPairOrderRankScore_le_weightedPairOrderRankScore
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type}
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    {leftWeight rightWeight : ℝ}
    (hLeftWeight : 1 ≤ leftWeight)
    (hRightWeight : 1 ≤ rightWeight)
    (a b : Pred) :
    predicateVocabularyPairOrderRankScore
        (Base := Base) (Const := Const) M σ decode a b ≤
      predicateVocabularyWeightedPairOrderRankScore
        (Base := Base) (Const := Const) M σ decode leftWeight rightWeight a b := by
  have hCardNonneg :
      0 ≤ predicateVocabularyIntentCard
        (Base := Base) (Const := Const) M σ decode a :=
    predicateVocabularyIntentCard_nonneg (Base := Base) (Const := Const) M σ decode a
  have hDeficitNonneg :
      0 ≤ predicateVocabularyIntentDeficit
        (Base := Base) (Const := Const) M σ decode b :=
    predicateVocabularyIntentDeficit_nonneg (Base := Base) (Const := Const) M σ decode b
  have hCardLe :
      predicateVocabularyIntentCard
          (Base := Base) (Const := Const) M σ decode a ≤
        leftWeight *
          predicateVocabularyIntentCard
            (Base := Base) (Const := Const) M σ decode a := by
    simpa using mul_le_mul_of_nonneg_right hLeftWeight hCardNonneg
  have hDeficitLe :
      predicateVocabularyIntentDeficit
          (Base := Base) (Const := Const) M σ decode b ≤
        rightWeight *
          predicateVocabularyIntentDeficit
            (Base := Base) (Const := Const) M σ decode b := by
    simpa using mul_le_mul_of_nonneg_right hRightWeight hDeficitNonneg
  unfold predicateVocabularyPairOrderRankScore predicateVocabularyWeightedPairOrderRankScore
  exact add_le_add hCardLe hDeficitLe

section Evidence

variable {State Pred PairQuery : Type}
variable [EvidenceType State]
variable [WorldModelSigma State InheritanceSort (InheritanceQueryFamily PairQuery)]

/-- A concrete ASSOC subset-semantics package when the ASSOC score channel is the
finite-vocabulary predicate-pair order-rank score. -/
theorem assocSubsetSemantics_of_predicateVocabularyPairOrderRankScore
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (pairEnc : InheritanceQueryBuilder Pred PairQuery)
    (model : InheritanceQueryBuilder.IntensionalScoreModel
      (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
    (hScore : ∀ (W : State) (a b : Pred),
      model.assocScore W a b =
        predicateVocabularyPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode a b) :
    InheritanceQueryBuilder.AssocSubsetSemantics
      (State := State) (Atom := Pred) (Query := PairQuery)
      pairEnc model
      (predicateVocabularyIntensionalPairSubsetRel
        (Base := Base) (Const := Const) M σ decode) := by
  intro W a b c d hRel
  rw [hScore W a b, hScore W c d]
  exact
    predicateVocabularyPairOrderRankScore_mono
      (Base := Base) (Const := Const) M σ decode hRel

/-- A concrete PAT subset-semantics package when the PAT score channel is the
finite-vocabulary predicate-pair order-rank score. -/
theorem patSubsetSemantics_of_predicateVocabularyPairOrderRankScore
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (pairEnc : InheritanceQueryBuilder Pred PairQuery)
    (model : InheritanceQueryBuilder.IntensionalScoreModel
      (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
    (hScore : ∀ (W : State) (a b : Pred),
      model.patScore W a b =
        predicateVocabularyPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode a b) :
    InheritanceQueryBuilder.PATSubsetSemantics
      (State := State) (Atom := Pred) (Query := PairQuery)
      pairEnc model
      (predicateVocabularyIntensionalPairSubsetRel
        (Base := Base) (Const := Const) M σ decode) := by
  intro W a b c d hRel
  rw [hScore W a b, hScore W c d]
  exact
    predicateVocabularyPairOrderRankScore_mono
      (Base := Base) (Const := Const) M σ decode hRel

/-- Concrete two-channel ASSOC/PAT subset semantics for finite HO predicate
vocabularies when both score channels are the same predicate-pair order-rank
score. This is the Chapter-12 systems-facing package: ASSOC and PAT reuse the
same finite predicate-intent order instead of becoming separate HO semantics. -/
theorem assocPatSubsetSemantics_of_predicateVocabularyPairOrderRankScore
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (pairEnc : InheritanceQueryBuilder Pred PairQuery)
    (model : InheritanceQueryBuilder.IntensionalScoreModel
      (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
    (hAssocScore : ∀ (W : State) (a b : Pred),
      model.assocScore W a b =
        predicateVocabularyPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode a b)
    (hPatScore : ∀ (W : State) (a b : Pred),
      model.patScore W a b =
        predicateVocabularyPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode a b) :
    InheritanceQueryBuilder.AssocSubsetSemantics
        (State := State) (Atom := Pred) (Query := PairQuery)
        pairEnc model
        (predicateVocabularyIntensionalPairSubsetRel
          (Base := Base) (Const := Const) M σ decode) ∧
      InheritanceQueryBuilder.PATSubsetSemantics
        (State := State) (Atom := Pred) (Query := PairQuery)
        pairEnc model
        (predicateVocabularyIntensionalPairSubsetRel
          (Base := Base) (Const := Const) M σ decode) := by
  exact
    ⟨assocSubsetSemantics_of_predicateVocabularyPairOrderRankScore
        (Base := Base) (Const := Const) M σ decode pairEnc model hAssocScore,
      patSubsetSemantics_of_predicateVocabularyPairOrderRankScore
        (Base := Base) (Const := Const) M σ decode pairEnc model hPatScore⟩

/-- Concrete ASSOC subset semantics for any nonnegatively weighted finite
HO predicate-vocabulary order-rank score. -/
theorem assocSubsetSemantics_of_predicateVocabularyWeightedPairOrderRankScore
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (pairEnc : InheritanceQueryBuilder Pred PairQuery)
    (model : InheritanceQueryBuilder.IntensionalScoreModel
      (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
    {leftWeight rightWeight : ℝ}
    (hLeftWeight : 0 ≤ leftWeight)
    (hRightWeight : 0 ≤ rightWeight)
    (hScore : ∀ (W : State) (a b : Pred),
      model.assocScore W a b =
        predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode leftWeight rightWeight a b) :
    InheritanceQueryBuilder.AssocSubsetSemantics
      (State := State) (Atom := Pred) (Query := PairQuery)
      pairEnc model
      (predicateVocabularyIntensionalPairSubsetRel
        (Base := Base) (Const := Const) M σ decode) := by
  intro W a b c d hRel
  rw [hScore W a b, hScore W c d]
  exact
    predicateVocabularyWeightedPairOrderRankScore_mono
      (Base := Base) (Const := Const) M σ decode
      hLeftWeight hRightWeight hRel

/-- Concrete PAT subset semantics for any nonnegatively weighted finite
HO predicate-vocabulary order-rank score. -/
theorem patSubsetSemantics_of_predicateVocabularyWeightedPairOrderRankScore
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (pairEnc : InheritanceQueryBuilder Pred PairQuery)
    (model : InheritanceQueryBuilder.IntensionalScoreModel
      (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
    {leftWeight rightWeight : ℝ}
    (hLeftWeight : 0 ≤ leftWeight)
    (hRightWeight : 0 ≤ rightWeight)
    (hScore : ∀ (W : State) (a b : Pred),
      model.patScore W a b =
        predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode leftWeight rightWeight a b) :
    InheritanceQueryBuilder.PATSubsetSemantics
      (State := State) (Atom := Pred) (Query := PairQuery)
      pairEnc model
      (predicateVocabularyIntensionalPairSubsetRel
        (Base := Base) (Const := Const) M σ decode) := by
  intro W a b c d hRel
  rw [hScore W a b, hScore W c d]
  exact
    predicateVocabularyWeightedPairOrderRankScore_mono
      (Base := Base) (Const := Const) M σ decode
      hLeftWeight hRightWeight hRel

/-- Two-channel ASSOC/PAT subset semantics for nonnegatively weighted
finite-vocabulary predicate-pair scores. The two channels may use distinct
weight pairs; both remain consumers of the same HO predicate-pair subset
relation. -/
theorem assocPatSubsetSemantics_of_predicateVocabularyWeightedPairOrderRankScore
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (pairEnc : InheritanceQueryBuilder Pred PairQuery)
    (model : InheritanceQueryBuilder.IntensionalScoreModel
      (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
    {assocLeftWeight assocRightWeight patLeftWeight patRightWeight : ℝ}
    (hAssocLeftWeight : 0 ≤ assocLeftWeight)
    (hAssocRightWeight : 0 ≤ assocRightWeight)
    (hPatLeftWeight : 0 ≤ patLeftWeight)
    (hPatRightWeight : 0 ≤ patRightWeight)
    (hAssocScore : ∀ (W : State) (a b : Pred),
      model.assocScore W a b =
        predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          assocLeftWeight assocRightWeight a b)
    (hPatScore : ∀ (W : State) (a b : Pred),
      model.patScore W a b =
        predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          patLeftWeight patRightWeight a b) :
    InheritanceQueryBuilder.AssocSubsetSemantics
        (State := State) (Atom := Pred) (Query := PairQuery)
        pairEnc model
        (predicateVocabularyIntensionalPairSubsetRel
          (Base := Base) (Const := Const) M σ decode) ∧
      InheritanceQueryBuilder.PATSubsetSemantics
        (State := State) (Atom := Pred) (Query := PairQuery)
        pairEnc model
        (predicateVocabularyIntensionalPairSubsetRel
          (Base := Base) (Const := Const) M σ decode) := by
  exact
    ⟨assocSubsetSemantics_of_predicateVocabularyWeightedPairOrderRankScore
        (Base := Base) (Const := Const) M σ decode pairEnc model
        hAssocLeftWeight hAssocRightWeight hAssocScore,
      patSubsetSemantics_of_predicateVocabularyWeightedPairOrderRankScore
        (Base := Base) (Const := Const) M σ decode pairEnc model
        hPatLeftWeight hPatRightWeight hPatScore⟩

/-- ASSOC evidence monotonicity instantiated at the finite HO
predicate-vocabulary pure-intensional pair relation. -/
theorem assocEvidence_mono_of_predicateVocabularyIntensionalSubsetSemantics
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (pairEnc : InheritanceQueryBuilder Pred PairQuery)
    (model : InheritanceQueryBuilder.IntensionalScoreModel
      (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
    (hSubset :
      InheritanceQueryBuilder.AssocSubsetSemantics
        (State := State) (Atom := Pred) (Query := PairQuery)
        pairEnc model
        (predicateVocabularyIntensionalPairSubsetRel
          (Base := Base) (Const := Const) M σ decode))
    {W : State} {a b c d : Pred}
    (hRel :
      predicateVocabularyIntensionalPairSubsetRel
        (Base := Base) (Const := Const) M σ decode W a b c d) :
    InheritanceQueryBuilder.intensionalAssocEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b ≤
      InheritanceQueryBuilder.intensionalAssocEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d := by
  exact
    InheritanceQueryBuilder.assocEvidence_mono_of_subsetSemantics
      (State := State) (Atom := Pred) (Query := PairQuery)
      pairEnc model
      (subsetRel :=
        predicateVocabularyIntensionalPairSubsetRel
          (Base := Base) (Const := Const) M σ decode)
      hSubset hRel

/-- PAT evidence monotonicity instantiated at the finite HO
predicate-vocabulary pure-intensional pair relation. -/
theorem patEvidence_mono_of_predicateVocabularyIntensionalSubsetSemantics
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (pairEnc : InheritanceQueryBuilder Pred PairQuery)
    (model : InheritanceQueryBuilder.IntensionalScoreModel
      (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
    (hSubset :
      InheritanceQueryBuilder.PATSubsetSemantics
        (State := State) (Atom := Pred) (Query := PairQuery)
        pairEnc model
        (predicateVocabularyIntensionalPairSubsetRel
          (Base := Base) (Const := Const) M σ decode))
    {W : State} {a b c d : Pred}
    (hRel :
      predicateVocabularyIntensionalPairSubsetRel
        (Base := Base) (Const := Const) M σ decode W a b c d) :
    InheritanceQueryBuilder.intensionalPATEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b ≤
      InheritanceQueryBuilder.intensionalPATEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d := by
  exact
    InheritanceQueryBuilder.patEvidence_mono_of_subsetSemantics
      (State := State) (Atom := Pred) (Query := PairQuery)
      pairEnc model
      (subsetRel :=
        predicateVocabularyIntensionalPairSubsetRel
          (Base := Base) (Const := Const) M σ decode)
      hSubset hRel

/-- ASSOC evidence is monotone under same-intent replacement of both endpoints,
provided the ASSOC score model is monotone for the induced HO predicate
intensional pair relation. -/
theorem assocEvidence_mono_of_predicateVocabularySameIntent
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (pairEnc : InheritanceQueryBuilder Pred PairQuery)
    (model : InheritanceQueryBuilder.IntensionalScoreModel
      (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
    (hSubset :
      InheritanceQueryBuilder.AssocSubsetSemantics
        (State := State) (Atom := Pred) (Query := PairQuery)
        pairEnc model
        (predicateVocabularyIntensionalPairSubsetRel
          (Base := Base) (Const := Const) M σ decode))
    {W : State} {a b c d : Pred}
    (hLeft :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode a c)
    (hRight :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode b d) :
    InheritanceQueryBuilder.intensionalAssocEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b ≤
      InheritanceQueryBuilder.intensionalAssocEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d := by
  exact
    assocEvidence_mono_of_predicateVocabularyIntensionalSubsetSemantics
      (Base := Base) (Const := Const) M σ decode pairEnc model hSubset
      (predicateVocabularyIntensionalPairSubsetRel_of_sameIntent
        (Base := Base) (Const := Const) M σ decode W hLeft hRight)

/-- ASSOC evidence monotonicity for a concrete finite-vocabulary order-rank
ASSOC score channel. -/
theorem assocEvidence_mono_of_predicateVocabularyPairOrderRankScore
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (pairEnc : InheritanceQueryBuilder Pred PairQuery)
    (model : InheritanceQueryBuilder.IntensionalScoreModel
      (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
    (hScore : ∀ (W : State) (a b : Pred),
      model.assocScore W a b =
        predicateVocabularyPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode a b)
    {W : State} {a b c d : Pred}
    (hRel :
      predicateVocabularyIntensionalPairSubsetRel
        (Base := Base) (Const := Const) M σ decode W a b c d) :
    InheritanceQueryBuilder.intensionalAssocEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b ≤
      InheritanceQueryBuilder.intensionalAssocEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d := by
  exact
    assocEvidence_mono_of_predicateVocabularyIntensionalSubsetSemantics
      (Base := Base) (Const := Const) M σ decode pairEnc model
      (assocSubsetSemantics_of_predicateVocabularyPairOrderRankScore
        (Base := Base) (Const := Const) M σ decode pairEnc model hScore)
      hRel

/-- ASSOC evidence is invariant under same-intent replacement of both endpoints
when the ASSOC score model is monotone for the induced HO predicate
intensional pair relation. -/
theorem assocEvidence_eq_of_predicateVocabularySameIntent
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (pairEnc : InheritanceQueryBuilder Pred PairQuery)
    (model : InheritanceQueryBuilder.IntensionalScoreModel
      (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
    (hSubset :
      InheritanceQueryBuilder.AssocSubsetSemantics
        (State := State) (Atom := Pred) (Query := PairQuery)
        pairEnc model
        (predicateVocabularyIntensionalPairSubsetRel
          (Base := Base) (Const := Const) M σ decode))
    {W : State} {a b c d : Pred}
    (hLeft :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode a c)
    (hRight :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode b d) :
    InheritanceQueryBuilder.intensionalAssocEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
      InheritanceQueryBuilder.intensionalAssocEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d := by
  have hLeftSymm :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode c a := by
    unfold Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent at hLeft ⊢
    exact hLeft.symm
  have hRightSymm :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode d b := by
    unfold Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent at hRight ⊢
    exact hRight.symm
  exact le_antisymm
    (assocEvidence_mono_of_predicateVocabularySameIntent
      (Base := Base) (Const := Const) M σ decode pairEnc model hSubset hLeft hRight)
    (assocEvidence_mono_of_predicateVocabularySameIntent
      (Base := Base) (Const := Const) M σ decode pairEnc model hSubset hLeftSymm hRightSymm)

/-- ASSOC evidence invariance under same-intent replacement for a concrete
finite-vocabulary order-rank ASSOC score channel. -/
theorem assocEvidence_eq_of_predicateVocabularyPairOrderRankScore_sameIntent
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (pairEnc : InheritanceQueryBuilder Pred PairQuery)
    (model : InheritanceQueryBuilder.IntensionalScoreModel
      (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
    (hScore : ∀ (W : State) (a b : Pred),
      model.assocScore W a b =
        predicateVocabularyPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode a b)
    {W : State} {a b c d : Pred}
    (hLeft :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode a c)
    (hRight :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode b d) :
    InheritanceQueryBuilder.intensionalAssocEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
      InheritanceQueryBuilder.intensionalAssocEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d := by
  exact
    assocEvidence_eq_of_predicateVocabularySameIntent
      (Base := Base) (Const := Const) M σ decode pairEnc model
      (assocSubsetSemantics_of_predicateVocabularyPairOrderRankScore
        (Base := Base) (Const := Const) M σ decode pairEnc model hScore)
      hLeft hRight

/-- PAT evidence is monotone under same-intent replacement of both endpoints,
provided the PAT score model is monotone for the induced HO predicate
intensional pair relation. -/
theorem patEvidence_mono_of_predicateVocabularySameIntent
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (pairEnc : InheritanceQueryBuilder Pred PairQuery)
    (model : InheritanceQueryBuilder.IntensionalScoreModel
      (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
    (hSubset :
      InheritanceQueryBuilder.PATSubsetSemantics
        (State := State) (Atom := Pred) (Query := PairQuery)
        pairEnc model
        (predicateVocabularyIntensionalPairSubsetRel
          (Base := Base) (Const := Const) M σ decode))
    {W : State} {a b c d : Pred}
    (hLeft :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode a c)
    (hRight :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode b d) :
    InheritanceQueryBuilder.intensionalPATEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b ≤
      InheritanceQueryBuilder.intensionalPATEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d := by
  exact
    patEvidence_mono_of_predicateVocabularyIntensionalSubsetSemantics
      (Base := Base) (Const := Const) M σ decode pairEnc model hSubset
      (predicateVocabularyIntensionalPairSubsetRel_of_sameIntent
        (Base := Base) (Const := Const) M σ decode W hLeft hRight)

/-- PAT evidence monotonicity for a concrete finite-vocabulary order-rank PAT
score channel. -/
theorem patEvidence_mono_of_predicateVocabularyPairOrderRankScore
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (pairEnc : InheritanceQueryBuilder Pred PairQuery)
    (model : InheritanceQueryBuilder.IntensionalScoreModel
      (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
    (hScore : ∀ (W : State) (a b : Pred),
      model.patScore W a b =
        predicateVocabularyPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode a b)
    {W : State} {a b c d : Pred}
    (hRel :
      predicateVocabularyIntensionalPairSubsetRel
        (Base := Base) (Const := Const) M σ decode W a b c d) :
    InheritanceQueryBuilder.intensionalPATEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b ≤
      InheritanceQueryBuilder.intensionalPATEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d := by
  exact
    patEvidence_mono_of_predicateVocabularyIntensionalSubsetSemantics
      (Base := Base) (Const := Const) M σ decode pairEnc model
      (patSubsetSemantics_of_predicateVocabularyPairOrderRankScore
        (Base := Base) (Const := Const) M σ decode pairEnc model hScore)
      hRel

/-- PAT evidence is invariant under same-intent replacement of both endpoints
when the PAT score model is monotone for the induced HO predicate intensional
pair relation. -/
theorem patEvidence_eq_of_predicateVocabularySameIntent
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (pairEnc : InheritanceQueryBuilder Pred PairQuery)
    (model : InheritanceQueryBuilder.IntensionalScoreModel
      (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
    (hSubset :
      InheritanceQueryBuilder.PATSubsetSemantics
        (State := State) (Atom := Pred) (Query := PairQuery)
        pairEnc model
        (predicateVocabularyIntensionalPairSubsetRel
          (Base := Base) (Const := Const) M σ decode))
    {W : State} {a b c d : Pred}
    (hLeft :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode a c)
    (hRight :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode b d) :
    InheritanceQueryBuilder.intensionalPATEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
      InheritanceQueryBuilder.intensionalPATEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d := by
  have hLeftSymm :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode c a := by
    unfold Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent at hLeft ⊢
    exact hLeft.symm
  have hRightSymm :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode d b := by
    unfold Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent at hRight ⊢
    exact hRight.symm
  exact le_antisymm
    (patEvidence_mono_of_predicateVocabularySameIntent
      (Base := Base) (Const := Const) M σ decode pairEnc model hSubset hLeft hRight)
    (patEvidence_mono_of_predicateVocabularySameIntent
      (Base := Base) (Const := Const) M σ decode pairEnc model hSubset hLeftSymm hRightSymm)

/-- PAT evidence invariance under same-intent replacement for a concrete
finite-vocabulary order-rank PAT score channel. -/
theorem patEvidence_eq_of_predicateVocabularyPairOrderRankScore_sameIntent
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (pairEnc : InheritanceQueryBuilder Pred PairQuery)
    (model : InheritanceQueryBuilder.IntensionalScoreModel
      (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
    (hScore : ∀ (W : State) (a b : Pred),
      model.patScore W a b =
        predicateVocabularyPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode a b)
    {W : State} {a b c d : Pred}
    (hLeft :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode a c)
    (hRight :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode b d) :
    InheritanceQueryBuilder.intensionalPATEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
      InheritanceQueryBuilder.intensionalPATEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d := by
  exact
    patEvidence_eq_of_predicateVocabularySameIntent
      (Base := Base) (Const := Const) M σ decode pairEnc model
      (patSubsetSemantics_of_predicateVocabularyPairOrderRankScore
        (Base := Base) (Const := Const) M σ decode pairEnc model hScore)
      hLeft hRight

/-- ASSOC and PAT evidence are jointly invariant under same-intent replacement
when both concrete score channels are the finite predicate-pair order-rank
score. This is the two-channel HO predicate-intension consumer that should be
used before adding any mixed-channel policy on top. -/
theorem assocPatEvidence_eq_of_predicateVocabularyPairOrderRankScore_sameIntent
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (pairEnc : InheritanceQueryBuilder Pred PairQuery)
    (model : InheritanceQueryBuilder.IntensionalScoreModel
      (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
    (hAssocScore : ∀ (W : State) (a b : Pred),
      model.assocScore W a b =
        predicateVocabularyPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode a b)
    (hPatScore : ∀ (W : State) (a b : Pred),
      model.patScore W a b =
        predicateVocabularyPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode a b)
    {W : State} {a b c d : Pred}
    (hLeft :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode a c)
    (hRight :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode b d) :
    InheritanceQueryBuilder.intensionalAssocEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
        InheritanceQueryBuilder.intensionalAssocEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d ∧
      InheritanceQueryBuilder.intensionalPATEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
        InheritanceQueryBuilder.intensionalPATEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d := by
  exact
    ⟨assocEvidence_eq_of_predicateVocabularyPairOrderRankScore_sameIntent
        (Base := Base) (Const := Const) M σ decode pairEnc model hAssocScore hLeft hRight,
      patEvidence_eq_of_predicateVocabularyPairOrderRankScore_sameIntent
        (Base := Base) (Const := Const) M σ decode pairEnc model hPatScore hLeft hRight⟩

/-- Mixed evidence is preserved whenever the three channels consumed by a
strong ASSOC+PAT score correspondence are preserved separately.

This generic helper keeps the higher-order PAT/ASSOC bridges from re-proving
the mixed-channel algebra every time a new score family is introduced. -/
theorem mixedEvidence_eq_of_extensional_assoc_pat_channel_eq
    (pairEnc : InheritanceQueryBuilder Pred PairQuery)
    (model : InheritanceQueryBuilder.IntensionalScoreModel
      (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
    (combine :
      Mettapedia.Logic.EvidenceQuantale.BinaryEvidence →
        Mettapedia.Logic.EvidenceQuantale.BinaryEvidence →
          Mettapedia.Logic.EvidenceQuantale.BinaryEvidence →
            Mettapedia.Logic.EvidenceQuantale.BinaryEvidence)
    (hMixed :
      InheritanceQueryBuilder.MixedAssocPatScoreCorrespondence
        (State := State) (Atom := Pred) (Query := PairQuery)
        pairEnc combine model.assocScore model.patScore model.scoreToEvidence)
    {W : State} {a b c d : Pred}
    (hExt :
      InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
        InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d)
    (hAssoc :
      InheritanceQueryBuilder.intensionalAssocEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
        InheritanceQueryBuilder.intensionalAssocEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d)
    (hPat :
      InheritanceQueryBuilder.intensionalPATEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
        InheritanceQueryBuilder.intensionalPATEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d) :
    InheritanceQueryBuilder.mixedEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
      InheritanceQueryBuilder.mixedEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d := by
  have hAssocLift :
      model.scoreToEvidence (model.assocScore W a b) =
        model.scoreToEvidence (model.assocScore W c d) := by
    calc
      model.scoreToEvidence (model.assocScore W a b)
          = InheritanceQueryBuilder.intensionalAssocEvidence
              (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b :=
        (model.assoc_sound W a b).symm
      _ = InheritanceQueryBuilder.intensionalAssocEvidence
            (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d :=
        hAssoc
      _ = model.scoreToEvidence (model.assocScore W c d) :=
        model.assoc_sound W c d
  have hPatLift :
      model.scoreToEvidence (model.patScore W a b) =
        model.scoreToEvidence (model.patScore W c d) := by
    calc
      model.scoreToEvidence (model.patScore W a b)
          = InheritanceQueryBuilder.intensionalPATEvidence
              (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b :=
        (model.pat_sound W a b).symm
      _ = InheritanceQueryBuilder.intensionalPATEvidence
            (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d :=
        hPat
      _ = model.scoreToEvidence (model.patScore W c d) :=
        model.pat_sound W c d
  calc
    InheritanceQueryBuilder.mixedEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b
        = combine
            (InheritanceQueryBuilder.extensionalEvidence
              (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b)
            (model.scoreToEvidence (model.assocScore W a b))
            (model.scoreToEvidence (model.patScore W a b)) :=
      hMixed W a b
    _ = combine
          (InheritanceQueryBuilder.extensionalEvidence
            (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d)
          (model.scoreToEvidence (model.assocScore W c d))
          (model.scoreToEvidence (model.patScore W c d)) := by
      rw [hExt, hAssocLift, hPatLift]
    _ = InheritanceQueryBuilder.mixedEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d :=
      (hMixed W c d).symm

/-- Semantic-package version of
`mixedEvidence_eq_of_extensional_assoc_pat_channel_eq`: a strong ASSOC+PAT
model already carries the mixed-channel score correspondence. -/
theorem mixedEvidence_eq_of_assocPatSemanticModel_extensional_assoc_pat_channel_eq
    (pairEnc : InheritanceQueryBuilder Pred PairQuery)
    (m : InheritanceQueryBuilder.AssocPatSemanticModel
      (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
    {W : State} {a b c d : Pred}
    (hExt :
      InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
        InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d)
    (hAssoc :
      InheritanceQueryBuilder.intensionalAssocEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
        InheritanceQueryBuilder.intensionalAssocEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d)
    (hPat :
      InheritanceQueryBuilder.intensionalPATEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
        InheritanceQueryBuilder.intensionalPATEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d) :
    InheritanceQueryBuilder.mixedEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
      InheritanceQueryBuilder.mixedEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d :=
  mixedEvidence_eq_of_extensional_assoc_pat_channel_eq
    (State := State) (Pred := Pred) (PairQuery := PairQuery)
    pairEnc m.scoreModel m.combine m.mixed_sound hExt hAssoc hPat

/-- ASSOC evidence invariance under same-intent replacement for a weighted
finite-vocabulary order-rank ASSOC score channel. -/
theorem assocEvidence_eq_of_predicateVocabularyWeightedPairOrderRankScore_sameIntent
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (pairEnc : InheritanceQueryBuilder Pred PairQuery)
    (model : InheritanceQueryBuilder.IntensionalScoreModel
      (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
    {leftWeight rightWeight : ℝ}
    (hLeftWeight : 0 ≤ leftWeight)
    (hRightWeight : 0 ≤ rightWeight)
    (hScore : ∀ (W : State) (a b : Pred),
      model.assocScore W a b =
        predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode leftWeight rightWeight a b)
    {W : State} {a b c d : Pred}
    (hLeft :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode a c)
    (hRight :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode b d) :
    InheritanceQueryBuilder.intensionalAssocEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
      InheritanceQueryBuilder.intensionalAssocEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d := by
  exact
    assocEvidence_eq_of_predicateVocabularySameIntent
      (Base := Base) (Const := Const) M σ decode pairEnc model
      (assocSubsetSemantics_of_predicateVocabularyWeightedPairOrderRankScore
        (Base := Base) (Const := Const) M σ decode pairEnc model
        hLeftWeight hRightWeight hScore)
      hLeft hRight

/-- PAT evidence invariance under same-intent replacement for a weighted
finite-vocabulary order-rank PAT score channel. -/
theorem patEvidence_eq_of_predicateVocabularyWeightedPairOrderRankScore_sameIntent
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (pairEnc : InheritanceQueryBuilder Pred PairQuery)
    (model : InheritanceQueryBuilder.IntensionalScoreModel
      (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
    {leftWeight rightWeight : ℝ}
    (hLeftWeight : 0 ≤ leftWeight)
    (hRightWeight : 0 ≤ rightWeight)
    (hScore : ∀ (W : State) (a b : Pred),
      model.patScore W a b =
        predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode leftWeight rightWeight a b)
    {W : State} {a b c d : Pred}
    (hLeft :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode a c)
    (hRight :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode b d) :
    InheritanceQueryBuilder.intensionalPATEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
      InheritanceQueryBuilder.intensionalPATEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d := by
  exact
    patEvidence_eq_of_predicateVocabularySameIntent
      (Base := Base) (Const := Const) M σ decode pairEnc model
      (patSubsetSemantics_of_predicateVocabularyWeightedPairOrderRankScore
        (Base := Base) (Const := Const) M σ decode pairEnc model
        hLeftWeight hRightWeight hScore)
      hLeft hRight

/-- ASSOC and PAT evidence are jointly invariant under same-intent replacement
when both score channels are weighted finite predicate-pair order-rank scores. -/
theorem assocPatEvidence_eq_of_predicateVocabularyWeightedPairOrderRankScore_sameIntent
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (pairEnc : InheritanceQueryBuilder Pred PairQuery)
    (model : InheritanceQueryBuilder.IntensionalScoreModel
      (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
    {assocLeftWeight assocRightWeight patLeftWeight patRightWeight : ℝ}
    (hAssocLeftWeight : 0 ≤ assocLeftWeight)
    (hAssocRightWeight : 0 ≤ assocRightWeight)
    (hPatLeftWeight : 0 ≤ patLeftWeight)
    (hPatRightWeight : 0 ≤ patRightWeight)
    (hAssocScore : ∀ (W : State) (a b : Pred),
      model.assocScore W a b =
        predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          assocLeftWeight assocRightWeight a b)
    (hPatScore : ∀ (W : State) (a b : Pred),
      model.patScore W a b =
        predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          patLeftWeight patRightWeight a b)
    {W : State} {a b c d : Pred}
    (hLeft :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode a c)
    (hRight :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode b d) :
    InheritanceQueryBuilder.intensionalAssocEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
        InheritanceQueryBuilder.intensionalAssocEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d ∧
      InheritanceQueryBuilder.intensionalPATEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
        InheritanceQueryBuilder.intensionalPATEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d := by
  exact
    ⟨assocEvidence_eq_of_predicateVocabularyWeightedPairOrderRankScore_sameIntent
        (Base := Base) (Const := Const) M σ decode pairEnc model
        hAssocLeftWeight hAssocRightWeight hAssocScore hLeft hRight,
      patEvidence_eq_of_predicateVocabularyWeightedPairOrderRankScore_sameIntent
        (Base := Base) (Const := Const) M σ decode pairEnc model
        hPatLeftWeight hPatRightWeight hPatScore hLeft hRight⟩

/-- Mixed evidence preservation for weighted finite-vocabulary ASSOC/PAT score
channels.

As in the unweighted theorem, same intent controls only the intensional
channels; preservation of the extensional channel remains an explicit
hypothesis. -/
theorem mixedEvidence_eq_of_predicateVocabularyWeightedPairOrderRankScore_sameIntent
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (pairEnc : InheritanceQueryBuilder Pred PairQuery)
    (model : InheritanceQueryBuilder.IntensionalScoreModel
      (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
    (combine :
      Mettapedia.Logic.EvidenceQuantale.BinaryEvidence →
        Mettapedia.Logic.EvidenceQuantale.BinaryEvidence →
          Mettapedia.Logic.EvidenceQuantale.BinaryEvidence →
            Mettapedia.Logic.EvidenceQuantale.BinaryEvidence)
    (hMixed :
      InheritanceQueryBuilder.MixedAssocPatScoreCorrespondence
        (State := State) (Atom := Pred) (Query := PairQuery)
        pairEnc combine model.assocScore model.patScore model.scoreToEvidence)
    {assocLeftWeight assocRightWeight patLeftWeight patRightWeight : ℝ}
    (hAssocLeftWeight : 0 ≤ assocLeftWeight)
    (hAssocRightWeight : 0 ≤ assocRightWeight)
    (hPatLeftWeight : 0 ≤ patLeftWeight)
    (hPatRightWeight : 0 ≤ patRightWeight)
    (hAssocScore : ∀ (W : State) (a b : Pred),
      model.assocScore W a b =
        predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          assocLeftWeight assocRightWeight a b)
    (hPatScore : ∀ (W : State) (a b : Pred),
      model.patScore W a b =
        predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          patLeftWeight patRightWeight a b)
    {W : State} {a b c d : Pred}
    (hExt :
      InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
        InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d)
    (hLeft :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode a c)
    (hRight :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode b d) :
    InheritanceQueryBuilder.mixedEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
      InheritanceQueryBuilder.mixedEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d := by
  have hAssocPat :
      InheritanceQueryBuilder.intensionalAssocEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
          InheritanceQueryBuilder.intensionalAssocEvidence
            (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d ∧
        InheritanceQueryBuilder.intensionalPATEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
          InheritanceQueryBuilder.intensionalPATEvidence
            (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d :=
    assocPatEvidence_eq_of_predicateVocabularyWeightedPairOrderRankScore_sameIntent
      (Base := Base) (Const := Const) M σ decode pairEnc model
      hAssocLeftWeight hAssocRightWeight hPatLeftWeight hPatRightWeight
      hAssocScore hPatScore hLeft hRight
  exact
    mixedEvidence_eq_of_extensional_assoc_pat_channel_eq
      (State := State) (Pred := Pred) (PairQuery := PairQuery)
      pairEnc model combine hMixed hExt hAssocPat.1 hAssocPat.2

/-- Semantic-package version of weighted mixed evidence preservation. This is
the systems-facing bridge: a strong `AssocPatSemanticModel` whose ASSOC and PAT
score channels are weighted predicate-vocabulary scores can consume the
same-intent theorem directly. -/
theorem mixedEvidence_eq_of_assocPatSemanticModel_predicateVocabularyWeightedPairOrderRankScore_sameIntent
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (pairEnc : InheritanceQueryBuilder Pred PairQuery)
    (m : InheritanceQueryBuilder.AssocPatSemanticModel
      (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
    {assocLeftWeight assocRightWeight patLeftWeight patRightWeight : ℝ}
    (hAssocLeftWeight : 0 ≤ assocLeftWeight)
    (hAssocRightWeight : 0 ≤ assocRightWeight)
    (hPatLeftWeight : 0 ≤ patLeftWeight)
    (hPatRightWeight : 0 ≤ patRightWeight)
    (hAssocScore : ∀ (W : State) (a b : Pred),
      m.scoreModel.assocScore W a b =
        predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          assocLeftWeight assocRightWeight a b)
    (hPatScore : ∀ (W : State) (a b : Pred),
      m.scoreModel.patScore W a b =
        predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          patLeftWeight patRightWeight a b)
    {W : State} {a b c d : Pred}
    (hExt :
      InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
        InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d)
    (hLeft :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode a c)
    (hRight :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode b d) :
    InheritanceQueryBuilder.mixedEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
      InheritanceQueryBuilder.mixedEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d :=
  mixedEvidence_eq_of_predicateVocabularyWeightedPairOrderRankScore_sameIntent
    (Base := Base) (Const := Const) (State := State) (Pred := Pred) (PairQuery := PairQuery)
    M σ decode pairEnc m.scoreModel m.combine m.mixed_sound
    hAssocLeftWeight hAssocRightWeight hPatLeftWeight hPatRightWeight
    hAssocScore hPatScore hExt hLeft hRight

/-- Mixed evidence is preserved by same-intent replacement only when the
extensional channel is preserved separately.

This is the honest three-channel Chapter-12 theorem for finite HO predicate
vocabularies. Same-intent replacement preserves the ASSOC and PAT score-derived
channels through the predicate-pair order-rank bridge, while the extensional
channel remains an explicit hypothesis instead of being silently inferred from
intensional sameness. -/
theorem mixedEvidence_eq_of_predicateVocabularyPairOrderRankScore_sameIntent
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (pairEnc : InheritanceQueryBuilder Pred PairQuery)
    (model : InheritanceQueryBuilder.IntensionalScoreModel
      (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
    (combine :
      Mettapedia.Logic.EvidenceQuantale.BinaryEvidence →
        Mettapedia.Logic.EvidenceQuantale.BinaryEvidence →
          Mettapedia.Logic.EvidenceQuantale.BinaryEvidence →
            Mettapedia.Logic.EvidenceQuantale.BinaryEvidence)
    (hMixed :
      InheritanceQueryBuilder.MixedAssocPatScoreCorrespondence
        (State := State) (Atom := Pred) (Query := PairQuery)
        pairEnc combine model.assocScore model.patScore model.scoreToEvidence)
    (hAssocScore : ∀ (W : State) (a b : Pred),
      model.assocScore W a b =
        predicateVocabularyPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode a b)
    (hPatScore : ∀ (W : State) (a b : Pred),
      model.patScore W a b =
        predicateVocabularyPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode a b)
    {W : State} {a b c d : Pred}
    (hExt :
      InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
        InheritanceQueryBuilder.extensionalEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d)
    (hLeft :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode a c)
    (hRight :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode b d) :
    InheritanceQueryBuilder.mixedEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
      InheritanceQueryBuilder.mixedEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d := by
  have hAssocPat :
      InheritanceQueryBuilder.intensionalAssocEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
          InheritanceQueryBuilder.intensionalAssocEvidence
            (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d ∧
        InheritanceQueryBuilder.intensionalPATEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
          InheritanceQueryBuilder.intensionalPATEvidence
            (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d :=
    assocPatEvidence_eq_of_predicateVocabularyPairOrderRankScore_sameIntent
      (Base := Base) (Const := Const) M σ decode pairEnc model hAssocScore hPatScore
      hLeft hRight
  have hAssocLift :
      model.scoreToEvidence (model.assocScore W a b) =
        model.scoreToEvidence (model.assocScore W c d) := by
    calc
      model.scoreToEvidence (model.assocScore W a b)
          = InheritanceQueryBuilder.intensionalAssocEvidence
              (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b :=
        (model.assoc_sound W a b).symm
      _ = InheritanceQueryBuilder.intensionalAssocEvidence
            (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d :=
        hAssocPat.1
      _ = model.scoreToEvidence (model.assocScore W c d) :=
        model.assoc_sound W c d
  have hPatLift :
      model.scoreToEvidence (model.patScore W a b) =
        model.scoreToEvidence (model.patScore W c d) := by
    calc
      model.scoreToEvidence (model.patScore W a b)
          = InheritanceQueryBuilder.intensionalPATEvidence
              (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b :=
        (model.pat_sound W a b).symm
      _ = InheritanceQueryBuilder.intensionalPATEvidence
            (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d :=
        hAssocPat.2
      _ = model.scoreToEvidence (model.patScore W c d) :=
        model.pat_sound W c d
  calc
    InheritanceQueryBuilder.mixedEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b
        = combine
            (InheritanceQueryBuilder.extensionalEvidence
              (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b)
            (model.scoreToEvidence (model.assocScore W a b))
            (model.scoreToEvidence (model.patScore W a b)) :=
      hMixed W a b
    _ = combine
          (InheritanceQueryBuilder.extensionalEvidence
            (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d)
          (model.scoreToEvidence (model.assocScore W c d))
          (model.scoreToEvidence (model.patScore W c d)) := by
      rw [hExt, hAssocLift, hPatLift]
    _ = InheritanceQueryBuilder.mixedEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d :=
      (hMixed W c d).symm

/-- If the mixed combiner is left-cancellable, then the explicit extensional
channel hypothesis in
`mixedEvidence_eq_of_predicateVocabularyPairOrderRankScore_sameIntent` is also
necessary: after same-intent replacement has fixed the ASSOC and PAT channels,
mixed-evidence equality forces extensional-evidence equality.

This is the theorem-level guardrail against reading same-intent as a
three-channel equality principle. Same intent controls the intensional
ASSOC/PAT channels; the extensional channel remains separate unless the mixed
evidence itself, together with a cancellative combiner, recovers it. -/
theorem extensionalEvidence_eq_of_mixedEvidence_eq_predicateVocabularyPairOrderRankScore_sameIntent
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    [Fintype Pred]
    (pairEnc : InheritanceQueryBuilder Pred PairQuery)
    (model : InheritanceQueryBuilder.IntensionalScoreModel
      (State := State) (Atom := Pred) (Query := PairQuery) pairEnc)
    (combine :
      Mettapedia.Logic.EvidenceQuantale.BinaryEvidence →
        Mettapedia.Logic.EvidenceQuantale.BinaryEvidence →
          Mettapedia.Logic.EvidenceQuantale.BinaryEvidence →
            Mettapedia.Logic.EvidenceQuantale.BinaryEvidence)
    (hMixed :
      InheritanceQueryBuilder.MixedAssocPatScoreCorrespondence
        (State := State) (Atom := Pred) (Query := PairQuery)
        pairEnc combine model.assocScore model.patScore model.scoreToEvidence)
    (hAssocScore : ∀ (W : State) (a b : Pred),
      model.assocScore W a b =
        predicateVocabularyPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode a b)
    (hPatScore : ∀ (W : State) (a b : Pred),
      model.patScore W a b =
        predicateVocabularyPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode a b)
    (hCancel :
      ∀ {x y assoc pat :
          Mettapedia.Logic.EvidenceQuantale.BinaryEvidence},
        combine x assoc pat = combine y assoc pat → x = y)
    {W : State} {a b c d : Pred}
    (hMixedEq :
      InheritanceQueryBuilder.mixedEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
        InheritanceQueryBuilder.mixedEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d)
    (hLeft :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode a c)
    (hRight :
      Mettapedia.Logic.PLNHigherOrderHOLSimilarityBridge.predicateVocabularySameIntent
        (Base := Base) (Const := Const) M σ decode b d) :
    InheritanceQueryBuilder.extensionalEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
      InheritanceQueryBuilder.extensionalEvidence
        (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d := by
  have hAssocPat :
      InheritanceQueryBuilder.intensionalAssocEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
          InheritanceQueryBuilder.intensionalAssocEvidence
            (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d ∧
        InheritanceQueryBuilder.intensionalPATEvidence
          (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b =
          InheritanceQueryBuilder.intensionalPATEvidence
            (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d :=
    assocPatEvidence_eq_of_predicateVocabularyPairOrderRankScore_sameIntent
      (Base := Base) (Const := Const) M σ decode pairEnc model hAssocScore hPatScore
      hLeft hRight
  have hAssocLift :
      model.scoreToEvidence (model.assocScore W a b) =
        model.scoreToEvidence (model.assocScore W c d) := by
    calc
      model.scoreToEvidence (model.assocScore W a b)
          = InheritanceQueryBuilder.intensionalAssocEvidence
              (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b :=
        (model.assoc_sound W a b).symm
      _ = InheritanceQueryBuilder.intensionalAssocEvidence
            (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d :=
        hAssocPat.1
      _ = model.scoreToEvidence (model.assocScore W c d) :=
        model.assoc_sound W c d
  have hPatLift :
      model.scoreToEvidence (model.patScore W a b) =
        model.scoreToEvidence (model.patScore W c d) := by
    calc
      model.scoreToEvidence (model.patScore W a b)
          = InheritanceQueryBuilder.intensionalPATEvidence
              (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b :=
        (model.pat_sound W a b).symm
      _ = InheritanceQueryBuilder.intensionalPATEvidence
            (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d :=
        hAssocPat.2
      _ = model.scoreToEvidence (model.patScore W c d) :=
        model.pat_sound W c d
  have hCombined :
      combine
          (InheritanceQueryBuilder.extensionalEvidence
            (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b)
          (model.scoreToEvidence (model.assocScore W a b))
          (model.scoreToEvidence (model.patScore W a b)) =
        combine
          (InheritanceQueryBuilder.extensionalEvidence
            (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d)
          (model.scoreToEvidence (model.assocScore W c d))
          (model.scoreToEvidence (model.patScore W c d)) := by
    calc
      combine
          (InheritanceQueryBuilder.extensionalEvidence
            (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b)
          (model.scoreToEvidence (model.assocScore W a b))
          (model.scoreToEvidence (model.patScore W a b))
          = InheritanceQueryBuilder.mixedEvidence
              (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b :=
        (hMixed W a b).symm
      _ = InheritanceQueryBuilder.mixedEvidence
            (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d :=
        hMixedEq
      _ = combine
            (InheritanceQueryBuilder.extensionalEvidence
              (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d)
            (model.scoreToEvidence (model.assocScore W c d))
            (model.scoreToEvidence (model.patScore W c d)) :=
        hMixed W c d
  have hAligned :
      combine
          (InheritanceQueryBuilder.extensionalEvidence
            (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc a b)
          (model.scoreToEvidence (model.assocScore W c d))
          (model.scoreToEvidence (model.patScore W c d)) =
        combine
          (InheritanceQueryBuilder.extensionalEvidence
            (State := State) (Atom := Pred) (Query := PairQuery) W pairEnc c d)
          (model.scoreToEvidence (model.assocScore W c d))
          (model.scoreToEvidence (model.patScore W c d)) := by
    simpa [hAssocLift, hPatLift] using hCombined
  exact hCancel hAligned

end Evidence

end Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge
