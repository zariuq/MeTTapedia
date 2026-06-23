import Mettapedia.Logic.AbstractInheritancePLNBridge
import Mettapedia.Logic.AbstractInheritanceStampedWitness
import Mettapedia.Logic.ConceptOntology.Examples
import Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge
import Mathlib.Tactic

/-!
# Live ASSOC/PAT Demo Through Abstract Inheritance

This module instantiates the abstract subset theorems on a concrete, finite
ontology fragment:

- the object/concept membership surface is the WM-backed toy ontology;
- ASSOC/PAT scores are derived from the abstract extent/intent interpretation;
- the Chapter-12 monotonicity theorems are exercised through
  `AbstractExtentPairSubsetRel`, not just the generic theorem surface.
-/

namespace Mettapedia.Logic.AbstractInheritanceIntensionalDemo

open Mettapedia.Logic
open Mettapedia.Logic.EvidenceClass
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNIntensionalWorldModel
open Mettapedia.Logic.ConceptOntology
open Mettapedia.Logic.ConceptOntology.Examples
open Mettapedia.Logic.AbstractInheritance
open scoped ENNReal

universe u v w

instance : Fintype Creature where
  elems := {Creature.tweety, Creature.pingu, Creature.plane}
  complete x := by
    cases x <;> simp

instance : Fintype Concept where
  elems := {Concept.bird, Concept.penguin, Concept.fly}
  complete x := by
    cases x <;> simp

/-- Scaling state for the fixed ontology fragment. Multiplicity changes evidence
mass additively while keeping the underlying distinction structure. -/
abbrev DemoState := ℕ

noncomputable instance : EvidenceType DemoState := { (inferInstance : AddCommMonoid DemoState) with }

/-- Additive scaling of fixed BinaryEvidence by a natural multiplicity. -/
noncomputable def natScaleEvidence (n : ℕ) (e : BinaryEvidence) : BinaryEvidence where
  pos := (n : ℝ≥0∞) * e.pos
  neg := (n : ℝ≥0∞) * e.neg

@[simp] theorem binaryEvidence_neg_zero : BinaryEvidence.neg (0 : BinaryEvidence) = 0 := rfl

@[simp] theorem natScaleEvidence_zero (e : BinaryEvidence) :
    natScaleEvidence 0 e = 0 := by
  ext <;> simp [natScaleEvidence]

@[simp] theorem natScaleEvidence_one (e : BinaryEvidence) :
    natScaleEvidence 1 e = e := by
  ext <;> simp [natScaleEvidence]

@[simp] theorem natScaleEvidence_add (n m : ℕ) (e : BinaryEvidence) :
    natScaleEvidence (n + m) e = natScaleEvidence n e + natScaleEvidence m e := by
  ext <;> simp [natScaleEvidence, BinaryEvidence.hplus_def, add_mul]

noncomputable instance : WorldModelSigma DemoState ToySort ToyQueryFamily where
  evidence W q := natScaleEvidence W (toyWM q)
  evidence_add W₁ W₂ q := by
    simp only [natScaleEvidence_add]
  evidence_zero q := by
    simp only [natScaleEvidence_zero]

/-- Untyped 4-channel inheritance queries over the concept fragment. -/
inductive DemoPairQuery where
  | ext : Concept → Concept → DemoPairQuery
  | assoc : Concept → Concept → DemoPairQuery
  | pat : Concept → Concept → DemoPairQuery
  | mix : Concept → Concept → DemoPairQuery
  deriving DecidableEq, Repr

/-- BinaryEvidence embedding for nonnegative scores. -/
def scoreToEvidenceNNReal (r : NNReal) : BinaryEvidence := ⟨(r : ℝ≥0∞), 0⟩

/-- Real-valued evidence embedding used by the intensional score-model API. -/
def scoreToEvidenceReal (s : ℝ) : BinaryEvidence := ⟨ENNReal.ofReal s, 0⟩

@[simp] theorem scoreToEvidenceReal_ofNNReal (r : NNReal) :
    scoreToEvidenceReal (r : ℝ) = scoreToEvidenceNNReal r := by
  ext <;> simp [scoreToEvidenceReal, scoreToEvidenceNNReal]

theorem natScaleEvidence_scoreToEvidenceNNReal (n : ℕ) (r : NNReal) :
    natScaleEvidence n (scoreToEvidenceNNReal r) =
      scoreToEvidenceReal ((((n : NNReal) * r : NNReal) : ℝ)) := by
  ext <;> simp [natScaleEvidence, scoreToEvidenceNNReal, scoreToEvidenceReal]

/-- The fixed abstract interpretation at unit multiplicity. Positive scaling
preserves the same crisp ontology. -/
noncomputable def baseInterpretation : Interpretation Concept Creature Concept :=
  MembershipQueryBuilder.abstractInterpretationAt
    (State := DemoState) gate 1 membershipBuilder

noncomputable def extentCard (c : Concept) : NNReal :=
  ((DualConcept.finiteExtent (baseInterpretation.meaning c)).card : NNReal)

noncomputable def intentCard (c : Concept) : NNReal :=
  ((DualConcept.finiteIntent (baseInterpretation.meaning c)).card : NNReal)

/-- ASSOC score: richer antecedent intent and broader consequent extent both
raise the score. -/
noncomputable def assocBaseScore (a b : Concept) : NNReal :=
  intentCard a + extentCard b

/-- PAT score: same abstract shape, but with extra weight on consequent extent
to keep the PAT channel distinct from ASSOC in the demo. -/
noncomputable def patBaseScore (a b : Concept) : NNReal :=
  intentCard a + extentCard b + extentCard b

/-- Extensional score view used by the mixed demo channel. -/
noncomputable def extBaseScore (_a b : Concept) : NNReal :=
  extentCard b

noncomputable def mixBaseEvidence (a b : Concept) : BinaryEvidence :=
  scoreToEvidenceNNReal (extBaseScore a b) +
    scoreToEvidenceNNReal (assocBaseScore a b) +
    scoreToEvidenceNNReal (patBaseScore a b)

noncomputable instance : BinaryWorldModel DemoState DemoPairQuery where
  evidence W q :=
    match q with
    | .ext a b => natScaleEvidence W (scoreToEvidenceNNReal (extBaseScore a b))
    | .assoc a b => natScaleEvidence W (scoreToEvidenceNNReal (assocBaseScore a b))
    | .pat a b => natScaleEvidence W (scoreToEvidenceNNReal (patBaseScore a b))
    | .mix a b => natScaleEvidence W (mixBaseEvidence a b)
  evidence_add W₁ W₂ q := by
    cases q <;> simp only [natScaleEvidence_add]
  evidence_zero q := by
    cases q <;> simp only [natScaleEvidence_zero]

def pairEnc : InheritanceQueryBuilder Concept DemoPairQuery where
  extensional := DemoPairQuery.ext
  intensionalAssoc := DemoPairQuery.assoc
  intensionalPAT := DemoPairQuery.pat
  mixed := DemoPairQuery.mix

noncomputable def assocScoreFn (W : DemoState) (a b : Concept) : ℝ :=
  ((((W : NNReal) * assocBaseScore a b : NNReal) : ℝ))

noncomputable def patScoreFn (W : DemoState) (a b : Concept) : ℝ :=
  ((((W : NNReal) * patBaseScore a b : NNReal) : ℝ))

noncomputable def demoScoreModel :
    InheritanceQueryBuilder.IntensionalScoreModel
      (State := DemoState) (Atom := Concept) (Query := DemoPairQuery) pairEnc where
  assocScore := assocScoreFn
  patScore := patScoreFn
  scoreToEvidence := scoreToEvidenceReal
  scoreToEvidence_mono := by
    intro x y hxy
    exact ⟨ENNReal.ofReal_le_ofReal hxy, le_rfl⟩
  assoc_sound := by
    intro W a b
    change natScaleEvidence W (scoreToEvidenceNNReal (assocBaseScore a b)) =
      scoreToEvidenceReal ((((W : NNReal) * assocBaseScore a b : NNReal) : ℝ))
    simpa using natScaleEvidence_scoreToEvidenceNNReal W (assocBaseScore a b)
  pat_sound := by
    intro W a b
    change natScaleEvidence W (scoreToEvidenceNNReal (patBaseScore a b)) =
      scoreToEvidenceReal ((((W : NNReal) * patBaseScore a b : NNReal) : ℝ))
    simpa using natScaleEvidence_scoreToEvidenceNNReal W (patBaseScore a b)

theorem gate_accept_natScaleEvidence_succ_iff_one
    (n : ℕ) (e : BinaryEvidence) :
    gate.accept (natScaleEvidence (Nat.succ n) e) ↔ gate.accept (natScaleEvidence 1 e) := by
  simp [gate, natScaleEvidence]

@[simp] theorem accept_memberEvidence_succ_iff_one
    (n : ℕ) (x : Creature) (c : Concept) :
    gate.accept
      (MembershipQueryBuilder.memberEvidence
        (State := DemoState) (Obj := Creature) (Con := Concept)
        (Srt := ToySort) (Query := ToyQueryFamily)
        (Nat.succ n) membershipBuilder x c)
      ↔
    gate.accept
      (MembershipQueryBuilder.memberEvidence
        (State := DemoState) (Obj := Creature) (Con := Concept)
        (Srt := ToySort) (Query := ToyQueryFamily)
        1 membershipBuilder x c) := by
  change gate.accept
      (natScaleEvidence (Nat.succ n)
        (WorldModelSigma.evidenceAt
          (State := ToyState) (Srt := ToySort) (Query := ToyQueryFamily)
          toyWM (membershipBuilder.member x c))) ↔
    gate.accept
      (natScaleEvidence 1
        (WorldModelSigma.evidenceAt
          (State := ToyState) (Srt := ToySort) (Query := ToyQueryFamily)
          toyWM (membershipBuilder.member x c)))
  exact gate_accept_natScaleEvidence_succ_iff_one n
    (WorldModelSigma.evidenceAt
      (State := ToyState) (Srt := ToySort) (Query := ToyQueryFamily)
      toyWM (membershipBuilder.member x c))

@[simp] theorem memberEvidence_one_eq_toy
    (x : Creature) (c : Concept) :
    MembershipQueryBuilder.memberEvidence
      (State := DemoState) (Obj := Creature) (Con := Concept)
      (Srt := ToySort) (Query := ToyQueryFamily)
      1 membershipBuilder x c
      =
    MembershipQueryBuilder.memberEvidence
      (State := ToyState) (Obj := Creature) (Con := Concept)
      (Srt := ToySort) (Query := ToyQueryFamily)
      toyWM membershipBuilder x c := by
  change natScaleEvidence 1
      (WorldModelSigma.evidenceAt
        (State := ToyState) (Srt := ToySort) (Query := ToyQueryFamily)
        toyWM (membershipBuilder.member x c))
    =
    WorldModelSigma.evidenceAt
      (State := ToyState) (Srt := ToySort) (Query := ToyQueryFamily)
      toyWM (membershipBuilder.member x c)
  simp [natScaleEvidence_one]

theorem crispExtensionalInheritsAt_one_iff_toy
    (a b : Concept) :
    MembershipQueryBuilder.crispExtensionalInheritsAt
        (State := DemoState) gate 1 membershipBuilder a b
      ↔
    MembershipQueryBuilder.crispExtensionalInheritsAt
        (State := ToyState) gate toyWM membershipBuilder a b := by
  rw [MembershipQueryBuilder.crispExtensionalInheritsAt_iff,
    MembershipQueryBuilder.crispExtensionalInheritsAt_iff]
  constructor
  · intro h x hx
    simpa using h x (by simpa using hx)
  · intro h x hx
    simpa using h x (by simpa using hx)

theorem crispExtensionalInheritsAt_succ_iff_one
    (n : ℕ) (a b : Concept) :
    MembershipQueryBuilder.crispExtensionalInheritsAt
        (State := DemoState) gate (Nat.succ n) membershipBuilder a b
      ↔
    MembershipQueryBuilder.crispExtensionalInheritsAt
        (State := DemoState) gate 1 membershipBuilder a b := by
  rw [MembershipQueryBuilder.crispExtensionalInheritsAt_iff,
    MembershipQueryBuilder.crispExtensionalInheritsAt_iff]
  constructor
  · intro h x hx
    exact (accept_memberEvidence_succ_iff_one n x b).1 <|
      h x ((accept_memberEvidence_succ_iff_one n x a).2 hx)
  · intro h x hx
    exact (accept_memberEvidence_succ_iff_one n x b).2 <|
      h x ((accept_memberEvidence_succ_iff_one n x a).1 hx)

theorem abstractInheritsAt_succ_iff_one
    (n : ℕ) (a b : Concept) :
    (MembershipQueryBuilder.abstractInterpretationAt
      (State := DemoState) gate (Nat.succ n) membershipBuilder).Inherits a b
      ↔
    (MembershipQueryBuilder.abstractInterpretationAt
      (State := DemoState) gate 1 membershipBuilder).Inherits a b := by
  rw [MembershipQueryBuilder.abstractInterpretationAt_inherits_iff,
    MembershipQueryBuilder.abstractInterpretationAt_inherits_iff,
    crispExtensionalInheritsAt_succ_iff_one]

theorem abstractExtentPairSubsetRel_succ_iff_one
    (n : ℕ) (a b c d : Concept) :
    AbstractExtentPairSubsetRel
        DemoState Creature Concept ToySort ToyQueryFamily
        gate membershipBuilder (Nat.succ n) a b c d
      ↔
    AbstractExtentPairSubsetRel
        DemoState Creature Concept ToySort ToyQueryFamily
        gate membershipBuilder 1 a b c d := by
  constructor
  · rintro ⟨hLeft, hRight⟩
    exact ⟨(abstractInheritsAt_succ_iff_one n c a).1 hLeft,
      (abstractInheritsAt_succ_iff_one n b d).1 hRight⟩
  · rintro ⟨hLeft, hRight⟩
    exact ⟨(abstractInheritsAt_succ_iff_one n c a).2 hLeft,
      (abstractInheritsAt_succ_iff_one n b d).2 hRight⟩

theorem finiteIntent_subset_of_inherits
    {a c : Concept} (h : baseInterpretation.Inherits c a) :
    DualConcept.finiteIntent (baseInterpretation.meaning a) ⊆
      DualConcept.finiteIntent (baseInterpretation.meaning c) := by
  intro t ht
  have ht' : t ∈ (baseInterpretation.meaning a).intent := by
    simpa using ht
  have : t ∈ (baseInterpretation.meaning c).intent := h.2 ht'
  simpa using this

theorem finiteExtent_subset_of_inherits
    {b d : Concept} (h : baseInterpretation.Inherits b d) :
    DualConcept.finiteExtent (baseInterpretation.meaning b) ⊆
      DualConcept.finiteExtent (baseInterpretation.meaning d) := by
  intro x hx
  have hx' : x ∈ (baseInterpretation.meaning b).extent := by
    simpa using hx
  have : x ∈ (baseInterpretation.meaning d).extent := h.1 hx'
  simpa using this

theorem intentCard_mono_of_inherits
    {a c : Concept} (h : baseInterpretation.Inherits c a) :
    intentCard a ≤ intentCard c := by
  simpa [intentCard] using
    (show ((DualConcept.finiteIntent (baseInterpretation.meaning a)).card : NNReal) ≤
        ((DualConcept.finiteIntent (baseInterpretation.meaning c)).card : NNReal) from by
      exact_mod_cast Finset.card_le_card (finiteIntent_subset_of_inherits h))

theorem extentCard_mono_of_inherits
    {b d : Concept} (h : baseInterpretation.Inherits b d) :
    extentCard b ≤ extentCard d := by
  simpa [extentCard] using
    (show ((DualConcept.finiteExtent (baseInterpretation.meaning b)).card : NNReal) ≤
        ((DualConcept.finiteExtent (baseInterpretation.meaning d)).card : NNReal) from by
      exact_mod_cast Finset.card_le_card (finiteExtent_subset_of_inherits h))

theorem assocBaseScore_mono
    {a b c d : Concept}
    (hLeft : baseInterpretation.Inherits c a)
    (hRight : baseInterpretation.Inherits b d) :
    assocBaseScore a b ≤ assocBaseScore c d := by
  simpa [assocBaseScore] using add_le_add
    (intentCard_mono_of_inherits hLeft)
    (extentCard_mono_of_inherits hRight)

theorem patBaseScore_mono
    {a b c d : Concept}
    (hLeft : baseInterpretation.Inherits c a)
    (hRight : baseInterpretation.Inherits b d) :
    patBaseScore a b ≤ patBaseScore c d := by
  simpa [patBaseScore, add_assoc] using add_le_add
    (intentCard_mono_of_inherits hLeft)
    (add_le_add
      (extentCard_mono_of_inherits hRight)
      (extentCard_mono_of_inherits hRight))

theorem assocSubsetSemantics :
    InheritanceQueryBuilder.AssocSubsetSemantics
      (State := DemoState) (Atom := Concept) (Query := DemoPairQuery)
      pairEnc demoScoreModel
      (AbstractExtentPairSubsetRel
        DemoState Creature Concept ToySort ToyQueryFamily gate membershipBuilder) := by
  intro W a b c d hRel
  cases W with
  | zero =>
      change assocScoreFn 0 a b ≤ assocScoreFn 0 c d
      simp [assocScoreFn]
  | succ n =>
      have hRel1 := (abstractExtentPairSubsetRel_succ_iff_one n a b c d).1 hRel
      have hBase : assocBaseScore a b ≤ assocBaseScore c d :=
        assocBaseScore_mono hRel1.1 hRel1.2
      change ((((Nat.succ n : NNReal) * assocBaseScore a b : NNReal) : ℝ) ≤
          (((Nat.succ n : NNReal) * assocBaseScore c d : NNReal) : ℝ))
      exact_mod_cast mul_le_mul_right hBase (Nat.succ n : NNReal)

theorem patSubsetSemantics :
    InheritanceQueryBuilder.PATSubsetSemantics
      (State := DemoState) (Atom := Concept) (Query := DemoPairQuery)
      pairEnc demoScoreModel
      (AbstractExtentPairSubsetRel
        DemoState Creature Concept ToySort ToyQueryFamily gate membershipBuilder) := by
  intro W a b c d hRel
  cases W with
  | zero =>
      change patScoreFn 0 a b ≤ patScoreFn 0 c d
      simp [patScoreFn]
  | succ n =>
      have hRel1 := (abstractExtentPairSubsetRel_succ_iff_one n a b c d).1 hRel
      have hBase : patBaseScore a b ≤ patBaseScore c d :=
        patBaseScore_mono hRel1.1 hRel1.2
      change ((((Nat.succ n : NNReal) * patBaseScore a b : NNReal) : ℝ) ≤
          (((Nat.succ n : NNReal) * patBaseScore c d : NNReal) : ℝ))
      exact_mod_cast mul_le_mul_right hBase (Nat.succ n : NNReal)

theorem penguin_inherits_bird_at_one :
    (MembershipQueryBuilder.abstractInterpretationAt
      (State := DemoState) gate 1 membershipBuilder).Inherits Concept.penguin Concept.bird := by
  exact (MembershipQueryBuilder.abstractInterpretationAt_inherits_iff
    (State := DemoState) (Obj := Creature) (Con := Concept)
    (Srt := ToySort) (Query := ToyQueryFamily)
    gate 1 membershipBuilder Concept.penguin Concept.bird).2 <|
    (crispExtensionalInheritsAt_one_iff_toy Concept.penguin Concept.bird).2
      penguin_extensionally_inherits_bird

theorem bird_inherits_bird_at_one :
    (MembershipQueryBuilder.abstractInterpretationAt
      (State := DemoState) gate 1 membershipBuilder).Inherits Concept.bird Concept.bird := by
  exact Interpretation.inherits_refl
    (I := MembershipQueryBuilder.abstractInterpretationAt
      (State := DemoState) gate 1 membershipBuilder)
    Concept.bird

theorem not_bird_inherits_fly_at_one :
    ¬ (MembershipQueryBuilder.abstractInterpretationAt
      (State := DemoState) gate 1 membershipBuilder).Inherits Concept.bird Concept.fly := by
  intro h
  exact bird_not_extensionally_inherits_fly <|
    (crispExtensionalInheritsAt_one_iff_toy Concept.bird Concept.fly).1
      ((MembershipQueryBuilder.abstractInterpretationAt_inherits_iff
        (State := DemoState) (Obj := Creature) (Con := Concept)
        (Srt := ToySort) (Query := ToyQueryFamily)
        gate 1 membershipBuilder Concept.bird Concept.fly).1 h)

theorem positive_pair_subset_rel :
    AbstractExtentPairSubsetRel
      DemoState Creature Concept ToySort ToyQueryFamily
      gate membershipBuilder 1
      Concept.bird Concept.bird Concept.penguin Concept.bird := by
  exact ⟨penguin_inherits_bird_at_one, bird_inherits_bird_at_one⟩

/-- The concrete Chapter-12 toy pair-subset witness can feed the finite
HO predicate-vocabulary ASSOC/PAT target once the toy concept intension is
transported into the decoded predicate vocabulary.

The transport hypothesis is intentionally explicit: this theorem connects the
old abstract-inheritance semantics to the new HO target without pretending that
the ontology concepts already are HOL predicates. -/
theorem positive_pair_subset_rel_transports_to_predicateVocabularyIntensionalPairSubsetRel
    {Base : Type u}
    {Const : Mettapedia.Logic.HOL.Ty Base → Type v}
    (M : Mettapedia.Logic.HOL.HenkinModel.{u, v, w} Base Const)
    (σ : Mettapedia.Logic.HOL.Ty Base)
    {Pred : Type}
    (code : Concept → Pred)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (hTransport : ∀ {p q : Concept},
      baseInterpretation.IntensionalInherits p q →
        (Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).IntensionalInherits
            (code p) (code q)) :
    Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel
      (Base := Base) (Const := Const) M σ decode (1 : DemoState)
      (code Concept.bird) (code Concept.bird)
      (code Concept.penguin) (code Concept.bird) := by
  exact
    Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel_of_interpretationPairSubsetRel
        (I := baseInterpretation)
        (M := M) (σ := σ) (code := code) (decode := decode)
        hTransport (1 : DemoState)
        (by
          simpa [ConceptOntology.AbstractExtentPairSubsetRel, baseInterpretation] using
            positive_pair_subset_rel)

/-- Intent-map variant of the concrete transport canary.

Instead of assuming a packaged transport theorem, this version asks for the two
primitive map laws that richer Chapter-12 pattern semantics should prove:
reflection of decoded HO intent items into concrete concept intent, and
preservation of concrete concept intent back into the decoded HO vocabulary. -/
theorem positive_pair_subset_rel_transports_to_predicateVocabularyIntensionalPairSubsetRel_viaIntentMap
    {Base : Type u}
    {Const : Mettapedia.Logic.HOL.Ty Base → Type v}
    (M : Mettapedia.Logic.HOL.HenkinModel.{u, v, w} Base Const)
    (σ : Mettapedia.Logic.HOL.Ty Base)
    {Pred : Type}
    (code : Concept → Pred)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → Concept)
    (hReflect : ∀ {p : Concept} {r : Pred},
      r ∈ ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent →
        attrOf r ∈ (baseInterpretation.meaning p).intent)
    (hPreserve : ∀ {p : Concept} {r : Pred},
      attrOf r ∈ (baseInterpretation.meaning p).intent →
        r ∈ ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent) :
    Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel
      (Base := Base) (Const := Const) M σ decode (1 : DemoState)
      (code Concept.bird) (code Concept.bird)
      (code Concept.penguin) (code Concept.bird) := by
  exact
    Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel_of_interpretationPairSubsetRel_viaIntentMap
      (I := baseInterpretation)
      (M := M) (σ := σ) (code := code) (decode := decode)
      attrOf hReflect hPreserve (1 : DemoState)
      (by
        simpa [ConceptOntology.AbstractExtentPairSubsetRel, baseInterpretation] using
          positive_pair_subset_rel)

/-- Calibrated-intent variant of the concrete transport canary.

This is the proof obligation richer empirical/factor-graph semantics should
prefer: one iff identifies decoded HO intent membership with concrete
pattern-side intent membership. The bridge then recovers both reflection and
preservation automatically. -/
theorem positive_pair_subset_rel_transports_to_predicateVocabularyIntensionalPairSubsetRel_viaIntentCalibration
    {Base : Type u}
    {Const : Mettapedia.Logic.HOL.Ty Base → Type v}
    (M : Mettapedia.Logic.HOL.HenkinModel.{u, v, w} Base Const)
    (σ : Mettapedia.Logic.HOL.Ty Base)
    {Pred : Type}
    (code : Concept → Pred)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → Concept)
    (hCal : ∀ {p : Concept} {r : Pred},
      r ∈ ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
        attrOf r ∈ (baseInterpretation.meaning p).intent) :
    Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel
      (Base := Base) (Const := Const) M σ decode (1 : DemoState)
      (code Concept.bird) (code Concept.bird)
      (code Concept.penguin) (code Concept.bird) := by
  exact
    Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel_of_interpretationPairSubsetRel_viaIntentCalibration
      (I := baseInterpretation)
      (M := M) (σ := σ) (code := code) (decode := decode)
      attrOf hCal (1 : DemoState)
      (by
        simpa [ConceptOntology.AbstractExtentPairSubsetRel, baseInterpretation] using
          positive_pair_subset_rel)

/-- Concrete Chapter-12 consumer theorem.

The toy `penguin ≤ bird` concept-geometry witness, once calibrated into a
finite HOL predicate vocabulary, drives actual ASSOC and PAT evidence
monotonicity for any nonnegatively weighted order-rank score model.  This is the
rule-facing version of the transport canary above: it consumes the existing
finite-vocabulary ASSOC/PAT bridge instead of stopping at the intermediate
pair-subset relation. -/
theorem positive_pair_subset_rel_weightedPredicateVocabularyAssocPatEvidence_mono_viaIntentCalibration
    {Base : Type u}
    {Const : Mettapedia.Logic.HOL.Ty Base → Type v}
    (M : Mettapedia.Logic.HOL.HenkinModel.{u, v, w} Base Const)
    (σ : Mettapedia.Logic.HOL.Ty Base)
    {Pred : Type}
    [Fintype Pred]
    (code : Concept → Pred)
    (decode : Pred →
      Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.UnaryPredicate
        (Base := Base) (Const := Const) σ)
    (attrOf : Pred → Concept)
    (hCal : ∀ {p : Concept} {r : Pred},
      r ∈ ((Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge.predicateVocabularyInterpretation
          (Base := Base) (Const := Const) M σ decode).meaning (code p)).intent ↔
        attrOf r ∈ (baseInterpretation.meaning p).intent)
    {State PairQuery : Type}
    [EvidenceType State]
    [WorldModelSigma State InheritanceSort (InheritanceQueryFamily PairQuery)]
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
        Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          assocLeftWeight assocRightWeight a b)
    (hPatScore : ∀ (W : State) (a b : Pred),
      model.patScore W a b =
        Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyWeightedPairOrderRankScore
          (Base := Base) (Const := Const) M σ decode
          patLeftWeight patRightWeight a b)
    (W : State) :
    InheritanceQueryBuilder.intensionalAssocEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        W pairEnc (code Concept.bird) (code Concept.bird) ≤
      InheritanceQueryBuilder.intensionalAssocEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        W pairEnc (code Concept.penguin) (code Concept.bird)
      ∧
      InheritanceQueryBuilder.intensionalPATEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        W pairEnc (code Concept.bird) (code Concept.bird) ≤
      InheritanceQueryBuilder.intensionalPATEvidence
        (State := State) (Atom := Pred) (Query := PairQuery)
        W pairEnc (code Concept.penguin) (code Concept.bird) := by
  have hRelDemo :=
    positive_pair_subset_rel_transports_to_predicateVocabularyIntensionalPairSubsetRel_viaIntentCalibration
      (Base := Base) (Const := Const) M σ code decode attrOf hCal
  have hRel :
      Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel
        (Base := Base) (Const := Const) M σ decode W
        (code Concept.bird) (code Concept.bird)
        (code Concept.penguin) (code Concept.bird) := by
    simpa [Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel]
      using hRelDemo
  have hAssocSubset :
      InheritanceQueryBuilder.AssocSubsetSemantics
        (State := State) (Atom := Pred) (Query := PairQuery)
        pairEnc model
        (Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel
          (Base := Base) (Const := Const) M σ decode) :=
    Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge.assocSubsetSemantics_of_predicateVocabularyWeightedPairOrderRankScore
      (Base := Base) (Const := Const) M σ decode pairEnc model
      hAssocLeftWeight hAssocRightWeight hAssocScore
  have hPatSubset :
      InheritanceQueryBuilder.PATSubsetSemantics
        (State := State) (Atom := Pred) (Query := PairQuery)
        pairEnc model
        (Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge.predicateVocabularyIntensionalPairSubsetRel
          (Base := Base) (Const := Const) M σ decode) :=
    Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge.patSubsetSemantics_of_predicateVocabularyWeightedPairOrderRankScore
      (Base := Base) (Const := Const) M σ decode pairEnc model
      hPatLeftWeight hPatRightWeight hPatScore
  exact
    ⟨Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge.assocEvidence_mono_of_predicateVocabularyIntensionalSubsetSemantics
        (Base := Base) (Const := Const) M σ decode pairEnc model hAssocSubset hRel,
      Mettapedia.Logic.PLNHigherOrderHOLAssocPatBridge.patEvidence_mono_of_predicateVocabularyIntensionalSubsetSemantics
        (Base := Base) (Const := Const) M σ decode pairEnc model hPatSubset hRel⟩

theorem negative_pair_subset_rel :
    ¬ AbstractExtentPairSubsetRel
      DemoState Creature Concept ToySort ToyQueryFamily
      gate membershipBuilder 1
      Concept.fly Concept.bird Concept.bird Concept.fly := by
  intro h
  exact not_bird_inherits_fly_at_one h.1

theorem assocEvidence_birdBird_le_penguinBird :
    InheritanceQueryBuilder.intensionalAssocEvidence
        (State := DemoState) (Atom := Concept) (Query := DemoPairQuery)
        1 pairEnc Concept.bird Concept.bird ≤
      InheritanceQueryBuilder.intensionalAssocEvidence
        (State := DemoState) (Atom := Concept) (Query := DemoPairQuery)
        1 pairEnc Concept.penguin Concept.bird := by
  exact assocEvidence_mono_of_abstractSubsetSemantics
    (State := DemoState) (Obj := Creature) (Con := Concept)
    (MemberSrt := ToySort) (PairQuery := DemoPairQuery)
    (MemberQuery := ToyQueryFamily)
    (G := gate) (memberEnc := membershipBuilder)
    pairEnc demoScoreModel assocSubsetSemantics positive_pair_subset_rel

theorem patEvidence_birdBird_le_penguinBird :
    InheritanceQueryBuilder.intensionalPATEvidence
        (State := DemoState) (Atom := Concept) (Query := DemoPairQuery)
        1 pairEnc Concept.bird Concept.bird ≤
      InheritanceQueryBuilder.intensionalPATEvidence
        (State := DemoState) (Atom := Concept) (Query := DemoPairQuery)
        1 pairEnc Concept.penguin Concept.bird := by
  exact patEvidence_mono_of_abstractSubsetSemantics
    (State := DemoState) (Obj := Creature) (Con := Concept)
    (MemberSrt := ToySort) (PairQuery := DemoPairQuery)
    (MemberQuery := ToyQueryFamily)
    (G := gate) (memberEnc := membershipBuilder)
    pairEnc demoScoreModel patSubsetSemantics positive_pair_subset_rel

noncomputable def penguinBirdStampedEvidence :
    StampedBinaryEvidence (DualConcept.WitnessStamp Creature Concept) :=
  baseInterpretation.finiteInheritanceStampedEvidence Concept.penguin Concept.bird

noncomputable def birdBirdStampedEvidence :
    StampedBinaryEvidence (DualConcept.WitnessStamp Creature Concept) :=
  baseInterpretation.finiteInheritanceStampedEvidence Concept.bird Concept.bird

theorem bird_mem_baseInterpretation_bird_intent :
    Concept.bird ∈ (baseInterpretation.meaning Concept.bird).intent := by
  simpa [baseInterpretation] using
    (MembershipQueryBuilder.self_mem_intent_abstractInterpretationAt
      (State := DemoState) (Obj := Creature) (Con := Concept)
      (Srt := ToySort) (Query := ToyQueryFamily)
      gate 1 membershipBuilder Concept.bird)

theorem bird_mem_baseInterpretation_penguin_intent :
    Concept.bird ∈ (baseInterpretation.meaning Concept.penguin).intent := by
  exact penguin_inherits_bird_at_one.2 bird_mem_baseInterpretation_bird_intent

theorem posIntBird_mem_penguinBirdStampedEvidence :
    DualConcept.WitnessStamp.posInt Concept.bird ∈ penguinBirdStampedEvidence.stamp := by
  rw [penguinBirdStampedEvidence,
    Interpretation.finiteInheritanceStampedEvidence_stamp]
  have hBird : Concept.bird ∈
      DualConcept.finiteIntent (baseInterpretation.meaning Concept.bird) := by
    simpa using bird_mem_baseInterpretation_bird_intent
  have hPenguin : Concept.bird ∈
      DualConcept.finiteIntent (baseInterpretation.meaning Concept.penguin) := by
    simpa using bird_mem_baseInterpretation_penguin_intent
  have hPosInt : Concept.bird ∈
      DualConcept.finitePositiveIntensionalWitnesses
        (baseInterpretation.meaning Concept.penguin)
        (baseInterpretation.meaning Concept.bird) := by
    exact Finset.mem_inter.mpr ⟨hBird, hPenguin⟩
  have hMap :
      DualConcept.WitnessStamp.posInt (Obj := Creature) (Attr := Concept) Concept.bird ∈
        (DualConcept.finitePositiveIntensionalWitnesses
          (baseInterpretation.meaning Concept.penguin)
          (baseInterpretation.meaning Concept.bird)).map
            (DualConcept.posIntEmbedding (Obj := Creature) (Attr := Concept)) := by
    exact Finset.mem_map.mpr ⟨Concept.bird, hPosInt, by
      simp [DualConcept.posIntEmbedding]⟩
  apply Finset.mem_union.mpr
  left
  apply Finset.mem_union.mpr
  left
  apply Finset.mem_union.mpr
  right
  exact hMap

theorem posIntBird_mem_birdBirdStampedEvidence :
    DualConcept.WitnessStamp.posInt Concept.bird ∈ birdBirdStampedEvidence.stamp := by
  rw [birdBirdStampedEvidence,
    Interpretation.finiteInheritanceStampedEvidence_stamp]
  have hBird : Concept.bird ∈
      DualConcept.finiteIntent (baseInterpretation.meaning Concept.bird) := by
    simpa using bird_mem_baseInterpretation_bird_intent
  have hPosInt : Concept.bird ∈
      DualConcept.finitePositiveIntensionalWitnesses
        (baseInterpretation.meaning Concept.bird)
        (baseInterpretation.meaning Concept.bird) := by
    exact Finset.mem_inter.mpr ⟨hBird, hBird⟩
  have hMap :
      DualConcept.WitnessStamp.posInt (Obj := Creature) (Attr := Concept) Concept.bird ∈
        (DualConcept.finitePositiveIntensionalWitnesses
          (baseInterpretation.meaning Concept.bird)
          (baseInterpretation.meaning Concept.bird)).map
            (DualConcept.posIntEmbedding (Obj := Creature) (Attr := Concept)) := by
    exact Finset.mem_map.mpr ⟨Concept.bird, hPosInt, by
      simp [DualConcept.posIntEmbedding]⟩
  apply Finset.mem_union.mpr
  left
  apply Finset.mem_union.mpr
  left
  apply Finset.mem_union.mpr
  right
  exact hMap

theorem premiseStampedEvidence_overlap_on_bird_intension :
    ¬ StampedBinaryEvidence.StampDisjoint
      penguinBirdStampedEvidence birdBirdStampedEvidence := by
  exact StampedBinaryEvidence.not_stampDisjoint_of_mem
    posIntBird_mem_penguinBirdStampedEvidence
    posIntBird_mem_birdBirdStampedEvidence

theorem premiseStampedEvidence_guardedRevise_eq_none :
    StampedBinaryEvidence.guardedRevise
      penguinBirdStampedEvidence birdBirdStampedEvidence = none := by
  exact StampedBinaryEvidence.guardedRevise_eq_none_of_not_stampDisjoint
    penguinBirdStampedEvidence birdBirdStampedEvidence
    premiseStampedEvidence_overlap_on_bird_intension

theorem penguinBirdStampedEvidence_guardedInternalRevision_eq_some :
    StampedBinaryEvidence.guardedRevise
      (DualConcept.positiveStampedEvidence
        (baseInterpretation.meaning Concept.penguin)
        (baseInterpretation.meaning Concept.bird))
      (DualConcept.negativeStampedEvidence
        (baseInterpretation.meaning Concept.penguin)
        (baseInterpretation.meaning Concept.bird))
      = some penguinBirdStampedEvidence := by
  change
    StampedBinaryEvidence.guardedRevise
      (DualConcept.positiveStampedEvidence
        (baseInterpretation.meaning Concept.penguin)
        (baseInterpretation.meaning Concept.bird))
      (DualConcept.negativeStampedEvidence
        (baseInterpretation.meaning Concept.penguin)
        (baseInterpretation.meaning Concept.bird))
      =
        some (DualConcept.finiteInheritanceStampedEvidence
          (baseInterpretation.meaning Concept.penguin)
          (baseInterpretation.meaning Concept.bird))
  exact DualConcept.finiteInheritanceStampedEvidence_guardedRevise_eq_some
    (baseInterpretation.meaning Concept.penguin)
    (baseInterpretation.meaning Concept.bird)

theorem birdBirdStampedEvidence_guardedInternalRevision_eq_some :
    StampedBinaryEvidence.guardedRevise
      (DualConcept.positiveStampedEvidence
        (baseInterpretation.meaning Concept.bird)
        (baseInterpretation.meaning Concept.bird))
      (DualConcept.negativeStampedEvidence
        (baseInterpretation.meaning Concept.bird)
        (baseInterpretation.meaning Concept.bird))
      = some birdBirdStampedEvidence := by
  change
    StampedBinaryEvidence.guardedRevise
      (DualConcept.positiveStampedEvidence
        (baseInterpretation.meaning Concept.bird)
        (baseInterpretation.meaning Concept.bird))
      (DualConcept.negativeStampedEvidence
        (baseInterpretation.meaning Concept.bird)
        (baseInterpretation.meaning Concept.bird))
      =
        some (DualConcept.finiteInheritanceStampedEvidence
          (baseInterpretation.meaning Concept.bird)
          (baseInterpretation.meaning Concept.bird))
  exact DualConcept.finiteInheritanceStampedEvidence_guardedRevise_eq_some
    (baseInterpretation.meaning Concept.bird)
    (baseInterpretation.meaning Concept.bird)

theorem assoc_pat_provenance_canary :
    InheritanceQueryBuilder.intensionalAssocEvidence
        (State := DemoState) (Atom := Concept) (Query := DemoPairQuery)
        1 pairEnc Concept.bird Concept.bird ≤
      InheritanceQueryBuilder.intensionalAssocEvidence
        (State := DemoState) (Atom := Concept) (Query := DemoPairQuery)
        1 pairEnc Concept.penguin Concept.bird
      ∧
      InheritanceQueryBuilder.intensionalPATEvidence
        (State := DemoState) (Atom := Concept) (Query := DemoPairQuery)
        1 pairEnc Concept.bird Concept.bird ≤
      InheritanceQueryBuilder.intensionalPATEvidence
        (State := DemoState) (Atom := Concept) (Query := DemoPairQuery)
        1 pairEnc Concept.penguin Concept.bird
      ∧
      StampedBinaryEvidence.guardedRevise
        penguinBirdStampedEvidence birdBirdStampedEvidence = none := by
  exact ⟨assocEvidence_birdBird_le_penguinBird,
    patEvidence_birdBird_le_penguinBird,
    premiseStampedEvidence_guardedRevise_eq_none⟩

end Mettapedia.Logic.AbstractInheritanceIntensionalDemo
