import Mettapedia.Logic.AbstractInheritance
import Mettapedia.Logic.ExtensionalIntensionalDivergence
import Mettapedia.Logic.PLNHigherOrderHOLConsequence

namespace Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge

open Mettapedia.Logic.HOL
open Mettapedia.Logic.EvidenceQuantale
open Mettapedia.Logic.ConceptOntology
open Mettapedia.Logic.AbstractInheritance

universe u v w x

variable {Base : Type u} {Const : Ty Base → Type v}

/-- Closed unary HOL predicates over a fixed argument type. -/
abbrev UnaryPredicate (σ : Ty Base) :=
  ClosedTerm Const (σ ⇒ propTy)

/-- Admissible objects of type `σ` in a pointed Henkin model. -/
abbrev PredicateObject
    (M : HenkinModel.{u, v, w} Base Const) (σ : Ty Base) :=
  {x : Ty.denote M.Carrier σ // M.adm σ x}

/-- The canonical empty valuation for closed HOL syntax at a pointed model. -/
def closedValuation (M : HenkinModel.{u, v, w} Base Const) :
    HenkinModel.Valuation M [] :=
  fun {_} v => nomatch v

/-- A closed unary HOL predicate holds of an admissible model object when its
application evaluates to true in the pointed model. -/
def predicateHoldsAt
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ)
    (x : PredicateObject (Base := Base) (Const := Const) M σ) : Prop :=
  (HenkinModel.denote M
      (.app (weaken (Base := Base) (σ := σ) p) (.var .vz))
      (HenkinModel.extend M (closedValuation M) x.1)).down

/-- Predicate membership evidence extracted from a pointed Henkin model. -/
noncomputable def predicateEvidence
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base) :
    PredicateObject (Base := Base) (Const := Const) M σ →
      UnaryPredicate (Base := Base) (Const := Const) σ → BinaryEvidence := by
  classical
  intro x p
  exact if predicateHoldsAt (Base := Base) (Const := Const) M σ p x then ⟨1, 0⟩ else ⟨0, 1⟩

@[simp] theorem positiveSupport_accept_predicateEvidence_iff
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (x : PredicateObject (Base := Base) (Const := Const) M σ)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    EvidenceGate.positiveSupport.accept
        (predicateEvidence (Base := Base) (Const := Const) M σ x p) ↔
      predicateHoldsAt (Base := Base) (Const := Const) M σ p x := by
  classical
  by_cases h : predicateHoldsAt (Base := Base) (Const := Const) M σ p x
  · simp [predicateEvidence, h, EvidenceGate.positiveSupport]
  · simp [predicateEvidence, h, EvidenceGate.positiveSupport]

/-- The abstract inheritance interpretation induced by unary HOL predicates at a
pointed Henkin model. -/
noncomputable def predicateInterpretation
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base) :
    Interpretation
      (UnaryPredicate (Base := Base) (Const := Const) σ)
      (PredicateObject (Base := Base) (Const := Const) M σ)
      (UnaryPredicate (Base := Base) (Const := Const) σ) :=
  crispInterpretation EvidenceGate.positiveSupport
    (predicateEvidence (Base := Base) (Const := Const) M σ)

/-! ## Full extensional/intensional predicate inheritance strength -/

/-- Predicate-level full inheritance strength, reusing the existing
extensional/intensional inheritance machinery on the interpretation induced by
the Henkin model. This is the higher-order version of the WM-PLN full-strength
inheritance quantity, not a duplicate predicate-only scoring rule. -/
noncomputable def predicateFullInheritanceStrength
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [Fintype (UnaryPredicate (Base := Base) (Const := Const) σ)]
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ) : ℝ :=
  Mettapedia.Logic.ExtensionalIntensionalDivergence.fullInheritanceStrength
    (predicateInterpretation (Base := Base) (Const := Const) M σ) p q

/-- Full predicate-inheritance strength is always nonnegative because it is the
existing full extensional/intensional strength on the induced interpretation. -/
theorem predicateFullInheritanceStrength_nonneg
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [Fintype (UnaryPredicate (Base := Base) (Const := Const) σ)]
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ) :
    0 ≤ predicateFullInheritanceStrength (Base := Base) (Const := Const) M σ p q := by
  exact
    Mettapedia.Logic.ExtensionalIntensionalDivergence.fullInheritanceStrength_nonneg
      (predicateInterpretation (Base := Base) (Const := Const) M σ) p q

/-- Full predicate-inheritance strength is bounded above by `1`. -/
theorem predicateFullInheritanceStrength_le_one
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [Fintype (UnaryPredicate (Base := Base) (Const := Const) σ)]
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ) :
    predicateFullInheritanceStrength (Base := Base) (Const := Const) M σ p q ≤ 1 := by
  exact
    Mettapedia.Logic.ExtensionalIntensionalDivergence.fullInheritanceStrength_le_one
      (predicateInterpretation (Base := Base) (Const := Const) M σ) p q

/-- The higher-order full-strength predicate bridge is faithful to the existing
dual inheritance relation: with nonempty extensional support for the
subpredicate and nonempty intensional support for the superpredicate, strength
`1` is exactly abstract predicate inheritance, hence exactly the HOL
`∀ x, p x -> q x` formula by the bridge below. -/
theorem predicateFullInheritanceStrength_eq_one_iff
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [Fintype (UnaryPredicate (Base := Base) (Const := Const) σ)]
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hsubE :
      ((predicateInterpretation (Base := Base) (Const := Const) M σ).meaning p).extent.ncard ≠ 0)
    (hsuperI :
      ((predicateInterpretation (Base := Base) (Const := Const) M σ).meaning q).intent.ncard ≠ 0) :
    predicateFullInheritanceStrength (Base := Base) (Const := Const) M σ p q = 1 ↔
      (predicateInterpretation (Base := Base) (Const := Const) M σ).Inherits p q := by
  exact
    Mettapedia.Logic.ExtensionalIntensionalDivergence.fullInheritanceStrength_eq_one_iff
      (predicateInterpretation (Base := Base) (Const := Const) M σ) p q hsubE hsuperI

/-! ## Finite working vocabularies of higher-order predicates -/

/-- Predicate evidence restricted to a finite working vocabulary. This is the
systems-facing version of `predicateEvidence`: the vocabulary item is decoded
to a closed unary HOL predicate before model-level membership is tested. -/
noncomputable def predicateVocabularyEvidence
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ) :
    PredicateObject (Base := Base) (Const := Const) M σ → Pred → BinaryEvidence := by
  classical
  intro obj p
  exact if predicateHoldsAt (Base := Base) (Const := Const) M σ (decode p) obj
    then ⟨1, 0⟩ else ⟨0, 1⟩

@[simp] theorem positiveSupport_accept_predicateVocabularyEvidence_iff
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (obj : PredicateObject (Base := Base) (Const := Const) M σ)
    (p : Pred) :
    EvidenceGate.positiveSupport.accept
        (predicateVocabularyEvidence
          (Base := Base) (Const := Const) M σ decode obj p) ↔
      predicateHoldsAt (Base := Base) (Const := Const) M σ (decode p) obj := by
  classical
  by_cases h : predicateHoldsAt (Base := Base) (Const := Const) M σ (decode p) obj
  · simp [predicateVocabularyEvidence, h, EvidenceGate.positiveSupport]
  · simp [predicateVocabularyEvidence, h, EvidenceGate.positiveSupport]

/-- The abstract inheritance interpretation induced by a finite working
vocabulary of unary HOL predicates. The attributes are vocabulary items, not
all closed HOL predicates, so the full extensional/intensional strength layer
can be used with an ordinary finite active vocabulary. -/
noncomputable def predicateVocabularyInterpretation
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ) :
    Interpretation Pred
      (PredicateObject (Base := Base) (Const := Const) M σ)
      Pred :=
  crispInterpretation EvidenceGate.positiveSupport
    (predicateVocabularyEvidence (Base := Base) (Const := Const) M σ decode)

/-- Full extensional/intensional inheritance strength on a finite working
predicate vocabulary. This is the deployable version of predicate-level
full-strength inheritance: the vocabulary is finite, but each item still has a
genuine HOL predicate interpretation in the Henkin model. -/
noncomputable def predicateVocabularyFullInheritanceStrength
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [Fintype Pred]
    (p q : Pred) : ℝ :=
  Mettapedia.Logic.ExtensionalIntensionalDivergence.fullInheritanceStrength
    (predicateVocabularyInterpretation (Base := Base) (Const := Const) M σ decode) p q

theorem predicateVocabularyFullInheritanceStrength_nonneg
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [Fintype Pred]
    (p q : Pred) :
    0 ≤ predicateVocabularyFullInheritanceStrength
      (Base := Base) (Const := Const) M σ decode p q := by
  exact
    Mettapedia.Logic.ExtensionalIntensionalDivergence.fullInheritanceStrength_nonneg
      (predicateVocabularyInterpretation
        (Base := Base) (Const := Const) M σ decode) p q

theorem predicateVocabularyFullInheritanceStrength_le_one
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [Fintype Pred]
    (p q : Pred) :
    predicateVocabularyFullInheritanceStrength
      (Base := Base) (Const := Const) M σ decode p q ≤ 1 := by
  exact
    Mettapedia.Logic.ExtensionalIntensionalDivergence.fullInheritanceStrength_le_one
      (predicateVocabularyInterpretation
        (Base := Base) (Const := Const) M σ decode) p q

/-- On a finite working predicate vocabulary, full abstract inheritance is
exactly pointwise implication between the decoded HOL predicates. -/
theorem predicateVocabularyInterpretation_inherits_iff
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (p q : Pred) :
    (predicateVocabularyInterpretation
      (Base := Base) (Const := Const) M σ decode).Inherits p q ↔
      ∀ obj : PredicateObject (Base := Base) (Const := Const) M σ,
        predicateHoldsAt (Base := Base) (Const := Const) M σ (decode p) obj →
          predicateHoldsAt (Base := Base) (Const := Const) M σ (decode q) obj := by
  classical
  have hCrisp :
      (predicateVocabularyInterpretation
        (Base := Base) (Const := Const) M σ decode).Inherits p q ↔
        ∀ obj : PredicateObject (Base := Base) (Const := Const) M σ,
          EvidenceGate.positiveSupport.accept
            (predicateVocabularyEvidence
              (Base := Base) (Const := Const) M σ decode obj p) →
              EvidenceGate.positiveSupport.accept
                (predicateVocabularyEvidence
                  (Base := Base) (Const := Const) M σ decode obj q) := by
    exact
      (crispInterpretation_inherits_iff
        EvidenceGate.positiveSupport
        (predicateVocabularyEvidence
          (Base := Base) (Const := Const) M σ decode) p q).trans
          (crispExtensionalInherits_iff
            EvidenceGate.positiveSupport
            (predicateVocabularyEvidence
              (Base := Base) (Const := Const) M σ decode) p q)
  rw [hCrisp]
  constructor
  · intro h obj hp
    exact
      (positiveSupport_accept_predicateVocabularyEvidence_iff
        (Base := Base) (Const := Const) M σ decode obj q).1 <|
        h obj <|
          (positiveSupport_accept_predicateVocabularyEvidence_iff
            (Base := Base) (Const := Const) M σ decode obj p).2 hp
  · intro h obj hp
    exact
      (positiveSupport_accept_predicateVocabularyEvidence_iff
        (Base := Base) (Const := Const) M σ decode obj q).2 <|
        h obj <|
          (positiveSupport_accept_predicateVocabularyEvidence_iff
            (Base := Base) (Const := Const) M σ decode obj p).1 hp

theorem predicateVocabularyFullInheritanceStrength_eq_one_iff
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [Fintype Pred]
    (p q : Pred)
    (hsubE :
      ((predicateVocabularyInterpretation
        (Base := Base) (Const := Const) M σ decode).meaning p).extent.ncard ≠ 0)
    (hsuperI :
      ((predicateVocabularyInterpretation
        (Base := Base) (Const := Const) M σ decode).meaning q).intent.ncard ≠ 0) :
    predicateVocabularyFullInheritanceStrength
        (Base := Base) (Const := Const) M σ decode p q = 1 ↔
      (predicateVocabularyInterpretation
        (Base := Base) (Const := Const) M σ decode).Inherits p q := by
  exact
    Mettapedia.Logic.ExtensionalIntensionalDivergence.fullInheritanceStrength_eq_one_iff
      (predicateVocabularyInterpretation
        (Base := Base) (Const := Const) M σ decode) p q hsubE hsuperI

/-- The closed HOL sentence expressing predicate-level inheritance
`∀ x, p x -> q x`. -/
def predicateImpFormula
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ) :
    ClosedFormula Const :=
  .all (.imp (.app (weaken (Base := Base) (σ := σ) p) (.var .vz))
             (.app (weaken (Base := Base) (σ := σ) q) (.var .vz)))

/-- The closed HOL sentence expressing predicate-level equivalence,
`∀ x, p x -> q x` and `∀ x, q x -> p x`. This is the HOL grounding of
the PLN-2008 move from predicate equivalence to similarity. -/
def predicateIffFormula
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ) :
    ClosedFormula Const :=
  .and (predicateImpFormula (Base := Base) (Const := Const) σ p q)
       (predicateImpFormula (Base := Base) (Const := Const) σ q p)

/-- Predicate-level similarity at a pointed model, grounded as mutual
inheritance in the existing abstract-inheritance interpretation. -/
def predicateMutualInheritsAt
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ) : Prop :=
  (predicateInterpretation (Base := Base) (Const := Const) M σ).MutualInherits p q

/-- The closed HOL sentence expressing `∀ x, p x`. -/
def predicateForAllFormula
    (σ : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    ClosedFormula Const :=
  .all (.app (weaken (Base := Base) (σ := σ) p) (.var .vz))

/-- The closed HOL sentence expressing `∃ x, p x`. -/
def predicateExistsFormula
    (σ : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    ClosedFormula Const :=
  .ex (.app (weaken (Base := Base) (σ := σ) p) (.var .vz))

/-- Predicate-level inheritance in the abstract dual-inheritance sense is
exactly pointwise implication over admissible Henkin-model objects. -/
theorem predicateInterpretation_extensionalInherits_iff
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ) :
    (predicateInterpretation (Base := Base) (Const := Const) M σ).ExtensionalInherits p q ↔
      ∀ x : PredicateObject (Base := Base) (Const := Const) M σ,
        predicateHoldsAt (Base := Base) (Const := Const) M σ p x →
          predicateHoldsAt (Base := Base) (Const := Const) M σ q x := by
  classical
  have hCrisp :
      (predicateInterpretation (Base := Base) (Const := Const) M σ).ExtensionalInherits p q ↔
        ∀ x : PredicateObject (Base := Base) (Const := Const) M σ,
          EvidenceGate.positiveSupport.accept
            (predicateEvidence (Base := Base) (Const := Const) M σ x p) →
              EvidenceGate.positiveSupport.accept
                (predicateEvidence (Base := Base) (Const := Const) M σ x q) := by
    change crispExtensionalInherits EvidenceGate.positiveSupport
        (predicateEvidence (Base := Base) (Const := Const) M σ) p q ↔
      ∀ x : PredicateObject (Base := Base) (Const := Const) M σ,
        EvidenceGate.positiveSupport.accept
          (predicateEvidence (Base := Base) (Const := Const) M σ x p) →
            EvidenceGate.positiveSupport.accept
              (predicateEvidence (Base := Base) (Const := Const) M σ x q)
    exact crispExtensionalInherits_iff
      EvidenceGate.positiveSupport
      (predicateEvidence (Base := Base) (Const := Const) M σ) p q
  rw [hCrisp]
  constructor
  · intro h x hx
    exact
      (positiveSupport_accept_predicateEvidence_iff
        (Base := Base) (Const := Const) M σ x q).1 <|
        h x <|
          (positiveSupport_accept_predicateEvidence_iff
            (Base := Base) (Const := Const) M σ x p).2 hx
  · intro h x hx
    exact
      (positiveSupport_accept_predicateEvidence_iff
        (Base := Base) (Const := Const) M σ x q).2 <|
        h x <|
          (positiveSupport_accept_predicateEvidence_iff
            (Base := Base) (Const := Const) M σ x p).1 hx

/-- Because the unary-predicate interpretation is generated as a crisp concept
family, full dual inheritance collapses to the same pointwise implication test. -/
theorem predicateInterpretation_inherits_iff
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ) :
    (predicateInterpretation (Base := Base) (Const := Const) M σ).Inherits p q ↔
      ∀ x : PredicateObject (Base := Base) (Const := Const) M σ,
        predicateHoldsAt (Base := Base) (Const := Const) M σ p x →
          predicateHoldsAt (Base := Base) (Const := Const) M σ q x := by
  classical
  have hCrisp :
      (predicateInterpretation (Base := Base) (Const := Const) M σ).Inherits p q ↔
        ∀ x : PredicateObject (Base := Base) (Const := Const) M σ,
          EvidenceGate.positiveSupport.accept
            (predicateEvidence (Base := Base) (Const := Const) M σ x p) →
              EvidenceGate.positiveSupport.accept
                (predicateEvidence (Base := Base) (Const := Const) M σ x q) := by
    exact
      (crispInterpretation_inherits_iff
        EvidenceGate.positiveSupport
        (predicateEvidence (Base := Base) (Const := Const) M σ) p q).trans
          (crispExtensionalInherits_iff
            EvidenceGate.positiveSupport
            (predicateEvidence (Base := Base) (Const := Const) M σ) p q)
  rw [hCrisp]
  constructor
  · intro h x hx
    exact
      (positiveSupport_accept_predicateEvidence_iff
        (Base := Base) (Const := Const) M σ x q).1 <|
        h x <|
          (positiveSupport_accept_predicateEvidence_iff
            (Base := Base) (Const := Const) M σ x p).2 hx
  · intro h x hx
    exact
      (positiveSupport_accept_predicateEvidence_iff
        (Base := Base) (Const := Const) M σ x q).2 <|
        h x <|
          (positiveSupport_accept_predicateEvidence_iff
            (Base := Base) (Const := Const) M σ x p).1 hx

/-- The HOL sentence `∀ x, p x -> q x` is satisfied exactly when the induced
abstract-inheritance interpretation validates predicate inheritance. -/
theorem models_predicateImpFormula_iff
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ) :
    HenkinModel.models M (predicateImpFormula (Base := Base) (Const := Const) σ p q) ↔
      ∀ x : PredicateObject (Base := Base) (Const := Const) M σ,
        predicateHoldsAt (Base := Base) (Const := Const) M σ p x →
          predicateHoldsAt (Base := Base) (Const := Const) M σ q x := by
  constructor
  · intro h x
    have hall :
        ∀ y : Ty.denote M.Carrier σ, M.adm σ y →
          (HenkinModel.denote M
              (.imp (.app (weaken (Base := Base) (σ := σ) p) (.var .vz))
                    (.app (weaken (Base := Base) (σ := σ) q) (.var .vz)))
              (HenkinModel.extend M (closedValuation M) y)).down := by
      change ∀ y : Ty.denote M.Carrier σ, M.adm σ y →
        (HenkinModel.denote M
          (.imp (.app (weaken (Base := Base) (σ := σ) p) (.var .vz))
                (.app (weaken (Base := Base) (σ := σ) q) (.var .vz)))
          (HenkinModel.extend M (closedValuation M) y)).down at h
      exact h
    have hx := hall x.1 x.2
    simpa [predicateHoldsAt, closedValuation] using hx
  · intro h
    have hall :
        ∀ y : Ty.denote M.Carrier σ, M.adm σ y →
          (HenkinModel.denote M
              (.imp (.app (weaken (Base := Base) (σ := σ) p) (.var .vz))
                    (.app (weaken (Base := Base) (σ := σ) q) (.var .vz)))
              (HenkinModel.extend M (closedValuation M) y)).down := by
      intro y hy
      have hy' := h ⟨y, hy⟩
      simpa [predicateHoldsAt, closedValuation] using hy'
    change HenkinModel.models M (predicateImpFormula (Base := Base) (Const := Const) σ p q)
    exact hall

/-- The higher-order inheritance bridge lands exactly on the existing abstract
inheritance layer. -/
theorem predicateInterpretation_inherits_iff_models_predicateImpFormula
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ) :
    (predicateInterpretation (Base := Base) (Const := Const) M σ).Inherits p q ↔
      HenkinModel.models M (predicateImpFormula (Base := Base) (Const := Const) σ p q) := by
  rw [predicateInterpretation_inherits_iff, models_predicateImpFormula_iff]

/-- Predicate-level higher-order inheritance composes through the existing
abstract-inheritance transitivity law. This is the crisp chain rule at the
satisfying-set bridge: no new predicate-only semantics are introduced. -/
theorem predicateInterpretation_inherits_trans
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (p q r : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hpq :
      (predicateInterpretation (Base := Base) (Const := Const) M σ).Inherits p q)
    (hqr :
      (predicateInterpretation (Base := Base) (Const := Const) M σ).Inherits q r) :
    (predicateInterpretation (Base := Base) (Const := Const) M σ).Inherits p r := by
  exact
    (predicateInterpretation (Base := Base) (Const := Const) M σ).inherits_trans
      hpq hqr

/-- Semantic predicate implication is transitive at the model level. This is
the HOL-facing form of the higher-order inheritance chain rule. -/
theorem models_predicateImpFormula_trans
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (p q r : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hpq : HenkinModel.models M
      (predicateImpFormula (Base := Base) (Const := Const) σ p q))
    (hqr : HenkinModel.models M
      (predicateImpFormula (Base := Base) (Const := Const) σ q r)) :
    HenkinModel.models M
      (predicateImpFormula (Base := Base) (Const := Const) σ p r) := by
  have hpqInh :
      (predicateInterpretation (Base := Base) (Const := Const) M σ).Inherits p q :=
    (predicateInterpretation_inherits_iff_models_predicateImpFormula
      (Base := Base) (Const := Const) M σ p q).2 hpq
  have hqrInh :
      (predicateInterpretation (Base := Base) (Const := Const) M σ).Inherits q r :=
    (predicateInterpretation_inherits_iff_models_predicateImpFormula
      (Base := Base) (Const := Const) M σ q r).2 hqr
  exact
    (predicateInterpretation_inherits_iff_models_predicateImpFormula
      (Base := Base) (Const := Const) M σ p r).1 <|
      predicateInterpretation_inherits_trans
        (Base := Base) (Const := Const) M σ p q r hpqInh hqrInh

/-- Full predicate-inheritance strength saturates exactly at the model-level
HOL predicate-implication sentence. This is the strength-valued form of the
PLN-2008 satisfying-set reduction: unary predicate inheritance is evaluated by
the existing extensional/intensional inheritance strength, then identified with
`∀ x, p x -> q x` in the Henkin model. -/
theorem predicateFullInheritanceStrength_eq_one_iff_models_predicateImpFormula
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [Fintype (UnaryPredicate (Base := Base) (Const := Const) σ)]
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hsubE :
      ((predicateInterpretation (Base := Base) (Const := Const) M σ).meaning p).extent.ncard ≠ 0)
    (hsuperI :
      ((predicateInterpretation (Base := Base) (Const := Const) M σ).meaning q).intent.ncard ≠ 0) :
    predicateFullInheritanceStrength (Base := Base) (Const := Const) M σ p q = 1 ↔
      HenkinModel.models M (predicateImpFormula (Base := Base) (Const := Const) σ p q) := by
  exact
    (predicateFullInheritanceStrength_eq_one_iff
      (Base := Base) (Const := Const) M σ p q hsubE hsuperI).trans
      (predicateInterpretation_inherits_iff_models_predicateImpFormula
        (Base := Base) (Const := Const) M σ p q)

/-- Maximal full predicate inheritance composes. This is the first crisp
strength-valued HO deduction/chain rule: two saturated predicate-inheritance
links yield a saturated composite link, with all nonempty-support assumptions
kept explicit rather than hidden in the arithmetic. -/
theorem predicateFullInheritanceStrength_eq_one_of_chain
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [Fintype (UnaryPredicate (Base := Base) (Const := Const) σ)]
    (p q r : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hpExtent :
      ((predicateInterpretation (Base := Base) (Const := Const) M σ).meaning p).extent.ncard ≠ 0)
    (hqIntent :
      ((predicateInterpretation (Base := Base) (Const := Const) M σ).meaning q).intent.ncard ≠ 0)
    (hqExtent :
      ((predicateInterpretation (Base := Base) (Const := Const) M σ).meaning q).extent.ncard ≠ 0)
    (hrIntent :
      ((predicateInterpretation (Base := Base) (Const := Const) M σ).meaning r).intent.ncard ≠ 0)
    (hpq :
      predicateFullInheritanceStrength (Base := Base) (Const := Const) M σ p q = 1)
    (hqr :
      predicateFullInheritanceStrength (Base := Base) (Const := Const) M σ q r = 1) :
    predicateFullInheritanceStrength (Base := Base) (Const := Const) M σ p r = 1 := by
  have hpqModels :
      HenkinModel.models M
        (predicateImpFormula (Base := Base) (Const := Const) σ p q) :=
    (predicateFullInheritanceStrength_eq_one_iff_models_predicateImpFormula
      (Base := Base) (Const := Const) M σ p q hpExtent hqIntent).1 hpq
  have hqrModels :
      HenkinModel.models M
        (predicateImpFormula (Base := Base) (Const := Const) σ q r) :=
    (predicateFullInheritanceStrength_eq_one_iff_models_predicateImpFormula
      (Base := Base) (Const := Const) M σ q r hqExtent hrIntent).1 hqr
  exact
    (predicateFullInheritanceStrength_eq_one_iff_models_predicateImpFormula
      (Base := Base) (Const := Const) M σ p r hpExtent hrIntent).2 <|
      models_predicateImpFormula_trans
        (Base := Base) (Const := Const) M σ p q r hpqModels hqrModels

/-- A finite working predicate vocabulary inherits exactly when the decoded HOL
predicate-implication formula holds in the model. This is the finite-vocabulary
version of the PLN-2008 satisfying-set reduction. -/
theorem predicateVocabularyInterpretation_inherits_iff_models_predicateImpFormula
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    (p q : Pred) :
    (predicateVocabularyInterpretation
      (Base := Base) (Const := Const) M σ decode).Inherits p q ↔
      HenkinModel.models M
        (predicateImpFormula (Base := Base) (Const := Const) σ (decode p) (decode q)) := by
  rw [predicateVocabularyInterpretation_inherits_iff,
    models_predicateImpFormula_iff]

/-- On a finite working predicate vocabulary, strength `1` is exactly the
model-level HOL predicate implication between the decoded predicates, under the
same nonempty-support hypotheses as the base full-strength theorem. -/
theorem predicateVocabularyFullInheritanceStrength_eq_one_iff_models_predicateImpFormula
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [Fintype Pred]
    (p q : Pred)
    (hsubE :
      ((predicateVocabularyInterpretation
        (Base := Base) (Const := Const) M σ decode).meaning p).extent.ncard ≠ 0)
    (hsuperI :
      ((predicateVocabularyInterpretation
        (Base := Base) (Const := Const) M σ decode).meaning q).intent.ncard ≠ 0) :
    predicateVocabularyFullInheritanceStrength
        (Base := Base) (Const := Const) M σ decode p q = 1 ↔
      HenkinModel.models M
        (predicateImpFormula (Base := Base) (Const := Const) σ (decode p) (decode q)) := by
  exact
    (predicateVocabularyFullInheritanceStrength_eq_one_iff
      (Base := Base) (Const := Const) M σ decode p q hsubE hsuperI).trans
      (predicateVocabularyInterpretation_inherits_iff_models_predicateImpFormula
        (Base := Base) (Const := Const) M σ decode p q)

/-- Maximal full inheritance also composes in a finite active predicate
vocabulary. This is the systems-facing chain rule: finite vocabulary items
decode to HOL predicates, while the scoring and transitivity remain the shared
abstract extensional/intensional inheritance machinery. -/
theorem predicateVocabularyFullInheritanceStrength_eq_one_of_chain
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    {Pred : Type x}
    (decode : Pred → UnaryPredicate (Base := Base) (Const := Const) σ)
    [Fintype (PredicateObject (Base := Base) (Const := Const) M σ)]
    [Fintype Pred]
    (p q r : Pred)
    (hpExtent :
      ((predicateVocabularyInterpretation
        (Base := Base) (Const := Const) M σ decode).meaning p).extent.ncard ≠ 0)
    (hqIntent :
      ((predicateVocabularyInterpretation
        (Base := Base) (Const := Const) M σ decode).meaning q).intent.ncard ≠ 0)
    (hqExtent :
      ((predicateVocabularyInterpretation
        (Base := Base) (Const := Const) M σ decode).meaning q).extent.ncard ≠ 0)
    (hrIntent :
      ((predicateVocabularyInterpretation
        (Base := Base) (Const := Const) M σ decode).meaning r).intent.ncard ≠ 0)
    (hpq :
      predicateVocabularyFullInheritanceStrength
        (Base := Base) (Const := Const) M σ decode p q = 1)
    (hqr :
      predicateVocabularyFullInheritanceStrength
        (Base := Base) (Const := Const) M σ decode q r = 1) :
    predicateVocabularyFullInheritanceStrength
      (Base := Base) (Const := Const) M σ decode p r = 1 := by
  have hpqModels :
      HenkinModel.models M
        (predicateImpFormula (Base := Base) (Const := Const) σ (decode p) (decode q)) :=
    (predicateVocabularyFullInheritanceStrength_eq_one_iff_models_predicateImpFormula
      (Base := Base) (Const := Const) M σ decode p q hpExtent hqIntent).1 hpq
  have hqrModels :
      HenkinModel.models M
        (predicateImpFormula (Base := Base) (Const := Const) σ (decode q) (decode r)) :=
    (predicateVocabularyFullInheritanceStrength_eq_one_iff_models_predicateImpFormula
      (Base := Base) (Const := Const) M σ decode q r hqExtent hrIntent).1 hqr
  exact
    (predicateVocabularyFullInheritanceStrength_eq_one_iff_models_predicateImpFormula
      (Base := Base) (Const := Const) M σ decode p r hpExtent hrIntent).2 <|
      models_predicateImpFormula_trans
        (Base := Base) (Const := Const) M σ (decode p) (decode q) (decode r)
        hpqModels hqrModels

/-- Predicate-level equivalence/similarity in HOL is exactly mutual inheritance
in the existing abstract-inheritance layer. -/
theorem predicateMutualInheritsAt_iff_models_predicateIffFormula
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ) :
    predicateMutualInheritsAt (Base := Base) (Const := Const) M σ p q ↔
      HenkinModel.models M (predicateIffFormula (Base := Base) (Const := Const) σ p q) := by
  constructor
  · intro h
    exact (HenkinModel.models_and M).2
      ⟨(predicateInterpretation_inherits_iff_models_predicateImpFormula
          (Base := Base) (Const := Const) M σ p q).1 h.1,
       (predicateInterpretation_inherits_iff_models_predicateImpFormula
          (Base := Base) (Const := Const) M σ q p).1 h.2⟩
  · intro h
    have hpairs := (HenkinModel.models_and M).1 h
    exact
      ⟨(predicateInterpretation_inherits_iff_models_predicateImpFormula
          (Base := Base) (Const := Const) M σ p q).2 hpairs.1,
       (predicateInterpretation_inherits_iff_models_predicateImpFormula
          (Base := Base) (Const := Const) M σ q p).2 hpairs.2⟩

/-- The HOL sentence `∀ x, p x` is satisfied exactly when the predicate holds
of every admissible Henkin-model object. -/
theorem models_predicateForAllFormula_iff
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    HenkinModel.models M (predicateForAllFormula (Base := Base) (Const := Const) σ p) ↔
      ∀ x : PredicateObject (Base := Base) (Const := Const) M σ,
        predicateHoldsAt (Base := Base) (Const := Const) M σ p x := by
  constructor
  · intro h x
    have hall :
        ∀ y : Ty.denote M.Carrier σ, M.adm σ y →
          (HenkinModel.denote M
              (.app (weaken (Base := Base) (σ := σ) p) (.var .vz))
              (HenkinModel.extend M (closedValuation M) y)).down := by
      change ∀ y : Ty.denote M.Carrier σ, M.adm σ y →
        (HenkinModel.denote M
          (.app (weaken (Base := Base) (σ := σ) p) (.var .vz))
          (HenkinModel.extend M (closedValuation M) y)).down at h
      exact h
    simpa [predicateHoldsAt, closedValuation] using hall x.1 x.2
  · intro h
    have hall :
        ∀ y : Ty.denote M.Carrier σ, M.adm σ y →
          (HenkinModel.denote M
              (.app (weaken (Base := Base) (σ := σ) p) (.var .vz))
              (HenkinModel.extend M (closedValuation M) y)).down := by
      intro y hy
      simpa [predicateHoldsAt, closedValuation] using h ⟨y, hy⟩
    change HenkinModel.models M (predicateForAllFormula (Base := Base) (Const := Const) σ p)
    exact hall

/-- The HOL sentence `∃ x, p x` is satisfied exactly when the predicate holds
of some admissible Henkin-model object. -/
theorem models_predicateExistsFormula_iff
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    HenkinModel.models M (predicateExistsFormula (Base := Base) (Const := Const) σ p) ↔
      ∃ x : PredicateObject (Base := Base) (Const := Const) M σ,
        predicateHoldsAt (Base := Base) (Const := Const) M σ p x := by
  constructor
  · intro h
    have hex :
        ∃ y : Ty.denote M.Carrier σ, M.adm σ y ∧
          (HenkinModel.denote M
              (.app (weaken (Base := Base) (σ := σ) p) (.var .vz))
              (HenkinModel.extend M (closedValuation M) y)).down := by
      change ∃ y : Ty.denote M.Carrier σ, M.adm σ y ∧
        (HenkinModel.denote M
          (.app (weaken (Base := Base) (σ := σ) p) (.var .vz))
          (HenkinModel.extend M (closedValuation M) y)).down at h
      exact h
    rcases hex with ⟨y, hy, hp⟩
    exact ⟨⟨y, hy⟩, by simpa [predicateHoldsAt, closedValuation] using hp⟩
  · intro h
    rcases h with ⟨x, hp⟩
    have hex :
        ∃ y : Ty.denote M.Carrier σ, M.adm σ y ∧
          (HenkinModel.denote M
              (.app (weaken (Base := Base) (σ := σ) p) (.var .vz))
              (HenkinModel.extend M (closedValuation M) y)).down :=
      ⟨x.1, x.2, by simpa [predicateHoldsAt, closedValuation] using hp⟩
    change HenkinModel.models M (predicateExistsFormula (Base := Base) (Const := Const) σ p)
    exact hex

/-- Predicate inheritance transports universal predicate truth: if every `p`
object satisfies `q`, then `∀x p x` implies `∀x q x`. -/
theorem predicateForAll_mono_of_inherits
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hInh :
      (predicateInterpretation (Base := Base) (Const := Const) M σ).Inherits p q)
    (hAll : HenkinModel.models M
      (predicateForAllFormula (Base := Base) (Const := Const) σ p)) :
    HenkinModel.models M
      (predicateForAllFormula (Base := Base) (Const := Const) σ q) := by
  have hPoint :=
    (predicateInterpretation_inherits_iff
      (Base := Base) (Const := Const) M σ p q).1 hInh
  exact
    (models_predicateForAllFormula_iff
      (Base := Base) (Const := Const) M σ q).2 <|
      fun x =>
        hPoint x <|
          (models_predicateForAllFormula_iff
            (Base := Base) (Const := Const) M σ p).1 hAll x

/-- Predicate inheritance transports existential predicate truth: a witness for
`p` is also a witness for `q`. -/
theorem predicateExists_mono_of_inherits
    (M : HenkinModel.{u, v, w} Base Const)
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (hInh :
      (predicateInterpretation (Base := Base) (Const := Const) M σ).Inherits p q)
    (hExists : HenkinModel.models M
      (predicateExistsFormula (Base := Base) (Const := Const) σ p)) :
    HenkinModel.models M
      (predicateExistsFormula (Base := Base) (Const := Const) σ q) := by
  have hPoint :=
    (predicateInterpretation_inherits_iff
      (Base := Base) (Const := Const) M σ p q).1 hInh
  rcases
    (models_predicateExistsFormula_iff
      (Base := Base) (Const := Const) M σ p).1 hExists with
    ⟨x, hx⟩
  exact
    (models_predicateExistsFormula_iff
      (Base := Base) (Const := Const) M σ q).2
      ⟨x, hPoint x hx⟩

/-- Reflexive predicate inheritance is provable directly in HOL. -/
theorem holProvable_predicateImpFormula_refl
    (σ : Ty Base)
    (p : UnaryPredicate (Base := Base) (Const := Const) σ) :
    Mettapedia.Logic.PLNHigherOrderHOLCore.HOLProvable
      (Const := Const) (predicateImpFormula (Base := Base) (Const := Const) σ p p) :=
  .allI (.impI (.hyp (by simp)))

/-- A proved HOL predicate-inheritance sentence induces higher-order abstract
inheritance at every pointed Henkin model. -/
theorem holProvable_predicateImpFormula_implies_inherits
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (h :
      Mettapedia.Logic.PLNHigherOrderHOLCore.HOLProvable
        (Const := Const) (predicateImpFormula (Base := Base) (Const := Const) σ p q)) :
    ∀ M : HenkinModel.{u, v, w} Base Const,
      (predicateInterpretation (Base := Base) (Const := Const) M σ).Inherits p q := by
  intro M
  exact
    (predicateInterpretation_inherits_iff_models_predicateImpFormula
      (Base := Base) (Const := Const) M σ p q).2 <|
      Mettapedia.Logic.PLNHigherOrderHOLSoundness.holProvable_models
        (Base := Base) (Const := Const) h M

/-- A proved HOL predicate-equivalence sentence induces predicate-level
similarity, represented here by mutual inheritance, at every pointed Henkin
model. -/
theorem holProvable_predicateIffFormula_implies_mutualInherits
    (σ : Ty Base)
    (p q : UnaryPredicate (Base := Base) (Const := Const) σ)
    (h :
      Mettapedia.Logic.PLNHigherOrderHOLCore.HOLProvable
        (Const := Const) (predicateIffFormula (Base := Base) (Const := Const) σ p q)) :
    ∀ M : HenkinModel.{u, v, w} Base Const,
      predicateMutualInheritsAt (Base := Base) (Const := Const) M σ p q := by
  intro M
  exact
    (predicateMutualInheritsAt_iff_models_predicateIffFormula
      (Base := Base) (Const := Const) M σ p q).2 <|
      Mettapedia.Logic.PLNHigherOrderHOLSoundness.holProvable_models
        (Base := Base) (Const := Const) h M

end Mettapedia.Logic.PLNHigherOrderHOLInheritanceBridge
