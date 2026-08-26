import Mettapedia.Enactive.Finite
import Mettapedia.Algebra.QuantaleWeakness
import Mathlib.Tactic.DeriveFintype

/-!
# Constrained selection profiles: Bennett, Ockham, and quantale weakness

There is no single mathematically canonical quantity called "simplicity".
Modern razors use importantly different comparison data:

* William of Ockham's historical principle is ontological parsimony under a
  necessity proviso, not the popular claim that the simplest theory is true.
* Rissanen's MDL (*Modeling by Shortest Data Description*, 1978) minimizes a
  code for model and data; Wallace and Boulton's MML (*An Information Measure
  for Classification*, 1968) derives a related two-part message criterion.
* Solomonoff (*A Formal Theory of Inductive Inference*, 1964) weights outputs
  by prefix-programs; MacKay (*Bayesian Interpolation*, 1992) selects by
  marginal likelihood and its evidence-volume penalty; Vapnik (*Principles of
  Risk Minimization for Learning Theory*, 1991) minimizes empirical risk plus
  a capacity-dependent confidence term.
* Michael Timothy Bennett's Bennett's Razor (*The Optimal Choice of Hypothesis
  Is the Weakest, Not the Shortest*, 2023) maximizes the number of semantic
  completions among correct hypotheses: explanations should be no more
  specific than necessary.
* Ben Goertzel's *Weakness Is All You Need: Quantale Weakness as a Unifying
  Principle for Cognition* (2026) replaces a single numerical range by
  quantale-valued relation scores while making their layer-relative valuation
  explicit.

The common abstraction below therefore retains only what all these methods
actually share: an admissible fibre and a preorder of preference.  It does not
force a scalar, a total order, a probability interpretation, or quantale
composition.  Those are additional profiles.  Products retain disagreement
as incomparability instead of silently choosing a scalarization.

The same construction is applied reflexively to formalization design.  A
formalization is at least as permissive as another when it admits every model
the other admits, provided it satisfies the named adequacy obligations.  This
is Bennett's semantic least-commitment principle at the metatheory level.  A
finite cardinality is only a lossy readout of that model-class order.
-/

set_option autoImplicit false

namespace Mettapedia.Enactive.Razor

universe uCandidate uModel uObligation uScore uWorld

/-! ## The weakest common interface -/

/-- A constrained selection criterion.  `atLeastAsGood left right` means that
`left` is at least as preferred as `right`.  Only a preorder is required, so
ties and incomparable candidates remain representable. -/
structure Criterion (Candidate : Type uCandidate) where
  admissible : Candidate → Prop
  atLeastAsGood : Candidate → Candidate → Prop
  refl : ∀ candidate, atLeastAsGood candidate candidate
  trans : ∀ {first second third},
    atLeastAsGood first second →
      atLeastAsGood second third →
        atLeastAsGood first third

namespace Criterion

variable {Candidate : Type uCandidate}

/-- A globally optimal candidate dominates every admissible candidate. -/
def IsOptimal (criterion : Criterion Candidate) (candidate : Candidate) : Prop :=
  criterion.admissible candidate ∧
    ∀ other, criterion.admissible other →
      criterion.atLeastAsGood candidate other

/-- A maximal candidate has no strictly dominating admissible competitor.
Unlike `IsOptimal`, maximality does not assume that all admissible candidates
are mutually comparable. -/
def IsMaximal (criterion : Criterion Candidate) (candidate : Candidate) : Prop :=
  criterion.admissible candidate ∧
    ¬ ∃ other, criterion.admissible other ∧
      criterion.atLeastAsGood other candidate ∧
      ¬ criterion.atLeastAsGood candidate other

theorem IsOptimal.isMaximal {criterion : Criterion Candidate}
    {candidate : Candidate} (optimal : criterion.IsOptimal candidate) :
    criterion.IsMaximal candidate := by
  refine ⟨optimal.1, ?_⟩
  rintro ⟨other, otherAdmissible, _, notReverse⟩
  exact notReverse (optimal.2 other otherAdmissible)

/-- Maximize a preorder-valued benefit. -/
def ofBenefit {Score : Type uScore} [Preorder Score]
    (admissible : Candidate → Prop) (score : Candidate → Score) :
    Criterion Candidate where
  admissible := admissible
  atLeastAsGood := fun left right => score right ≤ score left
  refl := fun _ => le_rfl
  trans := fun firstSecond secondThird => secondThird.trans firstSecond

/-- Minimize a preorder-valued cost. -/
def ofCost {Score : Type uScore} [Preorder Score]
    (admissible : Candidate → Prop) (cost : Candidate → Score) :
    Criterion Candidate where
  admissible := admissible
  atLeastAsGood := fun left right => cost left ≤ cost right
  refl := fun _ => le_rfl
  trans := fun firstSecond secondThird => firstSecond.trans secondThird

/-- Conjunction of independent profiles.  This is the Pareto/product order:
neither axis is assigned an arbitrary exchange rate. -/
def product (left right : Criterion Candidate) : Criterion Candidate where
  admissible := fun candidate =>
    left.admissible candidate ∧ right.admissible candidate
  atLeastAsGood := fun first second =>
    left.atLeastAsGood first second ∧
      right.atLeastAsGood first second
  refl := fun candidate => ⟨left.refl candidate, right.refl candidate⟩
  trans := fun firstSecond secondThird =>
    ⟨left.trans firstSecond.1 secondThird.1,
      right.trans firstSecond.2 secondThird.2⟩

@[simp]
theorem product_admissible (left right : Criterion Candidate)
    (candidate : Candidate) :
    (left.product right).admissible candidate ↔
      left.admissible candidate ∧ right.admissible candidate :=
  Iff.rfl

@[simp]
theorem product_atLeastAsGood (left right : Criterion Candidate)
    (first second : Candidate) :
    (left.product right).atLeastAsGood first second ↔
      left.atLeastAsGood first second ∧
        right.atLeastAsGood first second :=
  Iff.rfl

end Criterion

/-! ## Standard razor profiles -/

/-- Ontological Ockham profile: among candidates satisfying the same necessity
predicate, prefer the one positing fewer entities. -/
def ontologicalParsimony {Candidate : Type uCandidate}
    (necessary : Candidate → Prop) (entityCount : Candidate → ℕ) :
    Criterion Candidate :=
  Criterion.ofCost necessary entityCount

/-- Syntactic-description profile.  The description language is an explicit
argument because length is representation-relative. -/
def descriptionLength {Candidate : Type uCandidate}
    (adequate : Candidate → Prop) (encodedLength : Candidate → ℕ) :
    Criterion Candidate :=
  Criterion.ofCost adequate encodedLength

/-- Two-part coding profile shared at this abstraction level by early MDL and
MML: minimize the transmitted model/assertion plus the data encoded with it.
The probability and coding premises that derive the two terms remain external
and must not be inferred from this sum. -/
def twoPartCode {Candidate : Type uCandidate}
    (adequate : Candidate → Prop)
    (modelMessage dataGivenModelMessage : Candidate → ℕ) :
    Criterion Candidate :=
  Criterion.ofCost adequate fun candidate =>
    modelMessage candidate + dataGivenModelMessage candidate

/-- Bayesian evidence profile: maximize a marginal-likelihood score. -/
def bayesianEvidence {Candidate : Type uCandidate}
    {Score : Type uScore} [Preorder Score]
    (adequate : Candidate → Prop) (marginalLikelihood : Candidate → Score) :
    Criterion Candidate :=
  Criterion.ofBenefit adequate marginalLikelihood

/-- Solomonoff-shaped profile: maximize an algorithmic semimeasure or another
prefix-machine weight.  This interface does not assert computability. -/
def algorithmicWeight {Candidate : Type uCandidate}
    {Score : Type uScore} [Preorder Score]
    (adequate : Candidate → Prop) (weight : Candidate → Score) :
    Criterion Candidate :=
  Criterion.ofBenefit adequate weight

/-- Structural-risk profile: minimize empirical risk plus the certified
capacity/confidence penalty. -/
def structuralRisk {Candidate : Type uCandidate}
    (adequate : Candidate → Prop)
    (empiricalRisk confidencePenalty : Candidate → ℕ) :
    Criterion Candidate :=
  Criterion.ofCost adequate fun candidate =>
    empiricalRisk candidate + confidencePenalty candidate

/-! ## Bennett's Razor -/

namespace Bennett

variable {World : Type uWorld} [Fintype World] [DecidableEq World]

/-- Michael Timothy Bennett's finite razor: among correct policies for a task,
maximize completion-count weakness. -/
def criterion {finiteLayer : Mettapedia.Enactive.Finite.Layer World}
    (task : Mettapedia.Enactive.Finite.Task finiteLayer) :
    Criterion finiteLayer.Statement :=
  Criterion.ofBenefit task.IsCorrectPolicy finiteLayer.weakness

theorem isOptimal_iff
    {finiteLayer : Mettapedia.Enactive.Finite.Layer World}
    (task : Mettapedia.Enactive.Finite.Task finiteLayer)
    (policy : finiteLayer.Statement) :
    (criterion task).IsOptimal policy ↔
      task.IsCorrectPolicy policy ∧
        ∀ other, task.IsCorrectPolicy other →
          finiteLayer.weakness other ≤ finiteLayer.weakness policy :=
  Iff.rfl

/-- Inclusion of completion sets is a sufficient, more informative witness
for the cardinal Bennett comparison.  The converse fails in general because
equal cardinalities can conceal incomparable completion sets. -/
theorem extension_subset_implies_atLeastAsGood
    {finiteLayer : Mettapedia.Enactive.Finite.Layer World}
    (task : Mettapedia.Enactive.Finite.Task finiteLayer)
    {left right : finiteLayer.Statement}
    (included : finiteLayer.extension right ⊆ finiteLayer.extension left) :
    (criterion task).atLeastAsGood left right :=
  Finset.card_le_card included

end Bennett

/-! ## Goertzel's quantale-valued relation profile -/

namespace Goertzel

open Mettapedia.Algebra.QuantaleWeakness

variable {U : Type uWorld} [Fintype U]
variable {Q : Type uScore} [Monoid Q] [CompleteLattice Q] [IsQuantale Q]

/-- A quantale-valued Razor over finite relation events, using the weakness
construction from `QuantaleWeakness`.  The order of `Q` determines the
preference direction; an order dual must be supplied explicitly for a
cost-minimizing interpretation. -/
noncomputable def criterion (weight : WeightFunction U Q)
    (admissible : Finset (U × U) → Prop) :
    Criterion (Finset (U × U)) :=
  Criterion.ofBenefit admissible (weakness weight)

omit [IsQuantale Q] in
/-- Relation inclusion is always weakly preferred by the quantale profile.
This is the compositional generalization's core monotonicity law. -/
theorem inclusion_implies_atLeastAsGood
    (weight : WeightFunction U Q)
    (admissible : Finset (U × U) → Prop)
    {small large : Finset (U × U)} (included : small ⊆ large) :
    (criterion weight admissible).atLeastAsGood large small :=
  weakness_mono weight small large included

end Goertzel

/-! ## Reflexive application: least-committing formalizations -/

/-- A design space of formalizations, their semantic models, and the explicit
obligations that make a candidate adequate for the intended task. -/
structure FormalizationSpace
    (Candidate : Type uCandidate) (Model : Type uModel)
    (Obligation : Type uObligation) where
  models : Candidate → Set Model
  satisfies : Candidate → Obligation → Prop
  required : Set Obligation

namespace FormalizationSpace

variable {Candidate : Type uCandidate} {Model : Type uModel}
variable {Obligation : Type uObligation}

/-- Adequacy is external semantic evidence, not a Boolean attached by the
candidate formalization itself. -/
def Admissible (space : FormalizationSpace Candidate Model Obligation)
    (candidate : Candidate) : Prop :=
  ∀ obligation ∈ space.required, space.satisfies candidate obligation

/-- The semantic least-commitment criterion.  A candidate is preferred when
its model class contains the other's model class. -/
def semanticCriterion
    (space : FormalizationSpace Candidate Model Obligation) :
    Criterion Candidate where
  admissible := space.Admissible
  atLeastAsGood := fun left right => space.models right ⊆ space.models left
  refl := fun _ => Set.Subset.rfl
  trans := fun firstSecond secondThird => secondThird.trans firstSecond

/-- Exact meaning of "most permissive formalization": it satisfies every
required obligation and contains the model class of every other adequate
candidate. -/
theorem isOptimal_semanticCriterion_iff
    (space : FormalizationSpace Candidate Model Obligation)
    (candidate : Candidate) :
    space.semanticCriterion.IsOptimal candidate ↔
      space.Admissible candidate ∧
        ∀ other, space.Admissible other →
          space.models other ⊆ space.models candidate :=
  Iff.rfl

end FormalizationSpace

/-! ## Finite readout and its information loss -/

namespace FiniteReadout

variable {Candidate : Type uCandidate} {Model : Type uModel}
variable [DecidableEq Model]

/-- Informative finite semantic order by actual model-set inclusion. -/
def semanticCriterion (admissible : Candidate → Prop)
    (models : Candidate → Finset Model) : Criterion Candidate where
  admissible := admissible
  atLeastAsGood := fun left right => models right ⊆ models left
  refl := fun _ => Finset.Subset.rfl
  trans := fun firstSecond secondThird => secondThird.trans firstSecond

/-- Bennett cardinality as a scalar readout of finite model freedom. -/
def cardinalityCriterion (admissible : Candidate → Prop)
    (models : Candidate → Finset Model) : Criterion Candidate :=
  Criterion.ofBenefit admissible fun candidate => (models candidate).card

omit [DecidableEq Model] in
/-- Model-set inclusion always descends to the cardinality comparison. -/
theorem semantic_implies_cardinality
    (admissible : Candidate → Prop) (models : Candidate → Finset Model)
    {left right : Candidate}
    (preferred :
      (semanticCriterion admissible models).atLeastAsGood left right) :
    (cardinalityCriterion admissible models).atLeastAsGood left right :=
  Finset.card_le_card preferred

end FiniteReadout

/-! ## Positive and negative controls -/

namespace FormalizationCanary

inductive Candidate where
  | noCommitments
  | adequate
  | wrongOnly
  | inconsistent
deriving DecidableEq, Fintype

inductive Obligation where
  | rulesOutFalse
deriving DecidableEq, Fintype

def models : Candidate → Finset Bool
  | .noCommitments => Finset.univ
  | .adequate => {true}
  | .wrongOnly => {false}
  | .inconsistent => ∅

def space : FormalizationSpace Candidate Bool Obligation where
  models := fun candidate => models candidate
  satisfies := fun candidate obligation => match obligation with
    | .rulesOutFalse => false ∉ models candidate
  required := Set.univ

/-- Positive self-application: the adequate candidate is the most permissive
one that still rules out the prohibited model.  The inconsistent candidate
also rules it out, but makes an unnecessary additional commitment. -/
theorem adequate_is_mostPermissive :
    space.semanticCriterion.IsOptimal .adequate := by
  constructor
  · intro obligation _
    cases obligation
    simp [space, models]
  · intro other otherAdmissible
    change space.models other ⊆ space.models .adequate
    cases other with
    | noCommitments =>
        have impossible := otherAdmissible .rulesOutFalse (Set.mem_univ _)
        simp [space, models] at impossible
    | adequate => exact Set.Subset.rfl
    | wrongOnly =>
        have impossible := otherAdmissible .rulesOutFalse (Set.mem_univ _)
        simp [space, models] at impossible
    | inconsistent => simp [space, models]

/-- The empty/no-commitment specification is not automatically selected: it
admits a model forbidden by the adequacy obligation. -/
theorem noCommitments_not_admissible :
    ¬ space.Admissible .noCommitments := by
  intro admissible
  have excludesFalse := admissible .rulesOutFalse (Set.mem_univ _)
  simp [space, models] at excludesFalse

/-- A contradiction can satisfy a negative obligation vacuously, but it is
not weakness-optimal because an adequate candidate retains a strictly larger
model class. -/
theorem inconsistent_admissible_but_not_optimal :
    space.Admissible .inconsistent ∧
      ¬ space.semanticCriterion.IsOptimal .inconsistent := by
  constructor
  · intro obligation _
    cases obligation
    simp [space, models]
  · intro optimal
    have adequateAdmissible : space.Admissible .adequate := by
      intro obligation _
      cases obligation
      simp [space, models]
    have included := optimal.2 .adequate adequateAdmissible
    simp [FormalizationSpace.semanticCriterion, space, models] at included

/-- Negative scalar-readout control: the two singleton model classes have the
same cardinality. -/
theorem singleton_cardinality_tie :
    (FiniteReadout.cardinalityCriterion (fun _ : Candidate => True) models).atLeastAsGood
        .adequate .wrongOnly ∧
      (FiniteReadout.cardinalityCriterion (fun _ : Candidate => True) models).atLeastAsGood
        .wrongOnly .adequate := by
  simp [FiniteReadout.cardinalityCriterion, Criterion.ofBenefit, models]

/-- The informative semantic order correctly leaves the same two candidates
incomparable.  Cardinality is therefore a quotient, not the foundation. -/
theorem singleton_semantic_incomparable :
    ¬ (FiniteReadout.semanticCriterion (fun _ : Candidate => True) models).atLeastAsGood
        .adequate .wrongOnly ∧
      ¬ (FiniteReadout.semanticCriterion (fun _ : Candidate => True) models).atLeastAsGood
        .wrongOnly .adequate := by
  simp [FiniteReadout.semanticCriterion, models]

end FormalizationCanary

namespace BennettOckhamCanary

inductive Candidate where
  | weakLong
  | strongShort
deriving DecidableEq, Fintype

def completions : Candidate → Finset Bool
  | .weakLong => Finset.univ
  | .strongShort => {true}

def code : Candidate → List Bool
  | .weakLong => [false, false]
  | .strongShort => [true]

def weakness : Candidate → ℕ := fun candidate => (completions candidate).card

def weaknessRazor : Criterion Candidate :=
  Criterion.ofBenefit (fun _ => True) weakness

def codeLengthRazor : Criterion Candidate :=
  descriptionLength (fun _ => True) fun candidate => (code candidate).length

/-- The two explicit codewords are prefix-incomparable, so the length
comparison is not caused by an invalid prefix-code collision. -/
theorem codewords_prefix_incomparable :
    ¬ code .weakLong <+: code .strongShort ∧
      ¬ code .strongShort <+: code .weakLong := by
  decide

/-- Bennett's semantic criterion strictly prefers the longer candidate. -/
theorem weakness_prefers_weakLong :
    weaknessRazor.atLeastAsGood .weakLong .strongShort ∧
      ¬ weaknessRazor.atLeastAsGood .strongShort .weakLong := by
  simp [weaknessRazor, Criterion.ofBenefit, weakness, completions]

/-- The code-length Ockham profile strictly prefers the shorter candidate. -/
theorem codeLength_prefers_strongShort :
    codeLengthRazor.atLeastAsGood .strongShort .weakLong ∧
      ¬ codeLengthRazor.atLeastAsGood .weakLong .strongShort := by
  simp [codeLengthRazor, descriptionLength, Criterion.ofCost, code]

/-- The product profile retains the real disagreement as incomparability.
Thus neither Bennett nor code length globally subsumes the other. -/
theorem product_preserves_disagreement :
    ¬ (weaknessRazor.product codeLengthRazor).atLeastAsGood
        .weakLong .strongShort ∧
      ¬ (weaknessRazor.product codeLengthRazor).atLeastAsGood
        .strongShort .weakLong := by
  simp [Criterion.product, weaknessRazor, codeLengthRazor,
    descriptionLength, Criterion.ofBenefit, Criterion.ofCost,
    weakness, completions, code]

end BennettOckhamCanary

#print axioms Criterion.IsOptimal.isMaximal
#print axioms Bennett.extension_subset_implies_atLeastAsGood
#print axioms Goertzel.inclusion_implies_atLeastAsGood
#print axioms FormalizationSpace.isOptimal_semanticCriterion_iff
#print axioms FormalizationCanary.adequate_is_mostPermissive
#print axioms FormalizationCanary.inconsistent_admissible_but_not_optimal
#print axioms FormalizationCanary.singleton_semantic_incomparable
#print axioms BennettOckhamCanary.product_preserves_disagreement

end Mettapedia.Enactive.Razor
