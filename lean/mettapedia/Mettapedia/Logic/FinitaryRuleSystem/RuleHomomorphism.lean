import Mathlib.Data.List.OfFn
import Mettapedia.Logic.FinitaryRuleSystem.FiniteModel

/-!
# Translations and strict homomorphisms of finitary rule systems

Several comparison notions must not be conflated:

* a `DerivabilityTranslation` preserves closed derivability;
* a `RuleHomomorphism` maps each primitive rule instance to one primitive rule
  instance with the pointwise translated premise list;
* a `WitnessedRuleHomomorphism` additionally compiles replay witnesses and
  preserves successful replay;
* an `ExactWitnessedRuleHomomorphism` reflects the Boolean root test and does
  not collapse judgments, so complete replay results commute exactly.

Strict rule homomorphisms are intentionally narrower than interpretations by
open derivations.  Their extra locality is exactly what makes finite semantic
models pull back without assuming completeness.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.FinitaryRuleSystem

open Mettapedia.Logic

universe u v w x

variable {Source : Type u} {Target : Type v} {Third : Type w}
variable {sourceRules : List Source → Source → Prop}
variable {targetRules : List Target → Target → Prop}
variable {thirdRules : List Third → Third → Prop}

/-! ## Closed-derivability translations -/

/-- A translation of judgments that preserves closed derivability.  No claim
is made about primitive rules, models, or certificate representation. -/
structure DerivabilityTranslation
    (sourceRules : List Source → Source → Prop)
    (targetRules : List Target → Target → Prop) where
  mapJudgment : Source → Target
  map_derives : ∀ {judgment}, Derives sourceRules judgment →
    Derives targetRules (mapJudgment judgment)

namespace DerivabilityTranslation

/-- Identity preserves closed derivability. -/
def id (rules : List Source → Source → Prop) :
    DerivabilityTranslation rules rules where
  mapJudgment := fun judgment => judgment
  map_derives := fun derivation => derivation

/-- Closed-derivability translations compose. -/
def comp
    (earlier : DerivabilityTranslation sourceRules targetRules)
    (later : DerivabilityTranslation targetRules thirdRules) :
    DerivabilityTranslation sourceRules thirdRules where
  mapJudgment := later.mapJudgment ∘ earlier.mapJudgment
  map_derives := fun derivation => later.map_derives (earlier.map_derives derivation)

/-- A derivability translation is conservative when it also reflects every
translated theorem. -/
def Conservative
    (translation : DerivabilityTranslation sourceRules targetRules) : Prop :=
  ∀ judgment, Derives targetRules (translation.mapJudgment judgment) →
    Derives sourceRules judgment

/-- Identity translation is conservative. -/
theorem conservative_id (rules : List Source → Source → Prop) :
    (id rules).Conservative :=
  fun _judgment derivation => derivation

/-- Conservative closed-derivability translations compose. -/
theorem Conservative.comp
    {earlier : DerivabilityTranslation sourceRules targetRules}
    {later : DerivabilityTranslation targetRules thirdRules}
    (earlierConservative : earlier.Conservative)
    (laterConservative : later.Conservative) :
    (earlier.comp later).Conservative := by
  intro judgment targetDerivation
  exact earlierConservative judgment
    (laterConservative (earlier.mapJudgment judgment) targetDerivation)

/-- Conservative translations identify the source theorem set with its image. -/
theorem derives_iff_of_conservative
    (translation : DerivabilityTranslation sourceRules targetRules)
    (conservative : translation.Conservative) (judgment : Source) :
    Derives targetRules (translation.mapJudgment judgment) ↔
      Derives sourceRules judgment :=
  ⟨conservative judgment, translation.map_derives⟩

/-- If the image of a judgment is underivable in the target, the judgment is
underivable in the source. -/
theorem source_underivable_of_target_underivable
    (translation : DerivabilityTranslation sourceRules targetRules)
    (judgment : Source)
    (targetUnderivable :
      ¬ Derives targetRules (translation.mapJudgment judgment)) :
    ¬ Derives sourceRules judgment :=
  fun sourceDerivation => targetUnderivable
    (translation.map_derives sourceDerivation)

end DerivabilityTranslation

/-! ## Strict rule homomorphisms -/

/-- A strict homomorphism maps each primitive rule to a primitive target rule
with exactly the pointwise translated, ordered premise list. -/
structure RuleHomomorphism
    (sourceRules : List Source → Source → Prop)
    (targetRules : List Target → Target → Prop) where
  mapJudgment : Source → Target
  map_rule : ∀ {premises conclusion}, sourceRules premises conclusion →
    targetRules (premises.map mapJudgment) (mapJudgment conclusion)

namespace RuleHomomorphism

/-- Identity is a strict rule homomorphism. -/
def id (rules : List Source → Source → Prop) :
    RuleHomomorphism rules rules where
  mapJudgment := fun judgment => judgment
  map_rule := by
    intro premises conclusion rule
    simpa using rule

/-- Strict rule homomorphisms compose. -/
def comp
    (earlier : RuleHomomorphism sourceRules targetRules)
    (later : RuleHomomorphism targetRules thirdRules) :
    RuleHomomorphism sourceRules thirdRules where
  mapJudgment := later.mapJudgment ∘ earlier.mapJudgment
  map_rule := by
    intro premises conclusion rule
    simpa only [List.map_map, Function.comp_apply] using
      later.map_rule (earlier.map_rule rule)

/-- Strict rule homomorphisms preserve every generated derivation. -/
theorem map_derives (homomorphism : RuleHomomorphism sourceRules targetRules)
    {judgment : Source} (derivation : Derives sourceRules judgment) :
    Derives targetRules (homomorphism.mapJudgment judgment) := by
  apply Derives.least
    (fun sourceJudgment =>
      Derives targetRules (homomorphism.mapJudgment sourceJudgment)) _ derivation
  intro premises conclusion rule premiseDerivations
  refine Derives.node (premises.map homomorphism.mapJudgment)
    (homomorphism.mapJudgment conclusion) (homomorphism.map_rule rule) ?_
  intro targetPremise targetMember
  rw [List.mem_map] at targetMember
  obtain ⟨sourcePremise, sourceMember, rfl⟩ := targetMember
  exact premiseDerivations sourcePremise sourceMember

/-- Forget primitive-rule locality while retaining closed theorem transport. -/
def toDerivabilityTranslation
    (homomorphism : RuleHomomorphism sourceRules targetRules) :
    DerivabilityTranslation sourceRules targetRules where
  mapJudgment := homomorphism.mapJudgment
  map_derives := homomorphism.map_derives

end RuleHomomorphism

/-! ## Contravariant transport of finite models -/

namespace FiniteModel

/-- A finite target model pulls back along a strict rule homomorphism. -/
def reduct (homomorphism : RuleHomomorphism sourceRules targetRules)
    (targetModel : FiniteModel.{v, x} targetRules) :
    FiniteModel.{u, x} sourceRules where
  World := targetModel.World
  worldFintype := targetModel.worldFintype
  satisfies := fun world judgment =>
    targetModel.satisfies world (homomorphism.mapJudgment judgment)
  rulesSound := by
    intro premises conclusion rule world premiseSatisfaction
    apply targetModel.rulesSound (premises.map homomorphism.mapJudgment)
      (homomorphism.mapJudgment conclusion) (homomorphism.map_rule rule) world
    intro targetPremise targetMember
    rw [List.mem_map] at targetMember
    obtain ⟨sourcePremise, sourceMember, rfl⟩ := targetMember
    exact premiseSatisfaction sourcePremise sourceMember

/-- Pullback validity is exactly target validity of the translated judgment. -/
theorem reduct_valid_iff
    (homomorphism : RuleHomomorphism sourceRules targetRules)
    (targetModel : FiniteModel.{v, x} targetRules) (judgment : Source) :
    (targetModel.reduct homomorphism).Valid judgment ↔
      targetModel.Valid (homomorphism.mapJudgment judgment) :=
  Iff.rfl

/-- The exhaustive validity programs also agree definitionally after
pullback. -/
theorem reduct_checkValid
    (homomorphism : RuleHomomorphism sourceRules targetRules)
    (targetModel : FiniteModel.{v, x} targetRules) (judgment : Source) :
    (targetModel.reduct homomorphism).checkValid judgment =
      targetModel.checkValid (homomorphism.mapJudgment judgment) :=
  rfl

end FiniteModel

namespace FiniteCountermodel

/-- A finite countermodel to a translated target judgment pulls back to a
finite countermodel of the source judgment. -/
def reduct (homomorphism : RuleHomomorphism sourceRules targetRules)
    (judgment : Source)
    (targetCountermodel : FiniteCountermodel.{v, x} targetRules
      (homomorphism.mapJudgment judgment)) :
    FiniteCountermodel.{u, x} sourceRules judgment where
  model := targetCountermodel.model.reduct homomorphism
  refutes := targetCountermodel.refutes

end FiniteCountermodel

/-! ## Witness-preserving certificate compilation -/

/-- A witnessed rule homomorphism compiles source rule witnesses and preserves
every successful Boolean root test. -/
structure WitnessedRuleHomomorphism
    (sourceInterface : RuleWitness.{u, w} sourceRules)
    (targetInterface : RuleWitness.{v, x} targetRules) where
  mapJudgment : Source → Target
  mapWitness : sourceInterface.W → targetInterface.W
  rule_test_preserved : ∀ witness premises conclusion,
    sourceInterface.isInstance witness premises conclusion = true →
      targetInterface.isInstance (mapWitness witness)
        (premises.map mapJudgment) (mapJudgment conclusion) = true

namespace WitnessedRuleHomomorphism

variable {sourceInterface : RuleWitness.{u, w} sourceRules}
variable {targetInterface : RuleWitness.{v, x} targetRules}

/-- Witness preservation induces a strict homomorphism of the underlying rule
predicates. -/
def toRuleHomomorphism
    (homomorphism : WitnessedRuleHomomorphism sourceInterface targetInterface) :
    RuleHomomorphism sourceRules targetRules where
  mapJudgment := homomorphism.mapJudgment
  map_rule := by
    intro premises conclusion rule
    obtain ⟨witness, accepted⟩ :=
      sourceInterface.complete premises conclusion rule
    exact targetInterface.sound (homomorphism.mapWitness witness)
      (premises.map homomorphism.mapJudgment)
      (homomorphism.mapJudgment conclusion)
      (homomorphism.rule_test_preserved witness premises conclusion accepted)

/-- Compile every judgment and rule witness in a finite replay tree. -/
def mapCertificate
    (homomorphism : WitnessedRuleHomomorphism sourceInterface targetInterface) :
    Derivation Source sourceInterface.W →
      Derivation Target targetInterface.W
  | .node conclusion witness arity children =>
      .node (homomorphism.mapJudgment conclusion)
        (homomorphism.mapWitness witness) arity
        (fun position => homomorphism.mapCertificate (children position))

@[simp] theorem mapCertificate_concl
    (homomorphism : WitnessedRuleHomomorphism sourceInterface targetInterface)
    (certificate : Derivation Source sourceInterface.W) :
    (homomorphism.mapCertificate certificate).concl =
      homomorphism.mapJudgment certificate.concl := by
  cases certificate
  rfl

/-- Compiling witnesses preserves successful replay. -/
theorem mapCertificate_valid_of_valid
    (homomorphism : WitnessedRuleHomomorphism sourceInterface targetInterface) :
    ∀ certificate : Derivation Source sourceInterface.W,
      certificate.valid sourceInterface = true →
        (homomorphism.mapCertificate certificate).valid targetInterface = true := by
  intro certificate
  induction certificate with
  | node conclusion witness arity children inductionHypothesis =>
      intro accepted
      simp only [WitnessedRuleHomomorphism.mapCertificate, Derivation.valid,
        Bool.and_eq_true, List.all_eq_true,
        List.forall_mem_ofFn_iff, id] at accepted ⊢
      constructor
      · have rootAccepted := homomorphism.rule_test_preserved witness
          (List.ofFn fun position => (children position).concl)
          conclusion accepted.1
        have premiseListsEqual :
            (List.ofFn fun position =>
              (homomorphism.mapCertificate (children position)).concl) =
            (List.ofFn fun position => (children position).concl).map
              homomorphism.mapJudgment := by
          rw [List.map_ofFn]
          apply List.ofFn_inj.mpr
          funext position
          exact homomorphism.mapCertificate_concl (children position)
        rw [premiseListsEqual]
        exact rootAccepted
      · intro position
        exact inductionHypothesis position (accepted.2 position)

end WitnessedRuleHomomorphism

/-! ## Exact replay homomorphisms -/

/-- Exact witness translation commutes with the complete Boolean rule test and
uses an injective judgment map.  These are precisely the extra facts needed to
reflect replay, including the final claim-equality test. -/
structure ExactWitnessedRuleHomomorphism
    (sourceInterface : RuleWitness.{u, w} sourceRules)
    (targetInterface : RuleWitness.{v, x} targetRules) where
  mapJudgment : Source → Target
  mapJudgment_injective : Function.Injective mapJudgment
  mapWitness : sourceInterface.W → targetInterface.W
  rule_test_exact : ∀ witness premises conclusion,
    targetInterface.isInstance (mapWitness witness)
        (premises.map mapJudgment) (mapJudgment conclusion) =
      sourceInterface.isInstance witness premises conclusion

namespace ExactWitnessedRuleHomomorphism

variable {sourceInterface : RuleWitness.{u, w} sourceRules}
variable {targetInterface : RuleWitness.{v, x} targetRules}

/-- Forget reflection while retaining successful witness compilation. -/
def toWitnessed
    (homomorphism :
      ExactWitnessedRuleHomomorphism sourceInterface targetInterface) :
    WitnessedRuleHomomorphism sourceInterface targetInterface where
  mapJudgment := homomorphism.mapJudgment
  mapWitness := homomorphism.mapWitness
  rule_test_preserved := by
    intro witness premises conclusion accepted
    rw [homomorphism.rule_test_exact]
    exact accepted

/-- Exact root recognition lifts recursively to exact certificate replay. -/
theorem mapCertificate_valid
    (homomorphism :
      ExactWitnessedRuleHomomorphism sourceInterface targetInterface) :
    ∀ certificate : Derivation Source sourceInterface.W,
      (homomorphism.toWitnessed.mapCertificate certificate).valid
          targetInterface =
        certificate.valid sourceInterface := by
  intro certificate
  induction certificate with
  | node conclusion witness arity children inductionHypothesis =>
      simp only [WitnessedRuleHomomorphism.mapCertificate, Derivation.valid]
      have premiseListsEqual :
          (List.ofFn fun position =>
            (homomorphism.toWitnessed.mapCertificate
              (children position)).concl) =
          (List.ofFn fun position => (children position).concl).map
            homomorphism.mapJudgment := by
        rw [List.map_ofFn]
        apply List.ofFn_inj.mpr
        funext position
        exact homomorphism.toWitnessed.mapCertificate_concl
          (children position)
      rw [premiseListsEqual]
      change
        (targetInterface.isInstance (homomorphism.mapWitness witness)
            ((List.ofFn fun position => (children position).concl).map
              homomorphism.mapJudgment)
            (homomorphism.mapJudgment conclusion) &&
          _) = _
      rw [homomorphism.rule_test_exact]
      have childValuesEqual :
          (List.ofFn fun position =>
            (homomorphism.toWitnessed.mapCertificate
              (children position)).valid targetInterface) =
          List.ofFn (fun position =>
            (children position).valid sourceInterface) := by
        apply List.ofFn_inj.mpr
        funext position
        exact inductionHypothesis position
      rw [childValuesEqual]

/-- Exact witness and judgment translation commutes with the complete Boolean
replay-and-claim test on every certificate and claim. -/
theorem replay_test_commutes
    [DecidableEq Source] [DecidableEq Target]
    (homomorphism :
      ExactWitnessedRuleHomomorphism sourceInterface targetInterface)
    (claim : Source) (certificate : Derivation Source sourceInterface.W) :
    ((homomorphism.toWitnessed.mapCertificate certificate).valid
        targetInterface &&
      decide ((homomorphism.toWitnessed.mapCertificate certificate).concl =
        homomorphism.mapJudgment claim)) =
    (certificate.valid sourceInterface &&
      decide (certificate.concl = claim)) := by
  rw [homomorphism.mapCertificate_valid,
    homomorphism.toWitnessed.mapCertificate_concl]
  have equalityIff :
      homomorphism.mapJudgment certificate.concl =
          homomorphism.mapJudgment claim ↔
        certificate.concl = claim :=
    homomorphism.mapJudgment_injective.eq_iff
  change
    (certificate.valid sourceInterface &&
      decide (homomorphism.mapJudgment certificate.concl =
        homomorphism.mapJudgment claim)) =
    (certificate.valid sourceInterface &&
      decide (certificate.concl = claim))
  rw [decide_eq_decide.mpr equalityIff]

end ExactWitnessedRuleHomomorphism

end Mettapedia.Logic.FinitaryRuleSystem
