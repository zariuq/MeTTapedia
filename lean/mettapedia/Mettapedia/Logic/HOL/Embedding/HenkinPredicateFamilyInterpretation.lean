import Mettapedia.Logic.HOL.Embedding.HenkinDependentFamilyInterpretation
import Mettapedia.Logic.HOL.ProofSyntax
import Mettapedia.TypeTheory.FamilyEnclosingUniverse

/-!
# HOL predicates and proofs as dependent families and sections

The existing admissible Henkin interpretation sends simple HOL types to
constant families. HOL formulas supply another, genuinely dependent
construction: their truth at an admissible valuation gives a truth-valued
fibre, and a predicate with a free argument gives a refinement family.

This module interprets the actual typed HOL syntax and its extensional proof
syntax. Quantifiers correspond to sections and inhabited dependent sums over
the admitted Henkin domain. Context extension and substitution commute with
the construction. A proof of a universally quantified implication transports
refinement witnesses without changing their underlying values.

These are semantic families in the existing families CwF, not a translation
to the syntax of a native dependent kernel. Truth fibres do not retain which
HOL proof was supplied; the original `ProofSyntax` remains a separate object.
No full-domain, choice, HOTG universe, or native equality-reflection claim is
implicit in this interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.HenkinPredicateFamilyInterpretation

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.Logic.HOL.ContextualStructure
open Mettapedia.Logic.HOL.Embedding.HenkinDependentFamilyInterpretation
open Mettapedia.TypeTheory.FamilyEnclosingUniverse

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-- The lifted truth of an actual HOL formula at an admissible valuation. -/
def truthFamily (M : HenkinModel.{u, v, w} Base Const)
    {Γ : Ctx Base} (φ : Formula Const Γ) :
    AdmissibleContext M Γ → Type (max (u + 1) w) :=
  fun valuation => ULift (PLift (M.denote φ valuation.1).down)

/-- Extend an admissible context by an admissible value of the bound type. -/
def extendContext (M : HenkinModel.{u, v, w} Base Const)
    {Γ : Ctx Base} {A : Ty Base} (valuation : AdmissibleContext M Γ)
    (value : AdmissibleValue M A) : AdmissibleContext M (A :: Γ) :=
  (contextExtensionEquiv M Γ A).symm (valuation, value)

/-- A predicate in `A :: Γ` determines a truth-valued family over its
admissible arguments, at each admissible parameter valuation. -/
def predicateFamily (M : HenkinModel.{u, v, w} Base Const)
    {Γ : Ctx Base} {A : Ty Base} (φ : Formula Const (A :: Γ))
    (valuation : AdmissibleContext M Γ) :
    AdmissibleValue M A → Type (max (u + 1) w) :=
  fun value => truthFamily M φ (extendContext M valuation value)

/-- The dependent sum retaining an admitted value and predicate membership. -/
abbrev refinementFamily (M : HenkinModel.{u, v, w} Base Const)
    {Γ : Ctx Base} {A : Ty Base} (φ : Formula Const (A :: Γ))
    (valuation : AdmissibleContext M Γ) :=
  Σ value : AdmissibleValue M A, predicateFamily M φ valuation value

/-- Refinement is comprehension in the existing dependent families model. -/
theorem refinement_is_families_comprehension
    (M : HenkinModel.{u, v, w} Base Const)
    {Γ : Ctx Base} {A : Ty Base} (φ : Formula Const (A :: Γ))
    (valuation : AdmissibleContext M Γ) :
    familiesCwf.ext (AdmissibleValue M A) (predicateFamily M φ valuation) =
      refinementFamily M φ valuation := rfl

/-- The refinement presentation and the subtype presentation have exactly
the same witnesses, not just the same inhabitation proposition. -/
def refinementEquivSubtype (M : HenkinModel.{u, v, w} Base Const)
    {Γ : Ctx Base} {A : Ty Base} (φ : Formula Const (A :: Γ))
    (valuation : AdmissibleContext M Γ) :
    refinementFamily M φ valuation ≃
      {value : AdmissibleValue M A //
        (M.denote φ (M.extend valuation.1 value.1)).down} where
  toFun point := ⟨point.1, point.2.down.down⟩
  invFun point := ⟨point.1, ⟨⟨point.2⟩⟩⟩
  left_inv point := by cases point; rfl
  right_inv point := by cases point; rfl

/-! ## Context extension and substitution -/

/-- The comprehension square commutes for actual lifted HOL substitutions. -/
theorem extendContext_substitution
    (M : HenkinModel.{u, v, w} Base Const)
    {Γ Δ : Ctx Base} {A : Ty Base}
    (substitution : (holScwf Base Const).Sub Γ Δ)
    (valuation : AdmissibleContext M Γ) (value : AdmissibleValue M A) :
    interpretSubstitution M (Subst.lift substitution)
        (extendContext M valuation value) =
      extendContext M (interpretSubstitution M substitution valuation) value := by
  apply Subtype.ext
  exact Soundness.substVal_lift M substitution valuation.1 value.1

/-- Reindexing the truth family is the interpretation of syntactic
substitution, at every admissible valuation. -/
theorem truthFamily_substitution
    (M : HenkinModel.{u, v, w} Base Const)
    {Γ Δ : Ctx Base} (φ : Formula Const Δ)
    (substitution : (holScwf Base Const).Sub Γ Δ) :
    truthFamily M (subst substitution φ) =
      familiesCwf.tySub (truthFamily M φ)
        (interpretSubstitution M substitution) := by
  funext valuation
  unfold truthFamily
  change ULift (PLift (M.denote (subst substitution φ) valuation.1).down) =
    ULift (PLift (M.denote φ (Soundness.substVal M substitution valuation.1)).down)
  exact congrArg (fun proposition : Ty.denote M.Carrier .prop =>
    ULift.{max (u + 1) w} (PLift proposition.down))
    (Soundness.denote_subst M substitution φ valuation.1)

/-- Predicate fibres commute with parameter substitution while retaining
the admitted argument itself. -/
theorem predicateFamily_substitution
    (M : HenkinModel.{u, v, w} Base Const)
    {Γ Δ : Ctx Base} {A : Ty Base} (φ : Formula Const (A :: Δ))
    (substitution : (holScwf Base Const).Sub Γ Δ)
    (valuation : AdmissibleContext M Γ) (value : AdmissibleValue M A) :
    predicateFamily M (subst (Subst.lift substitution) φ) valuation value =
      predicateFamily M φ (interpretSubstitution M substitution valuation) value := by
  calc
    _ = truthFamily M φ
        (interpretSubstitution M (Subst.lift substitution)
          (extendContext M valuation value)) :=
      congrFun (truthFamily_substitution M φ (Subst.lift substitution))
        (extendContext M valuation value)
    _ = _ := congrArg (truthFamily M φ)
      (extendContext_substitution M substitution valuation value)

/-- Parameter substitution induces a value-preserving equivalence between
the two corresponding refinement comprehensions. -/
def refinementSubstitutionEquiv
    (M : HenkinModel.{u, v, w} Base Const)
    {Γ Δ : Ctx Base} {A : Ty Base} (φ : Formula Const (A :: Δ))
    (substitution : (holScwf Base Const).Sub Γ Δ)
    (valuation : AdmissibleContext M Γ) :
    refinementFamily M (subst (Subst.lift substitution) φ) valuation ≃
      refinementFamily M φ (interpretSubstitution M substitution valuation) :=
  Equiv.sigmaCongrRight fun value =>
    Equiv.cast (predicateFamily_substitution M φ substitution valuation value)

theorem refinementSubstitutionEquiv_preserves_value
    (M : HenkinModel.{u, v, w} Base Const)
    {Γ Δ : Ctx Base} {A : Ty Base} (φ : Formula Const (A :: Δ))
    (substitution : (holScwf Base Const).Sub Γ Δ)
    (valuation : AdmissibleContext M Γ)
    (point : refinementFamily M (subst (Subst.lift substitution) φ) valuation) :
    (refinementSubstitutionEquiv M φ substitution valuation point).1 = point.1 := rfl

/-! ## Quantification and actual proof interpretation -/

/-- HOL universal truth is exactly an inhabited dependent section over the
admissible Henkin domain. No full-domain or choice assumption is needed. -/
theorem universal_iff_nonempty_section
    (M : HenkinModel.{u, v, w} Base Const)
    {Γ : Ctx Base} {A : Ty Base} (φ : Formula Const (A :: Γ))
    (valuation : AdmissibleContext M Γ) :
    (M.denote (.all φ) valuation.1).down ↔
      Nonempty ((value : AdmissibleValue M A) → predicateFamily M φ valuation value) := by
  constructor
  · intro holds
    exact ⟨fun value => ⟨⟨holds value.1 value.2⟩⟩⟩
  · rintro ⟨witnessSection⟩ value admitted
    exact (witnessSection ⟨value, admitted⟩).down.down

/-- HOL existential truth is exactly inhabitation of the dependent
refinement comprehension, not extraction of a computational witness. -/
theorem existential_iff_nonempty_refinement
    (M : HenkinModel.{u, v, w} Base Const)
    {Γ : Ctx Base} {A : Ty Base} (φ : Formula Const (A :: Γ))
    (valuation : AdmissibleContext M Γ) :
    (M.denote (.ex φ) valuation.1).down ↔
      Nonempty (refinementFamily M φ valuation) := by
  constructor
  · rintro ⟨value, admitted, holds⟩
    exact ⟨⟨⟨value, admitted⟩, ⟨⟨holds⟩⟩⟩⟩
  · rintro ⟨point⟩
    exact ⟨point.1.1, point.1.2, point.2.down.down⟩

/-- Admissible valuations in which the proof's actual ordered hypotheses
hold. This names the proof's semantic domain, not an extra axiom. -/
abbrev SatisfiedContext (M : HenkinModel.{u, v, w} Base Const)
    {Γ : Ctx Base} (hypotheses : List (Formula Const Γ)) :=
  {valuation : AdmissibleContext M Γ //
    Soundness.SatisfiesHyps M valuation.1 hypotheses}

/-- An actual HOL proof denotes a section on precisely the valuations
satisfying its hypotheses. Extensional argument congruence is explicit. -/
def proofSection (M : HenkinModel.{u, v, w} Base Const)
    (respects : M.FunctionsRespectEqv)
    {Γ : Ctx Base} {hypotheses : List (Formula Const Γ)} {φ : Formula Const Γ}
    (proof : ProofSyntax Const hypotheses φ) :
    (valuation : SatisfiedContext M hypotheses) → truthFamily M φ valuation.1 :=
  fun valuation => ⟨⟨Soundness.extDerivation_sound proof.erase respects
    valuation.1.2 valuation.2⟩⟩

/-- A proved universal supplies a dependent section uniformly in its
parameters and all admitted arguments. -/
def universalProofSection (M : HenkinModel.{u, v, w} Base Const)
    (respects : M.FunctionsRespectEqv)
    {Γ : Ctx Base} {A : Ty Base} {hypotheses : List (Formula Const Γ)}
    {φ : Formula Const (A :: Γ)}
    (proof : ProofSyntax Const hypotheses (.all φ))
    (valuation : SatisfiedContext M hypotheses) :
    (value : AdmissibleValue M A) → predicateFamily M φ valuation.1 value :=
  fun value => ⟨⟨(proofSection M respects proof valuation).down.down
    value.1 value.2⟩⟩

/-- A proved universally quantified implication acts on actual refinement
witnesses, keeping the underlying admitted value and transporting membership. -/
def refinementMapOfProof (M : HenkinModel.{u, v, w} Base Const)
    (respects : M.FunctionsRespectEqv)
    {Γ : Ctx Base} {A : Ty Base} {hypotheses : List (Formula Const Γ)}
    {φ ψ : Formula Const (A :: Γ)}
    (proof : ProofSyntax Const hypotheses (.all (.imp φ ψ)))
    (valuation : SatisfiedContext M hypotheses) :
    refinementFamily M φ valuation.1 → refinementFamily M ψ valuation.1 :=
  fun point => ⟨point.1, ⟨⟨
    (universalProofSection M respects proof valuation point.1).down.down
      point.2.down.down⟩⟩⟩

theorem refinementMapOfProof_preserves_value
    (M : HenkinModel.{u, v, w} Base Const)
    (respects : M.FunctionsRespectEqv)
    {Γ : Ctx Base} {A : Ty Base} {hypotheses : List (Formula Const Γ)}
    {φ ψ : Formula Const (A :: Γ)}
    (proof : ProofSyntax Const hypotheses (.all (.imp φ ψ)))
    (valuation : SatisfiedContext M hypotheses)
    (point : refinementFamily M φ valuation.1) :
    (refinementMapOfProof M respects proof valuation point).1 = point.1 := rfl

/-- Two actual HOL implication proofs induce an equivalence of their
refinement families. This is equivalence of interpreted membership, not a
new native definitional equality or recovery of the original proof syntax. -/
def refinementEquivOfProofs (M : HenkinModel.{u, v, w} Base Const)
    (respects : M.FunctionsRespectEqv)
    {Γ : Ctx Base} {A : Ty Base} {hypotheses : List (Formula Const Γ)}
    {φ ψ : Formula Const (A :: Γ)}
    (forward : ProofSyntax Const hypotheses (.all (.imp φ ψ)))
    (backward : ProofSyntax Const hypotheses (.all (.imp ψ φ)))
    (valuation : SatisfiedContext M hypotheses) :
    refinementFamily M φ valuation.1 ≃ refinementFamily M ψ valuation.1 where
  toFun := refinementMapOfProof M respects forward valuation
  invFun := refinementMapOfProof M respects backward valuation
  left_inv point := by cases point; rfl
  right_inv point := by cases point; rfl

/-! ## Enclosing the interpreted predicate family -/

/-- Enclose this actual HOL-generated family in the independently supplied
family-universe operator. The ambient operator is an available instance;
this does not identify it with a HOTG set universe. -/
def predicateEnvelope
    (operator : FamilyEnclosingUniverseOperator.{max (u + 1) w})
    (M : HenkinModel.{u, v, w} Base Const)
    {Γ : Ctx Base} {A : Ty Base} (φ : Formula Const (A :: Γ))
    (valuation : AdmissibleContext M Γ) :
    ClosedTarskiUniverseOver (AdmissibleValue M A) (predicateFamily M φ valuation) :=
  operator.enclose (AdmissibleValue M A) (predicateFamily M φ valuation)

universe uCode

/-- The dependent-product code for a HOL universal, inside an envelope of
the actual predicate family. -/
def universalCode
    (M : HenkinModel.{u, v, w} Base Const)
    {Γ : Ctx Base} {A : Ty Base} (φ : Formula Const (A :: Γ))
    (valuation : AdmissibleContext M Γ)
    (envelope : ClosedTarskiUniverseOver.{uCode}
      (AdmissibleValue M A) (predicateFamily M φ valuation)) : envelope.Code :=
  envelope.piCode envelope.baseCode fun argument =>
    envelope.fibreCode (envelope.elBase argument)

/-- Decoding the universal code gives precisely a section over admitted
HOL arguments. The base-index change and fibre decoding are both explicit. -/
def universalCodeEquiv
    (M : HenkinModel.{u, v, w} Base Const)
    {Γ : Ctx Base} {A : Ty Base} (φ : Formula Const (A :: Γ))
    (valuation : AdmissibleContext M Γ)
    (envelope : ClosedTarskiUniverseOver.{uCode}
      (AdmissibleValue M A) (predicateFamily M φ valuation)) :
    envelope.El (universalCode M φ valuation envelope) ≃
      ((value : AdmissibleValue M A) → predicateFamily M φ valuation value) :=
  (envelope.elPi envelope.baseCode
    (fun argument => envelope.fibreCode (envelope.elBase argument))).trans
    ((Equiv.piCongrRight fun argument => envelope.elFibre (envelope.elBase argument)).trans
      (Equiv.piCongrLeft (predicateFamily M φ valuation) envelope.elBase))

/-- The actual HOL universal and the interpreted dependent-product code
agree on inhabitation. This is a semantic bridge, not native term extraction. -/
theorem universal_iff_nonempty_code
    (M : HenkinModel.{u, v, w} Base Const)
    {Γ : Ctx Base} {A : Ty Base} (φ : Formula Const (A :: Γ))
    (valuation : AdmissibleContext M Γ)
    (envelope : ClosedTarskiUniverseOver.{uCode}
      (AdmissibleValue M A) (predicateFamily M φ valuation)) :
    (M.denote (.all φ) valuation.1).down ↔
      Nonempty (envelope.El (universalCode M φ valuation envelope)) := by
  rw [universal_iff_nonempty_section]
  exact (universalCodeEquiv M φ valuation envelope).symm.nonempty_congr

/-- A genuine proof supplies an element of that dependent-product code. -/
def universalProofCode
    (M : HenkinModel.{u, v, w} Base Const)
    (respects : M.FunctionsRespectEqv)
    {Γ : Ctx Base} {A : Ty Base} {hypotheses : List (Formula Const Γ)}
    {φ : Formula Const (A :: Γ)}
    (proof : ProofSyntax Const hypotheses (.all φ))
    (valuation : SatisfiedContext M hypotheses)
    (envelope : ClosedTarskiUniverseOver.{uCode}
      (AdmissibleValue M A) (predicateFamily M φ valuation.1)) :
    envelope.El (universalCode M φ valuation.1 envelope) :=
  (universalCodeEquiv M φ valuation.1 envelope).symm
    (universalProofSection M respects proof valuation)

/-- Decoding the supplied proof code recovers its dependent section. -/
theorem universalProofCode_decode
    (M : HenkinModel.{u, v, w} Base Const)
    (respects : M.FunctionsRespectEqv)
    {Γ : Ctx Base} {A : Ty Base} {hypotheses : List (Formula Const Γ)}
    {φ : Formula Const (A :: Γ)}
    (proof : ProofSyntax Const hypotheses (.all φ))
    (valuation : SatisfiedContext M hypotheses)
    (envelope : ClosedTarskiUniverseOver.{uCode}
      (AdmissibleValue M A) (predicateFamily M φ valuation.1)) :
    universalCodeEquiv M φ valuation.1 envelope
        (universalProofCode M respects proof valuation envelope) =
      universalProofSection M respects proof valuation :=
  (universalCodeEquiv M φ valuation.1 envelope).apply_symm_apply _

/-! ## Actual higher-order and varying-family controls -/

namespace Controls

/-- The first of two higher-order predicate parameters applied to the
currently bound argument. -/
def firstPredicate (A : Ty Base) :
    Formula Const (A :: [A ⇒ .prop, A ⇒ .prop]) :=
  .app (.var (.vs (.vs .vz))) (.var .vz)

/-- The second predicate parameter, at the same argument. -/
def secondPredicate (A : Ty Base) :
    Formula Const (A :: [A ⇒ .prop, A ⇒ .prop]) :=
  .app (.var (.vs .vz)) (.var .vz)

/-- A concrete proof about arbitrary higher-order predicate parameters:
every witness of their intersection is a witness of the first predicate. -/
def intersectionProjection (A : Ty Base) :
    ProofSyntax Const ([] : List (Formula Const [A ⇒ .prop, A ⇒ .prop]))
      (.all (.imp (.and (firstPredicate A) (secondPredicate A)) (firstPredicate A))) :=
  .allI (.impI (.andEL (.hyp ⟨0, by simp⟩)))

/-- The same proof closes both predicate parameters by actual HOL
quantification, not a list of first-order ground instances. -/
def closedIntersectionProjection (A : Ty Base) :
    ProofSyntax Const ([] : List (Formula Const []))
      (.all (.all (.all
        (.imp (.and (firstPredicate A) (secondPredicate A)) (firstPredicate A))))) :=
  .allI (.allI (intersectionProjection A))

open HenkinModel.ModelPropertyCanary

abbrev boolean : Ty Unit := .base ()
abbrev model := booleanBaseModel

def emptyValuation : AdmissibleContext model [] :=
  ⟨(fun boundVar => nomatch boundVar), by intro A boundVar; exact nomatch boundVar⟩

def trueValue : AdmissibleValue model boolean :=
  ⟨⟨true⟩, booleanBaseModel_fullDomains _ _⟩

def falseValue : AdmissibleValue model boolean :=
  ⟨⟨false⟩, booleanBaseModel_fullDomains _ _⟩

def isTrue : AdmissibleValue model (boolean ⇒ .prop) :=
  ⟨fun value => ⟨value.down = true⟩, booleanBaseModel_fullDomains _ _⟩

def alwaysTrue : AdmissibleValue model (boolean ⇒ .prop) :=
  ⟨fun _ => ⟨True⟩, booleanBaseModel_fullDomains _ _⟩

def predicateParameters : AdmissibleContext model [boolean ⇒ .prop, boolean ⇒ .prop] :=
  extendContext model (extendContext model emptyValuation isTrue) alwaysTrue

def satisfiedParameters :
    SatisfiedContext model ([] : List (Formula (NoConstants Unit)
      [boolean ⇒ .prop, boolean ⇒ .prop])) :=
  ⟨predicateParameters, by intro φ member; cases member⟩

/-- A real inhabitant of the predicate intersection at the true argument. -/
def intersectionWitness :
    refinementFamily model (.and (firstPredicate boolean) (secondPredicate boolean))
      predicateParameters :=
  ⟨trueValue, ⟨⟨rfl, True.intro⟩⟩⟩

/-- Apply the interpreted higher-order proof to that dependent witness. -/
def projectedWitness :
    refinementFamily model (firstPredicate boolean) predicateParameters :=
  refinementMapOfProof model
    (model.functionsRespectEqv_of_fullDomains booleanBaseModel_fullDomains)
    (intersectionProjection boolean) satisfiedParameters intersectionWitness

theorem projectedWitness_value : projectedWitness.1 = trueValue := rfl

/-- A concrete family-enclosing universe for the interpreted implication.
Its codes are ambient types, not native dependent-kernel terms or HOTG sets. -/
def implicationEnvelope :=
  predicateEnvelope ambientOperator model
    (.imp (.and (firstPredicate boolean) (secondPredicate boolean))
      (firstPredicate boolean)) predicateParameters

/-- The actual higher-order projection proof supplies an inhabitant of its
dependent-product code in that concrete envelope. -/
def projectionCodeWitness :
    implicationEnvelope.El
      (universalCode model
        (.imp (.and (firstPredicate boolean) (secondPredicate boolean))
          (firstPredicate boolean)) predicateParameters implicationEnvelope) :=
  universalProofCode model
    (model.functionsRespectEqv_of_fullDomains booleanBaseModel_fullDomains)
    (intersectionProjection boolean) satisfiedParameters implicationEnvelope

/-- A negative argument has no membership witness in the same family. -/
theorem false_fibre_empty :
    ¬ Nonempty (predicateFamily model (firstPredicate boolean) predicateParameters falseValue) := by
  rintro ⟨evidence⟩
  exact Bool.false_ne_true evidence.down.down

/-- This HOL-generated dependent family is not a constant simple type. -/
theorem predicate_family_not_constant :
    ¬ ∃ T : Type 1,
      predicateFamily model (firstPredicate boolean) predicateParameters = constantFamily T := by
  rintro ⟨T, equal⟩
  have present : Nonempty
      (predicateFamily model (firstPredicate boolean) predicateParameters trueValue) :=
    ⟨projectedWitness.2⟩
  have absent : Nonempty
      (predicateFamily model (firstPredicate boolean) predicateParameters falseValue) := by
    rw [equal] at present ⊢
    exact present
  exact false_fibre_empty absent

/-- The true witness establishes an existential, while universal membership
is false because the false argument is admitted and has an empty fibre. -/
theorem existential_true_universal_false :
    (model.denote (.ex (firstPredicate boolean)) predicateParameters.1).down ∧
      ¬ (model.denote (.all (firstPredicate boolean)) predicateParameters.1).down := by
  constructor
  · exact (existential_iff_nonempty_refinement model _ _).mpr ⟨projectedWitness⟩
  · intro universal
    obtain ⟨witnessSection⟩ :=
      (universal_iff_nonempty_section model _ _).mp universal
    exact false_fibre_empty ⟨witnessSection falseValue⟩

/-- Retaining proof syntax is necessary if consumers distinguish proof
strategies: truth-family interpretation alone identifies these two proofs. -/
theorem distinct_proofs_same_truth_section
    (M : HenkinModel.{u, v, w} Base Const) (respects : M.FunctionsRespectEqv)
    {Γ : Ctx Base} (φ : Formula Const Γ) :
    ProofSyntax.Controls.direct φ ≠ ProofSyntax.Controls.detour φ ∧
      proofSection M respects (ProofSyntax.Controls.direct φ) =
        proofSection M respects (ProofSyntax.Controls.detour φ) := by
  constructor
  · exact ProofSyntax.Controls.distinct_trees φ
  · funext valuation
    rfl

end Controls

#print axioms extendContext_substitution
#print axioms truthFamily_substitution
#print axioms predicateFamily_substitution
#print axioms refinementSubstitutionEquiv
#print axioms universal_iff_nonempty_section
#print axioms existential_iff_nonempty_refinement
#print axioms proofSection
#print axioms universalProofSection
#print axioms refinementMapOfProof
#print axioms refinementEquivOfProofs
#print axioms universalCodeEquiv
#print axioms universal_iff_nonempty_code
#print axioms universalProofCode
#print axioms universalProofCode_decode
#print axioms Controls.closedIntersectionProjection
#print axioms Controls.projectedWitness
#print axioms Controls.projectionCodeWitness
#print axioms Controls.predicate_family_not_constant
#print axioms Controls.existential_true_universal_false
#print axioms Controls.distinct_proofs_same_truth_section

end Mettapedia.Logic.HOL.Embedding.HenkinPredicateFamilyInterpretation
