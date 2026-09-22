import Mettapedia.Logic.HOL.Embedding.HenkinPredicateFamilyInterpretation
import Mettapedia.Logic.HOL.ProofSyntaxStructural

/-!
# Coherent HOL proof actions on predicate families

Identity and composition are built as actual HOL derivation trees. Their
interpretations are respectively the identity and composite maps of
refinement witnesses. Simultaneous substitution traverses the retained
proof tree and reindexes its satisfied hypotheses; the resulting sections
and refinement maps commute with the existing family-substitution maps.

Truth-valued fibres intentionally forget proof strategy. These laws compare
their interpreted actions, not the retained derivation trees. The target is
the admissible Henkin families interpretation, not native dependent syntax.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.HenkinPredicateFamilyCoherence

open Mettapedia.Logic.HOL.Embedding.HenkinDependentFamilyInterpretation
open Mettapedia.Logic.HOL.Embedding.HenkinPredicateFamilyInterpretation

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

private theorem instantiate_bound_weaken {Γ : Ctx Base} {A B : Ty Base}
    (term : Term Const (A :: Γ) B) :
    instantiate (.var .vz) (HOL.rename (Rename.lift Rename.weaken) term) = term := by
  unfold instantiate
  rw [HOL.subst_rename]
  calc
    _ = HOL.subst Subst.id term := by
      apply HOL.subst_ext
      intro T index
      cases index <;> rfl
    _ = term := HOL.subst_id term

/-- Specialize a retained universal at the newly bound variable. The old
parameters are weakened, so the instantiation does not capture them. -/
def specializeBound {Γ : Ctx Base} {A : Ty Base}
    {hypotheses : List (Formula Const Γ)} {φ : Formula Const (A :: Γ)}
    (proof : ProofSyntax Const hypotheses (.all φ)) :
    ProofSyntax Const (weakenHyps hypotheses) φ := by
  change ProofSyntax Const (hypotheses.map (HOL.rename Rename.weaken)) φ
  simpa only [instantiate_bound_weaken] using
    ProofSyntax.allE (.var .vz) (ProofSyntax.rename Rename.weaken proof)

/-- The universally quantified identity implication, as retained syntax. -/
def identityProof {Γ : Ctx Base} {A : Ty Base}
    (hypotheses : List (Formula Const Γ)) (φ : Formula Const (A :: Γ)) :
    ProofSyntax Const hypotheses (.all (.imp φ φ)) :=
  .allI (.impI (.hyp ⟨0, by simp⟩))

/-- Compose two universally quantified implications by specialization,
implication elimination, and universal introduction in the object calculus. -/
def composeProof {Γ : Ctx Base} {A : Ty Base}
    {hypotheses : List (Formula Const Γ)} {φ ψ χ : Formula Const (A :: Γ)}
    (first : ProofSyntax Const hypotheses (.all (.imp φ ψ)))
    (second : ProofSyntax Const hypotheses (.all (.imp ψ χ))) :
    ProofSyntax Const hypotheses (.all (.imp φ χ)) :=
  .allI (.impI (.impE (ProofSyntax.prepend φ (specializeBound second))
    (.impE (ProofSyntax.prepend φ (specializeBound first)) (.hyp ⟨0, by simp⟩))))

/-- Interpreting the actual identity proof leaves every witness unchanged. -/
theorem refinementMap_identity
    (M : HenkinModel.{u, v, w} Base Const) (respects : M.FunctionsRespectEqv)
    {Γ : Ctx Base} {A : Ty Base} (hypotheses : List (Formula Const Γ))
    (φ : Formula Const (A :: Γ)) (valuation : SatisfiedContext M hypotheses) :
    refinementMapOfProof M respects (identityProof hypotheses φ) valuation = id := by
  funext point
  cases point
  rfl

/-- Interpreting the actual composite proof agrees with composing the two
interpreted refinement maps, not merely with their inhabitation claims. -/
theorem refinementMap_composition
    (M : HenkinModel.{u, v, w} Base Const) (respects : M.FunctionsRespectEqv)
    {Γ : Ctx Base} {A : Ty Base} {hypotheses : List (Formula Const Γ)}
    {φ ψ χ : Formula Const (A :: Γ)}
    (first : ProofSyntax Const hypotheses (.all (.imp φ ψ)))
    (second : ProofSyntax Const hypotheses (.all (.imp ψ χ)))
    (valuation : SatisfiedContext M hypotheses) :
    refinementMapOfProof M respects (composeProof first second) valuation =
      (refinementMapOfProof M respects second valuation) ∘
        (refinementMapOfProof M respects first valuation) := by
  funext point
  rfl

/-- A valuation satisfying substituted hypotheses pulls back to a valuation
satisfying the original hypotheses, by the actual HOL substitution theorem. -/
def pullSatisfiedContext (M : HenkinModel.{u, v, w} Base Const)
    {Γ Γ' : Ctx Base} {hypotheses : List (Formula Const Γ)}
    (θ : Subst Const Γ Γ')
    (valuation : SatisfiedContext M (hypotheses.map (HOL.subst θ))) :
    SatisfiedContext M hypotheses :=
  ⟨interpretSubstitution M θ valuation.1, by
    intro φ member
    have holds := valuation.2 (HOL.subst θ φ) (List.mem_map.mpr ⟨φ, member, rfl⟩)
    change (M.denote φ (Soundness.substVal M θ valuation.1.1)).down
    rw [Soundness.denote_subst] at holds
    exact holds⟩

/-- The truth-family substitution equivalence at one valuation. -/
def truthSubstitutionEquiv (M : HenkinModel.{u, v, w} Base Const)
    {Γ Γ' : Ctx Base} (φ : Formula Const Γ) (θ : Subst Const Γ Γ')
    (valuation : AdmissibleContext M Γ') :
    truthFamily M (HOL.subst θ φ) valuation ≃
      truthFamily M φ (interpretSubstitution M θ valuation) :=
  Equiv.cast (congrFun (truthFamily_substitution M φ θ) valuation)

/-- Substituting the retained derivation and then interpreting it gives
the original section at the pulled-back satisfying valuation. -/
theorem proofSection_substitution
    (M : HenkinModel.{u, v, w} Base Const) (respects : M.FunctionsRespectEqv)
    {Γ Γ' : Ctx Base} {hypotheses : List (Formula Const Γ)} {φ : Formula Const Γ}
    (θ : Subst Const Γ Γ') (proof : ProofSyntax Const hypotheses φ)
    (valuation : SatisfiedContext M (hypotheses.map (HOL.subst θ))) :
    truthSubstitutionEquiv M φ θ valuation.1
        (proofSection M respects (ProofSyntax.subst θ proof) valuation) =
      proofSection M respects proof (pullSatisfiedContext M θ valuation) := by
  rfl

/-- The section supplied by a universal proof also commutes pointwise with
parameter substitution, at every admitted argument. -/
theorem universalProofSection_substitution
    (M : HenkinModel.{u, v, w} Base Const) (respects : M.FunctionsRespectEqv)
    {Γ Γ' : Ctx Base} {A : Ty Base} {hypotheses : List (Formula Const Γ)}
    {φ : Formula Const (A :: Γ)} (θ : Subst Const Γ Γ')
    (proof : ProofSyntax Const hypotheses (.all φ))
    (valuation : SatisfiedContext M (hypotheses.map (HOL.subst θ)))
    (value : AdmissibleValue M A) :
    Equiv.cast (predicateFamily_substitution M φ θ valuation.1 value)
        (universalProofSection M respects (ProofSyntax.subst θ proof) valuation value) =
      universalProofSection M respects proof (pullSatisfiedContext M θ valuation) value := by
  rfl

/-- The substitution square commutes on refinement witnesses for every
actual retained proof of a universally quantified implication. -/
theorem refinementMap_substitution
    (M : HenkinModel.{u, v, w} Base Const) (respects : M.FunctionsRespectEqv)
    {Γ Γ' : Ctx Base} {A : Ty Base} {hypotheses : List (Formula Const Γ)}
    {φ ψ : Formula Const (A :: Γ)}
    (θ : Subst Const Γ Γ')
    (proof : ProofSyntax Const hypotheses (.all (.imp φ ψ)))
    (valuation : SatisfiedContext M (hypotheses.map (HOL.subst θ)))
    (point : refinementFamily M (HOL.subst (Subst.lift θ) φ) valuation.1) :
    refinementSubstitutionEquiv M ψ θ valuation.1
        (refinementMapOfProof M respects (ProofSyntax.subst θ proof) valuation point) =
      refinementMapOfProof M respects proof (pullSatisfiedContext M θ valuation)
        (refinementSubstitutionEquiv M φ θ valuation.1 point) := by
  rfl

/-! ## Higher-order substitution with an actual free parameter -/

namespace Controls

open HenkinModel.ModelPropertyCanary
open HenkinPredicateFamilyInterpretation.Controls

/-- Substitute `Q := fun x => True` and `P := fun x => x = y`.
The target retains a free Boolean parameter `y`; it is not a ground chart. -/
def predicateSubstitution :
    Subst (NoConstants Unit) [boolean ⇒ .prop, boolean ⇒ .prop] [boolean]
  | _, .vz => .lam .top
  | _, .vs .vz => .lam (.eq (.var .vz) (.var (.vs .vz)))
  | _, .vs (.vs index) => nomatch index

def matchingParameter : Formula (NoConstants Unit) [boolean, boolean] :=
  HOL.subst (Subst.lift predicateSubstitution) (firstPredicate boolean)

def trivialPredicate : Formula (NoConstants Unit) [boolean, boolean] :=
  HOL.subst (Subst.lift predicateSubstitution) (secondPredicate boolean)

/-- The free `y` crosses both the predicate argument binder and the lambda
binder. Its index is two, not either of the freshly bound variables. -/
theorem substitution_avoids_capture :
    matchingParameter =
      .app (.lam (.eq (.var .vz) (.var (.vs (.vs .vz))))) (.var .vz) := rfl

/-- Instantiate a genuine higher-order derivation using the proof traversal. -/
def instantiatedProjection :
    ProofSyntax (NoConstants Unit)
      ([] : List (Formula (NoConstants Unit) [boolean]))
      (.all (.imp (.and matchingParameter trivialPredicate) matchingParameter)) :=
  ProofSyntax.subst predicateSubstitution (intersectionProjection boolean)

/-- In this non-ground instance the retained proof still has its four
ordered rule nodes: universal introduction, implication introduction,
conjunction elimination, and the hypothesis occurrence. -/
theorem instantiated_projection_retains_nodes : instantiatedProjection.nodeCount = 4 := by
  rfl

def parameterTrue : AdmissibleContext model [boolean] :=
  extendContext model HenkinPredicateFamilyInterpretation.Controls.emptyValuation trueValue

def parameterFalse : AdmissibleContext model [boolean] :=
  extendContext model HenkinPredicateFamilyInterpretation.Controls.emptyValuation falseValue

def satisfiedTrue : SatisfiedContext model
    ([] : List (Formula (NoConstants Unit) [boolean])) :=
  ⟨parameterTrue, by intro φ member; cases member⟩

def matchingWitness :
    refinementFamily model (.and matchingParameter trivialPredicate) parameterTrue :=
  ⟨trueValue, ⟨⟨rfl, True.intro⟩⟩⟩

def instantiatedResult : refinementFamily model matchingParameter parameterTrue :=
  refinementMapOfProof model
    (model.functionsRespectEqv_of_fullDomains booleanBaseModel_fullDomains)
    instantiatedProjection satisfiedTrue matchingWitness

theorem instantiated_result_retains_value : instantiatedResult.1 = trueValue := rfl

theorem mismatching_argument_rejected :
    ¬ Nonempty (predicateFamily model matchingParameter parameterTrue falseValue) := by
  rintro ⟨witness⟩
  have equal : (⟨false⟩ : ULift Bool) = ⟨true⟩ := witness.down.down
  exact Bool.false_ne_true (congrArg ULift.down equal)

/-- A changed free parameter changes which arguments inhabit the same
instantiated syntax. It was not captured by either local binder. -/
theorem changed_parameter_changes_membership :
    Nonempty (predicateFamily model matchingParameter parameterFalse falseValue) ∧
      ¬ Nonempty (predicateFamily model matchingParameter parameterFalse trueValue) := by
  constructor
  · exact ⟨⟨⟨rfl⟩⟩⟩
  · rintro ⟨witness⟩
    have equal : (⟨true⟩ : ULift Bool) = ⟨false⟩ := witness.down.down
    exact Bool.false_ne_true (congrArg ULift.down equal.symm)

/-- The non-ground higher-order instantiation satisfies the actual
refinement naturality square, retaining its true-valued witness. -/
theorem instantiated_projection_naturality :
    refinementSubstitutionEquiv model (firstPredicate boolean)
        predicateSubstitution parameterTrue instantiatedResult =
      refinementMapOfProof model
        (model.functionsRespectEqv_of_fullDomains booleanBaseModel_fullDomains)
        (intersectionProjection boolean)
        (pullSatisfiedContext model predicateSubstitution satisfiedTrue)
        (refinementSubstitutionEquiv model
          (.and (firstPredicate boolean) (secondPredicate boolean))
          predicateSubstitution parameterTrue matchingWitness) :=
  refinementMap_substitution model
    (model.functionsRespectEqv_of_fullDomains booleanBaseModel_fullDomains)
    predicateSubstitution (intersectionProjection boolean) satisfiedTrue matchingWitness

end Controls

#print axioms ProofSyntax.subst
#print axioms ProofSyntax.subst_erasure
#print axioms specializeBound
#print axioms composeProof
#print axioms refinementMap_identity
#print axioms refinementMap_composition
#print axioms pullSatisfiedContext
#print axioms proofSection_substitution
#print axioms universalProofSection_substitution
#print axioms refinementMap_substitution
#print axioms Controls.substitution_avoids_capture
#print axioms Controls.instantiatedProjection
#print axioms Controls.instantiated_projection_retains_nodes
#print axioms Controls.instantiated_projection_naturality
#print axioms Controls.mismatching_argument_rejected
#print axioms Controls.changed_parameter_changes_membership

end Mettapedia.Logic.HOL.Embedding.HenkinPredicateFamilyCoherence
