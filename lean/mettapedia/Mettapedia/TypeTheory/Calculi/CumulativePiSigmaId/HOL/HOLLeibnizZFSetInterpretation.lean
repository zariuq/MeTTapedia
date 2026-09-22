import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLLeibnizProofComparison
import Mettapedia.Logic.HOL.Embedding.ZFSetUniverseInterpretation

/-!
# Retained predicate equality in the actual set/universe interpretation

The source HOL comparison between primitive equality and predicate equality
is interpreted in the existing Henkin model. Its retained proof trees then
act on bounded predicates, their dependent refinements and their actual
separated sets. Substitution preserves these actions. This is the set-side
interpretation of the source proofs, not a native dependent-calculus model.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLLeibnizZFSetInterpretation

open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding
open HenkinDependentFamilyInterpretation HenkinPredicateFamilyInterpretation
open HenkinPredicateFamilyCoherence
open ZFSetHenkinInterpretation ZFSetUniverseClosure ZFSetUniverseInterpretation

open HOLLeibnizProofComparison

universe u v w

/-! ## Interpreting the actual source comparison -/

/-- The retained source comparison has its advertised meaning independently
of whether a native compiler handles its equality inferences. -/
theorem leibniz_iff_primitive {Base : Type u} {Const : Ty Base → Type v}
    (M : HenkinModel.{u, v, w} Base Const) (respects : M.FunctionsRespectEqv)
    {Γ : Ctx Base} {A : Ty Base} (x y : Term Const Γ A)
    (valuation : AdmissibleContext M Γ) :
    (M.denote (Source.leibniz x y) valuation.1).down ↔
      (M.denote (.eq x y) valuation.1).down := by
  have both := Soundness.extDerivation_sound (Source.equivalence x y).erase
    respects valuation.2 (by intro φ member; cases member)
  exact ⟨both.2, both.1⟩

theorem leibniz_denotation {Base : Type u} {Const : Ty Base → Type v}
    (M : HenkinModel.{u, v, w} Base Const) (respects : M.FunctionsRespectEqv)
    {Γ : Ctx Base} {A : Ty Base} (x y : Term Const Γ A)
    (valuation : AdmissibleContext M Γ) :
    M.denote (Source.leibniz x y) valuation.1 =
      M.denote (.eq x y) valuation.1 := by
  apply ULift.down_injective
  exact propext (leibniz_iff_primitive M respects x y valuation)

theorem universe_leibniz_denotation (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} (x y : UniverseExpr Γ A)
    (valuation : AdmissibleContext (universeModel h) Γ) :
    (universeModel h).denote (Source.leibniz x y) valuation.1 =
      (universeModel h).denote (.eq x y) valuation.1 :=
  leibniz_denotation (universeModel h) (universeFunctionsRespectEqv h) x y valuation

/-- The universe-signature extension commutes with the actual source
predicate-equality formula, including its predicate binder. -/
theorem embed_leibniz {Γ : Ctx Unit} {A : Ty Unit} (x y : Expr Γ A) :
    embed (Source.leibniz x y) = Source.leibniz (embed x) (embed y) := by
  simp only [embed, Source.leibniz, substConst, substConst_weaken]

/-! ## Retained equality supplies a uniform predicate implication -/

/-- The bound variable is the set element; `x` is a parameter of the
predicate. These binders must not be conflated during substitution. -/
def atParameter {Base : Type u} {Const : Ty Base → Type v}
    {Γ : Ctx Base} {A B : Ty Base}
    (predicate : Term Const (B :: Γ) (A ⇒ .prop)) (x : Term Const Γ A) :
    Formula Const (B :: Γ) :=
  .app predicate (weaken x)

theorem atParameter_subst {Base : Type u} {Const : Ty Base → Type v}
    {Γ Δ : Ctx Base} {A B : Ty Base} (θ : Subst Const Γ Δ)
    (predicate : Term Const (B :: Γ) (A ⇒ .prop)) (x : Term Const Γ A) :
    subst (Subst.lift θ) (atParameter predicate x) =
      atParameter (subst (Subst.lift θ) predicate) (subst θ x) := by
  simp only [atParameter, subst, subst_weaken]

/-- Specialize the given equality proof at the actual predicate, retaining
its derivation under the additional object binder. -/
def equalityPredicateProof {Base : Type u} {Const : Ty Base → Type v}
    {Γ : Ctx Base} {A B : Ty Base} {hypotheses : List (Formula Const Γ)}
    {x y : Term Const Γ A} (predicate : Term Const (B :: Γ) (A ⇒ .prop))
    (equality : ProofSyntax Const hypotheses (Source.leibniz x y)) :
    ProofSyntax Const hypotheses
      (.all (.imp (atParameter predicate x) (atParameter predicate y))) := by
  apply ProofSyntax.allI
  apply Source.specialize (weaken x) (weaken y) predicate
  change ProofSyntax Const (hypotheses.map (rename Rename.weaken))
    (Source.leibniz (rename Rename.weaken x) (rename Rename.weaken y))
  simpa only [Source.leibniz_rename] using
    ProofSyntax.rename Rename.weaken equality

def primitivePredicateProof {Base : Type u} {Const : Ty Base → Type v}
    {Γ : Ctx Base} {A B : Ty Base} {hypotheses : List (Formula Const Γ)}
    {x y : Term Const Γ A} (predicate : Term Const (B :: Γ) (A ⇒ .prop))
    (equality : ProofSyntax Const hypotheses (.eq x y)) :
    ProofSyntax Const hypotheses
      (.all (.imp (atParameter predicate x) (atParameter predicate y))) :=
  equalityPredicateProof predicate (Source.ofPrimitive equality)

/-! ## The same separated sets and dependent refinements -/

def boundedPredicate {Γ : Ctx Unit} (bound : UniverseExpr Γ set)
    (φ : Formula UniverseSymbol (set :: Γ)) : Formula UniverseSymbol (set :: Γ) :=
  .and (inSet (.var .vz) (weaken bound)) φ

theorem mem_separatedSet (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    (bound : UniverseExpr Γ set) (φ : Formula UniverseSymbol (set :: Γ))
    (valuation : AdmissibleContext (universeModel h) Γ) (x : ZFSet.{u}) :
    x ∈ universePredicateSet h bound φ valuation ↔
      ((universeModel h).denote (boundedPredicate bound φ)
        ((universeModel h).extend (σ := set) valuation.1 x)).down := by
  change (x ∈ ZFSet.sep _ _) ↔
    (x ∈ (show ZFSet.{u} from (universeModel h).denote (weaken bound)
      ((universeModel h).extend (σ := set) valuation.1 x)) ∧ _)
  erw [ZFSet.mem_sep, Soundness.denote_weaken]

/-- This is the existing `universePredicateSet`, not a second set encoding. -/
noncomputable def refinementSetEquiv (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    (bound : UniverseExpr Γ set) (φ : Formula UniverseSymbol (set :: Γ))
    (valuation : AdmissibleContext (universeModel h) Γ) :
    refinementFamily (universeModel h) (boundedPredicate bound φ) valuation ≃
      {x : ZFSet.{u} // x ∈ universePredicateSet h bound φ valuation} where
  toFun point := ⟨point.1.1, (mem_separatedSet h bound φ valuation point.1.1).mpr
    point.2.down.down⟩
  invFun point := ⟨⟨point.1, trivial⟩, ⟨⟨
    (mem_separatedSet h bound φ valuation point.1).mp point.2⟩⟩⟩
  left_inv point := by cases point; rfl
  right_inv point := by cases point; rfl

def boundedPredicateProof {Γ : Ctx Unit} (bound : UniverseExpr Γ set)
    {hypotheses : List (Formula UniverseSymbol Γ)}
    {φ ψ : Formula UniverseSymbol (set :: Γ)}
    (proof : ProofSyntax UniverseSymbol hypotheses (.all (.imp φ ψ))) :
    ProofSyntax UniverseSymbol hypotheses
      (.all (.imp (boundedPredicate bound φ) (boundedPredicate bound ψ))) :=
  .allI (.impI (.andI (.andEL (.hyp ⟨0, by simp⟩))
    (.impE ((specializeBound proof).prepend _) (.andER (.hyp ⟨0, by simp⟩)))))

noncomputable def separatedSetMap (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    (bound : UniverseExpr Γ set) {hypotheses : List (Formula UniverseSymbol Γ)}
    {φ ψ : Formula UniverseSymbol (set :: Γ)}
    (proof : ProofSyntax UniverseSymbol hypotheses (.all (.imp φ ψ)))
    (valuation : SatisfiedContext (universeModel h) hypotheses) :
    {x : ZFSet.{u} // x ∈ universePredicateSet h bound φ valuation.1} →
      {x : ZFSet.{u} // x ∈ universePredicateSet h bound ψ valuation.1} :=
  fun point => ⟨point.1, by
    have memberSource := point.2
    change point.1 ∈ ZFSet.sep _ _ at memberSource
    obtain ⟨inBound, inPredicate⟩ := ZFSet.mem_sep.mp memberSource
    apply ZFSet.mem_sep.mpr
    refine ⟨inBound, ?_⟩
    have valid := Soundness.extDerivation_sound proof.erase
      (universeFunctionsRespectEqv h) valuation.1.2 valuation.2
    exact valid point.1 trivial inPredicate⟩

theorem separatedSetMap_preserves_value (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} (bound : UniverseExpr Γ set)
    {hypotheses : List (Formula UniverseSymbol Γ)}
    {φ ψ : Formula UniverseSymbol (set :: Γ)}
    (proof : ProofSyntax UniverseSymbol hypotheses (.all (.imp φ ψ)))
    (valuation : SatisfiedContext (universeModel h) hypotheses)
    (point : {x : ZFSet.{u} // x ∈ universePredicateSet h bound φ valuation.1}) :
    (separatedSetMap h bound proof valuation point).1 = point.1 := rfl

/-- The separated-set action and the dependent-refinement action use the
same retained proof, and agree on the actual witness. -/
theorem refinement_set_square (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    (bound : UniverseExpr Γ set) {hypotheses : List (Formula UniverseSymbol Γ)}
    {φ ψ : Formula UniverseSymbol (set :: Γ)}
    (proof : ProofSyntax UniverseSymbol hypotheses (.all (.imp φ ψ)))
    (valuation : SatisfiedContext (universeModel h) hypotheses)
    (point : refinementFamily (universeModel h) (boundedPredicate bound φ) valuation.1) :
    refinementSetEquiv h bound ψ valuation.1
        (refinementMapOfProof (universeModel h) (universeFunctionsRespectEqv h)
          (boundedPredicateProof bound proof) valuation point) =
      separatedSetMap h bound proof valuation
        (refinementSetEquiv h bound φ valuation.1 point) := by
  apply Subtype.ext
  rfl

/-- The source equality tree acts on these exact separated sets. -/
noncomputable def equalitySetMap (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    {A : Ty Unit} (bound : UniverseExpr Γ set)
    {hypotheses : List (Formula UniverseSymbol Γ)} {x y : UniverseExpr Γ A}
    (predicate : UniverseExpr (set :: Γ) (A ⇒ .prop))
    (equality : ProofSyntax UniverseSymbol hypotheses (Source.leibniz x y))
    (valuation : SatisfiedContext (universeModel h) hypotheses) :
    {z : ZFSet.{u} // z ∈ universePredicateSet h bound (atParameter predicate x) valuation.1} →
      {z : ZFSet.{u} // z ∈ universePredicateSet h bound (atParameter predicate y) valuation.1} :=
  separatedSetMap h bound (equalityPredicateProof predicate equality) valuation

theorem equality_refinement_set_square (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    {A : Ty Unit} (bound : UniverseExpr Γ set)
    {hypotheses : List (Formula UniverseSymbol Γ)} {x y : UniverseExpr Γ A}
    (predicate : UniverseExpr (set :: Γ) (A ⇒ .prop))
    (equality : ProofSyntax UniverseSymbol hypotheses (Source.leibniz x y))
    (valuation : SatisfiedContext (universeModel h) hypotheses)
    (point : refinementFamily (universeModel h)
      (boundedPredicate bound (atParameter predicate x)) valuation.1) :
    refinementSetEquiv h bound (atParameter predicate y) valuation.1
        (refinementMapOfProof (universeModel h) (universeFunctionsRespectEqv h)
          (boundedPredicateProof bound (equalityPredicateProof predicate equality))
          valuation point) =
      equalitySetMap h bound predicate equality valuation
        (refinementSetEquiv h bound (atParameter predicate x) valuation.1 point) :=
  refinement_set_square h bound (equalityPredicateProof predicate equality) valuation point

/-- Reverse transport is also built from retained source inferences, rather
than assumed when the two sets are compared. -/
theorem predicateSets_equal_of_equality (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    {A : Ty Unit} (bound : UniverseExpr Γ set)
    {hypotheses : List (Formula UniverseSymbol Γ)} {x y : UniverseExpr Γ A}
    (predicate : UniverseExpr (set :: Γ) (A ⇒ .prop))
    (equality : ProofSyntax UniverseSymbol hypotheses (Source.leibniz x y))
    (valuation : SatisfiedContext (universeModel h) hypotheses) :
    universePredicateSet h bound (atParameter predicate x) valuation.1 =
      universePredicateSet h bound (atParameter predicate y) valuation.1 := by
  apply ZFSet.ext
  intro z
  constructor
  · intro hz
    exact (equalitySetMap h bound predicate equality valuation ⟨z, hz⟩).2
  · intro hz
    let reverse := Source.ofPrimitive (.eqSymm (Source.toPrimitive equality))
    exact (equalitySetMap h bound predicate reverse valuation ⟨z, hz⟩).2

/-! ## Substitution on the same proof action -/

theorem separatedSet_substitution (h : CofinalInaccessibles.{u}) {Γ Δ : Ctx Unit}
    (bound : UniverseExpr Γ set) (φ : Formula UniverseSymbol (set :: Γ))
    (θ : Subst UniverseSymbol Γ Δ)
    (valuation : AdmissibleContext (universeModel h) Δ) :
    universePredicateSet h (subst θ bound) (subst (Subst.lift θ) φ) valuation =
      universePredicateSet h bound φ (interpretSubstitution (universeModel h) θ valuation) := by
  apply ZFSet.ext
  intro z
  unfold universePredicateSet
  erw [ZFSet.mem_sep, ZFSet.mem_sep, Soundness.denote_subst,
    Soundness.denote_subst, Soundness.substVal_lift]
  rfl

/-- Reindex membership proofs without replacing their set element. -/
def setElementsEquiv {a b : ZFSet.{u}} (equal : a = b) :
    {x : ZFSet.{u} // x ∈ a} ≃ {x : ZFSet.{u} // x ∈ b} where
  toFun point := ⟨point.1, equal ▸ point.2⟩
  invFun point := ⟨point.1, equal.symm ▸ point.2⟩
  left_inv point := by cases point; rfl
  right_inv point := by cases point; rfl

noncomputable def setSubstitutionEquiv (h : CofinalInaccessibles.{u}) {Γ Δ : Ctx Unit}
    (bound : UniverseExpr Γ set) (φ : Formula UniverseSymbol (set :: Γ))
    (θ : Subst UniverseSymbol Γ Δ)
    (valuation : AdmissibleContext (universeModel h) Δ) :
    {x : ZFSet.{u} // x ∈ universePredicateSet h (subst θ bound)
      (subst (Subst.lift θ) φ) valuation} ≃
    {x : ZFSet.{u} // x ∈ universePredicateSet h bound φ
      (interpretSubstitution (universeModel h) θ valuation)} :=
  setElementsEquiv (separatedSet_substitution h bound φ θ valuation)

/-- The substitution traverses the actual proof tree. Its interpreted set
action agrees with reindexing the original action at the satisfying context. -/
theorem setMap_substitution (h : CofinalInaccessibles.{u}) {Γ Δ : Ctx Unit}
    (bound : UniverseExpr Γ set) {hypotheses : List (Formula UniverseSymbol Γ)}
    {φ ψ : Formula UniverseSymbol (set :: Γ)} (θ : Subst UniverseSymbol Γ Δ)
    (proof : ProofSyntax UniverseSymbol hypotheses (.all (.imp φ ψ)))
    (valuation : SatisfiedContext (universeModel h) (hypotheses.map (subst θ)))
    (point : {x : ZFSet.{u} // x ∈ universePredicateSet h (subst θ bound)
      (subst (Subst.lift θ) φ) valuation.1}) :
    setSubstitutionEquiv h bound ψ θ valuation.1
        (separatedSetMap h (subst θ bound) (ProofSyntax.subst θ proof) valuation point) =
      separatedSetMap h bound proof (pullSatisfiedContext (universeModel h) θ valuation)
        (setSubstitutionEquiv h bound φ θ valuation.1 point) := by
  apply Subtype.ext
  rfl

theorem equality_setMap_substitution (h : CofinalInaccessibles.{u})
    {Γ Δ : Ctx Unit} {A : Ty Unit} (bound : UniverseExpr Γ set)
    {hypotheses : List (Formula UniverseSymbol Γ)} {x y : UniverseExpr Γ A}
    (predicate : UniverseExpr (set :: Γ) (A ⇒ .prop))
    (equality : ProofSyntax UniverseSymbol hypotheses (Source.leibniz x y))
    (θ : Subst UniverseSymbol Γ Δ)
    (valuation : SatisfiedContext (universeModel h) (hypotheses.map (subst θ)))
    (point : {z : ZFSet.{u} // z ∈ universePredicateSet h (subst θ bound)
      (subst (Subst.lift θ) (atParameter predicate x)) valuation.1}) :
    setSubstitutionEquiv h bound (atParameter predicate y) θ valuation.1
        (separatedSetMap h (subst θ bound)
          (ProofSyntax.subst θ (equalityPredicateProof predicate equality)) valuation point) =
      equalitySetMap h bound predicate equality
        (pullSatisfiedContext (universeModel h) θ valuation)
        (setSubstitutionEquiv h bound (atParameter predicate x) θ valuation.1 point) :=
  setMap_substitution h bound θ (equalityPredicateProof predicate equality) valuation point

theorem leibniz_denotation_substitution (h : CofinalInaccessibles.{u})
    {Γ Δ : Ctx Unit} {A : Ty Unit} (x y : UniverseExpr Γ A)
    (θ : Subst UniverseSymbol Γ Δ)
    (valuation : AdmissibleContext (universeModel h) Δ) :
    (universeModel h).denote (Source.leibniz (subst θ x) (subst θ y)) valuation.1 =
      (universeModel h).denote (.eq x y)
        (interpretSubstitution (universeModel h) θ valuation).1 := by
  rw [← Source.leibniz_subst, Soundness.denote_subst]
  exact universe_leibniz_denotation h x y
    (interpretSubstitution (universeModel h) θ valuation)

/-! ## Computing transport and changed-predicate controls -/

namespace Controls

def emptyTerm : UniverseExpr [] set := .const (.core .empty)

def bound : UniverseExpr [] set := .app (.const (.core .power)) emptyTerm

/-- A genuine authored beta redex, not a second name for the empty constant. -/
def betaEmpty : UniverseExpr [] set := .app (.lam (.var .vz)) emptyTerm

/-- The set element remains the outer variable of the parameter lambda. -/
def equalsParameter : UniverseExpr [set] (set ⇒ .prop) :=
  .lam (.eq (.var (.vs .vz)) (.var .vz))

def betaEquality : ProofSyntax UniverseSymbol
    ([] : List (Formula UniverseSymbol [])) (Source.leibniz betaEmpty emptyTerm) :=
  Source.ofPrimitive (ProofSyntax.beta emptyTerm (.var .vz))

theorem betaEquality_retains_inferences : betaEquality.nodeCount > 1 := by decide

noncomputable def satisfiedEmpty (h : CofinalInaccessibles.{u}) :
    SatisfiedContext (universeModel h) ([] : List (Formula UniverseSymbol [])) :=
  ⟨universeEmptyContext h, by intro φ member; cases member⟩

noncomputable def betaPoint (h : CofinalInaccessibles.{u}) :
    {z : ZFSet.{u} // z ∈ universePredicateSet h bound
      (atParameter equalsParameter betaEmpty) (universeEmptyContext h)} :=
  ⟨∅, ZFSet.mem_sep.mpr ⟨ZFSet.mem_powerset.mpr (fun _ hx => hx), rfl⟩⟩

noncomputable def transportedBetaPoint (h : CofinalInaccessibles.{u}) :
    {z : ZFSet.{u} // z ∈ universePredicateSet h bound
      (atParameter equalsParameter emptyTerm) (universeEmptyContext h)} :=
  equalitySetMap h bound equalsParameter betaEquality (satisfiedEmpty h) (betaPoint h)

theorem beta_transport_retains_element (h : CofinalInaccessibles.{u}) :
    (transportedBetaPoint h).1 = (∅ : ZFSet.{u}) := rfl

theorem empty_ne_power_empty : (∅ : ZFSet.{u}) ≠ ZFSet.powerset ∅ := by
  intro heq
  have member : (∅ : ZFSet.{u}) ∈ ZFSet.powerset ∅ :=
    ZFSet.mem_powerset.mpr (fun _ hx => hx)
  rw [← heq] at member
  exact ZFSet.mem_irrefl _ member

/-- Keeping the element but changing the equality parameter from empty to
its powerset does not preserve the predicate fibre. -/
theorem changed_parameter_rejects_element (h : CofinalInaccessibles.{u}) :
    ¬ Nonempty (predicateFamily (universeModel h)
      (atParameter equalsParameter bound) (universeEmptyContext h)
      ⟨(∅ : ZFSet.{u}), trivial⟩) := by
  rintro ⟨point⟩
  exact empty_ne_power_empty point.down.down

/-- This cannot be repaired by claiming an equality proof under the
combined validated set/universe theory. -/
theorem changed_parameter_has_no_equality_proof (h : CofinalInaccessibles.{u}) :
    ¬ Nonempty (ProofSyntax UniverseSymbol universeTheory
      (Source.leibniz emptyTerm bound)) := by
  rintro ⟨proof⟩
  have holds := (universeTheoremSection h proof).down.down
  have equal := (leibniz_iff_primitive (universeModel h)
    (universeFunctionsRespectEqv h) emptyTerm bound (universeEmptyContext h)).mp holds
  exact empty_ne_power_empty equal

/-- Even reflexive equality only transports one fixed predicate; it cannot
turn the previous inhabited refinement into a false-predicate refinement. -/
theorem changed_predicate_has_no_refinement (h : CofinalInaccessibles.{u}) :
    ¬ Nonempty (refinementFamily (universeModel h)
      (boundedPredicate bound .bot) (universeEmptyContext h)) := by
  rintro ⟨point⟩
  exact point.2.down.down.2

def freeParameterSubstitution : Subst UniverseSymbol [set] [set]
  | _, .vz => .app (.lam (.var .vz)) (.var .vz)
  | _, .vs index => nomatch index

def freePredicate : UniverseExpr [set, set] (set ⇒ .prop) :=
  .lam (.eq (.var (.vs .vz)) (.var .vz))

/-- The substituted free parameter crosses both the set-element binder and
the predicate lambda. It is not captured by either newly bound variable. -/
theorem free_parameter_substitution_shape :
    subst (Subst.lift freeParameterSubstitution)
        (atParameter freePredicate (.var .vz)) =
      .app (.lam (.eq (.var (.vs .vz)) (.var .vz)))
        (.app (.lam (.var .vz)) (.var (.vs .vz))) := rfl

end Controls

#print axioms leibniz_denotation
#print axioms universe_leibniz_denotation
#print axioms embed_leibniz
#print axioms equalityPredicateProof
#print axioms primitivePredicateProof
#print axioms equality_refinement_set_square
#print axioms predicateSets_equal_of_equality
#print axioms separatedSet_substitution
#print axioms setMap_substitution
#print axioms equality_setMap_substitution
#print axioms leibniz_denotation_substitution
#print axioms Controls.betaEquality
#print axioms Controls.transportedBetaPoint
#print axioms Controls.changed_parameter_rejects_element
#print axioms Controls.changed_parameter_has_no_equality_proof
#print axioms Controls.changed_predicate_has_no_refinement
#print axioms Controls.free_parameter_substitution_shape

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLLeibnizZFSetInterpretation
