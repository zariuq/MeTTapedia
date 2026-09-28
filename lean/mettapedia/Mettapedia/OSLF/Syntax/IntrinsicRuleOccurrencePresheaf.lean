import Mettapedia.OSLF.Syntax.IntrinsicScopedConditionalModelPresheaf
import Mettapedia.OSLF.Syntax.ScopedOperationalEvidenceExponential

/-!
# Contextual families of authored rule occurrences

A selected authored rule has a presheaf of its actual instances: a contextual
metavariable valuation and an environment closing the rule's ordinary
variables. The action along a context map is the existing simultaneous
substitution on instances. This is the parameter object needed to specify
the endpoints requested by each binder-local premise.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicRuleOccurrencePresheaf

open _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open Mettapedia.OSLF.Binding.BindingSubstitutionAlgebra
open Mettapedia.OSLF.Binding.SemanticContextualMetavariables
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalPresheaf
open Mettapedia.OSLF.Binding.ScopedOperationalEvidenceExponential
open Mettapedia.OSLF.Binding.MultiBinderPresheaf
open Mettapedia.OSLF.Binding.SemanticScopedPremiseInterpretation

universe u
variable {S : Signature} {M : List (MetaArity S)}
variable (R : List (Rule S M))
variable {A : BindingCloneAlgebra.Algebra.{u} S}

/-- Instances of one selected authored rule in an ambient context. The
index is retained even when two authored rules have the same endpoints. -/
structure OccurrenceAt (index : Fin R.length) (Γ : Ctx S) : Type u where
  valuation : Valuation (M := M) A Γ
  close : Environment S A.substitution.Carrier
    (R.get index).conclusion.ctx Γ

/-- Read the selected contextual parameters as the original intrinsic
constructor occurrence used by the free rule algebra. -/
def OccurrenceAt.toInstance (index : Fin R.length) {Γ : Ctx S}
    (occurrence : OccurrenceAt R (A := A) index Γ) : Instance R A :=
  ⟨index, Γ, occurrence.valuation, occurrence.close⟩

/-- Substitution of a rule occurrence along an actual context arrow. -/
def reindexOccurrence (index : Fin R.length)
    {X Z : Base A} (f : X ⟶ Z) :
    OccurrenceAt R (A := A) index X.unop.context →
      OccurrenceAt R (A := A) index Z.unop.context :=
  fun occurrence =>
    let σ := fromPositions X.unop.context f.unop
    ⟨substValuation A σ occurrence.valuation,
      fun sort bound =>
        A.substitution.substitute σ (occurrence.close sort bound)⟩

/-- Reindexing by the identity context map fixes an authored occurrence. -/
theorem reindexOccurrence_id (index : Fin R.length)
    (X : Base A) (occurrence : OccurrenceAt R (A := A) index X.unop.context) :
    reindexOccurrence R index (𝟙 X) occurrence = occurrence := by
  have environmentIdentity :
      fromPositions X.unop.context (𝟙 X).unop =
        (fun _ v => A.substitution.injectVar v) := by
    funext sort v
    exact fromPositions_ofEnvironment
      (fun _ v => A.substitution.injectVar v) v
  cases occurrence with
  | mk valuation close =>
      change (⟨substValuation A _ valuation,
        fun sort bound => A.substitution.substitute _ (close sort bound)⟩ :
          OccurrenceAt R (A := A) index X.unop.context) =
        ⟨valuation, close⟩
      rw [environmentIdentity]
      have valuationIdentity :
          substValuation A (fun _ v => A.substitution.injectVar v)
            valuation = valuation := by
        funext k
        change A.substitution.substitute
          (A.substitution.liftEnvironment
            (fun _ v => A.substitution.injectVar v) (M.get k).1)
            (valuation k) = valuation k
        rw [liftEnvironment_injectVar A.substitution (M.get k).1]
        exact A.substitution.substitute_identity (valuation k)
      have closeIdentity :
          (fun sort bound => A.substitution.substitute
            (fun _ v => A.substitution.injectVar v) (close sort bound)) =
          close := by
        funext sort bound
        exact A.substitution.substitute_identity (close sort bound)
      rw [valuationIdentity, closeIdentity]

/-- Reindexing respects composition of contextual substitutions. -/
theorem reindexOccurrence_comp (index : Fin R.length)
    {X V Z : Base A} (f : X ⟶ V) (g : V ⟶ Z)
    (occurrence : OccurrenceAt R (A := A) index X.unop.context) :
    reindexOccurrence R index (f ≫ g) occurrence =
      reindexOccurrence R index g (reindexOccurrence R index f occurrence) := by
  let σ : Environment S A.substitution.Carrier
      X.unop.context V.unop.context :=
    fromPositions X.unop.context f.unop
  let τ : Environment S A.substitution.Carrier
      V.unop.context Z.unop.context :=
    fromPositions V.unop.context g.unop
  have composite :
      fromPositions X.unop.context (f ≫ g).unop =
        (fun sort v => A.substitution.substitute τ (σ sort v)) := by
    funext sort v
    exact fromPositions_substitute A.substitution f.unop τ v
  cases occurrence with
  | mk valuation close =>
      change (⟨substValuation A _ valuation,
        fun sort bound => A.substitution.substitute _ (close sort bound)⟩ :
          OccurrenceAt R (A := A) index Z.unop.context) =
        ⟨substValuation A τ (substValuation A σ valuation),
          fun sort bound => A.substitution.substitute τ
            (A.substitution.substitute σ (close sort bound))⟩
      rw [composite]
      have valuationComp :
          substValuation A
            (fun sort v => A.substitution.substitute τ (σ sort v)) valuation =
          substValuation A τ (substValuation A σ valuation) := by
        funext k
        change A.substitution.substitute
          (A.substitution.liftEnvironment
            (fun sort v => A.substitution.substitute τ (σ sort v))
              (M.get k).1) (valuation k) =
          A.substitution.substitute (A.substitution.liftEnvironment τ (M.get k).1)
            (A.substitution.substitute
              (A.substitution.liftEnvironment σ (M.get k).1) (valuation k))
        rw [A.substitution.substitute_comp]
        congr 1
        funext sort v
        exact (substitute_liftEnvironment A.substitution τ σ
          (M.get k).1 v).symm
      have closeComp :
          (fun sort bound => A.substitution.substitute
            (fun s v => A.substitution.substitute τ (σ s v))
            (close sort bound)) =
          (fun sort bound => A.substitution.substitute τ
            (A.substitution.substitute σ (close sort bound))) := by
        funext sort bound
        exact (A.substitution.substitute_comp σ τ (close sort bound)).symm
      rw [valuationComp, closeComp]

/-- The actual selected rule occurrences form a presheaf on the binding
clone's context and substitution category. -/
def occurrencePresheaf (index : Fin R.length) : Base A ⥤ Type u where
  obj X := OccurrenceAt R (A := A) index X.unop.context
  map f := TypeCat.ofHom (reindexOccurrence R index f)
  map_id X := by
    apply ConcreteCategory.hom_ext
    intro occurrence
    exact reindexOccurrence_id R index X occurrence
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro occurrence
    exact reindexOccurrence_comp R index f g occurrence

/-- The presheaf action is exactly the substitution already proved for
intrinsic constructor occurrences. -/
theorem toInstance_reindex (index : Fin R.length)
    {X Z : Base A} (f : X ⟶ Z)
    (occurrence : OccurrenceAt R (A := A) index X.unop.context) :
    OccurrenceAt.toInstance R index (reindexOccurrence R index f occurrence) =
      Instance.subst R (OccurrenceAt.toInstance R index occurrence)
        (fromPositions X.unop.context f.unop) := by
  rfl

/-- Every premise judgment of a reindexed rule occurrence is the original
premise judgment substituted under that premise's own ordered binders. -/
theorem childJudgment_reindex (index : Fin R.length)
    (position : Fin (R.get index).premises.length)
    {X Z : Base A} (f : X ⟶ Z)
    (occurrence : OccurrenceAt R (A := A) index X.unop.context) :
    childJudgment R A
        (OccurrenceAt.toInstance R index
          (reindexOccurrence R index f occurrence)) position =
      substJudgment
        (childJudgment R A
          (OccurrenceAt.toInstance R index occurrence) position)
        (A.substitution.liftEnvironment
          (fromPositions X.unop.context f.unop)
          ((R.get index).premises.get position).binders) := by
  change childJudgment R A
      (Instance.subst R (OccurrenceAt.toInstance R index occurrence)
        (fromPositions X.unop.context f.unop)) position = _
  exact childJudgment_subst R
    (OccurrenceAt.toInstance R index occurrence)
    (fromPositions X.unop.context f.unop) position

/-- The requested source and target of one actual premise are values at
its binder-extended context, with their endpoint sort retained. -/
def childEndpointsAt (index : Fin R.length)
    (position : Fin (R.get index).premises.length)
    {Γ : Ctx S} (occurrence : OccurrenceAt R (A := A) index Γ) :
    (FunctorToTypes.prod (states A) (states A)).obj
      (Opposite.op (ContextObject.ofList A.substitution.toClone
        (((R.get index).premises.get position).binders ++ Γ))) :=
  let judgment := childJudgment R A
    (OccurrenceAt.toInstance R index occurrence) position
  (⟨judgment.2.1, judgment.2.2.1⟩,
    ⟨judgment.2.1, judgment.2.2.2⟩)

private def endpointPairOfJudgment (j :
    Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial.Judgment A) :
    Σ Γ : Ctx S,
      (Σ sort : S.Srt, A.substitution.Carrier Γ sort) ×
        (Σ sort : S.Srt, A.substitution.Carrier Γ sort) :=
  ⟨j.1, (⟨j.2.1, j.2.2.1⟩, ⟨j.2.1, j.2.2.2⟩)⟩

/-- The context arrow read as a typed environment reconstructs that arrow
exactly. This is the link between clone substitutions and scoped binders. -/
theorem environmentArrow_fromPositions {X Z : Base A} (f : X ⟶ Z) :
    environmentArrow A (fromPositions X.unop.context f.unop) = f.unop := by
  funext i
  exact fromPositions_varOfIdx X.unop.context f.unop i

/-- Substituting a rule instance transports the requested source and target
beneath the premise's binders. -/
theorem childEndpointsAt_reindex (index : Fin R.length)
    (position : Fin (R.get index).premises.length)
    {X Z : Base A} (f : X ⟶ Z)
    (occurrence : OccurrenceAt R (A := A) index X.unop.context) :
    childEndpointsAt R index position
        (reindexOccurrence R index f occurrence) =
      (scopedEvidence A ((R.get index).premises.get position).binders
        (FunctorToTypes.prod (states A) (states A))).map f
          (childEndpointsAt R index position occurrence) := by
  let scope := ((R.get index).premises.get position).binders
  let σ := fromPositions X.unop.context f.unop
  have environment :
      fromPositions (S := S) (F := A.substitution.Carrier)
          (scope ++ X.unop.context)
          (extendScope A scope f.unop) =
        A.substitution.liftEnvironment σ scope := by
    exact fromPositions_extendScope A scope f.unop
  have substituteExtended {sort : S.Srt}
      (term : A.substitution.Carrier (scope ++ X.unop.context) sort) :
      A.substitution.toClone.substitute term
          (extendScope A scope f.unop) =
        A.substitution.substitute
          (A.substitution.liftEnvironment σ scope) term := by
    change A.substitution.substitute
      (fromPositions (S := S) (F := A.substitution.Carrier)
        (scope ++ X.unop.context) (extendScope A scope f.unop)) term = _
    rw [environment]
    rfl
  have hJudgment := childJudgment_reindex R index position f occurrence
  have hPair := congrArg (endpointPairOfJudgment (A := A)) hJudgment
  have hPairValue := eq_of_heq (Sigma.mk.inj_iff.mp hPair).2
  refine hPairValue.trans ?_
  let oldJ := childJudgment R A
    (OccurrenceAt.toInstance R index occurrence) position
  change
    (Sigma.mk oldJ.2.1 (A.substitution.substitute
        (A.substitution.liftEnvironment σ scope) oldJ.2.2.1),
      Sigma.mk oldJ.2.1 (A.substitution.substitute
        (A.substitution.liftEnvironment σ scope) oldJ.2.2.2)) =
      (Sigma.mk oldJ.2.1 (A.substitution.toClone.substitute oldJ.2.2.1
        (extendScope A scope f.unop)),
        Sigma.mk oldJ.2.1 (A.substitution.toClone.substitute oldJ.2.2.2
          (extendScope A scope f.unop)))
  exact Prod.ext
    (congrArg (Sigma.mk oldJ.2.1)
      (substituteExtended oldJ.2.2.1).symm)
    (congrArg (Sigma.mk oldJ.2.1)
      (substituteExtended oldJ.2.2.2).symm)

/-- The authored premise's requested endpoint pair is natural in ambient
substitution, including the lift beneath its own binder list. -/
def childEndpointsNat (index : Fin R.length)
    (position : Fin (R.get index).premises.length) :
    occurrencePresheaf R (A := A) index ⟶
      scopedEvidence A ((R.get index).premises.get position).binders
        (FunctorToTypes.prod (states A) (states A)) where
  app X := TypeCat.ofHom (childEndpointsAt R index position)
  naturality X Z f := by
    apply ConcreteCategory.hom_ext
    intro occurrence
    exact childEndpointsAt_reindex R index position f occurrence

/-- The declared conclusion source and target of a selected rule instance. -/
def conclusionEndpointsAt (index : Fin R.length)
    {Γ : Ctx S} (occurrence : OccurrenceAt R (A := A) index Γ) :
    (FunctorToTypes.prod (states A) (states A)).obj
      (Opposite.op (ContextObject.ofList A.substitution.toClone Γ)) :=
  let judgment := conclusionJudgment R A
    (OccurrenceAt.toInstance R index occurrence)
  (⟨judgment.2.1, judgment.2.2.1⟩,
    ⟨judgment.2.1, judgment.2.2.2⟩)

/-- The authored conclusion endpoints commute with every ambient
substitution, using the existing rule-instance substitution law. -/
theorem conclusionEndpointsAt_reindex (index : Fin R.length)
    {X Z : Base A} (f : X ⟶ Z)
    (occurrence : OccurrenceAt R (A := A) index X.unop.context) :
    conclusionEndpointsAt R index
        (reindexOccurrence R index f occurrence) =
      (FunctorToTypes.prod (states A) (states A)).map f
        (conclusionEndpointsAt R index occurrence) := by
  have hJudgment := conclusionJudgment_subst R
    (OccurrenceAt.toInstance R index occurrence)
    (fromPositions X.unop.context f.unop)
  have hPair := congrArg (endpointPairOfJudgment (A := A)) hJudgment
  have hPairValue := eq_of_heq (Sigma.mk.inj_iff.mp hPair).2
  refine hPairValue.trans ?_
  let oldJ := conclusionJudgment R A
    (OccurrenceAt.toInstance R index occurrence)
  change
    (Sigma.mk oldJ.2.1
        (A.substitution.substitute
          (fromPositions X.unop.context f.unop) oldJ.2.2.1),
      Sigma.mk oldJ.2.1
        (A.substitution.substitute
          (fromPositions X.unop.context f.unop) oldJ.2.2.2)) =
      (Sigma.mk oldJ.2.1
        (A.substitution.toClone.substitute oldJ.2.2.1 f.unop),
      Sigma.mk oldJ.2.1
        (A.substitution.toClone.substitute oldJ.2.2.2 f.unop))
  rfl

/-- The authored conclusion map is natural on the selected rule-occurrence
presheaf; an operational action must produce an event above this map. -/
def conclusionEndpointsNat (index : Fin R.length) :
    occurrencePresheaf R (A := A) index ⟶
      FunctorToTypes.prod (states A) (states A) where
  app X := TypeCat.ofHom (conclusionEndpointsAt R index)
  naturality X Z f := by
    apply ConcreteCategory.hom_ext
    intro occurrence
    exact conclusionEndpointsAt_reindex R index f occurrence

end Mettapedia.OSLF.Binding.IntrinsicRuleOccurrencePresheaf

#print axioms Mettapedia.OSLF.Binding.IntrinsicRuleOccurrencePresheaf.occurrencePresheaf
#print axioms Mettapedia.OSLF.Binding.IntrinsicRuleOccurrencePresheaf.childJudgment_reindex
#print axioms Mettapedia.OSLF.Binding.IntrinsicRuleOccurrencePresheaf.childEndpointsNat
#print axioms Mettapedia.OSLF.Binding.IntrinsicRuleOccurrencePresheaf.conclusionEndpointsNat
