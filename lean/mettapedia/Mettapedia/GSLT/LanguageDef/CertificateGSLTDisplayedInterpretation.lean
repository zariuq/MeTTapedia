import Mettapedia.GSLT.LanguageDef.CertificateGSLTDisplayedDerivations
import Mettapedia.GSLT.LanguageDef.CertificateGSLTClassifyingInterpretation
import Mettapedia.TypeTheory.ModeIndexedFamilyTermsAndComprehension

/-!
# Theory translation of displayed open derivations

An interpretation replaces each source rule application by a target open
derivation. The resulting map on proof-bearing presheaves is natural under
contextual proof substitution. It keeps the goal and the translated proof,
not merely the proposition that some target proof exists.

This is a translation of the common-judgment, ordered-premise fragment. It
does not assert preservation of implication or arbitrary internal types.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open _root_.CategoryTheory
open scoped CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.DisplayedPresheafComprehension
open Mettapedia.TypeTheory.ModeIndexedFamilyTermsAndComprehension

/-- A common-judgment interpretation acts on contextual goal points: it
changes the proof-context category but leaves the goal label untouched. -/
def Interpretation.goalElementsFunctor {source target : Object}
    (interpretation : Interpretation source target) :
    (goalFace source.definition).Elements ⥤
      (goalFace target.definition).Elements where
  obj value :=
    ⟨interpretation.contextFunctor.op.obj value.1, value.2⟩
  map substitution :=
    CategoryOfElements.homMk _ _
      (interpretation.contextFunctor.op.map substitution.val)
      substitution.property
  map_id value := by
    apply CategoryOfElements.ext
    exact interpretation.contextFunctor.op.map_id value.1
  map_comp first second := by
    apply CategoryOfElements.ext
    exact interpretation.contextFunctor.op.map_comp first.val second.val

/-- Theory translation acts on the proof-relevant family over contextual
goals, not just on its total presheaf. The map is natural in both the goal
point and its proof-valued context substitution. -/
def Interpretation.derivationFamilyMap {source target : Object}
    (interpretation : Interpretation source target) :
    derivationFamily source.definition ⟶
      interpretation.goalElementsFunctor ⋙ derivationFamily target.definition where
  app _ := TypeCat.ofHom interpretation.mapOpen
  naturality := by
    intro first second substitution
    apply ConcreteCategory.hom_ext
    intro derivation
    have sameGoal : first.2 = second.2 := substitution.property
    cases first with
    | mk firstContext firstGoal =>
      cases second with
      | mk secondContext secondGoal =>
        dsimp at sameGoal
        subst secondGoal
        exact interpretation.mapOpen_bind derivation substitution.val.unop

/-- The translation of a displayed proof-bearing point through the
Grothendieck comprehensions of the two derivation families. -/
def Interpretation.derivationComprehensionFunctor {source target : Object}
    (interpretation : Interpretation source target) :
    (derivationFamily source.definition).Elements ⥤
      (derivationFamily target.definition).Elements :=
  elementsAction interpretation.derivationFamilyMap ⋙
    Functor.Elements.precomp interpretation.goalElementsFunctor
      (derivationFamily target.definition)

/-- A translated proof-bearing context projects to the translated goal
context. In particular, translation does not silently change the goal. -/
theorem Interpretation.derivationComprehension_projection
    {source target : Object}
    (interpretation : Interpretation source target) :
    interpretation.derivationComprehensionFunctor ⋙
        CategoryOfElements.π (derivationFamily target.definition) =
      CategoryOfElements.π (derivationFamily source.definition) ⋙
        interpretation.goalElementsFunctor := by
  rfl

/-- The canonical dependent last-variable term is transported as the
actual translated proof. This does not construct an authored Prime term. -/
theorem Interpretation.derivationLastVariable_transport
    {source target : Object}
    (interpretation : Interpretation source target)
    (point : (derivationFamily source.definition).Elements) :
    (lastVariable (derivationFamily target.definition)).1
        (interpretation.derivationComprehensionFunctor.obj point) =
      interpretation.mapOpen
        ((lastVariable (derivationFamily source.definition)).1 point) :=
  rfl

/-- Every common-judgment interpretation retains the distinction between
two ordered occurrences of the same assumption. This is deliberately narrower
than faithfulness on arbitrary rule derivations: rule templates can identify
different source rule nodes. -/
theorem Interpretation.duplicateAssumptionsTranslatedDistinct
    {source target : Object}
    (interpretation : Interpretation source target) (goal : Pattern) :
    interpretation.mapOpen
        (OpenDerivation.assumption (definition := source.definition)
          (context := [goal, goal]) (0 : Fin 2)) ≠
      interpretation.mapOpen
        (OpenDerivation.assumption (definition := source.definition)
          (context := [goal, goal]) (1 : Fin 2)) := by
  simpa only [Interpretation.mapOpen] using
    (ClassifyingContext.duplicate_assumptions_distinct target.definition goal)

/-- The induced comprehension functor also keeps the two proof-bearing
points distinct, even though their goal observations coincide. -/
theorem Interpretation.duplicateAssumptionsComprehensionDistinct
    {source target : Object}
    (interpretation : Interpretation source target) (goal : Pattern) :
    interpretation.derivationComprehensionFunctor.obj
        (derivationPoint source.definition ⟨[goal, goal]⟩ goal
          (.assumption (definition := source.definition)
            (context := [goal, goal]) (0 : Fin 2))) ≠
      interpretation.derivationComprehensionFunctor.obj
        (derivationPoint source.definition ⟨[goal, goal]⟩ goal
          (.assumption (definition := source.definition)
            (context := [goal, goal]) (1 : Fin 2))) := by
  intro same
  change point (derivationFamily target.definition)
      ⟨Opposite.op (⟨[goal, goal]⟩ : ClassifyingContext target.definition), goal⟩
      (interpretation.mapOpen
        (OpenDerivation.assumption (definition := source.definition)
          (context := [goal, goal]) (0 : Fin 2))) =
    point (derivationFamily target.definition)
      ⟨Opposite.op (⟨[goal, goal]⟩ : ClassifyingContext target.definition), goal⟩
      (interpretation.mapOpen
        (OpenDerivation.assumption (definition := source.definition)
          (context := [goal, goal]) (1 : Fin 2))) at same
  exact interpretation.duplicateAssumptionsTranslatedDistinct goal
    (point_injective (derivationFamily target.definition)
      ⟨Opposite.op (⟨[goal, goal]⟩ : ClassifyingContext target.definition), goal⟩ same)

/-- The identity interpretation is identity on displayed proof-bearing
contexts, including their retained derivations. -/
theorem Interpretation.id_derivationComprehension_obj
    (object : Object)
    (context : (derivationFamily object.definition).Elements) :
    (Interpretation.id object).derivationComprehensionFunctor.obj context =
      context := by
  cases context with
  | mk base derivation =>
      cases base with
      | mk context goal =>
          cases context with
          | op context =>
              cases context with
              | mk judgments =>
                  change (⟨⟨Opposite.op ⟨judgments⟩, goal⟩,
                    (Interpretation.id object).mapOpen derivation⟩ :
                    (derivationFamily object.definition).Elements) =
                    ⟨⟨Opposite.op ⟨judgments⟩, goal⟩, derivation⟩
                  exact congrArg
                    (fun proof : OpenDerivation object.definition judgments goal =>
                      point (derivationFamily object.definition)
                        (⟨Opposite.op ⟨judgments⟩, goal⟩ :
                          (goalFace object.definition).Elements) proof)
                    (Interpretation.id_mapOpen derivation)

/-- Successive theory interpretations compose on the displayed object,
including its actual translated derivation, not only on the goal. -/
theorem Interpretation.comp_derivationComprehension_obj
    {first middle last : Object}
    (earlier : Interpretation first middle)
    (later : Interpretation middle last)
    (context : (derivationFamily first.definition).Elements) :
    (Interpretation.comp earlier later).derivationComprehensionFunctor.obj context =
      later.derivationComprehensionFunctor.obj
        (earlier.derivationComprehensionFunctor.obj context) := by
  cases context with
  | mk base derivation =>
      cases base with
      | mk context goal =>
          cases context with
          | op context =>
              cases context with
              | mk judgments =>
                  change (⟨⟨Opposite.op ⟨judgments⟩, goal⟩,
                    (Interpretation.comp earlier later).mapOpen derivation⟩ :
                      (derivationFamily last.definition).Elements) =
                    ⟨⟨Opposite.op ⟨judgments⟩, goal⟩,
                      later.mapOpen (earlier.mapOpen derivation)⟩
                  exact congrArg
                    (fun proof : OpenDerivation last.definition judgments goal =>
                      point (derivationFamily last.definition)
                        (⟨Opposite.op ⟨judgments⟩, goal⟩ :
                          (goalFace last.definition).Elements) proof)
                    (Interpretation.comp_mapOpen earlier later derivation)

/-- Translate the actual proof in a contextual answer. Its naturality square
is the interpretation/substitution interchange law. -/
def Interpretation.derivationTotalMap {source target : Object}
    (interpretation : Interpretation source target) :
    derivationTotalFace source.definition ⟶
      interpretation.contextFunctor.op ⋙ derivationTotalFace target.definition where
  app _ := TypeCat.ofHom fun answer =>
    ⟨answer.1, interpretation.mapOpen answer.2⟩
  naturality := by
    intro first second substitution
    apply ConcreteCategory.hom_ext
    rintro ⟨goal, derivation⟩
    exact congrArg (Sigma.mk goal)
      (interpretation.mapOpen_bind derivation substitution.unop)

/-- Common-judgment theory interpretations do not rename goals. The
identity-on-goals comparison is natural because both goal presheaves are
constant on contextual substitutions. -/
def Interpretation.goalFaceMap {source target : Object}
    (interpretation : Interpretation source target) :
    goalFace source.definition ⟶
      interpretation.contextFunctor.op ⋙ goalFace target.definition where
  app _ := 𝟙 _
  naturality := by
    intros
    rfl

/-- Theory translation commutes with forgetting proof routes to goals as an
equality of natural transformations, not just at a chosen context. -/
theorem Interpretation.derivationTotalMap_projection {source target : Object}
    (interpretation : Interpretation source target) :
    interpretation.derivationTotalMap ≫
        Functor.whiskerLeft interpretation.contextFunctor.op
          (derivationToGoal target.definition) =
      derivationToGoal source.definition ≫ interpretation.goalFaceMap := by
  ext context answer
  rfl

/-- The translated total answer still projects to exactly its source goal. -/
@[simp] theorem Interpretation.derivationTotalMap_goal
    {source target : Object}
    (interpretation : Interpretation source target)
    (context : (ClassifyingContext source.definition)ᵒᵖ)
    (answer : (derivationTotalFace source.definition).obj context) :
    (derivationToGoal target.definition).app
        (Opposite.op (interpretation.contextFunctor.obj context.unop))
        ((interpretation.derivationTotalMap).app context answer) =
      (derivationToGoal source.definition).app context answer := rfl

/-- At a fixed goal the theory translation maps retained derivations,
rather than collapsing the fibre to an inhabitation claim. -/
def Interpretation.mapDerivationFibre {source target : Object}
    (interpretation : Interpretation source target)
    (context : ClassifyingContext source.definition) (goal : Pattern)
    (receipt : { answer : (derivationTotalFace source.definition).obj
        (Opposite.op context) //
        (derivationToGoal source.definition).app
          (Opposite.op context) answer = goal }) :
    { answer : (derivationTotalFace target.definition).obj
        (Opposite.op (interpretation.contextFunctor.obj context)) //
        (derivationToGoal target.definition).app
          (Opposite.op (interpretation.contextFunctor.obj context)) answer = goal } :=
  ⟨⟨receipt.val.1, interpretation.mapOpen receipt.val.2⟩, receipt.property⟩

/-- Translating proof evidence commutes with reindexing by an arbitrary
ordered, proof-valued context substitution. -/
theorem Interpretation.mapDerivationFibre_reindex {source target : Object}
    (interpretation : Interpretation source target)
    {first second : ClassifyingContext source.definition}
    (substitution : second ⟶ first) (goal : Pattern)
    (receipt : { answer : (derivationTotalFace source.definition).obj
        (Opposite.op first) //
        (derivationToGoal source.definition).app
          (Opposite.op first) answer = goal }) :
    interpretation.mapDerivationFibre second goal
        (reindexDerivationFibre source.definition substitution goal receipt) =
      reindexDerivationFibre target.definition
        (interpretation.contextFunctor.map substitution) goal
        (interpretation.mapDerivationFibre first goal receipt) := by
  obtain ⟨⟨otherGoal, derivation⟩, equal⟩ := receipt
  cases equal
  apply Subtype.ext
  exact congrArg (Sigma.mk otherGoal)
    (interpretation.mapOpen_bind derivation substitution)

/-- The identity rule interpretation leaves every retained receipt intact. -/
@[simp] theorem Interpretation.id_mapDerivationFibre
    (object : Object) (context : ClassifyingContext object.definition)
    (goal : Pattern)
    (receipt : { answer : (derivationTotalFace object.definition).obj
        (Opposite.op context) //
        (derivationToGoal object.definition).app
          (Opposite.op context) answer = goal }) :
    (Interpretation.id object).mapDerivationFibre context goal receipt =
      receipt := by
  obtain ⟨⟨otherGoal, derivation⟩, equal⟩ := receipt
  cases equal
  apply Subtype.ext
  exact congrArg (Sigma.mk otherGoal)
    (Interpretation.id_mapOpen derivation)

/-- Composed theory interpretations act by composing their translations
on actual proof-bearing fibres. -/
theorem Interpretation.comp_mapDerivationFibre
    {first middle last : Object}
    (earlier : Interpretation first middle)
    (later : Interpretation middle last)
    (context : ClassifyingContext first.definition) (goal : Pattern)
    (receipt : { answer : (derivationTotalFace first.definition).obj
        (Opposite.op context) //
        (derivationToGoal first.definition).app
          (Opposite.op context) answer = goal }) :
    (Interpretation.comp earlier later).mapDerivationFibre context goal receipt =
      later.mapDerivationFibre
        (earlier.contextFunctor.obj context) goal
        (earlier.mapDerivationFibre context goal receipt) := by
  obtain ⟨⟨otherGoal, derivation⟩, equal⟩ := receipt
  cases equal
  apply Subtype.ext
  exact congrArg (Sigma.mk otherGoal)
    (Interpretation.comp_mapOpen earlier later derivation)

#print axioms Interpretation.derivationTotalMap
#print axioms Interpretation.derivationTotalMap_projection
#print axioms Interpretation.derivationFamilyMap
#print axioms Interpretation.derivationComprehensionFunctor
#print axioms Interpretation.derivationLastVariable_transport
#print axioms Interpretation.duplicateAssumptionsTranslatedDistinct
#print axioms Interpretation.duplicateAssumptionsComprehensionDistinct
#print axioms Interpretation.id_derivationComprehension_obj
#print axioms Interpretation.comp_derivationComprehension_obj
#print axioms Interpretation.mapDerivationFibre_reindex
#print axioms Interpretation.comp_mapDerivationFibre

end Mettapedia.GSLT.LanguageDef.CertificateGSLT
