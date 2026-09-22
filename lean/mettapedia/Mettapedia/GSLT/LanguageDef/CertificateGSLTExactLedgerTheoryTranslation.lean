import Mettapedia.GSLT.LanguageDef.CertificateGSLTLedgerDependentFamily
import Mettapedia.GSLT.LanguageDef.CertificateGSLTOccurrencePreservingInterpretation
import Mettapedia.GSLT.LanguageDef.CertificateGSLTClassifyingInterpretation
import Mettapedia.GSLT.LanguageDef.CertificateGSLTDisplayedInterpretation
import Mettapedia.TypeTheory.ModeIndexedFamilyTermsAndComprehension

/-!
# Exact-ledger dependent evidence under theory interpretation

A derivation-valued interpretation always translates an authored open proof,
but it need not preserve how many times or in what order its premises were
used. The existing ordered-linearity condition is exactly what licenses
translation of the goal-and-ledger-indexed proof family without changing its
ledger index. No preservation of presheaf implication or arbitrary dependent
types is inferred.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT

open _root_.CategoryTheory
open scoped CategoryTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.TypeTheory.DisplayedPresheafTransport
open Mettapedia.TypeTheory.ModeIndexedFamilyTermsAndComprehension
open OpenSearchMachine

namespace Interpretation

universe u v w

/-- An arrow of an element category carries no independent proof choice once
its endpoints and underlying contextual arrow have been fixed. -/
private theorem elementsHom_heq_of_val_heq
    {Context : Type u} [Category.{v} Context]
    {family : Context ⥤ Type w}
    {first second first' second' : family.Elements}
    (firstEq : first = first') (secondEq : second = second')
    (arrow : first ⟶ second) (arrow' : first' ⟶ second')
    (underlyingEq : arrow.val ≍ arrow'.val) : arrow ≍ arrow' := by
  cases firstEq
  cases secondEq
  exact heq_of_eq (CategoryOfElements.ext family arrow arrow' (eq_of_heq underlyingEq))

/-- A locally ordered-linear rule interpretation commutes with reindexing
an exact occurrence ledger along an authored proof-vector substitution. -/
theorem mapLedger_mapOpenList
    {source target : Object}
    (interpretation : Interpretation source target)
    (linear : interpretation.PreservesOrderedPremises)
    {sourceContext targetContext : List Pattern}
    (environment : OpenDerivationList source.definition targetContext sourceContext)
    (ledger : List (Fin sourceContext.length)) :
    mapLedger (interpretation.mapOpenList environment) ledger =
      mapLedger environment ledger := by
  unfold mapLedger
  congr 1
  funext position
  rw [interpretation.mapOpenList_get]
  exact interpretation.holeOccurrences_mapOpen linear (environment.get position)

/-- Ordered-linear theory change maps the exact goal-and-ledger observation
as a natural family over contextual proof substitutions. -/
def goalLedgerFaceMap
    {source target : Object}
    (interpretation : Interpretation source target)
    (linear : interpretation.PreservesOrderedPremises) :
    goalLedgerFace source.definition ⟶
      interpretation.contextFunctor.op ⋙ goalLedgerFace target.definition where
  app _ := TypeCat.ofHom fun answer => answer
  naturality := by
    intro first second substitution
    apply ConcreteCategory.hom_ext
    rintro ⟨goal, ledger⟩
    exact congrArg (fun uses => (goal, uses))
      (mapLedger_mapOpenList interpretation linear substitution.unop ledger).symm

/-- Theory change and observation of the exact occurrence ledger commute
on the original proof presheaf. This is the underlying observation square
for the proof-relevant dependent-family map below. -/
theorem derivationTotalMap_goalLedger_square
    {source target : Object}
    (interpretation : Interpretation source target)
    (linear : interpretation.PreservesOrderedPremises) :
    interpretation.derivationTotalMap ≫
        Functor.whiskerLeft interpretation.contextFunctor.op
          (derivationToGoalLedger target.definition) =
      derivationToGoalLedger source.definition ≫
        interpretation.goalLedgerFaceMap linear := by
  ext context answer
  exact congrArg (fun uses => (answer.1, uses))
    (interpretation.holeOccurrences_mapOpen linear answer.2)

/-- Under the same resource certificate, a source goal-and-ledger point
translates to a target point with its ledger unchanged. -/
def goalLedgerElementsFunctor
    {source target : Object}
    (interpretation : Interpretation source target)
    (linear : interpretation.PreservesOrderedPremises) :
    (goalLedgerFace source.definition).Elements ⥤
      (goalLedgerFace target.definition).Elements where
  obj point := ⟨interpretation.contextFunctor.op.obj point.1, point.2⟩
  map {first second} arrow := CategoryOfElements.homMk _ _
    (interpretation.contextFunctor.op.map arrow.val) (by
      have follows := arrow.property
      change
        (first.2.1,
          mapLedger (interpretation.mapOpenList arrow.val.unop) first.2.2) =
          second.2
      change (first.2.1, mapLedger arrow.val.unop first.2.2) =
        second.2 at follows
      rw [mapLedger_mapOpenList interpretation linear arrow.val.unop first.2.2]
      exact follows)
  map_id point := by
    apply CategoryOfElements.ext (goalLedgerFace target.definition)
    exact interpretation.contextFunctor.op.map_id point.1
  map_comp first second := by
    apply CategoryOfElements.ext (goalLedgerFace target.definition)
    exact interpretation.contextFunctor.op.map_comp first.val second.val

/-- The context-level ledger functor is exactly the element-category action
of the natural observation map, including its contextual arrows. -/
theorem goalLedgerElementsFunctor_from_face_map
    {source target : Object}
    (interpretation : Interpretation source target)
    (linear : interpretation.PreservesOrderedPremises) :
    interpretation.goalLedgerElementsFunctor linear =
      elementsAction (interpretation.goalLedgerFaceMap linear) ⋙
        Functor.Elements.precomp interpretation.contextFunctor.op
          (goalLedgerFace target.definition) := by
  refine Functor.hext (fun _ => rfl) ?_
  intro first second arrow
  apply heq_of_eq
  apply CategoryOfElements.ext (goalLedgerFace target.definition)
  rfl

/-- Identity interpretation keeps every exact goal-and-ledger context and
its contextual substitution unchanged. -/
theorem goalLedgerElementsFunctor_id (object : Object) :
    (Interpretation.id object).goalLedgerElementsFunctor
        (id_preservesOrderedPremises object) =
      𝟭 (goalLedgerFace object.definition).Elements := by
  refine Functor.hext (fun _ => rfl) ?_
  intro first second arrow
  apply heq_of_eq
  apply CategoryOfElements.ext (goalLedgerFace object.definition)
  exact congrArg Quiver.Hom.op
    (Interpretation.id_contextFunctor_map object arrow.val.unop)

/-- Successive ordered-linear theory interpretations translate exact
goal-and-ledger contexts in the same order as their composite. -/
theorem goalLedgerElementsFunctor_comp
    {first middle last : Object}
    (earlier : Interpretation first middle)
    (later : Interpretation middle last)
    (earlierLinear : earlier.PreservesOrderedPremises)
    (laterLinear : later.PreservesOrderedPremises) :
    (Interpretation.comp earlier later).goalLedgerElementsFunctor
        (comp_preservesOrderedPremises earlier later earlierLinear laterLinear) =
      earlier.goalLedgerElementsFunctor earlierLinear ⋙
        later.goalLedgerElementsFunctor laterLinear := by
  refine Functor.hext (fun _ => rfl) ?_
  intro source target arrow
  apply heq_of_eq
  apply CategoryOfElements.ext (goalLedgerFace last.definition)
  exact congrArg Quiver.Hom.op
    (Interpretation.comp_contextFunctor_map earlier later arrow.val.unop)

/-- A checked source derivation in an exact goal-and-ledger fibre translates
to a target derivation in the corresponding exact fibre. Naturality says this
commutes with further authored proof substitution. -/
def exactDerivationFamilyMap
    {source target : Object}
    (interpretation : Interpretation source target)
    (linear : interpretation.PreservesOrderedPremises) :
    exactDerivationDisplayedFamily source.definition ⟶
      interpretation.goalLedgerElementsFunctor linear ⋙
        exactDerivationDisplayedFamily target.definition where
  app index := TypeCat.ofHom fun receipt =>
    ⟨⟨receipt.val.1, interpretation.mapOpen receipt.val.2⟩, by
      have observed := receipt.property
      change
        (receipt.val.1,
          holeOccurrences (interpretation.mapOpen receipt.val.2)) = index.2
      rw [interpretation.holeOccurrences_mapOpen linear]
      exact observed⟩
  naturality := by
    intro first second arrow
    apply ConcreteCategory.hom_ext
    intro receipt
    apply Subtype.ext
    exact congrArg (Sigma.mk receipt.val.1)
      (interpretation.mapOpen_bind receipt.val.2 arrow.val.unop)

/-- An ordered-linear theory translation acts on the actual category of
exact proof-bearing dependent contexts, keeping each translated derivation. -/
def exactDerivationComprehensionFunctor
    {source target : Object}
    (interpretation : Interpretation source target)
    (linear : interpretation.PreservesOrderedPremises) :
    (exactDerivationDisplayedFamily source.definition).Elements ⥤
      (exactDerivationDisplayedFamily target.definition).Elements :=
  elementsAction (interpretation.exactDerivationFamilyMap linear) ⋙
    Functor.Elements.precomp
      (interpretation.goalLedgerElementsFunctor linear)
      (exactDerivationDisplayedFamily target.definition)

/-- Theory translation of the extended proof context projects to theory
translation of its exact goal-and-ledger base. -/
theorem exactDerivationComprehension_projection
    {source target : Object}
    (interpretation : Interpretation source target)
    (linear : interpretation.PreservesOrderedPremises) :
    interpretation.exactDerivationComprehensionFunctor linear ⋙
        CategoryOfElements.π (exactDerivationDisplayedFamily target.definition) =
      CategoryOfElements.π (exactDerivationDisplayedFamily source.definition) ⋙
        interpretation.goalLedgerElementsFunctor linear := by
  rfl

/-- The dependent last variable after interpretation is exactly the
translated retained proof, not a fresh proof selected from modal support. -/
theorem exactDerivationLastVariable_transport
    {source target : Object}
    (interpretation : Interpretation source target)
    (linear : interpretation.PreservesOrderedPremises)
    (point : (exactDerivationDisplayedFamily source.definition).Elements) :
    ((lastVariable (exactDerivationDisplayedFamily target.definition)).1
      ((interpretation.exactDerivationComprehensionFunctor linear).obj point)).val =
        ⟨point.2.val.1, interpretation.mapOpen point.2.val.2⟩ := by
  rfl

/-- Identity interpretation keeps each actual proof-bearing indexed context
point, including its retained derivation. -/
theorem exactDerivationComprehensionFunctor_id_obj (object : Object)
    (point : (exactDerivationDisplayedFamily object.definition).Elements) :
    ((Interpretation.id object).exactDerivationComprehensionFunctor
      (id_preservesOrderedPremises object)).obj point = point := by
  rcases point with ⟨index, receipt⟩
  change
    (⟨index, ⟨⟨receipt.val.1,
      (Interpretation.id object).mapOpen receipt.val.2⟩, _⟩⟩ :
      (exactDerivationDisplayedFamily object.definition).Elements) =
      ⟨index, receipt⟩
  congr 1
  apply Subtype.ext
  exact congrArg (Sigma.mk receipt.val.1)
    (Interpretation.id_mapOpen receipt.val.2)

/-- Identity theory interpretation preserves arrows of the proof-bearing
dependent context as well as its retained proof objects. -/
theorem exactDerivationComprehensionFunctor_id (object : Object) :
    (Interpretation.id object).exactDerivationComprehensionFunctor
        (id_preservesOrderedPremises object) =
      𝟭 (exactDerivationDisplayedFamily object.definition).Elements := by
  refine Functor.hext (exactDerivationComprehensionFunctor_id_obj object) ?_
  intro first second arrow
  apply elementsHom_heq_of_val_heq
    (exactDerivationComprehensionFunctor_id_obj object first)
    (exactDerivationComprehensionFunctor_id_obj object second)
  apply heq_of_eq
  apply CategoryOfElements.ext (goalLedgerFace object.definition)
  exact congrArg Quiver.Hom.op
    (Interpretation.id_contextFunctor_map object arrow.val.val.unop)

/-- The retained proof in a dependent context translates through two
ordered-linear theory changes exactly as it does through their composite. -/
theorem exactDerivationComprehensionFunctor_comp_obj
    {first middle last : Object}
    (earlier : Interpretation first middle)
    (later : Interpretation middle last)
    (earlierLinear : earlier.PreservesOrderedPremises)
    (laterLinear : later.PreservesOrderedPremises)
    (point : (exactDerivationDisplayedFamily first.definition).Elements) :
    ((Interpretation.comp earlier later).exactDerivationComprehensionFunctor
      (comp_preservesOrderedPremises earlier later earlierLinear laterLinear)).obj point =
      (later.exactDerivationComprehensionFunctor laterLinear).obj
        ((earlier.exactDerivationComprehensionFunctor earlierLinear).obj point) := by
  rcases point with ⟨index, receipt⟩
  change
    (⟨((Interpretation.comp earlier later).goalLedgerElementsFunctor
        (comp_preservesOrderedPremises earlier later earlierLinear laterLinear)).obj index,
      ⟨⟨receipt.val.1,
      (Interpretation.comp earlier later).mapOpen receipt.val.2⟩, _⟩⟩ :
      (exactDerivationDisplayedFamily last.definition).Elements) =
    ⟨(later.goalLedgerElementsFunctor laterLinear).obj
        ((earlier.goalLedgerElementsFunctor earlierLinear).obj index),
      ⟨⟨receipt.val.1,
      later.mapOpen (earlier.mapOpen receipt.val.2)⟩, _⟩⟩
  congr 1
  apply Subtype.ext
  exact congrArg (Sigma.mk receipt.val.1)
    (Interpretation.comp_mapOpen earlier later receipt.val.2)

/-- Successive ordered-linear theory interpretations preserve the full
proof-bearing dependent context functor, including contextual arrows. -/
theorem exactDerivationComprehensionFunctor_comp
    {first middle last : Object}
    (earlier : Interpretation first middle)
    (later : Interpretation middle last)
    (earlierLinear : earlier.PreservesOrderedPremises)
    (laterLinear : later.PreservesOrderedPremises) :
    (Interpretation.comp earlier later).exactDerivationComprehensionFunctor
        (comp_preservesOrderedPremises earlier later earlierLinear laterLinear) =
      earlier.exactDerivationComprehensionFunctor earlierLinear ⋙
        later.exactDerivationComprehensionFunctor laterLinear := by
  refine Functor.hext
    (exactDerivationComprehensionFunctor_comp_obj earlier later earlierLinear laterLinear) ?_
  intro source target arrow
  apply elementsHom_heq_of_val_heq
    (exactDerivationComprehensionFunctor_comp_obj earlier later earlierLinear laterLinear source)
    (exactDerivationComprehensionFunctor_comp_obj earlier later earlierLinear laterLinear target)
  apply heq_of_eq
  apply CategoryOfElements.ext (goalLedgerFace last.definition)
  exact congrArg Quiver.Hom.op
    (Interpretation.comp_contextFunctor_map earlier later arrow.val.val.unop)

#print axioms mapLedger_mapOpenList
#print axioms goalLedgerFaceMap
#print axioms derivationTotalMap_goalLedger_square
#print axioms goalLedgerElementsFunctor
#print axioms goalLedgerElementsFunctor_from_face_map
#print axioms goalLedgerElementsFunctor_id
#print axioms goalLedgerElementsFunctor_comp
#print axioms exactDerivationFamilyMap
#print axioms exactDerivationComprehensionFunctor
#print axioms exactDerivationComprehension_projection
#print axioms exactDerivationLastVariable_transport
#print axioms exactDerivationComprehensionFunctor_id_obj
#print axioms exactDerivationComprehensionFunctor_id
#print axioms exactDerivationComprehensionFunctor_comp_obj
#print axioms exactDerivationComprehensionFunctor_comp

end Interpretation
end Mettapedia.GSLT.LanguageDef.CertificateGSLT
