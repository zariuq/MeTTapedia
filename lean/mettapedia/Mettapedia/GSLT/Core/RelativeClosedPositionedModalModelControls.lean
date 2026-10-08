import Mettapedia.GSLT.Core.RelativeClosedPositionedModalCoherent
import Mettapedia.GSLT.Core.RelativeClosedPositionedModalRelyControls
import Mettapedia.GSLT.Core.RelativeClosedWeakBaseControls

/-!
# A weak closed positioned-modal model and complete admitted cells

The Boolean source is interpreted by independent truth fibres: its false
object is empty and its true object is inhabited. The generated native
interpretation preserves this actual weak base, all original declarations
and their whole complete values. The earned local admission calibrates the
complete comparison and its unique primitive-admitted cells.

The mapped empty-context possibility cannot produce a member from an empty
postcondition. An independently classified constant-truth arrow is rejected
as a supplied declaration value. The richer numeric environment-only tests
are imported separately, without identifying their target hom universe with
this common-hom semantic-model instance.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedPositionedModalModelControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory
open scoped _root_.CategoryTheory.SemilatticeInf
open scoped Mettapedia.CategoryTheory.PredicateDoctrine.HeytingClosed
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory
open ProgramReductionTheory AuthoredClosedTheory RelativeClosedPositionedModalLocalModels
open PositionedRewritePredicatePower ElementaryTypePredicateReadout

abbrev base := RelativeClosedWeakBaseControls.truthFunctor
abbrev closed : LambdaTheory.{0,0} := LambdaTheory.ofCategory Bool

def graph : (true : Bool) ⟶ true ⨯ true := prod.lift (𝟙 true) (𝟙 true)

instance graph_mono : Mono graph := by
  unfold graph
  infer_instance

abbrev source : Theory.{0,0} where
  closed := closed
  program := true
  reduction := Subobject.mk graph

def event : (true : Bool) ≅ source.Event := (Subobject.underlyingIso graph).symm

theorem event_source : event.hom ≫ source.source = 𝟙 (true : Bool) :=
  Subsingleton.elim _ _

theorem event_target : event.hom ≫ source.target = 𝟙 (true : Bool) :=
  Subsingleton.elim _ _

def rule : Rule source where
  parameters := true
  left := 𝟙 true
  right := 𝟙 true
  action := event.hom
  source := event_source
  target := event_target

def position : Position rule where
  environment := true
  carrier := true
  relies := 𝟙 true
  focus := 𝟙 true
  plug := prod.fst
  decomposition := prod.lift_fst _ _

def selection : RelativeClosedPositionedModalPresentation.Selection source where
  rule := rule
  position := position
  assignments := true
  forget := 𝟙 true
  focus := 𝟙 true
  square := by
    change IsPullback (𝟙 (true : Bool)) (prod.lift (𝟙 (true : Bool)) (𝟙 (true : Bool)))
      (𝟙 (true : Bool)) (prod.snd : (true : Bool) ⨯ true ⟶ true)
    exact IsPullback.of_horiz_isIso_mono ⟨Subsingleton.elim _ _⟩

def selected (_origin : Bool) := selection

private instance base_finite : PreservesFiniteLimits (base : source.closed.Obj ⥤ Type) :=
  RelativeClosedWeakBaseControls.truth_lex

private instance base_closed : MonoidalClosedFunctor (base : source.closed.Obj ⥤ Type) :=
  RelativeClosedWeakBaseControls.truth_closed

def model : LocalModel source selected Type :=
  @native source Bool selected Type inferInstance inferInstance inferInstance inferInstance
    base base_finite base_closed doctrine

def interpretation : LambdaTheoryMap (RelativeClosedPositionedModalPresentation.nativeTheory source selected)
    (LambdaTheory.ofCategory Type) := model.closedInterpretation

theorem complete_weak_base :
    (RelativeClosedPositionedModalPresentation.baseMap source selected).functor ⋙ interpretation.functor = base :=
  model.base_readback

theorem complete_original_diagram :
    (RelativeClosedPositionedModalPresentation.nativeInclusion source selected).functor ⋙ interpretation.functor =
      model.diagram := model.original_diagram_readback

theorem false_scope_remains_empty : IsEmpty (interpretation.functor.obj
    (baseObject (RelativeClosedPositionedModalPresentation.nativeSignature source selected) false)) := by
  have same := RelativeClosedSyntax.Interpretation.functor_base_object
    model.nativeModel.meanings model.nativeModel.realization false
  exact same.symm ▸ RelativeClosedWeakBaseControls.false_fibre_empty

theorem nonconstant_base_is_retained : base.obj false ≠ base.obj true :=
  RelativeClosedWeakBaseControls.base_fibres_differ

def completeComparison := RelativeClosedPositionedModalCoherent.comparison model model.nativeDiagram
  (RelativeClosedPositionedModalCoherent.canonicalImages model)
  (RelativeClosedPositionedModalCoherent.canonical_admitted model)

theorem canonical_comparison_is_calibrated : completeComparison = Iso.refl model.nativeDiagram :=
  RelativeClosedPositionedModalCoherent.canonical_comparison_refl model

theorem every_primitive_admitted_complete_cell_agrees (cell : model.nativeDiagram ⟶ model.nativeDiagram)
    (localComponents : RelativeClosedPositionedModalCoherent.CellAdmission model model.nativeDiagram
      (RelativeClosedPositionedModalCoherent.canonicalImages model) cell) :
    cell = completeComparison.hom :=
  RelativeClosedPositionedModalCoherent.admitted_cell_unique model model.nativeDiagram
    (RelativeClosedPositionedModalCoherent.canonicalImages model)
    (RelativeClosedPositionedModalCoherent.canonical_admitted model) cell localComponents

theorem complete_isomorphism_class_is_inhabited_and_unique :
    Nonempty (Unique {comparison : model.nativeDiagram ≅ model.nativeDiagram //
      RelativeClosedPositionedModalCoherent.CellAdmission model model.nativeDiagram
        (RelativeClosedPositionedModalCoherent.canonicalImages model) comparison.hom}) :=
  ⟨RelativeClosedPositionedModalCoherent.admittedIsoUnique model model.nativeDiagram
    (RelativeClosedPositionedModalCoherent.canonicalImages model)
    (RelativeClosedPositionedModalCoherent.canonical_admitted model)⟩

abbrev Program := base.obj source.program

def emptyPost : Subobject (Program ⊗ Nat) := fromSet ∅
def emptyName : Nat ⟶ power doctrine Program := name doctrine emptyPost
def actualPossibility : power doctrine Program ⟶ power doctrine Program := model.namedImageAt none

theorem actual_possibility_complete : actualPossibility =
    RelativeClosedPositionedModalNativeMeaning.possibilityOperation doctrine
      (base.map source.source) (base.map source.target) := model.namedImageAt_complete none

theorem actual_possibility_does_not_invent_an_empty_postcondition :
    ¬ Contains (family doctrine (emptyName ≫ actualPossibility))
      (RelativeClosedWeakBaseControls.trueValue, 0) := by
  intro held
  have reading : family doctrine (emptyName ≫ actualPossibility) =
      doctrine.existsAlong (base.map source.source ▷ Nat)
        (doctrine.reindex (base.map source.target ▷ Nat) emptyPost) := by
    have operator := actual_possibility_complete.trans
      (RelativeClosedPositionedModalNativeMeaning.possibilityOperation_complete doctrine
        (base.map source.source) (base.map source.target)).symm
    have first := congrArg (family doctrine)
      ((congrArg (fun arrow => emptyName ≫ arrow) operator).trans
        (Category.assoc emptyName
          (InternalPredicateQuantifier.precomposition (HigherOrderInternalPredicateObject.operations doctrine)
            (base.map source.target))
          (HigherOrderInternalPredicateQuantifier.existsOperation doctrine (base.map source.source))).symm)
    have post := (HigherOrderInternalPredicateQuantifier.precomposition_supplied doctrine
      (base.map source.target) emptyName).trans
        (congrArg (doctrine.reindex (base.map source.target ▷ Nat)) (family_name doctrine emptyPost))
    exact first.trans ((HigherOrderInternalPredicateQuantifier.exists_supplied doctrine
      (base.map source.source)
      (emptyName ≫ InternalPredicateQuantifier.precomposition (HigherOrderInternalPredicateObject.operations doctrine)
        (base.map source.target))).trans
      (congrArg (doctrine.existsAlong (base.map source.source ▷ Nat)) post))
  have complete := (congrArg (fun predicate : Subobject (Program ⊗ Nat) =>
    Contains predicate (RelativeClosedWeakBaseControls.trueValue, 0)) reading).mp held
  obtain ⟨witness, admitted, _reaches⟩ := (contains_exists _ _ _).mp complete
  have emptyRead := (contains_reindex _ _ _).mp admitted
  exact (contains_fromSet ∅ _).mp emptyRead

def constantTruth : power doctrine Program ⟶ power doctrine Program :=
  name doctrine (⊤ : Subobject (Program ⊗ power doctrine Program))

theorem constant_truth_accepts_the_empty_postcondition :
    Contains (family doctrine (emptyName ≫ constantTruth))
      (RelativeClosedWeakBaseControls.trueValue, 0) := by
  have reading : family doctrine (emptyName ≫ constantTruth) = ⊤ := by
    rw [← family_substitution, constantTruth, family_name, doctrine.reindex_top]
  exact (congrArg (fun predicate : Subobject (Program ⊗ Nat) =>
    Contains predicate (RelativeClosedWeakBaseControls.trueValue, 0)) reading).mpr (contains_top _)

theorem constant_truth_is_not_the_actual_mapped_possibility : constantTruth ≠ actualPossibility := by
  intro same
  exact actual_possibility_does_not_invent_an_empty_postcondition
    ((congrArg (fun arrow : power doctrine Program ⟶ power doctrine Program =>
      Contains (family doctrine (emptyName ≫ arrow)) (RelativeClosedWeakBaseControls.trueValue, 0)) same).mp
        constant_truth_accepts_the_empty_postcondition)

def wrongValues : Option Bool → RelativeClosedSyntax.Interpretation.ArrowValue Type
  | none => ⟨power doctrine Program, power doctrine Program, constantTruth⟩
  | some origin => model.modalValues (some origin)

theorem wrong_local_declaration_square_is_rejected :
    ¬RelativeClosedPositionedModalRealization.LocalAdmission source selected base model.predicates wrongValues := by
  intro admitted
  have complete := RelativeClosedSyntax.Interpretation.ArrowValue.arrows_heq
    ((admitted none).trans (model.modalDiagrams none).symm)
  exact constant_truth_is_not_the_actual_mapped_possibility
    ((eq_of_heq complete).trans (model.namedImageAt_complete none).symm)

theorem wrong_complete_meanings_have_no_generated_realization :
    ¬RelativeClosedSyntax.Interpretation.Realization
      (RelativeClosedPositionedModalPresentation.signature source selected)
      (RelativeClosedPositionedModalRealization.assignment source base model.predicates wrongValues) :=
  fun realized => wrong_local_declaration_square_is_rejected
    (RelativeClosedPositionedModalRealization.necessary_local source selected base model.predicates wrongValues realized)

end Mettapedia.GSLT.Core.RelativeClosedPositionedModalModelControls
