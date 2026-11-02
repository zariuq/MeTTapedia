import Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLRealization
import Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLTermControls
import Mettapedia.GSLT.LanguageDef.AdmittedContainerHOL

/-!
# Admitted natural arithmetic and empty-element controls

The positive model evaluates the actual admitted Natural operations. The
Vector source syntax keeps its real length expressions; source elements are
mapped through primitive image guards, including an empty source sort.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLRealizationControls
open Mettapedia.Logic.HOL
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open IndexedInductiveHOLRealization IndexedInductiveNatVec
open IndexedInductiveHOLTerms.Controls (arithmetic model empty Symbol number element)
noncomputable section

def numbers : Numbers arithmetic model where
  equivalence := Natural.representation.symm.trans Equiv.ulift.symm
  zero := rfl
  successor _ := rfl
  addition n m := by
    apply ULift.ext
    apply Natural.representation.injective
    change Natural.toNat (Natural.add (Natural.fromNat n) (Natural.fromNat m)) =
      Natural.toNat (Natural.fromNat (n+m))
    rw [Natural.toNat_add, Natural.toNat_fromNat, Natural.toNat_fromNat, Natural.toNat_fromNat]

def elements : Elements arithmetic model Bool := fullElements arithmetic model Bool Equiv.ulift.symm

def interpreted := realization arithmetic model Bool numbers elements
theorem field_images : IndexedContainerPositionTerms.FieldImages interpreted
    (guards arithmetic model Bool elements) := images _ _ _ _ _

def sourceIndex : Vectors.IndexExpr [.length] := .addition (.variable .here) (.successor (.variable .here))

theorem composite_index (source : Natural.Carrier) :
    model.denote ((reading arithmetic Bool).indices.term sourceIndex)
      ((reading arithmetic Bool).indices.valuation model interpreted.value interpreted.parameterValues
        (context := [.length]) (source,PUnit.unit)) =
        interpreted.index (Natural.add source (Natural.succ source)) :=
  interpreted.index_correct sourceIndex (source,PUnit.unit)

theorem natural_values_injective : Function.Injective (naturalValues arithmetic model numbers) :=
  (naturalValues arithmetic model numbers).injective

def noElements : Elements arithmetic model Empty := emptyElements arithmetic model
def emptyInterpretation := realization arithmetic model Empty numbers noElements

theorem empty_field_images : IndexedContainerPositionTerms.FieldImages emptyInterpretation
    (guards arithmetic model Empty noElements) := images _ _ _ _ _

theorem empty_element_refused (target : Ty.denote model.Carrier element) :
    ¬ (model.denote ((guards arithmetic model Empty noElements).value .payload) empty target).down := by
  exact fun impossible => impossible

theorem wrong_bool_refused :
    ¬ ((guards arithmetic model Empty noElements).value .payload =
      (guards arithmetic model Bool elements).value .payload) := by
  intro same
  have different := congrArg (fun predicate => (model.denote predicate empty (.up false)).down) same
  change False = True at different
  exact (eq_iff_iff.mp different).mpr True.intro

def emptyBlock := PositiveInductiveBlockBridge.Direct.admitted 0 (Vectors.admitted Empty)
theorem emptyRegistered : emptyBlock.WellRegistered :=
  PositiveInductiveBlockBridge.Direct.admitted_registered 0 (Vectors.admitted Empty)
def emptyCodes := AdmittedContainerHOL.codes emptyBlock emptyRegistered
def emptyCons := IndexedContainerPositionTerms.codeAt (reading arithmetic Empty) emptyCodes ⟨1,by decide⟩
def emptyNil := IndexedContainerPositionTerms.codeAt (reading arithmetic Empty) emptyCodes ⟨0,by decide⟩

theorem empty_cons_source : emptyCons =
    .data .length (.data .payload (.recursive (.variable (.there .here))
      (.result (.successor (.variable (.there .here)))))) := rfl

theorem empty_cons_refused
    (data : Env (Ty.denote model.Carrier) ((reading arithmetic Empty).fields emptyCons)) :
    ¬ CurriedPredicates.holds model ((reading arithmetic Empty).fields emptyCons)
      ((guards arithmetic model Empty noElements).compile emptyCons Subst.id) empty data := by
  intro valid
  have represented : emptyInterpretation.Represents (context := []) PUnit.unit Subst.id empty := by
    intro type impossible
    exact nomatch impossible
  obtain ⟨index,shape,_⟩ := (empty_field_images.compile_holds emptyCons PUnit.unit Subst.id empty represented data).mp valid
  change Σ _length : Natural.Carrier, Σ _head : Empty, _ at shape
  exact shape.2.1.elim

theorem empty_nil_accepted :
    CurriedPredicates.holds model ((reading arithmetic Empty).fields emptyNil)
      ((guards arithmetic model Empty noElements).compile emptyNil Subst.id) empty PUnit.unit :=
  True.intro

def refusedFields : Env (Ty.denote.{0,0} model.Carrier) ((reading arithmetic Empty).fields emptyCons) :=
  (.up Natural.zero,.up false,PUnit.unit)

theorem empty_context_represented :
    emptyInterpretation.Represents (context := []) PUnit.unit Subst.id empty := by
  intro type impossible
  exact nomatch impossible

theorem concrete_empty_cons_refused :
    ¬ CurriedPredicates.holds model ((reading arithmetic Empty).fields emptyCons)
      ((guards arithmetic model Empty noElements).compile emptyCons Subst.id) empty refusedFields := by
  intro valid
  obtain ⟨index,shape,_⟩ := (empty_field_images.compile_holds emptyCons PUnit.unit
    Subst.id empty empty_context_represented refusedFields).mp valid
  change Σ _length : Natural.Carrier, Σ _head : Empty, _ at shape
  exact shape.2.1.elim

#print axioms field_images
#print axioms composite_index
#print axioms empty_field_images
#print axioms wrong_bool_refused
#print axioms empty_cons_refused
end
end Mettapedia.GSLT.LanguageDef.IndexedInductiveHOLRealizationControls
