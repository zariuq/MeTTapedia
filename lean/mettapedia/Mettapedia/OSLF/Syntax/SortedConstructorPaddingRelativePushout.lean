import Mettapedia.OSLF.Syntax.SortedConstructorPaddingCategory
import Mettapedia.GSLT.Logic.RelativePushoutFunctor

/-!
# Based normalization equivalence and actual equation-context RPOs

The quotient category has complete hom bijections and a surjective object
action. The full RPO universal property, including uniqueness, descends through
these earned actions. Its ground values are actual authored term classes.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.SortedConstructors.Padding

open _root_.CategoryTheory
open Mettapedia.GSLT.RelativePushout

universe u v

variable (signature : Signature.{u,v}) (paddingSort : signature.Srt)

instance normalization_full : (normalizationFunctor signature paddingSort).Full where
  map_surjective := fun supplied => ⟨EquationArrow.up supplied, EquationArrow.down_up supplied⟩

instance normalization_faithful : (normalizationFunctor signature paddingSort).Faithful where
  map_injective := by
    intro first second left right same
    exact EquationArrow.down_injective same

theorem normalization_objects : Function.Surjective (normalizationFunctor signature paddingSort).obj := by
  intro object
  cases object with
  | origin => exact ⟨.origin, rfl⟩
  | interface sort => exact ⟨.interface sort, rfl⟩

instance normalization_essSurj : (normalizationFunctor signature paddingSort).EssSurj where
  mem_essImage object := by
    obtain ⟨chosen, same⟩ := normalization_objects signature paddingSort object
    exact ⟨chosen, ⟨eqToIso same⟩⟩

instance normalization_isEquivalence : (normalizationFunctor signature paddingSort).IsEquivalence where

def normalizationEquivalence : EquationObject signature paddingSort ≌ ContextObject signature :=
  (normalizationFunctor signature paddingSort).asEquivalence

def classTermArrow {sort : signature.Srt} (term : Class signature paddingSort sort) :
    (.origin : EquationObject signature paddingSort) ⟶ .interface sort := EquationArrow.value term

def classContextArrow {source target : signature.Srt}
    (context : ContextClass signature paddingSort source target) :
    (.interface source : EquationObject signature paddingSort) ⟶ .interface target := EquationArrow.context context

theorem equation_hasRelativePushouts {first second : signature.Srt}
    (firstTerm : Class signature paddingSort first) (secondTerm : Class signature paddingSort second) :
    HasRelativePushouts (classTermArrow signature paddingSort firstTerm)
      (classTermArrow signature paddingSort secondTerm) := by
  apply reflects_hasRelativePushouts (normalizationFunctor signature paddingSort)
    (normalization_objects signature paddingSort)
  exact hasRelativePushouts signature
    (value signature paddingSort firstTerm) (value signature paddingSort secondTerm)

/-- The actual IPO judgment on classes agrees with the ordinary constructor
IPO on the fully retained normal forms. The bound need not act injectively. -/
theorem equation_idemPushout_iff {first second target : EquationObject signature paddingSort}
    (agent : (.origin : EquationObject signature paddingSort) ⟶ first)
    (redex : (.origin : EquationObject signature paddingSort) ⟶ second)
    (label : first ⟶ target) (reaction : second ⟶ target)
    (square : agent ≫ label = redex ≫ reaction) :
    IsIdemPushout agent redex label reaction square ↔
      IsIdemPushout ((normalizationFunctor signature paddingSort).map agent)
        ((normalizationFunctor signature paddingSort).map redex)
        ((normalizationFunctor signature paddingSort).map label)
        ((normalizationFunctor signature paddingSort).map reaction)
        (by rw [← Functor.map_comp, square, Functor.map_comp]) :=
  ⟨preserves_idemPushout (normalizationFunctor signature paddingSort)
      (normalization_objects signature paddingSort) square,
    reflects_idemPushout (normalizationFunctor signature paddingSort) square⟩

end Mettapedia.OSLF.SortedConstructors.Padding
