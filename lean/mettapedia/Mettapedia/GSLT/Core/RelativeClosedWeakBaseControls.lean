import Mettapedia.CategoryTheory.RelativeClosedSyntaxBaseExtensionWeakInterpretation
import Mettapedia.CategoryTheory.PredicateDoctrineClosed
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.CategoryTheory.Monoidal.Closed.Types

/-!
# Weak base augmentation retains independent native data

The Boolean order is interpreted by its actual representable truth fibres,
with an outer value lift. Its false fibre is empty and its true fibre is
inhabited. The genuine finite-limit and exponential comparisons are proved;
the base interpretation is neither an identity nor a constant functor.

Independent Boolean data and negation are then supplied over that base. The
augmented presentation retains both complete data values and the original
diagram, while its weak base map and guarded false scope remain distinct.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedWeakBaseControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open scoped _root_.CategoryTheory.SemilatticeInf
open scoped Mettapedia.CategoryTheory.PredicateDoctrine.HeytingClosed
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open GeneratedCategory Interpretation

abbrev truthFunctor : Bool ⥤ Type := coyoneda.obj (Opposite.op true) ⋙ uliftFunctor.{0, 0}

private instance raised_lex : PreservesFiniteLimits uliftFunctor.{0, 0} :=
  preservesFiniteLimits_of_natIso uliftFunctorTrivial.symm

instance truth_lex : PreservesFiniteLimits truthFunctor := inferInstance

private theorem truth_subsingleton (value : Bool) : Subsingleton (truthFunctor.obj value) := by
  change Subsingleton (ULift.{0} (true ⟶ value))
  infer_instance

private theorem function_subsingleton (argument result : Bool) :
    Subsingleton ((ihom (truthFunctor.obj argument)).obj (truthFunctor.obj result)) := by
  change Subsingleton (TypeCat.Hom (truthFunctor.obj argument) (truthFunctor.obj result))
  refine ⟨fun before after => ?_⟩
  apply TypeCat.Hom.ext
  apply TypeCat.Fun.ext
  funext value
  exact (truth_subsingleton result).elim (before.hom'.toFun value) (after.hom'.toFun value)

instance truth_closed : MonoidalClosedFunctor truthFunctor where
  comparison_iso argument := by
    suffices ∀ result : Bool,
        IsIso ((expComparison truthFunctor argument).natTrans.app result) from
      NatIso.isIso_of_isIso_app _
    intro result
    apply (isIso_iff_bijective _).mpr
    refine ⟨fun _ _ _ => (truth_subsingleton ((ihom argument).obj result)).elim _ _, ?_⟩
    intro output
    cases argument <;> cases result
    · exact ⟨ULift.up (𝟙 true), (function_subsingleton false false).elim _ _⟩
    · exact ⟨ULift.up (𝟙 true), (function_subsingleton false true).elim _ _⟩
    · change TypeCat.Hom (truthFunctor.obj true) (truthFunctor.obj false) at output
      have impossible : (true : Bool) ≤ false :=
        (output.hom'.toFun (ULift.up (𝟙 true))).down.le
      exact False.elim ((not_le_of_gt Bool.false_lt_true) impossible)
    · exact ⟨ULift.up (𝟙 true), (function_subsingleton true true).elim _ _⟩

def trueValue : truthFunctor.obj true := ULift.up (𝟙 true)

theorem false_fibre_empty : IsEmpty (truthFunctor.obj false) := by
  refine ⟨fun value => ?_⟩
  have impossible : (true : Bool) ≤ false := value.down.le
  exact (not_le_of_gt Bool.false_lt_true) impossible

theorem base_fibres_differ : truthFunctor.obj false ≠ truthFunctor.obj true := by
  intro same
  exact false_fibre_empty.false (same.symm ▸ trueValue)

abbrev names : Symbols where
  ObjectName := Unit
  ArrowName := Bool
  EquationName := Empty

def signature : Signature (C := Bool) (symbols := names) where
  objectRank _ := 0
  arrowRank _ := 1
  source _ := .name ()
  target _ := .name ()
  source_before _ := by simp only [ObjectCode.before]; decide
  target_before _ := by simp only [ObjectCode.before]; decide
  equationRank origin := origin.elim
  equationSource origin := origin.elim
  equationTarget origin := origin.elim
  left origin := origin.elim
  right origin := origin.elim
  equation_before origin := origin.elim

def negate : ULift.{0} Bool ⟶ ULift.{0} Bool :=
  TypeCat.ofHom (fun value => ULift.up (Bool.not value.down))

def meanings : Assignment Bool names Type where
  base := truthFunctor
  object _ := ULift Bool
  arrow origin := ⟨ULift Bool, ULift Bool, if origin then negate else 𝟙 _⟩

theorem realized : Realization signature meanings where
  source _ := rfl
  target _ := rfl
  equation origin := origin.elim

private instance meanings_lex : PreservesFiniteLimits meanings.base := truth_lex
private instance meanings_closed : MonoidalClosedFunctor meanings.base := truth_closed

abbrev augmented := BaseExtension.extend signature
abbrev extended := BaseExtension.WeakExtension.assignment meanings

theorem extended_realized : Realization augmented extended :=
  BaseExtension.WeakExtension.realization meanings realized

def completeInterpretation : Object augmented ⥤ Type := Interpretation.functor extended extended_realized

theorem complete_original_diagram : (BaseExtension.originalMap signature).functor ⋙
    completeInterpretation = Interpretation.functor meanings realized :=
  BaseExtension.WeakExtension.original_diagram_readback meanings realized

theorem complete_weak_base : baseFunctor augmented ⋙ completeInterpretation = truthFunctor :=
  Interpretation.functor_base extended extended_realized

theorem supplied_negation_read : extended.evaluateArrow
    (BaseExtension.originalArrowCode (C := Bool) (symbols := names) (.name true)) =
      some (⟨ULift Bool, ULift Bool, negate⟩ : ArrowValue Type) :=
  (BaseExtension.WeakExtension.original_arrow_read (signature := signature) meanings (.name true)).trans rfl

abbrev dataObject : Object augmented :=
  ⟨.name (BaseExtension.originalObjects (C := Bool) (symbols := names) ()),
    ⟨.objectName (signature := augmented) _⟩⟩

def originalNegation : RawHom dataObject dataObject :=
  ⟨BaseExtension.originalArrowCode (C := Bool) (symbols := names) (.name true),
    ⟨(BaseExtension.originalMap signature).derivation
      (.arrowName (signature := signature) true
        (by change Derivation signature (.object (.name ()))
            exact .objectName (signature := signature) ())
        (by change Derivation signature (.object (.name ()))
            exact .objectName (signature := signature) ()))⟩⟩

theorem actual_negation_value :
    HEq (rawArrowValue extended extended_realized originalNegation) negate :=
  functor_map_heq extended extended_realized originalNegation negate supplied_negation_read

theorem actual_data_object : objectValue extended extended_realized dataObject = ULift Bool :=
  objectValue_unique extended extended_realized dataObject _ rfl

def nativeNegation : ULift.{0} Bool ⟶ ULift.{0} Bool :=
  eqToHom actual_data_object.symm ≫ rawArrowValue extended extended_realized originalNegation ≫
    eqToHom actual_data_object

theorem nativeNegation_complete : nativeNegation = negate :=
  ((conj_eqToHom_iff_heq negate _ actual_data_object.symm actual_data_object.symm).mpr
    actual_negation_value.symm).symm

theorem complete_values_retained :
    (nativeNegation (ULift.up false)).down = true ∧
      (nativeNegation (ULift.up true)).down = false := by
  rw [nativeNegation_complete]
  exact ⟨rfl, rfl⟩

theorem constant_data_replacement_rejected :
    nativeNegation (ULift.up false) ≠ nativeNegation (ULift.up true) := by
  intro same
  have read := congrArg ULift.down same
  rw [complete_values_retained.1, complete_values_retained.2] at read
  exact Bool.false_ne_true read.symm

theorem old_false_scope_remains_empty : IsEmpty (completeInterpretation.obj (baseObject augmented false)) := by
  have same := functor_base_object extended extended_realized false
  exact same.symm ▸ false_fibre_empty

theorem false_scope_cannot_supply_true_value :
    ¬ Nonempty (completeInterpretation.obj (baseObject augmented false)) := by
  rintro ⟨value⟩
  exact old_false_scope_remains_empty.false value

end Mettapedia.GSLT.Core.RelativeClosedWeakBaseControls
