import Mettapedia.CategoryTheory.RelativeClosedConjunctiveNativePredicates
import Mettapedia.CategoryTheory.RelativeClosedConjunctiveInterpretation
import Mettapedia.GSLT.Core.RelativeClosedWeakBaseControls

/-!
# Complete conjunctive values and proper satisfying scopes

An independently supplied Boolean meet interprets the generated operations.
The actual quotient conjunction retains both input values. The generated
predicate identity is properly smaller than truth; its satisfying equalizer
admits precisely guarded maps. A first-projection operation has the same
formation and idempotence but cannot realize commutativity.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedConjunctiveControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open scoped _root_.CategoryTheory.SemilatticeInf
open scoped Mettapedia.CategoryTheory.PredicateDoctrine.HeytingClosed
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open GeneratedCategory Interpretation
open Mettapedia.CategoryTheory.RelativeClosedConjunctive

def boolean : Mettapedia.CategoryTheory.RelativeClosedConjunctive.Interpretation.Meaning Type where
  proposition := ULift.{0} Bool
  truth := TypeCat.ofHom (fun _ => ULift.up true)
  conjunction := TypeCat.ofHom (fun value => ULift.up (value.1.down && value.2.down))

theorem boolean_laws : Mettapedia.CategoryTheory.RelativeClosedConjunctive.Interpretation.Laws boolean where
  commutativity := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    change ULift.up (value.2.down && value.1.down) = ULift.up (value.1.down && value.2.down)
    exact congrArg ULift.up (Bool.and_comm _ _)
  associativity := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    change ULift.up ((value.1.1.down && value.1.2.down) && value.2.down) =
      ULift.up (value.1.1.down && (value.1.2.down && value.2.down))
    exact congrArg ULift.up (Bool.and_assoc _ _ _)
  idempotence := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    change ULift.up (value.down && value.down) = value
    cases value with
    | up value => cases value <;> rfl
  truthUnit := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    change ULift.up (value.down && true) = value
    cases value with
    | up value => cases value <;> rfl

def meanings := Mettapedia.CategoryTheory.RelativeClosedConjunctive.Interpretation.lawfulAssignment RelativeClosedWeakBaseControls.truthFunctor boolean

theorem realized : Realization (lawfulSignature (C := Bool)) meanings :=
  Mettapedia.CategoryTheory.RelativeClosedConjunctive.Interpretation.lawful_realization RelativeClosedWeakBaseControls.truthFunctor boolean boolean_laws

def rawConjunction := (equationInclusion (C := Bool)).rawArrow conjunctionRaw

theorem proposition_read : objectValue meanings realized (Predicates.propositionObject (C := Bool)) = ULift Bool :=
  objectValue_unique meanings realized _ _ rfl

theorem conjunction_domain_read : objectValue meanings realized (product (Predicates.propositionObject (C := Bool)) Predicates.propositionObject) = ULift Bool ⊗ ULift Bool :=
  objectValue_unique meanings realized _ _ (Assignment.evaluate_product meanings rfl rfl)

def actualConjunction : ULift.{0} Bool ⊗ ULift.{0} Bool ⟶ ULift.{0} Bool :=
  eqToHom conjunction_domain_read.symm ≫ rawArrowValue meanings realized rawConjunction ≫ eqToHom proposition_read

theorem complete_conjunction : actualConjunction = boolean.conjunction := by
  have reading : HEq (rawArrowValue meanings realized rawConjunction) boolean.conjunction :=
    functor_map_heq meanings realized rawConjunction boolean.conjunction rfl
  exact ((conj_eqToHom_iff_heq boolean.conjunction _ conjunction_domain_read.symm proposition_read.symm).mpr
    reading.symm).symm

theorem supplied_values_retained :
    (actualConjunction (ULift.up false, ULift.up true)).down = false ∧
      (actualConjunction (ULift.up true, ULift.up true)).down = true := by
  rw [complete_conjunction]
  exact ⟨rfl, rfl⟩

private def rawTop : RawHom (omega (C := Bool)) omega :=
  (⟨.terminal omegaCode, ⟨.terminalArrow omegaFormed⟩⟩ : RawHom omega (terminal signature)).compose truthRaw

theorem identity_predicate_is_proper :
    (𝟙 (Predicates.propositionObject (C := Bool)) : Predicates.Fiber (Predicates.propositionObject (C := Bool))) ≠ Predicates.top _ := by
  intro same
  have rawSame : classOf ((equationInclusion (C := Bool)).rawArrow (RawHom.identity omega)) =
      classOf ((equationInclusion (C := Bool)).rawArrow rawTop) := same
  have equation := Quotient.exact rawSame
  have sound := Interpretation.sound meanings realized equation.some
  have firstRead : meanings.evaluateArrow ((equationInclusion (C := Bool)).rawArrow (RawHom.identity omega)).code =
      some (⟨ULift Bool, ULift Bool, 𝟙 (ULift Bool)⟩ : ArrowValue Type) :=
    meanings.evaluate_identity rfl
  have secondRead : meanings.evaluateArrow ((equationInclusion (C := Bool)).rawArrow rawTop).code =
      some (⟨ULift Bool, ULift Bool, CartesianMonoidalCategory.toUnit (ULift Bool) ≫ boolean.truth⟩ : ArrowValue Type) :=
    meanings.evaluate_compose _ _ (meanings.evaluate_terminal_arrow rfl) rfl
  have impossible := Interprets.equal_arrows _ _ sound firstRead secondRead
  have retained := congrArg (fun function => (function (ULift.up false)).down) impossible
  exact Bool.false_ne_true retained

theorem unrestricted_identity_has_no_guarded_factor :
    ¬ ∃ factor : Predicates.propositionObject (C := Bool) ⟶
        Predicates.satisfying (𝟙 (Predicates.propositionObject (C := Bool))),
      factor ≫ Predicates.inclusion (𝟙 (Predicates.propositionObject (C := Bool))) = 𝟙 _ := by
  rintro ⟨factor, factors⟩
  have evidence := ((Predicates.factorization (𝟙 (Predicates.propositionObject (C := Bool)))).toFun factor).property
  change (factor ≫ Predicates.inclusion (𝟙 _)) ≫ 𝟙 _ = _ at evidence
  rw [factors, Category.id_comp] at evidence
  exact identity_predicate_is_proper evidence

theorem supplied_guard_scope_retained :
    Predicates.reindex (Predicates.inclusion (𝟙 (Predicates.propositionObject (C := Bool)))) (𝟙 _) = ⊤ :=
  Predicates.inclusion_satisfies _

def projecting : Mettapedia.CategoryTheory.RelativeClosedConjunctive.Interpretation.Meaning Type where
  proposition := ULift.{0} Bool
  truth := boolean.truth
  conjunction := CartesianMonoidalCategory.fst _ _

theorem projecting_retains_idempotence :
    Mettapedia.CategoryTheory.RelativeClosedConjunctive.Interpretation.diagonalBody projecting =
      𝟙 projecting.proposition := by
  apply TypeCat.Hom.ext
  apply TypeCat.Fun.ext
  funext value
  rfl

theorem projecting_cannot_realize :
    ¬ Realization (lawfulSignature (C := Bool))
      (Mettapedia.CategoryTheory.RelativeClosedConjunctive.Interpretation.lawfulAssignment RelativeClosedWeakBaseControls.truthFunctor projecting) := by
  intro realized
  have laws := Mettapedia.CategoryTheory.RelativeClosedConjunctive.Interpretation.necessary_laws RelativeClosedWeakBaseControls.truthFunctor projecting realized
  have retained := congrArg (fun function => (function (ULift.up false, ULift.up true)).down) laws.commutativity
  exact Bool.false_ne_true retained.symm

def nativeModel := Mettapedia.CategoryTheory.RelativeClosedConjunctive.Interpretation.nativeModel RelativeClosedWeakBaseControls.truthFunctor boolean boolean_laws

theorem complete_base_retained :
    baseFunctor (nativeSignature (C := Bool)) ⋙ nativeModel.diagram = RelativeClosedWeakBaseControls.truthFunctor :=
  Interpretation.functor_base nativeModel.meanings nativeModel.realization


def nativeProposition := (NativePredicates.operations (C := Bool)).proposition

def nativeRawConjunction := (nativeInclusion (C := Bool)).rawArrow rawConjunction

theorem native_proposition_read :
    objectValue nativeModel.meanings nativeModel.realization nativeProposition = ULift Bool :=
  objectValue_unique nativeModel.meanings nativeModel.realization _ _ rfl

theorem native_conjunction_domain_read :
    objectValue nativeModel.meanings nativeModel.realization (product nativeProposition nativeProposition) =
      ULift Bool ⊗ ULift Bool :=
  objectValue_unique nativeModel.meanings nativeModel.realization _ _
    (Assignment.evaluate_product nativeModel.meanings rfl rfl)

def actualNativeConjunction : ULift.{0} Bool ⊗ ULift.{0} Bool ⟶ ULift.{0} Bool :=
  eqToHom native_conjunction_domain_read.symm ≫
    rawArrowValue nativeModel.meanings nativeModel.realization nativeRawConjunction ≫
      eqToHom native_proposition_read

theorem complete_native_conjunction : actualNativeConjunction = boolean.conjunction := by
  have reading : HEq (rawArrowValue nativeModel.meanings nativeModel.realization nativeRawConjunction)
      boolean.conjunction :=
    functor_map_heq nativeModel.meanings nativeModel.realization nativeRawConjunction boolean.conjunction rfl
  exact ((conj_eqToHom_iff_heq boolean.conjunction _ native_conjunction_domain_read.symm
    native_proposition_read.symm).mpr reading.symm).symm

theorem native_supplied_values_retained :
    (actualNativeConjunction (ULift.up false, ULift.up true)).down = false ∧
      (actualNativeConjunction (ULift.up true, ULift.up true)).down = true := by
  rw [complete_native_conjunction]
  exact ⟨rfl, rfl⟩

private def nativeRawTop := (nativeInclusion (C := Bool)).rawArrow ((equationInclusion (C := Bool)).rawArrow rawTop)

private theorem native_top_class :
    (NativePredicates.operations (C := Bool)).top nativeProposition = classOf nativeRawTop := by
  change CartesianMonoidalCategory.toUnit nativeProposition ≫
    (NativePredicates.operations (C := Bool)).truth = classOf nativeRawTop
  have unit : CartesianMonoidalCategory.toUnit nativeProposition = toTerminal nativeProposition :=
    toTerminal_unique _
  rw [unit]
  rfl

theorem native_identity_predicate_is_proper :
    (𝟙 nativeProposition : NativePredicates.Fiber nativeProposition) ≠
      (NativePredicates.operations (C := Bool)).top nativeProposition := by
  intro same
  have rawSame : classOf ((nativeInclusion (C := Bool)).rawArrow
      ((equationInclusion (C := Bool)).rawArrow (RawHom.identity omega))) =
        classOf nativeRawTop := same.trans native_top_class
  have equation := Quotient.exact rawSame
  have sound := Interpretation.sound nativeModel.meanings nativeModel.realization equation.some
  have firstRead : nativeModel.meanings.evaluateArrow ((nativeInclusion (C := Bool)).rawArrow
      ((equationInclusion (C := Bool)).rawArrow (RawHom.identity omega))).code =
        some (⟨ULift Bool, ULift Bool, 𝟙 (ULift Bool)⟩ : ArrowValue Type) :=
    nativeModel.meanings.evaluate_identity rfl
  have secondRead : nativeModel.meanings.evaluateArrow nativeRawTop.code =
      some (⟨ULift Bool, ULift Bool, CartesianMonoidalCategory.toUnit (ULift Bool) ≫ boolean.truth⟩ : ArrowValue Type) :=
    nativeModel.meanings.evaluate_compose _ _ (nativeModel.meanings.evaluate_terminal_arrow rfl) rfl
  have impossible := Interprets.equal_arrows _ _ sound firstRead secondRead
  exact Bool.false_ne_true (congrArg (fun function => (function (ULift.up false)).down) impossible)

theorem native_identity_has_no_unguarded_factor :
    ¬ ∃ factor : nativeProposition ⟶ NativePredicates.satisfying (𝟙 nativeProposition),
      factor ≫ NativePredicates.inclusion (𝟙 nativeProposition) = 𝟙 _ := by
  rintro ⟨factor, factors⟩
  have evidence := ((NativePredicates.factorization (𝟙 nativeProposition)).toFun factor).property
  change (factor ≫ NativePredicates.inclusion (𝟙 _)) ≫ 𝟙 _ = _ at evidence
  have retained := (congrArg (fun arrow : nativeProposition ⟶ nativeProposition => arrow ≫ 𝟙 nativeProposition)
    factors).symm.trans evidence
  exact native_identity_predicate_is_proper ((Category.id_comp (𝟙 nativeProposition)).symm.trans retained)

theorem native_guard_scope_retained :
    NativePredicates.reindex (NativePredicates.inclusion (𝟙 nativeProposition)) (𝟙 _) = ⊤ :=
  NativePredicates.inclusion_satisfies _

end Mettapedia.GSLT.Core.RelativeClosedConjunctiveControls
