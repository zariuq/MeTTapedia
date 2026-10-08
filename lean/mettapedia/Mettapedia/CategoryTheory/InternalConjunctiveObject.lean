import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.Order.Lattice

/-!
# Internal conjunctive objects and their satisfying scopes

Two operation arrows and four finite diagrams earn the complete meet and
truth structure on every generalized-element fibre. Their contravariant
substitution preserves the order and operations. Actual equalizers with
truth represent satisfying scopes and every guarded-arrow factorization.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalConjunctiveObject

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory

universe w k

variable (D : Type w) [Category.{k} D] [CartesianMonoidalCategory D]

structure Operations where
  proposition : D
  truth : 𝟙_ D ⟶ proposition
  conjunction : proposition ⊗ proposition ⟶ proposition

namespace Operations

variable {D} (operations : Operations D)

def swapBody : operations.proposition ⊗ operations.proposition ⟶ operations.proposition :=
  CartesianMonoidalCategory.lift (CartesianMonoidalCategory.snd _ _) (CartesianMonoidalCategory.fst _ _) ≫
    operations.conjunction

def associateLeft : (operations.proposition ⊗ operations.proposition) ⊗ operations.proposition ⟶ operations.proposition :=
  CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst _ _ ≫ operations.conjunction)
    (CartesianMonoidalCategory.snd _ _) ≫ operations.conjunction

def associateRight : (operations.proposition ⊗ operations.proposition) ⊗ operations.proposition ⟶ operations.proposition :=
  CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst _ _ ≫ CartesianMonoidalCategory.fst _ _)
    (CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst _ _ ≫ CartesianMonoidalCategory.snd _ _)
      (CartesianMonoidalCategory.snd _ _) ≫ operations.conjunction) ≫ operations.conjunction

def diagonalBody : operations.proposition ⟶ operations.proposition :=
  CartesianMonoidalCategory.lift (𝟙 _) (𝟙 _) ≫ operations.conjunction

def truthUnitBody : operations.proposition ⟶ operations.proposition :=
  CartesianMonoidalCategory.lift (𝟙 _) (CartesianMonoidalCategory.toUnit _ ≫ operations.truth) ≫ operations.conjunction

structure Laws : Prop where
  commutativity : swapBody operations = operations.conjunction
  associativity : associateLeft operations = associateRight operations
  idempotence : diagonalBody operations = 𝟙 operations.proposition
  truthUnit : truthUnitBody operations = 𝟙 operations.proposition

def Fiber (context : D) := context ⟶ operations.proposition

def meet {context : D} (first second : operations.Fiber context) : operations.Fiber context :=
  CartesianMonoidalCategory.lift first second ≫ operations.conjunction

def top (context : D) : operations.Fiber context := CartesianMonoidalCategory.toUnit context ≫ operations.truth

variable {operations} (laws : Laws operations)

include laws in
theorem meet_comm {context : D} (first second : operations.Fiber context) :
    operations.meet first second = operations.meet second first := by
  have same := congrArg (fun arrow => CartesianMonoidalCategory.lift first second ≫ arrow) laws.commutativity
  simpa only [swapBody, ← Category.assoc, CartesianMonoidalCategory.comp_lift,
    CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd, meet] using same.symm

include laws in
theorem meet_assoc {context : D} (first second third : operations.Fiber context) :
    operations.meet (operations.meet first second) third = operations.meet first (operations.meet second third) := by
  have same := congrArg (fun arrow => CartesianMonoidalCategory.lift
    (CartesianMonoidalCategory.lift first second) third ≫ arrow) laws.associativity
  simpa only [associateLeft, associateRight, ← Category.assoc, CartesianMonoidalCategory.comp_lift,
    CartesianMonoidalCategory.lift_fst, CartesianMonoidalCategory.lift_snd, meet] using same

include laws in
theorem meet_idem {context : D} (predicate : operations.Fiber context) :
    operations.meet predicate predicate = predicate := by
  have same := congrArg (fun arrow => predicate ≫ arrow) laws.idempotence
  simpa only [diagonalBody, ← Category.assoc, CartesianMonoidalCategory.comp_lift, Category.comp_id, meet] using same

include laws in
theorem meet_top {context : D} (predicate : operations.Fiber context) :
    operations.meet predicate (operations.top context) = predicate := by
  have same := congrArg (fun arrow => predicate ≫ arrow) laws.truthUnit
  simpa only [truthUnitBody, ← Category.assoc, CartesianMonoidalCategory.comp_lift,
    Category.comp_id, CartesianMonoidalCategory.comp_toUnit, meet, top] using same

instance fiberMin (context : D) : Min (operations.Fiber context) := ⟨operations.meet⟩

@[instance_reducible] def semilattice (context : D) : SemilatticeInf (operations.Fiber context) :=
  SemilatticeInf.mk' (meet_comm laws) (meet_assoc laws) (meet_idem laws)

@[instance_reducible] def orderTop (context : D) :
    letI := semilattice laws context
    OrderTop (operations.Fiber context) := by
  letI := semilattice laws context
  refine
    { top := operations.top context
      le_top := ?_ }
  intro predicate
  exact (meet_comm laws _ _).trans (meet_top laws predicate)

variable (operations)

def reindex {context before : D} (mapping : context ⟶ before) : operations.Fiber before → operations.Fiber context :=
  fun predicate => mapping ≫ predicate

theorem reindex_identity (context : D) (predicate : operations.Fiber context) :
    operations.reindex (𝟙 context) predicate = predicate := Category.id_comp predicate

theorem reindex_comp {context before after : D} (first : context ⟶ before)
    (second : before ⟶ after) (predicate : operations.Fiber after) :
    operations.reindex (first ≫ second) predicate = operations.reindex first (operations.reindex second predicate) :=
  Category.assoc _ _ _

theorem reindex_top {context before : D} (mapping : context ⟶ before) :
    operations.reindex mapping (operations.top before) = operations.top context := by
  change mapping ≫ (CartesianMonoidalCategory.toUnit before ≫ operations.truth) =
    CartesianMonoidalCategory.toUnit context ≫ operations.truth
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun arrow => arrow ≫ operations.truth) (CartesianMonoidalCategory.comp_toUnit mapping))

theorem reindex_meet {context before : D} (mapping : context ⟶ before)
    (first second : operations.Fiber before) :
    operations.reindex mapping (operations.meet first second) =
      operations.meet (operations.reindex mapping first) (operations.reindex mapping second) := by
  change mapping ≫ (CartesianMonoidalCategory.lift first second ≫ operations.conjunction) =
    CartesianMonoidalCategory.lift (mapping ≫ first) (mapping ≫ second) ≫ operations.conjunction
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun arrow => arrow ≫ operations.conjunction)
      (CartesianMonoidalCategory.comp_lift mapping first second))

def reindexOrderHom {context before : D} (mapping : context ⟶ before) :
    letI := semilattice laws before
    letI := semilattice laws context
    OrderHom (operations.Fiber before) (operations.Fiber context) := by
  letI := semilattice laws before
  letI := semilattice laws context
  refine ⟨operations.reindex mapping, ?_⟩
  intro first second ordered
  change operations.meet second first = first at ordered
  change operations.meet (operations.reindex mapping second) (operations.reindex mapping first) =
    operations.reindex mapping first
  exact (reindex_meet operations mapping second first).symm.trans
    (congrArg (operations.reindex mapping) ordered)

variable [HasEqualizers D]

def satisfying {context : D} (predicate : operations.Fiber context) : D := equalizer predicate (operations.top context)

def inclusion {context : D} (predicate : operations.Fiber context) : operations.satisfying predicate ⟶ context :=
  equalizer.ι predicate (operations.top context)

instance inclusion_mono {context : D} (predicate : operations.Fiber context) : Mono (operations.inclusion predicate) where
  right_cancellation _ _ same := equalizer.hom_ext same

theorem inclusion_satisfies {context : D} (predicate : operations.Fiber context) :
    operations.reindex (operations.inclusion predicate) predicate = operations.top (operations.satisfying predicate) :=
  (equalizer.condition _ _).trans (reindex_top operations (operations.inclusion predicate))

def factor {context before : D} (predicate : operations.Fiber before) (mapping : context ⟶ before)
    (evidence : operations.reindex mapping predicate = operations.top context) : context ⟶ operations.satisfying predicate :=
  equalizer.lift mapping (evidence.trans (reindex_top operations mapping).symm)

theorem factor_inclusion {context before : D} (predicate : operations.Fiber before) (mapping : context ⟶ before)
    (evidence : operations.reindex mapping predicate = operations.top context) :
    operations.factor predicate mapping evidence ≫ operations.inclusion predicate = mapping := equalizer.lift_ι _ _

def factorization {context before : D} (predicate : operations.Fiber before) :
    (context ⟶ operations.satisfying predicate) ≃
      {mapping : context ⟶ before // operations.reindex mapping predicate = operations.top context} where
  toFun mapping := ⟨mapping ≫ operations.inclusion predicate, by
    rw [reindex_comp, inclusion_satisfies, reindex_top]⟩
  invFun mapping := operations.factor predicate mapping.val mapping.property
  left_inv mapping := (cancel_mono (operations.inclusion predicate)).mp (factor_inclusion _ _ _ _)
  right_inv mapping := Subtype.ext (factor_inclusion _ _ _ _)

end Operations

end Mettapedia.CategoryTheory.InternalConjunctiveObject
