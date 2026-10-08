import Mettapedia.CategoryTheory.RelativeClosedConjunctivePredicates
import Mettapedia.CategoryTheory.InternalConjunctiveObject

/-!
# Conjunctive predicates on the complete native extension

The native base-comparison declarations add equations to the authored
conjunctive presentation. The four local meet diagrams are transported
through that actual inclusion functor, then earn the predicate order,
substitution and guarded equalizer scopes on the final category itself.
No identification of its equation quotient with the earlier one is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedConjunctive.NativePredicates

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open RelativeClosedSyntax GeneratedCategory

universe k

variable {C : Type k} [Category.{k} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]

omit [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C] in
private theorem lift_pairing {names : Symbols.{k}}
    {presentation : Signature (C := C) (symbols := names)}
    {context left right : Object presentation} (first : context ⟶ left) (second : context ⟶ right) :
    CartesianMonoidalCategory.lift first second = pairing first second := by
  apply product_joint_cancel
  · exact (CartesianMonoidalCategory.lift_fst first second).trans (pairing_first first second).symm
  · exact (CartesianMonoidalCategory.lift_snd first second).trans (pairing_second first second).symm

omit [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C] in
private theorem toUnit_terminal {names : Symbols.{k}}
    {presentation : Signature (C := C) (symbols := names)} (context : Object presentation) :
    CartesianMonoidalCategory.toUnit context = toTerminal context := toTerminal_unique _

omit [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C] in
private theorem map_pairing {names nextNames : Symbols.{k}}
    {presentation : Signature (C := C) (symbols := names)}
    {next : Signature (C := C) (symbols := nextNames)} (mapping : SignatureMap presentation next)
    {context left right : Object presentation} (first : context ⟶ left) (second : context ⟶ right) :
    mapping.functor.map (pairing first second) =
      pairing (mapping.functor.map first) (mapping.functor.map second) := by
  refine Quotient.inductionOn₂ first second ?_
  intro before after
  rfl

def operations : InternalConjunctiveObject.Operations (Object (nativeSignature (C := C))) where
  proposition := (nativeInclusion (C := C)).object Predicates.propositionObject
  truth := (nativeInclusion (C := C)).functor.map Predicates.truth
  conjunction := (nativeInclusion (C := C)).functor.map Predicates.conjunction

theorem laws : InternalConjunctiveObject.Operations.Laws (operations (C := C)) where
  commutativity := by
    have mapped := congrArg (nativeInclusion (C := C)).functor.map (Predicates.commutative_diagram (C := C))
    rw [Functor.map_comp, map_pairing] at mapped
    change CartesianMonoidalCategory.lift
        (second operations.proposition operations.proposition)
        (first operations.proposition operations.proposition) ≫ operations.conjunction = operations.conjunction
    rw [lift_pairing]
    exact mapped
  associativity := by
    have mapped := congrArg (nativeInclusion (C := C)).functor.map (Predicates.associative_diagram (C := C))
    simp only [Functor.map_comp, map_pairing] at mapped
    change InternalConjunctiveObject.Operations.associateLeft operations =
      InternalConjunctiveObject.Operations.associateRight operations
    unfold InternalConjunctiveObject.Operations.associateLeft InternalConjunctiveObject.Operations.associateRight
    simp only [lift_pairing]
    exact mapped
  idempotence := by
    have mapped := congrArg (nativeInclusion (C := C)).functor.map (Predicates.idempotent_diagram (C := C))
    rw [Functor.map_comp, map_pairing, _root_.CategoryTheory.Functor.map_id] at mapped
    change CartesianMonoidalCategory.lift (𝟙 operations.proposition) (𝟙 operations.proposition) ≫
      operations.conjunction = 𝟙 operations.proposition
    rw [lift_pairing]
    exact mapped
  truthUnit := by
    have mapped := congrArg (nativeInclusion (C := C)).functor.map (Predicates.truth_unit_diagram (C := C))
    rw [Functor.map_comp, map_pairing, _root_.CategoryTheory.Functor.map_id, Functor.map_comp] at mapped
    change CartesianMonoidalCategory.lift (𝟙 operations.proposition)
        (CartesianMonoidalCategory.toUnit operations.proposition ≫ operations.truth) ≫
      operations.conjunction = 𝟙 operations.proposition
    rw [lift_pairing, toUnit_terminal]
    exact mapped

abbrev Fiber (context : Object (nativeSignature (C := C))) := (operations (C := C)).Fiber context

instance fiberMin (context : Object (nativeSignature (C := C))) : Min (Fiber context) :=
  ⟨operations.meet⟩

instance fiberSemilattice (context : Object (nativeSignature (C := C))) : SemilatticeInf (Fiber context) :=
  InternalConjunctiveObject.Operations.semilattice laws context

instance fiberTop (context : Object (nativeSignature (C := C))) : OrderTop (Fiber context) :=
  InternalConjunctiveObject.Operations.orderTop laws context

def reindex {context before : Object (nativeSignature (C := C))} (mapping : context ⟶ before) :
    Fiber before → Fiber context := operations.reindex mapping

theorem reindex_identity (context : Object (nativeSignature (C := C))) (predicate : Fiber context) :
    reindex (𝟙 context) predicate = predicate := operations.reindex_identity context predicate

theorem reindex_comp {context before after : Object (nativeSignature (C := C))}
    (first : context ⟶ before) (second : before ⟶ after) (predicate : Fiber after) :
    reindex (first ≫ second) predicate = reindex first (reindex second predicate) :=
  operations.reindex_comp first second predicate

theorem reindex_meet {context before : Object (nativeSignature (C := C))}
    (mapping : context ⟶ before) (first second : Fiber before) :
    reindex mapping (first ⊓ second) = reindex mapping first ⊓ reindex mapping second :=
  operations.reindex_meet mapping first second

theorem reindex_top {context before : Object (nativeSignature (C := C))} (mapping : context ⟶ before) :
    reindex mapping ⊤ = ⊤ := operations.reindex_top mapping

def reindexOrderHom {context before : Object (nativeSignature (C := C))} (mapping : context ⟶ before) :
    Fiber before →o Fiber context := InternalConjunctiveObject.Operations.reindexOrderHom operations laws mapping

abbrev satisfying {context : Object (nativeSignature (C := C))} (predicate : Fiber context) :=
  operations.satisfying predicate

abbrev inclusion {context : Object (nativeSignature (C := C))} (predicate : Fiber context) :=
  operations.inclusion predicate

theorem inclusion_satisfies {context : Object (nativeSignature (C := C))} (predicate : Fiber context) :
    reindex (inclusion predicate) predicate = ⊤ := operations.inclusion_satisfies predicate

abbrev factorization {context before : Object (nativeSignature (C := C))} (predicate : Fiber before) :=
  operations.factorization (context := context) predicate

end Mettapedia.CategoryTheory.RelativeClosedConjunctive.NativePredicates
