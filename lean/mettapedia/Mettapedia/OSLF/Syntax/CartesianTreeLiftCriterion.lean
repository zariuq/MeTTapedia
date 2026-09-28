import Mettapedia.OSLF.Syntax.IndexedRulePolynomialMorphisms

/-!
# Local criterion for lifting complete rule trees

A cartesian rule map preserves each recursive premise address, but its
constructor map need not be surjective. A raw firing tree lifts precisely
when its root constructor has a source constructor and every selected child
has a lift at the index specified by that constructor. This criterion keeps
the same premise occurrence even when two children have equal endpoints.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.CartesianTreeLiftCriterion

open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding.IndexedRulePolynomialMorphisms

universe uBase uIndex uOtherIndex uShape uPosition uOtherShape uOtherPosition

variable {Base : Type uBase}
variable {I : Base → Type uIndex} {J : Base → Type uOtherIndex}
variable {P : IndexedPolynomial.{uBase, uIndex, uShape, uPosition} Base I}
variable {Q : IndexedPolynomial.{uBase, uOtherIndex, uOtherShape, uOtherPosition} Base J}
variable {f : ∀ b, I b → J b}

/-- A source constructor at each node, with its own recursively checked
children, is the exact local condition for lifting a target firing tree.
This does not assume that every target constructor is representable. -/
inductive LocalTreeLift (h : Hom P Q f) (b : Base) :
    (i : I b) → Q.Fix b (f b i) → Prop where
  | roll {i : I b} (shape : P.Shape b i)
      (children : (position : Q.Position (h.onShape b i shape)) →
        Q.Fix b (Q.next (h.onShape b i shape) position))
      (childLift : ∀ position,
        LocalTreeLift h b
          (P.next shape ((h.onPosition b i shape) position))
          ((h.onNext b i shape position) ▸ children position)) :
      LocalTreeLift h b i (.roll (h.onShape b i shape) children)

private theorem cast_cancel {X : Type*} {F : X → Type*}
    {x y : X} (equal : x = y) (value : F x) :
    equal.symm ▸ (equal ▸ value) = value := by
  cases equal
  rfl

private theorem cast_dependent_congr {A B : Type*} {F : B → Type*}
    (index : A → B) (value : (x : A) → F (index x))
    {first second : A} (equal : first = second) :
    congrArg index equal ▸ value first = value second := by
  cases equal
  rfl

/-- Every locally liftable complete target tree has an actual source tree
whose cartesian image is exactly that tree. -/
theorem exists_lift (h : Hom P Q f) {b : Base} {i : I b}
    {tree : Q.Fix b (f b i)} (liftable : LocalTreeLift h b i tree) :
    ∃ source : P.Fix b i, h.mapFix b i source = tree := by
  induction liftable with
  | @roll i shape children childLift ih =>
      let values : (position : Q.Position (h.onShape b i shape)) →
          P.Fix b (P.next shape ((h.onPosition b i shape) position)) :=
        fun position => Classical.choose (ih position)
      let sourceChildren : (position : P.Position shape) →
          P.Fix b (P.next shape position) := fun position =>
        let targetPosition := (h.onPosition b i shape).symm position
        have same : (h.onPosition b i shape) targetPosition = position :=
          (h.onPosition b i shape).apply_symm_apply position
        congrArg (P.next shape) same ▸ values targetPosition
      refine ⟨.roll shape sourceChildren, ?_⟩
      change IndexedPolynomial.Fix.roll (h.onShape b i shape) _ =
        IndexedPolynomial.Fix.roll (h.onShape b i shape) children
      congr 1
      funext position
      have chosen :
          sourceChildren ((h.onPosition b i shape) position) =
            values position := by
        have samePosition :=
          (h.onPosition b i shape).symm_apply_apply position
        have moved := cast_dependent_congr
          (fun p => P.next shape ((h.onPosition b i shape) p))
          values samePosition
        have sameProof :
            congrArg
                (fun p => P.next shape ((h.onPosition b i shape) p))
                samePosition =
              congrArg (P.next shape)
                ((h.onPosition b i shape).apply_symm_apply
                  ((h.onPosition b i shape) position)) :=
          Subsingleton.elim _ _
        simpa only [sourceChildren, sameProof] using moved
      change (h.onNext b i shape position).symm ▸
          h.mapFix b _
            (sourceChildren ((h.onPosition b i shape) position)) =
        children position
      rw [chosen]
      change (h.onNext b i shape position).symm ▸
          h.mapFix b _ (Classical.choose (ih position)) = children position
      rw [Classical.choose_spec (ih position)]
      exact cast_cancel (h.onNext b i shape position) (children position)

/-- Cartesian mapping of a source firing tree satisfies the local
criterion at every node, including repeated premise occurrences. -/
theorem mapFix_liftable (h : Hom P Q f) (b : Base) (i : I b)
    (source : P.Fix b i) :
    LocalTreeLift h b i (h.mapFix b i source) := by
  refine IndexedPolynomial.Fix.eliminate P
    (fun b i source => LocalTreeLift h b i (h.mapFix b i source)) ?_
      b i source
  intro b i shape children ih
  change LocalTreeLift h b i
    (.roll (h.onShape b i shape)
      (fun position => (h.onNext b i shape position).symm ▸
        h.mapFix b _ (children ((h.onPosition b i shape) position))))
  apply LocalTreeLift.roll
  intro position
  simpa only [cast_cancel] using
    ih ((h.onPosition b i shape) position)

/-- The local condition characterizes the exact image of a cartesian
rule map on complete firing trees, not merely its endpoint relation. -/
theorem liftable_iff_exists (h : Hom P Q f) (b : Base) (i : I b)
    (tree : Q.Fix b (f b i)) :
    LocalTreeLift h b i tree ↔
      ∃ source : P.Fix b i, h.mapFix b i source = tree := by
  constructor
  · exact exists_lift h
  · rintro ⟨source, rfl⟩
    exact mapFix_liftable h b i source

#print axioms exists_lift
#print axioms mapFix_liftable
#print axioms liftable_iff_exists

end Mettapedia.OSLF.Binding.CartesianTreeLiftCriterion

namespace Mettapedia.OSLF.Binding.CartesianTreeLiftCriterion.Control

open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding.IndexedRulePolynomialMorphisms
open Mettapedia.OSLF.Binding.CartesianTreeLiftCriterion

/-- A source with one nullary constructor and a target with two distinct
nullary constructors. The source can interpret only the first target label. -/
private def source : IndexedPolynomial Unit (fun _ => Unit) where
  Shape := fun _ _ => Unit
  Position := fun _ => Empty
  next := fun _ position => nomatch position

private def target : IndexedPolynomial Unit (fun _ => Unit) where
  Shape := fun _ _ => Bool
  Position := fun _ => Empty
  next := fun _ position => nomatch position

private def inclusion : Hom source target (fun _ _ => ()) where
  onShape := fun _ _ _ => false
  onPosition := fun _ _ _ => Equiv.refl Empty
  onNext := by
    intro _ _ _ position
    cases position

private def missing : target.Fix () () :=
  .roll true (fun position => nomatch position)

private def rootLabel : target.Fix () () → Bool
  | .roll label _ => label

private theorem mapped_root_false (sourceTree : source.Fix () ()) :
    rootLabel (inclusion.mapFix () () sourceTree) = false := by
  match sourceTree with
  | .roll _ _ => rfl

/-- A cartesian premise map alone cannot lift an unrepresented constructor
label. This is why local constructor admission is a real hypothesis. -/
theorem missing_constructor_not_liftable :
    ¬ LocalTreeLift inclusion () () missing := by
  intro lift
  obtain ⟨sourceTree, mapped⟩ :=
    (liftable_iff_exists inclusion () () missing).mp lift
  have labels := (mapped_root_false sourceTree).symm.trans
    (congrArg rootLabel mapped)
  change false = true at labels
  cases labels

/-- The represented constructor does have a complete exact lift. -/
theorem represented_constructor_liftable :
    LocalTreeLift inclusion () ()
      (inclusion.mapFix () ()
        (.roll () (fun position => nomatch position))) :=
  mapFix_liftable inclusion () () _

#print axioms missing_constructor_not_liftable
#print axioms represented_constructor_liftable

end Mettapedia.OSLF.Binding.CartesianTreeLiftCriterion.Control
