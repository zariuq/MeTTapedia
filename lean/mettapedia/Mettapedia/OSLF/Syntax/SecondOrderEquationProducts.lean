import Mettapedia.OSLF.Syntax.SecondOrderEquationRepresentability

/-!
# Finite products after the authored equation quotient

The congruence on contextual assignments splits componentwise over a joined
metavariable context. Consequently the product universal property survives
the quotient by authored equations, with no additional product axiom.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SecondOrderContext

open _root_.CategoryTheory
open _root_.CategoryTheory.Limits

variable {S : Signature} {M : List (MetaArity S)}

private abbrev classContext (P : EquationPresentation S M)
    (X : Object S) : EquationContexts P := ⟨X⟩

private def classMap (P : EquationPresentation S M)
    {X Y : Object S} (arrow : X ⟶ Y) :
    classContext P X ⟶ classContext P Y :=
  Quot.mk _ arrow

/-- Pair maps between equation-class contexts by pairing representatives.
Pointwise equation congruence proves independence of both representatives. -/
def quotientPair (P : EquationPresentation S M)
    (source left right : Object S)
    (first : classContext P source ⟶ classContext P left)
    (second : classContext P source ⟶ classContext P right) :
    classContext P source ⟶
      classContext P (productObject S left right) :=
  Quot.liftOn₂ first second
    (fun f g => classMap P (pair S source left right f g))
    (by
      intro first second second' rightRelated
      apply _root_.CategoryTheory.Quotient.sound P.homRel
      apply (P.homRel_pair_iff source left right first first second second').mpr
      constructor
      · intro index
        exact .refl _
      · simpa only [HomRel.compClosure_eq_self P.homRel] using rightRelated)
    (by
      intro first first' second leftRelated
      apply _root_.CategoryTheory.Quotient.sound P.homRel
      apply (P.homRel_pair_iff source left right first first' second second).mpr
      constructor
      · simpa only [HomRel.compClosure_eq_self P.homRel] using leftRelated
      · intro index
        exact .refl _)

/-- The first projection of a pair of equation-class maps is its first map. -/
theorem quotientPair_first (P : EquationPresentation S M)
    (source left right : Object S)
    (first : classContext P source ⟶ classContext P left)
    (second : classContext P source ⟶ classContext P right) :
    quotientPair P source left right first second ≫
      classMap P (firstProjection S left right) = first := by
  induction first using Quot.ind with
  | _ rawFirst =>
      induction second using Quot.ind with
      | _ rawSecond =>
          change classMap P
            (pair S source left right rawFirst rawSecond ≫
              firstProjection S left right) =
            classMap P rawFirst
          rw [pair_first]

/-- The second projection of a pair is its second map. -/
theorem quotientPair_second (P : EquationPresentation S M)
    (source left right : Object S)
    (first : classContext P source ⟶ classContext P left)
    (second : classContext P source ⟶ classContext P right) :
    quotientPair P source left right first second ≫
      classMap P (secondProjection S left right) = second := by
  induction first using Quot.ind with
  | _ rawFirst =>
      induction second using Quot.ind with
      | _ rawSecond =>
          change classMap P
            (pair S source left right rawFirst rawSecond ≫
              secondProjection S left right) =
            classMap P rawSecond
          rw [pair_second]

/-- A map into the joined equation-class context is recovered from its two
projections. This proves uniqueness without choosing canonical term forms. -/
theorem quotientPair_components (P : EquationPresentation S M)
    (source left right : Object S)
    (candidate : classContext P source ⟶
      classContext P (productObject S left right)) :
    quotientPair P source left right
      (candidate ≫ classMap P (firstProjection S left right))
      (candidate ≫ classMap P (secondProjection S left right)) =
      candidate := by
  induction candidate using Quot.ind with
  | _ raw =>
      change classMap P
        (pair S source left right
          (raw ≫ firstProjection S left right)
          (raw ≫ secondProjection S left right)) =
        classMap P raw
      have components := productHomEquiv_natural S raw
        (𝟙 (productObject S left right))
      simp only [Category.comp_id] at components
      change productHomEquiv S source left right raw =
        (raw ≫ firstProjection S left right,
          raw ≫ secondProjection S left right) at components
      unfold pair
      rw [← components]
      exact congrArg (classMap P)
        ((productHomEquiv S source left right).symm_apply_apply raw)

/-- The original context product is still a categorical product after
quotienting by arbitrary authored equation lists. -/
def quotientProductIsLimit (P : EquationPresentation S M)
    (left right : Object S) :
    IsLimit (BinaryFan.mk
      (classMap P (firstProjection S left right))
      (classMap P (secondProjection S left right))) := by
  refine BinaryFan.isLimitMk
    (fun cone => quotientPair P cone.pt.as left right cone.fst cone.snd)
    ?_ ?_ ?_
  · intro cone
    exact quotientPair_first P cone.pt.as left right cone.fst cone.snd
  · intro cone
    exact quotientPair_second P cone.pt.as left right cone.fst cone.snd
  · intro cone candidate firstEq secondEq
    have components := quotientPair_components P cone.pt.as left right candidate
    simpa only [firstEq, secondEq] using components.symm

/-- The empty metavariable context remains terminal after equations. -/
def quotientEmptyIsTerminal (P : EquationPresentation S M) :
    IsTerminal (classContext P (empty S)) :=
  IsTerminal.ofUniqueHom
    (fun _ => Quot.mk _ (fun index => Fin.elim0 index))
    (by
      intro object arrow
      induction arrow using Quot.ind with
      | _ representative =>
          have same : representative = (fun index => Fin.elim0 index) := by
            funext index
            exact Fin.elim0 index
          exact congrArg (classMap P) same)

instance quotientHasTerminal (P : EquationPresentation S M) :
    HasTerminal (EquationContexts P) :=
  (quotientEmptyIsTerminal P).hasTerminal

instance quotientHasLimitPair (P : EquationPresentation S M)
    (left right : EquationContexts P) :
    HasLimit (Limits.pair left right) :=
  ⟨⟨BinaryFan.mk
    (classMap P (firstProjection S left.as right.as))
    (classMap P (secondProjection S left.as right.as)),
    quotientProductIsLimit P left.as right.as⟩⟩

instance quotientHasBinaryProducts (P : EquationPresentation S M) :
    HasBinaryProducts (EquationContexts P) :=
  hasBinaryProducts_of_hasLimit_pair (EquationContexts P)

/-- Every authored equation quotient of second-order contexts retains finite
products, so it is a valid input to the relative finite-limit completion. -/
instance quotientHasFiniteProducts (P : EquationPresentation S M) :
    HasFiniteProducts (EquationContexts P) :=
  CategoryTheory.hasFiniteProducts_of_has_binary_and_terminal

end Mettapedia.OSLF.Binding.SecondOrderContext

#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.quotientProductIsLimit
#print axioms Mettapedia.OSLF.Binding.SecondOrderContext.quotientHasFiniteProducts
