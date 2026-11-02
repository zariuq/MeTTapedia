import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.Reactions

/-!
# Two blocks side by side are one block

A labelled semantics composes the transitions of two members of a parallel composition into one synchronization. Each
member is equivalent to a block with parts at its front (`ReactsAt`); then the bag of the two is equivalent to one
block with both fronts (`ReactsAt.pair`):

- the first member's restrictions are outermost and the second's inside them;
- the first's members are lifted past the second's restrictions, and the second's past the first's, above its own;
- the other members of the bag are lifted past both.

This is scope extrusion twice (`bag_two_blocks_equivalent`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics (EquationEquiv DerivedInstance derivedInstance_equivalent
  equationEquiv_fill)
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)

variable {language : LanguageDef} {block : Block} [laws : BlockSignature language block]

/-- Lifting twice from the outside is lifting by the sum. -/
theorem liftBVars_zero_zero (first second : Nat) (pattern : Pattern) :
    liftBVars 0 first (liftBVars 0 second pattern) = liftBVars 0 (second + first) pattern := by
  rw [liftBVars_eq_rename, liftBVars_eq_rename, liftBVars_eq_rename, rename_comp]
  congr 1
  funext index
  simp only [Function.comp, shiftAbove, Nat.not_lt_zero, if_false]
  omega

/-- Lifting above a lift by the cutoff lifts by both. -/
theorem liftBVars_above_lift (cutoff shift : Nat) (pattern : Pattern) :
    liftBVars cutoff shift (liftBVars 0 cutoff pattern) = liftBVars 0 (cutoff + shift) pattern := by
  rw [liftBVars_eq_rename, liftBVars_eq_rename, liftBVars_eq_rename, rename_comp]
  congr 1
  funext index
  simp only [Function.comp, shiftAbove, Nat.not_lt_zero, if_false]
  split_ifs <;> omega

theorem liftBVars_bag (cutoff shift : Nat) (elements : List Pattern) :
    liftBVars cutoff shift (.collection .hashBag elements none) =
      .collection .hashBag (elements.map (liftBVars cutoff shift)) none := by
  simp [liftBVars, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVarsList_eq_map]

theorem perm_middle_swap {α : Type} (front back front' back' others : List α) :
    ((front ++ back) ++ (front' ++ back') ++ others).Perm ((front ++ front') ++ (back ++ back' ++ others)) := by
  have middle : (back ++ (front' ++ (back' ++ others))).Perm (front' ++ (back ++ (back' ++ others))) := by
    have swapped := (List.perm_append_comm (l₁ := back) (l₂ := front')).append_right (back' ++ others)
    simpa only [List.append_assoc] using swapped
  simpa only [List.append_assoc] using middle.append_left front

omit laws in
/-- Members typed under a block's restrictions, lifted past restrictions inserted outside them. -/
theorem lift_members_inside {free : FreeTypeContext} {bound : List TypeExpr} {elements : List Pattern}
    (inner inserted : Nat)
    (members : Members language block free (List.replicate inner (TypeExpr.base block.name) ++ bound) elements) :
    Members language block free (List.replicate inner (TypeExpr.base block.name) ++
        (List.replicate inserted (TypeExpr.base block.name) ++ bound)) (elements.map (liftBVars inner inserted)) := by
  intro element member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  have lifted := lift_typed (inner := List.replicate inner (TypeExpr.base block.name))
    (inserted := List.replicate inserted (TypeExpr.base block.name)) (outer := bound) (members original originalMember)
  simpa only [List.length_replicate, List.append_assoc] using lifted

theorem replicate_nested (first second : Nat) (sort : TypeExpr) (bound : List TypeExpr) :
    List.replicate first sort ++ (List.replicate second sort ++ bound) =
      List.replicate (second + first) sort ++ bound := by
  rw [← List.append_assoc, ← List.replicate_add, Nat.add_comm]

/-- **Two blocks side by side in a bag are one block**: the first's restrictions outermost, the second's inside. -/
theorem bag_two_blocks_equivalent {free : FreeTypeContext} {bound : List TypeExpr} {count count' : Nat}
    {inner inner' others : List Pattern}
    (innerMembers : Members language block free (List.replicate count (TypeExpr.base block.name) ++ bound) inner)
    (innerMembers' : Members language block free (List.replicate count' (TypeExpr.base block.name) ++ bound) inner')
    (othersMembers : Members language block free bound others) :
    EquationEquiv (engineBasePremises RelationEnv.empty) language
      (.collection .hashBag (Prenex.restricts block count (.collection .hashBag inner none) ::
        Prenex.restricts block count' (.collection .hashBag inner' none) :: others) none)
      (Prenex.restricts block (count + count') (.collection .hashBag (inner.map (liftBVars 0 count') ++
        inner'.map (liftBVars count' count) ++ others.map (liftBVars 0 (count + count'))) none)) := by
  have secondTyped : HasType language free bound (Prenex.restricts block count' (.collection .hashBag inner' none))
      (.base block.proc) := restricts_typed count' (bag_typed (rest := none) innerMembers')
  have outerMembers : Members language block free bound
      (Prenex.restricts block count' (.collection .hashBag inner' none) :: others) := by
    intro element member
    rcases List.mem_cons.mp member with rfl | inOthers
    · exact secondTyped
    · exact othersMembers element inOthers
  have first := bag_block_equivalent innerMembers outerMembers
  have liftedSecond : liftBVars 0 count (Prenex.restricts block count' (.collection .hashBag inner' none)) =
      Prenex.restricts block count' (.collection .hashBag (inner'.map (liftBVars count' count)) none) := by
    rw [liftBVars_restricts, Nat.zero_add, liftBVars_bag]
  rw [List.map_cons, liftedSecond] at first
  have liftedInner' := lift_members_inside (bound := bound) count' count innerMembers'
  have liftedOthers := lift_members count othersMembers
  have restMembers : Members language block free (List.replicate count (TypeExpr.base block.name) ++ bound)
      (inner ++ others.map (liftBVars 0 count)) := by
    intro element member
    rcases List.mem_append.mp member with inInner | inOthers
    · exact innerMembers element inInner
    · exact liftedOthers element inOthers
  have middleTyped : HasType language free (List.replicate count (TypeExpr.base block.name) ++ bound)
      (.collection .hashBag (inner ++ Prenex.restricts block count'
        (.collection .hashBag (inner'.map (liftBVars count' count)) none) :: others.map (liftBVars 0 count)) none)
      (.base block.proc) := by
    apply bag_typed (rest := none)
    intro element member
    rcases List.mem_append.mp member with inInner | inRest
    · exact innerMembers element inInner
    · rcases List.mem_cons.mp inRest with rfl | inOthers
      · exact restricts_typed count' (bag_typed (rest := none) liftedInner')
      · exact liftedOthers element inOthers
  have reordered := derivedInstance_equivalent (base := engineBasePremises RelationEnv.empty)
    (DerivedInstance.bagPerm_of_sorted ⟨free, _, middleTyped⟩
      (List.perm_middle (a := Prenex.restricts block count'
        (.collection .hashBag (inner'.map (liftBVars count' count)) none)) (l₁ := inner)
        (l₂ := others.map (liftBVars 0 count))))
  have second := bag_block_equivalent liftedInner' restMembers
  have inside := restricts_equation (language := language) (block := block) count (.trans _ _ _ reordered second)
  rw [restricts_add] at inside
  have finalMembers : Members language block free (List.replicate (count + count') (TypeExpr.base block.name) ++ bound)
      (inner'.map (liftBVars count' count) ++ (inner ++ others.map (liftBVars 0 count)).map (liftBVars 0 count')) := by
    rw [← replicate_nested]
    intro element member
    rcases List.mem_append.mp member with inFirst | inSecond
    · exact liftedInner' element inFirst
    · exact lift_members count' restMembers element inSecond
  have othersSame : (others.map (liftBVars 0 count)).map (liftBVars 0 count') =
      others.map (liftBVars 0 (count + count')) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro element _
    simp only [Function.comp_apply, liftBVars_zero_zero]
  have permutation : (inner'.map (liftBVars count' count) ++ (inner ++ others.map (liftBVars 0 count)).map
      (liftBVars 0 count')).Perm (inner.map (liftBVars 0 count') ++ inner'.map (liftBVars count' count) ++
        others.map (liftBVars 0 (count + count'))) := by
    rw [List.map_append, othersSame, ← List.append_assoc]
    exact List.perm_append_comm.append_right _
  have final := derivedInstance_equivalent (base := engineBasePremises RelationEnv.empty)
    (DerivedInstance.bagPerm_of_sorted ⟨free, _, bag_typed (rest := none) finalMembers⟩ permutation)
  have finalInside := restricts_equation (language := language) (block := block) (count + count') final
  exact .trans _ _ _ first (.trans _ _ _ inside finalInside)

/-- **Two members of a bag, each a reaction at the front of a block, are a reaction at the front of one block**,
with both fronts: the first's restrictions outermost. -/
theorem ReactsAt.pair {free : FreeTypeContext} {bound : List TypeExpr} {first second target target' : Pattern}
    {others : List Pattern} {count count' : Nat} {parts result rest parts' result' rest' : List Pattern}
    (results : Members language block free (List.replicate count (TypeExpr.base block.name) ++ bound) parts →
      Members language block free (List.replicate count (TypeExpr.base block.name) ++ bound) result)
    (results' : Members language block free (List.replicate count' (TypeExpr.base block.name) ++ bound) parts' →
      Members language block free (List.replicate count' (TypeExpr.base block.name) ++ bound) result')
    (othersMembers : Members language block free bound others)
    (othersObjects : ∀ element ∈ others, isObjectPattern element = true)
    (reacts : ReactsAt language block free bound first target count parts result rest)
    (reacts' : ReactsAt language block free bound second target' count' parts' result' rest') :
    ReactsAt language block free bound (.collection .hashBag (first :: second :: others) none)
      (.collection .hashBag (target :: target' :: others) none) (count + count')
      (parts.map (liftBVars 0 count') ++ parts'.map (liftBVars count' count))
      (result.map (liftBVars 0 count') ++ result'.map (liftBVars count' count))
      (rest.map (liftBVars 0 count') ++ rest'.map (liftBVars count' count) ++
        others.map (liftBVars 0 (count + count'))) := by
  have partsMembers : Members language block free (List.replicate count (TypeExpr.base block.name) ++ bound) parts :=
    fun element member => reacts.members element (by simp [member])
  have partsMembers' : Members language block free (List.replicate count' (TypeExpr.base block.name) ++ bound) parts' :=
    fun element member => reacts'.members element (by simp [member])
  have resultRest : Members language block free (List.replicate count (TypeExpr.base block.name) ++ bound)
      (result ++ rest) := by
    intro element member
    rcases List.mem_append.mp member with inResult | inRest
    · exact results partsMembers element inResult
    · exact reacts.members element (by simp [inRest])
  have resultRest' : Members language block free (List.replicate count' (TypeExpr.base block.name) ++ bound)
      (result' ++ rest') := by
    intro element member
    rcases List.mem_append.mp member with inResult | inRest
    · exact results' partsMembers' element inResult
    · exact reacts'.members element (by simp [inRest])
  have arrange : ∀ (front back front' back' : List Pattern),
      ((front ++ back).map (liftBVars 0 count') ++ (front' ++ back').map (liftBVars count' count) ++
        others.map (liftBVars 0 (count + count'))).Perm
      ((front.map (liftBVars 0 count') ++ front'.map (liftBVars count' count)) ++
        (back.map (liftBVars 0 count') ++ back'.map (liftBVars count' count) ++
          others.map (liftBVars 0 (count + count')))) := by
    intro front back front' back'
    simp only [List.map_append]
    exact perm_middle_swap _ _ _ _ _
  have lifted : ∀ {front back front' back' : List Pattern},
      Members language block free (List.replicate count (TypeExpr.base block.name) ++ bound) (front ++ back) →
      Members language block free (List.replicate count' (TypeExpr.base block.name) ++ bound) (front' ++ back') →
      Members language block free (List.replicate (count + count') (TypeExpr.base block.name) ++ bound)
        ((front ++ back).map (liftBVars 0 count') ++ (front' ++ back').map (liftBVars count' count) ++
          others.map (liftBVars 0 (count + count'))) := by
    intro front back front' back' members members'
    have firstLifted := lift_members (bound := List.replicate count (TypeExpr.base block.name) ++ bound) count' members
    have secondLifted := lift_members_inside (bound := bound) count' count members'
    have othersLifted := lift_members (count + count') othersMembers
    rw [replicate_nested] at firstLifted secondLifted
    intro element member
    rcases List.mem_append.mp member with inFirst | inOthers
    · rcases List.mem_append.mp inFirst with inLeft | inRight
      · exact firstLifted element inLeft
      · exact secondLifted element inRight
    · exact othersLifted element inOthers
  have objectsLifted : ∀ {front back front' back' : List Pattern},
      (∀ element ∈ front ++ back, isObjectPattern element = true) →
      (∀ element ∈ front' ++ back', isObjectPattern element = true) →
      ∀ element ∈ (front ++ back).map (liftBVars 0 count') ++ (front' ++ back').map (liftBVars count' count) ++
          others.map (liftBVars 0 (count + count')), isObjectPattern element = true := by
    intro front back front' back' objects objects' element member
    simp only [List.mem_append, List.mem_map] at member
    rcases member with (⟨original, member, rfl⟩ | ⟨original, member, rfl⟩) | ⟨original, member, rfl⟩ <;>
      rw [isObject_liftBVars]
    · exact objects original (List.mem_append.mpr member)
    · exact objects' original (List.mem_append.mpr member)
    · exact othersObjects original member
  have joined : ∀ {front back front' back' : List Pattern} {one two : Pattern},
      EquationEquiv (engineBasePremises RelationEnv.empty) language one
        (Prenex.restricts block count (.collection .hashBag (front ++ back) none)) →
      EquationEquiv (engineBasePremises RelationEnv.empty) language two
        (Prenex.restricts block count' (.collection .hashBag (front' ++ back') none)) →
      Members language block free (List.replicate count (TypeExpr.base block.name) ++ bound) (front ++ back) →
      Members language block free (List.replicate count' (TypeExpr.base block.name) ++ bound) (front' ++ back') →
      EquationEquiv (engineBasePremises RelationEnv.empty) language
        (.collection .hashBag (one :: two :: others) none)
        (Prenex.restricts block (count + count') (.collection .hashBag
          ((front.map (liftBVars 0 count') ++ front'.map (liftBVars count' count)) ++
            (back.map (liftBVars 0 count') ++ back'.map (liftBVars count' count) ++
              others.map (liftBVars 0 (count + count')))) none)) := by
    intro front back front' back' one two oneIs twoIs members members'
    have firstFilled := equationEquiv_fill (.collection .hashBag [] .hole (two :: others) none) oneIs
    have secondFilled := equationEquiv_fill
      (.collection .hashBag [Prenex.restricts block count (.collection .hashBag (front ++ back) none)] .hole others none)
      twoIs
    simp only [OneHoleContext.fill, List.nil_append, List.singleton_append] at firstFilled secondFilled
    have blocks := bag_two_blocks_equivalent members members' othersMembers
    have reordered := derivedInstance_equivalent (base := engineBasePremises RelationEnv.empty)
      (DerivedInstance.bagPerm_of_sorted ⟨free, _, bag_typed (rest := none) (lifted members members')⟩
        (arrange front back front' back'))
    exact .trans _ _ _ firstFilled (.trans _ _ _ secondFilled (.trans _ _ _ blocks
      (restricts_equation (language := language) (block := block) (count + count') reordered)))
  refine ⟨?_, ?_, joined reacts.source reacts'.source reacts.members reacts'.members,
    joined reacts.target reacts'.target resultRest resultRest'⟩
  · intro element member
    exact lifted reacts.members reacts'.members element
      ((arrange parts rest parts' rest').mem_iff.mpr member)
  · intro element member
    exact objectsLifted reacts.objects reacts'.objects element ((arrange parts rest parts' rest').mem_iff.mpr member)

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
