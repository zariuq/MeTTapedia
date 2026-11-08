import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.NativeUpToDead

/-!
# The cube is coherent: the joint state's inclusions commute with the swap of the two firings

The joint state of a clear diamond (`NativeDead.jointState`) depends on which firing is read first:
`jointState first second` keeps `f`'s rule locals in one copy and `g`'s in the other. Exchanging the
copies is an inclusion of one joint state in the other (`swapInclusion`), and:

* **the second inclusion is the first inclusion of the swapped diamond, after the swap**
  (`second_eq_swap_first`);
* **the swap carries the joint residual of every third firing to the joint residual of the swapped
  diamond** (`swap_jointResidual`);
* so **the cube is coherent** (`cube_coherent`): the third firing's residual after `f` and then `g / f`,
  read along the second inclusion of `jointState f g`, is the same firing read along the first inclusion
  of `jointState g f`. The two cubes (`NativeIterated.cube` for `f, g` and for `g, f`) fit along the swap,
  rather than being two separate diamonds.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open NativeResidual NativeDead NativeIterated NativeUpToDead

variable {S : Signature} {O : Type} [DecidableEq O] {Γ : Ctx S} {sort : S.Srt}
  [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

namespace NativeIterated

variable {s : NativeState S O Γ sort} {f g : LiveFiring s}

/-- **The swap of the two copies**, as an inclusion of one joint state in the other. -/
noncomputable def swapInclusion (first : f.toNative.Realized) (second : g.toNative.Realized)
    (clearF : Clear f g.selection g.rule g.outputs) (clearG : Clear g f.selection f.rule f.outputs) :
    Inclusion (jointState first second clearF) (jointState second first clearG) :=
  ⟨id, Function.injective_id, fun _ => rfl, swapNames, swapNames_injective,
    fun name => by rcases name with name | name | name <;> rfl⟩

/-- **The second inclusion is the first inclusion of the swapped diamond, after the swap.** -/
theorem second_eq_swap_first (first : f.toNative.Realized) (second : g.toNative.Realized)
    (clearF : Clear f g.selection g.rule g.outputs) (clearG : Clear g f.selection f.rule f.outputs) :
    (joint_second first second clearF clearG).toInclusion =
      (swapInclusion first second clearF clearG).comp (joint_first second first clearG clearF).toInclusion :=
  rfl

/-- Both orders reserve the same scopes. -/
theorem jointShift_swap (first : f.toNative.Realized) (second : g.toNative.Realized)
    (clearF : Clear f g.selection g.rule g.outputs) (clearG : Clear g f.selection f.rule f.outputs) :
    jointShift first second clearF = jointShift second first clearG := by
  unfold jointShift
  rw [show (jointState first second clearF).state.occupied = (jointState second first clearG).state.occupied from
    LiveFiring.closing_occupied first second clearF clearG]

/-- **The swap carries the joint residual of a third firing to the joint residual of the swapped
diamond.** -/
theorem swap_jointResidual (first : f.toNative.Realized) (second : g.toNative.Realized)
    (clearF : Clear f g.selection g.rule g.outputs) (clearG : Clear g f.selection f.rule f.outputs)
    (k : LiveFiring s) :
    (swapInclusion first second clearF clearG).firing (jointResidual first second clearF k) =
      jointResidual second first clearG k := by
  have source : Assignment.compose (swapInclusion first second clearF clearG).source (jointSource first second clearF) =
      jointSource second first clearG := by
    funext name
    cases name with
    | inl name => exact instantiate_generator _ _
    | inr name => exact instantiate_generator _ _
  have carried : jointCarry first second clearF = jointCarryAt s (jointShift second first clearG) :=
    congrArg (jointCarryAt s) (jointShift_swap first second clearF clearG)
  have target : Assignment.compose (swapInclusion first second clearF clearG).target (jointCarry first second clearF) =
      jointCarry second first clearG := by
    rw [carried]
    funext name
    cases name with
    | inl name => exact instantiate_generator _ _
    | inr name => exact instantiate_generator _ _
  show carryAlong (swapInclusion first second clearF clearG).source (swapInclusion first second clearF clearG).target
      (carryAlong (jointSource first second clearF) (jointCarry first second clearF) k) =
    carryAlong (jointSource second first clearG) (jointCarry second first clearG) k
  rw [carryAlong_comp, source, target]

/-- **The cube is coherent**: the third firing read along the second inclusion of `jointState f g` is
the same firing as read along the first inclusion of `jointState g f`, and both are its residual after
`f` and then `g / f`. -/
theorem cube_coherent (first : f.toNative.Realized) (second : g.toNative.Realized)
    (clearF : Clear f g.selection g.rule g.outputs) (clearG : Clear g f.selection f.rule f.outputs)
    (k : LiveFiring s) :
    (joint_second first second clearF clearG).firing (jointResidual first second clearF k) =
        (joint_first second first clearG clearF).firing (jointResidual second first clearG k) ∧
      (joint_first second first clearG clearF).firing (jointResidual second first clearG k) =
        residualAfter (LiveFiring.after second first clearG) (residualAfter first k) := by
  refine ⟨?_, (cube second first clearG clearF k).1⟩
  show (joint_second first second clearF clearG).toInclusion.firing _ = _
  rw [second_eq_swap_first, Inclusion.firing_comp, swap_jointResidual]

end NativeIterated

#print axioms NativeIterated.second_eq_swap_first
#print axioms NativeIterated.jointShift_swap
#print axioms NativeIterated.swap_jointResidual
#print axioms NativeIterated.cube_coherent

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
