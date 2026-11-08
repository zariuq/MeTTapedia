import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullSwap
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullControls

/-!
# The helper diamond up to the swap: controls

The state is `X : U0` with no rows and no knowledge (`DependentFull.Controls.baseState`), in the
cumulative tower.

**Positive control** (`firstAdmitted`, `secondAdmitted`, `independentAtJoint`, `swapped_diamond`).
`f` makes a helper `x : X` and the row `1 : x`; `g` makes a helper `y : X` and the row `2 : y`. Read
at the common frame `X, x : X, y : X`, they are independent, and the diamond closes up to the swap.
Without the swap the composites differ (`composites_differ`): in the composite of `g` after `f` the
row `1` is the variable `x`, which is the second newest variable, while in the composite of `f` after
`g` it is the newest; the swap sends the one to the other (`swapped_diamond`).

**Negative control** (`refl_run_admitted`, `refl_no_swap`). After `f`, the firing `g₁` makes a helper
`y : Ground` and the row `3 : refl x` of type `Id X x x`. The run `f ; g₁` is admitted, and `g₁` is
the residual after `f` of no helper firing at the start: its made row's type mentions `x`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace DependentFull.SwapControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open DependentFull.Controls
open ContextualDependentParameterExchange (second context base swap)

/-! ## The firings -/

/-- The helper `x : X`, as a row at `X, x : X`. -/
def helperRow : TotalTerm pairFrame := ⟨xType.reindex (projectionHom base xType), newest base xType⟩

/-- Make the row `o : x` for the fresh helper. -/
def makeHelper (o : Nat) : Natural setting.levels Nat pairFrame :=
  ⟨[], [], [], [], [(o, Make.ofRow helperRow)], [], [], []⟩

theorem makeHelper_admitted (o : Nat) (present : Finset Nat) (fresh : o ∉ present) :
    (Natural.withHelper (s := ⟨base, [], present, fun _ => ⟨smallUniverse _, ⟨.var 0, Derivable.var 0⟩⟩⟩)
      xType (makeHelper o)).Admits := by
  refine (Natural.admits_withHelper _ _).mpr ?_
  refine ⟨⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, fun m member => ?_⟩,
      (Plain.enabled_iff _ _).mpr ⟨fun _ member => absurd member List.not_mem_nil,
        fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil,
        fun o' member => ?_⟩,
      ⟨_, 𝟙 _, fun _ member => absurd member List.not_mem_nil⟩,
      fun _ _ _ => ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩⟩
  · obtain rfl := List.mem_singleton.mp member
    exact Make.ofRow_wellTyped _
  · obtain rfl := List.mem_singleton.mp member
    exact fresh

/-- `f`: the helper `x : X` and the row `1 : x`. -/
abbrev fData : Natural setting.levels Nat pairFrame := makeHelper 1

/-- `g`: the helper `y : X` and the row `2 : y`. -/
abbrev gData : Natural setting.levels Nat pairFrame := makeHelper 2

theorem firstAdmitted : (Natural.withHelper (s := baseState) xType fData).Admits :=
  makeHelper_admitted 1 ∅ (Finset.notMem_empty 1)

theorem secondAdmitted : (Natural.withHelper (s := baseState) xType gData).Admits :=
  makeHelper_admitted 2 ∅ (Finset.notMem_empty 2)

/-! ## The positive control -/

/-- **Read at the common frame, the two helper firings are independent.** -/
theorem independentAtJoint :
    Independent (baseState.toLocal.move (base xType xType)) (atJoint (s := baseState) fData gData).1
      (atJoint (s := baseState) fData gData).2 where
  takes_apart := fun _ inside => absurd inside List.not_mem_nil
  left_keeps_reads := fun _ inside => absurd inside List.not_mem_nil
  right_keeps_reads := fun _ inside => absurd inside List.not_mem_nil
  made_apart := fun o one two => by
    obtain rfl := List.mem_singleton.mp one
    exact absurd (List.mem_singleton.mp two) (by decide)
  joint_solvable := ⟨_, 𝟙 _, fun _ member => absurd member List.not_mem_nil⟩
  left_unwritten := fun _ member => absurd member List.not_mem_nil
  right_unwritten := fun _ member => absurd member List.not_mem_nil

/-- **The diamond of the two helper firings closes up to the swap.** -/
theorem swapped_diamond :
    ∃ (afterFirst : (Natural.residualHelper (s := baseState) fData gData firstAdmitted).Admits)
      (afterSecond : (Natural.residualHelper (s := baseState) gData fData secondAdmitted).Admits),
      Local.AgreeAlong (levels := setting.levels) (swap xType xType)
        ((Natural.residualHelper (s := baseState) fData gData firstAdmitted).after afterFirst).toLocal
        ((Natural.residualHelper (s := baseState) gData fData secondAdmitted).after afterSecond).toLocal :=
  helper_diamond firstAdmitted secondAdmitted independentAtJoint

/-- The row `1` after `f` then `g`: the second newest variable. -/
theorem first_composite_row
    (afterFirst : (Natural.residualHelper (s := baseState) fData gData firstAdmitted).Admits) :
    (((Natural.residualHelper (s := baseState) fData gData firstAdmitted).after afterFirst).label 1).2.code =
      (Tm.var (1 : Fin 3) : Tm Tower.Head 3) := rfl

/-- The row `1` after `g` then `f`: the newest variable. -/
theorem second_composite_row
    (afterSecond : (Natural.residualHelper (s := baseState) gData fData secondAdmitted).Admits) :
    (((Natural.residualHelper (s := baseState) gData fData secondAdmitted).after afterSecond).label 1).2.code =
      (Tm.var (0 : Fin 3) : Tm Tower.Head 3) := rfl

/-- **Without the swap the two composites differ**: they live at the same frame `X, x : X, y : X`,
and give the row `1` different variables. -/
theorem composites_differ
    (afterFirst : (Natural.residualHelper (s := baseState) fData gData firstAdmitted).Admits)
    (afterSecond : (Natural.residualHelper (s := baseState) gData fData secondAdmitted).Admits) :
    (((Natural.residualHelper (s := baseState) fData gData firstAdmitted).after afterFirst).label 1).2.code ≠
      (((Natural.residualHelper (s := baseState) gData fData secondAdmitted).after afterSecond).label 1).2.code := by
  rw [first_composite_row afterFirst, second_composite_row afterSecond]
  exact fun same => absurd (congrArg Fin.val (Tm.var.inj same)) (by decide)

/-! ## The negative control -/

/-- `y : Ground`, over `X, x : X`. -/
abbrev groundHelper : TypeOver pairFrame := groundType _

/-- The frame `X, x : X, y : Ground`. -/
abbrev reflFrame : Context Tower.rules := extend pairFrame groundHelper

/-- The type `Id X x x` at `X, x : X, y : Ground`. -/
def reflType : TypeOver reflFrame :=
  ⟨.id (.var 2) (.var 1) (.var 1), .sort Tower.zero, .sort _,
    .idForm (Derivable.var 2) (.sort _) (Derivable.var 1) (Derivable.var 1)⟩

/-- `g₁`'s data: the row `3 : refl x` of type `Id X x x`. -/
def reflData : Natural setting.levels Nat reflFrame :=
  ⟨[], [], [], [], [(3, ⟨reflType, .refl (.var 1)⟩)], [], [], []⟩

/-- `g₁`: after `f`, make the helper `y : Ground` and the row `3 : refl x`. -/
abbrev reflFiring : Firing setting.levels ((Natural.withHelper (s := baseState) xType fData).after firstAdmitted) :=
  Natural.withHelper (s := (Natural.withHelper (s := baseState) xType fData).after firstAdmitted) groundHelper
    reflData

/-- **The run `f ; g₁` is admitted.** -/
theorem refl_run_admitted : reflFiring.Admits := by
  refine (Natural.admits_withHelper _ _).mpr ?_
  refine ⟨⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, fun m member => ?_⟩,
      (Plain.enabled_iff _ _).mpr ⟨fun _ member => absurd member List.not_mem_nil,
        fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil,
        fun o member => ?_⟩, ⟨_, 𝟙 _, fun _ member => absurd member List.not_mem_nil⟩,
      fun _ _ _ => ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩⟩
  · obtain rfl := List.mem_singleton.mp member
    exact .reflIntro (Derivable.var 1)
  · obtain rfl := List.mem_singleton.mp member
    decide

/-- **`g₁` has no swap**: it is the residual after `f` of no helper firing at the start, since its
made row's type `Id X x x` mentions `f`'s helper `x`. -/
theorem refl_no_swap :
    ∀ (B : TypeOver baseState.frame) (g : Natural setting.levels Nat (extend baseState.frame B)),
      Natural.residualHelper (s := baseState) fData g firstAdmitted ≠ reflFiring :=
  no_residual_of_mentions (s := baseState) fData firstAdmitted groundHelper reflData (.var 2)
    ⟨_, List.mem_singleton_self _, rfl⟩

end DependentFull.SwapControls

#print axioms DependentFull.SwapControls.firstAdmitted
#print axioms DependentFull.SwapControls.secondAdmitted
#print axioms DependentFull.SwapControls.independentAtJoint
#print axioms DependentFull.SwapControls.swapped_diamond
#print axioms DependentFull.SwapControls.composites_differ
#print axioms DependentFull.SwapControls.refl_run_admitted
#print axioms DependentFull.SwapControls.refl_no_swap

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
