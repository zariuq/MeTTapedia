import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullTelescopes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullControls

/-!
# The telescope diamond with three helpers: controls

The state is `X : U0` with no rows and no knowledge (`DependentFull.Controls.baseState`), in the
cumulative tower.

* `f` makes the dependent telescope `x : X, p : Id X x x` and the row `1 : p`;
* `g` makes the telescope `y : X` and the row `2 : y`.

**Positive control** (`firstAdmitted`, `secondAdmitted`, `independentAtJoint`, `exchanged_diamond`).
Read at the common frame `X, x, p, y`, the two firings are independent, and the diamond closes up to
the block exchange `X, x, p, y ≅ X, y, x, p`, which moves the block `x, p` past `y` while keeping the
dependency of `p` on `x`.

**Without the exchange the composites differ** (`composites_differ`): the row `1` is the variable
`p` in both, which is the second newest variable after `f` then `g` and the newest after `g` then
`f`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace DependentFull.TelescopeControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open DependentFull.Controls

/-! ## The telescopes and the firings -/

/-- `p : Id X x x` over `X : U0, x : X`. -/
def reflexive : TypeOver pairFrame :=
  ⟨.id (.var 1) (.var 0) (.var 0), .sort Tower.zero, .sort _,
    .idForm (Derivable.var 1) (.sort _) (Derivable.var 0) (Derivable.var 0)⟩

/-- The dependent two-helper telescope `x : X, p : Id X x x`. -/
def pathHelpers : Helpers base := .cons xType (.cons reflexive (.nil _))

/-- The one-helper telescope `y : X`. -/
def pointHelpers : Helpers base := .cons xType (.nil _)

/-- The row `p`, at `X, x, p`. -/
def pathRow : TotalTerm pathHelpers.frame :=
  ⟨reflexive.reindex (projectionHom pairFrame reflexive), newest pairFrame reflexive⟩

/-- The row `y`, at `X, y`. -/
def pointRow : TotalTerm pointHelpers.frame := ⟨xType.reindex (projectionHom base xType), newest base xType⟩

/-- `f`'s data: the row `1 : p`. -/
def fData : Natural setting.levels Nat pathHelpers.frame := ⟨[], [], [], [], [(1, Make.ofRow pathRow)], [], [], []⟩

/-- `g`'s data: the row `2 : y`. -/
def gData : Natural setting.levels Nat pointHelpers.frame := ⟨[], [], [], [], [(2, Make.ofRow pointRow)], [], [], []⟩

theorem firstAdmitted : (Natural.withHelpers (s := baseState) pathHelpers fData).Admits := by
  refine (Natural.admits_withHelpers _ _).mpr ?_
  refine ⟨⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, fun m member => ?_⟩,
      (Plain.enabled_iff _ _).mpr ⟨fun _ member => absurd member List.not_mem_nil,
        fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil,
        fun o member => ?_⟩,
      ⟨_, 𝟙 _, fun _ member => absurd member List.not_mem_nil⟩,
      fun _ _ _ => ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩⟩
  · obtain rfl := List.mem_singleton.mp member
    exact Make.ofRow_wellTyped _
  · obtain rfl := List.mem_singleton.mp member
    exact Finset.notMem_empty _

theorem secondAdmitted : (Natural.withHelpers (s := baseState) pointHelpers gData).Admits := by
  refine (Natural.admits_withHelpers _ _).mpr ?_
  refine ⟨⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, fun m member => ?_⟩,
      (Plain.enabled_iff _ _).mpr ⟨fun _ member => absurd member List.not_mem_nil,
        fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil,
        fun o member => ?_⟩,
      ⟨_, 𝟙 _, fun _ member => absurd member List.not_mem_nil⟩,
      fun _ _ _ => ⟨fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil⟩⟩
  · obtain rfl := List.mem_singleton.mp member
    exact Make.ofRow_wellTyped _
  · obtain rfl := List.mem_singleton.mp member
    exact Finset.notMem_empty _

/-! ## The positive control -/

/-- **Read at the common frame `X, x, p, y`, the two telescope firings are independent.** -/
theorem independentAtJoint :
    Independent (jointState (s := baseState) pathHelpers pointHelpers)
      (atJointTelescopes (s := baseState) fData gData).1 (atJointTelescopes (s := baseState) fData gData).2 where
  takes_apart := fun _ inside => absurd inside List.not_mem_nil
  left_keeps_reads := fun _ inside => absurd inside List.not_mem_nil
  right_keeps_reads := fun _ inside => absurd inside List.not_mem_nil
  made_apart := fun o one two => by
    obtain rfl := List.mem_singleton.mp one
    exact absurd (List.mem_singleton.mp two) (by decide)
  joint_solvable := ⟨_, 𝟙 _, fun _ member => absurd member List.not_mem_nil⟩
  left_unwritten := fun _ member => absurd member List.not_mem_nil
  right_unwritten := fun _ member => absurd member List.not_mem_nil

/-- **The diamond of the two telescope firings closes up to the block exchange.** -/
theorem exchanged_diamond :
    ∃ (afterFirst : (Natural.residualHelpers (s := baseState) fData gData firstAdmitted).Admits)
      (afterSecond : (Natural.residualHelpers (s := baseState) gData fData secondAdmitted).Admits),
      Local.AgreeAlong (levels := setting.levels) (exchange pathHelpers pointHelpers)
        ((Natural.residualHelpers (s := baseState) fData gData firstAdmitted).after afterFirst).toLocal
        ((Natural.residualHelpers (s := baseState) gData fData secondAdmitted).after afterSecond).toLocal :=
  telescope_diamond firstAdmitted secondAdmitted independentAtJoint

/-- The composites live at frames of four variables. -/
theorem joint_arity : (pointHelpers.reindex pathHelpers.weaken).frame.arity = 4 := rfl

/-- The row `1` after `f` then `g`: the second newest variable `p`. -/
theorem first_composite_row
    (afterFirst : (Natural.residualHelpers (s := baseState) fData gData firstAdmitted).Admits) :
    (((Natural.residualHelpers (s := baseState) fData gData firstAdmitted).after afterFirst).label 1).2.code =
      (Tm.var (1 : Fin 4) : Tm Tower.Head 4) := rfl

/-- The row `1` after `g` then `f`: the newest variable `p`. -/
theorem second_composite_row
    (afterSecond : (Natural.residualHelpers (s := baseState) gData fData secondAdmitted).Admits) :
    (((Natural.residualHelpers (s := baseState) gData fData secondAdmitted).after afterSecond).label 1).2.code =
      (Tm.var (0 : Fin 4) : Tm Tower.Head 4) := rfl

/-- **Without the exchange the two composites differ**: both have four variables, and they give the
row `1` different ones. -/
theorem composites_differ
    (afterFirst : (Natural.residualHelpers (s := baseState) fData gData firstAdmitted).Admits)
    (afterSecond : (Natural.residualHelpers (s := baseState) gData fData secondAdmitted).Admits) :
    (((Natural.residualHelpers (s := baseState) fData gData firstAdmitted).after afterFirst).label 1).2.code ≠
      (((Natural.residualHelpers (s := baseState) gData fData secondAdmitted).after afterSecond).label 1).2.code := by
  rw [first_composite_row afterFirst, second_composite_row afterSecond]
  exact fun same => absurd (congrArg Fin.val (Tm.var.inj same)) (by decide)

/-- **The exchange keeps the dependency**: `Id X x x` at the frame `X, y, x, p` (where `x` is the
variable `1`) read along the exchange is `Id X x x` at the frame `X, x, p, y` (where `x` is the
variable `2`); the variable `y` moves from position `2` to the newest position. -/
theorem exchange_keeps_dependency :
    subst (exchange pathHelpers pointHelpers).substitution (.id (.var 3) (.var 1) (.var 1) : Tm Tower.Head 4) =
      (.id (.var 3) (.var 2) (.var 2) : Tm Tower.Head 4) ∧
    subst (exchange pathHelpers pointHelpers).substitution (.var 2 : Tm Tower.Head 4) =
      (.var 0 : Tm Tower.Head 4) :=
  ⟨rfl, rfl⟩

end DependentFull.TelescopeControls

#print axioms DependentFull.TelescopeControls.firstAdmitted
#print axioms DependentFull.TelescopeControls.secondAdmitted
#print axioms DependentFull.TelescopeControls.independentAtJoint
#print axioms DependentFull.TelescopeControls.exchanged_diamond
#print axioms DependentFull.TelescopeControls.composites_differ
#print axioms DependentFull.TelescopeControls.exchange_keeps_dependency

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
