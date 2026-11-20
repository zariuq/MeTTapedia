import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.Qualified
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.VectorFunction

/-!
# Controls for the qualification of the vectors package

**One row breaks it.** Adding the row `add zero b ⟶ zero` to the package overlaps addition's row
`add zero b ⟶ b`. The new row preserves types (both sides are numbers), yet the package is no longer
Church–Rosser: `add 0 1` reaches the two distinct normal forms `1` and `0`
(`overlap_not_churchRosser`), so the typed equality identifies `1` and `0` (`overlap_identifies`) and
no setting over the extended package is qualified (`overlap_not_qualified`). The field that fails is
the constructor presentation, and the syntactic check finds it: the extended table is rejected
(`overlap_check`) where the package's own table passes (`Vectors.vector_check`).

**The rigid package of the audit.** The package of rigid naturals and vectors that the consumer audit
programmed on has no computation at all. Its equation set is empty, so it is qualified, vacuously
(`rigid_qualified`): every field holds, the constructor presentation being the empty one. What it
lacks is not qualification but computation in types: its `add` runs only by firings, so `add 0 1 ≐ 1`
is refuted in its knowledge (`rigid_add_outside`).

Declaring its rows computing gives the step's own package with `add` and `append` in conversion. That
package has no normalization setting with its own roles (`declaredRigid_no_setting`): the field that
fails is the setting's root shape, which asks every row to inspect a constructor, while the package's
roles make `zero`, `succ`, `nil` and `cons` rigid. Making them constructors would need `vec`, a
family `nat → U0`, to be an inductive type of the model, whose inductive types are nullary: the
missing piece is an inductive-family case of the logical relation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Vectors

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open AlgebraicSchema AlgebraicParallel ConversionCoherence
open ConstructorSystem (ConstructorPresentation System)
open TowerNumbersModel (num zero succ numRec ctors u)
open TowerVectorsModel (unit tt add U0 numC zeroC succC unitC ttC vecC addC)

variable (lv : LevelExpr Nat)

/-! ## An overlap with addition -/

section Overlap

/-- The extra row `add zero b ⟶ zero`. -/
inductive DropStep : {n : Nat} → Tower.Tm n → Tower.Tm n → Prop
  | drop {n : Nat} (b : Tower.Tm n) : DropStep (addC zeroC b) zeroC

/-- The extra row, as a root computation. -/
def dropComputation : RootComputation Tower.Head where
  step l r := DropStep l r
  rename := by
    intro n m ρ left right h
    exact match h with
      | .drop b => DropStep.drop (Presentation.rename ρ b)
  substitute := by
    intro n m σ left right h
    exact match h with
      | .drop b => DropStep.drop (subst σ b)

/-- **The package with the overlapping row.** -/
abbrev overlapRules : Rules Tower.Head := declare (TowerVectorsModel.rules lv) dropComputation

/-- The number `1`. -/
abbrev one {n : Nat} : Tower.Tm n := succC zeroC

/-- A root step of the package starts at a spine headed by a defined constant. -/
theorem no_root_of_undefined {n : Nat} {t t' : Tower.Tm n} {c : DeclName} {count : Nat}
    (head : ConstructorSystem.spineHead t = some (c, count)) (undefined : vectorDefined c = false)
    (step : (TowerVectorsModel.rules lv).computation.step t t') : False := by
  obtain ⟨name, k, defined, found⟩ := ConstructorSystem.computation_head (vectorConstructors lv) step
  rw [head] at found
  cases found
  change vectorDefined c = true at defined
  rw [undefined] at defined
  cases defined

theorem overlap_zero_normal : ConstructorSystem.Normal (overlapRules lv) (zeroC : Tower.Tm 0) := by
  intro target step
  cases step with
  | root h =>
      rcases h with h | h
      · exact no_root_of_undefined lv rfl (by decide) h
      · cases h

theorem overlap_one_normal : ConstructorSystem.Normal (overlapRules lv) (one : Tower.Tm 0) := by
  intro target step
  cases step with
  | root h =>
      rcases h with h | h
      · exact no_root_of_undefined lv rfl (by decide) h
      · cases h
  | congAppFun inner =>
      cases inner with
      | root h =>
          rcases h with h | h
          · exact no_root_of_undefined lv rfl (by decide) h
          · cases h
  | congAppArg inner => exact overlap_zero_normal lv inner

/-- `add 0 1 ⟶ 1`, by addition's row. -/
theorem overlap_keep : StepStar (overlapRules lv) (addC zeroC one : Tower.Tm 0) one :=
  .single (.root (Or.inl (TowerVectorsModel.add_zero_step lv one)))

/-- `add 0 1 ⟶ 0`, by the extra row. -/
theorem overlap_drop : StepStar (overlapRules lv) (addC zeroC one : Tower.Tm 0) zeroC :=
  .single (.root (declare_step (DropStep.drop one)))

/-- **The extended package is not Church–Rosser**: `1` and `0` are convertible distinct normal forms. -/
theorem overlap_not_churchRosser : ¬ ChurchRosser (overlapRules lv) := by
  intro church
  have conversion : Conv (overlapRules lv).headEq (one : Tower.Tm 0) zeroC (overlapRules lv).computation :=
    .trans _ _ _ (.symm _ _ (conv_of_stepStar (overlap_keep lv))) (conv_of_stepStar (overlap_drop lv))
  obtain ⟨common, left, right⟩ := church conversion
  have toOne := ConstructorSystem.Normal.stepStar (overlap_one_normal lv) left
  have toZero := ConstructorSystem.Normal.stepStar (overlap_zero_normal lv) right
  exact absurd (toOne.symm.trans toZero) (by decide)

/-- **The extra row preserves types, and the typed equality of the extended package identifies `1`
and `0`.** -/
theorem overlap_identifies :
    Typed (overlapRules lv) .nil (addC zeroC one) numC ∧ Typed (overlapRules lv) .nil zeroC numC ∧
      Equal (overlapRules lv) .nil one zeroC numC := by
  have D := TowerVectorsModel.vecDeclared_rules lv
  have zeroTyped : Typed (overlapRules lv) .nil zeroC numC := typed_declare dropComputation D.zero_typed
  have oneTyped : Typed (overlapRules lv) .nil one numC :=
    typed_declare dropComputation (D.succ_typed D.zero_typed)
  have addTyped : Typed (overlapRules lv) .nil (addC zeroC one) numC :=
    typed_declare dropComputation
      (TowerVectorsPrograms.add_typed lv D.zero_typed (D.succ_typed D.zero_typed))
  refine ⟨addTyped, zeroTyped, ?_⟩
  exact .trans (.symm (.root (Or.inl (TowerVectorsModel.add_zero_step lv one)) addTyped oneTyped))
    (.root (declare_step (DropStep.drop one)) addTyped zeroTyped)

/-- **No setting over the extended package is qualified.** -/
theorem overlap_not_qualified {L : Type} [LevelOrder L] (S : Setting Tower.Head L)
    (same : S.R = overlapRules lv) : ¬ Qualified S := by
  intro q
  apply overlap_not_churchRosser lv
  rw [← same]
  exact q.churchRosser

/-- The extra row, as a row of the table. -/
def overlapRow : Σ a : Nat, Tower.Tm a × Tower.Tm a := ⟨1, (addC zeroC (.var 0), zeroC)⟩

/-- **The syntactic check rejects the extended table**: the new left side unifies with addition's
row at `zero`. -/
theorem overlap_check :
    DeclarationCheck.checkTable vectorDefined vectorArity (vectorEquations ++ [overlapRow]) = false := by
  decide

end Overlap

/-! ## The rigid package of the audit -/

section Rigid

open ProgrammingOnTheStep ContextualDependentEta

/-- The empty equation set. -/
def emptySystem : System Tower.Head where
  schema := fun _ _ => False
  defined _ := False
  arity _ := 0
  left := fun rule => rule.elim
  linear := fun rule => rule.elim
  covered := fun rule => rule.elim
  determined := fun rule => rule.elim

/-- **The rigid package presents its empty computation.** -/
def rigidConstructors : ConstructorPresentation VectorPackage.rules where
  presentation :=
    { schema := fun _ _ => False
      sound := fun rule => rule.elim
      cover := fun step => (step : False).elim }
  system := emptySystem
  same _ _ := Iff.rfl
  symmetric := DeclarationCheck.headSymm

/-- Head equality of the rigid package is decided. -/
theorem rigid_decideHeads (h h' : Tower.Head) :
    HeadSame VectorPackage.rules h h' ∨ ¬ HeadSame VectorPackage.rules h h' := by
  rcases Decidable.em (Tower.HeadEq h h') with same | different
  · exact .inl (.inr same)
  · rcases Decidable.em (h = h') with equal | unequal
    · exact .inl (.inl equal)
    · exact .inr fun same => same.elim unequal different

/-- **The audit's rigid package is qualified, vacuously**: its equation set is empty. -/
theorem rigid_qualified : Qualified VectorPackage.setting where
  laws := VectorPackage.laws
  constructors := ⟨rigidConstructors⟩
  constants := VectorPackage.constants
  roots := VectorPackage.roots
  heads := VectorPackage.heads
  algebra := VectorPackage.algebra
  algorithmicConstants := VectorPackage.algorithmicConstants
  decideHeads := rigid_decideHeads

/-- **... and its addition is outside its equation set**: `add 0 1 ≐ 1` is refuted in its knowledge. -/
theorem rigid_add_outside :
    ¬ (frames VectorPackage.levels).Solvable VectorPrograms.addStore :=
  VectorPrograms.add_not_in_knowledge

/-- `add 0 0 ⟶ 0` in the rigid package with its rows declared computing. -/
theorem declaredRigid_step :
    VectorFunction.arules.computation.step
      (VectorPackage.addC VectorPackage.zeroC VectorPackage.zeroC : Tower.Tm 0) VectorPackage.zeroC :=
  declare_step (VectorFunction.VecStep.addZero VectorPackage.zeroC)

/-- **The rigid package with its rows declared computing has no normalization setting with its own
roles**: the setting's root shape asks the row `add 0 b ⟶ b` to inspect a constructor at a computing
head, while the package's roles make every constant rigid. -/
theorem declaredRigid_no_setting {L : Type} [LevelOrder L] (S : Setting Tower.Head L)
    (same : S.R = VectorFunction.arules) (ownRoles : S.roles = VectorPackage.roles) : False := by
  have step : S.R.computation.step
      (VectorPackage.addC VectorPackage.zeroC VectorPackage.zeroC : Tower.Tm 0) VectorPackage.zeroC := by
    rw [same]
    exact declaredRigid_step
  obtain ⟨c, arity, scrutinee, args, role, -, -, -⟩ := S.shape.spine step
  rw [ownRoles] at role
  cases role

end Rigid

end NativeTypesOnTheStep.Computing.Vectors

#print axioms NativeTypesOnTheStep.Computing.Vectors.no_root_of_undefined
#print axioms NativeTypesOnTheStep.Computing.Vectors.overlap_zero_normal
#print axioms NativeTypesOnTheStep.Computing.Vectors.overlap_one_normal
#print axioms NativeTypesOnTheStep.Computing.Vectors.overlap_not_churchRosser
#print axioms NativeTypesOnTheStep.Computing.Vectors.overlap_identifies
#print axioms NativeTypesOnTheStep.Computing.Vectors.overlap_not_qualified
#print axioms NativeTypesOnTheStep.Computing.Vectors.overlap_check
#print axioms NativeTypesOnTheStep.Computing.Vectors.rigidConstructors
#print axioms NativeTypesOnTheStep.Computing.Vectors.rigid_qualified
#print axioms NativeTypesOnTheStep.Computing.Vectors.rigid_add_outside
#print axioms NativeTypesOnTheStep.Computing.Vectors.declaredRigid_step
#print axioms NativeTypesOnTheStep.Computing.Vectors.declaredRigid_no_setting

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
