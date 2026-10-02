import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectCaseTrees
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectPreservation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.CaseTreeTyping
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ConstantDeclarations

/-!
# The case trees of the object package, typed

`ObjectCaseTrees` extends the object package by the case trees of `max`,
`half` and `pick`; that extension computes by the trees and declares no type
for the three names. Here the three names are declared: `max` and `pick` at
`num → num → num`, `half` at `num → num` (`treeRules`).

Declared types do not enter reduction, so the typed package is Church–Rosser
and has root shape under the roles of the extension
(`treeRules_churchRosser`, `treeRules_rootShape`).

Each of the three constants computes by a typed case tree (`max_declares`,
`half_declares`, `pick_declares`). The leaves are typed in the stage that
declares the numbers, their constructors and the three names and computes
nothing (`treeStage`, `treeStage_no_step`); the typed package contains it
(`treeStage_sub`).

Positive example. The deepest equation of each tree is a typed definitional
equality of the typed package, for all arguments typed at `num` in any
context: `max (suc a) (suc b)` is equal to `suc (max a b)`
(`max_suc_suc_equal`), `half (suc (suc a))` to `suc (half a)`
(`half_suc_suc_equal`), and `pick (suc a) (suc b)` to the numeral three
(`pick_suc_suc_equal`). The arguments may be any terms of the object package,
codes included; at closed numerals, `max 1 1` is equal to `suc (max 0 0)`
(`max_one_one_equal`).

Subject reduction is conditional. Given the facts about the weak-head forms
of the typed package's types, a root step of one of the three trees from a
typed term gives a term of the same type (`tree_step_preserves`), and so does
a root step of the executable package (`executable_step_preserves`). Those
facts are a hypothesis: they are known for the object package without the
trees, and not for the typed package. The decodings of codes, the third kind
of root step, are not treated: their preservation in the object package rests
on an inversion of typed code spines proved for that package only.

Negative example. The tree `bad zero = junk; bad (suc n) = n`, with `junk` a
constant that no package here declares, meets the leaf conditions, covers and
is scoped; `bad` has the role of its tree and is declared at `num → num`. Only
the typing of the first leaf fails (`badTree_not_leavesTyped`), and with it
subject reduction: `bad zero` is typed at `num` and steps to `junk`, which has
no type (`bad_not_preserving`). So the typing of the leaves cannot be dropped
from the declaration. An undeclared constant has no type by inversion alone,
so this control needs no model.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
namespace CodeModel
namespace ObjectCaseTrees

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Normalization.CaseTreeExtension
open Presentation.ConversionCoherence (ChurchRosser)
open TelescopeAbstraction (closeType)
open Package (U0 numT)

/-! ## The declared types -/

/-- The declared types of the three names: `max, pick : num → num → num`, the
type of addition, and `half : num → num`. -/
def treeTypes (name : DeclName) : Option (Tower.Tm 0) :=
  if name = maxN ∨ name = pickN then some addType
  else if name = halfN then some (.pi numT numT)
  else none

/-- Only the three names are listed. -/
theorem treeTypes_listed {name : DeclName} {type : Tower.Tm 0}
    (listed : treeTypes name = some type) : name = maxN ∨ name = halfN ∨ name = pickN := by
  by_cases first : name = maxN ∨ name = pickN
  · exact first.elim .inl fun same => .inr (.inr same)
  · by_cases second : name = halfN
    · exact .inr (.inl second)
    · unfold treeTypes at listed
      rw [if_neg first, if_neg second] at listed
      cases listed

/-- The declaring stage: the numbers, their constructors and the three names
at their types, with no computation. The leaves of the trees are typed
here. -/
def treeStage : Rules Tower.Head := withConstants ctorStage treeTypes

/-- **The typed package**: the object package extended by the three trees,
with the three names declared at their types. -/
def treeRules : Rules Tower.Head := withConstants extended treeTypes

/-- The roles of the typed package: each of the three names computes by its
tree, and every other name keeps its role in the object package. -/
abbrev treeRoles : Roles Tower.Head := extendRoles objectRoles definitions

/-! ## The typed package contains its parts -/

/-- The stage of the numbers declares none of the three names. -/
theorem ctorStage_fresh {name : DeclName} {type : Tower.Tm 0}
    (listed : treeTypes name = some type) : ctorStage.constantType name = none := by
  rcases treeTypes_listed listed with rfl | rfl | rfl
  · exact stage_undeclared (by decide)
  · exact stage_undeclared (by decide)
  · exact stage_undeclared (by decide)

/-- The extended object package declares none of the three names. -/
theorem extended_fresh {name : DeclName} {type : Tower.Tm 0}
    (listed : treeTypes name = some type) : extended.constantType name = none := by
  rcases treeTypes_listed listed with rfl | rfl | rfl <;> decide

/-- The declaring stage contains the stage of the numbers. -/
theorem ctorStage_sub_treeStage : RulesSub ctorStage treeStage :=
  withConstants_sub ctorStage_fresh

/-- A package is contained in its extension by case trees: the extension adds
root steps only. -/
theorem extend_sub {Head : Type} (base : Rules Head) (defs : List (CaseTreeDefinition Head)) :
    RulesSub base (extend base defs) :=
  ⟨id, id, id, id, id, id, Or.inl⟩

/-- The extension by the trees contains the object package. -/
theorem objectRules_sub_extended : RulesSub objectRules extended :=
  extend_sub objectRules definitions

/-- The typed package contains the extension by the trees. -/
theorem extended_sub_treeRules : RulesSub extended treeRules :=
  withConstants_sub extended_fresh

/-- The typed package contains the executable package. -/
theorem rules_sub_treeRules : RulesSub rules treeRules :=
  (ConvRules.rules_sub_objectRules.trans objectRules_sub_extended).trans extended_sub_treeRules

/-- The typed package contains the declaring stage. -/
theorem treeStage_sub : RulesSub treeStage treeRules :=
  withConstants_mono
    (((stage_sub_rules _).trans ConvRules.rules_sub_objectRules).trans objectRules_sub_extended)

/-- The declaring stage computes nothing: none of its names has a
computation. -/
theorem treeStage_no_step {n : Nat} {t u : Tower.Tm n} : ¬ treeStage.computation.step t u := by
  intro step
  obtain ⟨entry, mem, -⟩ := RootComputation.unionAll_step step
  obtain ⟨listed, allowed⟩ := List.mem_filter.mp mem
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at listed
  rcases listed with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact absurd allowed (by decide)

/-! ## Reduction is that of the extension -/

/-- **The typed package is Church–Rosser.** -/
theorem treeRules_churchRosser : ChurchRosser treeRules :=
  churchRosser_withConstants.mpr extended_churchRosser

/-- **The typed package has root shape**: each of the three names computes by
its tree, and every other name keeps its role in the object package. -/
theorem treeRules_rootShape : RootShape treeRules treeRoles :=
  rootShape_withConstants.mpr extended_rootShape

/-- The universe levels of the typed package: those of the object package. -/
def treeLevels : LevelModel treeRules ℕ where
  level := ConvRules.objectLevels.level
  successor := ConvRules.objectLevels.successor
  universe_typing := ConvRules.objectLevels.universe_typing
  ground_typing := ConvRules.objectLevels.ground_typing
  cumulative_universe := ConvRules.objectLevels.cumulative_universe
  headEq_level := ConvRules.objectLevels.headEq_level
  join_level := ConvRules.objectLevels.join_level
  join_exists := ConvRules.objectLevels.join_exists
  join_upper := ConvRules.objectLevels.join_upper
  cumulative_refl := ConvRules.objectLevels.cumulative_refl
  headEq_symm := ConvRules.objectLevels.headEq_symm
  headEq_trans := ConvRules.objectLevels.headEq_trans
  universe_decided := ConvRules.objectLevels.universe_decided

/-- The normalization setting of the typed package, at typed equality. -/
def treeSetting : Setting Tower.Head ℕ where
  R := treeRules
  roles := treeRoles
  E := declarative treeRules
  levels := treeLevels
  shape := treeRules_rootShape
  constructors := extend_declared

/-! ## The declarations of the stage -/

/-- `num` is declared in the lowest universe. -/
theorem declared_num : treeStage.constantType numN = some U0 := rfl

/-- `zero` is declared at its constructor type. -/
theorem declared_zero : treeStage.constantType zeroN = some (ctorType numN []) := rfl

/-- `suc` is declared at its constructor type. -/
theorem declared_suc : treeStage.constantType sucN = some (ctorType numN [.recursive]) := rfl

/-- `max` is declared at `num → num → num`. -/
theorem declared_max :
    treeStage.constantType maxN = some (closeType (ofEntries addEntries 2) numT) :=
  rfl

/-- `half` is declared at `num → num`. -/
theorem declared_half :
    treeStage.constantType halfN = some (closeType (ofEntries addEntries 1) numT) :=
  rfl

/-- `pick` is declared at `num → num → num`. -/
theorem declared_pick :
    treeStage.constantType pickN = some (closeType (ofEntries addEntries 2) numT) :=
  rfl

/-! ## Typings at the declaring stage -/

section Typing

variable {n : Nat} {Γ : Tower.Ctx n}

/-- The numbers are a type of the lowest universe. -/
theorem numT_stage : Typed treeStage Γ numT U0 :=
  Derivable.mono ctorStage_sub_treeStage (numT_typed List.mem_cons_self)

/-- `num → num` is a type. -/
theorem unary_formed : Typed treeStage .nil (.pi numT numT) U0 :=
  Derivable.mono ctorStage_sub_treeStage
    (piT (numT_typed List.mem_cons_self) (numT_typed List.mem_cons_self))

/-- `num → num → num` is a type. -/
theorem binary_formed : Typed treeStage .nil (.pi numT (.pi numT numT)) U0 :=
  Derivable.mono ctorStage_sub_treeStage (addType_typed List.mem_cons_self)

/-- `zero` is a number. -/
theorem zero_stage : Typed treeStage Γ (.const zeroN) numT :=
  Derivable.mono ctorStage_sub_treeStage
    (zero_typed List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self))

/-- `suc` is a function on the numbers. -/
theorem suc_stage : Typed treeStage Γ (.const sucN) (.pi numT numT) :=
  Derivable.mono ctorStage_sub_treeStage
    (suc_typed List.mem_cons_self
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))

/-- `max` at its declared type. -/
theorem max_stage : Typed treeStage Γ (.const maxN) (.pi numT (.pi numT numT)) :=
  .const declared_max binary_formed (LevelTower.IsUniverse.sort _)

/-- `half` at its declared type. -/
theorem half_stage : Typed treeStage Γ (.const halfN) (.pi numT numT) :=
  .const declared_half unary_formed (LevelTower.IsUniverse.sort _)

/-- `pick` at its declared type. -/
theorem pick_stage : Typed treeStage Γ (.const pickN) (.pi numT (.pi numT numT)) :=
  .const declared_pick binary_formed (LevelTower.IsUniverse.sort _)

/-- Every numeral is a number. -/
theorem numeral_stage : ∀ k : Nat, Typed treeStage Γ (numeral k) numT
  | 0 => zero_stage
  | k + 1 => .appElim suc_stage (numeral_stage k)

end Typing

/-- A variable of a context of numbers is a number. -/
theorem numVar_stage {k : Nat} (i : Fin k) :
    Typed treeStage (ofEntries addEntries k) (.var i) numT := by
  have typing := Derivable.var (R := treeStage) (Γ := ofEntries addEntries k) i
  have lookup : Ctx.lookup (ofEntries addEntries k) i = numT :=
    ofEntries_lookup_closed (fun _ => numT) k i
  rw [lookup] at typing
  exact typing

/-- The constructor type of `zero` is a type. -/
theorem zero_formed :
    ∃ w, treeStage.isUniverse w ∧ Typed treeStage .nil (ctorType numN []) (.head w) :=
  ⟨_, LevelTower.IsUniverse.sort _, numT_stage⟩

/-- The constructor type of `suc` is a type. -/
theorem suc_formed :
    ∃ w, treeStage.isUniverse w ∧
      Typed treeStage .nil (ctorType numN [.recursive]) (.head w) :=
  ⟨_, LevelTower.IsUniverse.sort _, unary_formed⟩

/-! ## The three trees are typed -/

/-- The leaf of `max` under `suc`, `suc`: `suc (max x y)` is a number in the
context `x : num, y : num`. -/
theorem max_leaf_suc_suc :
    Typed treeStage (ofEntries addEntries 2)
      (.app (.const sucN) (appSpine (.const maxN) [.var 1, .var 0])) numT :=
  .appElim suc_stage
    (.appElim (.appElim max_stage (numVar_stage (k := 2) 1)) (numVar_stage (k := 2) 0))

/-- `max` is typed as a case tree: every leaf is a number in its context. -/
theorem max_leavesTyped :
    maxTree.LeavesTyped treeStage treeRoles (ofEntries addEntries 2) numT :=
  CaseTree.LeavesTyped.split (s := 0) (d := 1) (e := addEntries) (A := numT) rfl extend_num
    (.cons declared_zero zero_formed (.leaf (numVar_stage (k := 1) 0))
      (.cons declared_suc suc_formed
        (CaseTree.LeavesTyped.split (s := 1) (d := 0) (e := addEntries) (A := numT) rfl
          extend_num
          (.cons declared_zero zero_formed
            (.leaf (.appElim suc_stage (numVar_stage (k := 1) 0)))
            (.cons declared_suc suc_formed (.leaf max_leaf_suc_suc) .nil)))
        .nil))

/-- The leaf of `half` under `suc (suc _)`: `suc (half x)` is a number in the
context `x : num`. -/
theorem half_leaf_suc_suc :
    Typed treeStage (ofEntries addEntries 1)
      (.app (.const sucN) (appSpine (.const halfN) [.var 0])) numT :=
  .appElim suc_stage (.appElim half_stage (numVar_stage (k := 1) 0))

/-- `half` is typed as a case tree: every leaf is a number in its context. -/
theorem half_leavesTyped :
    halfTree.LeavesTyped treeStage treeRoles (ofEntries addEntries 1) numT :=
  CaseTree.LeavesTyped.split (s := 0) (d := 0) (e := addEntries) (A := numT) rfl extend_num
    (.cons declared_zero zero_formed (.leaf zero_stage)
      (.cons declared_suc suc_formed
        (CaseTree.LeavesTyped.split (s := 0) (d := 0) (e := addEntries) (A := numT) rfl
          extend_num
          (.cons declared_zero zero_formed (.leaf zero_stage)
            (.cons declared_suc suc_formed (.leaf half_leaf_suc_suc) .nil)))
        .nil))

/-- `pick` is typed as a case tree: every leaf is a numeral. -/
theorem pick_leavesTyped :
    pickTree.LeavesTyped treeStage treeRoles (ofEntries addEntries 2) numT :=
  CaseTree.LeavesTyped.split (s := 0) (d := 1) (e := addEntries) (A := numT) rfl extend_num
    (.cons declared_zero zero_formed (.leaf (numeral_stage 1))
      (.cons declared_suc suc_formed
        (CaseTree.LeavesTyped.split (s := 1) (d := 0) (e := addEntries) (A := numT) rfl
          extend_num
          (.cons declared_zero zero_formed (.leaf (numeral_stage 2))
            (.cons declared_suc suc_formed (.leaf (numeral_stage 3)) .nil)))
        .nil))

/-! ## The three declarations -/

/-- **`max : num → num → num` computes by its typed case tree** in the typed
package. -/
theorem max_declares :
    DeclaresCaseTree treeSetting treeStage maxN (ofEntries addEntries 2) numT maxTree where
  role := extendRoles_tree (baseRoles := objectRoles) (d := maxDef) leafConditions.names
    List.mem_cons_self
  sub₁ := treeStage_sub
  declared := declared_max
  typed := ⟨_, LevelTower.IsUniverse.sort _, binary_formed⟩
  leaves := max_leavesTyped
  steps := fun step => Or.inr ⟨maxDef, List.mem_cons_self, step⟩

/-- **`half : num → num` computes by its typed case tree** in the typed
package. -/
theorem half_declares :
    DeclaresCaseTree treeSetting treeStage halfN (ofEntries addEntries 1) numT halfTree where
  role := extendRoles_tree (baseRoles := objectRoles) (d := halfDef) leafConditions.names
    (List.mem_cons_of_mem _ List.mem_cons_self)
  sub₁ := treeStage_sub
  declared := declared_half
  typed := ⟨_, LevelTower.IsUniverse.sort _, unary_formed⟩
  leaves := half_leavesTyped
  steps := fun step => Or.inr ⟨halfDef, List.mem_cons_of_mem _ List.mem_cons_self, step⟩

/-- **`pick : num → num → num` computes by its typed case tree** in the typed
package. -/
theorem pick_declares :
    DeclaresCaseTree treeSetting treeStage pickN (ofEntries addEntries 2) numT pickTree where
  role := extendRoles_tree (baseRoles := objectRoles) (d := pickDef) leafConditions.names
    (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  sub₁ := treeStage_sub
  declared := declared_pick
  typed := ⟨_, LevelTower.IsUniverse.sort _, binary_formed⟩
  leaves := pick_leavesTyped
  steps := fun step =>
    Or.inr ⟨pickDef, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self), step⟩

/-! ## Leaf equations -/

section Equations

variable {n : Nat} {Γ : Tower.Ctx n}

/-- **The third equation of `max` is a typed definitional equality** of the
typed package: `max (suc a) (suc b)` is equal to `suc (max a b)` at `num`, for
all `a` and `b` typed at `num`. -/
theorem max_suc_suc_equal {a b : Tower.Tm n} (ha : Typed treeRules Γ a numT)
    (hb : Typed treeRules Γ b numT) :
    Equal treeRules Γ (appSpine (.const maxN) [.app (.const sucN) a, .app (.const sucN) b])
      (.app (.const sucN) (appSpine (.const maxN) [a, b])) numT := by
  have leaf : maxTree.TypedLeaf treeStage (ofEntries addEntries 2) numT
      (ofEntries addEntries 2) _ (.app (.const sucN) (appSpine (.const maxN) [.var 1, .var 0])) :=
    CaseTree.TypedLeaf.split (s := 0) (d := 1) (e := addEntries) (A := numT) (c := sucN)
      (fields := [.recursive]) rfl rfl declared_suc suc_formed
      (CaseTree.TypedLeaf.split (s := 1) (d := 0) (e := addEntries) (A := numT) (c := sucN)
        (fields := [.recursive]) rfl rfl declared_suc suc_formed (.leaf max_leaf_suc_suc))
  have typed : SubstMor treeRules (ofEntries addEntries 2) Γ
      (consSub b (consSub a fun i => i.elim0)) :=
    SubstMor.cons (SubstMor.cons (fun i => i.elim0) ha) hb
  exact max_declares.leaf_equation leaf typed

/-- **The third equation of `half` is a typed definitional equality** of the
typed package: `half (suc (suc a))` is equal to `suc (half a)` at `num`, for
every `a` typed at `num`. -/
theorem half_suc_suc_equal {a : Tower.Tm n} (ha : Typed treeRules Γ a numT) :
    Equal treeRules Γ (appSpine (.const halfN) [.app (.const sucN) (.app (.const sucN) a)])
      (.app (.const sucN) (appSpine (.const halfN) [a])) numT := by
  have leaf : halfTree.TypedLeaf treeStage (ofEntries addEntries 1) numT
      (ofEntries addEntries 1) _ (.app (.const sucN) (appSpine (.const halfN) [.var 0])) :=
    CaseTree.TypedLeaf.split (s := 0) (d := 0) (e := addEntries) (A := numT) (c := sucN)
      (fields := [.recursive]) rfl rfl declared_suc suc_formed
      (CaseTree.TypedLeaf.split (s := 0) (d := 0) (e := addEntries) (A := numT) (c := sucN)
        (fields := [.recursive]) rfl rfl declared_suc suc_formed (.leaf half_leaf_suc_suc))
  have typed : SubstMor treeRules (ofEntries addEntries 1) Γ (consSub a fun i => i.elim0) :=
    SubstMor.cons (fun i => i.elim0) ha
  exact half_declares.leaf_equation leaf typed

/-- **The third equation of `pick` is a typed definitional equality** of the
typed package: `pick (suc a) (suc b)` is equal to the numeral three at `num`,
for all `a` and `b` typed at `num`. -/
theorem pick_suc_suc_equal {a b : Tower.Tm n} (ha : Typed treeRules Γ a numT)
    (hb : Typed treeRules Γ b numT) :
    Equal treeRules Γ (appSpine (.const pickN) [.app (.const sucN) a, .app (.const sucN) b])
      (numeral 3) numT := by
  have leaf : pickTree.TypedLeaf treeStage (ofEntries addEntries 2) numT
      (ofEntries addEntries 2) _ (numeral 3) :=
    CaseTree.TypedLeaf.split (s := 0) (d := 1) (e := addEntries) (A := numT) (c := sucN)
      (fields := [.recursive]) rfl rfl declared_suc suc_formed
      (CaseTree.TypedLeaf.split (s := 1) (d := 0) (e := addEntries) (A := numT) (c := sucN)
        (fields := [.recursive]) rfl rfl declared_suc suc_formed (.leaf (numeral_stage 3)))
  have typed : SubstMor treeRules (ofEntries addEntries 2) Γ
      (consSub b (consSub a fun i => i.elim0)) :=
    SubstMor.cons (SubstMor.cons (fun i => i.elim0) ha) hb
  exact pick_declares.leaf_equation leaf typed

end Equations

/-- The equation of `max` at closed numerals: `max 1 1` is equal to
`suc (max 0 0)` at `num`, in the empty context. -/
theorem max_one_one_equal :
    Equal treeRules .nil (appSpine (.const maxN) [numeral 1, numeral 1])
      (.app (.const sucN) (appSpine (.const maxN) [numeral 0, numeral 0])) numT :=
  max_suc_suc_equal (Derivable.mono treeStage_sub zero_stage)
    (Derivable.mono treeStage_sub zero_stage)

/-! ## Subject reduction, given the facts about weak-head forms -/

section SubjectReduction

variable (facts : FormFacts treeRules treeRoles) {n : Nat} {Γ : Tower.Ctx n}
include facts

/-- **Given the facts about the weak-head forms of the typed package's types,
a root step of one of the three trees preserves typing.** -/
theorem tree_step_preserves {t u A : Tower.Tm n} (formed : CtxFormed treeRules Γ)
    (step : (caseTreeComputation definitions).step t u) (typing : Typed treeRules Γ t A) :
    Typed treeRules Γ u A := by
  obtain ⟨d, mem, treeStep⟩ := step
  simp only [definitions, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl
  · exact max_declares.step_preserves (S := treeSetting) facts (RulesSub.refl _) formed treeStep
      typing
  · exact half_declares.step_preserves (S := treeSetting) facts (RulesSub.refl _) formed treeStep
      typing
  · exact pick_declares.step_preserves (S := treeSetting) facts (RulesSub.refl _) formed treeStep
      typing

/-- Given the same facts, a root step of the executable package preserves
typing in the typed package. -/
theorem executable_step_preserves {t u A : Tower.Tm n} (formed : CtxFormed treeRules Γ)
    (step : rules.computation.step t u) (typing : Typed treeRules Γ t A) :
    Typed treeRules Γ u A :=
  roots_in (S := treeSetting) facts rules_sub_treeRules formed step typing

end SubjectReduction

/-! ## An ill-typed leaf -/

/-- The constant of the negative control. -/
def badN : DeclName := .mkSimple "bad"

/-- A constant that no package here declares. -/
def junkN : DeclName := .mkSimple "junk"

/-- `bad zero = junk`, `bad (suc n) = n`. -/
def badTree : CaseTree Tower.Head :=
  .split 0 numN (.cons zeroN 0 (.leaf 0 (.const junkN)) (.cons sucN 1 (.leaf 1 (.var 0)) .nil))

/-- The definition of the control. -/
def badDef : CaseTreeDefinition Tower.Head := ⟨badN, 1, badTree⟩

/-- The declared type of the control: `bad : num → num`. -/
def badTypes (name : DeclName) : Option (Tower.Tm 0) :=
  if name = badN then some (.pi numT numT) else none

/-- The object package extended by the tree of `bad`, with `bad` declared at
`num → num`. -/
def badRules : Rules Tower.Head := withConstants (extend objectRules [badDef]) badTypes

/-- The control is a case-tree definition: one name, positive arity, a scoped
tree, and splits on `zero` and `suc` only. -/
theorem bad_conditions : LeafConditions [badDef] where
  names := List.nodup_singleton _
  arity_pos := by decide
  inScope := by
    intro d mem
    obtain rfl := List.mem_singleton.mp mem
    exact .split Nat.zero_lt_one (.cons (.leaf _) (.cons (.leaf _) .nil))
  constructors := by decide

/-- The tree of the control covers, under the roles of its extension. -/
theorem badTree_covers : badTree.Covers (extendRoles objectRoles [badDef]) :=
  .split (constructors := ctors)
    ((extendRoles_base (by decide : ¬ definedIn [badDef] numN)).trans objectRoles_num)
    (.cons (.leaf _ _) (.cons (.leaf _ _) .nil))

/-- The role of `bad` carries the skeleton of its tree. -/
theorem bad_role : extendRoles objectRoles [badDef] badN = .computes 1 badTree.inspect :=
  extendRoles_tree (baseRoles := objectRoles) (defs := [badDef]) (d := badDef)
    (List.nodup_singleton badN) List.mem_cons_self

/-- `bad` is declared at `num → num`. -/
theorem bad_declared :
    badRules.constantType badN = some (closeType (ofEntries addEntries 1) numT) :=
  rfl

/-- The control's package declares no `junk`. -/
theorem junk_undeclared : badRules.constantType junkN = none := by
  decide

/-- The object package extended by the tree of `bad` does not declare `bad`. -/
theorem bad_fresh {name : DeclName} {type : Tower.Tm 0} (listed : badTypes name = some type) :
    (extend objectRules [badDef]).constantType name = none := by
  by_cases same : name = badN
  · subst same
    decide
  · unfold badTypes at listed
    rw [if_neg same] at listed
    cases listed

/-- The control's package contains the stage of the numbers. -/
theorem ctorStage_sub_badRules : RulesSub ctorStage badRules :=
  (((stage_sub_rules _).trans ConvRules.rules_sub_objectRules).trans
    (extend_sub objectRules [badDef])).trans (withConstants_sub bad_fresh)

/-- `bad` at its declared type. -/
theorem bad_typed {n : Nat} {Γ : Tower.Ctx n} :
    Typed badRules Γ (.const badN) (.pi numT numT) :=
  .const bad_declared
    (Derivable.mono ctorStage_sub_badRules
      (piT (numT_typed List.mem_cons_self) (numT_typed List.mem_cons_self)))
    (LevelTower.IsUniverse.sort _)

/-- `bad zero` is a number. -/
theorem bad_zero_typed :
    Typed badRules .nil (appSpine (.const badN) [.const zeroN]) numT :=
  .appElim bad_typed
    (Derivable.mono ctorStage_sub_badRules
      (zero_typed List.mem_cons_self (List.mem_cons_of_mem _ List.mem_cons_self)))

/-- `bad zero` steps to `junk`. -/
theorem bad_zero_step :
    badRules.computation.step (appSpine (.const badN) [.const zeroN] : Tower.Tm 0)
      (.const junkN) :=
  Or.inr ⟨badDef, List.mem_cons_self, ⟨[.const zeroN], rfl, rfl,
    .split (before := []) (after := []) (args := []) (c := zeroN) rfl rfl
      (.leaf (.const junkN) rfl)⟩⟩

/-- `junk` has no type: it is not declared. -/
theorem junk_untyped {n : Nat} {Γ : Tower.Ctx n} {A : Tower.Tm n} :
    ¬ Typed badRules Γ (.const junkN) A := by
  intro typing
  obtain ⟨type, w, declared, _⟩ := Typed.generation typing
  cases junk_undeclared.symm.trans declared

/-- **Without typed leaves subject reduction fails**: the root steps of the
control's package do not preserve typing. -/
theorem bad_not_preserving : ¬ RootPreserving badRules := fun roots =>
  junk_untyped (roots .nil bad_zero_step bad_zero_typed)

/-- The tree of the control is typed in no context of one variable, at no
type, under no roles: its first leaf has no type. -/
theorem badTree_not_leavesTyped {roles : Roles Tower.Head} {Γ : Tower.Ctx 1}
    {A : Tower.Tm 1} : ¬ badTree.LeavesTyped badRules roles Γ A := by
  intro typed
  have leafOf : badTree.LeafOf [.var] (Pat.splitAllAt zeroN 0 [.var] 0) 0 (.const junkN) :=
    .split (c := zeroN) (fields := 0) rfl (.leaf (.const junkN) _)
  obtain ⟨Δ, π, leaf, _⟩ := CaseTree.LeavesTyped.typedLeaf leafOf typed rfl
  exact junk_untyped leaf.typed

/-! ## Axiom audit -/

#print axioms treeTypes_listed
#print axioms ctorStage_fresh
#print axioms extended_fresh
#print axioms extend_sub
#print axioms treeStage_sub
#print axioms treeStage_no_step
#print axioms rules_sub_treeRules
#print axioms treeRules_churchRosser
#print axioms treeRules_rootShape
#print axioms numT_stage
#print axioms unary_formed
#print axioms binary_formed
#print axioms numeral_stage
#print axioms numVar_stage
#print axioms max_leavesTyped
#print axioms half_leavesTyped
#print axioms pick_leavesTyped
#print axioms max_declares
#print axioms half_declares
#print axioms pick_declares
#print axioms max_suc_suc_equal
#print axioms half_suc_suc_equal
#print axioms pick_suc_suc_equal
#print axioms max_one_one_equal
#print axioms tree_step_preserves
#print axioms executable_step_preserves
#print axioms bad_conditions
#print axioms badTree_covers
#print axioms bad_role
#print axioms junk_undeclared
#print axioms bad_zero_typed
#print axioms bad_zero_step
#print axioms junk_untyped
#print axioms bad_not_preserving
#print axioms badTree_not_leavesTyped

end ObjectCaseTrees
end CodeModel
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
