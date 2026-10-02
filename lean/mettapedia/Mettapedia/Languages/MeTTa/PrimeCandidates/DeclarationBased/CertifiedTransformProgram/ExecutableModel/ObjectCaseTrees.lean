import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectConfluence
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.ObjectShape
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.CaseTreeExtension

/-!
# The object package extended by case trees over the numbers

`max`, `half` and `pick` compute by case trees on `zero` and `suc`. Their
names are not defined by the object package, they do not occur in its left
sides, and `zero` and `suc` are constructors rather than defined names. The
extended package is therefore a constructor system: it is Church–Rosser, and
its root steps are deterministic. It keeps root shape under the roles that
send each new name to its tree.

`max (suc zero) zero` steps to `suc zero`. The zero equation of addition
still steps in the extended package.

A leaf for `add` itself is a critical pair with the zero equation of
addition. The leaf conditions hold and the separation condition does not, and
the two contracts have no common reduct.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
namespace CodeModel
namespace ObjectCaseTrees

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Normalization.CaseTreeExtension
open Presentation.TypedEquality.Impredicative
open Presentation.ConversionCoherence (ChurchRosser)
open Presentation.ConstructorSystem (ConstructorPresentation Normal spineHead
  spineHead_appSpine_const computation_head)

/-! ## The three definitions -/

def maxN : DeclName := .mkSimple "max"
def halfN : DeclName := .mkSimple "half"
def pickN : DeclName := .mkSimple "pick"

/-- The number `k`, built from `zero` and `suc`. -/
def numeral {n : Nat} : Nat → Tower.Tm n
  | 0 => .const zeroN
  | k + 1 => .app (.const sucN) (numeral k)

def maxSucZero : CaseTree Tower.Head := .leaf 1 (.app (.const sucN) (.var (0 : Fin 1)))

def maxSucSuc : CaseTree Tower.Head :=
  .leaf 2 (.app (.const sucN) (appSpine (.const maxN) [.var (1 : Fin 2), .var (0 : Fin 2)]))

def maxSucBranches : CaseBranches Tower.Head :=
  .cons zeroN 0 maxSucZero (.cons sucN 1 maxSucSuc .nil)

/-- After a successor, `max` splits the second argument. -/
def maxSucTree : CaseTree Tower.Head := .split 1 numN maxSucBranches

def maxBranches : CaseBranches Tower.Head :=
  .cons zeroN 0 (.leaf 1 (.var (0 : Fin 1))) (.cons sucN 1 maxSucTree .nil)

/-- `max zero y = y`, `max (suc x) zero = suc x`,
`max (suc x) (suc y) = suc (max x y)`. -/
def maxTree : CaseTree Tower.Head := .split 0 numN maxBranches

def halfSucZero : CaseTree Tower.Head := .leaf 0 (.const zeroN)

def halfSucSuc : CaseTree Tower.Head :=
  .leaf 1 (.app (.const sucN) (appSpine (.const halfN) [.var (0 : Fin 1)]))

def halfSucBranches : CaseBranches Tower.Head :=
  .cons zeroN 0 halfSucZero (.cons sucN 1 halfSucSuc .nil)

/-- `half` splits the predecessor of a successor. -/
def halfSucTree : CaseTree Tower.Head := .split 0 numN halfSucBranches

def halfBranches : CaseBranches Tower.Head :=
  .cons zeroN 0 (.leaf 0 (.const zeroN)) (.cons sucN 1 halfSucTree .nil)

/-- `half zero = zero`, `half (suc zero) = zero`,
`half (suc (suc n)) = suc (half n)`. -/
def halfTree : CaseTree Tower.Head := .split 0 numN halfBranches

def pickSucBranches : CaseBranches Tower.Head :=
  .cons zeroN 0 (.leaf 1 (numeral 2)) (.cons sucN 1 (.leaf 2 (numeral 3)) .nil)

def pickSucTree : CaseTree Tower.Head := .split 1 numN pickSucBranches

def pickBranches : CaseBranches Tower.Head :=
  .cons zeroN 0 (.leaf 1 (numeral 1)) (.cons sucN 1 pickSucTree .nil)

/-- `pick zero y = 1`, `pick (suc x) zero = 2`, `pick (suc x) (suc y) = 3`. -/
def pickTree : CaseTree Tower.Head := .split 0 numN pickBranches

def maxDef : CaseTreeDefinition Tower.Head := ⟨maxN, 2, maxTree⟩
def halfDef : CaseTreeDefinition Tower.Head := ⟨halfN, 1, halfTree⟩
def pickDef : CaseTreeDefinition Tower.Head := ⟨pickN, 2, pickTree⟩

def definitions : List (CaseTreeDefinition Tower.Head) := [maxDef, halfDef, pickDef]

theorem maxBranches_suc : maxBranches.find sucN = some (1, maxSucTree) := rfl

theorem maxSucBranches_zero : maxSucBranches.find zeroN = some (0, maxSucZero) := rfl

theorem max_constructors : maxTree.constructors = [zeroN, sucN, zeroN, sucN] := by
  simp only [maxTree, maxBranches, maxSucTree, maxSucBranches, maxSucZero, maxSucSuc,
    CaseTree.constructors, CaseBranches.constructors, List.append_nil, List.nil_append]

theorem half_constructors : halfTree.constructors = [zeroN, sucN, zeroN, sucN] := by
  simp only [halfTree, halfBranches, halfSucTree, halfSucBranches, halfSucZero, halfSucSuc,
    CaseTree.constructors, CaseBranches.constructors, List.append_nil, List.nil_append]

theorem pick_constructors : pickTree.constructors = [zeroN, sucN, zeroN, sucN] := by
  simp only [pickTree, pickBranches, pickSucTree, pickSucBranches,
    CaseTree.constructors, CaseBranches.constructors, List.append_nil, List.nil_append]

/-! ## Leaf conditions -/

theorem max_scoped : maxTree.Scoped 2 :=
  .split (Nat.zero_lt_succ 1)
    (.cons (.leaf _)
      (.cons (.split (Nat.lt_succ_self 1) (.cons (.leaf _) (.cons (.leaf _) .nil))) .nil))

theorem half_scoped : halfTree.Scoped 1 :=
  .split (Nat.zero_lt_succ 0)
    (.cons (.leaf _)
      (.cons
        (.split (Nat.zero_lt_succ 0) (.cons (.leaf _) (.cons (.leaf _) .nil)))
        .nil))

theorem pick_scoped : pickTree.Scoped 2 :=
  .split (Nat.zero_lt_succ 1)
    (.cons (.leaf _)
      (.cons (.split (Nat.lt_succ_self 1) (.cons (.leaf _) (.cons (.leaf _) .nil))) .nil))

theorem leafConditions : LeafConditions definitions where
  names := by decide
  arity_pos := by decide
  inScope := by
    intro _ mem
    simp only [definitions, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl
    · exact max_scoped
    · exact half_scoped
    · exact pick_scoped
  constructors := by decide

/-- `num` keeps its constructors under the extended roles. -/
theorem extend_num :
    extendRoles objectRoles definitions numN = .inductive ctors := by
  rw [extendRoles_base (by decide : ¬ definedIn definitions numN)]
  exact objectRoles_num

theorem max_covers : maxTree.Covers (extendRoles objectRoles definitions) :=
  .split extend_num
    (.cons (.leaf _ _)
      (.cons
        (.split extend_num (.cons (.leaf _ _) (.cons (.leaf _ _) .nil)))
        .nil))

theorem half_covers : halfTree.Covers (extendRoles objectRoles definitions) :=
  .split extend_num
    (.cons (.leaf _ _)
      (.cons
        (.split extend_num (.cons (.leaf _ _) (.cons (.leaf _ _) .nil)))
        .nil))

theorem pick_covers : pickTree.Covers (extendRoles objectRoles definitions) :=
  .split extend_num
    (.cons (.leaf _ _)
      (.cons
        (.split extend_num (.cons (.leaf _ _) (.cons (.leaf _ _) .nil)))
        .nil))

/-! ## Apart from the object package -/

/-- A defined name of the object package is an executable equation or the decoder. -/
theorem object_defined_iff (c : DeclName) :
    objectConstructors.system.defined c ↔ EquationDefined c ∨ c = holdsN :=
  Iff.rfl

theorem not_defined_zero : ¬ objectConstructors.system.defined zeroN := by
  intro defined
  rcases (object_defined_iff zeroN).mp defined with h | h
  · exact absurd h (by decide : ¬ EquationDefined zeroN)
  · exact absurd h (by decide : zeroN ≠ holdsN)

theorem not_defined_suc : ¬ objectConstructors.system.defined sucN := by
  intro defined
  rcases (object_defined_iff sucN).mp defined with h | h
  · exact absurd h (by decide : ¬ EquationDefined sucN)
  · exact absurd h (by decide : sucN ≠ holdsN)

theorem defined_add : objectConstructors.system.defined addN :=
  (object_defined_iff addN).mpr (Or.inl (by decide : EquationDefined addN))

/-- A simple name of one of the three definitions is not an instance name. -/
theorem fresh_name (name : DeclName) (h : name = maxN ∨ name = halfN ∨ name = pickN) :
    name ≠ holdsN ∧ name ≠ impN ∧ SetProfile.allInstance? name = none ∧
      SetProfile.eqInstance? name = none := by
  rcases h with rfl | rfl | rfl
  all_goals decide

theorem tree_rigid (name : DeclName) (h : name = maxN ∨ name = halfN ∨ name = pickN) :
    objectRoles name = .rigid := by
  obtain ⟨hh, hi, ha, he⟩ := fresh_name name h
  rw [objectRoles_of hh hi ha he]
  apply roles_of_not_mem
  rcases h with rfl | rfl | rfl
  all_goals decide

theorem object_onlyConstructors {c : DeclName} {arity : Nat} {inspect : InspectTree}
    (role : objectRoles c = .computes arity inspect) : inspect.OnlyConstructors := by
  unfold objectRoles at role
  split_ifs at role
  · cases role
    exact .split fun _ => .leaf
  · exact roles_onlyConstructors role

theorem quantifiers_none_of_fresh (c : DeclName) (noAll : SetProfile.allInstance? c = none)
    {A : Tower.Tm 0} : programCodes.quantifiers c ≠ some A := by
  intro found
  change (SetProfile.allInstance? c).map typeTerm = some A at found
  rw [noAll] at found
  cases found

theorem equationCarrier_none_of_fresh (c : DeclName) (noEq : SetProfile.eqInstance? c = none)
    {A : Tower.Tm 0} : programCodes.equationCarrier c ≠ some A := by
  intro found
  change (if true = true then (SetProfile.eqInstance? c).map typeTerm else Option.none) = some A
    at found
  rw [if_pos rfl, noEq] at found
  cases found

/-- None of `max`, `half` and `pick` occurs in an object left side. -/
theorem mentions_tree_name (name : DeclName) (isTree : name = maxN ∨ name = halfN ∨ name = pickN)
    {m : Nat} {left right : Tower.Tm m} (rule : objectConstructors.system.schema left right) :
    ConstructorSystem.mentionsConst name left = false := by
  rcases isTree with rfl | rfl | rfl
  all_goals
    cases rule with
    | base baseRule =>
        have listed := equations_family baseRule
        simp only [equations, SetProfile.nativeEquations, List.mem_append, List.mem_cons,
          List.not_mem_nil, or_false] at listed
        rcases listed with (same | same | same | same) | (same | same | same | same | same | same |
          same | same | same | same | same | same) <;> cases same <;> decide
    | decoder dec =>
        cases dec with
        | imp => decide
        | @all a A carrier =>
            simp only [Codes.allLeft, Codes.holdsOf, ConstructorSystem.mentionsConst,
              Bool.or_eq_false_iff, beq_eq_false_iff_ne]
            constructor
            · decide
            constructor
            · intro same
              rw [same] at carrier
              exact absurd carrier (quantifiers_none_of_fresh _ (by decide))
            · trivial
        | @eq e A carrier =>
            simp only [Codes.eqLeft, Codes.holdsOf, ConstructorSystem.mentionsConst,
              Bool.or_eq_false_iff, beq_eq_false_iff_ne]
            constructor
            · decide
            constructor
            · constructor
              · intro same
                rw [same] at carrier
                exact absurd carrier (equationCarrier_none_of_fresh _ (by decide))
              · trivial
            · trivial

/-- The three names are undefined, their pattern constructors `zero` and `suc`
are undefined, and none of the three names occurs in an object left side. -/
theorem definitions_apart : Apart definitions objectConstructors.system where
  names := by
    intro _ mem defined
    simp only [definitions, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl
    all_goals
      dsimp only [maxDef, halfDef, pickDef] at defined
      rcases (object_defined_iff _).mp defined with h | h
      · exact absurd h (by decide)
      · exact absurd h (by decide)
  constructors := by
    intro _ mem c hc defined
    simp only [definitions, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl
    all_goals
      dsimp only [maxDef, halfDef, pickDef] at hc defined
      try rw [max_constructors] at hc
      try rw [half_constructors] at hc
      try rw [pick_constructors] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl
      all_goals
        rcases (object_defined_iff _).mp defined with h | h
        · exact absurd h (by decide)
        · exact absurd h (by decide)
  absent := by
    intro _ mem _ _ _ rule
    simp only [definitions, List.mem_cons, List.not_mem_nil, or_false] at mem
    rcases mem with rfl | rfl | rfl
    · dsimp only [maxDef]
      exact mentions_tree_name maxN (.inl rfl) rule
    · dsimp only [halfDef]
      exact mentions_tree_name halfN (.inr (.inl rfl)) rule
    · dsimp only [pickDef]
      exact mentions_tree_name pickN (.inr (.inr rfl)) rule

/-- The object package extended by `max`, `half` and `pick`. -/
def extended : Rules Tower.Head := extend objectRules definitions

def extended_constructors : ConstructorPresentation extended :=
  extendConstructors objectConstructors leafConditions definitions_apart

theorem extended_churchRosser : ChurchRosser extended :=
  extend_churchRosser objectConstructors leafConditions definitions_apart

theorem extended_root_deterministic {n : Nat} {t u u' : Tower.Tm n}
    (step : extended.computation.step t u) (step' : extended.computation.step t u') : u = u' :=
  extend_root_deterministic objectConstructors leafConditions definitions_apart step step'

theorem extend_declared : ConstructorsDeclared (extendRoles objectRoles definitions) where
  arity := by
    intro T cs k fields role mem
    have base : objectRoles T = .inductive cs := by
      unfold extendRoles at role
      split at role
      · cases role
      · exact role
    obtain ⟨rfl, rfl⟩ := objectRoles_inductive base
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [extendRoles_base (by decide : ¬ definedIn definitions zeroN)]
      exact objectRoles_zero
    · rw [extendRoles_base (by decide : ¬ definedIn definitions sucN)]
      exact objectRoles_suc
  distinct := by
    intro T cs role
    have base : objectRoles T = .inductive cs := by
      unfold extendRoles at role
      split at role
      · cases role
      · exact role
    obtain ⟨rfl, rfl⟩ := objectRoles_inductive base
    exact objectConstructorsDeclared.distinct objectRoles_num

/-- Root shape of the extension: each new name computes by its tree, and every
other name keeps the role it has in the object package. -/
theorem extended_rootShape : RootShape extended (extendRoles objectRoles definitions) :=
  extend_rootShape objectConstructors objectShape leafConditions definitions_apart
    object_onlyConstructors
    (by
      intro _ mem arity role
      simp only [definitions, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl
      · dsimp only [maxDef] at role
        cases (tree_rigid maxN (.inl rfl)).symm.trans role
      · dsimp only [halfDef] at role
        cases (tree_rigid halfN (.inr (.inl rfl))).symm.trans role
      · dsimp only [pickDef] at role
        cases (tree_rigid pickN (.inr (.inr rfl))).symm.trans role)
    extend_declared
    (by
      intro d mem
      simp only [definitions, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl
      · exact max_covers
      · exact half_covers
      · exact pick_covers)

/-! ## Positive controls -/

/-- `max (suc zero) zero` evaluates to `suc zero`. -/
theorem max_suc_zero_eval (n : Nat) :
    maxTree.Eval
      ([.app (.const sucN) (.const zeroN), .const zeroN] : List (Tower.Tm n))
      (.app (.const sucN) (.const zeroN) : Tower.Tm n) := by
  refine .split (before := []) (after := [.const zeroN]) (args := [.const zeroN])
    rfl maxBranches_suc ?_
  refine .split (before := [.const zeroN]) (after := []) (args := [])
    rfl maxSucBranches_zero ?_
  exact .leaf (.app (.const sucN) (.var (0 : Fin 1))) rfl

/-- `max (suc zero) zero` reduces in the extended package. -/
theorem max_suc_zero_reduces (n : Nat) :
    extended.computation.step
      (appSpine (.const maxN)
        ([.app (.const sucN) (.const zeroN), .const zeroN] : List (Tower.Tm n)))
      (.app (.const sucN) (.const zeroN)) :=
  Or.inr ⟨maxDef, List.mem_cons_self, ⟨_, rfl, rfl, max_suc_zero_eval n⟩⟩

/-- `add x zero` still steps to `x`. -/
theorem add_zero_still {n : Nat} (x : Tower.Tm n) :
    extended.computation.step (.app (.app (.const addN) x) (.const zeroN)) x :=
  Or.inl (programCodes.extend_base_step rules
    (equation_sound (equation_listed 0 (by decide) rfl) (fun _ => x)))

/-! ## A defined name is a critical pair -/

/-- A leaf `add x y ⟶ suc zero`, for the same `add` the object package defines. -/
def addLeaf : CaseTreeDefinition Tower.Head where
  name := addN
  arity := 2
  tree := .leaf 2 (.app (.const sucN) (.const zeroN))

/-- The leaf is one scoped definition and splits on no constructor. -/
theorem addLeaf_conditions : LeafConditions [addLeaf] where
  names := by
    refine List.nodup_cons.mpr ⟨?_, List.nodup_nil⟩
    intro h
    cases h
  arity_pos := by
    intro _ mem
    cases mem with
    | head => exact Nat.zero_lt_succ 1
    | tail _ h => cases h
  inScope := by
    intro _ mem
    cases mem with
    | head => exact .leaf _
    | tail _ h => cases h
  constructors := by
    intro _ mem _ hc
    cases mem with
    | head => cases hc
    | tail _ h => cases h

/-- The separation fails: `add` is a defined name of the object package. -/
theorem addLeaf_not_apart : ¬ Apart [addLeaf] objectConstructors.system := by
  intro apart
  exact apart.names addLeaf (List.Mem.head []) defined_add

/-- The object package extended by that leaf. -/
def addOverlap : Rules Tower.Head := extend objectRules [addLeaf]

theorem add_base_step {n : Nat} :
    addOverlap.computation.step
      (.app (.app (.const addN) (.const zeroN)) (.const zeroN) : Tower.Tm n)
      (.const zeroN) :=
  Or.inl (programCodes.extend_base_step rules
    (equation_sound (equation_listed 0 (by decide) rfl) (fun _ => .const zeroN)))

theorem add_tree_step {n : Nat} :
    addOverlap.computation.step
      (.app (.app (.const addN) (.const zeroN)) (.const zeroN) : Tower.Tm n)
      (.app (.const sucN) (.const zeroN)) :=
  Or.inr ⟨addLeaf, List.Mem.head [],
    ⟨[.const zeroN, .const zeroN], rfl, rfl,
      .leaf (.app (.const sucN) (.const zeroN)) rfl⟩⟩

theorem addOverlap_head {n : Nat} {t u : Tower.Tm n} (step : addOverlap.computation.step t u) :
    (∃ name count, objectConstructors.system.defined name ∧ spineHead t = some (name, count)) ∨
      spineHead t = some (addN, 2) := by
  rcases step with step | step
  · exact .inl (computation_head objectConstructors step)
  · obtain ⟨_, mem, treeStep⟩ := step
    cases mem with
    | head =>
        obtain ⟨args, rfl, length, _⟩ := treeStep
        refine .inr ?_
        rw [spineHead_appSpine_const]
        rw [length]
        rfl
    | tail _ h => cases h

theorem addOverlap_no_zero {n : Nat} {u : Tower.Tm n} :
    ¬ addOverlap.computation.step (.const zeroN) u := by
  intro step
  rcases addOverlap_head step with ⟨name, _, defined, head⟩ | head
  · change (some (zeroN, 0) : Option (DeclName × Nat)) = some (name, _) at head
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj head)
    exact not_defined_zero defined
  · change (some (zeroN, 0) : Option (DeclName × Nat)) = some (addN, 2) at head
    obtain ⟨-, count⟩ := Prod.mk.inj (Option.some.inj head)
    cases count

theorem addOverlap_no_suc_zero {n : Nat} {u : Tower.Tm n} :
    ¬ addOverlap.computation.step (.app (.const sucN) (.const zeroN)) u := by
  intro step
  have shape : spineHead (.app (.const sucN) (.const zeroN) : Tower.Tm n) = some (sucN, 1) :=
    spineHead_appSpine_const sucN [.const zeroN]
  rcases addOverlap_head step with ⟨name, _, defined, head⟩ | head
  · obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj (shape.symm.trans head))
    exact not_defined_suc defined
  · obtain ⟨-, count⟩ := Prod.mk.inj (Option.some.inj (shape.symm.trans head))
    cases count

theorem zero_normal {n : Nat} : Normal addOverlap (.const zeroN : Tower.Tm n) :=
  Normal.const zeroN addOverlap_no_zero

theorem suc_zero_normal {n : Nat} :
    Normal addOverlap (.app (.const sucN) (.const zeroN) : Tower.Tm n) :=
  Normal.app (Normal.const sucN addOverlap_no_const_suc) zero_normal
    (fun _ h => by cases h) addOverlap_no_suc_zero
  where
    addOverlap_no_const_suc {n : Nat} {u : Tower.Tm n} :
        ¬ addOverlap.computation.step (.const sucN) u := by
      intro step
      rcases addOverlap_head step with ⟨name, _, defined, head⟩ | head
      · change (some (sucN, 0) : Option (DeclName × Nat)) = some (name, _) at head
        obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj head)
        exact not_defined_suc defined
      · change (some (sucN, 0) : Option (DeclName × Nat)) = some (addN, 2) at head
        obtain ⟨-, count⟩ := Prod.mk.inj (Option.some.inj head)
        cases count

theorem zero_ne_suc_zero :
    (.const zeroN : Tower.Tm 0) ≠ .app (.const sucN) (.const zeroN) := by
  intro h
  cases h

/-- Without the separation, Church–Rosser fails on the object package.
`add zero zero` steps to `zero` by the object equation and to `suc zero` by
the leaf. Both contracts are normal, and the leaf conditions hold. -/
theorem addOverlap_not_churchRosser : ¬ ChurchRosser addOverlap := by
  intro churchRosser
  obtain ⟨_, toZero, toSuc⟩ := churchRosser (n := 0)
    (.trans _ _ _
      (.symm _ _ (.rel _ _ (.root add_base_step)))
      (.rel _ _ (.root add_tree_step)))
  have atZero := Normal.stepStar (zero_normal (n := 0)) toZero
  have atSuc := Normal.stepStar (suc_zero_normal (n := 0)) toSuc
  exact zero_ne_suc_zero (atZero.symm.trans atSuc)

end ObjectCaseTrees
end CodeModel
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
