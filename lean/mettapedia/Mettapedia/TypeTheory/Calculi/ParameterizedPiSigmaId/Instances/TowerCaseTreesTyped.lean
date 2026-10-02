import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.CaseTreeTyping
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerCaseTrees
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.Tower

/-!
# The definitions over the numbers as typed case trees

The four definitions of `TowerCaseTrees` (`eqn`, `max`, `half`, `pick`) are
declared constants computing by typed case trees (`DeclaresCaseTree`). Their
leaves are typed in the package that declares the ten constants and computes
nothing; the package computing by the trees contains it.

Positive example. The tree of `max` has two nested splits. Its leaf under
`succ`, `succ` is typed in the context `x : num, y : num`, and its equation is a
typed definitional equality: `max (succ a) (succ b)` is equal to
`succ (max a b)` at `num`, for all `a` and `b` typed at `num` in any context
(`max_succ_succ_equal`). Likewise `half (succ (succ a))` is equal to
`succ (half a)` (`half_succ_succ_equal`): the recursive call is on a variable two
constructors down.

Given the facts about the weak-head forms of the package's types, the root
steps of the four trees preserve typing (`rootPreserving_of_facts`). Those
facts come from a model in which the four constants are semantic, which is not
built here.

Negative example. The tree `bad zero = junk; bad (succ n) = n`, with `junk` a
constant that no package declares, covers and is scoped; `bad` has the role of
its tree, is declared at `num → num`, and its package meets the root-shape
obligations. Only the typing of the first leaf fails
(`badTree_not_leavesTyped`), and with it subject reduction: `bad zero` is typed
at `num` and steps to `junk`, which has no type (`bad_not_preserving`). So the
typing of the leaves cannot be dropped from the declaration.

A leaf typed at the wrong type, say `bad zero = true` at `num`, is the more
familiar failure. Refuting `true : num` needs the types `bool` and `num` to be
distinct in the package extended by `bad`, which is again a fact about the
weak-head forms of that package's types. An undeclared constant has no type by
inversion alone, so the control needs no model.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open Mettapedia.TypeTheory.UniverseLevel
open TelescopeAbstraction (closeType applyClosed)

namespace TowerCaseTreesModel

/-! ## The declaring stage and the setting -/

/-- The package with the ten constants declared and no root computation: the
stage at which the leaves of the trees are typed. -/
def declaredRules : Rules Tower.Head :=
  { Tower.rules with constantType := constantType }

/-- The declaring stage is contained in the package computing by the trees. -/
theorem declaredRules_sub : RulesSub declaredRules rules :=
  ⟨id, id, id, id, id, id, fun step => nomatch step⟩

/-- The tower's level model, for the package computing by the trees. -/
def levels (valuation : Nat → Nat) : LevelModel rules ℕ where
  level := (TowerModel.levels valuation).level
  successor := (TowerModel.levels valuation).successor
  universe_typing := (TowerModel.levels valuation).universe_typing
  ground_typing := (TowerModel.levels valuation).ground_typing
  cumulative_universe := (TowerModel.levels valuation).cumulative_universe
  headEq_level := (TowerModel.levels valuation).headEq_level
  join_level := (TowerModel.levels valuation).join_level
  join_exists := (TowerModel.levels valuation).join_exists
  join_upper := (TowerModel.levels valuation).join_upper
  cumulative_refl := (TowerModel.levels valuation).cumulative_refl
  headEq_symm := (TowerModel.levels valuation).headEq_symm
  headEq_trans := (TowerModel.levels valuation).headEq_trans
  universe_decided := (TowerModel.levels valuation).universe_decided

/-- The normalization setting of the package computing by the trees. -/
def setting (valuation : Nat → Nat) : Setting Tower.Head ℕ where
  R := rules
  roles := roles
  E := declarative rules
  levels := levels valuation
  shape := shape
  constructors := constructorsDeclared

/-! ## The declared types -/

/-- The telescope of the numbers: every entry is `num`. -/
def numEntries : (i : Nat) → Tm Tower.Head i := fun _ => .const num

/-- `num` is declared in the lowest universe. -/
theorem declared_num : declaredRules.constantType num = some (.head u) := rfl

/-- `bool` is declared in the lowest universe. -/
theorem declared_bool : declaredRules.constantType bool = some (.head u) := rfl

/-- `zero` is declared at its constructor type. -/
theorem declared_zero : declaredRules.constantType zero = some (ctorType num []) := rfl

/-- `succ` is declared at its constructor type. -/
theorem declared_succ : declaredRules.constantType succ = some (ctorType num [.recursive]) := rfl

/-- `true` is declared a boolean. -/
theorem declared_tt : declaredRules.constantType tt = some (.const bool) := rfl

/-- `false` is declared a boolean. -/
theorem declared_ff : declaredRules.constantType ff = some (.const bool) := rfl

/-- `eqn` is declared at `num → num → bool`. -/
theorem declared_eqn :
    declaredRules.constantType eqn = some (closeType (ofEntries numEntries 2) (.const bool)) :=
  rfl

/-- `max` is declared at `num → num → num`. -/
theorem declared_max :
    declaredRules.constantType max = some (closeType (ofEntries numEntries 2) (.const num)) :=
  rfl

/-- `half` is declared at `num → num`. -/
theorem declared_half :
    declaredRules.constantType half = some (closeType (ofEntries numEntries 1) (.const num)) :=
  rfl

/-- `pick` is declared at `num → num → num`. -/
theorem declared_pick :
    declaredRules.constantType pick = some (closeType (ofEntries numEntries 2) (.const num)) :=
  rfl

/-! ## Typings at the declaring stage -/

section Typing

variable {n : Nat} {Γ : Ctx Tower.Head n}

/-- The numbers are a type of the lowest universe. -/
theorem num_typed : Typed declaredRules Γ (.const num) (.head u) :=
  .const declared_num (.headType (LevelTower.HeadTyping.sort _)) (LevelTower.IsUniverse.sort _)

/-- The booleans are a type of the lowest universe. -/
theorem bool_typed : Typed declaredRules Γ (.const bool) (.head u) :=
  .const declared_bool (.headType (LevelTower.HeadTyping.sort _)) (LevelTower.IsUniverse.sort _)

/-- `num → num` is a type. -/
theorem unary_formed : Typed declaredRules .nil (.pi (.const num) (.const num))
    (.head (.sort (.max (.const 0) (.const 0)))) :=
  .piForm num_typed (LevelTower.IsUniverse.sort _) num_typed (LevelTower.IsUniverse.sort _)
    (LevelTower.Join.sorts _ _)

/-- `num → num → result` is a type, for a type constant `result` of the lowest
universe. -/
theorem binary_formed {result : DeclName}
    (typed : ∀ {m : Nat} {Δ : Ctx Tower.Head m},
      Typed declaredRules Δ (.const result) (.head u)) :
    Typed declaredRules .nil (.pi (.const num) (.pi (.const num) (.const result)))
      (.head (.sort (.max (.const 0) (.max (.const 0) (.const 0))))) :=
  .piForm num_typed (LevelTower.IsUniverse.sort _)
    (.piForm num_typed (LevelTower.IsUniverse.sort _) typed (LevelTower.IsUniverse.sort _)
      (LevelTower.Join.sorts _ _))
    (LevelTower.IsUniverse.sort _) (LevelTower.Join.sorts _ _)

/-- `zero` is a number. -/
theorem zero_typed : Typed declaredRules Γ (.const zero) (.const num) :=
  .const declared_zero num_typed (LevelTower.IsUniverse.sort _)

/-- `succ` is a function on the numbers. -/
theorem succ_typed : Typed declaredRules Γ (.const succ) (.pi (.const num) (.const num)) :=
  .const declared_succ unary_formed (LevelTower.IsUniverse.sort _)

/-- `true` is a boolean. -/
theorem tt_typed : Typed declaredRules Γ (.const tt) (.const bool) :=
  .const declared_tt bool_typed (LevelTower.IsUniverse.sort _)

/-- `false` is a boolean. -/
theorem ff_typed : Typed declaredRules Γ (.const ff) (.const bool) :=
  .const declared_ff bool_typed (LevelTower.IsUniverse.sort _)

/-- `eqn` at its declared type. -/
theorem eqn_typed :
    Typed declaredRules Γ (.const eqn) (.pi (.const num) (.pi (.const num) (.const bool))) :=
  .const declared_eqn (binary_formed bool_typed) (LevelTower.IsUniverse.sort _)

/-- `max` at its declared type. -/
theorem max_typed :
    Typed declaredRules Γ (.const max) (.pi (.const num) (.pi (.const num) (.const num))) :=
  .const declared_max (binary_formed num_typed) (LevelTower.IsUniverse.sort _)

/-- `half` at its declared type. -/
theorem half_typed : Typed declaredRules Γ (.const half) (.pi (.const num) (.const num)) :=
  .const declared_half unary_formed (LevelTower.IsUniverse.sort _)

/-- `pick` at its declared type. -/
theorem pick_typed :
    Typed declaredRules Γ (.const pick) (.pi (.const num) (.pi (.const num) (.const num))) :=
  .const declared_pick (binary_formed num_typed) (LevelTower.IsUniverse.sort _)

/-- Every numeral is a number. -/
theorem numeral_typed : ∀ k : Nat, Typed declaredRules Γ (numeral k) (.const num)
  | 0 => zero_typed
  | k + 1 => .appElim succ_typed (numeral_typed k)

end Typing

/-- A variable of a context of numbers is a number. -/
theorem numVar_typed {k : Nat} (i : Fin k) :
    Typed declaredRules (ofEntries numEntries k) (.var i) (.const num) := by
  have h := Derivable.var (R := declaredRules) (Γ := ofEntries numEntries k) i
  have lookup : Ctx.lookup (ofEntries numEntries k) i = .const num :=
    ofEntries_lookup_closed (fun _ => .const num) k i
  rw [lookup] at h
  exact h

/-- The constructor type of `zero` is a type. -/
theorem zero_formed :
    ∃ w, declaredRules.isUniverse w ∧ Typed declaredRules .nil (ctorType num []) (.head w) :=
  ⟨u, LevelTower.IsUniverse.sort _, num_typed⟩

/-- The constructor type of `succ` is a type. -/
theorem succ_formed :
    ∃ w, declaredRules.isUniverse w ∧
      Typed declaredRules .nil (ctorType num [.recursive]) (.head w) :=
  ⟨_, LevelTower.IsUniverse.sort _, unary_formed⟩

/-! ## The four trees are typed -/

/-- `eqn` is typed as a case tree: every leaf is a boolean in its context. -/
theorem eqn_leavesTyped :
    eqnTree.LeavesTyped declaredRules roles (ofEntries numEntries 2) (.const bool) :=
  CaseTree.LeavesTyped.split (s := 0) (d := 1) (e := numEntries) (A := .const bool) rfl roles_num
    (.cons declared_zero zero_formed
      (CaseTree.LeavesTyped.split (s := 0) (d := 0) (e := numEntries) (A := .const bool) rfl
        roles_num
        (.cons declared_zero zero_formed (.leaf tt_typed)
          (.cons declared_succ succ_formed (.leaf ff_typed) .nil)))
      (.cons declared_succ succ_formed
        (CaseTree.LeavesTyped.split (s := 1) (d := 0) (e := numEntries) (A := .const bool) rfl
          roles_num
          (.cons declared_zero zero_formed (.leaf ff_typed)
            (.cons declared_succ succ_formed
              (.leaf (.appElim (.appElim eqn_typed (numVar_typed (k := 2) 1))
                (numVar_typed (k := 2) 0)))
              .nil)))
        .nil))

/-- The leaf of `max` under `succ`, `succ`: `succ (max x y)` is a number in the
context `x : num, y : num`. -/
theorem max_leaf_succ_succ :
    Typed declaredRules (ofEntries numEntries 2)
      (.app (.const succ) (appSpine (.const max) [.var 1, .var 0])) (.const num) :=
  .appElim succ_typed
    (.appElim (.appElim max_typed (numVar_typed (k := 2) 1)) (numVar_typed (k := 2) 0))

/-- `max` is typed as a case tree: every leaf is a number in its context. -/
theorem max_leavesTyped :
    maxTree.LeavesTyped declaredRules roles (ofEntries numEntries 2) (.const num) :=
  CaseTree.LeavesTyped.split (s := 0) (d := 1) (e := numEntries) (A := .const num) rfl roles_num
    (.cons declared_zero zero_formed (.leaf (numVar_typed (k := 1) 0))
      (.cons declared_succ succ_formed
        (CaseTree.LeavesTyped.split (s := 1) (d := 0) (e := numEntries) (A := .const num) rfl
          roles_num
          (.cons declared_zero zero_formed
            (.leaf (.appElim succ_typed (numVar_typed (k := 1) 0)))
            (.cons declared_succ succ_formed (.leaf max_leaf_succ_succ) .nil)))
        .nil))

/-- The leaf of `half` under `succ (succ _)`: `succ (half x)` is a number in the
context `x : num`. -/
theorem half_leaf_succ_succ :
    Typed declaredRules (ofEntries numEntries 1)
      (.app (.const succ) (appSpine (.const half) [.var 0])) (.const num) :=
  .appElim succ_typed (.appElim half_typed (numVar_typed (k := 1) 0))

/-- `half` is typed as a case tree: every leaf is a number in its context. -/
theorem half_leavesTyped :
    halfTree.LeavesTyped declaredRules roles (ofEntries numEntries 1) (.const num) :=
  CaseTree.LeavesTyped.split (s := 0) (d := 0) (e := numEntries) (A := .const num) rfl roles_num
    (.cons declared_zero zero_formed (.leaf zero_typed)
      (.cons declared_succ succ_formed
        (CaseTree.LeavesTyped.split (s := 0) (d := 0) (e := numEntries) (A := .const num) rfl
          roles_num
          (.cons declared_zero zero_formed (.leaf zero_typed)
            (.cons declared_succ succ_formed (.leaf half_leaf_succ_succ) .nil)))
        .nil))

/-- `pick` is typed as a case tree: every leaf is a numeral. -/
theorem pick_leavesTyped :
    pickTree.LeavesTyped declaredRules roles (ofEntries numEntries 2) (.const num) :=
  CaseTree.LeavesTyped.split (s := 0) (d := 1) (e := numEntries) (A := .const num) rfl roles_num
    (.cons declared_zero zero_formed (.leaf (numeral_typed 1))
      (.cons declared_succ succ_formed
        (CaseTree.LeavesTyped.split (s := 1) (d := 0) (e := numEntries) (A := .const num) rfl
          roles_num
          (.cons declared_zero zero_formed (.leaf (numeral_typed 2))
            (.cons declared_succ succ_formed (.leaf (numeral_typed 3)) .nil)))
        .nil))

/-! ## The four declarations -/

/-- `eqn : num → num → bool` computes by its typed case tree. -/
theorem eqn_declares (valuation : Nat → Nat) :
    DeclaresCaseTree (setting valuation) declaredRules eqn (ofEntries numEntries 2)
      (.const bool) eqnTree where
  role := rfl
  sub₁ := declaredRules_sub
  declared := declared_eqn
  typed := ⟨_, LevelTower.IsUniverse.sort _, binary_formed bool_typed⟩
  leaves := eqn_leavesTyped
  steps := fun step => ⟨⟨eqn, 2, eqnTree⟩, List.mem_cons_self, step⟩

/-- `max : num → num → num` computes by its typed case tree. -/
theorem max_declares (valuation : Nat → Nat) :
    DeclaresCaseTree (setting valuation) declaredRules max (ofEntries numEntries 2)
      (.const num) maxTree where
  role := rfl
  sub₁ := declaredRules_sub
  declared := declared_max
  typed := ⟨_, LevelTower.IsUniverse.sort _, binary_formed num_typed⟩
  leaves := max_leavesTyped
  steps := fun step => ⟨⟨max, 2, maxTree⟩, List.mem_cons_of_mem _ List.mem_cons_self, step⟩

/-- `half : num → num` computes by its typed case tree. -/
theorem half_declares (valuation : Nat → Nat) :
    DeclaresCaseTree (setting valuation) declaredRules half (ofEntries numEntries 1)
      (.const num) halfTree where
  role := rfl
  sub₁ := declaredRules_sub
  declared := declared_half
  typed := ⟨_, LevelTower.IsUniverse.sort _, unary_formed⟩
  leaves := half_leavesTyped
  steps := fun step =>
    ⟨⟨half, 1, halfTree⟩, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
      step⟩

/-- `pick : num → num → num` computes by its typed case tree. -/
theorem pick_declares (valuation : Nat → Nat) :
    DeclaresCaseTree (setting valuation) declaredRules pick (ofEntries numEntries 2)
      (.const num) pickTree where
  role := rfl
  sub₁ := declaredRules_sub
  declared := declared_pick
  typed := ⟨_, LevelTower.IsUniverse.sort _, binary_formed num_typed⟩
  leaves := pick_leavesTyped
  steps := fun step =>
    ⟨⟨pick, 2, pickTree⟩,
      List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)),
      step⟩

/-! ## Leaf equations -/

/-- **The third equation of `max` is a typed definitional equality**:
`max (succ a) (succ b)` is equal to `succ (max a b)` at `num`, for all `a` and
`b` typed at `num`. -/
theorem max_succ_succ_equal {n : Nat} {Γ : Ctx Tower.Head n} {a b : Tm Tower.Head n}
    (ha : Typed rules Γ a (.const num)) (hb : Typed rules Γ b (.const num)) :
    Equal rules Γ (appSpine (.const max) [.app (.const succ) a, .app (.const succ) b])
      (.app (.const succ) (appSpine (.const max) [a, b])) (.const num) := by
  have leaf : maxTree.TypedLeaf declaredRules (ofEntries numEntries 2) (.const num)
      (ofEntries numEntries 2) _ (.app (.const succ) (appSpine (.const max) [.var 1, .var 0])) :=
    CaseTree.TypedLeaf.split (s := 0) (d := 1) (e := numEntries) (A := .const num) (c := succ)
      (fields := [.recursive]) rfl rfl declared_succ succ_formed
      (CaseTree.TypedLeaf.split (s := 1) (d := 0) (e := numEntries) (A := .const num) (c := succ)
        (fields := [.recursive]) rfl rfl declared_succ succ_formed (.leaf max_leaf_succ_succ))
  have typed : SubstMor rules (ofEntries numEntries 2) Γ
      (consSub b (consSub a fun i => i.elim0)) :=
    SubstMor.cons (SubstMor.cons (fun i => i.elim0) ha) hb
  exact (max_declares fun _ => 0).leaf_equation leaf typed

/-- **The third equation of `half` is a typed definitional equality**:
`half (succ (succ a))` is equal to `succ (half a)` at `num`, for every `a` typed
at `num`. -/
theorem half_succ_succ_equal {n : Nat} {Γ : Ctx Tower.Head n} {a : Tm Tower.Head n}
    (ha : Typed rules Γ a (.const num)) :
    Equal rules Γ (appSpine (.const half) [.app (.const succ) (.app (.const succ) a)])
      (.app (.const succ) (appSpine (.const half) [a])) (.const num) := by
  have leaf : halfTree.TypedLeaf declaredRules (ofEntries numEntries 1) (.const num)
      (ofEntries numEntries 1) _ (.app (.const succ) (appSpine (.const half) [.var 0])) :=
    CaseTree.TypedLeaf.split (s := 0) (d := 0) (e := numEntries) (A := .const num) (c := succ)
      (fields := [.recursive]) rfl rfl declared_succ succ_formed
      (CaseTree.TypedLeaf.split (s := 0) (d := 0) (e := numEntries) (A := .const num) (c := succ)
        (fields := [.recursive]) rfl rfl declared_succ succ_formed (.leaf half_leaf_succ_succ))
  have typed : SubstMor rules (ofEntries numEntries 1) Γ (consSub a fun i => i.elim0) :=
    SubstMor.cons (fun i => i.elim0) ha
  exact (half_declares fun _ => 0).leaf_equation leaf typed

/-! ## Root shape and subject reduction of the package -/

/-- The root shape of the package follows from the typing of its trees. -/
example : RootShape rules roles :=
  RootShape.of_typedCaseTrees (definitions := definitions) constructorsDeclared (by decide)
    (fun d mem => by
      simp only [definitions, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl <;> rfl)
    (fun d mem => by
      simp only [definitions, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl
      · exact ⟨_, _, _, eqn_leavesTyped⟩
      · exact ⟨_, _, _, max_leavesTyped⟩
      · exact ⟨_, _, _, half_leavesTyped⟩
      · exact ⟨_, _, _, pick_leavesTyped⟩)
    (fun step => step)

/-- **Given the facts about the weak-head forms of the package's types, the
root steps of the four trees preserve typing.** -/
theorem rootPreserving_of_facts (facts : FormFacts rules roles) : RootPreserving rules :=
  RootPreserving.of_caseTrees (S := setting fun _ => 0) (definitions := definitions) facts
    (fun d mem => by
      simp only [definitions, List.mem_cons, List.not_mem_nil, or_false] at mem
      rcases mem with rfl | rfl | rfl | rfl
      · exact ⟨_, _, _, eqn_declares _⟩
      · exact ⟨_, _, _, max_declares _⟩
      · exact ⟨_, _, _, half_declares _⟩
      · exact ⟨_, _, _, pick_declares _⟩)
    (fun step => step)

/-! ## An ill-typed leaf -/

/-- The constant of the negative control. -/
def bad : DeclName := .mkSimple "bad"

/-- A constant that no package here declares. -/
def junk : DeclName := .mkSimple "junk"

/-- `bad zero = junk`, `bad (succ n) = n`. -/
def badTree : CaseTree Tower.Head :=
  .split 0 num (.cons zero 0 (.leaf 0 (.const junk)) (.cons succ 1 (.leaf 1 (.var 0)) .nil))

/-- The declared types of the control: the numbers and `bad : num → num`. -/
def badConstantType : DeclName → Option (Tm Tower.Head 0) := fun name =>
  if name = num then some (.head u)
  else if name = zero then some (.const num)
  else if name = succ then some (.pi (.const num) (.const num))
  else if name = bad then some (.pi (.const num) (.const num))
  else none

/-- The tower with the numbers and `bad`, computing by its tree. -/
def badRules : Rules Tower.Head :=
  { Tower.rules with
    constantType := badConstantType
    computation := caseTreeComputation [⟨bad, 1, badTree⟩] }

/-- The roles of the control: `bad` computes by the skeleton of its tree. -/
def badRoles : Roles Tower.Head := fun name =>
  if name = num then .inductive numCtors
  else if name = zero then .constructor 0
  else if name = succ then .constructor 1
  else if name = bad then .computes 1 badTree.inspect
  else .rigid

/-- The only inductive type of the control is `num`. -/
theorem badRoles_inductive {T : DeclName} {cs : List (DeclName × List (Field Tower.Head))}
    (role : badRoles T = .inductive cs) : T = num ∧ cs = numCtors := by
  unfold badRoles at role
  split at role
  · rename_i h
    exact ⟨h, (Role.inductive.inj role).symm⟩
  · split at role
    · cases role
    · split at role
      · cases role
      · split at role
        · cases role
        · cases role

/-- The constructors of the control are declared as constructors, under
distinct names. -/
theorem badConstructors : ConstructorsDeclared badRoles where
  arity := by
    intro T cs k fields role mem
    obtain ⟨rfl, rfl⟩ := badRoles_inductive role
    simp only [numCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
  distinct := by
    intro T cs role
    obtain ⟨rfl, rfl⟩ := badRoles_inductive role
    decide

/-- The tree of the control covers. -/
theorem badTree_covers : badTree.Covers badRoles :=
  .split (constructors := numCtors) rfl (.cons (.leaf _ _) (.cons (.leaf _ _) .nil))

/-- The tree of the control is scoped over its one argument. -/
theorem badTree_scoped : badTree.Scoped 1 :=
  .split Nat.zero_lt_one (.cons (.leaf _) (.cons (.leaf _) .nil))

/-- The role of `bad` carries the skeleton of its tree. -/
theorem bad_role : badRoles bad = .computes 1 badTree.inspect := rfl

/-- `bad` is declared at `num → num`. -/
theorem bad_declared :
    badRules.constantType bad = some (closeType (ofEntries numEntries 1) (.const num)) :=
  rfl

/-- The steps of the tree are root steps of the control's package. -/
theorem bad_steps {n : Nat} {t w : Tm Tower.Head n} (step : badTree.Step bad 1 t w) :
    badRules.computation.step t w :=
  ⟨⟨bad, 1, badTree⟩, List.mem_cons_self, step⟩

/-- The control's package meets the root-shape obligations: its tree covers. -/
theorem badShape : RootShape badRules badRoles :=
  RootShape.of_caseTrees (definitions := [⟨bad, 1, badTree⟩]) badConstructors
    (List.nodup_singleton _)
    (fun d mem => by
      obtain rfl := List.mem_singleton.mp mem
      rfl)
    (fun d mem => by
      obtain rfl := List.mem_singleton.mp mem
      exact badTree_covers)
    (fun step => step)

section BadTyping

variable {n : Nat} {Γ : Ctx Tower.Head n}

/-- The numbers are a type in the control's package. -/
theorem bad_num_typed : Typed badRules Γ (.const num) (.head u) :=
  .const (rfl : badRules.constantType num = some (.head u))
    (.headType (LevelTower.HeadTyping.sort _)) (LevelTower.IsUniverse.sort _)

/-- The declared type of `bad` is a type. -/
theorem bad_formed : Typed badRules .nil (closeType (ofEntries numEntries 1) (.const num))
    (.head (.sort (.max (.const 0) (.const 0)))) :=
  .piForm bad_num_typed (LevelTower.IsUniverse.sort _) bad_num_typed (LevelTower.IsUniverse.sort _)
    (LevelTower.Join.sorts _ _)

/-- `zero` is a number in the control's package. -/
theorem bad_zero_arg_typed : Typed badRules Γ (.const zero) (.const num) :=
  .const (rfl : badRules.constantType zero = some (.const num)) bad_num_typed
    (LevelTower.IsUniverse.sort _)

/-- `bad` at its declared type. -/
theorem bad_typed : Typed badRules Γ (.const bad) (.pi (.const num) (.const num)) :=
  .const bad_declared bad_formed (LevelTower.IsUniverse.sort _)

end BadTyping

/-- `bad zero` is a number. -/
theorem bad_zero_typed :
    Typed badRules .nil (appSpine (.const bad) [.const zero]) (.const num) :=
  .appElim bad_typed bad_zero_arg_typed

/-- `bad zero` steps to `junk`. -/
theorem bad_zero_step :
    badRules.computation.step (appSpine (.const bad) [.const zero] : Tm Tower.Head 0)
      (.const junk) :=
  bad_steps ⟨[.const zero], rfl, rfl,
    .split (before := []) (after := []) (args := []) (c := zero) rfl rfl
      (.leaf (.const junk) rfl)⟩

/-- `junk` has no type: it is not declared. -/
theorem junk_untyped {n : Nat} {Γ : Ctx Tower.Head n} {A : Tm Tower.Head n} :
    ¬ Typed badRules Γ (.const junk) A := by
  intro typing
  obtain ⟨type, w, declared, _⟩ := Typed.generation typing
  have undeclared : badRules.constantType junk = none := rfl
  cases undeclared.symm.trans declared

/-- **Without typed leaves subject reduction fails**: the root steps of the
control's package do not preserve typing. -/
theorem bad_not_preserving : ¬ RootPreserving badRules := fun roots =>
  junk_untyped (roots .nil bad_zero_step bad_zero_typed)

/-- The tree of the control is typed in no context of one variable, at no
type: its first leaf has no type. -/
theorem badTree_not_leavesTyped {Γ : Ctx Tower.Head 1} {A : Tm Tower.Head 1} :
    ¬ badTree.LeavesTyped badRules badRoles Γ A := by
  intro typed
  have leafOf : badTree.LeafOf [.var] (Pat.splitAllAt zero 0 [.var] 0) 0 (.const junk) :=
    .split (c := zero) (fields := 0) rfl (.leaf (.const junk) _)
  obtain ⟨Δ, π, leaf, _⟩ := CaseTree.LeavesTyped.typedLeaf leafOf typed rfl
  exact junk_untyped leaf.typed

/-! ## Axiom audit -/

#print axioms declaredRules_sub
#print axioms num_typed
#print axioms unary_formed
#print axioms binary_formed
#print axioms numeral_typed
#print axioms numVar_typed
#print axioms eqn_leavesTyped
#print axioms max_leavesTyped
#print axioms half_leavesTyped
#print axioms pick_leavesTyped
#print axioms eqn_declares
#print axioms max_declares
#print axioms half_declares
#print axioms pick_declares
#print axioms max_succ_succ_equal
#print axioms half_succ_succ_equal
#print axioms rootPreserving_of_facts
#print axioms badRoles_inductive
#print axioms badConstructors
#print axioms badTree_covers
#print axioms badTree_scoped
#print axioms bad_steps
#print axioms badShape
#print axioms bad_zero_typed
#print axioms bad_zero_step
#print axioms junk_untyped
#print axioms bad_not_preserving
#print axioms badTree_not_leavesTyped

end TowerCaseTreesModel

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
