import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Eventually.Normalizer
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Eventually.Comparison
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.DeclarationCheck
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerNumbers
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.DefinitionConsequences
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.RecursorDerivation

/-!
# A qualified package with weak-head normal forms on which the full normalizer never finishes

The numbers with their recursor into the small types, and two functions `b d : num → num`, each
defined by one equation:

    b x ⟶ zero
    d x ⟶ rec (λ _. num) zero (λ y r. d zero) (b zero)

* **The package is qualified** (`qualified`): its four rows (the recursor's two and the two above)
  pass the declaration-time check (`erasing_check`) and its root steps are exactly their instances
  (`erasingPresentation`), so it is a constructor system; its root steps preserve typing (`roots`);
  every declared constant is semantic for the typed equality (`constants`) and for the algorithmic
  equality (`algorithmicConstants`). `b` is semantic by its declaration; `d` because every application
  of `d` to a number reduces by typed weak-head steps to `zero` (`red_d_app`): the scrutinee `b zero`
  reduces to `zero`, and the recursor at `zero` returns `zero`.
* Hence **every typed term has a weak-head normal form** (`Qualified.whnf`).
* **Not strongly normalizing** (`not_typedSN`): `d zero` unfolds into a recursor whose successor case
  contains `d zero` again, without end (`tower_reduces`, `dZero_not_sn`).
* **`d zero` has the normal form `zero`** (`dZero_reduces`, `zero_normal`).
* **The package has one complete root evaluator** (`erasingRoot_complete`, `complete_root_eq`): its
  rows are deterministic, so every complete root evaluator is `erasingRoot`. Statements "for every
  complete root evaluator" below range over that one evaluator.
* **With it, the full normalizer fails on `d zero` at every budget** (`dZero_normalize_none`). At the
  recursor no row applies, since the scrutinee `b zero` is not a constructor form (`no_step_recAt`);
  the normalizer's traversal (`ExecutableReduction.step`: the root, then the children in source order)
  then reaches the successor case before the scrutinee, and unfolds the `d zero` inside it
  (`step_tower`). The failure is that fixed traversal's: a traversal that steps an application's
  argument before its function, with the same root evaluator, reaches `zero` in three steps
  (`argFirst_normalizes`).

So the package meets every hypothesis of `qualified_normalize_eventually` except strong normalization
of typed terms, has weak-head normal forms for all typed terms, and the conclusion fails on the typed
term `d zero` (`separation`): in that theorem about the tree's normalizer, strong normalization cannot
be weakened to weak-head normalization (`whnf_not_enough`). The recursor's row inspects its last
argument, and the normalizer reduces the arguments before it first: the rows are not left-normal.

**What this says of the comparison**: only that the tree's normalizer is not a reducer meeting the
hypothesis of `compare_eventually` on this package (`normalizer_not_whnfEventually`). The comparison's
own strong-normalization hypothesis enters through that one reducer (`sn_compare_eventually`); whether
the comparison over some other reducer succeeds on this package, or needs strong normalization at
all, is not decided here. Whether every typed term of the package has a normal form is not decided
here either.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Eventually
namespace Erasing

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open AlgebraicSchema AlgebraicParallel
open ConstructorSystem (ConstructorPresentation)
open TelescopeAbstraction (closeType applyClosed)
open TowerNumbersModel (num zero succ numRec ctors u mem_zero mem_succ)

/-! ## The rows -/

/-- The two defined functions. -/
def bName : DeclName := .mkSimple "b"
def dName : DeclName := .mkSimple "d"

theorem b_ne_d : bName ≠ dName := by decide
theorem num_ne_b : num ≠ bName := by decide
theorem num_ne_d : num ≠ dName := by decide
theorem zero_ne_b : zero ≠ bName := by decide
theorem zero_ne_d : zero ≠ dName := by decide
theorem succ_ne_b : succ ≠ bName := by decide
theorem succ_ne_d : succ ≠ dName := by decide
theorem rec_ne_b : numRec ≠ bName := by decide
theorem rec_ne_d : numRec ≠ dName := by decide

/-- The motive `λ _. num`. -/
abbrev motive {n : Nat} : Tm Tower.Head n := .lam (.const num)

/-- `b zero`. -/
abbrev bZero {n : Nat} : Tm Tower.Head n := .app (.const bName) (.const zero)

/-- `d zero`. -/
abbrev dZero {n : Nat} : Tm Tower.Head n := .app (.const dName) (.const zero)

/-- The successor case `λ y r. d zero`. -/
abbrev succCase {n : Nat} : Tm Tower.Head n := .lam (.lam dZero)

/-- The recursor at an argument spine. -/
abbrev recAt {n : Nat} (p z s t : Tm Tower.Head n) : Tm Tower.Head n :=
  .app (.app (.app (.app (.const numRec) p) z) s) t

/-- The right side of `d`'s row: `rec (λ _. num) zero (λ y r. d zero) (b zero)`. -/
abbrev unfold {n : Nat} : Tm Tower.Head n := recAt motive (.const zero) succCase bZero

/-- The telescope of one number, the arguments of `b` and `d`. -/
abbrev argTele : Ctx Tower.Head 1 := .snoc .nil (.const num)

/-- The result type `num`. -/
abbrev numResult : Tm Tower.Head 1 := .const num

/-- The computations: the recursor's two rules, `b x ⟶ zero` and `d x ⟶ unfold`. -/
def computations : List (DeclName × RootComputation Tower.Head) :=
  [(numRec, iotaComputation numRec ctors),
   (bName, definitionComputation bName argTele (.const zero)),
   (dName, definitionComputation dName argTele unfold)]

/-- The recursor eliminates into the small types. -/
abbrev lv : LevelExpr Nat := .const 0

/-- The declared types: those of the numbers, and `b d : num → num`. -/
def constantType : DeclName → Option (Tm Tower.Head 0) := fun name =>
  if name = bName ∨ name = dName then some (.pi (.const num) (.const num))
  else TowerNumbersModel.constantType lv name

/-- **The package**: the numbers with their recursor, `b` and `d`. -/
def rules : Rules Tower.Head :=
  { Tower.rules with
    constantType := constantType
    computation := RootComputation.unionAll computations }

/-- The roles: those of the numbers, and `b`, `d` compute at arity one without inspecting. -/
def roles : Roles Tower.Head := fun name =>
  if name = bName ∨ name = dName then .computes 1 .leaf else TowerNumbersModel.roles name

theorem roles_b : roles bName = .computes 1 .leaf := by simp [roles]
theorem roles_d : roles dName = .computes 1 .leaf := by simp [roles]

theorem roles_num : roles num = .inductive ctors := by
  simp [roles, num_ne_b, num_ne_d, TowerNumbersModel.roles_num]

theorem roles_numRec : roles numRec = .computes 4 (.split 3 .constructor fun _ => .leaf) := by
  simp [roles, rec_ne_b, rec_ne_d, TowerNumbersModel.roles_numRec]

theorem roles_zero : roles zero = .constructor 0 := by
  simp [roles, zero_ne_b, zero_ne_d, TowerNumbersModel.roles_zero]

theorem roles_succ : roles succ = .constructor 1 := by
  simp [roles, succ_ne_b, succ_ne_d, TowerNumbersModel.roles_succ]

/-- The only inductive type is `num`. -/
theorem roles_inductive {T : DeclName} {cs : List (DeclName × List (Normalization.Field Tower.Head))}
    (role : roles T = .inductive cs) : T = num ∧ cs = ctors := by
  unfold roles at role
  split at role
  · cases role
  · exact TowerNumbersModel.roles_inductive role

theorem constructorsDeclared : ConstructorsDeclared roles where
  arity := by
    intro T cs k fields role mem
    obtain ⟨rfl, rfl⟩ := roles_inductive role
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact roles_zero
    · exact roles_succ
  distinct := by
    intro T cs role
    obtain ⟨rfl, rfl⟩ := roles_inductive role
    simp only [ctors, List.map_cons, List.map_nil]
    exact List.nodup_cons.mpr ⟨by simp [TowerNumbersModel.zero_ne_succ], List.nodup_singleton _⟩

/-! ## The root steps -/

theorem mem_iota : (numRec, iotaComputation numRec ctors) ∈ computations := List.mem_cons_self ..

theorem mem_b : (bName, definitionComputation bName argTele (.const zero)) ∈ computations :=
  List.mem_cons_of_mem _ (List.mem_cons_self ..)

theorem mem_d : (dName, definitionComputation dName argTele unfold) ∈ computations :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))

theorem iotaZero {n : Nat} (p z s : Tm Tower.Head n) :
    rules.computation.step (recAt p z s (.const zero)) z :=
  RootComputation.step_unionAll mem_iota ⟨p, [z, s], 0, zero, [], [], z, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem iotaSucc {n : Nat} (p z s a : Tm Tower.Head n) :
    rules.computation.step (recAt p z s (.app (.const succ) a)) (.app (.app s a) (recAt p z s a)) :=
  RootComputation.step_unionAll mem_iota
    ⟨p, [z, s], 1, succ, [.recursive], [a], s, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `b x ⟶ zero`. -/
theorem bStep {n : Nat} (a : Tm Tower.Head n) : rules.computation.step (.app (.const bName) a) (.const zero) :=
  RootComputation.step_unionAll mem_b ⟨fun _ => a, rfl, rfl⟩

/-- `d x ⟶ rec (λ _. num) zero (λ y r. d zero) (b zero)`. -/
theorem dStep {n : Nat} (a : Tm Tower.Head n) : rules.computation.step (.app (.const dName) a) unfold :=
  RootComputation.step_unionAll mem_d ⟨fun _ => a, rfl, rfl⟩

/-- **The root steps of the package**: the recursor at `zero` and at a successor, `b x ⟶ zero`, and
`d x ⟶ unfold`. -/
theorem step_cases {n : Nat} {t u : Tm Tower.Head n} (step : rules.computation.step t u) :
    (∃ p z s, t = recAt p z s (.const zero) ∧ u = z) ∨
      (∃ p z s a, t = recAt p z s (.app (.const succ) a) ∧ u = .app (.app s a) (recAt p z s a)) ∨
      (∃ a, t = .app (.const bName) a ∧ u = .const zero) ∨
      (∃ a, t = .app (.const dName) a ∧ u = unfold) := by
  obtain ⟨entry, mem, step⟩ := RootComputation.unionAll_step step
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl
  · obtain ⟨p, ms, i, k, fields, args, m, hms, hi, has, hm, rfl, rfl⟩ := step
    rcases ms with _ | ⟨z, _ | ⟨s, _ | ⟨_, _⟩⟩⟩
    · cases hms
    · cases hms
    · rcases i with _ | _ | i
      · simp only [ctors, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        rcases args with _ | ⟨_, _⟩
        · simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
          subst hm
          exact .inl ⟨p, z, s, rfl, rfl⟩
        · cases has
      · simp only [ctors, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        rcases args with _ | ⟨a, _ | ⟨_, _⟩⟩
        · cases has
        · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hm
          subst hm
          exact .inr (.inl ⟨p, z, s, a, rfl, rfl⟩)
        · cases has
      · cases hi
    · cases hms
  · obtain ⟨σ, rfl, rfl⟩ := step
    exact .inr (.inr (.inl ⟨σ 0, rfl, rfl⟩))
  · obtain ⟨σ, rfl, rfl⟩ := step
    exact .inr (.inr (.inr ⟨σ 0, rfl, rfl⟩))

theorem computations_spine : ∀ entry ∈ computations, SpineShaped roles entry.2 := by
  intro entry mem
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl
  · exact fun _ _ _ step => IotaStep.spine (T := num) roles_num roles_numRec constructorsDeclared step
  · exact definitionComputation_spine roles_b
  · exact definitionComputation_spine roles_d

theorem computations_headed : ∀ entry ∈ computations, HeadedBy entry.1 entry.2 := by
  intro entry mem
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl
  · exact iotaComputation_headed
  · exact definitionComputation_headed
  · exact definitionComputation_headed

theorem computations_deterministic : ∀ entry ∈ computations, Deterministic entry.2 := by
  intro entry mem
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl
  · exact fun _ _ _ _ step step' =>
      IotaStep.deterministic (T := num) roles_num constructorsDeclared step step'
  · exact definitionComputation_deterministic
  · exact definitionComputation_deterministic

theorem computations_distinct : (computations.map Prod.fst).Nodup := by
  decide

/-- The root steps are deterministic. -/
theorem deterministic : Deterministic rules.computation :=
  RootComputation.unionAll_deterministic computations_distinct computations_headed
    computations_deterministic

theorem shape : RootShape rules roles where
  spine := fun step => RootComputation.unionAll_spine computations_spine step
  deterministic := fun step step' => (deterministic step step').symm

/-! ## The normalization setting -/

/-- The tower's level model, for the package. -/
def levels : LevelModel rules ℕ where
  level := (TowerModel.levels (fun _ => 0)).level
  successor := (TowerModel.levels (fun _ => 0)).successor
  universe_typing := (TowerModel.levels (fun _ => 0)).universe_typing
  ground_typing := (TowerModel.levels (fun _ => 0)).ground_typing
  cumulative_universe := (TowerModel.levels (fun _ => 0)).cumulative_universe
  headEq_level := (TowerModel.levels (fun _ => 0)).headEq_level
  join_level := (TowerModel.levels (fun _ => 0)).join_level
  join_exists := (TowerModel.levels (fun _ => 0)).join_exists
  join_upper := (TowerModel.levels (fun _ => 0)).join_upper
  cumulative_refl := (TowerModel.levels (fun _ => 0)).cumulative_refl
  headEq_symm := (TowerModel.levels (fun _ => 0)).headEq_symm
  headEq_trans := (TowerModel.levels (fun _ => 0)).headEq_trans
  universe_decided := (TowerModel.levels (fun _ => 0)).universe_decided

/-- The package's setting over a generic equality `E`: the declarative one is the normalization
setting, the algorithmic one reads the same declarations. -/
def settingWith (E : GenericEquality Tower.Head) : Setting Tower.Head ℕ where
  R := rules
  roles := roles
  E := E
  levels := levels
  shape := shape
  constructors := constructorsDeclared

/-- **The normalization setting of the package.** -/
abbrev setting : Setting Tower.Head ℕ := settingWith (declarative rules)

theorem laws : setting.E.Laws setting.R setting.roles := declarative_laws roles levels

/-! ## The declarations -/

theorem constantType_old {name : DeclName} (hb : name ≠ bName) (hd : name ≠ dName) :
    rules.constantType name = (TowerNumbersModel.rules lv).constantType name := by
  show constantType name = TowerNumbersModel.constantType lv name
  simp [constantType, hb, hd]

theorem declaredNum : rules.constantType num = some (.head u) :=
  (constantType_old num_ne_b num_ne_d).trans (TowerNumbersModel.declaredNum lv)

theorem declaredZero : rules.constantType zero = some (ctorType num []) :=
  (constantType_old zero_ne_b zero_ne_d).trans (TowerNumbersModel.declaredZero lv)

theorem declaredSucc : rules.constantType succ = some (ctorType num [.recursive]) :=
  (constantType_old succ_ne_b succ_ne_d).trans (TowerNumbersModel.declaredSucc lv)

theorem declaredRec : rules.constantType numRec = some (recType num (.sort lv) ctors) :=
  (constantType_old rec_ne_b rec_ne_d).trans (TowerNumbersModel.declaredRec lv)

theorem declaredB : rules.constantType bName = some (.pi (.const num) (.const num)) := by
  show constantType bName = some (.pi (.const num) (.const num))
  simp [constantType]

theorem declaredD : rules.constantType dName = some (.pi (.const num) (.const num)) := by
  show constantType dName = some (.pi (.const num) (.const num))
  simp [constantType]

/-- The numbers' constructors are inside the package. -/
theorem sub₂ : RulesSub TowerNumbersModel.rules₂ rules :=
  ⟨id, id, id, id, id, fun {name type} declared => (by
      simp only [TowerNumbersModel.rules₂] at declared
      split at declared
      · rename_i h
        subst h
        cases declared
        exact declaredNum
      · split at declared
        · rename_i _ h
          subst h
          cases declared
          exact declaredZero
        · split at declared
          · rename_i _ _ h
            subst h
            cases declared
            exact declaredSucc
          · cases declared), fun step => nomatch step⟩

/-- **The package declares the numbers**, over every generic equality. -/
theorem declaresWith (E : GenericEquality Tower.Head) :
    DeclaresInductive (settingWith E) (constantFreeRules rules) TowerNumbersModel.rules₁
      TowerNumbersModel.rules₂ num u ctors numRec (.sort lv) where
  role := roles_num
  recRole := roles_numRec
  hu := .sort _
  hv := .sort _
  sub₀ := RulesSub.constantFree _
  sub₁ := ⟨id, id, id, id, id, fun {name type} declared => (by
      simp only [TowerNumbersModel.rules₁] at declared
      split at declared
      · rename_i h
        subst h
        cases declared
        exact declaredNum
      · cases declared), fun step => nomatch step⟩
  sub₂ := sub₂
  semantic₀ := fun declared => nomatch declared
  stage₁ := (TowerNumbersModel.declares lv fun _ => 0).stage₁
  stage₂ := (TowerNumbersModel.declares lv fun _ => 0).stage₂
  declared := declaredNum
  ctorDeclared := by
    intro k fields mem
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact declaredZero
    · exact declaredSucc
  recDeclared := declaredRec
  fieldTyped := (TowerNumbersModel.declares lv fun _ => 0).fieldTyped
  ctorTyped := (TowerNumbersModel.declares lv fun _ => 0).ctorTyped
  recTyped := (TowerNumbersModel.declares lv fun _ => 0).recTyped
  iota := fun hms hi has hm =>
    RootComputation.step_unionAll mem_iota ⟨_, _, _, _, _, _, _, hms, hi, has, hm, rfl, rfl⟩

/-! ## Typing -/

section Typing

variable {m : Nat} {Δ : Ctx Tower.Head m}

theorem num_typed : Typed rules Δ (.const num) (.head u) :=
  .const declaredNum (.headType (.sort _)) (.sort _)

theorem zero_typed : Typed rules Δ (.const zero) (.const num) :=
  .const declaredZero num_typed (.sort _)

theorem succ_typed : Typed rules Δ (.const succ) (.pi (.const num) (.const num)) :=
  .const declaredSucc (.piForm num_typed (.sort _) num_typed (.sort _) (.sorts _ _)) (.sort _)

theorem b_typed : Typed rules Δ (.const bName) (.pi (.const num) (.const num)) :=
  .const declaredB (.piForm num_typed (.sort _) num_typed (.sort _) (.sorts _ _)) (.sort _)

theorem d_typed : Typed rules Δ (.const dName) (.pi (.const num) (.const num)) :=
  .const declaredD (.piForm num_typed (.sort _) num_typed (.sort _) (.sorts _ _)) (.sort _)

theorem bZero_typed : Typed rules Δ bZero (.const num) :=
  .appElim (A := .const num) (B := .const num) b_typed zero_typed

/-- `d zero : num`. -/
theorem dZero_typed : Typed rules Δ dZero (.const num) :=
  .appElim (A := .const num) (B := .const num) d_typed zero_typed

theorem rec_typed {n : Nat} {Γ : Ctx Tower.Head n} :
    Typed rules Γ (.const numRec) (liftClosed (recType num (.sort lv) ctors)) := by
  obtain ⟨w, hw, typed⟩ := (declaresWith (declarative rules)).toRecursor.recTyped
  exact .const declaredRec typed hw

theorem motiveTy_typed :
    Typed rules Δ (.pi (.const num) (.head (.sort lv))) (.head (.sort (.max (.const 0) (.succ lv)))) :=
  .piForm num_typed (.sort _) (.headType (.sort _)) (.sort _) (.sorts _ _)

/-- The motive `λ _. num` is a family of small types. -/
theorem motive_typed : Typed rules Δ motive (.pi (.const num) (.head (.sort lv))) :=
  .lamIntro motiveTy_typed (.sort _) num_typed

/-- The motive at a number is `num`. -/
theorem motive_beta {t : Tm Tower.Head m} (typed : Typed rules Δ t (.const num)) :
    Equal rules Δ (.app motive t) (.const num) (.head (.sort lv)) :=
  .betaPi motiveTy_typed (.sort _) num_typed typed

theorem zeroMethod : Typed rules Δ (.const zero) (.app motive (.const zero)) :=
  .conv zero_typed (.symm (motive_beta zero_typed)) (.sort _)

/-- The successor case `λ y r. d zero : Π (x : num). motive x → motive (succ x)`. -/
theorem succMethod :
    Typed rules Δ succCase
      (.pi (.const num) (.pi (.app motive (.var 0)) (.app motive (.app (.const succ) (.var 1))))) := by
  have x1 : Typed rules (.snoc (.snoc Δ (.const num)) (.app motive (.var 0))) (.var 1) (.const num) :=
    .var 1
  have succX : Typed rules (.snoc (.snoc Δ (.const num)) (.app motive (.var 0)))
      (.app (.const succ) (.var 1)) (.const num) :=
    .appElim succ_typed x1
  have body : Typed rules (.snoc (.snoc Δ (.const num)) (.app motive (.var 0))) dZero
      (.app motive (.app (.const succ) (.var 1))) :=
    .conv dZero_typed (.symm (motive_beta succX)) (.sort _)
  have x0 : Typed rules (.snoc Δ (.const num)) (.var 0) (.const num) := .var 0
  have innerPi : Typed rules (.snoc Δ (.const num))
      (.pi (.app motive (.var 0)) (.app motive (.app (.const succ) (.var 1))))
      (.head (.sort (.max lv lv))) :=
    .piForm (.appElim motive_typed x0) (.sort _) (.appElim motive_typed succX) (.sort _) (.sorts _ _)
  have outerPi : Typed rules Δ
      (.pi (.const num) (.pi (.app motive (.var 0)) (.app motive (.app (.const succ) (.var 1)))))
      (.head (.sort (.max (.const 0) (.max lv lv)))) :=
    .piForm num_typed (.sort _) innerPi (.sort _) (.sorts _ _)
  exact .lamIntro outerPi (.sort _) (.lamIntro innerPi (.sort _) body)

/-- The recursor of the unfolding, at a typed scrutinee. -/
theorem recAt_typed {t : Tm Tower.Head m} (typed : Typed rules Δ t (.const num)) :
    Typed rules Δ (recAt motive (.const zero) succCase t) (.app motive t) :=
  recApp_typed rec_typed motive_typed (.cons zeroMethod (.cons succMethod .nil)) typed

theorem recAt_typed_num {t : Tm Tower.Head m} (typed : Typed rules Δ t (.const num)) :
    Typed rules Δ (recAt motive (.const zero) succCase t) (.const num) :=
  .conv (recAt_typed typed) (motive_beta typed) (.sort _)

/-- The motive and the two methods, as a substitution of the recursor's prefix. -/
abbrev methods {k : Nat} : Sub Tower.Head (ctors.length + 1) k :=
  argsSub (ctors.length + 1) [motive, .const zero, succCase]

theorem methods_typed : SubstMor rules (recPrefix num (.sort lv) ctors) Δ methods :=
  substMor_recPrefix motive_typed (.cons zeroMethod (.cons succMethod .nil)) ctors.length (Nat.le_refl _)

theorem recHead_methods :
    recHead numRec num (.sort lv) ctors (methods : Sub Tower.Head (ctors.length + 1) m) =
      .app (.app (.app (.const numRec) motive) (.const zero)) succCase := by
  rw [recHead, applyClosed_eq_appSpine]
  exact congrArg (appSpine (.const numRec))
    (telescopeArgs_argsSub (recEntry num (.sort lv) ctors) (ctors.length + 1)
      [motive, .const zero, succCase] rfl)

end Typing

/-! ## `d` applied to a number reaches `zero` by typed weak-head steps -/

section Reduction

variable {m : Nat} {Δ : Ctx Tower.Head m}

theorem red_bZero : RedTm rules roles Δ bZero (.const zero) (.const num) :=
  RedTm.root (bStep _) bZero_typed zero_typed

/-- The scrutinee `b zero ⟶ zero` inside the recursor, typed. -/
theorem red_scrutinee :
    RedTm rules roles Δ unfold (recAt motive (.const zero) succCase (.const zero)) (.const num) := by
  have h := (declaresWith (declarative rules)).toRecursor.scrutinee_red (methods_typed (Δ := Δ))
    (red_bZero (Δ := Δ)) (X := .const num) ⟨_, .sort _, motive_beta bZero_typed⟩
    ⟨_, .sort _, motive_beta zero_typed⟩
  rw [recHead_methods] at h
  exact h

/-- The recursor at `zero` returns its zero case. -/
theorem red_iota :
    RedTm rules roles Δ (recAt motive (.const zero) succCase (.const zero)) (.const zero) (.const num) :=
  RedTm.root (iotaZero _ _ _) (recAt_typed_num zero_typed) zero_typed

/-- **`d a` reduces to `zero` by typed weak-head steps, for every typed application.** -/
theorem red_d_app {a : Tm Tower.Head m} (typed : Typed rules Δ (.app (.const dName) a) (.const num)) :
    RedTm rules roles Δ (.app (.const dName) a) (.const zero) (.const num) :=
  ((RedTm.root (dStep a) typed (recAt_typed_num bZero_typed)).trans red_scrutinee).trans red_iota

end Reduction

/-! ## Every declared constant is semantic, over every generic equality with the model's laws -/

section Semantics

variable {E : GenericEquality Tower.Head}
  (lawsE : (settingWith E).E.Laws (settingWith E).R (settingWith E).roles)

theorem num_typed₂ {n : Nat} {Γ : Ctx Tower.Head n} :
    Typed TowerNumbersModel.rules₂ Γ (.const num) (.head u) :=
  .const (show TowerNumbersModel.rules₂.constantType num = some (.head u) from rfl) (.headType (.sort _))
    (.sort _)

include lawsE in
/-- **`b` is declared by one equation**, `b x ⟶ zero`, typed over the numbers' constructors. -/
theorem declaresB :
    DeclaresDefinition (settingWith E) TowerNumbersModel.rules₂ bName argTele numResult (.const zero) where
  role := roles_b
  declared := declaredB
  sub₀ := sub₂
  semantic₀ := (declaresWith E).semantic₂ lawsE
  typed := ⟨_, .sort _, .piForm num_typed₂ (.sort _) num_typed₂ (.sort _) (.sorts _ _)⟩
  body := .const (show TowerNumbersModel.rules₂.constantType zero = some (ctorType num []) from rfl)
    num_typed₂ (.sort _)
  rule := fun σ => RootComputation.step_unionAll mem_b ⟨σ, rfl, rfl⟩

include lawsE in
/-- **The full application of `d` is valid**: at every valid argument it reduces to `zero`. -/
theorem d_full : ValidTm (settingWith E) argTele (applyClosed argTele ids (.const dName)) numResult := by
  obtain ⟨⟨w, hw, validType⟩, -⟩ := (declaresB lawsE).valid lawsE
  obtain ⟨-, validC⟩ := ValidTy.telescope lawsE argTele (validType.validTy lawsE hw)
  have toZero : ∀ {k : Nat} {Γ : Ctx Tower.Head k} {σ : Sub Tower.Head 1 k},
      ValidSubst (settingWith E) argTele Γ σ →
      RedTm rules roles Γ (.app (.const dName) (σ 0)) (.const zero) (.const num) := fun vσ =>
    red_d_app (Typed.telescope_apply (X := numResult) (vσ.substMor lawsE) d_typed)
  refine ⟨validC, fun {k Γ σ} vσ P r => ?_, fun {k Γ σ σ'} vσ vσ' _ P r => ?_⟩
  · have zeroRed : P.redTm (.const zero) := (declaresWith E).ctor_semantic lawsE mem_zero vσ.formed r
    exact (r.redTm_expand (toZero vσ) zeroRed).1
  · have zeroRed : P.redTm (.const zero) := (declaresWith E).ctor_semantic lawsE mem_zero vσ.formed r
    have zeroEq : P.eqTm (.const zero) (.const zero) :=
      (r.redTm_expand (RedTm.refl zero_typed) zeroRed).2
    exact r.eqTm_expand lawsE (toZero vσ) (toZero vσ') zeroEq

include lawsE in
/-- **`d` is semantic.** -/
theorem d_semantic : SemanticConstant (settingWith E) dName (closeType argTele numResult) := by
  obtain ⟨⟨w, hw, validType⟩, -⟩ := (declaresB lawsE).valid lawsE
  intro k Γ formed P r
  exact SemanticConstant.of_telescope lawsE (name := dName) (k := 1) (.inr ⟨_, roles_d⟩) (Θ := argTele)
    (C := numResult) d_typed (validType.validTy lawsE hw) (d_full lawsE) formed r

include lawsE in
/-- **Every declared constant of the package is semantic.** -/
theorem constantsWith : SemanticConstants (settingWith E) := by
  intro name type w declared _ _ k Γ formed P r
  by_cases hb : name = bName
  · subst hb
    rw [show (settingWith E).R.constantType bName = some (closeType argTele numResult) from declaredB]
      at declared
    cases declared
    exact (declaresB lawsE).semantic lawsE formed r
  by_cases hd : name = dName
  · subst hd
    rw [show (settingWith E).R.constantType dName = some (closeType argTele numResult) from declaredD]
      at declared
    cases declared
    exact d_semantic lawsE formed r
  have decl := declaresWith E
  rw [show (settingWith E).R.constantType name = (TowerNumbersModel.rules lv).constantType name from
    constantType_old hb hd] at declared
  change TowerNumbersModel.constantType lv name = some type at declared
  unfold TowerNumbersModel.constantType at declared
  split at declared
  · rename_i h
    subst h
    cases declared
    exact decl.type_semantic lawsE formed r
  · split at declared
    · rename_i _ h
      subst h
      cases declared
      exact decl.ctor_semantic lawsE mem_zero formed r
    · split at declared
      · rename_i _ _ h
        subst h
        cases declared
        exact decl.ctor_semantic lawsE mem_succ formed r
      · split at declared
        · rename_i _ _ _ h
          subst h
          cases declared
          exact decl.rec_semantic lawsE formed r
        · cases declared

end Semantics

/-! ## The package is qualified -/

/-- Every declared constant is semantic for the typed equality. -/
theorem constants : SemanticConstants setting := constantsWith laws

/-- The facts about the weak-head forms of the package's types. -/
theorem facts : FormFacts rules roles := .ofSemantic (S := setting) laws constants

/-- The root steps preserve typing. -/
theorem roots : RootPreserving rules := by
  intro n Γ l r A formed step typing
  obtain ⟨entry, mem, step⟩ := RootComputation.unionAll_step step
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl
  · exact (declaresWith (declarative rules)).toRecursor.step_preserves facts (RulesSub.refl _) formed
      step typing
  · obtain ⟨σ, rfl, rfl⟩ := step
    exact (declaresB laws).rule_preserves facts (RulesSub.refl _) formed σ typing
  · obtain ⟨σ, rfl, rfl⟩ := step
    obtain ⟨mor, -, le⟩ := Typed.telescope_inv (S := setting) facts formed argTele numResult declaredD
      typing
    exact Typed.subsume (Typed.substitute (recAt_typed_num (Δ := argTele) bZero_typed) mor) le

/-- Head equality steps preserve typing. -/
theorem heads : HeadPreserving rules := by
  intro n Γ h h' A same typing
  obtain ⟨w, headTyping, le⟩ := Typed.generation typing
  cases headTyping with
  | legacyGround =>
      cases h' with
      | legacyGround => exact Typed.subsume (.headType .legacyGround) le
      | sort _ => exact same.elim
  | sort l =>
      cases h' with
      | legacyGround => exact same.elim
      | sort r =>
          have raise : rules.cumulative (.sort (.succ r)) (.sort (.succ l)) := by
            intro ν
            show LevelExpr.eval ν r + 1 ≤ LevelExpr.eval ν l + 1
            have := same ν
            omega
          exact Typed.subsume (.cumul (.headType (.sort r)) raise) le

theorem algebra : CumulativeAlgebra rules where
  trans := TowerModel.algebra.trans
  same_left := TowerModel.algebra.same_left
  same_right := TowerModel.algebra.same_right
  join_least := TowerModel.algebra.join_least

/-- Head equality is decided. -/
theorem decideHeads (h h' : Tower.Head) : HeadSame rules h h' ∨ ¬ HeadSame rules h h' := by
  rcases Decidable.em (Tower.HeadEq h h') with same | different
  · exact .inl (.inr same)
  · rcases Decidable.em (h = h') with equal | unequal
    · exact .inl (.inl equal)
    · exact .inr fun same => same.elim unequal different

theorem lawsA :
    (algorithmicSetting setting).E.Laws (algorithmicSetting setting).R (algorithmicSetting setting).roles :=
  algorithmicSetting_laws (S := setting) laws constants roots heads algebra

/-- **Every declared constant is semantic for the algorithmic equality**: the same declarations, read
in the algorithmic setting. -/
theorem algorithmicConstants : SemanticConstants (algorithmicSetting setting) :=
  constantsWith (E := algorithmic rules roles) lawsA

/-- The four rows: the recursor at `zero` and at a successor, `b x ⟶ zero`, `d x ⟶ unfold`. -/
def erasingEquations : SchemaTable Tower.Head :=
  [⟨3, (recAt (.var 2) (.var 1) (.var 0) (.const zero), .var 1)⟩,
   ⟨4, (recAt (.var 3) (.var 2) (.var 1) (.app (.const succ) (.var 0)),
      .app (.app (.var 1) (.var 0)) (recAt (.var 3) (.var 2) (.var 1) (.var 0)))⟩,
   ⟨1, (.app (.const bName) (.var 0), .const zero)⟩,
   ⟨1, (.app (.const dName) (.var 0), unfold)⟩]

theorem listed (i : Nat) (h : i < erasingEquations.length) {arity : Nat}
    {left right : Tm Tower.Head arity} (same : erasingEquations[i] = ⟨arity, (left, right)⟩) :
    erasingEquations.family left right := by
  change (⟨arity, (left, right)⟩ : Σ arity : Nat, Tm Tower.Head arity × Tm Tower.Head arity) ∈
    erasingEquations
  rw [← same]
  exact List.getElem_mem h

/-- Every instance of a row is a root step. -/
theorem erasing_sound {arity n : Nat} {left right : Tm Tower.Head arity}
    (rule : erasingEquations.family left right) (σ : Sub Tower.Head arity n) :
    rules.computation.step (subst σ left) (subst σ right) := by
  change (⟨arity, (left, right)⟩ : Σ arity : Nat, Tm Tower.Head arity × Tm Tower.Head arity) ∈
    erasingEquations at rule
  simp only [erasingEquations, List.mem_cons, List.not_mem_nil, or_false] at rule
  rcases rule with same | same | same | same <;> cases same
  · exact iotaZero (σ 2) (σ 1) (σ 0)
  · exact iotaSucc (σ 3) (σ 2) (σ 1) (σ 0)
  · exact bStep (σ 0)
  · exact dStep (σ 0)

/-- Every root step is an instance of a row. -/
theorem erasing_cover {n : Nat} {l r : Tm Tower.Head n} (step : rules.computation.step l r) :
    ∃ (arity : Nat) (left right : Tm Tower.Head arity) (σ : Sub Tower.Head arity n),
      erasingEquations.family left right ∧ subst σ left = l ∧ subst σ right = r := by
  rcases step_cases step with ⟨p, z, s, rfl, rfl⟩ | ⟨p, z, s, a, rfl, rfl⟩ | ⟨a, rfl, rfl⟩ | ⟨a, rfl, rfl⟩
  · exact ⟨3, _, _, consSub s (consSub _ (consSub p Fin.elim0)), listed 0 (by decide) rfl, rfl, rfl⟩
  · exact ⟨4, _, _, consSub a (consSub s (consSub z (consSub p Fin.elim0))), listed 1 (by decide) rfl,
      rfl, rfl⟩
  · exact ⟨1, _, _, fun _ => a, listed 2 (by decide) rfl, rfl, rfl⟩
  · exact ⟨1, _, _, fun _ => a, listed 3 (by decide) rfl, rfl, rfl⟩

/-- **The package's root steps, presented by its rows.** -/
def erasingPresentation : SchemaPresentation rules where
  schema := erasingEquations.family
  sound := erasing_sound
  cover := erasing_cover

def erasingDefined (name : DeclName) : Bool := name == numRec || name == bName || name == dName

def erasingArity (name : DeclName) : Nat := if name == numRec then 4 else 1

/-- **The rows pass the declaration-time check.** -/
theorem erasing_check : DeclarationCheck.checkTable erasingDefined erasingArity erasingEquations = true := by
  decide

/-- **The package as a definition by constructor patterns.** -/
def erasingConstructors : ConstructorPresentation rules where
  presentation := erasingPresentation
  system := DeclarationCheck.checkedSystem erasing_check
  same _ _ := Iff.rfl
  symmetric := LevelTower.headEq_symmetric

/-- **The package is qualified.** -/
theorem qualified : Qualified setting where
  laws := laws
  constructors := ⟨erasingConstructors⟩
  constants := constants
  roots := roots
  heads := heads
  algebra := algebra
  algorithmicConstants := algorithmicConstants
  decideHeads := decideHeads

/-! ## Not strongly normalizing, with the normal form `zero` -/

/-- `d zero`, and the recursor around it `k` times, `d zero` under the two binders of the successor
case. -/
def tower : Nat → {n : Nat} → Tm Tower.Head n
  | 0, _ => dZero
  | k + 1, _ => recAt motive (.const zero) (.lam (.lam (tower k))) bZero

/-- Each term of the tower steps to the next, unfolding its innermost `d zero`. -/
theorem tower_reduces : ∀ k {n : Nat},
    StrongNormalization.Reduces rules (tower k : Tm Tower.Head n) (tower (k + 1))
  | 0, _ => .root (dStep _)
  | k + 1, _ => .congAppFun (.congAppArg (.congLam (.congLam (tower_reduces k))))

/-- **`d zero` is not strongly normalizing.** -/
theorem dZero_not_sn : ¬ StrongNormalization.SN rules (dZero : Tm Tower.Head 0) := by
  intro sn
  have never : ∀ t, StrongNormalization.SN rules t → ∀ k, (tower k : Tm Tower.Head 0) = t → False := by
    intro t accessible
    induction accessible with
    | intro t _ ih =>
        intro k same
        subst same
        exact ih (tower (k + 1)) (tower_reduces k) (k + 1) rfl
  exact never _ sn 0 rfl

/-- **The package is not strongly normalizing on typed terms.** -/
theorem not_typedSN : ¬ TypedSN rules := fun sn => dZero_not_sn (sn .nil dZero_typed)

/-- **`d zero` reduces to `zero`**: unfold `d`, reduce the scrutinee `b zero`, then the recursor's row. -/
theorem dZero_reduces : StrongNormalization.ReducesStar rules (dZero : Tm Tower.Head 0) (.const zero) :=
  ((Relation.ReflTransGen.single (.root (dStep _))).tail (.congAppArg (.root (bStep _)))).tail
    (.root (iotaZero _ _ _))

/-! ## Where no row applies -/

theorem no_step_lam {n : Nat} {X : Tm Tower.Head (n + 1)} (u : Tm Tower.Head n) :
    ¬ rules.computation.step (.lam X) u := by
  intro step
  rcases step_cases step with ⟨p, z, s, same, -⟩ | ⟨p, z, s, a, same, -⟩ | ⟨a, same, -⟩ | ⟨a, same, -⟩ <;>
    cases same

theorem no_step_const {n : Nat} (c : DeclName) (u : Tm Tower.Head n) :
    ¬ rules.computation.step (.const c) u := by
  intro step
  rcases step_cases step with ⟨p, z, s, same, -⟩ | ⟨p, z, s, a, same, -⟩ | ⟨a, same, -⟩ | ⟨a, same, -⟩ <;>
    cases same

/-- **`zero` is a normal form**: no step leaves it. -/
theorem zero_normal {n : Nat} :
    ContextualDependentExecutableJoin.Normal rules (.const zero : Tm Tower.Head n) := by
  intro u step
  generalize source : (.const zero : Tm Tower.Head n) = t at step
  cases step with
  | root h =>
      subst source
      exact no_step_const zero u h
  | _ => cases source

theorem no_step_recMotive {n : Nat} (u : Tm Tower.Head n) :
    ¬ rules.computation.step (.app (.const numRec) motive) u := by
  intro step
  rcases step_cases step with ⟨p, z, s, same, -⟩ | ⟨p, z, s, a, same, -⟩ | ⟨a, same, -⟩ | ⟨a, same, -⟩
  · cases same
  · cases same
  · exact rec_ne_b (Tm.const.inj (Tm.app.inj same).1)
  · exact rec_ne_d (Tm.const.inj (Tm.app.inj same).1)

theorem no_step_prefix {n : Nat} (u : Tm Tower.Head n) :
    ¬ rules.computation.step (.app (.app (.const numRec) motive) (.const zero)) u := by
  intro step
  rcases step_cases step with ⟨p, z, s, same, -⟩ | ⟨p, z, s, a, same, -⟩ | ⟨a, same, -⟩ | ⟨a, same, -⟩ <;>
    cases same

theorem no_step_three {n : Nat} {X : Tm Tower.Head n} (u : Tm Tower.Head n) :
    ¬ rules.computation.step (.app (.app (.app (.const numRec) motive) (.const zero)) X) u := by
  intro step
  rcases step_cases step with ⟨p, z, s, same, -⟩ | ⟨p, z, s, a, same, -⟩ | ⟨a, same, -⟩ | ⟨a, same, -⟩ <;>
    cases same

/-- **No row applies at the recursor whose scrutinee is `b zero`**: `b zero` is not a constructor
form. -/
theorem no_step_recAt {n : Nat} {s : Tm Tower.Head n} (u : Tm Tower.Head n) :
    ¬ rules.computation.step (recAt motive (.const zero) s bZero) u := by
  intro step
  rcases step_cases step with ⟨p, z, s', same, -⟩ | ⟨p, z, s', a, same, -⟩ | ⟨a, same, -⟩ | ⟨a, same, -⟩
  · cases same
  · exact succ_ne_b (Tm.const.inj (Tm.app.inj (Tm.app.inj same).2).1).symm
  · cases same
  · cases same

/-! ## The full normalizer, for every complete root evaluator -/

open ExecutableReduction

/-- Where no row applies, every root evaluator proposes nothing. -/
theorem root_none (root : RootEvaluator rules) {n : Nat} {t : Tm Tower.Head n}
    (noStep : ∀ u, ¬ rules.computation.step t u) : root t = none := by
  cases h : root t with
  | none => rfl
  | some next => exact absurd next.property (noStep next.val)

theorem root_lam (root : RootEvaluator rules) {n : Nat} (X : Tm Tower.Head (n + 1)) :
    root (.lam X) = none :=
  root_none root no_step_lam

theorem root_const (root : RootEvaluator rules) {n : Nat} (c : DeclName) :
    root (.const c : Tm Tower.Head n) = none :=
  root_none root (no_step_const c)

theorem root_recMotive (root : RootEvaluator rules) {n : Nat} :
    root (.app (.const numRec) motive : Tm Tower.Head n) = none :=
  root_none root no_step_recMotive

theorem root_prefix (root : RootEvaluator rules) {n : Nat} :
    root (.app (.app (.const numRec) motive) (.const zero) : Tm Tower.Head n) = none :=
  root_none root no_step_prefix

theorem root_three (root : RootEvaluator rules) {n : Nat} (X : Tm Tower.Head n) :
    root (.app (.app (.app (.const numRec) motive) (.const zero)) X) = none :=
  root_none root no_step_three

theorem root_recAt (root : RootEvaluator rules) {n : Nat} (s : Tm Tower.Head n) :
    root (recAt motive (.const zero) s bZero) = none :=
  root_none root no_step_recAt

/-- At `d zero` a complete root evaluator proposes `d`'s row. -/
theorem root_dZero (root : RootEvaluator rules) (complete : RootComplete rules root) {n : Nat} :
    (root (dZero : Tm Tower.Head n)).map Subtype.val = some unfold := by
  cases h : root (dZero : Tm Tower.Head n) with
  | none => exact absurd (dStep (.const zero)) (complete _ h unfold)
  | some next =>
      simp only [Option.map_some, Option.some.injEq]
      exact deterministic (dStep (.const zero)) next.property

theorem step_const (root : RootEvaluator rules) {n : Nat} (c : DeclName) :
    step rules root (.const c : Tm Tower.Head n) = none := by
  rw [ExecutableReduction.step]
  simp only [root_const root c]

theorem step_motive (root : RootEvaluator rules) {n : Nat} :
    step rules root (motive : Tm Tower.Head n) = none := by
  rw [ExecutableReduction.step]
  simp only [root_lam root]
  rw [step_const root num]

theorem step_prefix (root : RootEvaluator rules) {n : Nat} :
    step rules root (.app (.app (.const numRec) motive) (.const zero) : Tm Tower.Head n) = none := by
  have inner : step rules root (.app (.const numRec) motive : Tm Tower.Head n) = none := by
    rw [ExecutableReduction.step]
    simp only [root_recMotive root]
    rw [step_const root numRec, step_motive root]
    · intro body same
      cases same
  rw [ExecutableReduction.step]
  simp only [root_prefix root]
  rw [inner, step_const root zero]
  · intro body same
    cases same

/-- Under the two binders of the successor case, the normalizer steps inside. -/
theorem step_lamLam (root : RootEvaluator rules) {n : Nat} {X : Tm Tower.Head (n + 2)}
    {next : StepResult rules X} (stepped : step rules root X = some next) :
    (step rules root (.lam (.lam X) : Tm Tower.Head n)).map Subtype.val =
      some (.lam (.lam next.val)) := by
  rw [ExecutableReduction.step]
  simp only [root_lam root]
  rw [ExecutableReduction.step]
  simp only [root_lam root, stepped, Option.map_some]

/-- **At the recursor around a term, the normalizer steps inside the successor case**: no row applies
at the root, and the arguments before the scrutinee come first. -/
theorem step_recAt (root : RootEvaluator rules) {n : Nat} {X : Tm Tower.Head (n + 2)}
    {next : StepResult rules X} (stepped : step rules root X = some next) :
    (step rules root (recAt motive (.const zero) (.lam (.lam X)) bZero)).map Subtype.val =
      some (recAt motive (.const zero) (.lam (.lam next.val)) bZero) := by
  have inner := step_lamLam root stepped
  cases hs : step rules root (.lam (.lam X) : Tm Tower.Head n) with
  | none =>
      rw [hs] at inner
      cases inner
  | some next' =>
      rw [hs] at inner
      simp only [Option.map_some, Option.some.injEq] at inner
      have function : (step rules root
          (.app (.app (.app (.const numRec) motive) (.const zero)) (.lam (.lam X)) : Tm Tower.Head n)).map
            Subtype.val =
          some (.app (.app (.app (.const numRec) motive) (.const zero)) (.lam (.lam next.val))) := by
        rw [ExecutableReduction.step, root_three root]
        rw [step_prefix root]
        simp only [hs, Option.map_some, inner]
        intro body same
        cases same
      cases hf : step rules root
          (.app (.app (.app (.const numRec) motive) (.const zero)) (.lam (.lam X)) : Tm Tower.Head n) with
      | none =>
          rw [hf] at function
          cases function
      | some next'' =>
          rw [hf] at function
          simp only [Option.map_some, Option.some.injEq] at function
          rw [ExecutableReduction.step, root_recAt root]
          simp only [hf, Option.map_some, function]
          intro body same
          cases same

/-- **Each step of the normalizer unfolds the innermost `d zero`.** -/
theorem step_tower (root : RootEvaluator rules) (complete : RootComplete rules root) : ∀ k {n : Nat},
    (step rules root (tower k : Tm Tower.Head n)).map Subtype.val = some (tower (k + 1))
  | 0, n => by
      show (step rules root (dZero : Tm Tower.Head n)).map Subtype.val = some unfold
      have h := root_dZero root complete (n := n)
      cases hr : root (dZero : Tm Tower.Head n) with
      | none =>
          rw [hr] at h
          cases h
      | some next =>
          rw [hr] at h
          simp only [Option.map_some, Option.some.injEq] at h
          rw [ExecutableReduction.step, hr]
          · simp only [Option.map_some, h]
          · intro body same
            cases same
  | k + 1, n => by
      have ih := step_tower root complete k (n := n + 2)
      cases h : step rules root (tower k : Tm Tower.Head (n + 2)) with
      | none =>
          rw [h] at ih
          cases ih
      | some next =>
          rw [h] at ih
          simp only [Option.map_some, Option.some.injEq] at ih
          have stepped := step_recAt root h
          rw [ih] at stepped
          exact stepped

/-- The normalizer returns nothing from any term of the tower, at any budget. -/
theorem tower_normalize_none (root : RootEvaluator rules) (complete : RootComplete rules root) :
    ∀ (fuel k : Nat), normalize rules root fuel (tower k : Tm Tower.Head 0) = none
  | 0, _ => rfl
  | fuel + 1, k => by
      have stepped := step_tower root complete k (n := 0)
      cases h : step rules root (tower k : Tm Tower.Head 0) with
      | none =>
          rw [h] at stepped
          cases stepped
      | some next =>
          rw [h] at stepped
          obtain ⟨v, pv⟩ := next
          simp only [Option.map_some, Option.some.injEq] at stepped
          subst stepped
          rw [ExecutableReduction.normalize, h]
          simp only [tower_normalize_none root complete fuel (k + 1)]

/-- **For every complete root evaluator, the full normalizer fails on `d zero` at every budget.** -/
theorem dZero_normalize_none (root : RootEvaluator rules) (complete : RootComplete rules root)
    (fuel : Nat) : normalize rules root fuel (dZero : Tm Tower.Head 0) = none :=
  tower_normalize_none root complete fuel 0

/-! ## A complete root evaluator -/

/-- **The root evaluator**: `b`'s and `d`'s rows, and the recursor at `zero` and at a successor. -/
def erasingRoot : RootEvaluator rules := fun {_} t => match t with
  | .app (.const c) a =>
      if hb : c = bName then some ⟨.const zero, by subst hb; exact bStep a⟩
      else if hd : c = dName then some ⟨unfold, by subst hd; exact dStep a⟩
      else none
  | .app (.app (.app (.app (.const c) p) z) s) (.const k) =>
      if h : c = numRec ∧ k = zero then
        some ⟨z, by obtain ⟨rfl, rfl⟩ := h; exact iotaZero p z s⟩
      else none
  | .app (.app (.app (.app (.const c) p) z) s) (.app (.const k) a) =>
      if h : c = numRec ∧ k = succ then
        some ⟨.app (.app s a) (recAt p z s a), by obtain ⟨rfl, rfl⟩ := h; exact iotaSucc p z s a⟩
      else none
  | _ => none

/-- **The root evaluator is complete.** -/
theorem erasingRoot_complete : RootComplete rules erasingRoot := by
  intro n t none_ u step
  rcases step_cases step with ⟨p, z, s, rfl, -⟩ | ⟨p, z, s, a, rfl, -⟩ | ⟨a, rfl, -⟩ | ⟨a, rfl, -⟩
  · simp [erasingRoot] at none_
  · simp [erasingRoot] at none_
  · simp [erasingRoot] at none_
  · simp [erasingRoot, b_ne_d.symm] at none_

/-- **Every complete root evaluator of the package is `erasingRoot`**: the rows are deterministic, so a
complete evaluator proposes exactly the one root step there is. -/
theorem complete_root_eq (root : RootEvaluator rules) (complete : RootComplete rules root)
    {n : Nat} (t : Tm Tower.Head n) : root t = erasingRoot t := by
  cases h₁ : root t with
  | none =>
      cases h₂ : erasingRoot t with
      | none => rfl
      | some next => exact absurd next.property (complete t h₁ next.val)
  | some next =>
      cases h₂ : erasingRoot t with
      | none => exact absurd next.property (erasingRoot_complete t h₂ next.val)
      | some next' =>
          have same := deterministic next.property next'.property
          exact congrArg some (Subtype.ext (by first | exact same | exact same.symm))

/-! ## The traversal is what fails: stepping arguments first reaches the normal form -/

section ArgumentsFirst

variable {Head : Type}

/-- **A traversal that steps an application's argument before its function**: the root first, as in
`ExecutableReduction.step`; at an application that is not a β-redex, the argument, then the function;
every other former as in `ExecutableReduction.step`, with the same order of children. -/
def stepArgFirst (R : Rules Head) (root : RootEvaluator R) :
    {n : Nat} → (term : Tm Head n) → Option (StepResult R term)
  | _, term => match root term with
    | some next => some ⟨next.val, .root next.property⟩
    | none => match term with
      | .var _ | .const _ | .head _ => none
      | .pi domain body =>
          match stepArgFirst R root domain with
          | some next => some ⟨.pi next.val body, .congPiDom next.property⟩
          | none => match stepArgFirst R root body with
            | some next => some ⟨.pi domain next.val, .congPiCod next.property⟩
            | none => none
      | .sigma domain body =>
          match stepArgFirst R root domain with
          | some next => some ⟨.sigma next.val body, .congSigmaDom next.property⟩
          | none => match stepArgFirst R root body with
            | some next => some ⟨.sigma domain next.val, .congSigmaCod next.property⟩
            | none => none
      | .id carrier left right =>
          match stepArgFirst R root carrier with
          | some next => some ⟨.id next.val left right, .congIdTy next.property⟩
          | none => match stepArgFirst R root left with
            | some next => some ⟨.id carrier next.val right, .congIdLeft next.property⟩
            | none => match stepArgFirst R root right with
              | some next => some ⟨.id carrier left next.val, .congIdRight next.property⟩
              | none => none
      | .lam body => match stepArgFirst R root body with
          | some next => some ⟨.lam next.val, .congLam next.property⟩
          | none => none
      | .app (.lam body) argument => some ⟨inst0 argument body, .betaPi body argument⟩
      | .app function argument =>
          match stepArgFirst R root argument with
          | some next => some ⟨.app function next.val, .congAppArg next.property⟩
          | none => match stepArgFirst R root function with
            | some next => some ⟨.app next.val argument, .congAppFun next.property⟩
            | none => none
      | .pair first second =>
          match stepArgFirst R root first with
          | some next => some ⟨.pair next.val second, .congPairFst next.property⟩
          | none => match stepArgFirst R root second with
            | some next => some ⟨.pair first next.val, .congPairSnd next.property⟩
            | none => none
      | .fst (.pair first second) => some ⟨first, .betaSigmaFst first second⟩
      | .fst pair => match stepArgFirst R root pair with
          | some next => some ⟨.fst next.val, .congFst next.property⟩
          | none => none
      | .snd (.pair first second) => some ⟨second, .betaSigmaSnd first second⟩
      | .snd pair => match stepArgFirst R root pair with
          | some next => some ⟨.snd next.val, .congSnd next.property⟩
          | none => none
      | .refl subject => match stepArgFirst R root subject with
          | some next => some ⟨.refl next.val, .congRefl next.property⟩
          | none => none

/-- The fuelled normalizer over that traversal, as `ExecutableReduction.normalize` over its own. -/
def normalizeArgFirst (R : Rules Head) (root : RootEvaluator R) :
    Nat → {n : Nat} → (term : Tm Head n) → Option (Result R term)
  | 0, _, _ => none
  | fuel + 1, _, term =>
      match stepArgFirst R root term with
      | none => some ⟨term, .refl⟩
      | some next => match normalizeArgFirst R root fuel next.val with
        | none => none
        | some result => some ⟨result.val, .head next.property result.property⟩

end ArgumentsFirst

/-- **Positive control: stepping the inspected argument first reaches the normal form.** With the
package's one complete root evaluator, the normalizer that steps an application's argument before its
function unfolds `d`, reduces the scrutinee `b zero`, applies the recursor's row at `zero`, and returns
`zero` at budget four: three steps, then the normal form. -/
theorem argFirst_normalizes :
    (normalizeArgFirst rules erasingRoot 4 (dZero : Tm Tower.Head 0)).map Subtype.val =
      some (.const zero) := by
  rfl

/-- **What the package says of the comparison's hypothesis**: the tree's normalizer, with any complete
root evaluator, is not a reducer that eventually returns weak-head normal reducts of typed terms here
(it returns nothing for `d zero`). This refutes the hypothesis of `compare_eventually` for that one
reducer; it says nothing of the comparison's conclusion, nor of other reducers. -/
theorem normalizer_not_whnfEventually (root : RootEvaluator rules) (complete : RootComplete rules root) :
    ¬ WhnfEventually setting (normalize rules root) := by
  intro eventually
  obtain ⟨fuel, result, -, stable⟩ := eventually CtxFormed.nil (dZero_typed (Δ := .nil))
  have reached := stable fuel le_rfl
  rw [dZero_normalize_none root complete fuel] at reached
  cases reached

/-! ## The separation -/

/-- **Weak-head normalization does not suffice for the full normalizer.** The package is qualified,
every typed term in a formed context has a weak-head normal form, typed terms are not all strongly
normalizing, `d zero` is typed at `num` and reduces to the normal form `zero`, a complete root
evaluator exists, and with every complete root evaluator (there is one, `complete_root_eq`) the
normalizer returns nothing on `d zero` at every budget. -/
theorem separation :
    Qualified setting ∧
      (∀ {n : Nat} {Γ : Ctx Tower.Head n} {t A : Tm Tower.Head n}, CtxFormed rules Γ → Typed rules Γ t A →
        ∃ v, WhRed rules roles t v ∧ Whnf rules roles v) ∧
      ¬ TypedSN rules ∧
      Typed rules .nil (dZero : Tm Tower.Head 0) (.const num) ∧
      StrongNormalization.ReducesStar rules (dZero : Tm Tower.Head 0) (.const zero) ∧
      ContextualDependentExecutableJoin.Normal rules (.const zero : Tm Tower.Head 0) ∧
      RootComplete rules erasingRoot ∧
      ∀ root : RootEvaluator rules, RootComplete rules root → ∀ fuel,
        normalize rules root fuel (dZero : Tm Tower.Head 0) = none :=
  ⟨qualified, fun formed typed => qualified.whnf typed formed, not_typedSN, dZero_typed, dZero_reduces,
    zero_normal, erasingRoot_complete, dZero_normalize_none⟩

/-- **`qualified_normalize_eventually` with weak-head normalization in place of strong normalization is
false**: on this qualified package, whose typed terms all have weak-head normal forms, no complete root
evaluator (there is one) makes the normalizer succeed at some budget on every typed term of a formed
context. A statement about the tree's normalizer and its traversal, not about the comparison. -/
theorem whnf_not_enough :
    Qualified setting ∧
      (∀ {n : Nat} {Γ : Ctx Tower.Head n} {t A : Tm Tower.Head n}, CtxFormed rules Γ → Typed rules Γ t A →
        ∃ v, WhRed rules roles t v ∧ Whnf rules roles v) ∧
      ∀ root : RootEvaluator rules, RootComplete rules root →
        ¬ ∀ {n : Nat} {Γ : Ctx Tower.Head n} {t A : Tm Tower.Head n}, CtxFormed rules Γ →
          Typed rules Γ t A → ∃ fuel result, normalize rules root fuel t = some result := by
  refine ⟨qualified, fun formed typed => qualified.whnf typed formed, fun root complete all => ?_⟩
  obtain ⟨fuel, result, succeeds⟩ := all .nil (dZero_typed (Δ := .nil))
  rw [dZero_normalize_none root complete fuel] at succeeds
  cases succeeds

end Erasing
end NativeTypesOnTheStep.Computing.Eventually

section Audit
open NativeTypesOnTheStep.Computing.Eventually
#print axioms Erasing.step_cases
#print axioms Erasing.shape
#print axioms Erasing.declaresWith
#print axioms Erasing.declaresB
#print axioms Erasing.red_d_app
#print axioms Erasing.d_full
#print axioms Erasing.d_semantic
#print axioms Erasing.constants
#print axioms Erasing.roots
#print axioms Erasing.algorithmicConstants
#print axioms Erasing.erasing_check
#print axioms Erasing.erasingConstructors
#print axioms Erasing.qualified
#print axioms Erasing.not_typedSN
#print axioms Erasing.dZero_reduces
#print axioms Erasing.zero_normal
#print axioms Erasing.no_step_recAt
#print axioms Erasing.step_tower
#print axioms Erasing.dZero_normalize_none
#print axioms Erasing.erasingRoot_complete
#print axioms Erasing.complete_root_eq
#print axioms Erasing.argFirst_normalizes
#print axioms Erasing.normalizer_not_whnfEventually
#print axioms Erasing.separation
#print axioms Erasing.whnf_not_enough
end Audit

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
