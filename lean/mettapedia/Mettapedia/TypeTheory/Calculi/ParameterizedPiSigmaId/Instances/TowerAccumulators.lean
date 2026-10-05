import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerNumbers
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.RecursionComputation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.DeclaredComputations
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ScrutineeFirstEquations
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.RootReflection
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.RecursorDerivation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.CallReordering

/-!
# Recursion with an accumulator in the cumulative tower

`add-onto acc n` adds `n` onto the accumulator `acc`:

`add-onto acc zero = acc`,
`add-onto acc (succ n) = add-onto (succ acc) n`.

The recursive call changes the accumulator, the argument before the one
recursed on, so a hypothesis at the fixed accumulator cannot stand for it. The
definition is admitted through its scrutinee-first form, recursive on its first
argument, whose hypothesis is a function of the accumulator:

`add-onto~scrutinee-first zero acc = acc`,
`add-onto~scrutinee-first (succ n) acc = h (succ acc)`, with `h` for
`add-onto~scrutinee-first n`,

together with the definition `add-onto acc n = add-onto~scrutinee-first n acc`.
Every hypothesis of the normalization model holds for the tower with the
natural numbers and these two constants, and both authored equations hold as
typed equalities, the second with its authored right-hand side.

The scrutinee-first form's right-hand sides are admitted as the kernel admits
them: checked with the form declared and not computing, over the natural
numbers with their recursor. The recursive hypotheses' typing that the
semantic theorem needs follows from that check (`bodyTyped_of_check`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open Mettapedia.TypeTheory.UniverseLevel
open TelescopeAbstraction (closeType applyClosed)
open TowerNumbersModel (num zero succ numRec ctors u mem_zero mem_succ num_ne_zero num_ne_succ
  num_ne_numRec zero_ne_succ zero_ne_numRec succ_ne_numRec)

namespace TowerAccumulatorsModel

/-- The scrutinee-first form. -/
def addOntoFirst : DeclName := .mkSimple "add-onto~scrutinee-first"
/-- The authored definition. -/
def addOnto : DeclName := .mkSimple "add-onto"

theorem num_ne_first : num ≠ addOntoFirst := by decide
theorem zero_ne_first : zero ≠ addOntoFirst := by decide
theorem succ_ne_first : succ ≠ addOntoFirst := by decide
theorem numRec_ne_first : numRec ≠ addOntoFirst := by decide
theorem num_ne_addOnto : num ≠ addOnto := by decide
theorem zero_ne_addOnto : zero ≠ addOnto := by decide
theorem succ_ne_addOnto : succ ≠ addOnto := by decide
theorem numRec_ne_addOnto : numRec ≠ addOnto := by decide
theorem first_ne_addOnto : addOntoFirst ≠ addOnto := by decide

/-- The authored telescope's entries: the accumulator, then the number recursed
on. -/
def entryTypes : Nat → Tm Tower.Head 0 := fun _ => .const num

/-- The scrutinee-first telescope. -/
abbrev firstEntries : (i : Nat) → Tm Tower.Head i :=
  fun i => liftClosed (scrutineeFirst entryTypes 1 i)

/-- The authored telescope. -/
abbrev authoredTele : Ctx Tower.Head (1 + 1 + 0) :=
  ofEntries (fun i => liftClosed (entryTypes i)) (1 + 1 + 0)

/-- The result type. -/
def resultType : Tm Tower.Head (1 + 1 + 0) := .const num

/-- The scrutinee-first right-hand sides: the accumulator at zero, and at a
successor the hypothesis, a function of the accumulator, at `succ acc`. -/
def firstBody : (k : DeclName) → (fields : List (Field Tower.Head)) →
    Tm Tower.Head (0 + fields.length + (1 + 0) + (recPositions fields).length)
  | _, [] => .var ⟨0, by decide⟩
  | _, [.recursive] => .app (.var ⟨0, by decide⟩) (.app (.const succ) (.var ⟨1, by decide⟩))
  | _, _ => .const addOntoFirst

/-- The declared type of the scrutinee-first form. -/
def firstType : Tm Tower.Head 0 :=
  closeType (ofEntries firstEntries (0 + 1 + (1 + 0))) (Presentation.rename (teleMove 1 0) resultType)

/-- The declared type of the authored definition. -/
def authoredType : Tm Tower.Head 0 := closeType authoredTele resultType

/-- The authored definition's right-hand side: the scrutinee-first form at the
number and the accumulator. -/
def authoredRhs : Tm Tower.Head (1 + 1 + 0) := definitionBody entryTypes addOntoFirst 1 0

theorem firstType_eq : firstType = .pi (.const num) (.pi (.const num) (.const num)) := rfl
theorem authoredType_eq : authoredType = .pi (.const num) (.pi (.const num) (.const num)) := rfl
theorem authoredRhs_eq :
    authoredRhs = .app (.app (.const addOntoFirst) (.var 0)) (.var 1) := rfl

variable (lv : LevelExpr Nat)

/-- The declared types. -/
def constantType : DeclName → Option (Tm Tower.Head 0) := fun name =>
  if name = addOntoFirst then some firstType
  else if name = addOnto then some authoredType
  else TowerNumbersModel.constantType lv name

/-- The computations: the recursor's, the scrutinee-first form's equations,
and the authored definition's equation. -/
def computations : List (DeclName × RootComputation Tower.Head) :=
  [(numRec, iotaComputation numRec ctors),
   (addOntoFirst, recursionComputation addOntoFirst ctors firstEntries 0 (1 + 0) firstBody),
   (addOnto, definitionComputation addOnto authoredTele authoredRhs)]

/-- The tower with the natural numbers, their recursor into level `lv`, and
`add-onto` with its scrutinee-first form. -/
def rules : Rules Tower.Head :=
  { Tower.rules with
    constantType := constantType lv
    computation := RootComputation.unionAll computations }

/-- The stage in which the authored right-hand side is typed: the numbers and
the scrutinee-first form. -/
def firstStage : Rules Tower.Head :=
  { Tower.rules with
    constantType := fun name =>
      if name = addOntoFirst then some firstType else TowerNumbersModel.rules₂.constantType name }

/-- The roles of the declared constants. -/
def roles : Roles Tower.Head := fun name =>
  if name = addOntoFirst then .computes (0 + 1 + (1 + 0)) (.split 0 .constructor fun _ => .leaf)
  else if name = addOnto then .computes (1 + 1 + 0) .leaf
  else TowerNumbersModel.roles name

theorem roles_first : roles addOntoFirst = .computes (0 + 1 + (1 + 0)) (.split 0 .constructor fun _ => .leaf) := by
  simp [roles]
theorem roles_addOnto : roles addOnto = .computes (1 + 1 + 0) .leaf := by
  simp [roles, first_ne_addOnto.symm]
theorem roles_num : roles num = .inductive ctors := by
  simp [roles, num_ne_first, num_ne_addOnto, TowerNumbersModel.roles_num]
theorem roles_numRec : roles numRec = .computes 4 (.split 3 .constructor fun _ => .leaf) := by
  simp [roles, numRec_ne_first, numRec_ne_addOnto, TowerNumbersModel.roles_numRec]

/-- The only inductive type is `num`. -/
theorem roles_inductive {T : DeclName} {cs : List (DeclName × List (Field Tower.Head))}
    (role : roles T = .inductive cs) : T = num ∧ cs = ctors := by
  unfold roles at role
  split at role
  · cases role
  · split at role
    · cases role
    · exact TowerNumbersModel.roles_inductive role

theorem constructorsDeclared : ConstructorsDeclared roles where
  arity := by
    intro T cs k fields role mem
    obtain ⟨rfl, rfl⟩ := roles_inductive role
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp [roles, zero_ne_first, zero_ne_addOnto, TowerNumbersModel.roles_zero]
    · simp [roles, succ_ne_first, succ_ne_addOnto, TowerNumbersModel.roles_succ]
  distinct := by
    intro T cs role
    obtain ⟨rfl, rfl⟩ := roles_inductive role
    simp only [ctors, List.map_cons, List.map_nil]
    exact List.nodup_cons.mpr ⟨by simp [zero_ne_succ], List.nodup_singleton _⟩

/-! ## The shape of the computation -/

theorem computations_spine : ∀ entry ∈ computations, SpineShaped roles entry.2 := by
  intro entry mem
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl
  · exact fun _ _ _ step => IotaStep.spine (T := num) roles_num roles_numRec
      constructorsDeclared step
  · exact fun _ _ _ step => RecursionStep.spine roles_num constructorsDeclared roles_first step
  · exact definitionComputation_spine roles_addOnto

theorem computations_headed : ∀ entry ∈ computations, HeadedBy entry.1 entry.2 := by
  intro entry mem
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl
  · exact iotaComputation_headed
  · exact recursionComputation_headed
  · exact definitionComputation_headed

theorem computations_deterministic : ∀ entry ∈ computations, Deterministic entry.2 := by
  intro entry mem
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl
  · exact fun _ _ _ _ step step' =>
      IotaStep.deterministic (T := num) roles_num constructorsDeclared step step'
  · exact fun _ _ _ _ step step' =>
      RecursionStep.deterministic roles_num constructorsDeclared step step'
  · exact definitionComputation_deterministic

theorem computations_distinct : (computations.map Prod.fst).Nodup := by
  decide

theorem shape : RootShape (rules lv) roles where
  spine := fun step => RootComputation.unionAll_spine computations_spine step
  deterministic := fun step step' =>
    (RootComputation.unionAll_deterministic computations_distinct computations_headed
      computations_deterministic step step').symm

/-- The tower's level model, for this rule package. -/
def levels (valuation : Nat → Nat) : LevelModel (rules lv) ℕ where
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

/-- The normalization setting. -/
def setting (valuation : Nat → Nat) : Setting Tower.Head ℕ where
  R := rules lv
  roles := roles
  E := declarative (rules lv)
  levels := levels lv valuation
  shape := shape lv
  constructors := constructorsDeclared

theorem laws (valuation : Nat → Nat) :
    (setting lv valuation).E.Laws (setting lv valuation).R (setting lv valuation).roles :=
  declarative_laws roles (levels lv valuation)

/-! ## The declared types are typed -/

theorem declaredNum₂ : TowerNumbersModel.rules₂.constantType num = some (.head u) := by
  simp [TowerNumbersModel.rules₂]

theorem declaredZero₂ : TowerNumbersModel.rules₂.constantType zero = some (ctorType num []) := by
  simp [TowerNumbersModel.rules₂, num_ne_zero.symm]

theorem declaredSucc₂ :
    TowerNumbersModel.rules₂.constantType succ = some (ctorType num [.recursive]) := by
  simp [TowerNumbersModel.rules₂, num_ne_succ.symm, zero_ne_succ.symm]

theorem num_typed₂ {n : Nat} {Γ : Ctx Tower.Head n} :
    Typed TowerNumbersModel.rules₂ Γ (.const num) (.head u) :=
  TowerNumbersModel.num_typed LevelTower.HeadTyping.sort LevelTower.IsUniverse.sort declaredNum₂

theorem succ_typed₂ {n : Nat} {Γ : Ctx Tower.Head n} :
    Typed TowerNumbersModel.rules₂ Γ (.const succ) (.pi (.const num) (.const num)) :=
  .const declaredSucc₂ (.piForm num_typed₂ (.sort _) num_typed₂ (.sort _) (.sorts _ _)) (.sort _)

theorem numsType_typed : ∃ w, Tower.IsUniverse w ∧
    Typed TowerNumbersModel.rules₂ .nil (.pi (.const num) (.pi (.const num) (.const num)))
      (.head w) :=
  ⟨_, .sort _, .piForm num_typed₂ (.sort _)
    (.piForm num_typed₂ (.sort _) num_typed₂ (.sort _) (.sorts _ _)) (.sort _) (.sorts _ _)⟩

theorem declaredFirst₁ : firstStage.constantType addOntoFirst = some firstType := by
  simp [firstStage]

theorem declaredNum₁ : firstStage.constantType num = some (.head u) := by
  simp [firstStage, num_ne_first, TowerNumbersModel.rules₂]

theorem num_typed₁ {n : Nat} {Γ : Ctx Tower.Head n} :
    Typed firstStage Γ (.const num) (.head u) :=
  TowerNumbersModel.num_typed LevelTower.HeadTyping.sort LevelTower.IsUniverse.sort declaredNum₁

theorem first_typed₁ {n : Nat} {Γ : Ctx Tower.Head n} :
    Typed firstStage Γ (.const addOntoFirst) (.pi (.const num) (.pi (.const num) (.const num))) :=
  .const declaredFirst₁ (.piForm num_typed₁ (.sort _)
    (.piForm num_typed₁ (.sort _) num_typed₁ (.sort _) (.sorts _ _)) (.sort _) (.sorts _ _))
    (.sort _)

/-! ## The hypotheses of the model -/

section Hypotheses

variable (valuation : Nat → Nat)

theorem constantType_numbers {name : DeclName} (h₁ : name ≠ addOntoFirst) (h₂ : name ≠ addOnto) :
    (rules lv).constantType name = (TowerNumbersModel.rules lv).constantType name := by
  show (if name = addOntoFirst then some firstType
    else if name = addOnto then some authoredType
    else TowerNumbersModel.constantType lv name) = _
  rw [if_neg h₁, if_neg h₂]
  rfl

theorem declaredNum : (rules lv).constantType num = some (.head u) := by
  rw [constantType_numbers lv num_ne_first num_ne_addOnto]
  exact TowerNumbersModel.declaredNum lv

theorem declaredZero : (rules lv).constantType zero = some (ctorType num []) := by
  rw [constantType_numbers lv zero_ne_first zero_ne_addOnto]
  exact TowerNumbersModel.declaredZero lv

theorem declaredSucc : (rules lv).constantType succ = some (ctorType num [.recursive]) := by
  rw [constantType_numbers lv succ_ne_first succ_ne_addOnto]
  exact TowerNumbersModel.declaredSucc lv

theorem declaredRec : (rules lv).constantType numRec = some (recType num (.sort lv) ctors) := by
  rw [constantType_numbers lv numRec_ne_first numRec_ne_addOnto]
  exact TowerNumbersModel.declaredRec lv

theorem declaredFirst : (rules lv).constantType addOntoFirst = some firstType := by
  simp [rules, constantType]

theorem declaredAddOnto : (rules lv).constantType addOnto = some authoredType := by
  simp [rules, constantType, first_ne_addOnto.symm]

/-- The second stage of the natural numbers is inside the package. -/
theorem sub₂ : RulesSub TowerNumbersModel.rules₂ (rules lv) :=
  ⟨id, id, id, id, id, fun {name type} declared => (by
      simp only [TowerNumbersModel.rules₂] at declared
      split at declared
      · rename_i h
        subst h
        cases declared
        exact declaredNum lv
      · split at declared
        · rename_i _ h
          subst h
          cases declared
          exact declaredZero lv
        · split at declared
          · rename_i _ _ h
            subst h
            cases declared
            exact declaredSucc lv
          · cases declared), fun step => nomatch step⟩

/-- The stage with the scrutinee-first form is inside the package. -/
theorem subFirst : RulesSub firstStage (rules lv) :=
  ⟨id, id, id, id, id, fun {name type} declared => (by
      simp only [firstStage] at declared
      split at declared
      · rename_i h
        subst h
        cases declared
        exact declaredFirst lv
      · exact (sub₂ lv).constantType declared), fun step => nomatch step⟩

/-- The numbers' second stage is inside the stage with the scrutinee-first form. -/
theorem sub₂First : RulesSub TowerNumbersModel.rules₂ firstStage :=
  ⟨id, id, id, id, id, fun {name type} declared => (by
      show (if name = addOntoFirst then some firstType
        else TowerNumbersModel.rules₂.constantType name) = some type
      rw [if_neg]
      · exact declared
      · rintro rfl
        simp [TowerNumbersModel.rules₂, num_ne_first.symm, zero_ne_first.symm,
          succ_ne_first.symm] at declared), fun step => nomatch step⟩

/-- The package declares the natural numbers. -/
theorem declares :
    DeclaresInductive (setting lv valuation) (constantFreeRules (rules lv))
      TowerNumbersModel.rules₁ TowerNumbersModel.rules₂ num u ctors numRec (.sort lv) where
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
        exact declaredNum lv
      · cases declared), fun step => nomatch step⟩
  sub₂ := sub₂ lv
  semantic₀ := fun declared => nomatch declared
  stage₁ := (TowerNumbersModel.declares lv valuation).stage₁
  stage₂ := (TowerNumbersModel.declares lv valuation).stage₂
  declared := declaredNum lv
  ctorDeclared := by
    intro k fields mem
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact declaredZero lv
    · exact declaredSucc lv
  recDeclared := declaredRec lv
  fieldTyped := (TowerNumbersModel.declares lv valuation).fieldTyped
  ctorTyped := (TowerNumbersModel.declares lv valuation).ctorTyped
  recTyped := (TowerNumbersModel.declares lv valuation).recTyped
  iota := fun hms hi has hm =>
    RootComputation.step_unionAll (cs := computations) (List.mem_cons_self ..)
      ⟨_, _, _, _, _, _, _, hms, hi, has, hm, rfl, rfl⟩


/-! ## The kernel's check of the scrutinee-first form's right-hand sides -/

/-- The natural numbers with the scrutinee-first form declared and not
computing: the package in which the kernel checks the form's equations. -/
def firstCheckStage : Rules Tower.Head :=
  { TowerNumbersModel.rules lv with
    constantType := fun name =>
      if name = addOntoFirst then some firstType else (TowerNumbersModel.rules lv).constantType name }

theorem declaredFirstCheck : (firstCheckStage lv).constantType addOntoFirst = some firstType := by
  simp [firstCheckStage]

theorem declaredNumCheck : (firstCheckStage lv).constantType num = some (.head u) := by
  simp only [firstCheckStage, if_neg num_ne_first]
  exact TowerNumbersModel.declaredNum lv

theorem declaredSuccCheck :
    (firstCheckStage lv).constantType succ = some (ctorType num [.recursive]) := by
  simp only [firstCheckStage, if_neg succ_ne_first]
  exact TowerNumbersModel.declaredSucc lv

/-- No type the natural numbers declare mentions the scrutinee-first form. -/
theorem numbers_typesFree {c : DeclName} {type : Tm Tower.Head 0}
    (declared : (TowerNumbersModel.rules lv).constantType c = some type) :
    ConstFree addOntoFirst type := by
  change TowerNumbersModel.constantType lv c = some type at declared
  unfold TowerNumbersModel.constantType at declared
  split at declared
  · cases declared; exact ConstFree.of_mentions rfl
  · split at declared
    · cases declared; exact ConstFree.of_mentions rfl
    · split at declared
      · cases declared; exact ConstFree.of_mentions rfl
      · split at declared
        · cases declared; exact ConstFree.of_mentions rfl
        · cases declared

theorem firstCheck_declaresCall :
    DeclaresCall (firstCheckStage lv) (TowerNumbersModel.rules lv) addOntoFirst where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  computation := id
  constantType := by
    intro c type hc declared
    simpa [firstCheckStage, hc] using declared
  typesFree := numbers_typesFree lv

theorem firstCheck_inert : CallsInert (firstCheckStage lv) addOntoFirst := by
  intro n t w step
  obtain ⟨args, rfl⟩ := iotaComputation_spine step
  exact ⟨numRec, args, numRec_ne_first, rfl⟩

theorem firstCheck_reflects : RootReflects (firstCheckStage lv) addOntoFirst (0 + 1) := by
  intro n m τ call t w free step
  refine iotaComputation_reflects numRec_ne_first ?_ call free step
  intro c fields mem
  simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
  rcases mem with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact zero_ne_first
  · exact succ_ne_first

/-- The declared types of the natural numbers are types. -/
theorem numbers_typesFormed (valuation : Nat → Nat) :
    DeclaredTypesFormed (TowerNumbersModel.rules lv) := by
  intro name type declared
  have decl := TowerNumbersModel.declares lv valuation
  change TowerNumbersModel.constantType lv name = some type at declared
  unfold TowerNumbersModel.constantType at declared
  split at declared
  · cases declared
    exact ⟨_, .sort _, .headType (LevelTower.HeadTyping.sort _)⟩
  · split at declared
    · cases declared
      exact ⟨_, .sort _, Derivable.mono decl.sub₁ TowerNumbersModel.ctorType_zero_typed⟩
    · split at declared
      · cases declared
        exact ⟨_, .sort _, Derivable.mono decl.sub₁ TowerNumbersModel.ctorType_succ_typed⟩
      · split at declared
        · cases declared
          obtain ⟨w, hw, t⟩ := TowerNumbersModel.recType_typed lv
          exact ⟨w, hw, Derivable.mono decl.sub₂ t⟩
        · cases declared

/-- The kernel relates the numbers' type to itself. -/
theorem numBelowCheck {n : Nat} {Γ : Ctx Tower.Head n} :
    BelowAlgorithm (firstCheckStage lv) Γ (.const num) (.const num) :=
  .conv (.neutralTypes .refl .refl (.const (declaredNumCheck lv)))

/-- The kernel's check of the equation at `zero`: the accumulator. -/
theorem checkZero :
    CheckingAlgorithm (firstCheckStage lv) .check (.snoc .nil (.const num)) (.var 0) (.const num) :=
  .switch (.var 0) (numBelowCheck lv)

/-- The kernel's check of the equation at `succ n`: the form at `n`, applied to
`succ acc`, with the form declared and not computing. -/
theorem checkSucc :
    CheckingAlgorithm (firstCheckStage lv) .check (.snoc (.snoc .nil (.const num)) (.const num))
      (.app (.app (.const addOntoFirst) (.var 1)) (.app (.const succ) (.var 0))) (.const num) := by
  have tForm : CheckingAlgorithm (firstCheckStage lv) .synth
      (.snoc (.snoc .nil (.const num)) (.const num)) (.const addOntoFirst)
      (.pi (.const num) (.pi (.const num) (.const num))) :=
    .const (declaredFirstCheck lv)
  have tSucc : CheckingAlgorithm (firstCheckStage lv) .synth
      (.snoc (.snoc .nil (.const num)) (.const num)) (.const succ)
      (.pi (.const num) (.const num)) :=
    .const (declaredSuccCheck lv)
  have tFirst : CheckingAlgorithm (firstCheckStage lv) .synth
      (.snoc (.snoc .nil (.const num)) (.const num)) (.app (.const addOntoFirst) (.var 1))
      (.pi (.const num) (.const num)) :=
    .app (A := .const num) (B := .pi (.const num) (.const num)) tForm .refl
      (.switch (.var 1) (numBelowCheck lv))
  have tArg : CheckingAlgorithm (firstCheckStage lv) .check
      (.snoc (.snoc .nil (.const num)) (.const num)) (.app (.const succ) (.var 0)) (.const num) :=
    .switch (.app (A := .const num) (B := .const num) tSucc .refl
      (.switch (.var 0) (numBelowCheck lv))) (numBelowCheck lv)
  exact .switch (.app (A := .const num) (B := .const num) tFirst .refl tArg) (numBelowCheck lv)

/-! ### A rejection control -/

/-- In the checking package, the numbers' type reduces only to itself. -/
theorem num_reduces_self {n : Nat} {X : Tm Tower.Head n}
    (red : Reduces (firstCheckStage lv) (.const num) X) : X = .const num := by
  induction red with
  | refl => rfl
  | tail _ step ih =>
      subst ih
      cases step with
      | root step =>
          obtain ⟨args, h⟩ := iotaComputation_spine step
          exact absurd (appSpine_const_injective (show appSpine (.const num) [] = _ from h)).1
            num_ne_numRec

/-- A dependent function type is not usable as the numbers' type in the
kernel's subtype test. -/
theorem pi_not_below_num {n : Nat} {Γ : Ctx Tower.Head n} {A : Tm Tower.Head n}
    {B : Tm Tower.Head (n + 1)} : ¬ BelowAlgorithm (firstCheckStage lv) Γ (.pi A B) (.const num) := by
  intro below
  cases below with
  | conv d =>
      cases d with
      | heads rA _ _ =>
          obtain ⟨_, _, e, _⟩ := Reduces.pi_inv (firstCheck_inert lv) rA
          cases e
      | piTypes _ rB _ _ =>
          cases num_reduces_self lv rB
      | sigmaTypes rA _ _ _ =>
          obtain ⟨_, _, e, _⟩ := Reduces.pi_inv (firstCheck_inert lv) rA
          cases e
      | idTypes rA _ _ _ _ =>
          obtain ⟨_, _, e, _⟩ := Reduces.pi_inv (firstCheck_inert lv) rA
          cases e
      | neutralTypes rA _ dn =>
          obtain ⟨_, _, e, _⟩ := Reduces.pi_inv (firstCheck_inert lv) rA
          subst e
          cases dn
  | universes rA _ _ =>
      obtain ⟨_, _, e, _⟩ := Reduces.pi_inv (firstCheck_inert lv) rA
      cases e
  | pi _ rB _ _ =>
      cases num_reduces_self lv rB
  | sigma rA _ _ _ =>
      obtain ⟨_, _, e, _⟩ := Reduces.pi_inv (firstCheck_inert lv) rA
      cases e

/-- A rejection control: with `succ` itself where the changed accumulator
`succ acc` belongs, the kernel refuses the right-hand side at `succ n`: the
argument `succ` has type `num → num`, not usable as a number. -/
theorem checkSucc_rejects_function_accumulator :
    ¬ CheckingAlgorithm (firstCheckStage lv) .check (.snoc (.snoc .nil (.const num)) (.const num))
      (.app (.app (.const addOntoFirst) (.var 1)) (.const succ)) (.const num) := by
  intro check
  cases check with
  | switch synth _ =>
      cases synth with
      | app sf red argCheck =>
          cases sf with
          | app sf' red' _ =>
              cases sf' with
              | const declared =>
                  rw [declaredFirstCheck lv] at declared
                  cases declared
                  obtain ⟨_, B', e, _, rB⟩ := Reduces.pi_inv (firstCheck_inert lv) red'
                  cases e
                  obtain ⟨A₁, B₁, e₁, rA₁, rB₁⟩ := Reduces.pi_inv (firstCheck_inert lv) rB
                  subst e₁
                  have hA₁ := num_reduces_self lv rA₁
                  have hB₁ := num_reduces_self lv rB₁
                  subst hA₁ hB₁
                  obtain ⟨_, _, e₂, rA₂, _⟩ := Reduces.pi_inv (firstCheck_inert lv) red
                  cases e₂
                  have hA₂ := num_reduces_self lv rA₂
                  subst hA₂
                  cases argCheck with
                  | switch synthSucc belowSucc =>
                      cases synthSucc with
                      | const declaredS =>
                          rw [declaredSuccCheck lv] at declaredS
                          cases declaredS
                          exact pi_not_below_num lv belowSucc

/-- The natural numbers with their recursor are inside the package. -/
theorem subNumbers : RulesSub (TowerNumbersModel.rules lv) (rules lv) :=
  ⟨id, id, id, id, id, fun {name type} declared => (by
      have h₁ : name ≠ addOntoFirst := by
        rintro rfl
        simp [TowerNumbersModel.rules, TowerNumbersModel.constantType, num_ne_first.symm,
          zero_ne_first.symm, succ_ne_first.symm, numRec_ne_first.symm] at declared
      have h₂ : name ≠ addOnto := by
        rintro rfl
        simp [TowerNumbersModel.rules, TowerNumbersModel.constantType, num_ne_addOnto.symm,
          zero_ne_addOnto.symm, succ_ne_addOnto.symm, numRec_ne_addOnto.symm] at declared
      rw [constantType_numbers lv h₁ h₂]
      exact declared),
    fun step => RootComputation.step_unionAll (cs := computations) (List.mem_cons_self ..) step⟩

/-- The natural numbers' constants are semantic in the package. -/
theorem semanticNumbers : AllSemantic (setting lv valuation) (TowerNumbersModel.rules lv) := by
  intro name type declared
  have decl := declares lv valuation
  have laws' := laws lv valuation
  change TowerNumbersModel.constantType lv name = some type at declared
  unfold TowerNumbersModel.constantType at declared
  split at declared
  · rename_i h
    subst h
    cases declared
    intro m Δ formed P r
    exact decl.type_semantic laws' formed r
  · split at declared
    · rename_i _ h
      subst h
      cases declared
      intro m Δ formed P r
      exact decl.ctor_semantic laws' mem_zero formed r
    · split at declared
      · rename_i _ _ h
        subst h
        cases declared
        intro m Δ formed P r
        exact decl.ctor_semantic laws' mem_succ formed r
      · split at declared
        · rename_i _ _ _ h
          subst h
          cases declared
          intro m Δ formed P r
          exact decl.rec_semantic laws' formed r
        · cases declared

theorem num_typedNumbers {n : Nat} {Γ : Ctx Tower.Head n} :
    Typed (TowerNumbersModel.rules lv) Γ (.const num) (.head u) :=
  TowerNumbersModel.num_typed LevelTower.HeadTyping.sort LevelTower.IsUniverse.sort
    (TowerNumbersModel.declaredNum lv)

/-- The package declares the scrutinee-first form by structural recursion on
its first argument. Each right-hand side is typed with its recursive
hypothesis because the kernel checks it with the form declared and not
computing (`checkZero`, `checkSucc`, `bodyTyped_of_check`). -/
theorem declaresFirst :
    DeclaresRecursion (setting lv valuation) (TowerNumbersModel.rules lv) addOntoFirst num ctors
      firstEntries 0 (1 + 0) (Presentation.rename (teleMove 1 0) resultType) firstBody where
  role := roles_first
  scrutinee := rfl
  declared := declaredFirst lv
  sub₀ := subNumbers lv
  semantic₀ := semanticNumbers lv valuation
  typed := by
    obtain ⟨w, hw, t⟩ := numsType_typed
    exact ⟨w, hw, Derivable.mono (TowerNumbersModel.declares lv valuation).sub₂ t⟩
  formed := by
    intro k fields mem
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show CtxFormed (TowerNumbersModel.rules lv) (.snoc .nil (.const num))
      exact .snoc .nil ⟨_, .sort _, num_typedNumbers lv⟩
    · show CtxFormed (TowerNumbersModel.rules lv)
        (.snoc (.snoc (.snoc .nil (.const num)) (.const num)) (.pi (.const num) (.const num)))
      exact .snoc (.snoc (.snoc .nil ⟨_, .sort _, num_typedNumbers lv⟩)
        ⟨_, .sort _, num_typedNumbers lv⟩)
        ⟨_, .sort _, .piForm (num_typedNumbers lv) (.sort _) (num_typedNumbers lv) (.sort _)
          (.sorts _ _)⟩
  bodyTyped := by
    have freeE : ∀ i, ConstFree addOntoFirst (firstEntries i) := by
      intro i
      refine ConstFree.liftClosed ?_
      cases i with
      | zero => exact num_ne_first
      | succ j =>
          show ConstFree addOntoFirst (if j < 1 then entryTypes j else entryTypes (j + 1))
          split <;> exact num_ne_first
    have freeC : ConstFree addOntoFirst
        (Presentation.rename (teleMove 1 0) resultType : Tm Tower.Head (0 + 1 + (1 + 0))) :=
      num_ne_first
    intro k fields mem
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact bodyTyped_of_check (S₀ := TowerNumbersModel.setting lv valuation)
        (f := addOntoFirst) (T := num) (k := zero) (e := firstEntries) (s := 0) (d := 1 + 0)
        (fields := []) (C := Presentation.rename (teleMove 1 0) resultType)
        (TowerNumbersModel.facts lv) (TowerNumbersModel.roots lv)
        (TowerNumbersModel.heads lv) (TowerNumbersModel.algebra lv) (numbers_typesFormed lv valuation)
        (firstCheck_declaresCall lv) (firstCheck_inert lv) (firstCheck_reflects lv)
        (declaredFirstCheck lv) freeE (fun _ => num_ne_first) zero_ne_first freeC
        (.snoc .nil ⟨_, LevelTower.IsUniverse.sort _, num_typedNumbers lv⟩)
        ⟨_, LevelTower.IsUniverse.sort _, num_typedNumbers lv⟩
        (body := firstBody zero []) trivial (checkZero lv)
    · exact bodyTyped_of_check (S₀ := TowerNumbersModel.setting lv valuation)
        (f := addOntoFirst) (T := num) (k := succ) (e := firstEntries) (s := 0) (d := 1 + 0)
        (fields := [.recursive]) (C := Presentation.rename (teleMove 1 0) resultType)
        (TowerNumbersModel.facts lv) (TowerNumbersModel.roots lv)
        (TowerNumbersModel.heads lv) (TowerNumbersModel.algebra lv) (numbers_typesFormed lv valuation)
        (firstCheck_declaresCall lv) (firstCheck_inert lv) (firstCheck_reflects lv)
        (declaredFirstCheck lv) freeE (fun l => by cases l <;> exact num_ne_first) succ_ne_first freeC
        (.snoc (.snoc (.snoc .nil ⟨_, LevelTower.IsUniverse.sort _, num_typedNumbers lv⟩)
          ⟨_, LevelTower.IsUniverse.sort _, num_typedNumbers lv⟩)
          ⟨_, LevelTower.IsUniverse.sort _, .piForm (num_typedNumbers lv) (LevelTower.IsUniverse.sort _)
            (num_typedNumbers lv) (LevelTower.IsUniverse.sort _) (.sorts _ _)⟩)
        ⟨_, LevelTower.IsUniverse.sort _, num_typedNumbers lv⟩
        (body := firstBody succ [.recursive]) ⟨trivial, succ_ne_first, trivial⟩ (checkSucc lv)
  rule := by
    intro k fields mem m σ as has
    exact RootComputation.step_unionAll (cs := computations)
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) ⟨_, _, σ, as, mem, has, rfl, rfl⟩

/-- The package declares `add-onto` by passing its arguments to the
scrutinee-first form. -/
theorem declaresAuthored :
    DeclaresDefinition (setting lv valuation) firstStage addOnto authoredTele resultType
      authoredRhs where
  role := roles_addOnto
  declared := declaredAddOnto lv
  sub₀ := subFirst lv
  semantic₀ := by
    intro name type declared
    simp only [firstStage] at declared
    split at declared
    · rename_i h
      subst h
      cases declared
      exact (declaresFirst lv valuation).semantic (laws lv valuation) (declares lv valuation)
    · exact (declares lv valuation).semantic₂ (laws lv valuation) declared
  typed := by
    show ∃ w, Tower.IsUniverse w ∧
      Typed firstStage .nil (.pi (.const num) (.pi (.const num) (.const num))) (.head w)
    obtain ⟨w, hw, t⟩ := numsType_typed
    exact ⟨w, hw, Derivable.mono sub₂First t⟩
  body := by
    rw [authoredRhs_eq]
    show Typed firstStage (.snoc (.snoc .nil (.const num)) (.const num))
      (.app (.app (.const addOntoFirst) (.var 0)) (.var 1)) (.const num)
    exact .appElim (A := .const num) (B := .const num) (.appElim first_typed₁ (.var 0)) (.var 1)
  rule := by
    intro n σ
    exact RootComputation.step_unionAll (cs := computations)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) ⟨σ, rfl, rfl⟩

/-- Every declared constant is semantic. -/
theorem constants : SemanticConstants (setting lv valuation) := by
  intro name type w declared _ _
  have decl := declares lv valuation
  have laws' := laws lv valuation
  change constantType lv name = some type at declared
  unfold constantType at declared
  split at declared
  · rename_i h
    subst h
    cases declared
    intro m Δ formed P r
    exact (declaresFirst lv valuation).semantic laws' decl formed r
  · split at declared
    · rename_i _ h
      subst h
      cases declared
      intro m Δ formed P r
      exact (declaresAuthored lv valuation).semantic laws' formed r
    · unfold TowerNumbersModel.constantType at declared
      split at declared
      · rename_i _ _ h
        subst h
        cases declared
        intro m Δ formed P r
        exact decl.type_semantic laws' formed r
      · split at declared
        · rename_i _ _ _ h
          subst h
          cases declared
          intro m Δ formed P r
          exact decl.ctor_semantic laws' mem_zero formed r
        · split at declared
          · rename_i _ _ _ _ h
            subst h
            cases declared
            intro m Δ formed P r
            exact decl.ctor_semantic laws' mem_succ formed r
          · split at declared
            · rename_i _ _ _ _ _ h
              subst h
              cases declared
              intro m Δ formed P r
              exact decl.rec_semantic laws' formed r
            · cases declared

/-- **The facts about the weak-head forms of the package's types**, from the
normalization model, in which its declared constants are semantic. -/
theorem facts : FormFacts (rules lv) roles :=
  .ofSemantic (S := setting lv fun _ => 0) (laws lv _) (constants lv _)

/-- The computation rules preserve typing. -/
theorem roots : RootPreserving (rules lv) := by
  intro n Γ l r A formed step typing
  obtain ⟨entry, mem, step⟩ := RootComputation.unionAll_step step
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl
  · exact (declares lv fun _ => 0).toRecursor.step_preserves (TowerAccumulatorsModel.facts lv)
      (RulesSub.refl _) formed step typing
  · obtain ⟨k, fields, σ, as, mem, has, rfl, rfl⟩ := step
    exact (declaresFirst lv fun _ => 0).rule_preserves (TowerAccumulatorsModel.facts lv) (declares
        lv fun _ => 0) (RulesSub.refl _) formed mem σ as has typing
  · obtain ⟨σ, rfl, rfl⟩ := step
    exact (declaresAuthored lv fun _ => 0).rule_preserves (TowerAccumulatorsModel.facts lv) (RulesSub.refl _) formed
        σ typing

/-- Head equality steps preserve typing. -/
theorem heads : HeadPreserving (rules lv) := by
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
          have raise : (rules lv).cumulative (.sort (.succ r)) (.sort (.succ l)) := by
            intro ν
            show LevelExpr.eval ν r + 1 ≤ LevelExpr.eval ν l + 1
            have := same ν
            omega
          exact Typed.subsume (.cumul (.headType (.sort r)) raise) le

theorem algebra : CumulativeAlgebra (rules lv) where
  trans := TowerModel.algebra.trans
  same_left := TowerModel.algebra.same_left
  same_right := TowerModel.algebra.same_right
  join_least := TowerModel.algebra.join_least

end Hypotheses

end TowerAccumulatorsModel

/-! ## The authored equations -/

section Equations

open TowerAccumulatorsModel

variable {lv : LevelExpr Nat} {n : Nat} {Γ : Ctx Tower.Head n}

theorem TowerAccumulators.succ_typed {t : Tm Tower.Head n}
    (typing : Typed (rules lv) Γ t (.const num)) :
    Typed (rules lv) Γ (.app (.const succ) t) (.const num) :=
  .appElim (A := .const num) (B := .const num)
    (Derivable.mono (sub₂ lv) succ_typed₂) typing

theorem TowerAccumulators.addOnto_typed {a b : Tm Tower.Head n}
    (ta : Typed (rules lv) Γ a (.const num)) (tb : Typed (rules lv) Γ b (.const num)) :
    Typed (rules lv) Γ (.app (.app (.const addOnto) a) b) (.const num) := by
  have declared := declaredAddOnto lv
  rw [authoredType_eq] at declared
  have tf : Typed (rules lv) Γ (.const addOnto) (.pi (.const num) (.pi (.const num) (.const num))) :=
    .const declared (Derivable.mono (sub₂ lv) (.piForm num_typed₂ (.sort _)
      (.piForm num_typed₂ (.sort _) num_typed₂ (.sort _) (.sorts _ _)) (.sort _) (.sorts _ _)))
      (.sort _)
  exact .appElim (A := .const num) (B := .const num) (.appElim tf ta) tb

/-- The authored substitution of the accumulator and the number. -/
def TowerAccumulators.args (acc m : Tm Tower.Head n) : Sub Tower.Head (1 + 1 + 0) n :=
  consSub m (consSub acc fun i => Fin.elim0 i)

theorem TowerAccumulators.args_typed {acc m : Tm Tower.Head n}
    (tacc : Typed (rules lv) Γ acc (.const num)) (tm : Typed (rules lv) Γ m (.const num)) :
    SubstMor (rules lv) authoredTele Γ (TowerAccumulators.args acc m) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact tm
  · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    exact tacc

/-- `add-onto acc zero = acc`. -/
theorem TowerAccumulators.addOnto_zero (formed : CtxFormed (rules lv) Γ) {acc : Tm Tower.Head n}
    (tacc : Typed (rules lv) Γ acc (.const num)) :
    Equal (rules lv) Γ (.app (.app (.const addOnto) acc) (.const zero)) acc (.const num) := by
  have tzero : Typed (rules lv) Γ (.const zero) (.const num) :=
    Derivable.mono (sub₂ lv) (.const declaredZero₂ num_typed₂ (.sort _))
  have typing := TowerAccumulators.addOnto_typed tacc tzero
  exact ScrutineeFirst.equation (S := setting lv fun _ => 0) (TowerAccumulatorsModel.facts lv)
    (declaresAuthored lv _) (declaresFirst lv _) (declares lv _) formed mem_zero
    (TowerAccumulators.args acc (.const zero)) [] rfl typing

/-- `add-onto acc (succ m) = add-onto (succ acc) m`, with the authored right-hand
side: the instance of `ScrutineeFirst.authored_equation`, the authored right-hand
side written as a term of its own, the scrutinee-first form's right-hand side
the kernel's rewriting of it. -/
theorem TowerAccumulators.addOnto_succ (formed : CtxFormed (rules lv) Γ)
    {acc m : Tm Tower.Head n} (tacc : Typed (rules lv) Γ acc (.const num))
    (tm : Typed (rules lv) Γ m (.const num)) :
    Equal (rules lv) Γ (.app (.app (.const addOnto) acc) (.app (.const succ) m))
      (.app (.app (.const addOnto) (.app (.const succ) acc)) m) (.const num) := by
  have patFormed : CtxFormed (rules lv) (.snoc (.snoc .nil (.const num)) (.const num)) :=
    .snoc (.snoc .nil ⟨_, .sort _, Derivable.mono (sub₂ lv) num_typed₂⟩)
      ⟨_, .sort _, Derivable.mono (sub₂ lv) num_typed₂⟩
  have rhsTyped : Typed (rules lv) (.snoc (.snoc .nil (.const num)) (.const num))
      (.app (.app (.const addOnto) (.app (.const succ) (.var 1))) (.var 0)) (.const num) :=
    TowerAccumulators.addOnto_typed (TowerAccumulators.succ_typed (.var 1)) (.var 0)
  exact ScrutineeFirst.authored_equation (S := setting lv fun _ => 0)
      (TowerAccumulatorsModel.facts lv)
    (roots lv) (heads lv) (declaresAuthored lv _) (declaresFirst lv _) (declares lv _) formed
    mem_succ (rhs := .app (.app (.const addOnto) (.app (.const succ) (.var 1))) (.var 0))
    patFormed rhsTyped rfl (TowerAccumulators.args_typed tacc (TowerAccumulators.succ_typed tm))
    (as := [m]) rfl (fun l hl => by
      obtain rfl : l = 0 := by
        rw [List.length_cons, List.length_nil] at hl
        omega
      exact tm) rfl

end Equations

/-! ## The scrutinee-first form derived from the recursor -/

section Recursor

open TowerAccumulatorsModel

variable {lv : LevelExpr Nat} {n : Nat} {Γ : Ctx Tower.Head n}

/-- The recursion's result family `λ t. Π acc. num` is a family of types of the
recursor's universe. -/
theorem TowerAccumulators.first_motive_typed :
    Typed (rules lv) (ofEntries firstEntries (0 + 1))
      (piRange firstEntries (0 + 1) (1 + 0) (Presentation.rename (teleMove 1 0) resultType))
      (.head (.sort lv)) := by
  have tnum : ∀ {m : Nat} {Δ : Ctx Tower.Head m}, Typed (rules lv) Δ (.const num) (.head u) :=
    fun {_ _} => Derivable.mono (sub₂ lv) num_typed₂
  show Typed (rules lv) (.snoc .nil (.const num)) (.pi (.const num) (.const num)) (.head (.sort lv))
  exact Derivable.cumul (.piForm tnum (.sort _) tnum (.sort _) (.sorts _ _)) (fun _ => Nat.zero_le _)

/-- `add-onto`'s scrutinee-first form written with the numbers' recursor: the
recursor applied to the motive and to the methods built from the form's
right-hand sides. -/
def TowerAccumulators.recursorForm (t : Tm Tower.Head n) : Tm Tower.Head n :=
  recApp numRec (recPre firstEntries 0 (1 + 0) (Presentation.rename (teleMove 1 0) resultType)
    ctors firstBody (fun i => Fin.elim0 i)) t

/-- The scrutinee-first arguments: the number, then the accumulator. -/
def TowerAccumulators.firstArgs (t acc : Tm Tower.Head n) : Sub Tower.Head (0 + 1 + (1 + 0)) n :=
  consSub acc (consSub t fun i => Fin.elim0 i)

theorem TowerAccumulators.firstArgs_typed {t acc : Tm Tower.Head n}
    (tt : Typed (rules lv) Γ t (.const num)) (tacc : Typed (rules lv) Γ acc (.const num)) :
    SubstMor (rules lv) (ofEntries firstEntries (0 + 1 + (1 + 0))) Γ
      (TowerAccumulators.firstArgs t acc) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact tacc
  · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    exact tt

theorem TowerAccumulators.firstArgs_prefix (t acc : Tm Tower.Head n) :
    prefixSub 0 (1 + 0) (TowerAccumulators.firstArgs t acc) = fun i => Fin.elim0 i :=
  funext fun i => Fin.elim0 i

/-- The recursor-built form at zero returns the accumulator. -/
theorem TowerAccumulators.recursorForm_zero (formed : CtxFormed (rules lv) Γ)
    {acc : Tm Tower.Head n} (tacc : Typed (rules lv) Γ acc (.const num)) :
    Equal (rules lv) Γ (.app (TowerAccumulators.recursorForm (.const zero)) acc) acc
      (.const num) := by
  have tzero : Typed (rules lv) Γ (.const zero) (.const num) :=
    Derivable.mono (sub₂ lv) (.const declaredZero₂ num_typed₂ (.sort _))
  have h := (declares lv fun _ => 0).recursor_equation_matched (declaresFirst lv fun _ => 0).scrutinee
    TowerAccumulators.first_motive_typed
    (fun mem => Derivable.mono (declaresFirst lv fun _ => 0).sub₀ ((declaresFirst lv fun _ => 0).bodyTyped mem))
    (TowerAccumulatorsModel.facts lv) (roots lv) (heads lv) formed
    (TowerAccumulators.firstArgs_typed tzero tacc) (i := 0) rfl (as := []) rfl rfl
  rw [TowerAccumulators.firstArgs_prefix] at h
  exact h

/-- The recursor-built form satisfies `add-onto`'s equation with the changing
accumulator: `R (succ m) acc = R m (succ acc)`. -/
theorem TowerAccumulators.recursorForm_succ (formed : CtxFormed (rules lv) Γ)
    {acc m : Tm Tower.Head n} (tacc : Typed (rules lv) Γ acc (.const num))
    (tm : Typed (rules lv) Γ m (.const num)) :
    Equal (rules lv) Γ (.app (TowerAccumulators.recursorForm (.app (.const succ) m)) acc)
      (.app (TowerAccumulators.recursorForm m) (.app (.const succ) acc)) (.const num) := by
  have h := (declares lv fun _ => 0).recursor_equation_matched (declaresFirst lv fun _ => 0).scrutinee
    TowerAccumulators.first_motive_typed
    (fun mem => Derivable.mono (declaresFirst lv fun _ => 0).sub₀ ((declaresFirst lv fun _ => 0).bodyTyped mem))
    (TowerAccumulatorsModel.facts lv) (roots lv) (heads lv) formed
    (TowerAccumulators.firstArgs_typed (TowerAccumulators.succ_typed tm) tacc) (i := 1) rfl
    (as := [m]) rfl rfl
  rw [TowerAccumulators.firstArgs_prefix] at h
  exact h

end Recursor

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
