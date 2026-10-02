import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerNumbers
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.RecursionComputation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.DeclaredComputations
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.ScrutineeFirstEquations
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.CallReordering
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.RecursorDerivation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.RootReflection

/-!
# Recursion over lists with an accumulator in the cumulative tower

Lists of natural numbers, `nil` and `cons : num → list → list`, and two
definitions whose recursive call changes the argument before the list:

`rev-onto acc nil = acc`, `rev-onto acc (cons x xs) = rev-onto (cons x acc) xs`,

`dfa-run q nil = q`, `dfa-run q (cons a w) = dfa-run (step q a) w`,

the second running a transition function `step : num → num → num`, declared
without equations, over a word. Each is admitted through its scrutinee-first
form, recursive on the list, whose hypothesis is a function of the
accumulator:

`rev-onto~scrutinee-first (cons x xs) acc = h (cons x acc)`,
`dfa-run~scrutinee-first (cons a w) q = h (step q a)`,

together with the definition passing the arguments to it. The recursive field
follows a field that is not recursive. Every hypothesis of the normalization
model holds, and all four authored equations hold as typed equalities, with
their authored right-hand sides.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open Mettapedia.TypeTheory.UniverseLevel
open TelescopeAbstraction (closeType applyClosed)
open TowerNumbersModel (num zero succ numRec ctors u mem_zero mem_succ num_ne_zero num_ne_succ
  num_ne_numRec zero_ne_succ zero_ne_numRec succ_ne_numRec)

namespace TowerListAccumulatorsModel

/-! ## Names -/

def list : DeclName := .mkSimple "list"
def nil : DeclName := .mkSimple "nil"
def cons : DeclName := .mkSimple "cons"
def listRec : DeclName := .mkSimple "list-rec"
def step : DeclName := .mkSimple "step"
def revOntoFirst : DeclName := .mkSimple "rev-onto~scrutinee-first"
def revOnto : DeclName := .mkSimple "rev-onto"
def runFirst : DeclName := .mkSimple "dfa-run~scrutinee-first"
def run : DeclName := .mkSimple "dfa-run"

/-- The fields of `cons`: a number, then the rest of the list. -/
def consFields : List (Field Tower.Head) := [.closed (.const num), .recursive]

/-- The constructors of lists. -/
def listCtors : List (DeclName × List (Field Tower.Head)) := [(nil, []), (cons, consFields)]

theorem mem_nil : ((nil, []) : DeclName × List (Field Tower.Head)) ∈ listCtors :=
  List.mem_cons_self ..

theorem mem_cons : ((cons, consFields) : DeclName × List (Field Tower.Head)) ∈ listCtors :=
  List.mem_cons_of_mem _ (List.mem_cons_self ..)

/-! ## Declared types and right-hand sides -/

/-- `num → num → num`. -/
def stepType : Tm Tower.Head 0 := .pi (.const num) (.pi (.const num) (.const num))

/-- The authored telescope of `rev-onto`: the accumulator, then the list. -/
def revEntryTypes : Nat → Tm Tower.Head 0 := fun _ => .const list

/-- The authored telescope of `dfa-run`: the state, then the word. -/
def runEntryTypes : Nat → Tm Tower.Head 0
  | 0 => .const num
  | _ + 1 => .const list

abbrev revFirstEntries : (i : Nat) → Tm Tower.Head i :=
  fun i => liftClosed (scrutineeFirst revEntryTypes 1 i)

abbrev runFirstEntries : (i : Nat) → Tm Tower.Head i :=
  fun i => liftClosed (scrutineeFirst runEntryTypes 1 i)

abbrev revTele : Ctx Tower.Head (1 + 1 + 0) :=
  ofEntries (fun i => liftClosed (revEntryTypes i)) (1 + 1 + 0)

abbrev runTele : Ctx Tower.Head (1 + 1 + 0) :=
  ofEntries (fun i => liftClosed (runEntryTypes i)) (1 + 1 + 0)

def revResult : Tm Tower.Head (1 + 1 + 0) := .const list
def runResult : Tm Tower.Head (1 + 1 + 0) := .const num

/-- The scrutinee-first right-hand sides of `rev-onto`: the accumulator at
`nil`, and at `cons x xs` the hypothesis, a function of the accumulator, at
`cons x acc`. -/
def revBody : (k : DeclName) → (fields : List (Field Tower.Head)) →
    Tm Tower.Head (0 + fields.length + (1 + 0) + (recPositions fields).length)
  | _, [] => .var ⟨0, by decide⟩
  | _, [.closed _, .recursive] =>
      .app (.var ⟨0, (by decide : (0 : Nat) < 4)⟩)
        (.app (.app (.const cons) (.var ⟨3, (by decide : (3 : Nat) < 4)⟩)) (.var ⟨1, (by decide : (1 : Nat) < 4)⟩))
  | _, _ => .const revOntoFirst

/-- The scrutinee-first right-hand sides of `dfa-run`: the state at `nil`, and
at `cons a w` the hypothesis at `step q a`. -/
def runBody : (k : DeclName) → (fields : List (Field Tower.Head)) →
    Tm Tower.Head (0 + fields.length + (1 + 0) + (recPositions fields).length)
  | _, [] => .var ⟨0, by decide⟩
  | _, [.closed _, .recursive] =>
      .app (.var ⟨0, (by decide : (0 : Nat) < 4)⟩)
        (.app (.app (.const step) (.var ⟨1, (by decide : (1 : Nat) < 4)⟩)) (.var ⟨3, (by decide : (3 : Nat) < 4)⟩))
  | _, _ => .const runFirst

def revFirstType : Tm Tower.Head 0 :=
  closeType (ofEntries revFirstEntries (0 + 1 + (1 + 0))) (Presentation.rename (teleMove 1 0) revResult)
def runFirstType : Tm Tower.Head 0 :=
  closeType (ofEntries runFirstEntries (0 + 1 + (1 + 0))) (Presentation.rename (teleMove 1 0) runResult)
def revType : Tm Tower.Head 0 := closeType revTele revResult
def runType : Tm Tower.Head 0 := closeType runTele runResult

def revRhs : Tm Tower.Head (1 + 1 + 0) := definitionBody revEntryTypes revOntoFirst 1 0
def runRhs : Tm Tower.Head (1 + 1 + 0) := definitionBody runEntryTypes runFirst 1 0

theorem revFirstType_eq : revFirstType = .pi (.const list) (.pi (.const list) (.const list)) := rfl
theorem runFirstType_eq : runFirstType = .pi (.const list) (.pi (.const num) (.const num)) := rfl
theorem revType_eq : revType = .pi (.const list) (.pi (.const list) (.const list)) := rfl
theorem runType_eq : runType = .pi (.const num) (.pi (.const list) (.const num)) := rfl
theorem revRhs_eq : revRhs = .app (.app (.const revOntoFirst) (.var 0)) (.var 1) := rfl
theorem runRhs_eq : runRhs = .app (.app (.const runFirst) (.var 0)) (.var 1) := rfl
theorem consType_eq :
    ctorType list consFields = .pi (.const num) (.pi (.const list) (.const list)) := rfl

/-! ## Stages -/

/-- The numbers and `list`. -/
def listStage₁ : Rules Tower.Head :=
  { Tower.rules with
    constantType := fun name =>
      if name = list then some (.head u) else TowerNumbersModel.rules₂.constantType name }

/-- With the constructors of lists. -/
def listStage₂ : Rules Tower.Head :=
  { Tower.rules with
    constantType := fun name =>
      if name = nil then some (ctorType list [])
      else if name = cons then some (ctorType list consFields)
      else listStage₁.constantType name }

/-- With `step`: the stage in which the scrutinee-first bodies are typed. -/
def bodyStage : Rules Tower.Head :=
  { Tower.rules with
    constantType := fun name => if name = step then some stepType else listStage₂.constantType name }

/-- With the scrutinee-first forms: the stage in which the authored right-hand
sides are typed. -/
def defStage : Rules Tower.Head :=
  { Tower.rules with
    constantType := fun name =>
      if name = revOntoFirst then some revFirstType
      else if name = runFirst then some runFirstType
      else bodyStage.constantType name }

variable (lv : LevelExpr Nat)

/-- The declared types of the package. -/
def constantType : DeclName → Option (Tm Tower.Head 0) := fun name =>
  if name = revOnto then some revType
  else if name = run then some runType
  else if name = listRec then some (recType list (.sort lv) listCtors)
  else if name = numRec then some (recType num (.sort lv) ctors)
  else defStage.constantType name

/-- The computations: both recursors, and the equations of the four
definitions. -/
def computations : List (DeclName × RootComputation Tower.Head) :=
  [(numRec, iotaComputation numRec ctors),
   (listRec, iotaComputation listRec listCtors),
   (revOntoFirst, recursionComputation revOntoFirst listCtors revFirstEntries 0 (1 + 0) revBody),
   (revOnto, definitionComputation revOnto revTele revRhs),
   (runFirst, recursionComputation runFirst listCtors runFirstEntries 0 (1 + 0) runBody),
   (run, definitionComputation run runTele runRhs)]

/-- The tower with numbers, lists, their recursors into level `lv`, `step`,
`rev-onto` and `dfa-run` with their scrutinee-first forms. -/
def rules : Rules Tower.Head :=
  { Tower.rules with
    constantType := constantType lv
    computation := RootComputation.unionAll computations }

/-! ## Roles -/

/-- The roles of the declared constants. -/
def roles : Roles Tower.Head := fun name =>
  if name = list then .inductive listCtors
  else if name = nil then .constructor 0
  else if name = cons then .constructor 2
  else if name = listRec then .computes 4 (.split 3 .constructor fun _ => .leaf)
  else if name = revOntoFirst then .computes (0 + 1 + (1 + 0)) (.split 0 .constructor fun _ => .leaf)
  else if name = revOnto then .computes (1 + 1 + 0) .leaf
  else if name = runFirst then .computes (0 + 1 + (1 + 0)) (.split 0 .constructor fun _ => .leaf)
  else if name = run then .computes (1 + 1 + 0) .leaf
  else TowerNumbersModel.roles name

theorem roles_num : roles num = .inductive ctors := rfl
theorem roles_zero : roles zero = .constructor 0 := rfl
theorem roles_succ : roles succ = .constructor 1 := rfl
theorem roles_numRec : roles numRec = .computes 4 (.split 3 .constructor fun _ => .leaf) := rfl
theorem roles_list : roles list = .inductive listCtors := rfl
theorem roles_nil : roles nil = .constructor 0 := rfl
theorem roles_cons : roles cons = .constructor 2 := rfl
theorem roles_listRec : roles listRec = .computes 4 (.split 3 .constructor fun _ => .leaf) := rfl
theorem roles_revFirst : roles revOntoFirst = .computes (0 + 1 + (1 + 0)) (.split 0 .constructor fun _ => .leaf) := rfl
theorem roles_revOnto : roles revOnto = .computes (1 + 1 + 0) .leaf := rfl
theorem roles_runFirst : roles runFirst = .computes (0 + 1 + (1 + 0)) (.split 0 .constructor fun _ => .leaf) := rfl
theorem roles_run : roles run = .computes (1 + 1 + 0) .leaf := rfl
theorem roles_step : roles step = .rigid := rfl

/-- The inductive types are `num` and `list`. -/
theorem roles_inductive {T : DeclName} {cs : List (DeclName × List (Field Tower.Head))}
    (role : roles T = .inductive cs) :
    (T = num ∧ cs = ctors) ∨ (T = list ∧ cs = listCtors) := by
  unfold roles at role
  split at role
  · rename_i h
    exact .inr ⟨h, (Role.inductive.inj role).symm⟩
  split at role
  · cases role
  split at role
  · cases role
  split at role
  · cases role
  split at role
  · cases role
  split at role
  · cases role
  split at role
  · cases role
  split at role
  · cases role
  exact .inl (TowerNumbersModel.roles_inductive role)

theorem constructorsDeclared : ConstructorsDeclared roles where
  arity := by
    intro T cs k fields role mem
    rcases roles_inductive role with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
      rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact roles_zero
      · exact roles_succ
    · simp only [listCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
      rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact roles_nil
      · exact roles_cons
  distinct := by
    intro T cs role
    rcases roles_inductive role with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · decide
    · decide

/-! ## The shape of the computation -/

theorem computations_spine : ∀ entry ∈ computations, SpineShaped roles entry.2 := by
  intro entry mem
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun _ _ _ step => IotaStep.spine (T := num) roles_num roles_numRec
      constructorsDeclared step
  · exact fun _ _ _ step => IotaStep.spine (T := list) roles_list roles_listRec
      constructorsDeclared step
  · exact fun _ _ _ step => RecursionStep.spine roles_list constructorsDeclared roles_revFirst step
  · exact definitionComputation_spine roles_revOnto
  · exact fun _ _ _ step => RecursionStep.spine roles_list constructorsDeclared roles_runFirst step
  · exact definitionComputation_spine roles_run

theorem computations_headed : ∀ entry ∈ computations, HeadedBy entry.1 entry.2 := by
  intro entry mem
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact iotaComputation_headed
  · exact iotaComputation_headed
  · exact recursionComputation_headed
  · exact definitionComputation_headed
  · exact recursionComputation_headed
  · exact definitionComputation_headed

theorem computations_deterministic : ∀ entry ∈ computations, Deterministic entry.2 := by
  intro entry mem
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact fun _ _ _ _ step step' =>
      IotaStep.deterministic (T := num) roles_num constructorsDeclared step step'
  · exact fun _ _ _ _ step step' =>
      IotaStep.deterministic (T := list) roles_list constructorsDeclared step step'
  · exact fun _ _ _ _ step step' =>
      RecursionStep.deterministic roles_list constructorsDeclared step step'
  · exact definitionComputation_deterministic
  · exact fun _ _ _ _ step step' =>
      RecursionStep.deterministic roles_list constructorsDeclared step step'
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

/-! ## Stage inclusions -/

theorem numbers_to_list₁ {name : DeclName} {type : Tm Tower.Head 0}
    (declared : TowerNumbersModel.rules₂.constantType name = some type) :
    listStage₁.constantType name = some type := by
  show (if name = list then some (.head u) else TowerNumbersModel.rules₂.constantType name) = _
  rw [if_neg]
  · exact declared
  · rintro rfl
    have none : TowerNumbersModel.rules₂.constantType list = none := rfl
    rw [none] at declared
    cases declared

theorem list₁_to_list₂ {name : DeclName} {type : Tm Tower.Head 0}
    (declared : listStage₁.constantType name = some type) :
    listStage₂.constantType name = some type := by
  show (if name = nil then some (ctorType list [])
    else if name = cons then some (ctorType list consFields)
    else listStage₁.constantType name) = _
  by_cases h₁ : name = nil
  · subst h₁
    have none : listStage₁.constantType nil = none := rfl
    rw [none] at declared
    cases declared
  · by_cases h₂ : name = cons
    · subst h₂
      have none : listStage₁.constantType cons = none := rfl
      rw [none] at declared
      cases declared
    · rw [if_neg h₁, if_neg h₂]
      exact declared

theorem list₂_to_body {name : DeclName} {type : Tm Tower.Head 0}
    (declared : listStage₂.constantType name = some type) :
    bodyStage.constantType name = some type := by
  show (if name = step then some stepType else listStage₂.constantType name) = _
  rw [if_neg]
  · exact declared
  · rintro rfl
    have none : listStage₂.constantType step = none := rfl
    rw [none] at declared
    cases declared

theorem body_to_def {name : DeclName} {type : Tm Tower.Head 0}
    (declared : bodyStage.constantType name = some type) :
    defStage.constantType name = some type := by
  show (if name = revOntoFirst then some revFirstType
    else if name = runFirst then some runFirstType
    else bodyStage.constantType name) = _
  by_cases h₁ : name = revOntoFirst
  · subst h₁
    have none : bodyStage.constantType revOntoFirst = none := rfl
    rw [none] at declared
    cases declared
  · by_cases h₂ : name = runFirst
    · subst h₂
      have none : bodyStage.constantType runFirst = none := rfl
      rw [none] at declared
      cases declared
    · rw [if_neg h₁, if_neg h₂]
      exact declared

theorem def_to_rules {name : DeclName} {type : Tm Tower.Head 0}
    (declared : defStage.constantType name = some type) :
    (rules lv).constantType name = some type := by
  show (if name = revOnto then some revType
    else if name = run then some runType
    else if name = listRec then some (recType list (.sort lv) listCtors)
    else if name = numRec then some (recType num (.sort lv) ctors)
    else defStage.constantType name) = _
  by_cases h₁ : name = revOnto
  · subst h₁
    have none : defStage.constantType revOnto = none := rfl
    rw [none] at declared
    cases declared
  · by_cases h₂ : name = run
    · subst h₂
      have none : defStage.constantType run = none := rfl
      rw [none] at declared
      cases declared
    · by_cases h₃ : name = listRec
      · subst h₃
        have none : defStage.constantType listRec = none := rfl
        rw [none] at declared
        cases declared
      · by_cases h₄ : name = numRec
        · subst h₄
          have none : defStage.constantType numRec = none := rfl
          rw [none] at declared
          cases declared
        · rw [if_neg h₁, if_neg h₂, if_neg h₃, if_neg h₄]
          exact declared

theorem sub_numbers : RulesSub TowerNumbersModel.rules₂ (rules lv) :=
  ⟨id, id, id, id, id, fun declared =>
    def_to_rules lv (body_to_def (list₂_to_body (list₁_to_list₂ (numbers_to_list₁ declared)))),
    fun step => nomatch step⟩
theorem sub_list₁ : RulesSub listStage₁ (rules lv) :=
  ⟨id, id, id, id, id, fun declared =>
    def_to_rules lv (body_to_def (list₂_to_body (list₁_to_list₂ declared))), fun step => nomatch step⟩
theorem sub_list₂ : RulesSub listStage₂ (rules lv) :=
  ⟨id, id, id, id, id, fun declared => def_to_rules lv (body_to_def (list₂_to_body declared)),
    fun step => nomatch step⟩
theorem sub_body : RulesSub bodyStage (rules lv) :=
  ⟨id, id, id, id, id, fun declared => def_to_rules lv (body_to_def declared),
    fun step => nomatch step⟩
theorem sub_def : RulesSub defStage (rules lv) :=
  ⟨id, id, id, id, id, fun declared => def_to_rules lv declared, fun step => nomatch step⟩
theorem sub_rules₁ : RulesSub TowerNumbersModel.rules₁ (rules lv) :=
  ⟨id, id, id, id, id, fun {name type} declared => (by
      simp only [TowerNumbersModel.rules₁] at declared
      split at declared
      · rename_i h
        subst h
        cases declared
        rfl
      · cases declared), fun step => nomatch step⟩
theorem sub_bodyToDef : RulesSub bodyStage defStage :=
  ⟨id, id, id, id, id, fun declared => body_to_def declared, fun step => nomatch step⟩

/-! ## Typings in the stages -/

section Typings

variable {R : Rules Tower.Head}

theorem const_type_typed (headTyping : ∀ l, R.headTyping (.sort l) (.sort (.succ l)))
    (isUniverse : ∀ l, R.isUniverse (.sort l)) {T : DeclName}
    (declared : R.constantType T = some (.head u)) {n : Nat} {Γ : Ctx Tower.Head n} :
    Typed R Γ (.const T) (.head u) :=
  .const declared (.headType (headTyping _)) (isUniverse _)

end Typings

theorem num_typedB {n : Nat} {Γ : Ctx Tower.Head n} : Typed bodyStage Γ (.const num) (.head u) :=
  const_type_typed LevelTower.HeadTyping.sort LevelTower.IsUniverse.sort rfl
theorem list_typedB {n : Nat} {Γ : Ctx Tower.Head n} : Typed bodyStage Γ (.const list) (.head u) :=
  const_type_typed LevelTower.HeadTyping.sort LevelTower.IsUniverse.sort rfl
theorem num_typedD {n : Nat} {Γ : Ctx Tower.Head n} : Typed defStage Γ (.const num) (.head u) :=
  const_type_typed LevelTower.HeadTyping.sort LevelTower.IsUniverse.sort rfl
theorem list_typedD {n : Nat} {Γ : Ctx Tower.Head n} : Typed defStage Γ (.const list) (.head u) :=
  const_type_typed LevelTower.HeadTyping.sort LevelTower.IsUniverse.sort rfl

theorem cons_typedB {n : Nat} {Γ : Ctx Tower.Head n} :
    Typed bodyStage Γ (.const cons) (.pi (.const num) (.pi (.const list) (.const list))) :=
  .const (type := ctorType list consFields) rfl
    (.piForm num_typedB (.sort _) (.piForm list_typedB (.sort _) list_typedB (.sort _) (.sorts _ _))
      (.sort _) (.sorts _ _)) (.sort _)

theorem step_typedB {n : Nat} {Γ : Ctx Tower.Head n} :
    Typed bodyStage Γ (.const step) (.pi (.const num) (.pi (.const num) (.const num))) :=
  .const (type := stepType) rfl
    (.piForm num_typedB (.sort _) (.piForm num_typedB (.sort _) num_typedB (.sort _) (.sorts _ _))
      (.sort _) (.sorts _ _)) (.sort _)

theorem revFirst_typedD {n : Nat} {Γ : Ctx Tower.Head n} :
    Typed defStage Γ (.const revOntoFirst) (.pi (.const list) (.pi (.const list) (.const list))) :=
  .const (type := revFirstType) rfl
    (.piForm list_typedD (.sort _) (.piForm list_typedD (.sort _) list_typedD (.sort _) (.sorts _ _))
      (.sort _) (.sorts _ _)) (.sort _)

theorem runFirst_typedD {n : Nat} {Γ : Ctx Tower.Head n} :
    Typed defStage Γ (.const runFirst) (.pi (.const list) (.pi (.const num) (.const num))) :=
  .const (type := runFirstType) rfl
    (.piForm list_typedD (.sort _) (.piForm num_typedD (.sort _) num_typedD (.sort _) (.sorts _ _))
      (.sort _) (.sorts _ _)) (.sort _)

/-- A type `A → B → C` of three type constants of a universe. -/
theorem arrowType_typed {R : Rules Tower.Head} {A B C : DeclName}
    (tA : ∀ {n : Nat} {Γ : Ctx Tower.Head n}, Typed R Γ (.const A) (.head u))
    (tB : ∀ {n : Nat} {Γ : Ctx Tower.Head n}, Typed R Γ (.const B) (.head u))
    (tC : ∀ {n : Nat} {Γ : Ctx Tower.Head n}, Typed R Γ (.const C) (.head u))
    (hu : R.isUniverse u) (join : ∀ l r, R.join (.sort l) (.sort r) (.sort (.max l r)))
    (isU : ∀ l, R.isUniverse (.sort l)) :
    ∃ w, R.isUniverse w ∧ Typed R .nil (.pi (.const A) (.pi (.const B) (.const C))) (.head w) :=
  ⟨_, isU _, .piForm tA hu (.piForm tB hu tC hu (join _ _)) (isU _) (join _ _)⟩

/-- The list recursor's type is typed at the second stage of lists. -/
theorem listRecType_typed : ∃ w, Tower.IsUniverse w ∧
    Typed listStage₂ .nil (recType list (.sort lv) listCtors) (.head w) := by
  have hu : listStage₂.isUniverse u := .sort _
  have hv : listStage₂.isUniverse (.sort lv) := .sort _
  have tNum : ∀ {n : Nat} {Γ : Ctx Tower.Head n}, Typed listStage₂ Γ (.const num) (.head u) :=
    fun {_ _} => const_type_typed LevelTower.HeadTyping.sort LevelTower.IsUniverse.sort rfl
  have tList : ∀ {n : Nat} {Γ : Ctx Tower.Head n}, Typed listStage₂ Γ (.const list) (.head u) :=
    fun {_ _} => const_type_typed LevelTower.HeadTyping.sort LevelTower.IsUniverse.sort rfl
  have tNil : ∀ {n : Nat} {Γ : Ctx Tower.Head n}, Typed listStage₂ Γ (.const nil) (.const list) :=
    fun {_ _} => .const (type := ctorType list []) rfl tList hu
  have tCons : ∀ {n : Nat} {Γ : Ctx Tower.Head n},
      Typed listStage₂ Γ (.const cons) (.pi (.const num) (.pi (.const list) (.const list))) :=
    fun {_ _} => .const (type := ctorType list consFields) rfl
      (.piForm tNum hu (.piForm tList hu tList hu (.sorts _ _)) (.sort _) (.sorts _ _)) (.sort _)
  -- the motive's type
  have tE0 : Typed listStage₂ .nil (.pi (.const list) (.head (.sort lv)))
      (.head (.sort (.max (.const 0) (.succ lv)))) :=
    .piForm tList hu (.headType (.sort lv)) (.sort _) (.sorts _ _)
  -- the case of nil
  let Γ₁ : Ctx Tower.Head 1 := .snoc .nil (.pi (.const list) (.head (.sort lv)))
  have tP₁ : Typed listStage₂ Γ₁ (.var 0) (.pi (.const list) (.head (.sort lv))) := .var 0
  have tE1 : Typed listStage₂ Γ₁ (.app (.var 0) (.const nil)) (.head (.sort lv)) :=
    .appElim tP₁ tNil
  -- the case of cons
  let Γ₂ : Ctx Tower.Head 2 := .snoc Γ₁ (.app (.var 0) (.const nil))
  let Γ₂x : Ctx Tower.Head 3 := .snoc Γ₂ (.const num)
  let Γ₂xs : Ctx Tower.Head 4 := .snoc Γ₂x (.const list)
  have tP₃ : Typed listStage₂ Γ₂xs (.var 3) (.pi (.const list) (.head (.sort lv))) := .var 3
  have tXs : Typed listStage₂ Γ₂xs (.var 0) (.const list) := .var 0
  have tIH : Typed listStage₂ Γ₂xs (.app (.var 3) (.var 0)) (.head (.sort lv)) := .appElim tP₃ tXs
  let Γ₂h : Ctx Tower.Head 5 := .snoc Γ₂xs (.app (.var 3) (.var 0))
  have tX' : Typed listStage₂ Γ₂h (.var 2) (.const num) := .var 2
  have tXs' : Typed listStage₂ Γ₂h (.var 1) (.const list) := .var 1
  have tConsXs : Typed listStage₂ Γ₂h (.app (.app (.const cons) (.var 2)) (.var 1)) (.const list) :=
    .appElim (A := .const list) (B := .const list) (.appElim tCons tX') tXs'
  have tP₄ : Typed listStage₂ Γ₂h (.var 4) (.pi (.const list) (.head (.sort lv))) := .var 4
  have tGoal : Typed listStage₂ Γ₂h (.app (.var 4) (.app (.app (.const cons) (.var 2)) (.var 1)))
      (.head (.sort lv)) :=
    .appElim tP₄ tConsXs
  have tHyp := Derivable.piForm tIH hv tGoal hv (.sorts lv lv)
  have tXsHyp := Derivable.piForm (tList (Γ := Γ₂x)) hu tHyp (.sort _) (.sorts _ _)
  have tE2 := Derivable.piForm (tNum (Γ := Γ₂)) hu tXsHyp (.sort _) (.sorts _ _)
  -- the scrutinee and the result
  let Γ₃ : Ctx Tower.Head 3 :=
    .snoc Γ₂ (.pi (.const num) (.pi (.const list) (.pi (.app (.var 3) (.var 0))
      (.app (.var 4) (.app (.app (.const cons) (.var 2)) (.var 1))))))
  let Γ₄ : Ctx Tower.Head 4 := .snoc Γ₃ (.const list)
  have tP₅ : Typed listStage₂ Γ₄ (.var 3) (.pi (.const list) (.head (.sort lv))) := .var 3
  have tT : Typed listStage₂ Γ₄ (.var 0) (.const list) := .var 0
  have tBody : Typed listStage₂ Γ₄ (.app (.var 3) (.var 0)) (.head (.sort lv)) := .appElim tP₅ tT
  -- closing the telescope
  have t4 := Derivable.piForm (tList (Γ := Γ₃)) hu tBody hv (.sorts _ _)
  have t3 := Derivable.piForm tE2 (.sort _) t4 (.sort _) (.sorts _ _)
  have t2 := Derivable.piForm tE1 hv t3 (.sort _) (.sorts _ _)
  have t1 := Derivable.piForm tE0 (.sort _) t2 (.sort _) (.sorts _ _)
  exact ⟨_, .sort _, t1⟩

/-! ## The package in which the kernel checks the scrutinee-first forms

The numbers, the lists, `step` and the two recursors, computing, without the
recursive definitions. The kernel checks a scrutinee-first form's right-hand
sides with the form declared and not computing; that check is read in this
package's normalization model. -/

/-- The declared types of the checking package. -/
def stageConstantType : DeclName → Option (Tm Tower.Head 0) := fun name =>
  if name = listRec then some (recType list (.sort lv) listCtors)
  else if name = numRec then some (recType num (.sort lv) ctors)
  else bodyStage.constantType name

/-- The recursors' computations. -/
def stageComputations : List (DeclName × RootComputation Tower.Head) :=
  [(numRec, iotaComputation numRec ctors), (listRec, iotaComputation listRec listCtors)]

/-- The numbers, the lists, `step` and the two recursors. -/
def stageRules : Rules Tower.Head :=
  { Tower.rules with
    constantType := stageConstantType lv
    computation := RootComputation.unionAll stageComputations }

theorem stageComputations_sub : ∀ entry ∈ stageComputations, entry ∈ computations := by
  intro entry mem
  simp only [stageComputations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact List.mem_cons_self ..
  · exact List.mem_cons_of_mem _ (List.mem_cons_self ..)

theorem stageShape : RootShape (stageRules lv) roles where
  spine := fun step => RootComputation.unionAll_spine
    (fun entry mem => computations_spine entry (stageComputations_sub entry mem)) step
  deterministic := fun step step' =>
    (RootComputation.unionAll_deterministic (by decide)
      (fun entry mem => computations_headed entry (stageComputations_sub entry mem))
      (fun entry mem => computations_deterministic entry (stageComputations_sub entry mem))
      step step').symm

/-- The tower's level model, for the checking package. -/
def stageLevels (valuation : Nat → Nat) : LevelModel (stageRules lv) ℕ where
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

/-- The normalization setting of the checking package. -/
def stageSetting (valuation : Nat → Nat) : Setting Tower.Head ℕ where
  R := stageRules lv
  roles := roles
  E := declarative (stageRules lv)
  levels := stageLevels lv valuation
  shape := stageShape lv
  constructors := constructorsDeclared

theorem stageLaws (valuation : Nat → Nat) :
    (stageSetting lv valuation).E.Laws (stageSetting lv valuation).R
      (stageSetting lv valuation).roles :=
  declarative_laws roles (stageLevels lv valuation)

theorem body_to_stage {name : DeclName} {type : Tm Tower.Head 0}
    (declared : bodyStage.constantType name = some type) :
    (stageRules lv).constantType name = some type := by
  show (if name = listRec then some (recType list (.sort lv) listCtors)
    else if name = numRec then some (recType num (.sort lv) ctors)
    else bodyStage.constantType name) = _
  by_cases h₁ : name = listRec
  · subst h₁
    have none : bodyStage.constantType listRec = none := rfl
    rw [none] at declared
    cases declared
  · by_cases h₂ : name = numRec
    · subst h₂
      have none : bodyStage.constantType numRec = none := rfl
      rw [none] at declared
      cases declared
    · rw [if_neg h₁, if_neg h₂]
      exact declared

theorem stage_to_rules {name : DeclName} {type : Tm Tower.Head 0}
    (declared : (stageRules lv).constantType name = some type) :
    (rules lv).constantType name = some type := by
  by_cases h₁ : name = listRec
  · subst h₁
    have e₁ : (stageRules lv).constantType listRec = some (recType list (.sort lv) listCtors) := rfl
    have e₂ : (rules lv).constantType listRec = some (recType list (.sort lv) listCtors) := rfl
    rw [e₁] at declared
    rw [e₂]
    exact declared
  · by_cases h₂ : name = numRec
    · subst h₂
      have e₁ : (stageRules lv).constantType numRec = some (recType num (.sort lv) ctors) := rfl
      have e₂ : (rules lv).constantType numRec = some (recType num (.sort lv) ctors) := rfl
      rw [e₁] at declared
      rw [e₂]
      exact declared
    · change (if name = listRec then some (recType list (.sort lv) listCtors)
        else if name = numRec then some (recType num (.sort lv) ctors)
        else bodyStage.constantType name) = some type at declared
      rw [if_neg h₁, if_neg h₂] at declared
      exact def_to_rules lv (body_to_def declared)

theorem stage_sub_numbers : RulesSub TowerNumbersModel.rules₂ (stageRules lv) :=
  ⟨id, id, id, id, id, fun declared =>
    body_to_stage lv (list₂_to_body (list₁_to_list₂ (numbers_to_list₁ declared))),
    fun step => nomatch step⟩
theorem stage_sub_list₁ : RulesSub listStage₁ (stageRules lv) :=
  ⟨id, id, id, id, id, fun declared => body_to_stage lv (list₂_to_body (list₁_to_list₂ declared)),
    fun step => nomatch step⟩
theorem stage_sub_list₂ : RulesSub listStage₂ (stageRules lv) :=
  ⟨id, id, id, id, id, fun declared => body_to_stage lv (list₂_to_body declared),
    fun step => nomatch step⟩
theorem stage_sub_body : RulesSub bodyStage (stageRules lv) :=
  ⟨id, id, id, id, id, fun declared => body_to_stage lv declared, fun step => nomatch step⟩
theorem stage_sub_rules₁ : RulesSub TowerNumbersModel.rules₁ (stageRules lv) :=
  ⟨id, id, id, id, id, fun {name type} declared => (by
      simp only [TowerNumbersModel.rules₁] at declared
      split at declared
      · rename_i h
        subst h
        cases declared
        rfl
      · cases declared), fun step => nomatch step⟩
theorem stage_sub_rules : RulesSub (stageRules lv) (rules lv) :=
  ⟨id, id, id, id, id, fun declared => stage_to_rules lv declared, fun step => by
    obtain ⟨entry, mem, h⟩ := RootComputation.unionAll_step step
    exact RootComputation.step_unionAll (stageComputations_sub entry mem) h⟩

theorem num_typedS {n : Nat} {Γ : Ctx Tower.Head n} : Typed (stageRules lv) Γ (.const num) (.head u) :=
  const_type_typed LevelTower.HeadTyping.sort LevelTower.IsUniverse.sort rfl
theorem list_typedS {n : Nat} {Γ : Ctx Tower.Head n} :
    Typed (stageRules lv) Γ (.const list) (.head u) :=
  const_type_typed LevelTower.HeadTyping.sort LevelTower.IsUniverse.sort rfl

/-- Head equality steps preserve typing in the checking package. -/
theorem stageHeads : HeadPreserving (stageRules lv) := by
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
          have raise : (stageRules lv).cumulative (.sort (.succ r)) (.sort (.succ l)) := by
            intro ν
            show LevelExpr.eval ν r + 1 ≤ LevelExpr.eval ν l + 1
            have := same ν
            omega
          exact Typed.subsume (.cumul (.headType (.sort r)) raise) le

theorem stageAlgebra : CumulativeAlgebra (stageRules lv) where
  trans := TowerModel.algebra.trans
  same_left := TowerModel.algebra.same_left
  same_right := TowerModel.algebra.same_right
  join_least := TowerModel.algebra.join_least

/-- The declared types of the checking package are types. -/
theorem stage_typesFormed : DeclaredTypesFormed (stageRules lv) := by
  intro name type declared
  change (if name = listRec then some (recType list (.sort lv) listCtors)
    else if name = numRec then some (recType num (.sort lv) ctors)
    else if name = step then some stepType
    else if name = nil then some (ctorType list [])
    else if name = cons then some (ctorType list consFields)
    else if name = list then some (.head u)
    else if name = num then some (.head u)
    else if name = zero then some (ctorType num [])
    else if name = succ then some (ctorType num [.recursive])
    else none) = some type at declared
  have tNum := num_typedS lv (Γ := .nil)
  have tList := list_typedS lv (Γ := .nil)
  split at declared
  · cases declared
    obtain ⟨w, hw, t⟩ := listRecType_typed lv
    exact ⟨w, hw, Derivable.mono (stage_sub_list₂ lv) t⟩
  split at declared
  · cases declared
    obtain ⟨w, hw, t⟩ := TowerNumbersModel.recType_typed lv
    exact ⟨w, hw, Derivable.mono (stage_sub_numbers lv) t⟩
  split at declared
  · cases declared
    exact arrowType_typed (R := stageRules lv) (num_typedS lv) (num_typedS lv) (num_typedS lv)
      (.sort _) (fun _ _ => .sorts _ _) (fun _ => .sort _)
  split at declared
  · cases declared
    exact ⟨_, .sort _, tList⟩
  split at declared
  · cases declared
    exact ⟨_, .sort _, .piForm tNum (.sort _) (.piForm (list_typedS lv) (.sort _) (list_typedS lv)
      (.sort _) (.sorts _ _)) (.sort _) (.sorts _ _)⟩
  split at declared
  · cases declared
    exact ⟨_, .sort _, .headType (LevelTower.HeadTyping.sort _)⟩
  split at declared
  · cases declared
    exact ⟨_, .sort _, .headType (LevelTower.HeadTyping.sort _)⟩
  split at declared
  · cases declared
    exact ⟨_, .sort _, tNum⟩
  split at declared
  · cases declared
    exact ⟨_, .sort _, .piForm tNum (.sort _) (num_typedS lv) (.sort _) (.sorts _ _)⟩
  cases declared

/-! ### The checking packages of the two scrutinee-first forms -/

/-- The checking package with the scrutinee-first form `f` declared at `fType`
and not computing. -/
def checkStage (f : DeclName) (fType : Tm Tower.Head 0) : Rules Tower.Head :=
  { stageRules lv with
    constantType := fun name => if name = f then some fType else (stageRules lv).constantType name }

section CheckStage

variable {f : DeclName} (fType : Tm Tower.Head 0) (hf : f = revOntoFirst ∨ f = runFirst)
include hf

theorem checkStage_declared {c : DeclName} {type : Tm Tower.Head 0}
    (hc : c = list ∨ c = num ∨ c = cons ∨ c = step)
    (declared : (stageRules lv).constantType c = some type) :
    (checkStage lv f fType).constantType c = some type := by
  have hcf : c ≠ f := by
    rcases hf with rfl | rfl <;> rcases hc with rfl | rfl | rfl | rfl <;> decide
  simp only [checkStage, if_neg hcf]
  exact declared

/-- No type the checking package declares mentions `f`. -/
theorem stage_typesFree {c : DeclName} {type : Tm Tower.Head 0}
    (declared : (stageRules lv).constantType c = some type) : ConstFree f type := by
  refine ConstFree.of_mentions ?_
  change (if c = listRec then some (recType list (.sort lv) listCtors)
    else if c = numRec then some (recType num (.sort lv) ctors)
    else if c = step then some stepType
    else if c = nil then some (ctorType list [])
    else if c = cons then some (ctorType list consFields)
    else if c = list then some (.head u)
    else if c = num then some (.head u)
    else if c = zero then some (ctorType num [])
    else if c = succ then some (ctorType num [.recursive])
    else none) = some type at declared
  split at declared
  · cases declared; rcases hf with rfl | rfl <;> rfl
  split at declared
  · cases declared; rcases hf with rfl | rfl <;> rfl
  split at declared
  · cases declared; rcases hf with rfl | rfl <;> rfl
  split at declared
  · cases declared; rcases hf with rfl | rfl <;> rfl
  split at declared
  · cases declared; rcases hf with rfl | rfl <;> rfl
  split at declared
  · cases declared; rcases hf with rfl | rfl <;> rfl
  split at declared
  · cases declared; rcases hf with rfl | rfl <;> rfl
  split at declared
  · cases declared; rcases hf with rfl | rfl <;> rfl
  split at declared
  · cases declared; rcases hf with rfl | rfl <;> rfl
  cases declared

theorem check_declaresCall : DeclaresCall (checkStage lv f fType) (stageRules lv) f where
  headTyping := id
  isUniverse := id
  join := id
  cumulative := id
  headEq := id
  computation := id
  constantType := by
    intro c type hc declared
    simpa [checkStage, hc] using declared
  typesFree := stage_typesFree lv hf

theorem check_inert : CallsInert (checkStage lv f fType) f := by
  intro n t w step
  obtain ⟨entry, mem, h⟩ := RootComputation.unionAll_step step
  simp only [stageComputations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · obtain ⟨args, rfl⟩ := iotaComputation_spine h
    exact ⟨numRec, args, by rcases hf with rfl | rfl <;> decide, rfl⟩
  · obtain ⟨args, rfl⟩ := iotaComputation_spine h
    exact ⟨listRec, args, by rcases hf with rfl | rfl <;> decide, rfl⟩

theorem check_reflects : RootReflects (checkStage lv f fType) f (0 + 1) := by
  intro n m τ call t w free step
  obtain ⟨entry, mem, h⟩ := RootComputation.unionAll_step step
  simp only [stageComputations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · obtain ⟨w', h', rfl, free'⟩ := iotaComputation_reflects
      (by rcases hf with rfl | rfl <;> decide : numRec ≠ f) (fun {c fields} mem => by
        simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
        rcases mem with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rcases hf with rfl | rfl <;> decide) call free h
    exact ⟨w', RootComputation.step_unionAll (cs := stageComputations) (List.mem_cons_self ..) h',
      rfl, free'⟩
  · obtain ⟨w', h', rfl, free'⟩ := iotaComputation_reflects
      (by rcases hf with rfl | rfl <;> decide : listRec ≠ f) (fun {c fields} mem => by
        simp only [listCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
        rcases mem with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> rcases hf with rfl | rfl <;> decide) call free h
    exact ⟨w', RootComputation.step_unionAll (cs := stageComputations)
      (List.mem_cons_of_mem _ (List.mem_cons_self ..)) h', rfl, free'⟩

/-- The kernel relates the lists' type to itself. -/
theorem listBelowCheck {n : Nat} {Γ : Ctx Tower.Head n} :
    BelowAlgorithm (checkStage lv f fType) Γ (.const list) (.const list) :=
  .conv (.neutralTypes .refl .refl (.const (checkStage_declared lv fType hf (.inl rfl) rfl)))

/-- The kernel relates the numbers' type to itself. -/
theorem numBelowCheckS {n : Nat} {Γ : Ctx Tower.Head n} :
    BelowAlgorithm (checkStage lv f fType) Γ (.const num) (.const num) :=
  .conv (.neutralTypes .refl .refl
    (.const (checkStage_declared lv fType hf (.inr (.inl rfl)) rfl)))

end CheckStage

theorem entries_free {F : Nat → Tm Tower.Head 0} {f : DeclName} (hF : ∀ j, ConstFree f (F j)) :
    ∀ i, ConstFree f (liftClosed (scrutineeFirst F 1 i) : Tm Tower.Head i) := by
  intro i
  refine ConstFree.liftClosed ?_
  cases i with
  | zero => exact hF 1
  | succ j =>
      show ConstFree f (if j < 1 then F j else F (j + 1))
      split
      · exact hF j
      · exact hF (j + 1)

theorem declaredRevCheck :
    (checkStage lv revOntoFirst revFirstType).constantType revOntoFirst = some revFirstType := by
  simp [checkStage]

theorem declaredRunCheck :
    (checkStage lv runFirst runFirstType).constantType runFirst = some runFirstType := by
  simp [checkStage]

/-- The kernel's check of `rev-onto`'s equation at `nil`: the accumulator. -/
theorem checkRevNil :
    CheckingAlgorithm (checkStage lv revOntoFirst revFirstType) .check (.snoc .nil (.const list))
      (.var 0) (.const list) :=
  .switch (.var 0) (listBelowCheck lv revFirstType (.inl rfl))

/-- The kernel's check of `rev-onto`'s equation at `cons x xs`: the form at `xs`,
applied to `cons x acc`, with the form declared and not computing. -/
theorem checkRevCons :
    CheckingAlgorithm (checkStage lv revOntoFirst revFirstType) .check
      (.snoc (.snoc (.snoc .nil (.const num)) (.const list)) (.const list))
      (.app (.app (.const revOntoFirst) (.var 1)) (.app (.app (.const cons) (.var 2)) (.var 0)))
      (.const list) := by
  have lb := listBelowCheck lv revFirstType (.inl rfl)
    (Γ := .snoc (.snoc (.snoc .nil (.const num)) (.const list)) (.const list))
  have nb := numBelowCheckS lv revFirstType (.inl rfl)
    (Γ := .snoc (.snoc (.snoc .nil (.const num)) (.const list)) (.const list))
  have tForm : CheckingAlgorithm (checkStage lv revOntoFirst revFirstType) .synth
      (.snoc (.snoc (.snoc .nil (.const num)) (.const list)) (.const list)) (.const revOntoFirst)
      (.pi (.const list) (.pi (.const list) (.const list))) :=
    .const (show (checkStage lv revOntoFirst revFirstType).constantType revOntoFirst =
      some revFirstType by simp [checkStage])
  have tCons : CheckingAlgorithm (checkStage lv revOntoFirst revFirstType) .synth
      (.snoc (.snoc (.snoc .nil (.const num)) (.const list)) (.const list)) (.const cons)
      (.pi (.const num) (.pi (.const list) (.const list))) :=
    .const (checkStage_declared lv revFirstType (.inl rfl) (.inr (.inr (.inl rfl))) rfl)
  have tFirst : CheckingAlgorithm (checkStage lv revOntoFirst revFirstType) .synth
      (.snoc (.snoc (.snoc .nil (.const num)) (.const list)) (.const list))
      (.app (.const revOntoFirst) (.var 1)) (.pi (.const list) (.const list)) :=
    .app (A := .const list) (B := .pi (.const list) (.const list)) tForm .refl (.switch (.var 1) lb)
  have tConsX : CheckingAlgorithm (checkStage lv revOntoFirst revFirstType) .synth
      (.snoc (.snoc (.snoc .nil (.const num)) (.const list)) (.const list))
      (.app (.const cons) (.var 2)) (.pi (.const list) (.const list)) :=
    .app (A := .const num) (B := .pi (.const list) (.const list)) tCons .refl (.switch (.var 2) nb)
  have tArg : CheckingAlgorithm (checkStage lv revOntoFirst revFirstType) .check
      (.snoc (.snoc (.snoc .nil (.const num)) (.const list)) (.const list))
      (.app (.app (.const cons) (.var 2)) (.var 0)) (.const list) :=
    .switch (.app (A := .const list) (B := .const list) tConsX .refl (.switch (.var 0) lb)) lb
  exact .switch (.app (A := .const list) (B := .const list) tFirst .refl tArg) lb

/-- The kernel's check of `dfa-run`'s equation at `nil`: the state. -/
theorem checkRunNil :
    CheckingAlgorithm (checkStage lv runFirst runFirstType) .check (.snoc .nil (.const num))
      (.var 0) (.const num) :=
  .switch (.var 0) (numBelowCheckS lv runFirstType (.inr rfl))

/-- The kernel's check of `dfa-run`'s equation at `cons a w`: the form at `w`,
applied to `step q a`, with the form declared and not computing. -/
theorem checkRunCons :
    CheckingAlgorithm (checkStage lv runFirst runFirstType) .check
      (.snoc (.snoc (.snoc .nil (.const num)) (.const list)) (.const num))
      (.app (.app (.const runFirst) (.var 1)) (.app (.app (.const step) (.var 0)) (.var 2)))
      (.const num) := by
  have lb := listBelowCheck lv runFirstType (.inr rfl)
    (Γ := .snoc (.snoc (.snoc .nil (.const num)) (.const list)) (.const num))
  have nb := numBelowCheckS lv runFirstType (.inr rfl)
    (Γ := .snoc (.snoc (.snoc .nil (.const num)) (.const list)) (.const num))
  have tForm : CheckingAlgorithm (checkStage lv runFirst runFirstType) .synth
      (.snoc (.snoc (.snoc .nil (.const num)) (.const list)) (.const num)) (.const runFirst)
      (.pi (.const list) (.pi (.const num) (.const num))) :=
    .const (show (checkStage lv runFirst runFirstType).constantType runFirst =
      some runFirstType by simp [checkStage])
  have tStep : CheckingAlgorithm (checkStage lv runFirst runFirstType) .synth
      (.snoc (.snoc (.snoc .nil (.const num)) (.const list)) (.const num)) (.const step)
      (.pi (.const num) (.pi (.const num) (.const num))) :=
    .const (checkStage_declared lv runFirstType (.inr rfl) (.inr (.inr (.inr rfl))) rfl)
  have tFirst : CheckingAlgorithm (checkStage lv runFirst runFirstType) .synth
      (.snoc (.snoc (.snoc .nil (.const num)) (.const list)) (.const num))
      (.app (.const runFirst) (.var 1)) (.pi (.const num) (.const num)) :=
    .app (A := .const list) (B := .pi (.const num) (.const num)) tForm .refl (.switch (.var 1) lb)
  have tStepQ : CheckingAlgorithm (checkStage lv runFirst runFirstType) .synth
      (.snoc (.snoc (.snoc .nil (.const num)) (.const list)) (.const num))
      (.app (.const step) (.var 0)) (.pi (.const num) (.const num)) :=
    .app (A := .const num) (B := .pi (.const num) (.const num)) tStep .refl (.switch (.var 0) nb)
  have tArg : CheckingAlgorithm (checkStage lv runFirst runFirstType) .check
      (.snoc (.snoc (.snoc .nil (.const num)) (.const list)) (.const num))
      (.app (.app (.const step) (.var 0)) (.var 2)) (.const num) :=
    .switch (.app (A := .const num) (B := .const num) tStepQ .refl (.switch (.var 2) nb)) nb
  exact .switch (.app (A := .const num) (B := .const num) tFirst .refl tArg) nb

/-! ## The hypotheses of the model -/

section Hypotheses

variable (valuation : Nat → Nat)

/-- The package declares the natural numbers. -/
theorem declaresNum :
    DeclaresInductive (setting lv valuation) (constantFreeRules (rules lv))
      TowerNumbersModel.rules₁ TowerNumbersModel.rules₂ num u ctors numRec (.sort lv) where
  role := roles_num
  recRole := roles_numRec
  hu := .sort _
  hv := .sort _
  sub₀ := RulesSub.constantFree _
  sub₁ := sub_rules₁ lv
  sub₂ := sub_numbers lv
  semantic₀ := fun declared => nomatch declared
  stage₁ := (TowerNumbersModel.declares lv valuation).stage₁
  stage₂ := (TowerNumbersModel.declares lv valuation).stage₂
  declared := rfl
  ctorDeclared := by
    intro k fields mem
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · rfl
  recDeclared := rfl
  fieldTyped := (TowerNumbersModel.declares lv valuation).fieldTyped
  ctorTyped := (TowerNumbersModel.declares lv valuation).ctorTyped
  recTyped := (TowerNumbersModel.declares lv valuation).recTyped
  iota := fun hms hi has hm =>
    RootComputation.step_unionAll (cs := computations) (List.mem_cons_self ..)
      ⟨_, _, _, _, _, _, _, hms, hi, has, hm, rfl, rfl⟩

/-- The package declares the lists of numbers. -/
theorem declaresList :
    DeclaresInductive (setting lv valuation) TowerNumbersModel.rules₂ listStage₁ listStage₂ list u
      listCtors listRec (.sort lv) where
  role := roles_list
  recRole := roles_listRec
  hu := .sort _
  hv := .sort _
  sub₀ := sub_numbers lv
  sub₁ := sub_list₁ lv
  sub₂ := sub_list₂ lv
  semantic₀ := (declaresNum lv valuation).semantic₂ (laws lv valuation)
  stage₁ := by
    intro name type declared
    change (if name = list then some (.head u) else TowerNumbersModel.rules₂.constantType name) =
      some type at declared
    split at declared
    · rename_i h
      cases declared
      exact .inr ⟨h, rfl⟩
    · exact .inl declared
  stage₂ := by
    intro name type declared
    change (if name = nil then some (ctorType list [])
      else if name = cons then some (ctorType list consFields)
      else listStage₁.constantType name) = some type at declared
    split at declared
    · rename_i h
      cases declared
      exact .inr ⟨[], by subst h; exact mem_nil, rfl⟩
    · split at declared
      · rename_i _ h
        cases declared
        exact .inr ⟨consFields, by subst h; exact mem_cons, rfl⟩
      · exact .inl declared
  declared := rfl
  ctorDeclared := by
    intro k fields mem
    simp only [listCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · rfl
  recDeclared := rfl
  fieldTyped := by
    intro k fields F mem closed
    simp only [listCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp at closed
    · simp only [consFields, List.mem_cons, Field.closed.injEq, List.not_mem_nil, or_false,
        reduceCtorEq] at closed
      subst closed
      exact const_type_typed LevelTower.HeadTyping.sort LevelTower.IsUniverse.sort rfl
  ctorTyped := by
    intro k fields mem
    simp only [listCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨_, .sort _, const_type_typed LevelTower.HeadTyping.sort LevelTower.IsUniverse.sort rfl⟩
    · have tNum : ∀ {n : Nat} {Γ : Ctx Tower.Head n}, Typed listStage₁ Γ (.const num) (.head u) :=
        fun {_ _} => const_type_typed LevelTower.HeadTyping.sort LevelTower.IsUniverse.sort rfl
      have tList : ∀ {n : Nat} {Γ : Ctx Tower.Head n}, Typed listStage₁ Γ (.const list) (.head u) :=
        fun {_ _} => const_type_typed LevelTower.HeadTyping.sort LevelTower.IsUniverse.sort rfl
      exact ⟨_, .sort _, .piForm tNum (.sort _) (.piForm tList (.sort _) tList (.sort _) (.sorts _ _))
        (.sort _) (.sorts _ _)⟩
  recTyped := listRecType_typed lv
  iota := fun hms hi has hm =>
    RootComputation.step_unionAll (cs := computations) (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      ⟨_, _, _, _, _, _, _, hms, hi, has, hm, rfl, rfl⟩

/-- The constants of the stage of the bodies are semantic. -/
theorem semantic_body : AllSemantic (setting lv valuation) bodyStage := by
  intro name type declared
  change (if name = step then some stepType else listStage₂.constantType name) = some type at declared
  split at declared
  · rename_i h
    subst h
    cases declared
    obtain ⟨w, hw, t⟩ := arrowType_typed (R := bodyStage) num_typedB num_typedB num_typedB
      (.sort _) (fun _ _ => .sorts _ _) (fun _ => .sort _)
    exact SemanticConstant.rigid (S := setting lv valuation) (laws lv valuation) (name := step) rfl
      (Derivable.mono (sub_body lv) t) hw roles_step
  · exact (declaresList lv valuation).semantic₂ (laws lv valuation) declared

/-- The checking package declares the natural numbers. -/
theorem stageDeclaresNum :
    DeclaresInductive (stageSetting lv valuation) (constantFreeRules (stageRules lv))
      TowerNumbersModel.rules₁ TowerNumbersModel.rules₂ num u ctors numRec (.sort lv) where
  role := roles_num
  recRole := roles_numRec
  hu := .sort _
  hv := .sort _
  sub₀ := RulesSub.constantFree _
  sub₁ := stage_sub_rules₁ lv
  sub₂ := stage_sub_numbers lv
  semantic₀ := fun declared => nomatch declared
  stage₁ := (TowerNumbersModel.declares lv valuation).stage₁
  stage₂ := (TowerNumbersModel.declares lv valuation).stage₂
  declared := rfl
  ctorDeclared := by
    intro k fields mem
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · rfl
  recDeclared := rfl
  fieldTyped := (TowerNumbersModel.declares lv valuation).fieldTyped
  ctorTyped := (TowerNumbersModel.declares lv valuation).ctorTyped
  recTyped := (TowerNumbersModel.declares lv valuation).recTyped
  iota := fun hms hi has hm =>
    RootComputation.step_unionAll (cs := stageComputations) (List.mem_cons_self ..)
      ⟨_, _, _, _, _, _, _, hms, hi, has, hm, rfl, rfl⟩

/-- The checking package declares the lists of numbers. -/
theorem stageDeclaresList :
    DeclaresInductive (stageSetting lv valuation) TowerNumbersModel.rules₂ listStage₁ listStage₂ list u
      listCtors listRec (.sort lv) where
  role := roles_list
  recRole := roles_listRec
  hu := .sort _
  hv := .sort _
  sub₀ := stage_sub_numbers lv
  sub₁ := stage_sub_list₁ lv
  sub₂ := stage_sub_list₂ lv
  semantic₀ := (stageDeclaresNum lv valuation).semantic₂ (stageLaws lv valuation)
  stage₁ := (declaresList lv valuation).stage₁
  stage₂ := (declaresList lv valuation).stage₂
  declared := rfl
  ctorDeclared := by
    intro k fields mem
    simp only [listCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · rfl
  recDeclared := rfl
  fieldTyped := (declaresList lv valuation).fieldTyped
  ctorTyped := (declaresList lv valuation).ctorTyped
  recTyped := listRecType_typed lv
  iota := fun hms hi has hm =>
    RootComputation.step_unionAll (cs := stageComputations)
      (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      ⟨_, _, _, _, _, _, _, hms, hi, has, hm, rfl, rfl⟩

/-- Every constant of the checking package is semantic in its model. -/
theorem stageConstants : SemanticConstants (stageSetting lv valuation) := by
  intro name type w declared _ _
  change (if name = listRec then some (recType list (.sort lv) listCtors)
    else if name = numRec then some (recType num (.sort lv) ctors)
    else bodyStage.constantType name) = some type at declared
  split at declared
  · rename_i h
    subst h
    cases declared
    intro m Δ formed P r
    exact (stageDeclaresList lv valuation).rec_semantic (stageLaws lv valuation) formed r
  · split at declared
    · rename_i _ h
      subst h
      cases declared
      intro m Δ formed P r
      exact (stageDeclaresNum lv valuation).rec_semantic (stageLaws lv valuation) formed r
    · change (if name = step then some stepType else listStage₂.constantType name) = some type
        at declared
      split at declared
      · rename_i _ _ h
        subst h
        cases declared
        obtain ⟨w', hw', t⟩ := arrowType_typed (R := bodyStage) num_typedB num_typedB num_typedB
          (.sort _) (fun _ _ => .sorts _ _) (fun _ => .sort _)
        exact SemanticConstant.rigid (S := stageSetting lv valuation) (stageLaws lv valuation)
          (name := step) rfl (Derivable.mono (stage_sub_body lv) t) hw' roles_step
      · exact (stageDeclaresList lv valuation).semantic₂ (stageLaws lv valuation) declared

/-- The facts about the weak-head forms of the checking package's types, from
the normalization model, in which its declared constants are semantic. -/
theorem stageFacts : FormFacts (stageRules lv) roles :=
  .ofSemantic (S := stageSetting lv fun _ => 0) (stageLaws lv _) (stageConstants lv _)

/-- The recursors' computations preserve typing in the checking package. -/
theorem stageRoots : RootPreserving (stageRules lv) := by
  intro n Γ l r A formed step typing
  obtain ⟨entry, mem, step⟩ := RootComputation.unionAll_step step
  simp only [stageComputations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl
  · exact (stageDeclaresNum lv fun _ => 0).step_preserves
      (stageFacts lv) (RulesSub.refl _) formed step typing
  · exact (stageDeclaresList lv fun _ => 0).step_preserves
      (stageFacts lv) (RulesSub.refl _) formed step typing

/-- The constants of the checking package are semantic in the full package's
model. -/
theorem semantic_stage : AllSemantic (setting lv valuation) (stageRules lv) := by
  intro name type declared
  change (if name = listRec then some (recType list (.sort lv) listCtors)
    else if name = numRec then some (recType num (.sort lv) ctors)
    else bodyStage.constantType name) = some type at declared
  split at declared
  · rename_i h
    subst h
    cases declared
    intro m Δ formed P r
    exact (declaresList lv valuation).rec_semantic (laws lv valuation) formed r
  · split at declared
    · rename_i _ h
      subst h
      cases declared
      intro m Δ formed P r
      exact (declaresNum lv valuation).rec_semantic (laws lv valuation) formed r
    · exact semantic_body lv valuation declared

/-- The package declares `rev-onto`'s scrutinee-first form. Each right-hand side
is typed with its recursive hypothesis because the kernel checks it with the
form declared and not computing (`checkRevNil`, `checkRevCons`,
`bodyTyped_of_check`), in the model of the numbers and lists with their
recursors. -/
theorem declaresRevFirst :
    DeclaresRecursion (setting lv valuation) (stageRules lv) revOntoFirst list listCtors
      revFirstEntries 0 (1 + 0) (Presentation.rename (teleMove 1 0) revResult) revBody where
  role := roles_revFirst
  scrutinee := rfl
  declared := rfl
  sub₀ := stage_sub_rules lv
  semantic₀ := semantic_stage lv valuation
  typed := by
    show ∃ w, Tower.IsUniverse w ∧
      Typed (stageRules lv) .nil (.pi (.const list) (.pi (.const list) (.const list))) (.head w)
    exact arrowType_typed (list_typedS lv) (list_typedS lv) (list_typedS lv) (.sort _)
      (fun _ _ => .sorts _ _) (fun _ => .sort _)
  formed := by
    intro k fields mem
    simp only [listCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show CtxFormed (stageRules lv) (.snoc .nil (.const list))
      exact .snoc .nil ⟨_, .sort _, list_typedS lv⟩
    · show CtxFormed (stageRules lv) (.snoc (.snoc (.snoc (.snoc .nil (.const num)) (.const list))
        (.const list)) (.pi (.const list) (.const list)))
      exact .snoc (.snoc (.snoc (.snoc .nil ⟨_, .sort _, num_typedS lv⟩) ⟨_, .sort _, list_typedS lv⟩)
        ⟨_, .sort _, list_typedS lv⟩)
        ⟨_, .sort _, .piForm (list_typedS lv) (.sort _) (list_typedS lv) (.sort _) (.sorts _ _)⟩
  bodyTyped := by
    have freeE : ∀ i, ConstFree revOntoFirst (revFirstEntries i) :=
      entries_free (fun _ => (show list ≠ revOntoFirst by decide))
    have freeC : ConstFree revOntoFirst
        (Presentation.rename (teleMove 1 0) revResult : Tm Tower.Head (0 + 1 + (1 + 0))) :=
      show list ≠ revOntoFirst by decide
    intro k fields mem
    simp only [listCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact bodyTyped_of_check (S₀ := stageSetting lv valuation)
        (f := revOntoFirst) (T := list) (k := nil) (e := revFirstEntries) (s := 0) (d := 1 + 0)
        (fields := []) (C := Presentation.rename (teleMove 1 0) revResult)
        (stageFacts lv) (stageRoots lv) (stageHeads lv) (stageAlgebra lv)
        (stage_typesFormed lv) (check_declaresCall lv revFirstType (.inl rfl))
        (check_inert lv revFirstType (.inl rfl)) (check_reflects lv revFirstType (.inl rfl))
        (declaredRevCheck lv) freeE (fun _ => show list ≠ revOntoFirst by decide)
        (show nil ≠ revOntoFirst by decide) freeC
        (.snoc .nil ⟨_, LevelTower.IsUniverse.sort _, list_typedS lv⟩)
        ⟨_, LevelTower.IsUniverse.sort _, list_typedS lv⟩
        (body := revBody nil []) trivial (checkRevNil lv)
    · exact bodyTyped_of_check (S₀ := stageSetting lv valuation)
        (f := revOntoFirst) (T := list) (k := cons) (e := revFirstEntries) (s := 0) (d := 1 + 0)
        (fields := consFields) (C := Presentation.rename (teleMove 1 0) revResult)
        (stageFacts lv) (stageRoots lv) (stageHeads lv) (stageAlgebra lv)
        (stage_typesFormed lv) (check_declaresCall lv revFirstType (.inl rfl))
        (check_inert lv revFirstType (.inl rfl)) (check_reflects lv revFirstType (.inl rfl))
        (declaredRevCheck lv) freeE
        (fun l => by
          rcases l with _ | _ | l
          · exact show num ≠ revOntoFirst by decide
          · exact show list ≠ revOntoFirst by decide
          · exact show list ≠ revOntoFirst by decide)
        (show cons ≠ revOntoFirst by decide) freeC
        (.snoc (.snoc (.snoc (.snoc .nil ⟨_, LevelTower.IsUniverse.sort _, num_typedS lv⟩)
          ⟨_, LevelTower.IsUniverse.sort _, list_typedS lv⟩) ⟨_, LevelTower.IsUniverse.sort _, list_typedS lv⟩)
          ⟨_, LevelTower.IsUniverse.sort _, .piForm (list_typedS lv) (LevelTower.IsUniverse.sort _)
            (list_typedS lv) (LevelTower.IsUniverse.sort _) (.sorts _ _)⟩)
        ⟨_, LevelTower.IsUniverse.sort _, list_typedS lv⟩
        (body := revBody cons consFields) (ConstFree.of_mentions rfl) (checkRevCons lv)
  rule := by
    intro k fields mem m σ as has
    exact RootComputation.step_unionAll (cs := computations)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))
      ⟨_, _, σ, as, mem, has, rfl, rfl⟩

/-- The package declares `dfa-run`'s scrutinee-first form, each right-hand side
typed from the kernel's check (`checkRunNil`, `checkRunCons`,
`bodyTyped_of_check`). -/
theorem declaresRunFirst :
    DeclaresRecursion (setting lv valuation) (stageRules lv) runFirst list listCtors runFirstEntries
      0 (1 + 0) (Presentation.rename (teleMove 1 0) runResult) runBody where
  role := roles_runFirst
  scrutinee := rfl
  declared := rfl
  sub₀ := stage_sub_rules lv
  semantic₀ := semantic_stage lv valuation
  typed := by
    show ∃ w, Tower.IsUniverse w ∧
      Typed (stageRules lv) .nil (.pi (.const list) (.pi (.const num) (.const num))) (.head w)
    exact arrowType_typed (list_typedS lv) (num_typedS lv) (num_typedS lv) (.sort _)
      (fun _ _ => .sorts _ _) (fun _ => .sort _)
  formed := by
    intro k fields mem
    simp only [listCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show CtxFormed (stageRules lv) (.snoc .nil (.const num))
      exact .snoc .nil ⟨_, .sort _, num_typedS lv⟩
    · show CtxFormed (stageRules lv) (.snoc (.snoc (.snoc (.snoc .nil (.const num)) (.const list))
        (.const num)) (.pi (.const num) (.const num)))
      exact .snoc (.snoc (.snoc (.snoc .nil ⟨_, .sort _, num_typedS lv⟩) ⟨_, .sort _, list_typedS lv⟩)
        ⟨_, .sort _, num_typedS lv⟩)
        ⟨_, .sort _, .piForm (num_typedS lv) (.sort _) (num_typedS lv) (.sort _) (.sorts _ _)⟩
  bodyTyped := by
    have freeE : ∀ i, ConstFree runFirst (runFirstEntries i) :=
      entries_free (fun j => by
        cases j with
        | zero => exact show num ≠ runFirst by decide
        | succ j => exact show list ≠ runFirst by decide)
    have freeC : ConstFree runFirst
        (Presentation.rename (teleMove 1 0) runResult : Tm Tower.Head (0 + 1 + (1 + 0))) :=
      show num ≠ runFirst by decide
    intro k fields mem
    simp only [listCtors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact bodyTyped_of_check (S₀ := stageSetting lv valuation)
        (f := runFirst) (T := list) (k := nil) (e := runFirstEntries) (s := 0) (d := 1 + 0)
        (fields := []) (C := Presentation.rename (teleMove 1 0) runResult)
        (stageFacts lv) (stageRoots lv) (stageHeads lv) (stageAlgebra lv)
        (stage_typesFormed lv) (check_declaresCall lv runFirstType (.inr rfl))
        (check_inert lv runFirstType (.inr rfl)) (check_reflects lv runFirstType (.inr rfl))
        (declaredRunCheck lv) freeE (fun _ => show list ≠ runFirst by decide)
        (show nil ≠ runFirst by decide) freeC
        (.snoc .nil ⟨_, LevelTower.IsUniverse.sort _, num_typedS lv⟩)
        ⟨_, LevelTower.IsUniverse.sort _, num_typedS lv⟩
        (body := runBody nil []) trivial (checkRunNil lv)
    · exact bodyTyped_of_check (S₀ := stageSetting lv valuation)
        (f := runFirst) (T := list) (k := cons) (e := runFirstEntries) (s := 0) (d := 1 + 0)
        (fields := consFields) (C := Presentation.rename (teleMove 1 0) runResult)
        (stageFacts lv) (stageRoots lv) (stageHeads lv) (stageAlgebra lv)
        (stage_typesFormed lv) (check_declaresCall lv runFirstType (.inr rfl))
        (check_inert lv runFirstType (.inr rfl)) (check_reflects lv runFirstType (.inr rfl))
        (declaredRunCheck lv) freeE
        (fun l => by
          rcases l with _ | _ | l
          · exact show num ≠ runFirst by decide
          · exact show list ≠ runFirst by decide
          · exact show list ≠ runFirst by decide)
        (show cons ≠ runFirst by decide) freeC
        (.snoc (.snoc (.snoc (.snoc .nil ⟨_, LevelTower.IsUniverse.sort _, num_typedS lv⟩)
          ⟨_, LevelTower.IsUniverse.sort _, list_typedS lv⟩) ⟨_, LevelTower.IsUniverse.sort _, num_typedS lv⟩)
          ⟨_, LevelTower.IsUniverse.sort _, .piForm (num_typedS lv) (LevelTower.IsUniverse.sort _)
            (num_typedS lv) (LevelTower.IsUniverse.sort _) (.sorts _ _)⟩)
        ⟨_, LevelTower.IsUniverse.sort _, num_typedS lv⟩
        (body := runBody cons consFields) (ConstFree.of_mentions rfl) (checkRunCons lv)
  rule := by
    intro k fields mem m σ as has
    exact RootComputation.step_unionAll (cs := computations)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))
      ⟨_, _, σ, as, mem, has, rfl, rfl⟩

/-- The constants of the stage of the definitions are semantic. -/
theorem semantic_def : AllSemantic (setting lv valuation) defStage := by
  intro name type declared
  change (if name = revOntoFirst then some revFirstType
    else if name = runFirst then some runFirstType
    else bodyStage.constantType name) = some type at declared
  split at declared
  · rename_i h
    subst h
    cases declared
    exact (declaresRevFirst lv valuation).semantic (laws lv valuation) (declaresList lv valuation)
  · split at declared
    · rename_i _ h
      subst h
      cases declared
      exact (declaresRunFirst lv valuation).semantic (laws lv valuation) (declaresList lv valuation)
    · exact semantic_body lv valuation declared

/-- The package declares `rev-onto` by passing its arguments to the
scrutinee-first form. -/
theorem declaresRev :
    DeclaresDefinition (setting lv valuation) defStage revOnto revTele revResult revRhs where
  role := roles_revOnto
  declared := rfl
  sub₀ := sub_def lv
  semantic₀ := semantic_def lv valuation
  typed := by
    show ∃ w, Tower.IsUniverse w ∧
      Typed defStage .nil (.pi (.const list) (.pi (.const list) (.const list))) (.head w)
    exact arrowType_typed list_typedD list_typedD list_typedD (.sort _) (fun _ _ => .sorts _ _)
      (fun _ => .sort _)
  body := by
    rw [revRhs_eq]
    show Typed defStage (.snoc (.snoc .nil (.const list)) (.const list))
      (.app (.app (.const revOntoFirst) (.var 0)) (.var 1)) (.const list)
    exact .appElim (A := .const list) (B := .const list) (.appElim revFirst_typedD (.var 0)) (.var 1)
  rule := by
    intro n σ
    exact RootComputation.step_unionAll (cs := computations)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))) ⟨σ, rfl, rfl⟩

/-- The package declares `dfa-run` by passing its arguments to the
scrutinee-first form. -/
theorem declaresRun :
    DeclaresDefinition (setting lv valuation) defStage run runTele runResult runRhs where
  role := roles_run
  declared := rfl
  sub₀ := sub_def lv
  semantic₀ := semantic_def lv valuation
  typed := by
    show ∃ w, Tower.IsUniverse w ∧
      Typed defStage .nil (.pi (.const num) (.pi (.const list) (.const num))) (.head w)
    exact arrowType_typed num_typedD list_typedD num_typedD (.sort _) (fun _ _ => .sorts _ _)
      (fun _ => .sort _)
  body := by
    rw [runRhs_eq]
    show Typed defStage (.snoc (.snoc .nil (.const num)) (.const list))
      (.app (.app (.const runFirst) (.var 0)) (.var 1)) (.const num)
    exact .appElim (A := .const num) (B := .const num) (.appElim runFirst_typedD (.var 0)) (.var 1)
  rule := by
    intro n σ
    exact RootComputation.step_unionAll (cs := computations)
      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))))) ⟨σ, rfl, rfl⟩

/-- Every declared constant is semantic. -/
theorem constants : SemanticConstants (setting lv valuation) := by
  intro name type w declared _ _
  change (if name = revOnto then some revType
    else if name = run then some runType
    else if name = listRec then some (recType list (.sort lv) listCtors)
    else if name = numRec then some (recType num (.sort lv) ctors)
    else defStage.constantType name) = some type at declared
  split at declared
  · rename_i h
    subst h
    cases declared
    exact (declaresRev lv valuation).semantic (laws lv valuation)
  · split at declared
    · rename_i _ h
      subst h
      cases declared
      exact (declaresRun lv valuation).semantic (laws lv valuation)
    · split at declared
      · rename_i _ _ h
        subst h
        cases declared
        intro m Δ formed P r
        exact (declaresList lv valuation).rec_semantic (laws lv valuation) formed r
      · split at declared
        · rename_i _ _ _ h
          subst h
          cases declared
          intro m Δ formed P r
          exact (declaresNum lv valuation).rec_semantic (laws lv valuation) formed r
        · exact semantic_def lv valuation declared

/-- **The facts about the weak-head forms of the package's types**, from the
normalization model, in which its declared constants are semantic. -/
theorem facts : FormFacts (rules lv) roles :=
  .ofSemantic (S := setting lv fun _ => 0) (laws lv _) (constants lv _)

/-- The computation rules preserve typing. -/
theorem roots : RootPreserving (rules lv) := by
  intro n Γ l r A formed step typing
  obtain ⟨entry, mem, step⟩ := RootComputation.unionAll_step step
  simp only [computations, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (declaresNum lv fun _ => 0).step_preserves (TowerListAccumulatorsModel.facts lv) (RulesSub.refl _)
      formed step typing
  · exact (declaresList lv fun _ => 0).step_preserves (TowerListAccumulatorsModel.facts lv) (RulesSub.refl _) formed
        step typing
  · obtain ⟨k, fields, σ, as, mem, has, rfl, rfl⟩ := step
    exact (declaresRevFirst lv fun _ => 0).rule_preserves (TowerListAccumulatorsModel.facts lv)
        (declaresList lv fun _ => 0) (RulesSub.refl _) formed mem σ as has typing
  · obtain ⟨σ, rfl, rfl⟩ := step
    exact (declaresRev lv fun _ => 0).rule_preserves (TowerListAccumulatorsModel.facts lv) (RulesSub.refl _) formed
        σ typing
  · obtain ⟨k, fields, σ, as, mem, has, rfl, rfl⟩ := step
    exact (declaresRunFirst lv fun _ => 0).rule_preserves (TowerListAccumulatorsModel.facts lv)
        (declaresList lv fun _ => 0) (RulesSub.refl _) formed mem σ as has typing
  · obtain ⟨σ, rfl, rfl⟩ := step
    exact (declaresRun lv fun _ => 0).rule_preserves (TowerListAccumulatorsModel.facts lv) (RulesSub.refl _) formed
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

end TowerListAccumulatorsModel

/-! ## The authored equations -/

section Equations

open TowerListAccumulatorsModel

variable {lv : LevelExpr Nat} {n : Nat} {Γ : Ctx Tower.Head n}

theorem TowerListAccumulators.list_typed : Typed (rules lv) Γ (.const list) (.head u) :=
  Derivable.mono (sub_body lv) list_typedB

theorem TowerListAccumulators.nil_typed : Typed (rules lv) Γ (.const nil) (.const list) :=
  .const (type := ctorType list []) rfl
    (const_type_typed LevelTower.HeadTyping.sort LevelTower.IsUniverse.sort rfl) (.sort _)

theorem TowerListAccumulators.cons_typed {x xs : Tm Tower.Head n}
    (tx : Typed (rules lv) Γ x (.const num)) (txs : Typed (rules lv) Γ xs (.const list)) :
    Typed (rules lv) Γ (.app (.app (.const cons) x) xs) (.const list) :=
  .appElim (A := .const list) (B := .const list)
    (.appElim (Derivable.mono (sub_body lv) cons_typedB) tx) txs

theorem TowerListAccumulators.step_typed {q a : Tm Tower.Head n}
    (tq : Typed (rules lv) Γ q (.const num)) (ta : Typed (rules lv) Γ a (.const num)) :
    Typed (rules lv) Γ (.app (.app (.const step) q) a) (.const num) :=
  .appElim (A := .const num) (B := .const num)
    (.appElim (Derivable.mono (sub_body lv) step_typedB) tq) ta

theorem TowerListAccumulators.revOnto_typed {acc xs : Tm Tower.Head n}
    (tacc : Typed (rules lv) Γ acc (.const list)) (txs : Typed (rules lv) Γ xs (.const list)) :
    Typed (rules lv) Γ (.app (.app (.const revOnto) acc) xs) (.const list) := by
  have tf : Typed (rules lv) Γ (.const revOnto) (.pi (.const list) (.pi (.const list) (.const list))) :=
    .const (type := revType) rfl (Derivable.mono (sub_def lv) (.piForm list_typedD (.sort _)
      (.piForm list_typedD (.sort _) list_typedD (.sort _) (.sorts _ _)) (.sort _) (.sorts _ _)))
      (.sort _)
  exact .appElim (A := .const list) (B := .const list) (.appElim tf tacc) txs

theorem TowerListAccumulators.run_typed {q w : Tm Tower.Head n}
    (tq : Typed (rules lv) Γ q (.const num)) (tw : Typed (rules lv) Γ w (.const list)) :
    Typed (rules lv) Γ (.app (.app (.const run) q) w) (.const num) := by
  have tf : Typed (rules lv) Γ (.const run) (.pi (.const num) (.pi (.const list) (.const num))) :=
    .const (type := runType) rfl (Derivable.mono (sub_def lv) (.piForm num_typedD (.sort _)
      (.piForm list_typedD (.sort _) num_typedD (.sort _) (.sorts _ _)) (.sort _) (.sorts _ _)))
      (.sort _)
  exact .appElim (A := .const list) (B := .const num) (.appElim tf tq) tw

/-- The authored substitution of the accumulator and the list. -/
def TowerListAccumulators.args (a b : Tm Tower.Head n) : Sub Tower.Head (1 + 1 + 0) n :=
  consSub b (consSub a fun i => Fin.elim0 i)

theorem TowerListAccumulators.args_typed_rev {acc xs : Tm Tower.Head n}
    (tacc : Typed (rules lv) Γ acc (.const list)) (txs : Typed (rules lv) Γ xs (.const list)) :
    SubstMor (rules lv) revTele Γ (TowerListAccumulators.args acc xs) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact txs
  · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    exact tacc

theorem TowerListAccumulators.args_typed_run {q w : Tm Tower.Head n}
    (tq : Typed (rules lv) Γ q (.const num)) (tw : Typed (rules lv) Γ w (.const list)) :
    SubstMor (rules lv) runTele Γ (TowerListAccumulators.args q w) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact tw
  · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    exact tq

/-- `rev-onto acc nil = acc`. -/
theorem TowerListAccumulators.revOnto_nil (formed : CtxFormed (rules lv) Γ) {acc : Tm Tower.Head n}
    (tacc : Typed (rules lv) Γ acc (.const list)) :
    Equal (rules lv) Γ (.app (.app (.const revOnto) acc) (.const nil)) acc (.const list) :=
  ScrutineeFirst.equation (S := setting lv fun _ => 0) (TowerListAccumulatorsModel.facts lv)
    (declaresRev lv _) (declaresRevFirst lv _) (declaresList lv _) formed mem_nil
    (TowerListAccumulators.args acc (.const nil)) [] rfl
    (TowerListAccumulators.revOnto_typed tacc TowerListAccumulators.nil_typed)

theorem TowerListAccumulators.num_typed : Typed (rules lv) Γ (.const num) (.head u) :=
  Derivable.mono (sub_def lv) num_typedD

/-- `rev-onto acc (cons x xs) = rev-onto (cons x acc) xs`, with the authored
right-hand side: the instance of `ScrutineeFirst.authored_equation`, the authored
right-hand side a term of its own, the scrutinee-first form's right-hand side
the kernel's rewriting of it. -/
theorem TowerListAccumulators.revOnto_cons (formed : CtxFormed (rules lv) Γ)
    {acc x xs : Tm Tower.Head n} (tacc : Typed (rules lv) Γ acc (.const list))
    (tx : Typed (rules lv) Γ x (.const num)) (txs : Typed (rules lv) Γ xs (.const list)) :
    Equal (rules lv) Γ (.app (.app (.const revOnto) acc) (.app (.app (.const cons) x) xs))
      (.app (.app (.const revOnto) (.app (.app (.const cons) x) acc)) xs) (.const list) := by
  have patFormed : CtxFormed (rules lv)
      (.snoc (.snoc (.snoc .nil (.const list)) (.const num)) (.const list)) :=
    .snoc (.snoc (.snoc .nil ⟨_, .sort _, TowerListAccumulators.list_typed⟩)
      ⟨_, .sort _, TowerListAccumulators.num_typed⟩) ⟨_, .sort _, TowerListAccumulators.list_typed⟩
  have rhsTyped : Typed (rules lv) (.snoc (.snoc (.snoc .nil (.const list)) (.const num)) (.const list))
      (.app (.app (.const revOnto) (.app (.app (.const cons) (.var 1)) (.var 2))) (.var 0))
      (.const list) :=
    TowerListAccumulators.revOnto_typed (TowerListAccumulators.cons_typed (.var 1) (.var 2)) (.var 0)
  exact ScrutineeFirst.authored_equation (S := setting lv fun _ => 0)
      (TowerListAccumulatorsModel.facts lv)
    (roots lv) (heads lv) (declaresRev lv _) (declaresRevFirst lv _) (declaresList lv _) formed
    mem_cons (rhs := .app (.app (.const revOnto) (.app (.app (.const cons) (.var 1)) (.var 2)))
      (.var 0))
    patFormed rhsTyped rfl
    (TowerListAccumulators.args_typed_rev tacc (TowerListAccumulators.cons_typed tx txs))
    (as := [x, xs]) rfl (fun l hl => by
      rw [show consFields.length = 2 from rfl] at hl
      rcases l with _ | _ | l
      · exact tx
      · exact txs
      · exfalso; omega) rfl

/-- `dfa-run q nil = q`. -/
theorem TowerListAccumulators.run_nil (formed : CtxFormed (rules lv) Γ) {q : Tm Tower.Head n}
    (tq : Typed (rules lv) Γ q (.const num)) :
    Equal (rules lv) Γ (.app (.app (.const run) q) (.const nil)) q (.const num) :=
  ScrutineeFirst.equation (S := setting lv fun _ => 0) (TowerListAccumulatorsModel.facts lv)
    (declaresRun lv _) (declaresRunFirst lv _) (declaresList lv _) formed mem_nil
    (TowerListAccumulators.args q (.const nil)) [] rfl
    (TowerListAccumulators.run_typed tq TowerListAccumulators.nil_typed)

/-- `dfa-run q (cons a w) = dfa-run (step q a) w`, with the authored right-hand
side: the instance of `ScrutineeFirst.authored_equation`. -/
theorem TowerListAccumulators.run_cons (formed : CtxFormed (rules lv) Γ)
    {q a w : Tm Tower.Head n} (tq : Typed (rules lv) Γ q (.const num))
    (ta : Typed (rules lv) Γ a (.const num)) (tw : Typed (rules lv) Γ w (.const list)) :
    Equal (rules lv) Γ (.app (.app (.const run) q) (.app (.app (.const cons) a) w))
      (.app (.app (.const run) (.app (.app (.const step) q) a)) w) (.const num) := by
  have patFormed : CtxFormed (rules lv)
      (.snoc (.snoc (.snoc .nil (.const num)) (.const num)) (.const list)) :=
    .snoc (.snoc (.snoc .nil ⟨_, .sort _, TowerListAccumulators.num_typed⟩)
      ⟨_, .sort _, TowerListAccumulators.num_typed⟩) ⟨_, .sort _, TowerListAccumulators.list_typed⟩
  have rhsTyped : Typed (rules lv) (.snoc (.snoc (.snoc .nil (.const num)) (.const num)) (.const list))
      (.app (.app (.const run) (.app (.app (.const step) (.var 2)) (.var 1))) (.var 0))
      (.const num) :=
    TowerListAccumulators.run_typed (TowerListAccumulators.step_typed (.var 2) (.var 1)) (.var 0)
  exact ScrutineeFirst.authored_equation (S := setting lv fun _ => 0)
      (TowerListAccumulatorsModel.facts lv)
    (roots lv) (heads lv) (declaresRun lv _) (declaresRunFirst lv _) (declaresList lv _) formed
    mem_cons (rhs := .app (.app (.const run) (.app (.app (.const step) (.var 2)) (.var 1)))
      (.var 0))
    patFormed rhsTyped rfl
    (TowerListAccumulators.args_typed_run tq (TowerListAccumulators.cons_typed ta tw))
    (as := [a, w]) rfl (fun l hl => by
      rw [show consFields.length = 2 from rfl] at hl
      rcases l with _ | _ | l
      · exact ta
      · exact tw
      · exfalso; omega) rfl

end Equations

/-! ## The scrutinee-first forms derived from the recursor -/

section Recursor

open TowerListAccumulatorsModel

variable {lv : LevelExpr Nat} {n : Nat} {Γ : Ctx Tower.Head n}

/-- `rev-onto`'s result family `λ xs. Π acc. list` is a family of types of the
list recursor's universe. -/
theorem TowerListAccumulators.rev_motive_typed :
    Typed (rules lv) (ofEntries revFirstEntries (0 + 1))
      (piRange revFirstEntries (0 + 1) (1 + 0) (Presentation.rename (teleMove 1 0) revResult))
      (.head (.sort lv)) := by
  show Typed (rules lv) (.snoc .nil (.const list)) (.pi (.const list) (.const list)) (.head (.sort lv))
  exact Derivable.cumul (.piForm TowerListAccumulators.list_typed (.sort _)
    TowerListAccumulators.list_typed (.sort _) (.sorts _ _)) (fun _ => Nat.zero_le _)

/-- `dfa-run`'s result family `λ w. Π q. num` is a family of types of the list
recursor's universe. -/
theorem TowerListAccumulators.run_motive_typed :
    Typed (rules lv) (ofEntries runFirstEntries (0 + 1))
      (piRange runFirstEntries (0 + 1) (1 + 0) (Presentation.rename (teleMove 1 0) runResult))
      (.head (.sort lv)) := by
  show Typed (rules lv) (.snoc .nil (.const list)) (.pi (.const num) (.const num)) (.head (.sort lv))
  exact Derivable.cumul (.piForm TowerListAccumulators.num_typed (.sort _)
    TowerListAccumulators.num_typed (.sort _) (.sorts _ _)) (fun _ => Nat.zero_le _)

/-- `rev-onto`'s scrutinee-first form written with the list recursor. -/
def TowerListAccumulators.revRecursor (t : Tm Tower.Head n) : Tm Tower.Head n :=
  recApp listRec (recPre revFirstEntries 0 (1 + 0) (Presentation.rename (teleMove 1 0) revResult)
    listCtors revBody (fun i => Fin.elim0 i)) t

/-- `dfa-run`'s scrutinee-first form written with the list recursor. -/
def TowerListAccumulators.runRecursor (t : Tm Tower.Head n) : Tm Tower.Head n :=
  recApp listRec (recPre runFirstEntries 0 (1 + 0) (Presentation.rename (teleMove 1 0) runResult)
    listCtors runBody (fun i => Fin.elim0 i)) t

/-- The scrutinee-first arguments: the list, then the other argument. -/
def TowerListAccumulators.firstArgs (t a : Tm Tower.Head n) : Sub Tower.Head (0 + 1 + (1 + 0)) n :=
  consSub a (consSub t fun i => Fin.elim0 i)

theorem TowerListAccumulators.firstArgs_prefix (t a : Tm Tower.Head n) :
    prefixSub 0 (1 + 0) (TowerListAccumulators.firstArgs t a) = fun i => Fin.elim0 i :=
  funext fun i => Fin.elim0 i

theorem TowerListAccumulators.firstArgs_typed_rev {t acc : Tm Tower.Head n}
    (tt : Typed (rules lv) Γ t (.const list)) (tacc : Typed (rules lv) Γ acc (.const list)) :
    SubstMor (rules lv) (ofEntries revFirstEntries (0 + 1 + (1 + 0))) Γ
      (TowerListAccumulators.firstArgs t acc) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact tacc
  · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    exact tt

theorem TowerListAccumulators.firstArgs_typed_run {t q : Tm Tower.Head n}
    (tt : Typed (rules lv) Γ t (.const list)) (tq : Typed (rules lv) Γ q (.const num)) :
    SubstMor (rules lv) (ofEntries runFirstEntries (0 + 1 + (1 + 0))) Γ
      (TowerListAccumulators.firstArgs t q) := by
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact tq
  · refine Fin.cases ?_ (fun k => Fin.elim0 k) j
    exact tt

/-- The recursor-built `rev-onto` at `nil` returns the accumulator. -/
theorem TowerListAccumulators.revRecursor_nil (formed : CtxFormed (rules lv) Γ)
    {acc : Tm Tower.Head n} (tacc : Typed (rules lv) Γ acc (.const list)) :
    Equal (rules lv) Γ (.app (TowerListAccumulators.revRecursor (.const nil)) acc) acc
      (.const list) := by
  have h := (declaresList lv fun _ => 0).recursor_equation_matched
    (declaresRevFirst lv fun _ => 0).scrutinee TowerListAccumulators.rev_motive_typed
    (fun mem => Derivable.mono (declaresRevFirst lv fun _ => 0).sub₀
      ((declaresRevFirst lv fun _ => 0).bodyTyped mem))
    (TowerListAccumulatorsModel.facts lv) (roots lv) (heads lv) formed
    (TowerListAccumulators.firstArgs_typed_rev TowerListAccumulators.nil_typed tacc) (i := 0) rfl
    (as := []) rfl rfl
  rw [TowerListAccumulators.firstArgs_prefix] at h
  exact h

/-- The recursor-built `rev-onto` satisfies the equation with the changing
accumulator: `R (cons x xs) acc = R xs (cons x acc)`. -/
theorem TowerListAccumulators.revRecursor_cons (formed : CtxFormed (rules lv) Γ)
    {acc x xs : Tm Tower.Head n} (tacc : Typed (rules lv) Γ acc (.const list))
    (tx : Typed (rules lv) Γ x (.const num)) (txs : Typed (rules lv) Γ xs (.const list)) :
    Equal (rules lv) Γ
      (.app (TowerListAccumulators.revRecursor (.app (.app (.const cons) x) xs)) acc)
      (.app (TowerListAccumulators.revRecursor xs) (.app (.app (.const cons) x) acc))
      (.const list) := by
  have h := (declaresList lv fun _ => 0).recursor_equation_matched
    (declaresRevFirst lv fun _ => 0).scrutinee TowerListAccumulators.rev_motive_typed
    (fun mem => Derivable.mono (declaresRevFirst lv fun _ => 0).sub₀
      ((declaresRevFirst lv fun _ => 0).bodyTyped mem))
    (TowerListAccumulatorsModel.facts lv) (roots lv) (heads lv) formed
    (TowerListAccumulators.firstArgs_typed_rev (TowerListAccumulators.cons_typed tx txs) tacc)
    (i := 1) rfl (as := [x, xs]) rfl rfl
  rw [TowerListAccumulators.firstArgs_prefix] at h
  exact h

/-- The recursor-built `dfa-run` at `nil` returns the state. -/
theorem TowerListAccumulators.runRecursor_nil (formed : CtxFormed (rules lv) Γ)
    {q : Tm Tower.Head n} (tq : Typed (rules lv) Γ q (.const num)) :
    Equal (rules lv) Γ (.app (TowerListAccumulators.runRecursor (.const nil)) q) q
      (.const num) := by
  have h := (declaresList lv fun _ => 0).recursor_equation_matched
    (declaresRunFirst lv fun _ => 0).scrutinee TowerListAccumulators.run_motive_typed
    (fun mem => Derivable.mono (declaresRunFirst lv fun _ => 0).sub₀
      ((declaresRunFirst lv fun _ => 0).bodyTyped mem))
    (TowerListAccumulatorsModel.facts lv) (roots lv) (heads lv) formed
    (TowerListAccumulators.firstArgs_typed_run TowerListAccumulators.nil_typed tq) (i := 0) rfl
    (as := []) rfl rfl
  rw [TowerListAccumulators.firstArgs_prefix] at h
  exact h

/-- The recursor-built `dfa-run` satisfies the equation with the changing
state: `R (cons a w) q = R w (step q a)`. -/
theorem TowerListAccumulators.runRecursor_cons (formed : CtxFormed (rules lv) Γ)
    {q a w : Tm Tower.Head n} (tq : Typed (rules lv) Γ q (.const num))
    (ta : Typed (rules lv) Γ a (.const num)) (tw : Typed (rules lv) Γ w (.const list)) :
    Equal (rules lv) Γ
      (.app (TowerListAccumulators.runRecursor (.app (.app (.const cons) a) w)) q)
      (.app (TowerListAccumulators.runRecursor w) (.app (.app (.const step) q) a))
      (.const num) := by
  have h := (declaresList lv fun _ => 0).recursor_equation_matched
    (declaresRunFirst lv fun _ => 0).scrutinee TowerListAccumulators.run_motive_typed
    (fun mem => Derivable.mono (declaresRunFirst lv fun _ => 0).sub₀
      ((declaresRunFirst lv fun _ => 0).bodyTyped mem))
    (TowerListAccumulatorsModel.facts lv) (roots lv) (heads lv) formed
    (TowerListAccumulators.firstArgs_typed_run (TowerListAccumulators.cons_typed ta tw) tq)
    (i := 1) rfl (as := [a, w]) rfl rfl
  rw [TowerListAccumulators.firstArgs_prefix] at h
  exact h

end Recursor

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
