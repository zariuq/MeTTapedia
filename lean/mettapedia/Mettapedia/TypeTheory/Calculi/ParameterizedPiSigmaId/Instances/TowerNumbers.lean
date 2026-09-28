import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.IotaComputation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.Tower
/-!
# The cumulative tower with natural numbers

The tower extended by the natural numbers as a simple inductive type in the
lowest universe: the type `num`, its constructors `zero : num` and
`succ : num → num`, and its recursor into a universe of level `lv`,

`num-rec : Π (P : num → U_lv). P zero → (Π (x : num). P x → P (succ x)) →
  Π (t : num). P t`,

with its two computation rules. Every hypothesis of the normalization model
holds, so the consequences hold without hypotheses: constructors are injective
and distinct, type formers are injective and distinguished, reduction,
including the recursor's computation, preserves typing, and the conversion
algorithm is sound.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open Mettapedia.TypeTheory.UniverseLevel
open TelescopeAbstraction (closeType applyClosed)

namespace TowerNumbersModel

/-- The type of natural numbers. -/
def num : DeclName := .mkSimple "num"
/-- The constructor for zero. -/
def zero : DeclName := .mkSimple "zero"
/-- The successor constructor. -/
def succ : DeclName := .mkSimple "succ"
/-- The recursor. -/
def numRec : DeclName := .mkSimple "num-rec"

/-- The constructors of the natural numbers. -/
def ctors : List (DeclName × List (Field Tower.Head)) := [(zero, []), (succ, [.recursive])]

/-- The universe of the natural numbers: level zero. -/
def u : Tower.Head := .sort (.const 0)

theorem mem_zero : ((zero, []) : DeclName × List (Field Tower.Head)) ∈ ctors :=
  List.mem_cons_self ..

theorem mem_succ : ((succ, [.recursive]) : DeclName × List (Field Tower.Head)) ∈ ctors :=
  List.mem_cons_of_mem _ (List.mem_cons_self ..)

theorem num_ne_zero : num ≠ zero := by decide
theorem num_ne_succ : num ≠ succ := by decide
theorem num_ne_numRec : num ≠ numRec := by decide
theorem zero_ne_succ : zero ≠ succ := by decide
theorem zero_ne_numRec : zero ≠ numRec := by decide
theorem succ_ne_numRec : succ ≠ numRec := by decide

variable (lv : LevelExpr)

/-- The declared types. -/
def constantType : DeclName → Option (Tm Tower.Head 0) := fun name =>
  if name = num then some (.head u)
  else if name = zero then some (ctorType num [])
  else if name = succ then some (ctorType num [.recursive])
  else if name = numRec then some (recType num (.sort lv) ctors)
  else none

/-- The tower with the natural numbers and their recursor into level `lv`. -/
def rules : Rules Tower.Head :=
  { Tower.rules with
    constantType := constantType lv
    computation := iotaComputation numRec ctors }

/-- The first stage: the type alone. -/
def rules₁ : Rules Tower.Head :=
  { Tower.rules with constantType := fun name => if name = num then some (.head u) else none }

/-- The second stage: the type and its constructors. -/
def rules₂ : Rules Tower.Head :=
  { Tower.rules with
    constantType := fun name =>
      if name = num then some (.head u)
      else if name = zero then some (ctorType num [])
      else if name = succ then some (ctorType num [.recursive])
      else none }

/-- The roles of the declared constants. -/
def roles : Roles Tower.Head := fun name =>
  if name = num then .inductive ctors
  else if name = zero then .constructor 0
  else if name = succ then .constructor 1
  else if name = numRec then .computes 4 (.split 3 .constructor fun _ => .leaf)
  else .rigid

theorem roles_num : roles num = .inductive ctors := by simp [roles]
theorem roles_zero : roles zero = .constructor 0 := by simp [roles, num_ne_zero.symm]
theorem roles_succ : roles succ = .constructor 1 := by
  simp [roles, num_ne_succ.symm, zero_ne_succ.symm]
theorem roles_numRec : roles numRec = .computes 4 (.split 3 .constructor fun _ => .leaf) := by
  simp [roles, num_ne_numRec.symm, zero_ne_numRec.symm, succ_ne_numRec.symm]

/-- The only inductive type is `num`. -/
theorem roles_inductive {T : DeclName} {cs : List (DeclName × List (Field Tower.Head))}
    (role : roles T = .inductive cs) : T = num ∧ cs = ctors := by
  unfold roles at role
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
    exact List.nodup_cons.mpr ⟨by simp [zero_ne_succ], List.nodup_singleton _⟩

theorem shape : RootShape (rules lv) roles where
  spine := fun step => IotaStep.spine (T := num) roles_num roles_numRec constructorsDeclared step
  deterministic := fun step step' =>
    IotaStep.deterministic (T := num) roles_num constructorsDeclared step' step

/-- The tower's level model, for the rule package with the numbers. -/
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

section Typing

variable {R : Rules Tower.Head}
  (headTyping : ∀ l, R.headTyping (.sort l) (.sort (.succ l)))
  (isUniverse : ∀ l, R.isUniverse (.sort l))
include headTyping isUniverse

theorem num_typed (declaredNum : R.constantType num = some (.head u)) {n : Nat}
    {Γ : Ctx Tower.Head n} : Typed R Γ (.const num) (.head u) :=
  .const declaredNum (.headType (headTyping _)) (isUniverse _)

omit isUniverse in
theorem head_typed {n : Nat} {Γ : Ctx Tower.Head n} (l : LevelExpr) :
    Typed R Γ (.head (.sort l)) (.head (.sort (.succ l))) :=
  .headType (headTyping l)

end Typing

/-- The constructor types are typed at the first stage. -/
theorem ctorType_zero_typed : Typed (rules₁) .nil (ctorType num []) (.head u) :=
  num_typed Tower.HeadTyping.sort Tower.IsUniverse.sort (by simp [rules₁])

theorem ctorType_succ_typed :
    Typed (rules₁) .nil (ctorType num [.recursive]) (.head (.sort (.max (.const 0) (.const 0)))) :=
  .piForm (num_typed Tower.HeadTyping.sort Tower.IsUniverse.sort (by simp [rules₁])) (.sort _)
    (num_typed Tower.HeadTyping.sort Tower.IsUniverse.sort (by simp [rules₁])) (.sort _)
    (.sorts _ _)

/-- The recursor's type is typed at the second stage. -/
theorem recType_typed : ∃ w, Tower.IsUniverse w ∧
    Typed rules₂ .nil (recType num (.sort lv) ctors) (.head w) := by
  have declaredNum : rules₂.constantType num = some (.head u) := by simp [rules₂]
  have declaredZero : rules₂.constantType zero = some (ctorType num []) := by
    simp [rules₂, num_ne_zero.symm]
  have declaredSucc : rules₂.constantType succ = some (ctorType num [.recursive]) := by
    simp [rules₂, num_ne_succ.symm, zero_ne_succ.symm]
  have hu : rules₂.isUniverse u := .sort _
  have hv : rules₂.isUniverse (.sort lv) := .sort _
  have tNum : ∀ {n : Nat} {Γ : Ctx Tower.Head n}, Typed rules₂ Γ (.const num) (.head u) :=
    fun {_ _} => num_typed Tower.HeadTyping.sort Tower.IsUniverse.sort declaredNum
  have tZero : ∀ {n : Nat} {Γ : Ctx Tower.Head n}, Typed rules₂ Γ (.const zero) (.const num) :=
    fun {_ _} => .const declaredZero tNum hu
  have tSucc : ∀ {n : Nat} {Γ : Ctx Tower.Head n},
      Typed rules₂ Γ (.const succ) (.pi (.const num) (.const num)) :=
    fun {_ _} => .const declaredSucc (.piForm tNum hu tNum hu (.sorts _ _)) (.sort _)
  -- the motive's type
  have tE0 : Typed rules₂ .nil (.pi (.const num) (.head (.sort lv)))
      (.head (.sort (.max (.const 0) (.succ lv)))) :=
    .piForm tNum hu (head_typed Tower.HeadTyping.sort lv) (.sort _) (.sorts _ _)
  -- the case of zero
  let Γ₁ : Ctx Tower.Head 1 := .snoc .nil (.pi (.const num) (.head (.sort lv)))
  have tP₁ : Typed rules₂ Γ₁ (.var 0) (.pi (.const num) (.head (.sort lv))) := .var 0
  have tE1 : Typed rules₂ Γ₁ (.app (.var 0) (.const zero)) (.head (.sort lv)) :=
    .appElim tP₁ tZero
  -- the case of the successor
  let Γ₂ : Ctx Tower.Head 2 := .snoc Γ₁ (.app (.var 0) (.const zero))
  let Γ₂x : Ctx Tower.Head 3 := .snoc Γ₂ (.const num)
  have tP₂ : Typed rules₂ Γ₂x (.var 2) (.pi (.const num) (.head (.sort lv))) := .var 2
  have tX : Typed rules₂ Γ₂x (.var 0) (.const num) := .var 0
  have tIH : Typed rules₂ Γ₂x (.app (.var 2) (.var 0)) (.head (.sort lv)) := .appElim tP₂ tX
  let Γ₂h : Ctx Tower.Head 4 := .snoc Γ₂x (.app (.var 2) (.var 0))
  have tX' : Typed rules₂ Γ₂h (.var 1) (.const num) := .var 1
  have tSuccX : Typed rules₂ Γ₂h (.app (.const succ) (.var 1)) (.const num) :=
    .appElim tSucc tX'
  have tP₂' : Typed rules₂ Γ₂h (.var 3) (.pi (.const num) (.head (.sort lv))) := .var 3
  have tGoal : Typed rules₂ Γ₂h (.app (.var 3) (.app (.const succ) (.var 1))) (.head (.sort lv)) :=
    .appElim tP₂' tSuccX
  have tHyp := Derivable.piForm tIH hv tGoal hv (.sorts lv lv)
  have tE2 := Derivable.piForm (tNum (Γ := Γ₂)) hu tHyp (.sort _) (.sorts _ _)
  -- the scrutinee and the result
  let Γ₃ : Ctx Tower.Head 3 :=
    .snoc Γ₂ (.pi (.const num) (.pi (.app (.var 2) (.var 0))
      (.app (.var 3) (.app (.const succ) (.var 1)))))
  let Γ₄ : Ctx Tower.Head 4 := .snoc Γ₃ (.const num)
  have tP₄ : Typed rules₂ Γ₄ (.var 3) (.pi (.const num) (.head (.sort lv))) := .var 3
  have tT : Typed rules₂ Γ₄ (.var 0) (.const num) := .var 0
  have tBody : Typed rules₂ Γ₄ (.app (.var 3) (.var 0)) (.head (.sort lv)) := .appElim tP₄ tT
  -- closing the telescope
  have t4 := Derivable.piForm (tNum (Γ := Γ₃)) hu tBody hv (.sorts _ _)
  have t3 := Derivable.piForm tE2 (.sort _) t4 (.sort _) (.sorts _ _)
  have t2 := Derivable.piForm tE1 hv t3 (.sort _) (.sorts _ _)
  have t1 := Derivable.piForm tE0 (.sort _) t2 (.sort _) (.sorts _ _)
  exact ⟨_, .sort _, t1⟩

/-! ## The hypotheses of the model -/

section Hypotheses

variable (valuation : Nat → Nat)

theorem declaredNum : (rules lv).constantType num = some (.head u) := by
  simp [rules, constantType]

theorem declaredZero : (rules lv).constantType zero = some (ctorType num []) := by
  simp [rules, constantType, num_ne_zero.symm]

theorem declaredSucc : (rules lv).constantType succ = some (ctorType num [.recursive]) := by
  simp [rules, constantType, num_ne_succ.symm, zero_ne_succ.symm]

theorem declaredRec : (rules lv).constantType numRec = some (recType num (.sort lv) ctors) := by
  simp [rules, constantType, num_ne_numRec.symm, zero_ne_numRec.symm, succ_ne_numRec.symm]

/-- The package declares the natural numbers. -/
theorem declares :
    DeclaresInductive (setting lv valuation) (constantFreeRules (rules lv)) rules₁ rules₂ num u
      ctors numRec (.sort lv) where
  role := roles_num
  recRole := roles_numRec
  hu := .sort _
  hv := .sort _
  sub₀ := RulesSub.constantFree _
  sub₁ := ⟨id, id, id, id, id, fun {name type} declared => (by
      simp only [rules₁] at declared
      split at declared
      · rename_i h
        subst h
        cases declared
        exact declaredNum lv
      · cases declared), fun step => nomatch step⟩
  sub₂ := ⟨id, id, id, id, id, fun {name type} declared => (by
      simp only [rules₂] at declared
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
  semantic₀ := fun declared => nomatch declared
  stage₁ := by
    intro name type declared
    simp only [rules₁] at declared
    split at declared
    · rename_i h
      cases declared
      exact .inr ⟨h, rfl⟩
    · cases declared
  stage₂ := by
    intro name type declared
    simp only [rules₂] at declared
    split at declared
    · rename_i h
      cases declared
      exact .inl (by simp [rules₁, h])
    · split at declared
      · rename_i _ h
        cases declared
        exact .inr ⟨[], by simp [ctors, h], rfl⟩
      · split at declared
        · rename_i _ _ h
          cases declared
          exact .inr ⟨[.recursive], by simp [ctors, h], rfl⟩
        · cases declared
  declared := declaredNum lv
  ctorDeclared := by
    intro k fields mem
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact declaredZero lv
    · exact declaredSucc lv
  recDeclared := declaredRec lv
  fieldTyped := by
    intro k fields F mem closed
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp at closed
    · simp at closed
  ctorTyped := by
    intro k fields mem
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨_, .sort _, ctorType_zero_typed⟩
    · exact ⟨_, .sort _, ctorType_succ_typed⟩
  recTyped := by
    obtain ⟨w, hw, typed⟩ := recType_typed lv
    exact ⟨w, hw, typed⟩
  iota := fun hms hi has hm => ⟨_, _, _, _, _, _, _, hms, hi, has, hm, rfl, rfl⟩

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

/-- **The facts about the weak-head forms of the package's types**, from the
normalization model, in which its declared constants are semantic. -/
theorem facts : FormFacts (rules lv) roles :=
  .ofSemantic (S := setting lv fun _ => 0) (laws lv _) (constants lv _)

/-- The recursor's computation rules preserve typing. -/
theorem roots : RootPreserving (rules lv) := by
  intro n Γ l r A formed step typing
  exact (declares lv fun _ => 0).step_preserves (TowerNumbersModel.facts lv) (RulesSub.refl _)
    formed step typing

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

end TowerNumbersModel

/-! ## Consequences for the tower with natural numbers -/

theorem TowerNumbersModel.setting_roles_num (lv : LevelExpr) (valuation : Nat → Nat) :
    (TowerNumbersModel.setting lv valuation).roles TowerNumbersModel.num =
      .inductive TowerNumbersModel.ctors :=
  TowerNumbersModel.roles_num

section Consequences

open TowerNumbersModel

variable {lv : LevelExpr} {n : Nat} {Γ : Ctx Tower.Head n}

/-- Zero is not a successor. -/
theorem TowerNumbers.zero_ne_succ (formed : CtxFormed (rules lv) Γ) {a : Tm Tower.Head n} :
    ¬ Equal (rules lv) Γ (.const zero) (.app (.const succ) a) (.const num) :=
  Equal.ctor_discrimination (S := setting lv fun _ => 0) (laws lv _) (constants lv _) formed
    (setting_roles_num lv _) mem_zero mem_succ TowerNumbersModel.zero_ne_succ (as := []) (bs := [a])

/-- The successor is injective. -/
theorem TowerNumbers.succ_injective (formed : CtxFormed (rules lv) Γ) {a b : Tm Tower.Head n}
    (equal : Equal (rules lv) Γ (.app (.const succ) a) (.app (.const succ) b) (.const num)) :
    Equal (rules lv) Γ a b (.const num) := by
  obtain ⟨_, _, fieldsEqual⟩ := Equal.ctor_injective (S := setting lv fun _ => 0) (laws lv _)
    (constants lv _) formed (setting_roles_num lv _) mem_succ mem_succ (as := [a]) (bs := [b]) equal
  cases fieldsEqual with
  | cons head _ => exact head

/-- Injectivity of dependent function types. -/
theorem TowerNumbers.pi_injective {A A' : Tm Tower.Head n} {B B' : Tm Tower.Head (n + 1)}
    (equal : TypeEq (rules lv) Γ (.pi A B) (.pi A' B')) (formed : CtxFormed (rules lv) Γ) :
    TypeEq (rules lv) Γ A A' ∧ TypeEq (rules lv) (.snoc Γ A) B B' :=
  TypeEq.pi_injective (TowerNumbersModel.facts lv) equal formed

/-- The natural numbers are not a dependent function type. -/
theorem TowerNumbers.num_ne_pi {A : Tm Tower.Head n} {B : Tm Tower.Head (n + 1)}
    (formed : CtxFormed (rules lv) Γ) : ¬ TypeEq (rules lv) Γ (.const num) (.pi A B) :=
  TypeEq.inductive_ne_pi (TowerNumbersModel.facts lv) roles_num formed

/-- Reduction preserves typing, including the recursor's computation. -/
theorem TowerNumbers.reduces_preserve {t t' T : Tm Tower.Head n}
    (formed : CtxFormed (rules lv) Γ) (red : Reduces (rules lv) t t')
    (typing : Typed (rules lv) Γ t T) :
    Typed (rules lv) Γ t' T ∧ Equal (rules lv) Γ t t' T :=
  Reduces.preserve (S := setting lv fun _ => 0) (TowerNumbersModel.facts lv) (roots lv) (heads lv)
    formed red typing

/-- Soundness of the conversion algorithm. -/
theorem TowerNumbers.algorithm_sound {st : AlgorithmStatement Tower.Head}
    (derivation : Algorithm (rules lv) st) : AlgorithmSound (setting lv fun _ => 0) st :=
  Algorithm.sound (S := setting lv fun _ => 0) (TowerNumbersModel.facts lv) (roots lv) (heads lv)
    (algebra lv) derivation

end Consequences

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
