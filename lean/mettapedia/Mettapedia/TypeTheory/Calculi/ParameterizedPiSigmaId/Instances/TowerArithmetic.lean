import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.RecursionComputation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.TowerNumbers
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Normalization.WeakHeadNormalization

/-!
# The cumulative tower with natural numbers and addition

The tower with the natural numbers and their recursor, extended by addition,
defined by structural recursion on its second argument:

`add : Π (n : num) (t : num). num`,
`add n zero ⟶ n`,
`add n (succ m) ⟶ succ (add n m)`.

The recursive call `add n m` is abstracted as the hypothesis of the second
equation. Every hypothesis of the normalization model holds, so addition is a
semantic constant and the consequences hold without hypotheses: typed terms
have weak-head normal forms, reduction, including both recursive equations,
preserves typing, the conversion algorithm is sound, and a sum
`add a (succ b)` is never equal to `zero`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Normalization

open Mettapedia.TypeTheory.UniverseLevel
open TelescopeAbstraction (closeType applyClosed)
open TowerNumbersModel (num zero succ numRec ctors u mem_zero mem_succ num_ne_zero num_ne_succ
  num_ne_numRec zero_ne_succ zero_ne_numRec succ_ne_numRec)

namespace TowerArithmeticModel

/-- Addition. -/
def add : DeclName := .mkSimple "add"

theorem num_ne_add : num ≠ add := by decide
theorem zero_ne_add : zero ≠ add := by decide
theorem succ_ne_add : succ ≠ add := by decide
theorem numRec_ne_add : numRec ≠ add := by decide

/-- The entries of addition's telescope: two numbers. -/
def entries : (i : Nat) → Tm Tower.Head i := fun _ => .const num

/-- The right-hand sides with the recursive call abstracted: the first argument
at zero, and the successor of the hypothesis, which stands for the recursive
call, at a successor. -/
def body : (k : DeclName) → (fields : List (Field Tower.Head)) →
    Tm Tower.Head (1 + fields.length + 0 + (recPositions fields).length)
  | _, [] => .var ⟨0, by decide⟩
  | _, [.recursive] => .app (.const succ) (.var ⟨0, by decide⟩)
  | _, _ => .const add

/-- The declared type of addition. -/
def addType : Tm Tower.Head 0 := closeType (ofEntries entries 2) (.const num)

variable (lv : LevelExpr)

/-- The declared types. -/
def constantType : DeclName → Option (Tm Tower.Head 0) := fun name =>
  if name = add then some addType else TowerNumbersModel.constantType lv name

/-- The tower with the natural numbers, their recursor into level `lv`, and
addition. -/
def rules : Rules Tower.Head :=
  { Tower.rules with
    constantType := constantType lv
    computation := RootComputation.union (iotaComputation numRec ctors)
      (recursionComputation add ctors entries 1 0 body) }

/-- The roles of the declared constants. -/
def roles : Roles Tower.Head := fun name =>
  if name = add then .computes 2 (.split 1 .constructor fun _ => .leaf) else TowerNumbersModel.roles name

theorem roles_add : roles add = .computes 2 (.split 1 .constructor fun _ => .leaf) := by simp [roles]
theorem roles_num : roles num = .inductive ctors := by
  simp [roles, num_ne_add, TowerNumbersModel.roles_num]
theorem roles_numRec : roles numRec = .computes 4 (.split 3 .constructor fun _ => .leaf) := by
  simp [roles, numRec_ne_add, TowerNumbersModel.roles_numRec]

/-- The only inductive type is `num`. -/
theorem roles_inductive {T : DeclName} {cs : List (DeclName × List (Field Tower.Head))}
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
    · simp [roles, zero_ne_add, TowerNumbersModel.roles_zero]
    · simp [roles, succ_ne_add, TowerNumbersModel.roles_succ]
  distinct := by
    intro T cs role
    obtain ⟨rfl, rfl⟩ := roles_inductive role
    simp only [ctors, List.map_cons, List.map_nil]
    exact List.nodup_cons.mpr ⟨by simp [zero_ne_succ], List.nodup_singleton _⟩

theorem shape : RootShape (rules lv) roles where
  spine := by
    intro n t u step
    rcases step with step | step
    · exact IotaStep.spine (T := num) roles_num roles_numRec constructorsDeclared step
    · exact RecursionStep.spine roles_num constructorsDeclared roles_add step
  deterministic := by
    intro n t u u' step step'
    exact RootComputation.union_deterministic numRec_ne_add
      (fun h => by
        obtain ⟨p, ms, _, k, _, args, _, _, _, _, _, rfl, rfl⟩ := h
        exact ⟨_, rfl⟩)
      (fun h => by
        obtain ⟨_, _, σ, _, _, _, rfl, rfl⟩ := h
        exact ⟨_, applyClosed_eq_appSpine _ _ _⟩)
      (fun h h' => IotaStep.deterministic (T := num) roles_num constructorsDeclared h h')
      (fun h h' => RecursionStep.deterministic roles_num constructorsDeclared h h') step' step

/-- The tower's level model, for the rule package with addition. -/
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

theorem declaredSucc₂ :
    TowerNumbersModel.rules₂.constantType succ = some (ctorType num [.recursive]) := by
  simp [TowerNumbersModel.rules₂, num_ne_succ.symm, zero_ne_succ.symm]

theorem num_typed₂ {n : Nat} {Γ : Ctx Tower.Head n} :
    Typed TowerNumbersModel.rules₂ Γ (.const num) (.head u) :=
  TowerNumbersModel.num_typed Tower.HeadTyping.sort Tower.IsUniverse.sort declaredNum₂

theorem succ_typed₂ {n : Nat} {Γ : Ctx Tower.Head n} :
    Typed TowerNumbersModel.rules₂ Γ (.const succ) (.pi (.const num) (.const num)) :=
  .const declaredSucc₂ (.piForm num_typed₂ (.sort _) num_typed₂ (.sort _) (.sorts _ _)) (.sort _)

theorem addType_typed : ∃ w, Tower.IsUniverse w ∧
    Typed TowerNumbersModel.rules₂ .nil addType (.head w) :=
  ⟨_, .sort _, .piForm num_typed₂ (.sort _)
    (.piForm num_typed₂ (.sort _) num_typed₂ (.sort _) (.sorts _ _)) (.sort _) (.sorts _ _)⟩

/-! ## The hypotheses of the model -/

section Hypotheses

variable (valuation : Nat → Nat)

theorem constantType_ne_add {name : DeclName} (h : name ≠ add) :
    (rules lv).constantType name = (TowerNumbersModel.rules lv).constantType name := by
  show (if name = add then some addType else TowerNumbersModel.constantType lv name) = _
  rw [if_neg h]
  rfl

theorem declaredNum : (rules lv).constantType num = some (.head u) := by
  rw [constantType_ne_add lv num_ne_add]
  exact TowerNumbersModel.declaredNum lv

theorem declaredZero : (rules lv).constantType zero = some (ctorType num []) := by
  rw [constantType_ne_add lv zero_ne_add]
  exact TowerNumbersModel.declaredZero lv

theorem declaredSucc : (rules lv).constantType succ = some (ctorType num [.recursive]) := by
  rw [constantType_ne_add lv succ_ne_add]
  exact TowerNumbersModel.declaredSucc lv

theorem declaredRec : (rules lv).constantType numRec = some (recType num (.sort lv) ctors) := by
  rw [constantType_ne_add lv numRec_ne_add]
  exact TowerNumbersModel.declaredRec lv

theorem declaredAdd : (rules lv).constantType add = some addType := by
  simp [rules, constantType]

/-- The earlier stages of the natural numbers are inside the package. -/
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
  iota := fun hms hi has hm => .inl ⟨_, _, _, _, _, _, _, hms, hi, has, hm, rfl, rfl⟩

/-- The package declares addition by structural recursion. -/
theorem declaresAdd :
    DeclaresRecursion (setting lv valuation) TowerNumbersModel.rules₂ add num ctors entries 1 0
      (.const num) body where
  role := roles_add
  scrutinee := rfl
  declared := declaredAdd lv
  sub₀ := sub₂ lv
  semantic₀ := (declares lv valuation).semantic₂ (laws lv valuation)
  typed := addType_typed
  formed := by
    intro k fields mem
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show CtxFormed TowerNumbersModel.rules₂ (.snoc .nil (.const num))
      exact .snoc .nil ⟨_, .sort _, num_typed₂⟩
    · show CtxFormed TowerNumbersModel.rules₂
        (.snoc (.snoc (.snoc .nil (.const num)) (.const num)) (.const num))
      exact .snoc (.snoc (.snoc .nil ⟨_, .sort _, num_typed₂⟩) ⟨_, .sort _, num_typed₂⟩)
        ⟨_, .sort _, num_typed₂⟩
  bodyTyped := by
    intro k fields mem
    simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · show Typed TowerNumbersModel.rules₂ (.snoc .nil (.const num)) (.var 0) (.const num)
      exact .var 0
    · show Typed TowerNumbersModel.rules₂
        (.snoc (.snoc (.snoc .nil (.const num)) (.const num)) (.const num))
        (.app (.const succ) (.var 0)) (.const num)
      exact .appElim succ_typed₂ (.var 0)
  rule := by
    intro k fields mem m σ as has
    exact .inr ⟨_, _, σ, as, mem, has, rfl, rfl⟩

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
    exact (declaresAdd lv valuation).semantic laws' decl formed r
  · unfold TowerNumbersModel.constantType at declared
    split at declared
    · rename_i _ h
      subst h
      cases declared
      intro m Δ formed P r
      exact decl.type_semantic laws' formed r
    · split at declared
      · rename_i _ _ h
        subst h
        cases declared
        intro m Δ formed P r
        exact decl.ctor_semantic laws' mem_zero formed r
      · split at declared
        · rename_i _ _ _ h
          subst h
          cases declared
          intro m Δ formed P r
          exact decl.ctor_semantic laws' mem_succ formed r
        · split at declared
          · rename_i _ _ _ _ h
            subst h
            cases declared
            intro m Δ formed P r
            exact decl.rec_semantic laws' formed r
          · cases declared

/-- **The facts about the weak-head forms of the package's types**, from the
normalization model, in which its declared constants are semantic. -/
theorem facts : FormFacts (rules lv) roles :=
  .ofSemantic (S := setting lv fun _ => 0) (laws lv _) (constants lv _)

/-- The recursor's computation rules and the equations of addition preserve
typing. -/
theorem roots : RootPreserving (rules lv) := by
  intro n Γ l r A formed step typing
  rcases step with step | step
  · exact (declares lv fun _ => 0).step_preserves (TowerArithmeticModel.facts lv) (RulesSub.refl _)
      formed step typing
  · obtain ⟨k, fields, σ, as, mem, has, rfl, rfl⟩ := step
    exact (declaresAdd lv fun _ => 0).rule_preserves (TowerArithmeticModel.facts lv) (declares lv
        fun _ => 0) (RulesSub.refl _) formed mem σ as has typing

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

/-- The step of the second equation at `add a (succ b)`. -/
theorem add_succ_step {n : Nat} (a b : Tm Tower.Head n) :
    (rules lv).computation.step (.app (.app (.const add) a) (.app (.const succ) b))
      (.app (.const succ) (.app (.app (.const add) a) b)) :=
  .inr ⟨succ, [.recursive], consSub (.app (.const succ) b) (consSub a fun i => Fin.elim0 i), [b],
    mem_succ, rfl, rfl, rfl⟩

end TowerArithmeticModel

/-! ## Consequences for the tower with addition -/

theorem TowerArithmeticModel.setting_roles_num (lv : LevelExpr) (valuation : Nat → Nat) :
    (TowerArithmeticModel.setting lv valuation).roles num = .inductive ctors :=
  TowerArithmeticModel.roles_num

section Consequences

open TowerArithmeticModel

variable {lv : LevelExpr} {n : Nat} {Γ : Ctx Tower.Head n}

/-- Reduction preserves typing, including the recursor's computation and the
equations of addition. -/
theorem TowerArithmetic.reduces_preserve {t t' T : Tm Tower.Head n}
    (formed : CtxFormed (rules lv) Γ) (red : Reduces (rules lv) t t')
    (typing : Typed (rules lv) Γ t T) :
    Typed (rules lv) Γ t' T ∧ Equal (rules lv) Γ t t' T :=
  Reduces.preserve (S := setting lv fun _ => 0) (TowerArithmeticModel.facts lv) (roots lv) (heads
      lv)
    formed red typing

/-- Every typed term of a formed context has a weak-head normal form. -/
theorem TowerArithmetic.whnf_exists {t T : Tm Tower.Head n} (typing : Typed (rules lv) Γ t T)
    (formed : CtxFormed (rules lv) Γ) :
    ∃ nf, WhRed (rules lv) roles t nf ∧ Whnf (rules lv) roles nf :=
  Typed.whnf_exists (S := setting lv fun _ => 0) (laws lv _) (constants lv _) typing formed

/-- Soundness of the conversion algorithm. -/
theorem TowerArithmetic.algorithm_sound {st : AlgorithmStatement Tower.Head}
    (derivation : Algorithm (rules lv) st) : AlgorithmSound (setting lv fun _ => 0) st :=
  Algorithm.sound (S := setting lv fun _ => 0) (TowerArithmeticModel.facts lv) (roots lv) (heads lv)
    (algebra lv) derivation

/-- A sum with a successor as second argument is never zero. -/
theorem TowerArithmetic.add_succ_ne_zero (formed : CtxFormed (rules lv) Γ) {a b : Tm Tower.Head n}
    (typing : Typed (rules lv) Γ (.app (.app (.const add) a) (.app (.const succ) b)) (.const num)) :
    ¬ Equal (rules lv) Γ (.app (.app (.const add) a) (.app (.const succ) b)) (.const zero)
      (.const num) := by
  intro equal
  have red : Reduces (rules lv) (.app (.app (.const add) a) (.app (.const succ) b))
      (.app (.const succ) (.app (.app (.const add) a) b)) :=
    .single (.root (add_succ_step lv a b))
  obtain ⟨_, computed⟩ := TowerArithmetic.reduces_preserve formed red typing
  have toSucc : Equal (rules lv) Γ (.const zero) (.app (.const succ) (.app (.app (.const add) a) b))
      (.const num) := .trans (.symm equal) computed
  exact Equal.ctor_discrimination (S := setting lv fun _ => 0) (laws lv _) (constants lv _) formed
    (setting_roles_num lv _) mem_zero mem_succ zero_ne_succ (as := [])
    (bs := [.app (.app (.const add) a) b])
    toSucc

end Consequences

end Normalization
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
