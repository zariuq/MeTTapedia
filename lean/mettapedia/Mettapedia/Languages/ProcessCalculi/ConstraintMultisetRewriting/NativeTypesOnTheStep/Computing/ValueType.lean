import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.TwoReadings

/-!
# A value type that computes: the numbers with their recursor are qualified at every level

The tree's package of natural numbers with their recursor into a universe of level `lv`
(`TowerNumbersModel`) is **qualified** at every level (`numbers_qualified`), with every hypothesis
proved:

* the recursor's two computation rules are a constructor system (`numConstructors`): linear constructor
  patterns at the last argument, covered right sides, distinct constructors;
* the right sides are typed (the declaration record of the numbers), so subject reduction holds;
* every constant is semantic for the typed equality (the tree's model) and for the algorithmic
  equality (`algorithmicConstants`, the same declaration record read in the algorithmic setting), so
  conversion is decided.

At level one the recursor eliminates into the universe of small types: a **large elimination**. The
value type of a typed interpreter whose codes are numerals is one: `val 0 = num` and
`val (k + 1) = (val k → val k)` (`valueType`). It computes by the recursor's rules and β
(`val_zero_reduces`, `val_succ_reduces`): `val 1` reduces to `num → num` (`val_one_answer`), its unique
answer; at level one the qualified package then gives subject reduction and decided conversion for
every typed instance.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.ValueType

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open AlgebraicSchema AlgebraicParallel ConversionCoherence
open ConstructorSystem (System LeftSide Pattern ConstructorPresentation)
open TowerNumbersModel (num zero succ numRec ctors u mem_zero mem_succ)

variable (lv : LevelExpr Nat)

/-! ## The numbers are qualified -/

/-- The declaration of the numbers, read in the algorithmic setting: only its earlier stage mentions
the equality, and that stage declares no constant. -/
theorem declaresAlgorithmic (valuation : Nat → Nat) :
    DeclaresInductive (algorithmicSetting (TowerNumbersModel.setting lv valuation))
      (constantFreeRules (TowerNumbersModel.rules lv)) TowerNumbersModel.rules₁ TowerNumbersModel.rules₂
      num u ctors numRec (.sort lv) :=
  have d := TowerNumbersModel.declares lv valuation
  { role := d.role
    recRole := d.recRole
    hu := d.hu
    hv := d.hv
    sub₀ := d.sub₀
    sub₁ := d.sub₁
    sub₂ := d.sub₂
    semantic₀ := fun declared => nomatch declared
    stage₁ := d.stage₁
    stage₂ := d.stage₂
    declared := d.declared
    ctorDeclared := d.ctorDeclared
    recDeclared := d.recDeclared
    fieldTyped := d.fieldTyped
    ctorTyped := d.ctorTyped
    recTyped := d.recTyped
    iota := d.iota }

/-- **Every constant of the numbers is semantic for the algorithmic equality.** -/
theorem algorithmicConstants :
    SemanticConstants (algorithmicSetting (TowerNumbersModel.setting lv fun _ => 0)) := by
  intro name type w declared _ _
  have decl := declaresAlgorithmic lv fun _ => 0
  have laws' := algorithmicSetting_laws (S := TowerNumbersModel.setting lv fun _ => 0)
    (TowerNumbersModel.laws lv _) (TowerNumbersModel.constants lv _) (TowerNumbersModel.roots lv)
    (TowerNumbersModel.heads lv) (TowerNumbersModel.algebra lv)
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

/-- Head equality of the numbers is decided. -/
theorem decideHeads (h h' : Tower.Head) :
    HeadSame (TowerNumbersModel.rules lv) h h' ∨ ¬ HeadSame (TowerNumbersModel.rules lv) h h' := by
  rcases Decidable.em (Tower.HeadEq h h') with same | different
  · exact .inl (.inr same)
  · rcases Decidable.em (h = h') with equal | unequal
    · exact .inl (.inl equal)
    · exact .inr fun same => same.elim unequal different

/-- The recursor at an argument spine. -/
abbrev recAt {n : Nat} (p z s t : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.app (.app (.const numRec) p) z) s) t

/-- **The recursor's two rules**, as open equations. -/
inductive IotaSchema : {arity : Nat} → Tower.Tm arity → Tower.Tm arity → Prop
  | zero : IotaSchema (arity := 3) (recAt (.var 2) (.var 1) (.var 0) (.const zero)) (.var 1)
  | succ : IotaSchema (arity := 4) (recAt (.var 3) (.var 2) (.var 1) (.app (.const succ) (.var 0)))
      (.app (.app (.var 1) (.var 0)) (recAt (.var 3) (.var 2) (.var 1) (.var 0)))

/-- The root steps of the numbers are exactly the instances of the two rules. -/
def numPresentation : SchemaPresentation (TowerNumbersModel.rules lv) where
  schema := IotaSchema
  sound := by
    intro arity ambient left right rule σ
    cases rule with
    | zero => exact ⟨σ 2, [σ 1, σ 0], 0, zero, [], [], σ 1, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | succ =>
        exact ⟨σ 3, [σ 2, σ 1], 1, succ, [.recursive], [σ 0], σ 1, rfl, rfl, rfl, rfl, rfl, rfl⟩
  cover := by
    intro n source target step
    obtain ⟨p, ms, i, k, fields, args, m, hms, hi, has, hm, rfl, rfl⟩ := step
    rcases ms with _ | ⟨z, _ | ⟨s, _ | ⟨_, _⟩⟩⟩
    · cases hms
    · cases hms
    · rcases i with _ | _ | i
      · simp only [ctors, List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        rcases args with _ | ⟨_, _⟩
        · simp only [List.getElem?_cons_zero, Option.some.injEq] at hm
          subst hm
          exact ⟨3, _, _, consSub s (consSub z (consSub p Fin.elim0)), .zero, rfl, rfl⟩
        · cases has
      · simp only [ctors, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq,
          Prod.mk.injEq] at hi
        obtain ⟨rfl, rfl⟩ := hi
        rcases args with _ | ⟨a, _ | ⟨_, _⟩⟩
        · cases has
        · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hm
          subst hm
          exact ⟨4, _, _, consSub a (consSub s (consSub z (consSub p Fin.elim0))), .succ, rfl, rfl⟩
        · cases has
      · cases hi
    · cases hms

/-- **The recursor's rules are a constructor system.** -/
def numSystem : System Tower.Head where
  schema := IotaSchema
  defined name := name = numRec
  arity _ := 4
  left := by
    intro m left right rule
    refine ⟨numRec, rfl, by decide, ?_⟩
    cases rule with
    | zero =>
        exact .app (.app (.app (.app (.const numRec) (.var 2)) (.var 1)) (.var 0))
          (.const (show ¬ zero = numRec by decide))
    | succ =>
        exact .app (.app (.app (.app (.const numRec) (.var 3)) (.var 2)) (.var 1))
          (.app (.const (show ¬ succ = numRec by decide)) (.var 0))
  linear := by
    intro arity left right rule
    cases rule with
    | zero => unfold LeftLinear; decide
    | succ => unfold LeftLinear; decide
  covered := by
    intro m left right rule
    cases rule with
    | zero => decide
    | succ => decide
  determined := by
    intro m m' n n' left right left' right' rule rule' σ σ' same develop
    cases rule with
    | zero =>
        cases rule' with
        | zero =>
            have same' : recAt (σ 2) (σ 1) (σ 0) (.const zero) = recAt (σ' 2) (σ' 1) (σ' 0) (.const zero) :=
              same
            obtain ⟨f₁, -⟩ := Tm.app.inj same'
            obtain ⟨f₂, -⟩ := Tm.app.inj f₁
            obtain ⟨-, second⟩ := Tm.app.inj f₂
            show develop (σ 1) = develop (σ' 1)
            rw [second]
        | succ =>
            have same' : recAt (σ 2) (σ 1) (σ 0) (.const zero) =
                recAt (σ' 3) (σ' 2) (σ' 1) (.app (.const succ) (σ' 0)) := same
            obtain ⟨-, clash⟩ := Tm.app.inj same'
            cases clash
    | succ =>
        cases rule' with
        | zero =>
            have same' : recAt (σ 3) (σ 2) (σ 1) (.app (.const succ) (σ 0)) =
                recAt (σ' 2) (σ' 1) (σ' 0) (.const zero) := same
            obtain ⟨-, clash⟩ := Tm.app.inj same'
            cases clash
        | succ =>
            have same' : recAt (σ 3) (σ 2) (σ 1) (.app (.const succ) (σ 0)) =
                recAt (σ' 3) (σ' 2) (σ' 1) (.app (.const succ) (σ' 0)) := same
            obtain ⟨f₁, scrutinee⟩ := Tm.app.inj same'
            obtain ⟨f₂, third⟩ := Tm.app.inj f₁
            obtain ⟨f₃, second⟩ := Tm.app.inj f₂
            obtain ⟨-, first⟩ := Tm.app.inj f₃
            obtain ⟨-, field⟩ := Tm.app.inj scrutinee
            show Tm.app (.app (develop (σ 1)) (develop (σ 0)))
                (recAt (develop (σ 3)) (develop (σ 2)) (develop (σ 1)) (develop (σ 0))) =
              Tm.app (.app (develop (σ' 1)) (develop (σ' 0)))
                (recAt (develop (σ' 3)) (develop (σ' 2)) (develop (σ' 1)) (develop (σ' 0)))
            rw [first, second, third, field]

/-- **The numbers as a definition by constructor patterns.** -/
def numConstructors : ConstructorPresentation (TowerNumbersModel.rules lv) where
  presentation := numPresentation lv
  system := numSystem
  same _ _ := Iff.rfl
  symmetric := LevelTower.headEq_symmetric

/-- **The numbers with their recursor are qualified, at every level.** -/
theorem numbers_qualified : Qualified (TowerNumbersModel.setting lv fun _ => 0) where
  laws := TowerNumbersModel.laws lv _
  constructors := ⟨numConstructors lv⟩
  constants := TowerNumbersModel.constants lv _
  roots := TowerNumbersModel.roots lv
  heads := TowerNumbersModel.heads lv
  algebra := TowerNumbersModel.algebra lv
  algorithmicConstants := algorithmicConstants lv
  decideHeads := decideHeads lv

/-! ## The value type of an interpreter, computing -/

/-- The level of the universe of small types: the recursor eliminates into it at level one. -/
abbrev smallTypes : LevelExpr Nat := .succ (.const 0)

/-- The universe of small types. -/
abbrev U0 {n : Nat} : Tower.Tm n := .head u

/-- The motive `λ _. U0`. -/
abbrev motive {n : Nat} : Tower.Tm n := .lam U0

/-- The successor case `λ _ X. X → X`. -/
abbrev arrowCase {n : Nat} : Tower.Tm n := .lam (.lam (.pi (.var 0) (.var 1)))

/-- **The value type of codes**: `val 0 = num`, `val (k + 1) = val k → val k`. -/
abbrev valueType {n : Nat} (code : Tower.Tm n) : Tower.Tm n := recAt motive (.const num) arrowCase code

abbrev numbers : Rules Tower.Head := TowerNumbersModel.rules smallTypes

/-- `val 0 ⟶ num`, by the recursor's zero rule. -/
theorem val_zero_reduces {n : Nat} : StepStar numbers (valueType (.const zero) : Tower.Tm n) (.const num) :=
  .single (.root ((numPresentation smallTypes).sound IotaSchema.zero
    (consSub arrowCase (consSub (.const num) (consSub motive Fin.elim0)))))

/-- `val (k + 1) ⟶ val k → val k`, by the recursor's successor rule and two β-steps. -/
theorem val_succ_reduces {n : Nat} (code : Tower.Tm n) :
    StepStar numbers (valueType (.app (.const succ) code))
      (.pi (valueType code) (Presentation.rename wk (valueType code))) := by
  have iota : StepCore numbers.computation numbers.headEq (valueType (.app (.const succ) code))
      (.app (.app arrowCase code) (valueType code)) :=
    .root ((numPresentation smallTypes).sound IotaSchema.succ
      (consSub code (consSub arrowCase (consSub (.const num) (consSub motive Fin.elim0)))))
  have beta₁ : StepCore numbers.computation numbers.headEq (.app (.app arrowCase code) (valueType code))
      (.app (inst0 code (.lam (.pi (.var 0) (.var 1)))) (valueType code)) :=
    .congAppFun (.betaPi _ _)
  have beta₂ : StepCore numbers.computation numbers.headEq
      (.app (inst0 code (.lam (.pi (.var 0) (.var 1)))) (valueType code))
      (inst0 (valueType code) (.pi (.var 0) (.var 1))) :=
    .betaPi _ _
  exact .head iota (.head beta₁ (.single beta₂))

theorem stepStar_piDom {n : Nat} {A A' : Tower.Tm n} {B : Tower.Tm (n + 1)}
    (steps : StepStar numbers A A') : StepStar numbers (.pi A B) (.pi A' B) := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (.congPiDom step)

theorem stepStar_piCod {n : Nat} {A : Tower.Tm n} {B B' : Tower.Tm (n + 1)}
    (steps : StepStar numbers B B') : StepStar numbers (.pi A B) (.pi A B') := by
  induction steps with
  | refl => exact .refl
  | tail _ step ih => exact .tail ih (.congPiCod step)

/-- The type `num` is normal. -/
theorem num_normal {n : Nat} : ConstructorSystem.Normal numbers (.const num : Tower.Tm n) := by
  intro t h
  cases h with
  | root h =>
      obtain ⟨name, count, defined, head⟩ :=
        ConstructorSystem.computation_head (numConstructors smallTypes) h
      cases head
      exact TowerNumbersModel.num_ne_numRec defined

/-- **`val 1 = num → num`**, the unique answer of the code `1`. -/
theorem val_one_answer :
    Answer numbers (valueType (.app (.const succ) (.const zero)) : Tower.Tm 0)
      (.pi (.const num) (.const num)) ∧
    ∀ v, Answer numbers (valueType (.app (.const succ) (.const zero)) : Tower.Tm 0) v →
      v = .pi (.const num) (.const num) := by
  have steps : StepStar numbers (valueType (.app (.const succ) (.const zero)) : Tower.Tm 0)
      (.pi (.const num) (.const num)) :=
    (val_succ_reduces (n := 0) (.const zero)).trans
      ((stepStar_piDom (val_zero_reduces (n := 0))).trans (stepStar_piCod (val_zero_reduces (n := 1))))
  have normal : ConstructorSystem.Normal numbers (.pi (.const num) (.const num) : Tower.Tm 0) := by
    intro t h
    cases h with
    | root h => exact (numConstructors smallTypes).no_root_of_spineHead h rfl
    | congPiDom h => exact num_normal h
    | congPiCod h => exact num_normal h
  refine ⟨⟨steps, normal⟩, fun v answer => ?_⟩
  exact answer_unique (numbers_qualified smallTypes).churchRosser answer ⟨steps, normal⟩

/-! ## The value type is typed, and types use it -/

section Typing

variable {m : Nat} {Δ : Ctx Tower.Head m}

/-- The universe of the universe of small types. -/
abbrev U1 {n : Nat} : Tower.Tm n := .head (.sort smallTypes)

theorem num_typedV : Typed numbers Δ (.const num) U0 :=
  .const (TowerNumbersModel.declaredNum smallTypes) (.headType (.sort _)) (.sort _)

theorem zero_typedV : Typed numbers Δ (.const zero) (.const num) :=
  .const (TowerNumbersModel.declaredZero smallTypes) num_typedV (.sort _)

theorem succ_typedV : Typed numbers Δ (.const succ) (.pi (.const num) (.const num)) :=
  .const (TowerNumbersModel.declaredSucc smallTypes)
    (.piForm num_typedV (.sort _) num_typedV (.sort _) (.sorts _ _)) (.sort _)

theorem rec_typedV : Typed numbers Δ (.const numRec) (liftClosed (recType num (.sort smallTypes) ctors)) := by
  obtain ⟨w, hw, typed⟩ := (TowerNumbersModel.declares smallTypes fun _ => 0).toRecursor.recTyped
  exact .const (TowerNumbersModel.declaredRec smallTypes) typed hw

theorem motiveTy_typed :
    Typed numbers Δ (.pi (.const num) U1) (.head (.sort (.max (.const 0) (.succ smallTypes)))) :=
  .piForm num_typedV (.sort _) (.headType (.sort _)) (.sort _) (.sorts _ _)

/-- The motive is a family of small types. -/
theorem motive_typed : Typed numbers Δ motive (.pi (.const num) U1) :=
  .lamIntro motiveTy_typed (.sort _) (.headType (.sort _))

/-- The motive at a number is the universe of small types. -/
theorem motive_beta {t : Tower.Tm m} (typed : Typed numbers Δ t (.const num)) :
    Equal numbers Δ (.app motive t) U0 U1 :=
  .betaPi motiveTy_typed (.sort _) (.headType (.sort _)) typed

/-- A dependent function type between small types is small. -/
theorem collapse0 : numbers.cumulative (.sort (.max (.const 0) (.const 0))) (.sort (.const 0)) := by
  change LevelTower.Cumulative (.sort (.max (.const 0) (.const 0))) (.sort (.const 0))
  intro valuation
  simp [LevelExpr.eval]

theorem arrow_small {n : Nat} {Γ : Ctx Tower.Head n} {A : Tower.Tm n} {B : Tower.Tm (n + 1)}
    (typedA : Typed numbers Γ A U0) (typedB : Typed numbers (.snoc Γ A) B U0) :
    Typed numbers Γ (.pi A B) U0 :=
  .cumul (.piForm typedA (.sort _) typedB (.sort _) (.sorts _ _)) collapse0

/-- The method at zero, `num : motive zero`. -/
theorem zeroMethod : Typed numbers Δ (.const num) (.app motive (.const zero)) :=
  .conv num_typedV (.symm (motive_beta zero_typedV)) (.sort _)

/-- The method at a successor, `λ x X. X → X : Π (x : num). motive x → motive (succ x)`. -/
theorem succMethod :
    Typed numbers Δ arrowCase
      (.pi (.const num) (.pi (.app motive (.var 0)) (.app motive (.app (.const succ) (.var 1))))) := by
  have x1 : Typed numbers (.snoc (.snoc Δ (.const num)) (.app motive (.var 0))) (.var 1) (.const num) :=
    .var 1
  have succX : Typed numbers (.snoc (.snoc Δ (.const num)) (.app motive (.var 0)))
      (.app (.const succ) (.var 1)) (.const num) :=
    .appElim succ_typedV x1
  have bigX : Typed numbers (.snoc (.snoc Δ (.const num)) (.app motive (.var 0))) (.var 0) U0 :=
    .conv (.var 0) (motive_beta x1) (.sort _)
  have x2 : Typed numbers (.snoc (.snoc (.snoc Δ (.const num)) (.app motive (.var 0))) (.var 0)) (.var 2)
      (.const num) :=
    .var 2
  have bigX' : Typed numbers (.snoc (.snoc (.snoc Δ (.const num)) (.app motive (.var 0))) (.var 0))
      (.var 1) U0 :=
    .conv (.var 1) (motive_beta x2) (.sort _)
  have body : Typed numbers (.snoc (.snoc Δ (.const num)) (.app motive (.var 0))) (.pi (.var 0) (.var 1))
      (.app motive (.app (.const succ) (.var 1))) :=
    .conv (arrow_small bigX bigX') (.symm (motive_beta succX)) (.sort _)
  have x0 : Typed numbers (.snoc Δ (.const num)) (.var 0) (.const num) := .var 0
  have innerPi : Typed numbers (.snoc Δ (.const num))
      (.pi (.app motive (.var 0)) (.app motive (.app (.const succ) (.var 1))))
      (.head (.sort (.max smallTypes smallTypes))) :=
    .piForm (.appElim motive_typed x0) (.sort _) (.appElim motive_typed succX) (.sort _) (.sorts _ _)
  have outerPi : Typed numbers Δ
      (.pi (.const num) (.pi (.app motive (.var 0)) (.app motive (.app (.const succ) (.var 1)))))
      (.head (.sort (.max (.const 0) (.max smallTypes smallTypes)))) :=
    .piForm num_typedV (.sort _) innerPi (.sort _) (.sorts _ _)
  exact .lamIntro outerPi (.sort _) (.lamIntro innerPi (.sort _) body)

/-- **The value type of a code is a small type.** -/
theorem valueType_typed {code : Tower.Tm m} (typed : Typed numbers Δ code (.const num)) :
    Typed numbers Δ (valueType code) U0 :=
  .conv (recApp_typed rec_typedV motive_typed (.cons zeroMethod (.cons succMethod .nil)) typed)
    (motive_beta typed) (.sort _)

/-- **`val 1 ≡ num → num`, as a typed equality of small types**, by the qualified package. -/
theorem val_one_equal :
    Typed numbers .nil (.pi (.const num) (.const num)) U0 ∧
      Equal numbers .nil (valueType (.app (.const succ) (.const zero))) (.pi (.const num) (.const num)) U0 :=
  (numbers_qualified smallTypes).answer_typed .nil (valueType_typed (.appElim succ_typedV zero_typedV))
    val_one_answer.1

/-- **A program typed by the value type**: the identity has type `val 1`. -/
theorem identity_at_val_one :
    Typed numbers .nil (.lam (.var 0)) (valueType (.app (.const succ) (.const zero))) :=
  .conv (.lamIntro val_one_equal.1 (.sort _) (.var 0)) (.symm val_one_equal.2) (.sort _)

end Typing

end NativeTypesOnTheStep.Computing.ValueType

#print axioms NativeTypesOnTheStep.Computing.ValueType.declaresAlgorithmic
#print axioms NativeTypesOnTheStep.Computing.ValueType.algorithmicConstants
#print axioms NativeTypesOnTheStep.Computing.ValueType.decideHeads
#print axioms NativeTypesOnTheStep.Computing.ValueType.numPresentation
#print axioms NativeTypesOnTheStep.Computing.ValueType.numSystem
#print axioms NativeTypesOnTheStep.Computing.ValueType.numConstructors
#print axioms NativeTypesOnTheStep.Computing.ValueType.numbers_qualified
#print axioms NativeTypesOnTheStep.Computing.ValueType.val_zero_reduces
#print axioms NativeTypesOnTheStep.Computing.ValueType.val_succ_reduces
#print axioms NativeTypesOnTheStep.Computing.ValueType.val_one_answer
#print axioms NativeTypesOnTheStep.Computing.ValueType.motive_typed
#print axioms NativeTypesOnTheStep.Computing.ValueType.succMethod
#print axioms NativeTypesOnTheStep.Computing.ValueType.valueType_typed
#print axioms NativeTypesOnTheStep.Computing.ValueType.val_one_equal
#print axioms NativeTypesOnTheStep.Computing.ValueType.identity_at_val_one

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
