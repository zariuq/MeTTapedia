import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.ValueTypeRow

/-!
# Unification modulo the package's computation is not unitary

A qualified package lets its equations compute in types, and so in the knowledge of the step. Then a
store can be solvable with no principal answer for a reason the tower does not have: the unknowns may
be fixed only by running the computation backwards.

**Canonical forms** (`num_canonical`): a number in a formed context is typed-equal to a constructor
application or to a neutral term, its weak-head normal form.

**The smallest example** (`addStore`): over `x y : num`, the single equation `add x y ≐ 1`. It is
solved by `x ↦ 0, y ↦ 1` and by `x ↦ 1, y ↦ 0` (`addStore_solved₀₁`, `addStore_solved₁₀`), and **it
has no principal answer** (`addStore_no_principal`): an answer sends `x` to a number whose weak-head
normal form is neutral, `zero` or a successor; neutral makes `add x y` stuck where it must be `1`,
`zero` cannot become `1` along the second solution, and a successor cannot become `0` along the first.

**The package's settler postpones it**: its family neither settles nor refutes the store, by kernel
evaluation (`addStore_postponed`). The store is outside the pattern fragment; the family's third
outcome is the honest one.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Vectors

open _root_.CategoryTheory Opposite Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open TowerNumbersModel (num zero succ numRec ctors u mem_zero mem_succ)
open TowerVectorsModel (U0 numC zeroC succC addC)
open TowerVectorsPrograms (add_typed)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (level1 pkg D numType)

/-! ## Canonical forms of numbers -/

/-- **A number is typed-equal to its weak-head normal form**, which is a constructor application of
the numbers or a neutral term. -/
theorem num_canonical {n : Nat} {Γ : Ctx Tower.Head n} (formed : CtxFormed pkg Γ) {t : Tower.Tm n}
    (typing : Typed pkg Γ t numC) :
    ∃ nf, Equal pkg Γ t nf numC ∧
      ((∃ k fields args, (k, fields) ∈ ctors ∧ nf = appSpine (.const k) args) ∨
        Neutral TowerVectorsModel.roles nf) := by
  obtain ⟨r, eq⟩ := Equal.reducible (S := vecS) (TowerVectorsModel.laws level1 _)
    (TowerVectorsModel.constants level1 _) (Derivable.refl typing) formed
  obtain ⟨fieldPack, same, _⟩ := Reducible.inductive_view (S := vecS)
    (show vecS.roles num = .inductive ctors from TowerVectorsModel.roles_num) r
  rw [same] at eq
  obtain ⟨red, _, _, normal⟩ := eq
  have equal : Equal pkg Γ t _ numC :=
    (vectors_subjectReduction level1 formed (WhRed.reduces red.red) typing).2
  rcases normal.shape with ⟨k₀, fields₀, args, _, mem₀, _, e, _⟩ | ⟨neutral₀, _⟩
  · exact ⟨_, equal, .inl ⟨k₀, fields₀, args, mem₀, e⟩⟩
  · exact ⟨_, equal, .inr neutral₀⟩

/-- `zero` as a constructor application. -/
theorem zero_spine {n : Nat} : (zeroC : Tower.Tm n) = appSpine (.const zero) [] := rfl

/-- `succ t` as a constructor application. -/
theorem succ_spine {n : Nat} (t : Tower.Tm n) : succC t = appSpine (.const succ) [t] := rfl

/-- Distinct constructors of the numbers are never equal. -/
theorem num_ctor_apart {n : Nat} {Γ : Ctx Tower.Head n} (formed : CtxFormed pkg Γ) {k k' : DeclName}
    {fields fields' : List (Normalization.Field Tower.Head)} (mem : (k, fields) ∈ ctors)
    (mem' : (k', fields') ∈ ctors) (distinct : k ≠ k') {as bs : List (Tower.Tm n)} :
    ¬ Equal pkg Γ (appSpine (.const k) as) (appSpine (.const k') bs) numC :=
  Equal.ctor_discrimination (S := vecS) (TowerVectorsModel.laws level1 _) (TowerVectorsModel.constants level1 _)
    formed (show vecS.roles num = .inductive ctors from TowerVectorsModel.roles_num) mem mem' distinct

/-- A constructor application of the numbers is never a neutral term. -/
theorem num_ctor_ne_neutral {n : Nat} {Γ : Ctx Tower.Head n} (formed : CtxFormed pkg Γ) {k : DeclName}
    {fields : List (Normalization.Field Tower.Head)} (mem : (k, fields) ∈ ctors) {as : List (Tower.Tm n)}
    {b : Tower.Tm n} (neutral : Neutral TowerVectorsModel.roles b) :
    ¬ Equal pkg Γ (appSpine (.const k) as) b numC :=
  Equal.ctor_ne_neutral (S := vecS) (TowerVectorsModel.laws level1 _) (TowerVectorsModel.constants level1 _)
    formed (show vecS.roles num = .inductive ctors from TowerVectorsModel.roles_num) mem neutral

/-- Substituting a constructor application substitutes its arguments. -/
theorem subst_ctorSpine {n m : Nat} (ρ : Sub Tower.Head n m) (k : DeclName) :
    ∀ (args : List (Tower.Tm n)),
      Presentation.subst ρ (appSpine (.const k) args) = appSpine (.const k) (args.map (Presentation.subst ρ)) :=
  fun args => subst_appSpine ρ (.const k) args

/-! ## `add x y ≐ 1` -/

/-- The frame `x y : num`. -/
abbrev addFrame : Context pkg := extend (extend (empty pkg) (numType _)) (numType _)

/-- `add x y`. -/
def addRow : TotalTerm addFrame :=
  ⟨numType _, ⟨addC (.var 1) (.var 0), add_typed level1 (Derivable.var (1 : Fin 2)) (Derivable.var (0 : Fin 2))⟩⟩

/-- `1`. -/
def oneRow : TotalTerm addFrame := ⟨numType _, ⟨one, D.succ_typed D.zero_typed⟩⟩

/-- **The store `add x y ≐ 1`.** -/
def addStore : EquationStore (TotalTerm addFrame) := [(addRow, oneRow)]

/-- `x`, as a term of the frame. -/
def xRow : TotalTerm addFrame := ⟨numType _, ⟨.var 1, Derivable.var (1 : Fin 2)⟩⟩

/-- The closed solution `x ↦ 0, y ↦ 1`. -/
def solution₀₁ : empty pkg ⟶ addFrame :=
  pair (pair (toEmpty (empty pkg)) ⟨zeroC, D.zero_typed⟩) ⟨one, D.succ_typed D.zero_typed⟩

/-- The closed solution `x ↦ 1, y ↦ 0`. -/
def solution₁₀ : empty pkg ⟶ addFrame :=
  pair (pair (toEmpty (empty pkg)) ⟨one, D.succ_typed D.zero_typed⟩) ⟨zeroC, D.zero_typed⟩

theorem addStore_solved₀₁ : (frames vecS.levels).Models solution₀₁ addStore := by
  intro e member
  obtain rfl := List.mem_singleton.mp member
  exact (equivalent_iff vecS.levels _ _).mpr ⟨⟨u, LevelTower.IsUniverse.sort _, .refl D.num_typed⟩,
    TowerVectors.add_zero (D.succ_typed D.zero_typed)⟩

theorem addStore_solved₁₀ : (frames vecS.levels).Models solution₁₀ addStore := by
  intro e member
  obtain rfl := List.mem_singleton.mp member
  have inner : Equal pkg .nil (addC zeroC zeroC) zeroC numC := TowerVectors.add_zero D.zero_typed
  have succConst : Typed pkg .nil (.const succ) (.pi numC numC) :=
    .const rfl (D.tower.pi_small D.num_typed D.num_typed) (D.tower.isUniverse _)
  exact (equivalent_iff vecS.levels _ _).mpr ⟨⟨u, LevelTower.IsUniverse.sort _, .refl D.num_typed⟩,
    .trans (TowerVectors.add_succ D.zero_typed D.zero_typed) (.appCong (.refl succConst) inner)⟩

/-- **The store is solvable.** -/
theorem addStore_solvable : (frames vecS.levels).Solvable addStore := ⟨empty pkg, solution₀₁, addStore_solved₀₁⟩

/-- Along a factorization of a closed solution, the answer's value of `x` meets the solution's. -/
theorem value_of_factor {Δ : Context pkg} {σ : Δ ⟶ addFrame} {τ : empty pkg ⟶ addFrame}
    {ρ : empty pkg ⟶ Δ}
    (agree : ∀ t : TotalTerm addFrame, (frames vecS.levels).E ((frames vecS.levels).act τ t)
      ((frames vecS.levels).act ((frames vecS.levels).comp ρ σ) t)) :
    Equal pkg .nil (τ.substitution 1) (subst ρ.substitution (σ.substitution 1)) numC :=
  ((equivalent_iff vecS.levels _ _).mp (agree xRow)).2

/-- **`add x y ≐ 1` has no principal answer.** -/
theorem addStore_no_principal {Δ : Context pkg} (σ : Δ ⟶ addFrame) :
    ¬ (frames vecS.levels).Principal addStore σ := by
  intro principal
  have formed : CtxFormed pkg Δ.raw := Δ.formed
  have solved : Equal pkg Δ.raw (addC (σ.substitution 1) (σ.substitution 0)) one numC :=
    ((equivalent_iff vecS.levels _ _).mp (principal.sound _ (List.mem_singleton_self _))).2
  obtain ⟨ρ₀₁, agree₀₁⟩ := principal.factors (empty pkg) solution₀₁ addStore_solved₀₁
  obtain ⟨ρ₁₀, agree₁₀⟩ := principal.factors (empty pkg) solution₁₀ addStore_solved₁₀
  have atZero : Equal pkg .nil zeroC (subst ρ₀₁.substitution (σ.substitution 1)) numC :=
    value_of_factor agree₀₁
  have atOne : Equal pkg .nil one (subst ρ₁₀.substitution (σ.substitution 1)) numC :=
    value_of_factor agree₁₀
  have typedX : Typed pkg Δ.raw (σ.substitution 1) numC := σ.typed 1
  obtain ⟨nf, toNf, shape⟩ := num_canonical formed typedX
  rcases shape with ⟨k, fields, args, mem, rfl⟩ | neutral
  · simp only [ctors, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at mem
    rcases mem with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- `x` is `zero`: along the second solution it must be `1`
      have moved : Equal pkg .nil (Presentation.subst ρ₁₀.substitution (σ.substitution 1))
          (Presentation.subst ρ₁₀.substitution (appSpine (.const zero) args)) numC :=
        toNf.substitutes ρ₁₀.typed
      have moved' : Equal pkg .nil (Presentation.subst ρ₁₀.substitution (σ.substitution 1))
          (appSpine (.const zero) (args.map (Presentation.subst ρ₁₀.substitution))) numC :=
        Eq.mp (congrArg (fun T : Tower.Tm 0 =>
          Equal pkg .nil (Presentation.subst ρ₁₀.substitution (σ.substitution 1)) T numC)
          (subst_ctorSpine ρ₁₀.substitution zero args)) moved
      exact num_ctor_apart .nil mem_succ mem_zero (by decide) (as := [zeroC]) (.trans atOne moved')
    · -- `x` is a successor: along the first solution it must be `0`
      have moved : Equal pkg .nil (Presentation.subst ρ₀₁.substitution (σ.substitution 1))
          (Presentation.subst ρ₀₁.substitution (appSpine (.const succ) args)) numC :=
        toNf.substitutes ρ₀₁.typed
      have moved' : Equal pkg .nil (Presentation.subst ρ₀₁.substitution (σ.substitution 1))
          (appSpine (.const succ) (args.map (Presentation.subst ρ₀₁.substitution))) numC :=
        Eq.mp (congrArg (fun T : Tower.Tm 0 =>
          Equal pkg .nil (Presentation.subst ρ₀₁.substitution (σ.substitution 1)) T numC)
          (subst_ctorSpine ρ₀₁.substitution succ args)) moved
      exact num_ctor_apart .nil mem_zero mem_succ (by decide) (as := []) (.trans atZero moved')
  · -- `x` is neutral: `add x y` is stuck, and stuck is not `1`
    have typedY : Typed pkg Δ.raw (σ.substitution 0) numC := σ.typed 0
    have addConst : Typed pkg Δ.raw (.const TowerVectorsModel.add) (.pi numC (.pi numC numC)) :=
      .const rfl (D.tower.pi_small D.num_typed (D.tower.pi_small D.num_typed D.num_typed))
        (D.tower.isUniverse _)
    have congruent : Equal pkg Δ.raw (addC (σ.substitution 1) (σ.substitution 0))
        (addC nf (σ.substitution 0)) numC :=
      .appCong (.appCong (.refl addConst) toNf) (.refl typedY)
    have stuck : Neutral TowerVectorsModel.roles (addC nf (σ.substitution 0)) :=
      Neutral.stuck_single (before := []) (after := [σ.substitution 0]) TowerVectorsModel.roles_add rfl neutral
    exact num_ctor_ne_neutral formed mem_succ (as := [zeroC]) stuck (.trans (.symm solved) congruent)

/-- **The package's settler postpones the store**: its family neither settles nor refutes it, by kernel
evaluation. -/
theorem addStore_postponed :
    (vecFamily 16 4 addStore).isSettled = false ∧ (vecFamily 16 4 addStore).isRefuted = false := by
  decide +kernel

end NativeTypesOnTheStep.Computing.Vectors

#print axioms NativeTypesOnTheStep.Computing.Vectors.num_canonical
#print axioms NativeTypesOnTheStep.Computing.Vectors.num_ctor_apart
#print axioms NativeTypesOnTheStep.Computing.Vectors.num_ctor_ne_neutral
#print axioms NativeTypesOnTheStep.Computing.Vectors.addStore_solved₀₁
#print axioms NativeTypesOnTheStep.Computing.Vectors.addStore_solved₁₀
#print axioms NativeTypesOnTheStep.Computing.Vectors.addStore_solvable
#print axioms NativeTypesOnTheStep.Computing.Vectors.addStore_no_principal
#print axioms NativeTypesOnTheStep.Computing.Vectors.addStore_postponed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
