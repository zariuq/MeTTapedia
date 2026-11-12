import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.RootDeterminism

/-!
# The declaration-time check, as one Boolean computation

How small can a declaration-time check be? Its syntactic part is one Boolean function of the table of
rows (`checkTable`): every left side is a defined constant at its arity applied to constructor patterns,
every left side is linear, every variable of a right side occurs on its left, and two left sides that
unify belong to the same row. When it answers `true`, the declared package is a constructor system
(`checkedConstructors`), so its conversion is Church–Rosser (`checked_churchRosser`) and its root steps
are deterministic (`checked_rootDeterministic`).

The rest of the check is not syntactic and is not part of this function: each right side must be typed
at the declared type after its match, and termination needs structural recursion on a constructor
argument (or a budget). Each part has its counterexample.

**Positive instances**: addition's two rows, and addition with append's two rows, pass
(`add_check`, `append_check`).

**Negative instances**: the overlapping rows `add 0 b ↦ b`, `add 0 b ↦ 0` fail (`overlap_check`); the
nested left side `add (add a b) c` fails (`nest_check`); a repeated pattern variable fails
(`nonlinear_check`); a right side with a variable not on the left fails (`uncovered_check`). The looping
row passes (`loop_check`): the syntactic check says nothing about termination.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.DeclarationCheck

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open AlgebraicSchema AlgebraicParallel ConversionCoherence
open ConstructorSystem (System LeftSide Pattern ConstructorPresentation unifiable)

/-! ## The check -/

section Check

variable {Head : Type} (isDefined : DeclName → Bool)

/-- Is the term an argument pattern (`true`) or the function part of a constructor spine (`false`)? -/
def isPattern : {m : Nat} → Bool → Tm Head m → Bool
  | _, true, .var _ => true
  | _, _, .const name => !isDefined name
  | _, _, .app function argument => isPattern false function && isPattern true argument
  | _, true, .refl term => isPattern true term
  | _, _, _ => false

/-- The head and the number of arguments of a left side: a defined constant applied to patterns. -/
def leftSide? : {m : Nat} → Tm Head m → Option (DeclName × Nat)
  | _, .const name => if isDefined name then some (name, 0) else none
  | _, .app function argument =>
      match leftSide? function with
      | some (name, count) => if isPattern isDefined true argument then some (name, count + 1) else none
      | none => none
  | _, _ => none

/-- Every variable occurs at most once. -/
def linearB {a : Nat} (t : Tm Head a) : Bool :=
  (List.finRange a).all fun i => decide (variableMultiplicity i t ≤ 1)

/-- Every variable of the right side occurs on the left. -/
def coveredB {a : Nat} (left right : Tm Head a) : Bool :=
  (List.finRange a).all fun i =>
    !decide (0 < variableMultiplicity i right) || decide (0 < variableMultiplicity i left)

variable (arityOf : DeclName → Nat)

/-- One row passes: a defined head at its arity over patterns, linear, covered. -/
def rowOK (row : Σ a : Nat, Tm Head a × Tm Head a) : Bool :=
  match leftSide? isDefined row.2.1 with
  | some (name, count) =>
      decide (count = arityOf name) && decide (0 < count) && linearB row.2.1 && coveredB row.2.1 row.2.2
  | none => false

/-- Two rows whose left sides unify are one row. -/
def disjointB [DecidableEq Head] (table : AlgebraicSchema.SchemaTable Head) : Bool :=
  table.all fun row => table.all fun row' => !unifiable row.2.1 row'.2.1 || decide (row = row')

/-- **The syntactic declaration-time check.** -/
def checkTable [DecidableEq Head] (table : AlgebraicSchema.SchemaTable Head) : Bool :=
  table.all (rowOK isDefined arityOf) && disjointB table

end Check

/-! ## Soundness -/

section Soundness

variable {Head : Type} {isDefined : DeclName → Bool}

theorem isPattern_sound {m : Nat} {flag : Bool} {t : Tm Head m} (h : isPattern isDefined flag t = true) :
    Pattern (fun name => isDefined name = true) flag t := by
  induction t generalizing flag with
  | var i =>
      cases flag with
      | true => exact .var i
      | false => simp [isPattern] at h
  | const name => exact .const (by simpa [isPattern] using h)
  | app f a ihf iha =>
      simp only [isPattern, Bool.and_eq_true] at h
      exact .app (ihf h.1) (iha h.2)
  | refl t ih =>
      cases flag with
      | true => exact .refl (ih (by simpa [isPattern] using h))
      | false => simp [isPattern] at h
  | _ => simp [isPattern] at h

theorem leftSide?_sound {m : Nat} {t : Tm Head m} {name : DeclName} {count : Nat}
    (h : leftSide? isDefined t = some (name, count)) :
    LeftSide (fun name => isDefined name = true) t name count ∧ isDefined name = true := by
  induction t generalizing name count with
  | const c =>
      cases hc : isDefined c with
      | false => simp [leftSide?, hc] at h
      | true =>
          simp only [leftSide?, hc, if_true, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨.const c, hc⟩
  | app f a ihf _ =>
      cases hf : leftSide? isDefined f with
      | none => simp [leftSide?, hf] at h
      | some p =>
          obtain ⟨name', count'⟩ := p
          cases ha : isPattern isDefined true a with
          | false => simp [leftSide?, hf, ha] at h
          | true =>
              simp only [leftSide?, hf, ha, if_true, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨side, defined⟩ := ihf hf
              exact ⟨.app side (isPattern_sound ha), defined⟩
  | _ => simp [leftSide?] at h

theorem linearB_sound {a : Nat} {t : Tm Head a} (h : linearB t = true) : LeftLinear t := fun i => by
  have row := List.all_eq_true.mp h i (List.mem_finRange i)
  simpa using row

theorem coveredB_sound {a : Nat} {left right : Tm Head a} (h : coveredB left right = true) :
    ∀ i, 0 < variableMultiplicity i right → 0 < variableMultiplicity i left := fun i occurs => by
  have row := List.all_eq_true.mp h i (List.mem_finRange i)
  by_contra absent
  have none : variableMultiplicity i left = 0 := by omega
  simp [none, occurs] at row

variable {arityOf : DeclName → Nat}

theorem rowOK_sound {row : Σ a : Nat, Tm Head a × Tm Head a} (h : rowOK isDefined arityOf row = true) :
    ∃ name, isDefined name = true ∧ 0 < arityOf name ∧
      LeftSide (fun name => isDefined name = true) row.2.1 name (arityOf name) ∧ LeftLinear row.2.1 ∧
      ∀ i, 0 < variableMultiplicity i row.2.2 → 0 < variableMultiplicity i row.2.1 := by
  cases hl : leftSide? isDefined row.2.1 with
  | none => simp [rowOK, hl] at h
  | some p =>
      obtain ⟨name, count⟩ := p
      simp only [rowOK, hl, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨same, positive⟩, linear⟩, covered⟩ := h
      obtain ⟨side, defined⟩ := leftSide?_sound hl
      subst same
      exact ⟨name, defined, positive, side, linearB_sound linear, coveredB_sound covered⟩

variable [DecidableEq Head] {table : AlgebraicSchema.SchemaTable Head}

theorem checkTable_split (ok : checkTable isDefined arityOf table = true) :
    table.all (rowOK isDefined arityOf) = true ∧ disjointB table = true := by
  simp only [checkTable, Bool.and_eq_true] at ok
  exact ok

theorem checkTable_rows (ok : checkTable isDefined arityOf table = true) {m : Nat} {left right : Tm Head m}
    (rule : table.family left right) :
    ∃ name, isDefined name = true ∧ 0 < arityOf name ∧
      LeftSide (fun name => isDefined name = true) left name (arityOf name) ∧ LeftLinear left ∧
      ∀ i, 0 < variableMultiplicity i right → 0 < variableMultiplicity i left :=
  rowOK_sound (row := ⟨m, (left, right)⟩)
    (List.all_eq_true.mp (checkTable_split ok).1 _ rule)

theorem checkTable_disjoint (ok : checkTable isDefined arityOf table = true) {m m' : Nat}
    {left right : Tm Head m} {left' right' : Tm Head m'} (rule : table.family left right)
    (rule' : table.family left' right') (unifies : unifiable left left' = true) :
    (⟨m, (left, right)⟩ : Σ arity : Nat, Tm Head arity × Tm Head arity) = ⟨m', (left', right')⟩ := by
  have pair := List.all_eq_true.mp (List.all_eq_true.mp (checkTable_split ok).2 _ rule) _ rule'
  rw [unifies] at pair
  simp only [Bool.not_true, Bool.false_or, decide_eq_true_eq] at pair
  exact pair

/-- **A table that passes the check is a constructor system.** -/
def checkedSystem (ok : checkTable isDefined arityOf table = true) : System Head where
  schema := table.family
  defined name := isDefined name = true
  arity := arityOf
  left := fun rule => by
    obtain ⟨name, defined, positive, side, -, -⟩ := checkTable_rows ok rule
    exact ⟨name, defined, positive, side⟩
  linear := fun rule => by
    obtain ⟨-, -, -, -, linear, -⟩ := checkTable_rows ok rule
    exact linear
  covered := fun rule => by
    obtain ⟨-, -, -, -, -, covered⟩ := checkTable_rows ok rule
    exact covered
  determined := ConstructorSystem.determined_of_disjoint
    (fun rule => by
      obtain ⟨name, -, -, side, -, -⟩ := checkTable_rows ok rule
      exact ⟨name, _, side⟩)
    (fun rule => by
      obtain ⟨-, -, -, -, -, covered⟩ := checkTable_rows ok rule
      exact covered)
    (fun rule rule' unifies => checkTable_disjoint ok rule rule' unifies)

omit [DecidableEq Head] in
/-- The declared package's root steps are the instances of the rows, when the package had none. -/
def checkedPresentation (R : Rules Head)
    (noComputation : ∀ {n : Nat} {l r : Tm Head n}, ¬ R.computation.step l r)
    (table : AlgebraicSchema.SchemaTable Head) :
    SchemaPresentation (declare R (SchemaFamily.computation table.family)) where
  schema := table.family
  sound := fun rule σ => Or.inr (SchemaStep.instantiate rule σ)
  cover := by
    intro n source target step
    rcases step with impossible | step
    · exact (noComputation impossible).elim
    · cases step with
      | instantiate rule σ => exact ⟨_, _, _, σ, rule, rfl, rfl⟩

/-- **The checked rows, as a definition by constructor patterns.** -/
def checkedConstructors (R : Rules Head)
    (noComputation : ∀ {n : Nat} {l r : Tm Head n}, ¬ R.computation.step l r)
    (symmetric : Std.Symm R.headEq) (ok : checkTable isDefined arityOf table = true) :
    ConstructorPresentation (declare R (SchemaFamily.computation table.family)) where
  presentation := checkedPresentation R noComputation table
  system := checkedSystem ok
  same _ _ := Iff.rfl
  symmetric := symmetric

/-- **The check gives Church–Rosser.** -/
theorem checked_churchRosser (R : Rules Head)
    (noComputation : ∀ {n : Nat} {l r : Tm Head n}, ¬ R.computation.step l r)
    (symmetric : Std.Symm R.headEq) (ok : checkTable isDefined arityOf table = true) :
    ChurchRosser (declare R (SchemaFamily.computation table.family)) :=
  (checkedConstructors R noComputation symmetric ok).churchRosser

/-- **... and root determinism.** -/
theorem checked_rootDeterministic (R : Rules Head)
    (noComputation : ∀ {n : Nat} {l r : Tm Head n}, ¬ R.computation.step l r)
    (symmetric : Std.Symm R.headEq) (ok : checkTable isDefined arityOf table = true) :
    RootDeterministic (SchemaFamily.computation table.family) :=
  RootDeterminism.rootDeterministic_of_presentation R _ (checkedConstructors R noComputation symmetric ok)

end Soundness

/-! ## Instances on the vector package -/

section Instances

open ProgrammingOnTheStep.VectorPackage

/-- Addition's two rows. -/
def addTable : AlgebraicSchema.SchemaTable Tower.Head :=
  [⟨1, (.app (.app (.const addN) (.const zeroN)) (.var 0), .var 0)⟩,
   ⟨2, (.app (.app (.const addN) (.app (.const succN) (.var 0))) (.var 1),
      .app (.const succN) (.app (.app (.const addN) (.var 0)) (.var 1)))⟩]

/-- Addition's and append's rows, the length argument of append inaccessible. -/
def appendTable : AlgebraicSchema.SchemaTable Tower.Head :=
  addTable ++
  [⟨3, (.app (.app (.app (.app (.const appendN) (.var 2)) (.var 1)) (.const nilN)) (.var 0), .var 0)⟩,
   ⟨6, (.app (.app (.app (.app (.const appendN) (.var 5)) (.var 4))
        (.app (.app (.app (.const consN) (.var 3)) (.var 2)) (.var 1))) (.var 0),
      .app (.app (.app (.const consN) (.app (.app (.const addN) (.var 3)) (.var 4))) (.var 2))
        (.app (.app (.app (.app (.const appendN) (.var 3)) (.var 4)) (.var 1)) (.var 0)))⟩]

def addDefined (name : DeclName) : Bool := name == addN
def appendDefined (name : DeclName) : Bool := name == addN || name == appendN
def appendArity (name : DeclName) : Nat := if name == appendN then 4 else 2

theorem add_check : checkTable addDefined (fun _ => 2) addTable = true := by decide

theorem append_check : checkTable appendDefined appendArity appendTable = true := by decide

theorem noComputation {n : Nat} {l r : Tower.Tm n} : ¬ rules.computation.step l r := fun step => step

theorem headSymm : Std.Symm rules.headEq :=
  ⟨fun _ _ same => Interface.DependentFull.Controls.setting.levels.headEq_symm same⟩

/-- **Addition, checked, is Church–Rosser.** -/
theorem add_checked_churchRosser :
    ChurchRosser (declare rules (SchemaFamily.computation addTable.family)) :=
  checked_churchRosser rules noComputation headSymm add_check

/-- **Addition and append, checked, are Church–Rosser.** -/
theorem append_checked_churchRosser :
    ChurchRosser (declare rules (SchemaFamily.computation appendTable.family)) :=
  checked_churchRosser rules noComputation headSymm append_check

/-- `add 0 b ↦ b` with `add 0 b ↦ 0`. -/
def overlapTable : AlgebraicSchema.SchemaTable Tower.Head :=
  [⟨1, (.app (.app (.const addN) (.const zeroN)) (.var 0), .var 0)⟩,
   ⟨1, (.app (.app (.const addN) (.const zeroN)) (.var 0), .const zeroN)⟩]

/-- `add 0 b ↦ b` with `add (add a b) c ↦ 0`. -/
def nestTable : AlgebraicSchema.SchemaTable Tower.Head :=
  [⟨1, (.app (.app (.const addN) (.const zeroN)) (.var 0), .var 0)⟩,
   ⟨3, (.app (.app (.const addN) (.app (.app (.const addN) (.var 2)) (.var 1))) (.var 0), .const zeroN)⟩]

/-- `add x x ↦ 0`: a repeated pattern variable. -/
def nonlinearTable : AlgebraicSchema.SchemaTable Tower.Head :=
  [⟨1, (.app (.app (.const addN) (.var 0)) (.var 0), .const zeroN)⟩]

/-- `add 0 x ↦ y`: a right-side variable not on the left. -/
def uncoveredTable : AlgebraicSchema.SchemaTable Tower.Head :=
  [⟨2, (.app (.app (.const addN) (.const zeroN)) (.var 0), .var 1)⟩]

/-- `lookup k v i ↦ succ (lookup k v i)`. -/
def loopTable : AlgebraicSchema.SchemaTable Tower.Head :=
  [⟨3, (.app (.app (.app (.const lookupN) (.var 2)) (.var 1)) (.var 0),
      .app (.const succN) (.app (.app (.app (.const lookupN) (.var 2)) (.var 1)) (.var 0)))⟩]

theorem overlap_check : checkTable addDefined (fun _ => 2) overlapTable = false := by decide

theorem nest_check : checkTable addDefined (fun _ => 2) nestTable = false := by decide

theorem nonlinear_check : checkTable addDefined (fun _ => 2) nonlinearTable = false := by decide

theorem uncovered_check : checkTable addDefined (fun _ => 2) uncoveredTable = false := by decide

/-- **The looping row passes the syntactic check**: termination is a separate part of the check. -/
theorem loop_check : checkTable (fun name => name == lookupN) (fun _ => 3) loopTable = true := by decide

end Instances

end NativeTypesOnTheStep.Computing.DeclarationCheck

#print axioms NativeTypesOnTheStep.Computing.DeclarationCheck.isPattern_sound
#print axioms NativeTypesOnTheStep.Computing.DeclarationCheck.leftSide?_sound
#print axioms NativeTypesOnTheStep.Computing.DeclarationCheck.linearB_sound
#print axioms NativeTypesOnTheStep.Computing.DeclarationCheck.coveredB_sound
#print axioms NativeTypesOnTheStep.Computing.DeclarationCheck.rowOK_sound
#print axioms NativeTypesOnTheStep.Computing.DeclarationCheck.checkTable_disjoint
#print axioms NativeTypesOnTheStep.Computing.DeclarationCheck.checkedSystem
#print axioms NativeTypesOnTheStep.Computing.DeclarationCheck.checkedConstructors
#print axioms NativeTypesOnTheStep.Computing.DeclarationCheck.checked_churchRosser
#print axioms NativeTypesOnTheStep.Computing.DeclarationCheck.checked_rootDeterministic
#print axioms NativeTypesOnTheStep.Computing.DeclarationCheck.add_check
#print axioms NativeTypesOnTheStep.Computing.DeclarationCheck.append_check
#print axioms NativeTypesOnTheStep.Computing.DeclarationCheck.add_checked_churchRosser
#print axioms NativeTypesOnTheStep.Computing.DeclarationCheck.append_checked_churchRosser
#print axioms NativeTypesOnTheStep.Computing.DeclarationCheck.overlap_check
#print axioms NativeTypesOnTheStep.Computing.DeclarationCheck.nest_check
#print axioms NativeTypesOnTheStep.Computing.DeclarationCheck.nonlinear_check
#print axioms NativeTypesOnTheStep.Computing.DeclarationCheck.uncovered_check
#print axioms NativeTypesOnTheStep.Computing.DeclarationCheck.loop_check

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
