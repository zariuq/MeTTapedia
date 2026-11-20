import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Definitions.Compile

/-!
# The checker of definitions as functions, and what its verdict guarantees

**The verdict** (`qualify fuel d`), in order:

1. **the rows**: the definition checker of the vectors package (`Vectors.Checker.checkDefinition`)
   admits every row (typed after its match), refuses a row, or does not decide;
2. **the class**: the definition compiles to the recursor (`compile`), over the function's own name
   when the rows do not cover (`baseOf`);
3. **the function's type**: the tree's executable checker certifies the compiled term at the declared
   type, in the base context (`typed?`, sound by `CheckingAlgorithm.sound`);
4. **the rows as conversions**: for every row, the compiled function applied to the row's patterns
   and the row's body at the compiled function reach one term by the package's executable reduction
   (`rowsConvert`); for every uncovered case, the call reaches the stuck call of the function's own
   name (`stuckConvert`).

Three outcomes, as for the rows: **a function** (closed when the rows cover), **refused** at a row
(by the row checker's proved refusal), **not decided** with its reason (the rows not decided, outside
the class, or a certificate not found within the budget). A budget that runs out is never a refusal.

**The guarantee** (`qualify_function`), for every definition whose verdict is a function: its rows
are admitted by the row checker; its compiled term is typed at its declared type (item 1); every row
holds as a conversion of the package at every instance of its pattern (item 2); every uncovered case
converts to the stuck call (the partial case of item 3 of the whole-function guarantee). **Nothing is
added to the package**: the function is a term of `TowerVectorsModel.rules`, whose qualification
(`vectors_qualified`) is unchanged, so conversion stays Church–Rosser, type-preserving and decided,
and no judgment about old terms changes (`function_package_laws`).

**What is not claimed.** The typing of the compiled term is certified by the tree's checker run on the
compiled term, not derived from the row checker's certificate: that bridge needs call abstraction for
the declarative typing with the function a variable (the tree has it for the algorithmic checking with
the function a constant, `bodyTyped_of_check`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Definitions

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ConversionCoherence (StepStar)
open TowerVectorsModel (numC zeroC succC ttC)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (level1 pkg)
open Vectors (vecReducer vecNormalize vecNormalize_sound vecS vecChoices vecDeclared)
open Vectors.Checker (Pattern Row Definition formed? level?)

/-! ## The function's type -/

/-- The base context: `b` copies of the declared type; the oldest is the function's own name. -/
def baseCtx (d : Definition) : (b : Nat) → Ctx Tower.Head b
  | 0 => .nil
  | b + 1 => .snoc (baseCtx d b) (liftClosed d.type)

/-- **A typing certified by the tree's executable checker**, within a budget: the context formed, the
type at a universe, and the term checked against the type. -/
def typed? (fuel : Nat) {b : Nat} (Γ : Ctx Tower.Head b) (t T : Tower.Tm b) :
    Option (PLift (Typed pkg Γ t T)) :=
  (formed? fuel Γ).bind fun formed =>
    (level? fuel ⟨b, Γ, formed.down⟩ T).bind fun l =>
      (ExecutableChecking.check vecS.R vecChoices (vecReducer level1) fuel Γ t T).bind fun ch =>
        some ⟨CheckingAlgorithm.sound (S := vecS) (TowerVectorsModel.facts level1)
          (TowerVectorsModel.roots level1) (TowerVectorsModel.heads level1)
          (TowerVectorsModel.algebra level1) (vecDeclared level1) ch.down formed.down
          ⟨l.val, l.property.1, l.property.2⟩⟩

/-- **What the certificate says.** -/
theorem typed?_sound {fuel b : Nat} {Γ : Ctx Tower.Head b} {t T : Tower.Tm b}
    (found : (typed? fuel Γ t T).isSome = true) : Typed pkg Γ t T := by
  obtain ⟨p, _⟩ := Option.isSome_iff_exists.mp found
  exact p.down

/-! ## The rows as conversions -/

/-- The base variables, below the row's variables. -/
def shiftBase (b vars : Nat) : Ren b (b + vars) := fun y => ⟨y.val + vars, by omega⟩

/-- The row variable at left-to-right position `ℓ`, over the base. -/
def patVar (b vars ℓ : Nat) : Option (Tower.Tm (b + vars)) :=
  if ℓ < vars then varAt (b + vars) (vars - 1 - ℓ) else none

/-- What the call index stands for in a row: `zero`, or `succ k`. -/
def indexImage (b vars : Nat) (case : Bool) (slots : List Slot) : Option (Tower.Tm (b + vars)) :=
  if case then (slots.idxOf? .pred).bind fun ℓ => (patVar b vars ℓ).map succC else some zeroC

/-- One argument of a row's left side. -/
def argStep (b vars : Nat) (slots : List Slot) (idx : Option (Tower.Tm (b + vars)))
    (acc : Nat × List (Tower.Tm (b + vars))) (p : Pattern) : Option (Nat × List (Tower.Tm (b + vars))) :=
  match p with
  | .var =>
      if slots[acc.1]? = some .index then idx.map fun t => (acc.1 + 1, acc.2 ++ [t])
      else (patVar b vars acc.1).map fun t => (acc.1 + 1, acc.2 ++ [t])
  | .zero => some (acc.1, acc.2 ++ [zeroC])
  | .succ .var => (patVar b vars acc.1).map fun t => (acc.1 + 1, acc.2 ++ [succC t])
  | .nil => some (acc.1, acc.2 ++ [ttC])
  | .cons .var .var => do
      let a ← patVar b vars (acc.1 + 1)
      let v ← patVar b vars (acc.1 + 2)
      pure (acc.1 + 3, acc.2 ++ [.pair a v])
  | _ => none

/-- **The arguments of a left side**: the patterns as terms over the base and the pattern variables. -/
def lhsArgs (b vars : Nat) (patterns : List Pattern) (slots : List Slot) (case : Bool) :
    Option (List (Tower.Tm (b + vars))) :=
  (patterns.foldlM (argStep b vars slots (indexImage b vars case slots)) (0, [])).map (·.2)

/-- **A row's left side**: the compiled function applied to the row's patterns. -/
def lhs (b : Nat) (c : Tower.Tm b) (r : Row) (slots : List Slot) (case : Bool) :
    Option (Tower.Tm (b + r.vars)) :=
  (lhsArgs b r.vars r.patterns slots case).map (spine (rename (shiftBase b r.vars) c))

/-- The row's variables at the left side's instance: the call index at its constructor, the function
at the compiled function. -/
def rowSub (b : Nat) (c : Tower.Tm b) (r : Row) (slots : List Slot) (case : Bool) :
    Sub Tower.Head (r.vars + 1) (b + r.vars) := fun x =>
  if h : x.val < r.vars then
    if slots[r.vars - 1 - x.val]? = some .index then (indexImage b r.vars case slots).getD zeroC
    else .var ⟨x.val, by omega⟩
  else rename (shiftBase b r.vars) c

/-- **A row's right side**: its body at the compiled function. -/
def rhs (b : Nat) (c : Tower.Tm b) (r : Row) (slots : List Slot) (case : Bool) : Tower.Tm (b + r.vars) :=
  subst (rowSub b c r slots case) r.body

/-- Both terms reach one term by the package's executable reduction. -/
def joins (fuel : Nat) {n : Nat} (t u : Tower.Tm n) : Bool :=
  match vecNormalize level1 fuel t, vecNormalize level1 fuel u with
  | some v, some w => v == w
  | _, _ => false

/-- **Two terms that join are convertible.** -/
theorem joins_conv {fuel n : Nat} {t u : Tower.Tm n} (ok : joins fuel t u = true) :
    Conv pkg.headEq t u pkg.computation := by
  unfold joins at ok
  split at ok
  · rename_i v w hv hw
    have same : v = w := by simpa using ok
    subst same
    exact .trans _ _ _ (conv_of_stepStar (vecNormalize_sound level1 hv))
      (.symm _ _ (conv_of_stepStar (vecNormalize_sound level1 hw)))
  · cases ok

/-- **A row converts.** -/
def rowConverts (fuel b : Nat) (c : Tower.Tm b) (r : Row) (slots : List Slot) (case : Bool) : Bool :=
  match lhs b c r slots case with
  | none => false
  | some l => joins fuel l (rhs b c r slots case)

/-- **Every row converts.** -/
def rowsConvert (fuel b : Nat) (d : Definition) (c : Tower.Tm b) : Bool :=
  match shapesOf d with
  | some shapes => shapes.all fun s => rowConverts fuel b c s.1 s.2.2 s.2.1
  | none => false

/-- **A converting row holds at every instance of its pattern.** -/
theorem rowConverts_holds {fuel b : Nat} {c : Tower.Tm b} {r : Row} {slots : List Slot} {case : Bool}
    (ok : rowConverts fuel b c r slots case = true) :
    ∃ l, lhs b c r slots case = some l ∧ ∀ {m : Nat} (σ : Sub Tower.Head (b + r.vars) m),
      Conv pkg.headEq (subst σ l) (subst σ (rhs b c r slots case)) pkg.computation := by
  unfold rowConverts at ok
  split at ok
  · cases ok
  · rename_i l hl
    exact ⟨l, hl, fun σ => Conv.substitute σ (joins_conv ok)⟩

/-! ## Uncovered cases -/

/-- The patterns of a case: variables, with the case's constructor at the call index. -/
def casePatterns (arity j : Nat) (kind : Kind) (case : Bool) : List Pattern :=
  (List.range arity).map fun i =>
    if i = j then
      match kind with
      | .number => if case then .succ .var else .zero
      | .vector _ => .var
    else
      match kind with
      | .vector v => if i = v then (if case then .cons .var .var else .nil) else .var
      | .number => .var

/-- The number of pattern variables of a case. -/
def caseVars (arity j : Nat) (kind : Kind) (case : Bool) : Nat :=
  ((casePatterns arity j kind case).map Pattern.vars).sum

/-- The slots of a case, as for a row. -/
def caseSlots (arity j : Nat) (kind : Kind) (case : Bool) : Option (List Slot) :=
  match ((List.range arity).zip (casePatterns arity j kind case)).foldlM (slotStep j kind) (none, []) with
  | some (_, slots) => some slots
  | none => none

/-- The function's own name, over the base and the case's variables. -/
def baseName (b vars : Nat) : Option (Tower.Tm (b + vars)) :=
  if 0 < b then varAt (b + vars) (vars + b - 1) else none

/-- **An uncovered case converts to the stuck call**: the compiled function and its own name, applied
to the case's patterns, reach one term. -/
def stuckConverts (fuel b : Nat) (c : Tower.Tm b) (arity j : Nat) (kind : Kind) (case : Bool) : Bool :=
  match caseSlots arity j kind case with
  | none => false
  | some slots =>
      match lhsArgs b (caseVars arity j kind case) (casePatterns arity j kind case) slots case,
          baseName b (caseVars arity j kind case) with
      | some args, some f => joins fuel (spine (rename (shiftBase b _) c) args) (spine f args)
      | _, _ => false

/-- The cases without a row. -/
def uncovered (d : Definition) : List Bool :=
  match shapesOf d with
  | some shapes => [false, true].filter fun case => !(shapes.any fun s => s.2.1 == case)
  | none => []

/-- **Every uncovered case converts to the stuck call.** -/
def stuckConvert (fuel b : Nat) (d : Definition) (c : Tower.Tm b) : Bool :=
  match scrutinee d with
  | some (j, kind) => (uncovered d).all fun case => stuckConverts fuel b c d.arity j kind case
  | none => true

/-- **An uncovered case holds as the stuck call**, at every instance. -/
theorem stuckConverts_holds {fuel b : Nat} {c : Tower.Tm b} {arity j : Nat} {kind : Kind} {case : Bool}
    (ok : stuckConverts fuel b c arity j kind case = true) :
    ∃ slots args f, caseSlots arity j kind case = some slots ∧
      lhsArgs b (caseVars arity j kind case) (casePatterns arity j kind case) slots case = some args ∧
      baseName b (caseVars arity j kind case) = some f ∧
      ∀ {m : Nat} (σ : Sub Tower.Head (b + caseVars arity j kind case) m),
        Conv pkg.headEq (subst σ (spine (rename (shiftBase b _) c) args)) (subst σ (spine f args))
          pkg.computation := by
  unfold stuckConverts at ok
  split at ok
  · cases ok
  · rename_i slots hslots
    split at ok
    · rename_i args f hargs hf
      exact ⟨slots, args, f, hslots, hargs, hf, fun σ => Conv.substitute σ (joins_conv ok)⟩
    · cases ok

/-! ## The verdict -/

/-- Why a definition is not decided. -/
inductive Reason where
  | rows
  | outside
  | typing
  | conversion
  deriving DecidableEq, Repr

/-- **The verdict on a definition as a function.** -/
inductive Verdict where
  | function (closed : Bool)
  | refused (row : Nat)
  | undecided (reason : Reason)
  deriving DecidableEq, Repr

/-- **The checker of definitions as functions.** -/
def qualify (fuel : Nat) (d : Definition) : Verdict :=
  match Vectors.Checker.checkDefinition fuel d with
  | .refused i => .refused i
  | .undecided => .undecided .rows
  | .admitted =>
      match compile (baseOf d) d with
      | none => .undecided .outside
      | some c =>
          if (typed? fuel (baseCtx d (baseOf d)) c (liftClosed d.type)).isSome then
            if rowsConvert fuel (baseOf d) d c && stuckConvert fuel (baseOf d) d c then
              .function (covers d)
            else .undecided .conversion
          else .undecided .typing

/-! ## What the verdict guarantees -/

/-- **A refusal is the row checker's**: the refused row is refused by the converting step for every
settler. -/
theorem qualify_refused {fuel : Nat} {d : Definition} {i : Nat} (verdict : qualify fuel d = .refused i) :
    Vectors.Checker.checkDefinition fuel d = .refused i := by
  unfold qualify at verdict
  split at verdict
  · rename_i j h
    cases verdict
    exact h
  · cases verdict
  · split at verdict
    · cases verdict
    · split at verdict
      · split at verdict <;> cases verdict
      · cases verdict

/-- **A function, checked component by component**: the row checker's admission, the compilation, the
certified typing, the rows' conversions and the uncovered cases' conversions, each a kernel-evaluated
check with its own budget. A function verdict gives one (`qualify_checked`); a definition too large for
one evaluation is checked this way, one component per evaluation. -/
structure Checked (d : Definition) (b : Nat) (c : Tower.Tm b) : Prop where
  base : b = baseOf d
  rows : ∃ fuel, Vectors.Checker.checkDefinition fuel d = .admitted
  compiled : compile b d = some c
  typed : ∃ fuel, (typed? fuel (baseCtx d b) c (liftClosed d.type)).isSome = true
  converts : ∃ fuel, rowsConvert fuel b d c = true
  stuck : ∃ fuel, stuckConvert fuel b d c = true

/-- **A function verdict is a checked function**, closed exactly when the rows cover. -/
theorem qualify_checked {fuel : Nat} {d : Definition} {closed : Bool}
    (verdict : qualify fuel d = .function closed) : closed = covers d ∧ ∃ c, Checked d (baseOf d) c := by
  unfold qualify at verdict
  split at verdict
  · cases verdict
  · cases verdict
  · rename_i admitted
    split at verdict
    · cases verdict
    · rename_i c compiled
      split at verdict
      · rename_i typedOk
        split at verdict
        · rename_i convertOk
          cases verdict
          obtain ⟨rowsOk, stuckOk⟩ := Bool.and_eq_true_iff.mp convertOk
          exact ⟨rfl, c, ⟨rfl, ⟨fuel, admitted⟩, compiled, ⟨fuel, typedOk⟩, ⟨fuel, rowsOk⟩, ⟨fuel, stuckOk⟩⟩⟩
        · cases verdict
      · cases verdict

/-- **A closed function verdict is a closed checked function.** -/
theorem qualify_closed {fuel : Nat} {d : Definition} (verdict : qualify fuel d = .function true) :
    ∃ c : Tower.Tm 0, Checked d 0 c := by
  obtain ⟨same, c, checked⟩ := qualify_checked verdict
  have zero : baseOf d = 0 := by
    unfold baseOf
    rw [← same]
    rfl
  revert c
  rw [zero]
  exact fun c checked => ⟨c, checked⟩

/-- **An open function verdict is a checked function over the function's own name.** -/
theorem qualify_open {fuel : Nat} {d : Definition} (verdict : qualify fuel d = .function false) :
    ∃ c : Tower.Tm 1, Checked d 1 c := by
  obtain ⟨same, c, checked⟩ := qualify_checked verdict
  have one : baseOf d = 1 := by
    unfold baseOf
    rw [← same]
    rfl
  revert c
  rw [one]
  exact fun c checked => ⟨c, checked⟩

/-- **What a checked function guarantees, for every definition**:
* the compiled term, over the base (nothing when the rows cover, the function's own name otherwise),
  is typed at the declared type (**item 1**);
* every row of the definition holds as a conversion of the package at every instance of its pattern:
  the compiled function applied to the row's patterns converts to the row's body at the compiled
  function (**item 2**);
* every uncovered case converts, at every instance, to the stuck call of the function's own name. -/
theorem Checked.guarantee {d : Definition} {b : Nat} {c : Tower.Tm b} (checked : Checked d b c) :
    Typed pkg (baseCtx d b) c (liftClosed d.type) ∧
      (∃ shapes, shapesOf d = some shapes ∧ shapes.map (·.1) = d.rows ∧
        ∀ s ∈ shapes, ∃ l, lhs b c s.1 s.2.2 s.2.1 = some l ∧
          ∀ {m : Nat} (σ : Sub Tower.Head (b + s.1.vars) m),
            Conv pkg.headEq (subst σ l) (subst σ (rhs b c s.1 s.2.2 s.2.1)) pkg.computation) ∧
      ∀ j kind, scrutinee d = some (j, kind) → ∀ case ∈ uncovered d,
        ∃ fuel, stuckConverts fuel b c d.arity j kind case = true := by
  obtain ⟨-, -, -, ⟨_, typedOk⟩, ⟨_, rowsOk⟩, ⟨fuel, stuckOk⟩⟩ := checked
  refine ⟨typed?_sound typedOk, ?_, ?_⟩
  · unfold rowsConvert at rowsOk
    split at rowsOk
    · rename_i shapes found
      refine ⟨shapes, found, shapesOf_rows found, fun s member => ?_⟩
      exact rowConverts_holds (List.all_eq_true.mp rowsOk s member)
    · cases rowsOk
  · intro j kind hs case member
    unfold stuckConvert at stuckOk
    rw [hs] at stuckOk
    exact ⟨fuel, List.all_eq_true.mp stuckOk case member⟩

/-- **What a function verdict gives, for every definition**: the row checker admits every row (each
typed after its match, `checkDefinition_admitted`), the verdict says `closed` exactly when the rows
cover, and the compiled function has the guarantee of a checked function (items 1 and 2, and the
uncovered cases). -/
theorem qualify_function {fuel : Nat} {d : Definition} {closed : Bool}
    (verdict : qualify fuel d = .function closed) :
    Vectors.Checker.checkDefinition fuel d = .admitted ∧ closed = covers d ∧
      ∃ c, compile (baseOf d) d = some c ∧ Checked d (baseOf d) c := by
  have admitted : Vectors.Checker.checkDefinition fuel d = .admitted := by
    unfold qualify at verdict
    split at verdict
    · cases verdict
    · cases verdict
    · assumption
  obtain ⟨same, c, checked⟩ := qualify_checked verdict
  exact ⟨admitted, same, c, checked.compiled, checked⟩

/-- **Nothing is added to the package.** The compiled function is a term of the vectors package, whose
qualification is unchanged: conversion is Church–Rosser, every reduction preserves typing, and the
typed equality of two terms of a type is decided, for terms that mention the function as for every
other term. -/
theorem function_package_laws (valuation : Nat → Nat) :
    Qualified (TowerVectorsModel.setting level1 valuation) :=
  Vectors.vectors_qualified level1 valuation

/-- **Calls of the function answer at most once, at their type**: for a call typed at a type, every
answer by the package's computation has that type and is the only one. -/
theorem call_answers {n : Nat} {Γ : Ctx Tower.Head n} (formed : CtxFormed pkg Γ) {t v A : Tower.Tm n}
    (typing : Typed pkg Γ t A) (answer : Answer pkg t v) :
    Typed pkg Γ v A ∧ Equal pkg Γ t v A ∧ ∀ v', Answer pkg t v' → v' = v :=
  ⟨(Vectors.vectors_answer_typed level1 formed typing answer).1,
    (Vectors.vectors_answer_typed level1 formed typing answer).2,
    fun _ other => Vectors.vectors_answer_unique level1 other answer⟩

/-- **A row's conversion is a typed equality** where both sides are typed at one type. -/
theorem row_equal {n : Nat} {Γ : Ctx Tower.Head n} (formed : CtxFormed pkg Γ) {l r T : Tower.Tm n}
    (conversion : Conv pkg.headEq l r pkg.computation) (typedL : Typed pkg Γ l T) (typedR : Typed pkg Γ r T) :
    Equal pkg Γ l r T :=
  Vectors.vectors_conv_toEqual level1 formed conversion typedL typedR

end NativeTypesOnTheStep.Computing.Definitions

#print axioms NativeTypesOnTheStep.Computing.Definitions.typed?_sound
#print axioms NativeTypesOnTheStep.Computing.Definitions.joins_conv
#print axioms NativeTypesOnTheStep.Computing.Definitions.rowConverts_holds
#print axioms NativeTypesOnTheStep.Computing.Definitions.stuckConverts_holds
#print axioms NativeTypesOnTheStep.Computing.Definitions.qualify_refused
#print axioms NativeTypesOnTheStep.Computing.Definitions.qualify_checked
#print axioms NativeTypesOnTheStep.Computing.Definitions.qualify_closed
#print axioms NativeTypesOnTheStep.Computing.Definitions.qualify_open
#print axioms NativeTypesOnTheStep.Computing.Definitions.Checked.guarantee
#print axioms NativeTypesOnTheStep.Computing.Definitions.qualify_function
#print axioms NativeTypesOnTheStep.Computing.Definitions.function_package_laws
#print axioms NativeTypesOnTheStep.Computing.Definitions.call_answers
#print axioms NativeTypesOnTheStep.Computing.Definitions.row_equal

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
