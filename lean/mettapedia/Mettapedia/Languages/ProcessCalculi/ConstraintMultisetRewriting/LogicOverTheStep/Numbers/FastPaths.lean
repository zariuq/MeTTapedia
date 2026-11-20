import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.OnTheStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.GroundedTables

/-!
# Fast paths that read storage, and their licence

A **fast path** for a binary operation on stored numbers (`FastPath`) is a region of the arguments,
decided by a Boolean test, and a fast function consulted only there. It may read storage: the 64-bit
paths below answer only on two stored integers.

**The licence** (`Licensed`): wherever the path answers, it answers what the value operation
answers. Where it cannot answer it hands over, to the exact operation computed from the values
(`Tower.lift`); it neither errs nor answers otherwise.

* **The composite equals the value operation** (`withFasts_value`): fast where a licensed region
  holds, exact otherwise, for any list of licensed paths tried in order. So it respects the value
  lens (`withFasts_respects`), whatever the paths read.
* **Regions compose in any order** (`withFasts_any`): two lists of licensed paths, in any order and
  of any length, give answers of one value. **Adding a region changes no answer exactly when its
  path is licensed** (`adding_iff_licensed`).
* **The 64-bit paths** for addition, subtraction and multiplication (`int64`: both arguments stored
  as integers and the exact result `Fits`) are licensed (`add64_licensed`, `sub64_licensed`,
  `mul64_licensed`).
* **HE's measured integer table is the fast path with an error outside the region**
  (`measured_add`): on two integers whose sum fits, HE's outcome is the sum, and the tree's model of
  HE's table agrees (`GroundedTables.measured_agrees`, used unchanged); outside, HE's outcome is the
  runtime error `IntegerOverflow`, while the model's table, which has no width, answers the sum: it
  is the licensed composite.

**Controls**, each on a stated pair of storages of one value (a model of measured behaviour, checked
against the measured rows `(* 4611686018427387904 2)`, an `IntegerOverflow` error, and
`(* 4611686018427387904.0 2)`, a number):

* **answering an error outside the region** (`checkedMul`) does not respect the value lens
  (`checkedMul_not_respects`): the stored integer `4611686018427387904` times `2` errs, the
  fraction of the same value times `2` answers;
* **wrapping** (`wrapMul`) does not respect it (`wrapMul_not_respects`): the same pair gives
  `-9223372036854775808` and `9223372036854775808`;
* the licensed composite gives one value on that pair (`mul64_composite_pair`).

**On the step**: a grounded table built from licensed fast paths (`fastTable`) respects the value
lens (`fastTable_respects`), so re-storing every numeral changes no answer of the step for it
(`fastTable_answers`, an instance of `OnTheStep.answer_restore`).

No claim about speed is made here: no work is counted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.FastPaths

open Distinctions.ObserverConcepts Distinctions.NumberLens Tower
open DialectsAsStrategies.TriangleFootprints.GroundedTables
  (Fits measuredOutcome heOutcome measured_agrees he_int_op IntOp intValue checkedResult)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE (Bindings GroundedResult)

/-! ## Fast paths and the licence -/

/-- **A fast path**: a region of the arguments, decided by a Boolean test, and a fast function
consulted only there. -/
structure FastPath where
  /-- The region. -/
  region : Stored → Stored → Bool
  /-- The fast function. -/
  fast : Stored → Stored → Stored

/-- **The licence**: wherever the path answers, it answers what the value operation answers. -/
def Licensed (f : ℚ → ℚ → ℚ) (p : FastPath) : Prop :=
  ∀ a b, p.region a b = true → value (p.fast a b) = f (value a) (value b)

/-- **Fast where licensed, exact otherwise**: the paths are tried in order; where none answers, the
exact operation computed from the values answers. -/
def withFasts (f : ℚ → ℚ → ℚ) : List FastPath → Stored → Stored → Stored
  | [], a, b => lift f (a, b)
  | p :: ps, a, b => if p.region a b then p.fast a b else withFasts f ps a b

/-- **The composite equals the value operation.** -/
theorem withFasts_value {f : ℚ → ℚ → ℚ} {ps : List FastPath} (licensed : ∀ p ∈ ps, Licensed f p)
    (a b : Stored) : value (withFasts f ps a b) = f (value a) (value b) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
      unfold withFasts
      split_ifs with inside
      · exact licensed p (List.mem_cons.mpr (Or.inl rfl)) a b inside
      · exact ih (fun q member => licensed q (List.mem_cons.mpr (Or.inr member)))

/-- **So it respects the value lens**, whatever the paths read. -/
theorem withFasts_respects {f : ℚ → ℚ → ℚ} {ps : List FastPath}
    (licensed : ∀ p ∈ ps, Licensed f p) :
    Respects (pairRead valueLens valueLens) valueLens (fun x : Stored × Stored => withFasts f ps x.1 x.2) := by
  rw [respects_pair_iff]
  intro a a' b b' first second _
  show value (withFasts f ps a b) = value (withFasts f ps a' b')
  rw [withFasts_value licensed, withFasts_value licensed, show value a = value a' from first (),
    show value b = value b' from second ()]

/-- **Regions compose in any order**: two lists of licensed paths give answers of one value. -/
theorem withFasts_any {f : ℚ → ℚ → ℚ} {ps qs : List FastPath} (licensedP : ∀ p ∈ ps, Licensed f p)
    (licensedQ : ∀ q ∈ qs, Licensed f q) (a b : Stored) :
    value (withFasts f ps a b) = value (withFasts f qs a b) := by
  rw [withFasts_value licensedP, withFasts_value licensedQ]

/-- **Adding a region changes no answer exactly when its path is licensed.** -/
theorem adding_iff_licensed {f : ℚ → ℚ → ℚ} (p : FastPath) {ps : List FastPath}
    (licensed : ∀ q ∈ ps, Licensed f q) :
    (∀ a b, value (withFasts f (p :: ps) a b) = value (withFasts f ps a b)) ↔ Licensed f p := by
  constructor
  · intro same a b inside
    have added := same a b
    rw [withFasts_value licensed] at added
    unfold withFasts at added
    rw [if_pos inside] at added
    exact added
  · intro licensedP a b
    rw [withFasts_value (ps := p :: ps) (fun q member => by
      rcases List.mem_cons.mp member with rfl | inside
      · exact licensedP
      · exact licensed q inside), withFasts_value licensed]

/-! ## The 64-bit paths -/

/-- **The 64-bit path** of an integer operation: both arguments stored as integers and the exact
result fits in 64 bits; there the answer is the integer result. -/
def int64 (g : ℤ → ℤ → ℤ) : FastPath where
  region a b := match a, b with
    | .int m, .int n => decide (Fits (g m n))
    | _, _ => false
  fast a b := match a, b with
    | .int m, .int n => .int (g m n)
    | a, _ => a

theorem int64_licensed (g : ℤ → ℤ → ℤ) (f : ℚ → ℚ → ℚ)
    (commutes : ∀ m n : ℤ, ((g m n : ℤ) : ℚ) = f m n) : Licensed f (int64 g) := by
  intro a b inside
  cases a with
  | int m =>
      cases b with
      | int n => exact commutes m n
      | frac q => exact (Bool.false_ne_true inside).elim
  | frac p => exact (Bool.false_ne_true inside).elim

/-- 64-bit addition. -/
def add64 : FastPath := int64 (· + ·)

/-- 64-bit subtraction. -/
def sub64 : FastPath := int64 (· - ·)

/-- 64-bit multiplication. -/
def mul64 : FastPath := int64 (· * ·)

theorem add64_licensed : Licensed (· + ·) add64 := int64_licensed _ _ fun m n => Int.cast_add m n

theorem sub64_licensed : Licensed (· - ·) sub64 := int64_licensed _ _ fun m n => Int.cast_sub m n

theorem mul64_licensed : Licensed (· * ·) mul64 := int64_licensed _ _ fun m n => Int.cast_mul m n

/-! ## HE's measured table as a path -/

/-- **HE's measured `+` is the fast path with an error outside its region**, and the model's table is
the licensed composite. On two integers whose sum fits, HE's measured outcome is the sum and equals
the model's (`measured_agrees`); outside, HE's is the runtime error `IntegerOverflow`, the model's
the sum. -/
theorem measured_add (m n : ℤ) :
    (Fits (m + n) →
        measuredOutcome (.symbol "+") [.grounded (.int m), .grounded (.int n)] =
          .ok [(.grounded (.int (m + n)), Bindings.empty)] ∧
        measuredOutcome (.symbol "+") [.grounded (.int m), .grounded (.int n)] =
          heOutcome (.symbol "+") [.grounded (.int m), .grounded (.int n)]) ∧
      (¬ Fits (m + n) →
        measuredOutcome (.symbol "+") [.grounded (.int m), .grounded (.int n)] =
          .runtimeError "IntegerOverflow") ∧
      heOutcome (.symbol "+") [.grounded (.int m), .grounded (.int n)] =
        .ok [(.grounded (.int (m + n)), Bindings.empty)] := by
  refine ⟨fun fits => ⟨?_, measured_agrees IntOp.plus m n fun k same => ?_⟩, fun notFits => ?_, ?_⟩
  · simp [measuredOutcome, checkedResult, fits]
  · have equal : m + n = k := by
      have reduced : Atom.grounded (GroundedValue.int (m + n)) = Atom.grounded (GroundedValue.int k) :=
        same
      injection reduced with inner
      injection inner
    rw [← equal]
    exact fits
  · simp [measuredOutcome, checkedResult, notFits]
  · rw [heOutcome, he_int_op IntOp.plus m n]
    rfl

/-- **The same for `-`.** -/
theorem measured_sub (m n : ℤ) :
    (Fits (m - n) →
        measuredOutcome (.symbol "-") [.grounded (.int m), .grounded (.int n)] =
          .ok [(.grounded (.int (m - n)), Bindings.empty)] ∧
        measuredOutcome (.symbol "-") [.grounded (.int m), .grounded (.int n)] =
          heOutcome (.symbol "-") [.grounded (.int m), .grounded (.int n)]) ∧
      (¬ Fits (m - n) →
        measuredOutcome (.symbol "-") [.grounded (.int m), .grounded (.int n)] =
          .runtimeError "IntegerOverflow") ∧
      heOutcome (.symbol "-") [.grounded (.int m), .grounded (.int n)] =
        .ok [(.grounded (.int (m - n)), Bindings.empty)] := by
  refine ⟨fun fits => ⟨?_, measured_agrees IntOp.minus m n fun k same => ?_⟩, fun notFits => ?_, ?_⟩
  · simp [measuredOutcome, checkedResult, fits]
  · have equal : m - n = k := by
      have reduced : Atom.grounded (GroundedValue.int (m - n)) = Atom.grounded (GroundedValue.int k) :=
        same
      injection reduced with inner
      injection inner
    rw [← equal]
    exact fits
  · simp [measuredOutcome, checkedResult, notFits]
  · rw [heOutcome, he_int_op IntOp.minus m n]
    rfl

/-- **The same for `*`.** -/
theorem measured_mul (m n : ℤ) :
    (Fits (m * n) →
        measuredOutcome (.symbol "*") [.grounded (.int m), .grounded (.int n)] =
          .ok [(.grounded (.int (m * n)), Bindings.empty)] ∧
        measuredOutcome (.symbol "*") [.grounded (.int m), .grounded (.int n)] =
          heOutcome (.symbol "*") [.grounded (.int m), .grounded (.int n)]) ∧
      (¬ Fits (m * n) →
        measuredOutcome (.symbol "*") [.grounded (.int m), .grounded (.int n)] =
          .runtimeError "IntegerOverflow") ∧
      heOutcome (.symbol "*") [.grounded (.int m), .grounded (.int n)] =
        .ok [(.grounded (.int (m * n)), Bindings.empty)] := by
  refine ⟨fun fits => ⟨?_, measured_agrees IntOp.times m n fun k same => ?_⟩, fun notFits => ?_, ?_⟩
  · simp [measuredOutcome, checkedResult, fits]
  · have equal : m * n = k := by
      have reduced : Atom.grounded (GroundedValue.int (m * n)) = Atom.grounded (GroundedValue.int k) :=
        same
      injection reduced with inner
      injection inner
    rw [← equal]
    exact fits
  · simp [measuredOutcome, checkedResult, notFits]
  · rw [heOutcome, he_int_op IntOp.times m n]
    rfl

/-- **On the region the fast answer is HE's measured answer**: for two stored integers in the
64-bit region of `+`, `-` or `*`, the fast path answers the integer that HE's measured table answers. -/
theorem fast_is_measured (m n : ℤ) :
    (add64.region (.int m) (.int n) = true →
        add64.fast (.int m) (.int n) = .int (m + n) ∧
        measuredOutcome (.symbol "+") [.grounded (.int m), .grounded (.int n)] =
          .ok [(.grounded (.int (m + n)), Bindings.empty)]) ∧
      (sub64.region (.int m) (.int n) = true →
        sub64.fast (.int m) (.int n) = .int (m - n) ∧
        measuredOutcome (.symbol "-") [.grounded (.int m), .grounded (.int n)] =
          .ok [(.grounded (.int (m - n)), Bindings.empty)]) ∧
      (mul64.region (.int m) (.int n) = true →
        mul64.fast (.int m) (.int n) = .int (m * n) ∧
        measuredOutcome (.symbol "*") [.grounded (.int m), .grounded (.int n)] =
          .ok [(.grounded (.int (m * n)), Bindings.empty)]) := by
  refine ⟨fun inside => ⟨rfl, ((measured_add m n).1 (of_decide_eq_true inside)).1⟩,
    fun inside => ⟨rfl, ((measured_sub m n).1 (of_decide_eq_true inside)).1⟩,
    fun inside => ⟨rfl, ((measured_mul m n).1 (of_decide_eq_true inside)).1⟩⟩

/-! ## Controls -/

/-- The value lens on outcomes: the value of an answer, or the error. -/
def outcomeLens : Unit → Except String Stored → Except String ℚ := fun _ r => r.map value

/-- **A model of measured behaviour, HE's checked multiplication**: on two stored integers the
product if it fits and the error `IntegerOverflow` otherwise; with a fraction, the exact product.
Measured: `(* 4611686018427387904 2)` is that error, `(* 4611686018427387904.0 2)` is a number. -/
def checkedMul (a b : Stored) : Except String Stored :=
  match a, b with
  | .int m, .int n => if Fits (m * n) then .ok (.int (m * n)) else .error "IntegerOverflow"
  | a, b => .ok (lift (· * ·) (a, b))

/-- The stored integer `2^62`. -/
def bigInt : Stored := .int 4611686018427387904

/-- The fraction `2^62`. -/
def bigFrac : Stored := .frac 4611686018427387904

theorem big_same_value : value bigInt = value bigFrac := by
  simp [bigInt, bigFrac, value]

theorem big_overflows : ¬ Fits 9223372036854775808 := by
  decide

/-- **Control: answering an error outside the region does not respect the value lens**, on the
stored integer `2^62` and the fraction of the same value, each times `2`. -/
theorem checkedMul_not_respects :
    ¬ Respects (pairRead valueLens valueLens) outcomeLens
      (fun x : Stored × Stored => checkedMul x.1 x.2) := by
  rw [respects_pair_iff]
  intro respects
  have split := respects bigInt bigFrac (.int 2) (.int 2) (fun _ => big_same_value) (fun _ => rfl) ()
  simp [outcomeLens, checkedMul, bigInt, bigFrac, big_overflows, Except.map] at split

/-- 64-bit wrapping. -/
def wrap64 (z : ℤ) : ℤ := (z + 2 ^ 63) % 2 ^ 64 - 2 ^ 63

/-- **Wrapping multiplication**: on two stored integers the product wrapped to 64 bits; with a
fraction, the exact product. -/
def wrapMul (a b : Stored) : Stored :=
  match a, b with
  | .int m, .int n => .int (wrap64 (m * n))
  | a, b => lift (· * ·) (a, b)

theorem wrap_big : wrap64 (4611686018427387904 * 2) = -9223372036854775808 := by
  decide

/-- **Control: wrapping does not respect the value lens**, on the same pair: `-2^63` against
`2^63`. -/
theorem wrapMul_not_respects :
    ¬ Respects (pairRead valueLens valueLens) valueLens (fun x : Stored × Stored => wrapMul x.1 x.2) := by
  rw [respects_pair_iff]
  intro respects
  have split := respects bigInt bigFrac (.int 2) (.int 2) (fun _ => big_same_value) (fun _ => rfl) ()
  have wrapped : value (wrapMul bigInt (.int 2)) = -9223372036854775808 := by
    show ((wrap64 (4611686018427387904 * 2) : ℤ) : ℚ) = -9223372036854775808
    rw [wrap_big]
    norm_num
  have exact : value (wrapMul bigFrac (.int 2)) = 9223372036854775808 := by
    show (4611686018427387904 : ℚ) * ((2 : ℤ) : ℚ) = 9223372036854775808
    norm_num
  have equal : value (wrapMul bigInt (.int 2)) = value (wrapMul bigFrac (.int 2)) := split
  rw [wrapped, exact] at equal
  norm_num at equal

/-- **The licensed composite gives one value on that pair.** -/
theorem mul64_composite_pair :
    value (withFasts (· * ·) [mul64] bigInt (.int 2)) = 9223372036854775808 ∧
      value (withFasts (· * ·) [mul64] bigFrac (.int 2)) = 9223372036854775808 := by
  have licensed : ∀ p ∈ [mul64], Licensed (· * ·) p := fun p member => by
    rcases List.mem_singleton.mp member with rfl
    exact mul64_licensed
  rw [withFasts_value licensed, withFasts_value licensed]
  constructor <;> norm_num [bigInt, bigFrac, value]

/-! ## On the step -/

/-- **A grounded table built from licensed fast paths**: the 64-bit paths where they apply, exact
otherwise; division exact by a nonzero divisor. -/
def fastTable : OnTheStep.Table
  | .plus, a, b => some (withFasts (· + ·) [add64] a b)
  | .minus, a, b => some (withFasts (· - ·) [sub64] a b)
  | .times, a, b => some (withFasts (· * ·) [mul64] a b)
  | .divide, a, b => if value b = 0 then none else some (lift (· / ·) (a, b))

theorem singleton_licensed {f : ℚ → ℚ → ℚ} {p : FastPath} (licensed : Licensed f p) :
    ∀ q ∈ [p], Licensed f q := fun q member => by
  rcases List.mem_singleton.mp member with rfl
  exact licensed

/-- **The table built from licensed fast paths respects the value lens.** -/
theorem fastTable_respects : OnTheStep.TableRespects fastTable := by
  intro o a a' b b' first second
  cases o with
  | plus =>
      show some (value (withFasts (· + ·) [add64] a b)) = some (value (withFasts (· + ·) [add64] a' b'))
      rw [withFasts_value (singleton_licensed add64_licensed),
        withFasts_value (singleton_licensed add64_licensed), first, second]
  | minus =>
      show some (value (withFasts (· - ·) [sub64] a b)) = some (value (withFasts (· - ·) [sub64] a' b'))
      rw [withFasts_value (singleton_licensed sub64_licensed),
        withFasts_value (singleton_licensed sub64_licensed), first, second]
  | times =>
      show some (value (withFasts (· * ·) [mul64] a b)) = some (value (withFasts (· * ·) [mul64] a' b'))
      rw [withFasts_value (singleton_licensed mul64_licensed),
        withFasts_value (singleton_licensed mul64_licensed), first, second]
  | divide =>
      show (if value b = 0 then none else some (lift (· / ·) (a, b))).map value =
        (if value b' = 0 then none else some (lift (· / ·) (a', b'))).map value
      rw [second]
      split_ifs
      · rfl
      · show some (value a / value b) = some (value a' / value b')
        rw [first, second]

/-- **Representation independence for the step with the fast table**: re-storing every numeral
changes no answer. -/
theorem fastTable_answers {O : Type} [DecidableEq O] {ρ : Stored → Stored} (restoring : Restoring ρ)
    (label : O → OnTheStep.NTerm Stored) (C : Configuration (OnTheStep.NTerm Stored) O)
    (check : Check (OnTheStep.NTerm Stored)) :
    OnTheStep.Answer fastTable (OnTheStep.NTerm.map ρ ∘ label) (OnTheStep.restoreConf ρ C)
        (check.map (OnTheStep.NTerm.map ρ)) ↔ OnTheStep.Answer fastTable label C check :=
  OnTheStep.answer_restore fastTable_respects restoring label C check

#print axioms withFasts_value
#print axioms withFasts_respects
#print axioms withFasts_any
#print axioms adding_iff_licensed
#print axioms int64_licensed
#print axioms add64_licensed
#print axioms sub64_licensed
#print axioms mul64_licensed
#print axioms measured_add
#print axioms measured_sub
#print axioms measured_mul
#print axioms fast_is_measured
#print axioms checkedMul_not_respects
#print axioms wrapMul_not_respects
#print axioms mul64_composite_pair
#print axioms fastTable_respects
#print axioms fastTable_answers

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.FastPaths
