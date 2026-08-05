import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.DynamicFrontierTrace

/-!
# Hysteretic active-frontier selection

Error-threshold sparsity can chatter when one threshold is used both to enter
and leave the active set.  This module isolates the finite variation argument
behind a two-threshold selector.  Successive switch events must cross the
hysteresis gap, so all switches after the first consume measured signal
variation.

The result concerns selection stability only.  It does not certify that the
selected frontier captures enough credit mass or decreases task loss; those
obligations remain in `ActiveFrontierSettling` and `DynamicFrontierTrace`.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace FrontierHysteresis

/-- Keep an active coordinate while its signal stays above `exitThreshold`;
activate an inactive coordinate only at the higher `enterThreshold`. -/
noncomputable def nextActive
    (exitThreshold enterThreshold : ℝ) (active : Bool) (signal : ℝ) : Bool :=
  if active then decide (exitThreshold ≤ signal)
  else decide (enterThreshold ≤ signal)

theorem entry_signal_ge
    {exitThreshold enterThreshold signal : ℝ}
    (entry : nextActive exitThreshold enterThreshold false signal = true) :
    enterThreshold ≤ signal := by
  simpa [nextActive] using entry

theorem exit_signal_lt
    {exitThreshold enterThreshold signal : ℝ}
    (exit : nextActive exitThreshold enterThreshold true signal = false) :
    signal < exitThreshold := by
  simpa [nextActive, decide_eq_false_iff_not] using exit

/-- An entry followed immediately by an exit requires movement at least as
large as the threshold gap. -/
theorem entry_then_exit_gap_lt_abs
    {exitThreshold enterThreshold firstSignal secondSignal : ℝ}
    (thresholds : exitThreshold < enterThreshold)
    (entry :
      nextActive exitThreshold enterThreshold false firstSignal = true)
    (exit :
      nextActive exitThreshold enterThreshold true secondSignal = false) :
    enterThreshold - exitThreshold <
      |secondSignal - firstSignal| := by
  have hentry := entry_signal_ge entry
  have hexit := exit_signal_lt exit
  rw [abs_of_nonpos (by linarith : secondSignal - firstSignal ≤ 0)]
  linarith

/-- An exit followed immediately by an entry obeys the same gap bound. -/
theorem exit_then_entry_gap_lt_abs
    {exitThreshold enterThreshold firstSignal secondSignal : ℝ}
    (thresholds : exitThreshold < enterThreshold)
    (exit :
      nextActive exitThreshold enterThreshold true firstSignal = false)
    (entry :
      nextActive exitThreshold enterThreshold false secondSignal = true) :
    enterThreshold - exitThreshold <
      |secondSignal - firstSignal| := by
  have hexit := exit_signal_lt exit
  have hentry := entry_signal_ge entry
  rw [abs_of_nonneg (by linarith : 0 ≤ secondSignal - firstSignal)]
  linarith

/-- The value recorded when one coordinate changes membership. -/
structure SwitchEvent where
  active : Bool
  signal : ℝ

/-- Every entry is recorded at or above the entry threshold and every exit at
or below the exit threshold. -/
def SwitchEvent.Valid
    (exitThreshold enterThreshold : ℝ) (event : SwitchEvent) : Prop :=
  if event.active then enterThreshold ≤ event.signal
  else event.signal ≤ exitThreshold

/-- A switch trace is valid when each event crosses its corresponding
threshold and successive events alternate membership. -/
def ValidSwitchTrace
    (exitThreshold enterThreshold : ℝ) : List SwitchEvent → Prop
  | [] => True
  | [event] => event.Valid exitThreshold enterThreshold
  | first :: second :: rest =>
      first.Valid exitThreshold enterThreshold ∧
        first.active ≠ second.active ∧
        ValidSwitchTrace exitThreshold enterThreshold (second :: rest)

/-- Total scalar variation along the emitted switch events. -/
def switchVariation : List SwitchEvent → ℝ
  | [] => 0
  | [_] => 0
  | first :: second :: rest =>
      |second.signal - first.signal| +
        switchVariation (second :: rest)

theorem adjacent_gap_le
    {exitThreshold enterThreshold : ℝ}
    {first second : SwitchEvent}
    (thresholds : exitThreshold ≤ enterThreshold)
    (firstValid : first.Valid exitThreshold enterThreshold)
    (secondValid : second.Valid exitThreshold enterThreshold)
    (different : first.active ≠ second.active) :
    enterThreshold - exitThreshold ≤
      |second.signal - first.signal| := by
  cases hfirst : first.active <;> cases hsecond : second.active
  · exact (different (by simp [hfirst, hsecond])).elim
  · simp [SwitchEvent.Valid, hfirst, hsecond] at firstValid secondValid
    rw [abs_of_nonneg (by linarith [thresholds] :
      0 ≤ second.signal - first.signal)]
    linarith
  · simp [SwitchEvent.Valid, hfirst, hsecond] at firstValid secondValid
    rw [abs_of_nonpos (by linarith [thresholds] :
      second.signal - first.signal ≤ 0)]
    linarith
  · exact (different (by simp [hfirst, hsecond])).elim

/-- **Variation budget for hysteretic switching.**  All switch events after
the first consume at least one threshold gap.  Equivalently, a trace with
`n` emitted switches requires variation at least `(n-1) * gap`.

This formulation deliberately gives the first switch for free, so it remains
valid for either initial membership state and for a trace that starts between
the thresholds. -/
theorem gap_mul_switches_after_first_le_variation
    {exitThreshold enterThreshold : ℝ}
    (trace : List SwitchEvent)
    (thresholds : exitThreshold ≤ enterThreshold)
    (valid : ValidSwitchTrace exitThreshold enterThreshold trace) :
    (((trace.length - 1 : ℕ) : ℝ) *
        (enterThreshold - exitThreshold)) ≤
      switchVariation trace := by
  induction trace with
  | nil =>
      simp [switchVariation]
  | cons first tail inductionHypothesis =>
      cases tail with
      | nil =>
          simp [switchVariation]
      | cons second rest =>
          rcases valid with ⟨firstValid, different, tailValid⟩
          have secondValid :
              second.Valid exitThreshold enterThreshold := by
            cases rest with
            | nil =>
                simpa [ValidSwitchTrace] using tailValid
            | cons third rest =>
                exact tailValid.1
          have gapBound :
              enterThreshold - exitThreshold ≤
                |second.signal - first.signal| :=
            adjacent_gap_le thresholds firstValid secondValid different
          have tailBound := inductionHypothesis tailValid
          simp only [List.length_cons, Nat.add_sub_cancel,
            Nat.cast_add, Nat.cast_one, switchVariation]
          calc
            ((rest.length : ℝ) + 1) *
                  (enterThreshold - exitThreshold) =
                (enterThreshold - exitThreshold) +
                  (rest.length : ℝ) *
                    (enterThreshold - exitThreshold) := by ring
            _ ≤ |second.signal - first.signal| +
                  switchVariation (second :: rest) :=
              add_le_add gapBound (by simpa using tailBound)

/-! ## Aggregate coordinate accounting

A runtime usually reports frontier churn as the sum of symmetric-difference
sizes between consecutive active sets.  The scalar theorem above does not
charge the first switch of each coordinate.  Consequently, total churn alone
is insufficient: the certificate must additionally report how many distinct
coordinates switched at least once.
-/

variable {Coordinate : Type*} [Fintype Coordinate]

/-- One unit for a coordinate that emitted at least one switch event. -/
def firstSwitchIndicator : List SwitchEvent → ℕ
  | [] => 0
  | _ :: _ => 1

/-- Total membership changes across every coordinate.  When a runtime emits
one event per symmetric-difference membership change, this is its summed
churn. -/
def totalSwitchEvents
    (traces : Coordinate → List SwitchEvent) : ℕ :=
  ∑ coordinate, (traces coordinate).length

/-- Number of distinct coordinates that changed membership at least once. -/
def switchedCoordinateCount
    (traces : Coordinate → List SwitchEvent) : ℕ :=
  ∑ coordinate, firstSwitchIndicator (traces coordinate)

/-- Switches to which a hysteresis-gap charge applies: every switch after the
first one on each coordinate. -/
def chargeableSwitches
    (traces : Coordinate → List SwitchEvent) : ℕ :=
  ∑ coordinate, ((traces coordinate).length - 1)

/-- Sum of the signal variation measured along every coordinate's emitted
switch events. -/
def totalSwitchVariation
    (traces : Coordinate → List SwitchEvent) : ℝ :=
  ∑ coordinate, switchVariation (traces coordinate)

private theorem length_eq_chargeable_add_firstIndicator
    (events : List SwitchEvent) :
    events.length =
      events.length - 1 + firstSwitchIndicator events := by
  cases events <;> simp [firstSwitchIndicator]

/-- Exact accounting identity.  The uncharged part of aggregate churn is one
first event for every coordinate that ever switched. -/
theorem totalSwitchEvents_eq_chargeable_add_switchedCoordinateCount
    (traces : Coordinate → List SwitchEvent) :
    totalSwitchEvents traces =
      chargeableSwitches traces + switchedCoordinateCount traces := by
  unfold totalSwitchEvents chargeableSwitches switchedCoordinateCount
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun coordinate _ =>
    length_eq_chargeable_add_firstIndicator (traces coordinate)

theorem totalSwitchEvents_sub_switchedCoordinateCount
    (traces : Coordinate → List SwitchEvent) :
    totalSwitchEvents traces - switchedCoordinateCount traces =
      chargeableSwitches traces := by
  have accounting :=
    totalSwitchEvents_eq_chargeable_add_switchedCoordinateCount traces
  omega

/-- **Coordinate-aggregate variation budget.**  The total number of
chargeable membership changes times the threshold gap is bounded by the
total signal variation at switch events. -/
theorem gap_mul_chargeableSwitches_le_totalSwitchVariation
    {exitThreshold enterThreshold : ℝ}
    (traces : Coordinate → List SwitchEvent)
    (thresholds : exitThreshold ≤ enterThreshold)
    (valid :
      ∀ coordinate,
        ValidSwitchTrace exitThreshold enterThreshold (traces coordinate)) :
    ((chargeableSwitches traces : ℕ) : ℝ) *
        (enterThreshold - exitThreshold) ≤
      totalSwitchVariation traces := by
  unfold chargeableSwitches totalSwitchVariation
  rw [Nat.cast_sum, Finset.sum_mul]
  exact Finset.sum_le_sum fun coordinate _ =>
    gap_mul_switches_after_first_le_variation
      (traces coordinate) thresholds (valid coordinate)

/-- Runtime-facing form: subtract the number of distinct switched
coordinates from total membership churn before charging the gap. -/
theorem gap_mul_reportedChurn_sub_distinct_le_totalSwitchVariation
    {exitThreshold enterThreshold : ℝ}
    (traces : Coordinate → List SwitchEvent)
    (thresholds : exitThreshold ≤ enterThreshold)
    (valid :
      ∀ coordinate,
        ValidSwitchTrace exitThreshold enterThreshold (traces coordinate)) :
    (((totalSwitchEvents traces - switchedCoordinateCount traces : ℕ) : ℝ) *
        (enterThreshold - exitThreshold)) ≤
      totalSwitchVariation traces := by
  rw [totalSwitchEvents_sub_switchedCoordinateCount]
  exact gap_mul_chargeableSwitches_le_totalSwitchVariation
    traces thresholds valid

/-- A positive hysteresis gap gives an explicit upper bound on chargeable
membership changes. -/
theorem chargeableSwitches_le_totalVariation_div_gap
    {exitThreshold enterThreshold : ℝ}
    (traces : Coordinate → List SwitchEvent)
    (thresholds : exitThreshold < enterThreshold)
    (valid :
      ∀ coordinate,
        ValidSwitchTrace exitThreshold enterThreshold (traces coordinate)) :
    ((chargeableSwitches traces : ℕ) : ℝ) ≤
      totalSwitchVariation traces /
        (enterThreshold - exitThreshold) := by
  apply (le_div_iff₀ (sub_pos.mpr thresholds)).2
  exact gap_mul_chargeableSwitches_le_totalSwitchVariation
    traces (le_of_lt thresholds) valid

/-! ## Positive and negative fixtures -/

def threeSwitchTrace : List SwitchEvent :=
  [{ active := true, signal := 3 },
   { active := false, signal := 0 },
   { active := true, signal := 4 }]

theorem threeSwitchTrace_valid :
    ValidSwitchTrace 1 3 threeSwitchTrace := by
  norm_num [threeSwitchTrace, ValidSwitchTrace, SwitchEvent.Valid]

theorem threeSwitchTrace_variation :
    switchVariation threeSwitchTrace = 7 := by
  norm_num [threeSwitchTrace, switchVariation]

theorem threeSwitchTrace_pays_two_gaps :
    (((threeSwitchTrace.length - 1 : ℕ) : ℝ) * (3 - 1)) ≤
      switchVariation threeSwitchTrace :=
  gap_mul_switches_after_first_le_variation
    threeSwitchTrace (by norm_num) threeSwitchTrace_valid

/-- With no gap, alternating switches can occur under arbitrarily small
movement.  This concrete trace refutes any unconditional unit-cost claim. -/
noncomputable def zeroGapChatter : List SwitchEvent :=
  [{ active := true, signal := 11 / 10 },
   { active := false, signal := 9 / 10 },
   { active := true, signal := 11 / 10 }]

theorem zeroGapChatter_valid :
    ValidSwitchTrace 1 1 zeroGapChatter := by
  norm_num [zeroGapChatter, ValidSwitchTrace, SwitchEvent.Valid]

theorem zeroGapChatter_refutes_unit_switch_cost :
    ¬ ((((zeroGapChatter.length - 1 : ℕ) : ℝ) * 1) ≤
      switchVariation zeroGapChatter) := by
  norm_num [zeroGapChatter, switchVariation]

/-! ### Aggregate fixtures -/

/-- Two coordinate traces with three chargeable switches in total. -/
def twoCoordinateSwitchTraces : Fin 2 → List SwitchEvent :=
  fun coordinate =>
    if coordinate = 0 then threeSwitchTrace
    else
      [{ active := true, signal := 3 },
       { active := false, signal := 1 }]

theorem twoCoordinateSwitchTraces_valid :
    ∀ coordinate,
      ValidSwitchTrace 1 3 (twoCoordinateSwitchTraces coordinate) := by
  intro coordinate
  fin_cases coordinate <;>
    norm_num [twoCoordinateSwitchTraces, threeSwitchTrace,
      ValidSwitchTrace, SwitchEvent.Valid]

theorem twoCoordinateSwitchTraces_accounting :
    totalSwitchEvents twoCoordinateSwitchTraces = 5 ∧
      switchedCoordinateCount twoCoordinateSwitchTraces = 2 ∧
      chargeableSwitches twoCoordinateSwitchTraces = 3 ∧
      totalSwitchVariation twoCoordinateSwitchTraces = 9 := by
  norm_num [totalSwitchEvents, switchedCoordinateCount,
    firstSwitchIndicator, chargeableSwitches, totalSwitchVariation,
    twoCoordinateSwitchTraces, threeSwitchTrace, switchVariation,
    Fin.sum_univ_two]

theorem twoCoordinateSwitchTraces_pay_aggregate_gap :
    (((chargeableSwitches twoCoordinateSwitchTraces : ℕ) : ℝ) * (3 - 1)) ≤
      totalSwitchVariation twoCoordinateSwitchTraces :=
  gap_mul_chargeableSwitches_le_totalSwitchVariation
    twoCoordinateSwitchTraces (by norm_num)
      twoCoordinateSwitchTraces_valid

/-- Every coordinate switches once.  Aggregate churn is positive, but every
event is a free first switch and the emitted-event variation is zero. -/
def firstSwitchOnlyTraces : Fin 2 → List SwitchEvent :=
  fun _ => [{ active := true, signal := 3 }]

theorem firstSwitchOnlyTraces_valid :
    ∀ coordinate,
      ValidSwitchTrace 1 3 (firstSwitchOnlyTraces coordinate) := by
  intro coordinate
  norm_num [firstSwitchOnlyTraces, ValidSwitchTrace, SwitchEvent.Valid]

theorem firstSwitchOnlyTraces_accounting :
    totalSwitchEvents firstSwitchOnlyTraces = 2 ∧
      switchedCoordinateCount firstSwitchOnlyTraces = 2 ∧
      chargeableSwitches firstSwitchOnlyTraces = 0 ∧
      totalSwitchVariation firstSwitchOnlyTraces = 0 := by
  norm_num [totalSwitchEvents, switchedCoordinateCount,
    firstSwitchIndicator, chargeableSwitches, totalSwitchVariation,
    firstSwitchOnlyTraces, switchVariation, Fin.sum_univ_two]

/-- Negative boundary: charging the hysteresis gap to every reported
membership change is unsound, even with a positive gap and valid traces. -/
theorem totalChurn_without_distinctCount_cannot_be_charged :
    ¬ ((((totalSwitchEvents firstSwitchOnlyTraces : ℕ) : ℝ) * (3 - 1)) ≤
      totalSwitchVariation firstSwitchOnlyTraces) := by
  norm_num [totalSwitchEvents, totalSwitchVariation,
    firstSwitchOnlyTraces, switchVariation, Fin.sum_univ_two]

#print axioms entry_then_exit_gap_lt_abs
#print axioms exit_then_entry_gap_lt_abs
#print axioms gap_mul_switches_after_first_le_variation
#print axioms totalSwitchEvents_eq_chargeable_add_switchedCoordinateCount
#print axioms gap_mul_chargeableSwitches_le_totalSwitchVariation
#print axioms gap_mul_reportedChurn_sub_distinct_le_totalSwitchVariation
#print axioms chargeableSwitches_le_totalVariation_div_gap
#print axioms threeSwitchTrace_pays_two_gaps
#print axioms zeroGapChatter_refutes_unit_switch_cost
#print axioms twoCoordinateSwitchTraces_pay_aggregate_gap
#print axioms totalChurn_without_distinctCount_cannot_be_charged

end FrontierHysteresis

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
