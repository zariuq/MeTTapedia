import Mettapedia.Machines.InformationFlow.CheckErasure

/-!
# Checked regions with exact read effects

A checked region can omit write and output checks while retaining the join of
labels actually read along its executed control path. The evaluator below is
defined over raw states independently of the monitored evaluator. It carries
neither an input current label nor dynamic write/output flow checks.

For an admitted source command and an initial current label within its static
bound, the raw result and actual read effect reconstruct the full monitored
state. This licenses re-entry into an arbitrary monitored continuation. Merely
reattaching the static all-branches read bound does not have this property: an
untaken private read can then suppress a subsequent public output.

The result removes redundant checks, not all label accounting. It does not
claim a native implementation correspondence or physical performance bound.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.InformationFlow.CheckedRegion

open FloatingLabel

universe u

structure EffectResult (Label : Type u) where
  raw : RawState Label
  readEffect : Label

variable {Label : Type u} [SemilatticeSup Label] [OrderBot Label]

/-- No current label and no dynamic write/output checks occur here. Only
queries contribute an effect; their contents cannot remove that effect. -/
def effectStep (spaceLabel : Nat → Label) : Primitive Label → RawState Label → EffectResult Label
  | .literal value, s => ⟨{ s with register := value }, ⊥⟩
  | .query space predicate, s =>
      ⟨{ s with register := (s.store space).filter predicate }, spaceLabel space⟩
  | .count, s => ⟨{ s with register := [s.register.length] }, ⊥⟩
  | .write space, s =>
      ⟨{ s with store := Function.update s.store space s.register }, ⊥⟩
  | .emit destination, s =>
      ⟨{ s with trace := s.trace ++ [(destination, s.register)] }, ⊥⟩

/-- Sequential composition joins the actual effects. A conditional executes
and records only the branch selected by its raw register. -/
def effectRun (spaceLabel : Nat → Label) : Command Label → RawState Label → EffectResult Label
  | .skip, s => ⟨s, ⊥⟩
  | .primitive operation, s => effectStep spaceLabel operation s
  | .seq first second, s =>
      let earlier := effectRun spaceLabel first s
      let later := effectRun spaceLabel second earlier.raw
      ⟨later.raw, earlier.readEffect ⊔ later.readEffect⟩
  | .ifEmpty yes no, s =>
      if s.register.isEmpty then effectRun spaceLabel yes s else effectRun spaceLabel no s

/-- Re-entry preserves the incoming label and incorporates every actual read. -/
def reconstitute (initial : Label) (result : EffectResult Label) : State Label :=
  { current := initial ⊔ result.readEffect
    register := result.raw.register
    store := result.raw.store
    trace := result.raw.trace }

theorem effectStep_raw (spaceLabel : Nat → Label) (operation : Primitive Label)
    (s : RawState Label) :
    (effectStep spaceLabel operation s).raw = uncheckedStep operation s := by
  cases operation <;> rfl

theorem effectStep_readEffect (spaceLabel : Nat → Label) (operation : Primitive Label)
    (s : RawState Label) :
    (effectStep spaceLabel operation s).readEffect = primitiveReadLabel spaceLabel operation := by
  cases operation <;> rfl

/-- The receipt instrumentation leaves the independent unchecked result
unchanged, for every finite command and raw input. -/
theorem effectRun_raw (spaceLabel : Nat → Label) (command : Command Label)
    (s : RawState Label) :
    (effectRun spaceLabel command s).raw = uncheckedRun command s := by
  induction command generalizing s with
  | skip => rfl
  | primitive operation => exact effectStep_raw _ _ _
  | seq first second ihFirst ihSecond =>
      simp only [effectRun, uncheckedRun, ihSecond, ihFirst]
  | ifEmpty yes no ihYes ihNo =>
      by_cases empty : s.register.isEmpty = true
      · simpa [effectRun, uncheckedRun, empty] using ihYes s
      · simpa [effectRun, uncheckedRun, empty] using ihNo s

/-- The static effect bounds the actually executed path, but may be strictly
larger when a conditional branch is not taken. -/
theorem effectRun_readEffect_le (spaceLabel : Nat → Label) (command : Command Label)
    (s : RawState Label) :
    (effectRun spaceLabel command s).readEffect ≤ readLabel spaceLabel command := by
  induction command generalizing s with
  | skip => exact le_rfl
  | primitive operation => exact le_of_eq (effectStep_readEffect _ _ _)
  | seq first second ihFirst ihSecond =>
      exact sup_le_sup (ihFirst s) (ihSecond _)
  | ifEmpty yes no ihYes ihNo =>
      simp only [effectRun]
      split
      · exact (ihYes s).trans le_sup_left
      · exact (ihNo s).trans le_sup_right

omit [OrderBot Label] in
theorem erase_reconstitute (initial : Label) (result : EffectResult Label) :
    erase (reconstitute initial result) = result.raw := by
  cases result with
  | mk raw effect => cases raw; rfl

omit [SemilatticeSup Label] [OrderBot Label] in
private theorem state_eq_of_current_erase {s t : State Label}
    (current : s.current = t.current) (raw : erase s = erase t) : s = t := by
  cases s
  cases t
  cases current
  cases raw
  rfl

variable [DecidableLE Label]

/-- Static admission ensures the two evaluators take the same control path.
On that path the receipt reconstructs the exact current label, rather than a
conservative bound which could change a later dynamic decision. -/
theorem effectRun_current_eq {spaceLabel : Nat → Label} {command : Command Label}
    {bound : Label} (typed : WellTyped spaceLabel bound command)
    (s : State Label) (within : s.current ≤ bound) :
    (run spaceLabel command s).current =
      s.current ⊔ (effectRun spaceLabel command (erase s)).readEffect := by
  induction typed generalizing s with
  | skip => simp [run, effectRun]
  | primitive bound operation allowed =>
      rw [run, effectRun, effectStep_readEffect]
      exact step_current_eq _ _ _
  | seq bound first second firstTyped secondTyped ihFirst ihSecond =>
      have nextBound : (run spaceLabel first s).current ≤ bound ⊔ readLabel spaceLabel first :=
        (run_current_bound _ _ _).trans (sup_le_sup_right within _)
      have firstRaw : (effectRun spaceLabel first (erase s)).raw =
          erase (run spaceLabel first s) :=
        (effectRun_raw _ _ _).trans (run_check_erasure firstTyped s within).symm
      simp only [run, effectRun]
      rw [firstRaw, ihSecond _ nextBound, ihFirst s within, sup_assoc]
  | ifEmpty bound yes no yesTyped noTyped ihYes ihNo =>
      by_cases empty : s.register.isEmpty = true
      · simpa [run, effectRun, erase, empty] using ihYes s within
      · simpa [run, effectRun, erase, empty] using ihNo s within

/-- The independently evaluated raw state and actual read receipt recover
every field of the monitored result for a statically admitted region. -/
theorem reconstitute_effectRun_eq {spaceLabel : Nat → Label} {command : Command Label}
    {bound : Label} (typed : WellTyped spaceLabel bound command)
    (s : State Label) (within : s.current ≤ bound) :
    reconstitute s.current (effectRun spaceLabel command (erase s)) =
      run spaceLabel command s := by
  apply state_eq_of_current_erase
  · exact (effectRun_current_eq typed s within).symm
  · rw [erase_reconstitute]
    exact (effectRun_raw _ _ _).trans (run_check_erasure typed s within).symm

/-- No static typing premise is imposed on the continuation: dynamic checks
resume with exactly the state they would have received from the source. -/
theorem monitored_continuation_exact {spaceLabel : Nat → Label} {command : Command Label}
    {bound : Label} (typed : WellTyped spaceLabel bound command)
    (s : State Label) (within : s.current ≤ bound) (continuation : Command Label) :
    run spaceLabel continuation
        (reconstitute s.current (effectRun spaceLabel command (erase s))) =
      run spaceLabel (.seq command continuation) s := by
  rw [reconstitute_effectRun_eq typed s within]
  rfl

namespace Controls

def spaceLabels (space : Nat) : Nat := if space = 0 then 0 else 1

def initial : State Nat where
  current := 0
  register := [7]
  store := fun _ => []
  trace := []

def conditionalRead : Command Nat :=
  .ifEmpty (.primitive (.query 1 (fun _ => true))) .skip

def publicOutput : Command Nat := .primitive (.emit 0)

theorem conditionalRead_wellTyped : WellTyped spaceLabels 0 conditionalRead :=
  .ifEmpty _ _ _ (.primitive _ _ (.query _ _)) (.skip _)

/-- The nonempty input selects the branch with no reads. The source's
all-branches summary nevertheless includes the private read. -/
theorem actual_effect_strictly_below_static :
    (effectRun spaceLabels conditionalRead (erase initial)).readEffect = 0 ∧
      readLabel spaceLabels conditionalRead = 1 := by
  decide

def staticReentry : State Nat :=
  reconstitute initial.current
    ⟨uncheckedRun conditionalRead (erase initial), readLabel spaceLabels conditionalRead⟩

def exactReentry : State Nat :=
  reconstitute initial.current (effectRun spaceLabels conditionalRead (erase initial))

/-- Reattaching a static overapproximation suppresses a real public output.
This is a counterexample to exact mixed-region execution, not to security. -/
theorem static_reentry_changes_public_output :
    visibleTrace 0 (run spaceLabels publicOutput staticReentry) = [] ∧
      visibleTrace 0 (run spaceLabels (.seq conditionalRead publicOutput) initial) =
        [(0, [7])] := by
  decide

theorem exact_reentry_keeps_public_output :
    run spaceLabels publicOutput exactReentry =
      run spaceLabels (.seq conditionalRead publicOutput) initial :=
  monitored_continuation_exact conditionalRead_wellTyped initial le_rfl publicOutput

/-- Reading the private space really raises the receipt even if it is empty. -/
theorem taken_empty_query_retains_effect :
    let emptyInitial : State Nat := { initial with register := [] }
    (effectRun spaceLabels conditionalRead (erase emptyInitial)).raw.register = [] ∧
      (effectRun spaceLabels conditionalRead (erase emptyInitial)).readEffect = 1 := by
  decide

end Controls

end Mettapedia.Machines.InformationFlow.CheckedRegion
