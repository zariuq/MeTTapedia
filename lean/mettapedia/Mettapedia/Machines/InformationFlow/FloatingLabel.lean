import Mathlib.Order.Lattice
import Mathlib.Data.List.Basic
import Mathlib.Data.Bool.Basic
import Mathlib.Tactic

/-!
# A floating-label machine with labeled stores

Finite structured commands operate on a register containing answer occurrences,
fixed-label spaces, and an output trace. Reading a space raises the current label
before inspecting its contents, including an empty result. Writes and outputs
require the current label to flow to their destination. Conditionals retain the
current label, so their control dependencies survive the selected branch.

The public observation includes all visible store contents and the ordered visible
output trace. It excludes elapsed time, allocation, and the number of internal
steps. This module does not model unrestricted foreign calls, capabilities,
declassification, divergence, or parallel scheduling. It is a reusable monitor
core, not a claim that an existing MeTTa evaluator already implements it.

Two runs use the same command, pure predicates, destination identities, and
space-label policy. A secret-dependent closure, program, or space handle must
retain that dependency when lowering into this core. The raw register is not
an unconditional public return value: publication uses a checked output or
`visibleRegister`.
-/

namespace Mettapedia.Machines.InformationFlow.FloatingLabel

universe u

structure State (Label : Type u) where
  current : Label
  register : List Nat
  store : Nat → List Nat
  trace : List (Label × List Nat)

inductive Primitive (Label : Type u) where
  | literal (value : List Nat)
  | query (space : Nat) (predicate : Nat → Bool)
  | count
  | write (space : Nat)
  | emit (destination : Label)

inductive Command (Label : Type u) where
  | skip
  | primitive (operation : Primitive Label)
  | seq (first second : Command Label)
  | ifEmpty (yes no : Command Label)

variable {Label : Type u} [SemilatticeSup Label] [DecidableLE Label]

def step (spaceLabel : Nat → Label) : Primitive Label → State Label → State Label
  | .literal value, s => { s with register := value }
  | .query space predicate, s =>
      { s with current := s.current ⊔ spaceLabel space,
               register := (s.store space).filter predicate }
  | .count, s => { s with register := [s.register.length] }
  | .write space, s =>
      if s.current ≤ spaceLabel space then
        { s with store := Function.update s.store space s.register }
      else s
  | .emit destination, s =>
      if s.current ≤ destination then
        { s with trace := s.trace ++ [(destination, s.register)] }
      else s

def run (spaceLabel : Nat → Label) : Command Label → State Label → State Label
  | .skip, s => s
  | .primitive operation, s => step spaceLabel operation s
  | .seq first second, s => run spaceLabel second (run spaceLabel first s)
  | .ifEmpty yes no, s =>
      if s.register.isEmpty then run spaceLabel yes s else run spaceLabel no s

def visibleTrace (observer : Label) (s : State Label) : List (Label × List Nat) :=
  s.trace.filter (fun event => decide (event.1 ≤ observer))

/-- A query return is mediated just like an explicit output. Empty and nonempty
private registers are both withheld. -/
def visibleRegister (observer : Label) (s : State Label) : Option (List Nat) :=
  if s.current ≤ observer then some s.register else none

structure PublicEquivalent (spaceLabel : Nat → Label) (observer : Label)
    (s t : State Label) : Prop where
  store : ∀ space, spaceLabel space ≤ observer → s.store space = t.store space
  trace : visibleTrace observer s = visibleTrace observer t

structure LowEquivalent (spaceLabel : Nat → Label) (observer : Label)
    (s t : State Label) : Prop extends PublicEquivalent spaceLabel observer s t where
  visibility : s.current ≤ observer ↔ t.current ≤ observer
  current : s.current ≤ observer → s.current = t.current
  register : s.current ≤ observer → s.register = t.register

theorem LowEquivalent.visibleRegister_eq {spaceLabel : Nat → Label} {observer : Label}
    {s t : State Label} (h : LowEquivalent spaceLabel observer s t) :
    visibleRegister observer s = visibleRegister observer t := by
  by_cases low : s.current ≤ observer
  · simp [visibleRegister, low, h.visibility.mp low, h.register low]
  · have highT : ¬ t.current ≤ observer := fun ht => low (h.visibility.mpr ht)
    simp [visibleRegister, low, highT]

theorem PublicEquivalent.refl (spaceLabel : Nat → Label) (observer : Label)
    (s : State Label) : PublicEquivalent spaceLabel observer s s :=
  ⟨fun _ _ => rfl, rfl⟩

theorem PublicEquivalent.symm {spaceLabel : Nat → Label} {observer : Label}
    {s t : State Label} (h : PublicEquivalent spaceLabel observer s t) :
    PublicEquivalent spaceLabel observer t s :=
  ⟨fun space hs => (h.store space hs).symm, h.trace.symm⟩

theorem PublicEquivalent.trans {spaceLabel : Nat → Label} {observer : Label}
    {s t v : State Label} (h : PublicEquivalent spaceLabel observer s t)
    (k : PublicEquivalent spaceLabel observer t v) :
    PublicEquivalent spaceLabel observer s v :=
  ⟨fun space hs => (h.store space hs).trans (k.store space hs), h.trace.trans k.trace⟩

theorem step_current_mono (spaceLabel : Nat → Label) (operation : Primitive Label)
    (s : State Label) : s.current ≤ (step spaceLabel operation s).current := by
  cases operation <;> simp only [step]
  · exact le_rfl
  · exact le_sup_left
  · exact le_rfl
  · split <;> exact le_rfl
  · split <;> exact le_rfl

theorem run_current_mono (spaceLabel : Nat → Label) (command : Command Label)
    (s : State Label) : s.current ≤ (run spaceLabel command s).current := by
  induction command generalizing s with
  | skip => exact le_rfl
  | primitive operation => exact step_current_mono _ _ _
  | seq first second ihFirst ihSecond => exact (ihFirst s).trans (ihSecond _)
  | ifEmpty yes no ihYes ihNo =>
      simp only [run]
      split
      · exact ihYes s
      · exact ihNo s

theorem step_confinement (spaceLabel : Nat → Label) (observer : Label)
    (operation : Primitive Label) (s : State Label) (high : ¬ s.current ≤ observer) :
    PublicEquivalent spaceLabel observer (step spaceLabel operation s) s := by
  cases operation with
  | literal value => exact ⟨fun _ _ => rfl, rfl⟩
  | query space predicate => exact ⟨fun _ _ => rfl, rfl⟩
  | count => exact ⟨fun _ _ => rfl, rfl⟩
  | write target =>
      simp only [step]
      split
      · rename_i allowed
        refine ⟨?_, rfl⟩
        intro space visible
        have different : space ≠ target := by
          intro eq
          subst space
          exact high (allowed.trans visible)
        simp [Function.update, different]
      · exact PublicEquivalent.refl _ _ _
  | emit destination =>
      simp only [step]
      split
      · rename_i allowed
        have hidden : ¬ destination ≤ observer := fun h => high (allowed.trans h)
        refine ⟨fun _ _ => rfl, ?_⟩
        simp [visibleTrace, List.filter_append, hidden]
      · exact PublicEquivalent.refl _ _ _

theorem run_confinement (spaceLabel : Nat → Label) (observer : Label)
    (command : Command Label) (s : State Label) (high : ¬ s.current ≤ observer) :
    PublicEquivalent spaceLabel observer (run spaceLabel command s) s := by
  induction command generalizing s with
  | skip => exact PublicEquivalent.refl _ _ _
  | primitive operation => exact step_confinement _ _ _ _ high
  | seq first second ihFirst ihSecond =>
      have stillHigh : ¬ (run spaceLabel first s).current ≤ observer :=
        fun h => high ((run_current_mono _ _ _).trans h)
      exact (ihSecond _ stillHigh).trans (ihFirst s high)
  | ifEmpty yes no ihYes ihNo =>
      simp only [run]
      split
      · exact ihYes s high
      · exact ihNo s high

theorem step_noninterference (spaceLabel : Nat → Label) (observer : Label)
    (operation : Primitive Label) {s t : State Label}
    (h : LowEquivalent spaceLabel observer s t) :
    LowEquivalent spaceLabel observer (step spaceLabel operation s)
      (step spaceLabel operation t) := by
  by_cases low : s.current ≤ observer
  · have current := h.current low
    have register := h.register low
    cases operation with
    | literal value =>
        exact ⟨⟨h.store, h.trace⟩, h.visibility, fun _ => current, fun _ => rfl⟩
    | count =>
        exact ⟨⟨h.store, h.trace⟩, h.visibility, fun _ => current,
          fun _ => by simp [step, register]⟩
    | query space predicate =>
        refine ⟨⟨h.store, h.trace⟩, ?_, ?_, ?_⟩
        · simp only [step, current]
        · intro _; simp [step, current]
        · intro visible
          have sourceVisible : spaceLabel space ≤ observer := le_sup_right.trans visible
          simp only [step, h.store space sourceVisible]
    | write space =>
        simp only [step, current]
        split
        · refine ⟨⟨?_, h.trace⟩, Iff.rfl, fun _ => rfl, fun _ => register⟩
          · intro other visible
            by_cases eq : other = space
            · subst other; simp [register]
            · simp [Function.update, eq, h.store other visible]
        · exact h
    | emit destination =>
        simp only [step, current]
        split
        · refine ⟨⟨h.store, ?_⟩, Iff.rfl, fun _ => rfl, fun _ => register⟩
          simp only [visibleTrace, List.filter_append]
          change visibleTrace observer s ++ _ = visibleTrace observer t ++ _
          rw [h.trace, register]
        · exact h
  · have highT : ¬ t.current ≤ observer := fun ht => low (h.visibility.mpr ht)
    have highS' : ¬ (step spaceLabel operation s).current ≤ observer :=
      fun hs => low ((step_current_mono _ _ _).trans hs)
    have highT' : ¬ (step spaceLabel operation t).current ≤ observer :=
      fun ht => highT ((step_current_mono _ _ _).trans ht)
    refine ⟨(step_confinement _ _ _ _ low).trans
      (h.toPublicEquivalent.trans (step_confinement _ _ _ _ highT).symm), ?_, ?_, ?_⟩
    · exact ⟨fun hs => (highS' hs).elim, fun ht => (highT' ht).elim⟩
    · exact fun hs => (highS' hs).elim
    · exact fun hs => (highS' hs).elim

/-- Ordered public outputs and visible mutable spaces are independent of
private contents, for every finite command in the monitored core. -/
theorem run_noninterference (spaceLabel : Nat → Label) (observer : Label)
    (command : Command Label) {s t : State Label}
    (h : LowEquivalent spaceLabel observer s t) :
    LowEquivalent spaceLabel observer (run spaceLabel command s)
      (run spaceLabel command t) := by
  induction command generalizing s t with
  | skip => exact h
  | primitive operation => exact step_noninterference _ _ _ h
  | seq first second ihFirst ihSecond => exact ihSecond (ihFirst h)
  | ifEmpty yes no ihYes ihNo =>
      by_cases low : s.current ≤ observer
      · have register := h.register low
        simp only [run, register]
        split
        · exact ihYes h
        · exact ihNo h
      · have highT : ¬ t.current ≤ observer := fun ht => low (h.visibility.mpr ht)
        have highS' : ¬ (run spaceLabel (.ifEmpty yes no) s).current ≤ observer :=
          fun hs => low ((run_current_mono _ _ _).trans hs)
        have highT' : ¬ (run spaceLabel (.ifEmpty yes no) t).current ≤ observer :=
          fun ht => highT ((run_current_mono _ _ _).trans ht)
        refine ⟨(run_confinement _ _ _ _ low).trans
          (h.toPublicEquivalent.trans (run_confinement _ _ _ _ highT).symm), ?_, ?_, ?_⟩
        · exact ⟨fun hs => (highS' hs).elim, fun ht => (highT' ht).elim⟩
        · exact fun hs => (highS' hs).elim
        · exact fun hs => (highS' hs).elim

theorem run_visibleRegister_noninterference (spaceLabel : Nat → Label) (observer : Label)
    (command : Command Label) {s t : State Label}
    (h : LowEquivalent spaceLabel observer s t) :
    visibleRegister observer (run spaceLabel command s) =
      visibleRegister observer (run spaceLabel command t) :=
  (run_noninterference spaceLabel observer command h).visibleRegister_eq

end Mettapedia.Machines.InformationFlow.FloatingLabel
