import Mettapedia.Languages.ProcessCalculi.Ambient.DecodingRoles

/-!
# What reading from a place reaches

Reading back from a place reads the components sitting there, and under each marker sitting there, the components
reached from the marker's location among those placed elsewhere (`Reaches`). Components sitting at no reached place
are never read (`readPlaced_unreached`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.Ambient.Decoding

open Mettapedia.Languages.ProcessCalculi.Ambient.Comm (ambientCoreCalc)

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- **The places reading from a place reaches**: the place itself, and those reached from the location of a marker
sitting there, among the components placed elsewhere. -/
inductive Reaches : List Pattern → Pattern → Pattern → Prop
  | here {components : List Pattern} {place : Pattern} : Reaches components place place
  | down {components : List Pattern} {place child target marker : Pattern} :
      marker ∈ components → placedAt place marker = true → childOf marker = some child →
      Reaches (components.filter fun other => !placedAt place other) child target →
      Reaches components place target

/-- **A place reached below another is reached through a marker placing an ambient at it.** -/
theorem Reaches.last {components : List Pattern} {place target : Pattern} (reached : Reaches components place target)
    (different : place ≠ target) : ∃ marker ∈ components, childOf marker = some target := by
  induction reached with
  | here => exact absurd rfl different
  | @down components place child target marker member isPlaced isChild below recurse =>
      by_cases same : child = target
      · subst same
        exact ⟨marker, member, isChild⟩
      · obtain ⟨last, inFiltered, lastChild⟩ := recurse same
        exact ⟨last, (List.mem_filter.mp inFiltered).1, lastChild⟩

/-- Reaching within a sublist reaches within the list. -/
theorem Reaches.mono {components bigger : List Pattern} {place target : Pattern}
    (reached : Reaches components place target) (sub : components.Sublist bigger) : Reaches bigger place target := by
  induction reached generalizing bigger with
  | here => exact .here
  | @down components place child target marker member isPlaced isChild below recurse =>
      exact .down (sub.subset member) isPlaced isChild (recurse (sub.filter _))

/-- Reaching a place in a number of steps. -/
inductive ReachesIn : Nat → List Pattern → Pattern → Pattern → Prop
  | here {components : List Pattern} {place : Pattern} : ReachesIn 0 components place place
  | down {steps : Nat} {components : List Pattern} {place child target marker : Pattern} :
      marker ∈ components → placedAt place marker = true → childOf marker = some child →
      ReachesIn steps (components.filter fun other => !placedAt place other) child target →
      ReachesIn (steps + 1) components place target

theorem Reaches.steps {components : List Pattern} {place target : Pattern} (reached : Reaches components place target) :
    ∃ steps, ReachesIn steps components place target := by
  induction reached with
  | here => exact ⟨0, .here⟩
  | down member isPlaced isChild _ recurse =>
      obtain ⟨steps, below⟩ := recurse
      exact ⟨steps + 1, .down member isPlaced isChild below⟩

theorem ReachesIn.reaches {steps : Nat} {components : List Pattern} {place target : Pattern}
    (reached : ReachesIn steps components place target) : Reaches components place target := by
  induction reached with
  | here => exact .here
  | down member isPlaced isChild _ recurse => exact .down member isPlaced isChild recurse

theorem placedAt_same {first second component : Pattern} (firstPlaced : placedAt first component = true)
    (secondPlaced : placedAt second component = true) : first = second := by
  simp only [placedAt, beq_iff_eq] at firstPlaced secondPlaced
  rw [firstPlaced, Option.some.injEq] at secondPlaced
  exact secondPlaced

/-- **The step before the last**: a place reached in one more step is placed under a marker sitting at a place reached
in that many steps. -/
theorem ReachesIn.prefix : ∀ {steps : Nat} {components : List Pattern} {place target : Pattern},
    ReachesIn (steps + 1) components place target →
    ∃ marker ∈ components, childOf marker = some target ∧ ∃ parent, placedAt parent marker = true ∧
      ReachesIn steps components place parent
  | 0, components, place, target, reached => by
      cases reached with
      | down member isPlaced isChild below =>
          cases below
          exact ⟨_, member, isChild, place, isPlaced, .here⟩
  | steps + 1, components, place, target, reached => by
      cases reached with
      | down member isPlaced isChild below =>
          obtain ⟨last, inFiltered, lastChild, parent, parentPlaced, reachedParent⟩ := ReachesIn.prefix below
          exact ⟨last, (List.mem_filter.mp inFiltered).1, lastChild, parent, parentPlaced,
            .down member isPlaced isChild reachedParent⟩

/-- **Below a place, one location of each marker there leads to a place**: two markers sitting at a place whose
locations reach one place, among the components placed elsewhere, are one, when every location has one marker. -/
theorem reaches_unique {whole : List Pattern}
    (unique : ∀ first ∈ whole, ∀ second ∈ whole, ∀ child, childOf first = some child → childOf second = some child →
      first = second)
    {components : List Pattern} (inWhole : ∀ component ∈ components, component ∈ whole) {place : Pattern} :
    ∀ (steps : Nat) {first second target : Pattern},
      ReachesIn steps (components.filter fun other => !placedAt place other) first target →
      Reaches (components.filter fun other => !placedAt place other) second target →
      (∃ marker ∈ whole, placedAt place marker = true ∧ childOf marker = some first) →
      (∃ marker ∈ whole, placedAt place marker = true ∧ childOf marker = some second) → first = second
  | 0, first, second, target, reachedFirst, reachedSecond, ⟨firstMarker, firstWhole, firstPlaced, firstChild⟩,
      secondMarker => by
      cases reachedFirst
      by_contra different
      obtain ⟨last, inFiltered, lastChild⟩ := reachedSecond.last (Ne.symm different)
      have same := unique last (inWhole _ (List.mem_filter.mp inFiltered).1) firstMarker firstWhole _ lastChild firstChild
      subst same
      simp [firstPlaced] at inFiltered
  | steps + 1, first, second, target, reachedFirst, reachedSecond, firstMarker,
      ⟨secondMarker, secondWhole, secondPlaced, secondChild⟩ => by
      obtain ⟨last, inFiltered, lastChild, parent, parentPlaced, reachedParent⟩ := reachedFirst.prefix
      have lastWhole := inWhole _ (List.mem_filter.mp inFiltered).1
      by_cases atTarget : second = target
      · subst atTarget
        have same := unique last lastWhole secondMarker secondWhole _ lastChild secondChild
        subst same
        simp [secondPlaced] at inFiltered
      · obtain ⟨steps', reachedSteps⟩ := reachedSecond.steps
        cases steps' with
        | zero => cases reachedSteps; exact absurd rfl atTarget
        | succ steps' =>
            obtain ⟨last', inFiltered', lastChild', parent', parentPlaced', reachedParent'⟩ := reachedSteps.prefix
            have same := unique last lastWhole last' (inWhole _ (List.mem_filter.mp inFiltered').1) _ lastChild lastChild'
            subst same
            have sameParent := placedAt_same parentPlaced parentPlaced'
            subst sameParent
            exact reaches_unique unique inWhole steps reachedParent (reachedParent'.reaches) firstMarker
              ⟨secondMarker, secondWhole, secondPlaced, secondChild⟩

/-- **Components sitting at no reached place are never read**: added to a list, they change no reading. -/
theorem readPlaced_unreached : ∀ (fuel : Nat) (place : Pattern) (first second : List Pattern),
    (∀ component ∈ second, ∀ at', placeAt component = some at' → ¬ Reaches (first ++ second) place at') →
    readPlaced fuel place (first ++ second) = readPlaced fuel place first
  | 0, _, _, _, _ => rfl
  | fuel + 1, place, first, second, unreached => by
      rw [readPlaced_succ, readPlaced_succ]
      simp only [List.filter_append]
      have nothingHere : second.filter (placedAt place) = [] := by
        rw [List.filter_eq_nil_iff]
        intro component member isPlaced
        exact unreached component member place (by simpa [placedAt] using isPlaced) .here
      rw [nothingHere, List.append_nil]
      refine List.map_congr_left fun component inFiltered => ?_
      obtain ⟨inFirst, isPlaced⟩ := List.mem_filter.mp inFiltered
      cases fuel with
      | zero => rfl
      | succ fuel =>
          refine readComponent_congr fun child isChild => ?_
          exact readPlaced_unreached fuel child _ _ fun other inSecond at' otherPlaced reached =>
            unreached other (List.mem_filter.mp inSecond).1 at' otherPlaced
              (.down (List.mem_append_left _ inFirst) isPlaced isChild (by rw [List.filter_append]; exact reached))

/-! ## Restrictions nothing uses -/

open Mettapedia.OSLF.MeTTaIL.Substitution (liftBVars)
open Mettapedia.GSLT.LanguageDef.WellSorted (HasType FreeTypeContext)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex ProcEquiv garbage_equivalent restrict_fill lift_typed
  liftBVars_zero_add)
open Mettapedia.Languages.ProcessCalculi.Ambient.Full (ambientBlock)
open Mettapedia.Languages.ProcessCalculi.Ambient.Encoding (nameType procType)

/-- **Restrictions nothing uses are garbage**: `(νx̄) Q↑ ≡ Q`. -/
theorem restricts_lift_equivalent {free : FreeTypeContext} : ∀ (count : Nat) {bound : List TypeExpr} {process : Pattern},
    HasType ambientCoreCalc free bound process procType →
    ProcEquiv ambientCoreCalc ambientBlock free bound
      (Prenex.restricts ambientBlock count (liftBVars 0 count process)) process
  | 0, _, process, _ => by
      simp only [Prenex.restricts, Mettapedia.OSLF.MeTTaIL.Substitution.liftBVars_zero]
      exact .refl _
  | count + 1, bound, process, typed => by
      have lifted : HasType ambientCoreCalc free (nameType :: bound) (liftBVars 0 1 process) procType := by
        simpa using lift_typed (language := ambientCoreCalc) (inner := []) (inserted := [nameType]) (outer := bound) typed
      have inner := restricts_lift_equivalent count lifted
      rw [liftBVars_zero_add] at inner
      rw [Prenex.restricts_succ]
      exact .trans _ _ _ (restrict_fill (language := ambientCoreCalc) (block := ambientBlock) inner)
        (garbage_equivalent (language := ambientCoreCalc) (block := ambientBlock) typed)

end Mettapedia.Languages.ProcessCalculi.Ambient.Decoding
