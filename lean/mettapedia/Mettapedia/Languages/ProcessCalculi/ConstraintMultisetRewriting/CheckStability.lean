import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceStep
import Mettapedia.Machines.ConstraintPropagation.ResidualChecks

/-!
# Certain checks, unresolved checks and constraint refinement

A check is discharged only when it holds in every remaining solution. A
refuted check fails in every remaining solution. An unresolved check remains
in the store. The existing residual-check pass preserves this interpretation
under further equation refinement, relative to the same occurrence world.

The count profile here counts resolved occurrences in every solution. Counting
potential unification answers is a different observation and is not identified
with this one. New arrivals or removals likewise change the occurrence world.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

open Mettapedia.Machines.ConstraintPropagation
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO}

namespace Check

def Unresolved (A : SubstitutionAction T S) (equations : EquationStore T)
    (label : O → T) (world : Finset O) (check : Check T) : Prop :=
  ¬ A.Entails equations (fun σ => check.Holds A σ label world) ∧
  ¬ A.Entails equations (fun σ => ¬ check.Holds A σ label world)

/-- Sound readiness is a statement about all completions, rather than a test
that the current variable happens to have no conflicting binding. -/
def ProbeSound (A : SubstitutionAction T S) (equations : EquationStore T)
    (label : O → T) (world : Finset O) (probe : Check T → Option Bool) : Prop :=
  ∀ check b, probe check = some b →
    A.Entails equations (fun σ => check.Holds A σ label world ↔ b = true)

theorem probe_sound_of_refines (A : SubstitutionAction T S)
    {early late : EquationStore T} (refinement : A.Refines late early)
    {label : O → T} {world : Finset O} {probe : Check T → Option Bool}
    (sound : ProbeSound A early label world probe) : ProbeSound A late label world probe :=
  fun check b ready => A.entails_of_refines refinement (sound check b ready)

theorem unresolved_not_discharged (A : SubstitutionAction T S)
    {equations : EquationStore T} {label : O → T} {world : Finset O}
    {probe : Check T → Option Bool} (sound : ProbeSound A equations label world probe)
    {check : Check T} (unresolved : Unresolved A equations label world check) :
    probe check = none := by
  cases ready : probe check with
  | none => rfl
  | some b =>
    have result := sound check b ready
    cases b with
    | true => exact False.elim (unresolved.1 (fun σ model => (result σ model).mpr rfl))
    | false => exact False.elim (unresolved.2 (fun σ model holds => by
        have impossible := (result σ model).mp holds
        cases impossible))

/-- Completed passes preserve each later solution's obligations. Checks whose
variables disappear from the output still occur in the original check list. -/
theorem discharge_preserves_later_models (A : SubstitutionAction T S)
    {early late : EquationStore T} (refinement : A.Refines late early)
    {label : O → T} {world : Finset O} {probe : Check T → Option Bool}
    (sound : ProbeSound A early label world probe) (checks : List (Check T))
    (σ : S) (model : A.Models σ late) :
    ResidualChecks.OutcomeHolds (fun check => check.Holds A σ label world)
      (ResidualChecks.discharge probe checks) ↔
      ResidualChecks.Holds (fun check => check.Holds A σ label world) checks :=
  ResidualChecks.discharge_correct _ probe
    (fun check b ready => sound check b ready σ (refinement σ model)) checks

/-- Definite absence is exactly non-unifiability of every occurrence under
the same current equations. This is stable under equation refinement only
while the occurrence world and the equality theory stay fixed. -/
theorem entails_absent_iff_apart (A : SubstitutionAction T S) (equations : EquationStore T)
    (label : O → T) (world : Finset O) (pattern : T) :
    A.Entails equations (fun σ => (Check.absent pattern).Holds A σ label world) ↔
      ∀ o ∈ world, A.Apart equations pattern (label o) := by
  constructor
  · intro absent o member
    rintro ⟨σ, solved⟩
    obtain ⟨old, equation⟩ := (A.models_append _ _ _).mp solved
    exact absent σ old o member (equation (pattern, label o) (by simp))
  · intro apart σ solved o member same
    apply apart o member
    refine ⟨σ, (A.models_append _ _ _).mpr ⟨solved, ?_⟩⟩
    intro equation inSingleton
    have equal : equation = (pattern, label o) := by simpa using inSingleton
    subst equation
    exact same

/-- A scan retains every potentially matching physical occurrence, in every
solution of the current store. This is a coverage contract, not a claim that
an unfinished search has found all answers. -/
def CoversMatches (A : SubstitutionAction T S) (equations : EquationStore T)
    (label : O → T) (visible world : Finset O) (pattern : T) : Prop :=
  ∀ σ, A.Models σ equations → ∀ o ∈ world,
    A.E (A.apply σ pattern) (A.apply σ (label o)) → o ∈ visible

/-- Omitted rows are harmless precisely when none can match under the joint
constraints. This permits a certified candidate filter to justify a scan. -/
theorem coversMatches_iff_omitted_apart (A : SubstitutionAction T S)
    (equations : EquationStore T) (label : O → T) (visible world : Finset O) (pattern : T) :
    CoversMatches A equations label visible world pattern ↔
      ∀ o ∈ world, o ∉ visible → A.Apart equations pattern (label o) := by
  constructor
  · intro covered o member omitted
    rintro ⟨σ, model⟩
    obtain ⟨old, extra⟩ := (A.models_append _ _ _).mp model
    exact omitted (covered σ old o member (extra _ (List.mem_singleton_self _)))
  · intro apart σ model o member same
    by_contra omitted
    apply apart o member omitted
    refine ⟨σ, (A.models_append _ _ _).mpr ⟨model, ?_⟩⟩
    intro equation inSingleton
    have only := List.mem_singleton.mp inSingleton
    subst equation
    exact same

theorem CoversMatches.refines (A : SubstitutionAction T S)
    {early late : EquationStore T} (refinement : A.Refines late early)
    {label : O → T} {visible world : Finset O} {pattern : T}
    (covered : CoversMatches A early label visible world pattern) :
    CoversMatches A late label visible world pattern :=
  fun σ model => covered σ (refinement σ model)

/-- Covered scans preserve actual occurrence counts, as well as emptiness.
Equal-valued rows retain their separate physical identities. -/
theorem region_eq_of_covered [DecidableEq O] (A : SubstitutionAction T S)
    {equations : EquationStore T} {label : O → T} {visible world : Finset O} {pattern : T}
    (included : visible ⊆ world) (covered : CoversMatches A equations label visible world pattern)
    (σ : S) (model : A.Models σ equations) :
    «matches» A σ label visible pattern = «matches» A σ label world pattern := by
  classical
  ext o
  simp only [«matches», Finset.mem_filter]
  exact ⟨fun h => ⟨included h.1, h.2⟩, fun h => ⟨covered σ model o h.1 h.2, h.2⟩⟩

/-- A negative scan is sound only with the coverage argument. Equations and
the observed occurrence world are the same on both sides. -/
theorem entails_absent_iff_of_covered (A : SubstitutionAction T S)
    {equations : EquationStore T} {label : O → T} {visible world : Finset O} {pattern : T}
    (included : visible ⊆ world) (covered : CoversMatches A equations label visible world pattern) :
    A.Entails equations (fun σ => (absent pattern).Holds A σ label visible) ↔
      A.Entails equations (fun σ => (absent pattern).Holds A σ label world) := by
  constructor
  · intro holds σ model o member same
    exact holds σ model o (covered σ model o member same) same
  · intro holds σ model o member
    exact holds σ model o (included member)

theorem entails_count_iff_of_covered [DecidableEq O] (A : SubstitutionAction T S)
    {equations : EquationStore T} {label : O → T} {visible world : Finset O} {pattern : T}
    (included : visible ⊆ world) (covered : CoversMatches A equations label visible world pattern)
    (number : Nat) :
    A.Entails equations (fun σ => (count pattern number).Holds A σ label visible) ↔
      A.Entails equations (fun σ => (count pattern number).Holds A σ label world) := by
  constructor <;> intro holds σ model
  · change («matches» A σ label world pattern).card = number
    rw [← region_eq_of_covered A included covered σ model]
    exact holds σ model
  · change («matches» A σ label visible pattern).card = number
    rw [region_eq_of_covered A included covered σ model]
    exact holds σ model

/-- Equation refinement and adding only provably nonmatching occurrences
preserve a negative observation. Adding an arbitrary row is not allowed. -/
theorem absent_after_refinement_and_extension [DecidableEq O] (A : SubstitutionAction T S)
    {early late : EquationStore T} (refinement : A.Refines late early)
    {label : O → T} {world added : Finset O} {pattern : T}
    (absentNow : A.Entails early (fun σ => (absent pattern).Holds A σ label world))
    (newApart : ∀ o ∈ added, A.Apart late pattern (label o)) :
    A.Entails late (fun σ => (absent pattern).Holds A σ label (world ∪ added)) := by
  intro σ model o member
  rcases Finset.mem_union.mp member with old | new
  · exact absentNow σ (refinement σ model) o old
  · exact ((entails_absent_iff_apart A late label added pattern).mpr newApart) σ model o new

/-- A resource update cannot change this check's matching occurrences under
the stated joint constraints. Equality checks do not inspect occurrences. -/
def IgnoresWrites (A : SubstitutionAction T S) (equations : EquationStore T)
    (label : O → T) (selection : Selection O) : Check T → Prop
  | .equal _ _ => True
  | .absent pattern | .count pattern _ =>
      ∀ o ∈ selection.taken ++ selection.made, A.Apart equations pattern (label o)

private theorem no_match_of_apart (A : SubstitutionAction T S)
    {equations : EquationStore T} {pattern value : T} (apart : A.Apart equations pattern value)
    (σ : S) (model : A.Models σ equations) : ¬ A.E (A.apply σ pattern) (A.apply σ value) := by
  intro same
  apply apart
  refine ⟨σ, (A.models_append _ _ _).mpr ⟨model, ?_⟩⟩
  intro equation member
  have only := List.mem_singleton.mp member
  subst equation
  exact same

theorem region_fire_eq_of_apart [DecidableEq O] (A : SubstitutionAction T S)
    {equations : EquationStore T} {label : O → T} (world : Finset O)
    (selection : Selection O) {pattern : T}
    (apart : ∀ o ∈ selection.taken ++ selection.made, A.Apart equations pattern (label o))
    (σ : S) (model : A.Models σ equations) :
    «matches» A σ label (fire world (selection.commit (T := T))) pattern = «matches» A σ label world pattern := by
  classical
  ext o
  simp only [«matches», Finset.mem_filter]
  constructor
  · rintro ⟨present, same⟩
    rcases mem_fire.mp present with ⟨old, _⟩ | made
    · exact ⟨old, same⟩
    · have member : o ∈ selection.made := by simpa [Selection.commit] using made
      exact False.elim (no_match_of_apart A (apart o (List.mem_append_right _ member)) σ model same)
  · rintro ⟨present, same⟩
    refine ⟨mem_fire.mpr (Or.inl ⟨present, ?_⟩), same⟩
    intro taken
    have member : o ∈ selection.taken := by simpa [Selection.commit] using taken
    exact no_match_of_apart A (apart o (List.mem_append_left _ member)) σ model same

/-- Guard stability is derived from excluded matching writes, rather than
supplied as equality of the two guard verdicts. -/
theorem holds_fire_iff_of_ignored [DecidableEq O] (A : SubstitutionAction T S)
    {equations : EquationStore T} {label : O → T} (world : Finset O)
    (selection : Selection O) (check : Check T)
    (ignored : IgnoresWrites A equations label selection check)
    (σ : S) (model : A.Models σ equations) :
    check.Holds A σ label (fire world (selection.commit (T := T))) ↔ check.Holds A σ label world := by
  cases check with
  | equal left right => rfl
  | absent pattern =>
      have same := region_fire_eq_of_apart A world selection ignored σ model
      have absent_iff (current : Finset O) :
          (Check.absent pattern).Holds A σ label current ↔ «matches» A σ label current pattern = ∅ := by
        classical
        simp only [Holds, «matches», Finset.filter_eq_empty_iff]
      rw [absent_iff, absent_iff, same]
  | count pattern number =>
      change («matches» A σ label (fire world (selection.commit (T := T))) pattern).card = number ↔
        («matches» A σ label world pattern).card = number
      rw [region_fire_eq_of_apart A world selection ignored σ model]

end Check

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
