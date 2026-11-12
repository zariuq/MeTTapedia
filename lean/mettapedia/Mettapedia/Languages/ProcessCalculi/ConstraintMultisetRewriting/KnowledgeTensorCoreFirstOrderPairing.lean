import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.KnowledgeTensorCoreNeutral
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FirstOrderContextRuns

/-!
# Framing a first-order run by a pair of contexts is framing it twice

First-order configurations have a tensor, so two contexts have a pair. The grade of a run beside
the pair is the grade, beside the second context, of the run placed beside the first.

* `WordChecks`: the checks of a word of firings beside a context, from a configuration.
  `checks_iff_wordChecks`: the grade of a run is the checks of its word.
* `contextChecks_congr`, `wordChecks_congr`: the checks depend only on the solutions and the
  present occurrences of the configuration.
* `wordChecks_pair`, `checks_pair`: **a run is in its grade beside the pair exactly when it
  neither takes from the first context nor makes into it, and the same firings, run from the
  pairing with the first context, are in their grade beside the second.**
* `checks_pair_of_plan`: the same law at the placed run of a plan.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.FirstOrder

open AnnotatedRuns (Firing firstOrder firstOrderTransport)
open GuardFreeProcessOrders (SameUpTo)
open FirstOrderNativeRuns

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  (A : SubstitutionAction T S) (label : O → T)

/-- The checks of a word of firings beside a context: each firing leaves the context in place and
passes its checks beside it, at the configuration the word has reached. -/
def WordChecks (right : Configuration T O) : Configuration T O → List (Firing T S O) → Prop
  | _, [] => True
  | left, f :: rest =>
      (Disjoint f.selection.taken.toFinset right.present ∧ ContextChecks A label left right f) ∧
        WordChecks right (f.result label left) rest

/-- **The grade of a run is the checks of its word.** -/
theorem checks_iff_wordChecks (right : Configuration T O) :
    ∀ {left : Configuration T O} (run : (firstOrder A label).toStep.Run left),
      (contextualRunInterpretation A label).Checks (left := left) (right := right) PUnit.unit run ↔
        WordChecks A label right left (sites A label run)
  | _, .nil _ => Iff.rfl
  | _, .cons _ _ rest => by
      have ih := checks_iff_wordChecks right rest
      show (_ ∧ _) ↔ (_ ∧ _)
      exact and_congr Iff.rfl ih

/-- The checks of a firing beside a context depend only on the solutions and the present
occurrences of the configuration. -/
theorem contextChecks_congr {C D : Configuration T O} (same : SameUpTo A C D)
    (right : Configuration T O) (f : Firing T S O) :
    ContextChecks A label C right f ↔ ContextChecks A label D right f := by
  have problems : A.Equivalent (f.selection.problem label f.rule (AnnotatedRuns.tensor C right))
      (f.selection.problem label f.rule (AnnotatedRuns.tensor D right)) := by
    rw [GuardFreeProcessOrders.problem_eq, GuardFreeProcessOrders.problem_eq]
    exact GuardFreeProcessOrders.equivalent_append A
      (GuardFreeProcessOrders.equivalent_append A same.1 right.equations) _
  unfold ContextChecks
  rw [same.2]
  constructor
  · rintro ⟨fresh, ⟨σ, solved⟩, guards, queries⟩
    exact ⟨fresh, ⟨σ, (problems σ).mp solved⟩,
      fun check member τ later => guards check member τ ((problems τ).mpr later),
      fun query member τ later => queries query member τ ((problems τ).mpr later)⟩
  · rintro ⟨fresh, ⟨σ, solved⟩, guards, queries⟩
    exact ⟨fresh, ⟨σ, (problems σ).mpr solved⟩,
      fun check member τ later => guards check member τ ((problems τ).mp later),
      fun query member τ later => queries query member τ ((problems τ).mp later)⟩

/-- The checks of a word depend only on the solutions and the present occurrences of the
configuration it starts from. -/
theorem wordChecks_congr (right : Configuration T O) :
    ∀ (word : List (Firing T S O)) {C D : Configuration T O}, SameUpTo A C D →
      (WordChecks A label right C word ↔ WordChecks A label right D word)
  | [], _, _, _ => Iff.rfl
  | f :: rest, C, D, same => by
      have ih := wordChecks_congr right rest (AnnotatedRuns.Firing.result_congr A label f same)
      show ((Disjoint f.selection.taken.toFinset right.present ∧
            ContextChecks A label C right f) ∧ WordChecks A label right (f.result label C) rest) ↔
        ((Disjoint f.selection.taken.toFinset right.present ∧
            ContextChecks A label D right f) ∧ WordChecks A label right (f.result label D) rest)
      rw [contextChecks_congr A label same right f, ih]

/-- **Framing a word by a pair of contexts is framing it twice.** -/
theorem wordChecks_pair (first second : Configuration T O) :
    ∀ (word : List (Firing T S O)) {C D : Configuration T O},
      SameUpTo A D (AnnotatedRuns.tensor C first) →
      (WordChecks A label (AnnotatedRuns.tensor first second) C word ↔
        (∀ f ∈ word, Disjoint f.selection.taken.toFinset first.present ∧
          Disjoint f.selection.made.toFinset first.present) ∧
          WordChecks A label second D word)
  | [], _, _, _ => ⟨fun _ => ⟨fun _ member => (by cases member), trivial⟩, fun _ => trivial⟩
  | f :: rest, C, D, same => by
      have here : ContextChecks A label C (AnnotatedRuns.tensor first second) f ↔
          Disjoint f.selection.made.toFinset first.present ∧ ContextChecks A label D second f := by
        rw [contextChecks_pair A label C first second f, contextChecks_congr A label same second f]
      have takes : Disjoint f.selection.taken.toFinset (AnnotatedRuns.tensor first second).present ↔
          Disjoint f.selection.taken.toFinset first.present ∧
            Disjoint f.selection.taken.toFinset second.present :=
        Finset.disjoint_union_right
      have next : Disjoint f.selection.taken.toFinset first.present →
          SameUpTo A (f.result label D) (AnnotatedRuns.tensor (f.result label C) first) :=
        fun takenFirst => SameUpTo.trans A (AnnotatedRuns.Firing.result_congr A label f same)
          (AnnotatedRuns.tensor_result_left A label takenFirst)
      show ((Disjoint f.selection.taken.toFinset (AnnotatedRuns.tensor first second).present ∧
            ContextChecks A label C (AnnotatedRuns.tensor first second) f) ∧
          WordChecks A label (AnnotatedRuns.tensor first second) (f.result label C) rest) ↔
        (∀ g ∈ f :: rest, Disjoint g.selection.taken.toFinset first.present ∧
          Disjoint g.selection.made.toFinset first.present) ∧
          ((Disjoint f.selection.taken.toFinset second.present ∧
            ContextChecks A label D second f) ∧ WordChecks A label second (f.result label D) rest)
      constructor
      · rintro ⟨⟨taken, checked⟩, later⟩
        obtain ⟨takenFirst, takenSecond⟩ := takes.mp taken
        obtain ⟨madeFirst, checkedSecond⟩ := here.mp checked
        obtain ⟨restApart, restChecked⟩ :=
          (wordChecks_pair first second rest (next takenFirst)).mp later
        refine ⟨?_, ⟨takenSecond, checkedSecond⟩, restChecked⟩
        intro g member
        rcases List.mem_cons.mp member with rfl | inRest
        · exact ⟨takenFirst, madeFirst⟩
        · exact restApart g inRest
      · rintro ⟨apart, ⟨takenSecond, checkedSecond⟩, restChecked⟩
        obtain ⟨takenFirst, madeFirst⟩ := apart f (List.mem_cons.mpr (Or.inl rfl))
        exact ⟨⟨takes.mpr ⟨takenFirst, takenSecond⟩, here.mpr ⟨madeFirst, checkedSecond⟩⟩,
          (wordChecks_pair first second rest (next takenFirst)).mpr
            ⟨fun g member => apart g (List.mem_cons.mpr (Or.inr member)), restChecked⟩⟩

/-- **Framing a run by a pair of contexts is framing it twice.** A run is in its grade beside the
pair exactly when it neither takes from the first context nor makes into it, and a run of the
same firings from the pairing with the first context is in its grade beside the second. -/
theorem checks_pair {left first second : Configuration T O}
    (run : (firstOrder A label).toStep.Run left) {start : Configuration T O}
    (native : (firstOrder A label).toStep.Run start)
    (same : SameUpTo A start (AnnotatedRuns.tensor left first))
    (word : sites A label native = sites A label run) :
    (contextualRunInterpretation A label).Checks (left := left)
        (right := AnnotatedRuns.tensor first second) PUnit.unit run ↔
      (∀ f ∈ sites A label run, Disjoint f.selection.taken.toFinset first.present ∧
        Disjoint f.selection.made.toFinset first.present) ∧
        (contextualRunInterpretation A label).Checks (left := start) (right := second)
          PUnit.unit native := by
  rw [checks_iff_wordChecks A label _ run, checks_iff_wordChecks A label _ native, word]
  exact wordChecks_pair A label first second (sites A label run) same

/-- The same law at the placed run of a plan. -/
theorem checks_pair_of_plan {left first second : Configuration T O}
    (run : (firstOrder A label).toStep.Run left)
    (plan : (contextualRunInterpretation A label).Plan (right := first) PUnit.unit run) :
    (contextualRunInterpretation A label).Checks (left := left)
        (right := AnnotatedRuns.tensor first second) PUnit.unit run ↔
      (∀ f ∈ sites A label run, Disjoint f.selection.taken.toFinset first.present ∧
        Disjoint f.selection.made.toFinset first.present) ∧
        (contextualRunInterpretation A label).Checks (left := AnnotatedRuns.tensor left first)
          (right := second) PUnit.unit
          (plan.realize (contextualRunInterpretation A label) PUnit.unit run).execution :=
  checks_pair A label run _ (SameUpTo.refl A _) (plan_sites A label PUnit.unit run plan)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.KnowledgeTensorCore.FirstOrder
