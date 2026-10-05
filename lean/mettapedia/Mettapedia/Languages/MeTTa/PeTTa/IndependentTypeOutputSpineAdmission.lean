import Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutputSpineRecursive
import Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutputNativeAdmission
import Mettapedia.Languages.MeTTa.PeTTa.IntrinsicTypeTraversalMemoized

/-!
# Incremental-spine admission and independent-output publication

The recursive incremental relation is connected here to the existing
caller-coordinate, answer-materialization, and retained-traversal interfaces.
All equalities preserve the full ordered answer vector. Fuel bounds describe
complete finite approximations; no resource failure becomes normal empty
exhaustion. The native coordinate theorems concern mathematical identities,
not a formal verification of C allocation, ownership, or unification.

The retained walk retains its own operation trace and weighted work theorem.
Semantic transparency transfers to the incremental relation. This does not
identify the operation counts of eager rejection and an incremental row's
possibly longer failing prefix.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutput.SpineAdmission

open Mettapedia.Logic.LP
open Mettapedia.Logic.LP.IndependentOutputUnification
open IntrinsicTypeFacts (signature TypeTerm Declaration)
open Structural SpineRecursive NativeAdmission

private theorem independent_disjoint (subject : TypeTerm) (output : Nat)
    (independent : output ∉ subject.freeVars) :
    Disjoint subject.freeVars (Term.var output : TypeTerm).freeVars := by
  apply Finset.disjoint_left.mpr
  intro name inSource inOutput
  exact independent ((Term.mem_freeVars_var (σ := signature)).mp inOutput ▸ inSource)

/-- The root shortcut remains valid with recursively incremental structural
queries. Both sides are genuine recursive evaluations, not a wrapper around
the old child service. Separate sufficient budgets are allowed. -/
theorem completed_publication_exact (library : List Declaration)
    (boundFuel freshFuel : Nat) (path : Path) (subject : TypeTerm) (output : Nat)
    (sourceApart : AllocationApart path subject)
    (outputApart : AllocationApart path (.var output)) (independent : output ∉ subject.freeVars)
    (boundEnough : subject.size < boundFuel) (freshEnough : subject.size < freshFuel)
    (bound fresh : List TypeTerm)
    (boundRun : runSpine library boundFuel path subject (some (.var output)) = some bound)
    (freshRun : runSpine library freshFuel path subject none = some fresh)
    (observations : List TypeTerm)
    (observationsApart : ∀ term ∈ observations, AllocationApart path term) :
    bound.map (fun answer => solutions [(answer, .var output)] observations) =
      fresh.map (fun answer => solutions [(answer, .var output)] observations) := by
  apply Root.completed_publication_exact library boundFuel freshFuel path subject output sourceApart
    outputApart independent bound fresh _ _ observations observationsApart
  · rw [recursive_spine_equivalence library boundFuel path subject (some (.var output)) sourceApart
      (by simpa using independent_disjoint subject output independent) (by simpa using outputApart) boundEnough]
    exact boundRun
  · rw [recursive_spine_equivalence library freshFuel path subject none sourceApart (by simp) (by simp) freshEnough]
    exact freshRun

/-- Native caller coordinates discharge allocation exclusion without
renaming one caller variable to a different caller variable. -/
theorem caller_allocation_apart (path : Path) (subject : TypeTerm) :
    AllocationApart path (callerTerm subject) := by
  apply Root.caller_term_allocation_apart
  intro name present
  obtain ⟨original, _, same⟩ := caller_term_names subject name present
  exact ⟨original, same⟩

private theorem caller_output_apart (path : Path) (output : Nat) :
    AllocationApart path (.var (callerName output)) := by
  apply Root.caller_term_allocation_apart
  intro name present
  exact ⟨output, (Term.mem_freeVars_var (σ := signature)).mp present⟩

/-- Whole-vector inventory materialization composes with the recursive
spine repair. Aliases shared between answer occurrences remain shared;
all caller coordinates, including repeated observations, stay fixed. -/
theorem completed_inventory_publication_exact (library : List Declaration)
    (boundFuel freshFuel : Nat) (path : Path) (subject : TypeTerm) (output : Nat)
    (independent : output ∉ subject.freeVars) (identity : Nat) (inventory : List Nat)
    (boundEnough : (callerTerm subject).size < boundFuel)
    (freshEnough : (callerTerm subject).size < freshFuel)
    (bound fresh : List TypeTerm)
    (boundRun : runSpine library boundFuel path (callerTerm subject)
      (some (.var (callerName output))) = some bound)
    (freshRun : runSpine library freshFuel path (callerTerm subject) none = some fresh)
    (observations : List TypeTerm) :
    bound.map (fun answer => solutions [(answer, .var (callerName output))]
      (observations.map callerTerm)) =
    (materialize identity inventory fresh).map (fun answer =>
      solutions [(answer, .var (callerName output))] (observations.map callerTerm)) := by
  apply NativeAdmission.completed_inventory_publication_exact library boundFuel freshFuel path subject output
    independent identity inventory bound fresh _ _ observations
  · rw [recursive_spine_equivalence library boundFuel path (callerTerm subject)
      (some (.var (callerName output))) (caller_allocation_apart path subject)
      (by simpa using (independent_disjoint (callerTerm subject) (callerName output)
        (caller_term_independent subject output independent)))
      (by simpa using caller_output_apart path output) boundEnough]
    exact boundRun
  · rw [recursive_spine_equivalence library freshFuel path (callerTerm subject) none
      (caller_allocation_apart path subject) (by simp) (by simp) freshEnough]
    exact freshRun

/-- The existing retained traversal computes the same completed ordered
answers as recursive incremental typing. Cache refusal and misses are
unrestricted; stored facts must satisfy the existing validity invariant. -/
theorem memoized_spine_exact (library : List Declaration) (admit : Memoized.ClosedKey → Bool)
    (retained : Memoized.ClosedKey → Option (List TypeTerm))
    (sound : ∀ key facts, retained key = some facts → facts = Memoized.closedFacts library key)
    (fuel : Nat) (demand : Memoized.Demand)
    (sourceApart : AllocationApart demand.path demand.subject)
    (requiredApart : ∀ term ∈ demand.required.toList, Disjoint demand.subject.freeVars term.freeVars)
    (requiredFresh : ∀ term ∈ demand.required.toList, AllocationApart demand.path term)
    (enough : demand.subject.size < fuel) :
    (Memoized.walk library admit retained fuel demand).answer =
      runSpine library fuel demand.path demand.subject demand.required := by
  rw [Memoized.walk_exact library admit retained sound fuel demand]
  exact recursive_spine_equivalence library fuel demand.path demand.subject demand.required
    sourceApart requiredApart requiredFresh enough

/-- The retained walk's weighted frontier bound and its incremental-query
semantics hold together. Concrete residency is required at each visited
boundary; bounded capacity alone is not a residency proof. The work is the
retained walk's trace, not an assertion that different row schedules have
identical operation counts. -/
theorem warm_memoized_spine (library : List Declaration) (admit : Memoized.ClosedKey → Bool)
    (retained : Memoized.ClosedKey → Option (List TypeTerm))
    (sound : ∀ key facts, retained key = some facts → facts = Memoized.closedFacts library key)
    (fuel : Nat) (demand : Memoized.Demand) (model : Memoized.CostModel)
    (covered : Memoized.Covers retained (Memoized.frontier library admit fuel demand).events)
    (sourceApart : AllocationApart demand.path demand.subject)
    (requiredApart : ∀ term ∈ demand.required.toList, Disjoint demand.subject.freeVars term.freeVars)
    (requiredFresh : ∀ term ∈ demand.required.toList, AllocationApart demand.path term)
    (enough : demand.subject.size < fuel) :
    (Memoized.walk library admit retained fuel demand).answer =
        runSpine library fuel demand.path demand.subject demand.required ∧
    Memoized.executionWork model (Memoized.walk library admit retained fuel demand).events =
      Memoized.frontierWork model (Memoized.frontier library admit fuel demand).events +
      Memoized.boundaryWork model (Memoized.frontier library admit fuel demand).events +
      model.copyNode * Memoized.materializedWork (Memoized.frontier library admit fuel demand).events := by
  exact ⟨memoized_spine_exact library admit retained sound fuel demand sourceApart
      requiredApart requiredFresh enough,
    Memoized.warm_work_bound library admit retained fuel demand model covered⟩

/-- Sharing the result variable with the source fails the actual admission,
so the shared-output spine counterexample cannot enter this bridge. -/
example (output : Nat) :
    ¬ Disjoint (row [.var output]).freeVars (Term.var output : TypeTerm).freeVars := by
  intro disjoint
  exact Finset.disjoint_left.mp disjoint
    (show output ∈ (row [Term.var output]).freeVars by simp [row, Term.freeVars])
    (by simp [Term.freeVars])

/-- Distinct caller coordinates satisfy separation even when the source
contains the same caller variable more than once. -/
example :
    AllocationApart [] (callerTerm (row [.var 0, .var 0])) ∧
      Disjoint (callerTerm (row [.var 0, .var 0])).freeVars
        (Term.var (callerName 1) : TypeTerm).freeVars := by
  refine ⟨caller_allocation_apart [] _, independent_disjoint _ _ ?_⟩
  apply caller_term_independent
  simp [row, Term.freeVars, Fin.exists_fin_two]

end Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutput.SpineAdmission
