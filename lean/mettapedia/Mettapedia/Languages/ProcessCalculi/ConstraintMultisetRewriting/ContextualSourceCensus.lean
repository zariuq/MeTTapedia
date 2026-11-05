import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalClauses
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveAbsence
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternTermination

/-!
# Complete rejection of resolved source alternatives at one entry cut

Candidates enumerate physical take and read positions, with aliased reads
allowed. A rejection records a resource conflict, an actual solver
refutation or a countermodel to a guard. The joint problem retains incoming
and per-use stored conditions. An unfinished solver result is no rejection.

Output names are allocated fresh before this comparison. Replacing a
selection's output names preserves its information and guards, so the
census covers source enablement rather than one accidental allocation.
The candidate product is a finite reference contract, not a native join
strategy. Guard countermodels are proof certificates; no decision procedure
for arbitrary higher-order guards is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceCensus

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries

variable {S : Signature} {Local O : Type} {Γ : Ctx S} {sort : S.Srt}
    [DecidableEq O]

structure Request (locals : Local → MetaArity S)
    (before : ContextualConditionalExecution.State locals O Γ sort) : Type 1 where
  Query : Type
  queries : Query → MetaArity S
  equality : DecidableEq Query
  plan : ContextualPublication.Plan (Term (signature S (queryFamily queries before.declarations)) Γ sort)
  made : List O
  distinct : made.Nodup
  length : made.length = plan.rule.produce.length
  fresh : Disjoint made.toFinset before.present

variable {locals : Local → MetaArity S}
    {before : ContextualConditionalExecution.State locals O Γ sort}

namespace Request

abbrev Candidate (request : Request locals before) :=
  (Fin request.plan.rule.take.length → O) × (Fin request.plan.rule.read.length → O)

def candidates (request : Request locals before) : Finset request.Candidate :=
  (ContextualConjunctiveAbsence.candidates before.present request.plan.rule.take.length) ×ˢ
    (ContextualConjunctiveAbsence.candidates before.present request.plan.rule.read.length)

def selection (request : Request locals before) (chosen : request.Candidate) : Selection O :=
  ⟨List.ofFn chosen.1, List.ofFn chosen.2, request.made⟩

abbrev Admits (request : Request locals before) (picked : Selection O) :=
  ContextualConditionalSourceAdmission.Admitted request.queries locals before.declarations picked
    request.plan.rule before.rows before.equations before.present

def Enabled (request : Request locals before) : Prop := ∃ picked, request.Admits picked

theorem replace_output_names (request : Request locals before) {picked : Selection O}
    (admitted : request.Admits picked) : request.Admits {picked with made := request.made} :=
  ⟨admitted.take_distinct, request.distinct, admitted.take_shape, admitted.read_shape,
    request.length, admitted.taken_present, admitted.read_present, admitted.apart,
    request.fresh, admitted.solvable, admitted.checks⟩

def coordinates {count : Nat} (values : List O) (size : count = values.length) : Fin count → O :=
  fun port => values.get ⟨port.val, size ▸ port.isLt⟩

omit [DecidableEq O] in
theorem ofFn_coordinates {count : Nat} (values : List O) (size : count = values.length) :
    List.ofFn (coordinates values size) = values := by
  subst count
  exact List.ofFn_get values

theorem covers_selection (request : Request locals before) {picked : Selection O}
    (admitted : request.Admits picked) :
    ∃ chosen ∈ request.candidates, request.selection chosen = {picked with made := request.made} := by
  let chosen : request.Candidate :=
    ⟨coordinates picked.taken admitted.take_shape, coordinates picked.read admitted.read_shape⟩
  refine ⟨chosen, Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
  · apply (ContextualConjunctiveAbsence.mem_candidates before.present _).mpr
    intro port
    exact admitted.taken_present (List.mem_toFinset.mpr (List.get_mem _ _))
  · apply (ContextualConjunctiveAbsence.mem_candidates before.present _).mpr
    intro port
    exact admitted.read_present (List.mem_toFinset.mpr (List.get_mem _ _))
  · simp only [selection, chosen, ofFn_coordinates]

def information (request : Request locals before) (chosen : request.Candidate) :=
  ContextualConditionalSourceProblem.problem request.queries locals before.declarations
    (request.selection chosen) request.plan.rule before.rows before.equations

variable [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

def scan (request : Request locals before) (chosen : request.Candidate) (fuel : Nat) :=
  letI := request.equality
  letI := before.equality
  ContextualFrameWorklist.run fuel (family request.queries locals before.declarations)
    (request.information chosen)

def RefutedAt (request : Request locals before) (chosen : request.Candidate) (fuel : Nat) : Prop :=
  letI := request.equality
  letI := before.equality
  ∃ impossible, request.scan chosen fuel = .refuted impossible

def refutedB (request : Request locals before) (chosen : request.Candidate) (fuel : Nat) : Bool :=
  match request.scan chosen fuel with
  | .refuted _ => true
  | .residual _ => false

theorem refutedB_iff (request : Request locals before) (chosen : request.Candidate) (fuel : Nat) :
    request.refutedB chosen fuel = true ↔ request.RefutedAt chosen fuel := by
  let _ := request.equality
  let _ := before.equality
  dsimp only [refutedB, RefutedAt]
  cases request.scan chosen fuel with
  | refuted impossible => exact ⟨fun _ => ⟨impossible, rfl⟩, fun _ => rfl⟩
  | residual update =>
      constructor
      · intro accepted
        cases accepted
      · rintro ⟨impossible, refuted⟩
        cases refuted

inductive Rejected (request : Request locals before) (chosen : request.Candidate) : Prop where
  | aliased_take (conflict : ¬ (request.selection chosen).taken.Nodup)
  | take_read (conflict : ¬ Disjoint (request.selection chosen).taken.toFinset
      (request.selection chosen).read.toFinset)
  | equations (fuel : Nat) (refuted : request.RefutedAt chosen fuel)
  | guard (check : Check (Term (signature S (queryFamily request.queries before.declarations)) Γ sort))
      (member : check ∈ request.plan.rule.checks)
      (Future : Type) (future : Future → MetaArity S)
      (candidate : Assignment (family request.queries locals before.declarations) future)
      (model : ContextualResidual.Models candidate (request.information chosen))
      (failed : ¬ ContextualConditionalGuards.Holds locals candidate
        (ContextualConditionalSourceAdmission.sourceRows request.queries locals before.declarations before.rows)
        before.present (check.map (queryView request.queries locals before.declarations)))

theorem Rejected.no_admission {request : Request locals before} {chosen : request.Candidate}
    (rejected : request.Rejected chosen) : ¬ request.Admits (request.selection chosen) := by
  intro admitted
  cases rejected with
  | aliased_take conflict => exact conflict admitted.take_distinct
  | take_read conflict => exact conflict admitted.apart
  | equations fuel refuted =>
      obtain ⟨impossible, _⟩ := refuted
      obtain ⟨Future, future, candidate, model⟩ := admitted.solvable
      exact impossible future candidate model
  | guard check member Future future candidate model failed =>
      exact failed (admitted.checks check member Future future candidate model)

structure CertifiedEmpty (request : Request locals before) : Prop where
  rejected : ∀ chosen ∈ request.candidates, request.Rejected chosen

theorem CertifiedEmpty.no_source {request : Request locals before}
    (complete : request.CertifiedEmpty) : ¬ request.Enabled := by
  rintro ⟨picked, admitted⟩
  obtain ⟨chosen, present, shape⟩ := request.covers_selection admitted
  exact (complete.rejected chosen present).no_admission
    (shape.symm ▸ request.replace_output_names admitted)

theorem zero_fuel_is_not_a_refutation (request : Request locals before) (chosen : request.Candidate) :
    ¬ request.RefutedAt chosen 0 := by
  rintro ⟨impossible, computed⟩
  cases computed

/-- In the terminating equation fragment, rejection is complete when guard
failures are supplied as their actual countermodels. This is semantic
completeness of proof certificates, not an executable guard oracle. -/
theorem rejected_of_no_admission (request : Request locals before) (chosen : request.Candidate)
    (present : chosen ∈ request.candidates)
    (patterned : ContextualPatternFragment.ProblemPattern (request.information chosen))
    (denied : ¬ request.Admits (request.selection chosen)) : request.Rejected chosen := by
  classical
  let _ := request.equality
  let _ := before.equality
  by_cases distinct : (request.selection chosen).taken.Nodup
  · by_cases apart : Disjoint (request.selection chosen).taken.toFinset (request.selection chosen).read.toFinset
    · by_cases solvable : ContextualConditionalExecution.Solvable (request.information chosen)
      · by_contra unrejected
        apply denied
        have positions := Finset.mem_product.mp present
        have takePresent := (ContextualConjunctiveAbsence.mem_candidates before.present chosen.1).mp positions.1
        have readPresent := (ContextualConjunctiveAbsence.mem_candidates before.present chosen.2).mp positions.2
        refine ⟨distinct, request.distinct, by simp [selection], by simp [selection], request.length,
          ?_, ?_, apart, request.fresh, solvable, ?_⟩
        · intro occurrence member
          obtain ⟨port, rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp member)
          exact takePresent port
        · intro occurrence member
          obtain ⟨port, rfl⟩ := List.mem_ofFn.mp (List.mem_toFinset.mp member)
          exact readPresent port
        · intro check member
          by_contra failed
          unfold ContextualConditionalGuards.Ask at failed
          push Not at failed
          obtain ⟨Future, future, candidate, model, counterexample⟩ := failed
          exact unrejected (.guard check member Future future candidate model counterexample)
      · obtain ⟨fuel, finished⟩ := ContextualPatternTermination.finishes (request.information chosen) patterned
        change ContextualPatternTermination.Finished (request.scan chosen fuel) at finished
        cases computed : request.scan chosen fuel with
        | refuted impossible => exact .equations fuel ⟨impossible, computed⟩
        | residual update =>
            rw [computed] at finished
            cases finished with
            | solved _ empty =>
                exact False.elim (solvable ⟨update.Variables, update.declaration,
                  update.answer, update.completed empty⟩)
    · exact .take_read apart
  · exact .aliased_take distinct

theorem certified_empty_iff (request : Request locals before)
    (patterned : ∀ chosen ∈ request.candidates,
      ContextualPatternFragment.ProblemPattern (request.information chosen)) :
    request.CertifiedEmpty ↔ ¬ request.Enabled := by
  constructor
  · exact CertifiedEmpty.no_source
  · intro disabled
    refine ⟨fun chosen present => request.rejected_of_no_admission chosen present (patterned chosen present) ?_⟩
    exact fun admitted => disabled ⟨request.selection chosen, admitted⟩

end Request

structure EmptyCensus (locals : Local → MetaArity S)
    (before : ContextualConditionalExecution.State locals O Γ sort)
    [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)] : Type 1 where
  alternatives : List (Request locals before)
  complete : ∀ request ∈ alternatives, request.CertifiedEmpty

theorem EmptyCensus.no_primary [DecidableEq Local] [DecidableEq S.Srt]
    [∀ result, DecidableEq (S.Op result)] (census : EmptyCensus locals before)
    (request : Request locals before) (member : request ∈ census.alternatives) : ¬ request.Enabled :=
  (census.complete request member).no_source

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualSourceCensus
