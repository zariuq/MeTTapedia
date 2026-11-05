import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseSourceState
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalClauses
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseStateRefinement
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualOccurrenceRenaming
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceAllocationRenaming

/-!
# Fresh physical names retain a clause's complete binding problem

The reindexed world has the same contextual declarations, equations and
conditional row meanings. Only physical locations of occurrences change.
Per-use scopes depend on source-port positions, so the complete problem,
including latent conditions, is unchanged by the allocation comparison.

The original source freshness condition remains explicit. Giving an output
a fresh target name does not license an originally invalid source creation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseOccurrenceRenaming

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows
open OccurrenceAllocationRenaming
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {Query Local Shared O : Type} [DecidableEq O]
    (queries : Query → MetaArity S) (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
    {Γ : Ctx S} {sort : S.Srt}

abbrev world (cursor : Cursor O) (before : ContextualClauseSourceState.World locals O Γ sort) :
    ContextualClauseSourceState.World locals (Name O) Γ sort where
  Names := before.Names
  equality := before.equality
  declarations := before.declarations
  equations := before.equations
  present := before.present.image cursor.current
  rows physical := before.rows (erase physical)

omit [DecidableEq O] in
theorem binding_equations (cursor : Cursor O) (picked : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → Row locals captures Γ sort) :
    ContextualConditionalSourceProblem.bindingEquations queries locals captures (cursor.rename picked) code
      (fun physical => rows (erase physical)) =
    ContextualConditionalSourceProblem.bindingEquations queries locals captures picked code rows := by
  simp only [ContextualConditionalSourceProblem.bindingEquations, ContextualClauseProblem.problem,
    ContextualClauseProblem.takeViews, ContextualClauseProblem.readViews, Cursor.rename, List.length_map,
    List.get_eq_getElem, List.getElem_map, cursor.projects, Fin.cast]

omit [DecidableEq O] in
theorem latent_conditions (cursor : Cursor O) (picked : Selection O) (rows : O → Row locals captures Γ sort) :
    ContextualConditionalSourceProblem.latent queries locals captures (cursor.rename picked)
      (fun physical => rows (erase physical)) =
    ContextualConditionalSourceProblem.latent queries locals captures picked rows := by
  simp only [ContextualConditionalSourceProblem.latent, Cursor.rename, List.length_map,
    List.get_eq_getElem, List.getElem_map, cursor.projects, Fin.cast]

omit [DecidableEq O] in
theorem problem (cursor : Cursor O) (picked : Selection O)
    (code : RuleInstance (Term (signature S (queryFamily queries captures)) Γ sort))
    (rows : O → Row locals captures Γ sort) (incoming : ContextualResidual.Problem captures) :
    ContextualConditionalSourceProblem.problem queries locals captures (cursor.rename picked) code
      (fun physical => rows (erase physical)) incoming =
    ContextualConditionalSourceProblem.problem queries locals captures picked code rows incoming := by
  rw [ContextualConditionalSourceProblem.problem, ContextualConditionalSourceProblem.problem,
    binding_equations, latent_conditions]

variable {queries locals captures}

theorem information (cursor : Cursor O) (before : ContextualClauseSourceState.World locals O Γ sort)
    (queries : Query → MetaArity S)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries before.declarations)) Γ sort))
    (picked : Selection O) :
    ContextualClauseSourceState.information queries locals (world locals cursor before) plan (cursor.rename picked) =
      ContextualClauseSourceState.information queries locals before plan picked :=
  problem queries locals before.declarations cursor picked plan.rule before.rows before.equations

theorem check_iff (cursor : Cursor O) (before : ContextualClauseSourceState.World locals O Γ sort)
    (queries : Query → MetaArity S)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries before.declarations)) Γ sort))
    (picked : Selection O) (check : Check (Term (signature S (queryFamily queries before.declarations)) Γ sort)) :
    ContextualConditionalGuards.Ask locals
      (ContextualClauseSourceState.information queries locals (world locals cursor before) plan (cursor.rename picked))
      (ContextualConditionalSourceAdmission.sourceRows queries locals before.declarations (world locals cursor before).rows)
      (world locals cursor before).present (check.map (queryView queries locals before.declarations)) ↔
    ContextualConditionalGuards.Ask locals (ContextualClauseSourceState.information queries locals before plan picked)
      (ContextualConditionalSourceAdmission.sourceRows queries locals before.declarations before.rows)
      before.present (check.map (queryView queries locals before.declarations)) := by
  rw [information]
  apply ContextualOccurrenceRenaming.ask_iff locals cursor.current cursor.injective
  intro occurrence _present
  change (before.rows (erase (cursor.current occurrence))).map locals before.declarations _ = _
  rw [cursor.projects]
  rfl

theorem admit_renamed (cursor : Cursor O) (before : ContextualClauseSourceState.World locals O Γ sort)
    (queries : Query → MetaArity S)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries before.declarations)) Γ sort))
    (picked : Selection O) (admitted : ContextualClauseSourceState.Admitted queries locals before plan picked) :
    ContextualClauseSourceState.Admitted queries locals (world locals cursor before) plan (cursor.rename picked) := by
  have enabled : Enabled label before.present (picked.commit : Commit O Unit) :=
    ⟨admitted.taken_present, admitted.read_present, admitted.apart, admitted.fresh, by simp [Selection.commit]⟩
  have represented := cursor.rename_enabled enabled
  have freshInjective : Function.Injective (fresh cursor.next : O → Name O) := by
    intro first second same
    exact (Prod.mk.inj (Sum.inr.inj same)).2
  refine ⟨admitted.take_distinct.map cursor.injective, admitted.output_distinct.map freshInjective,
    ?_, ?_, ?_, represented.taken_subset, represented.kept_subset, represented.apart, represented.fresh, ?_, ?_⟩
  · simpa only [Cursor.rename, List.length_map] using admitted.take_shape
  · simpa only [Cursor.rename, List.length_map] using admitted.read_shape
  · simpa only [Cursor.rename, List.length_map] using admitted.output_shape
  · change ContextualConditionalExecution.Solvable
      (ContextualClauseSourceState.information queries locals (world locals cursor before) plan (cursor.rename picked))
    rw [information]
    exact admitted.solvable
  · intro check member
    apply (check_iff cursor before queries plan picked check).mpr
    exact admitted.checks check member

/-- Admission is exact when the source's own freshness condition is retained. -/
theorem admitted_iff (cursor : Cursor O) (before : ContextualClauseSourceState.World locals O Γ sort)
    (queries : Query → MetaArity S)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries before.declarations)) Γ sort))
    (picked : Selection O) :
    ContextualClauseSourceState.Admitted queries locals before plan picked ↔
      Disjoint picked.made.toFinset before.present ∧
      ContextualClauseSourceState.Admitted queries locals (world locals cursor before) plan (cursor.rename picked) := by
  constructor
  · intro admitted
    exact ⟨admitted.fresh, admit_renamed cursor before queries plan picked admitted⟩
  · rintro ⟨sourceFresh, represented⟩
    have taken : picked.taken.toFinset ⊆ before.present := by
      apply (Finset.image_subset_image_iff cursor.injective).mp
      simpa only [Cursor.rename, Selection.commit, mapped_toFinset] using represented.taken_present
    have read : picked.read.toFinset ⊆ before.present := by
      apply (Finset.image_subset_image_iff cursor.injective).mp
      simpa only [Cursor.rename, Selection.commit, mapped_toFinset] using represented.read_present
    have apart : Disjoint picked.taken.toFinset picked.read.toFinset := by
      apply (Finset.disjoint_image cursor.injective).mp
      simpa only [Cursor.rename, mapped_toFinset] using represented.apart
    refine ⟨List.Nodup.of_map cursor.current represented.take_distinct,
      List.Nodup.of_map (fresh cursor.next) represented.output_distinct, ?_, ?_, ?_,
      taken, read, apart, sourceFresh, ?_, ?_⟩
    · simpa only [Cursor.rename, List.length_map] using represented.take_shape
    · simpa only [Cursor.rename, List.length_map] using represented.read_shape
    · simpa only [Cursor.rename, List.length_map] using represented.output_shape
    · have consistent := represented.solvable
      change ContextualConditionalExecution.Solvable
        (ContextualClauseSourceState.information queries locals (world locals cursor before) plan (cursor.rename picked)) at consistent
      rw [information] at consistent
      exact consistent
    · intro check member
      exact (check_iff cursor before queries plan picked check).mp (represented.checks check member)

theorem produced_row (cursor : Cursor O) (before : ContextualClauseSourceState.World locals O Γ sort)
    (queries : Query → MetaArity S)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries before.declarations)) Γ sort))
    (picked : Selection O) (port : Fin plan.rule.produce.length) :
    ContextualClauseSourceState.producedRow queries locals (world locals cursor before) plan (cursor.rename picked) port =
      ContextualClauseSourceState.producedRow queries locals before plan picked port := by
  simp only [ContextualClauseSourceState.producedRow, information]

section Results

variable [DecidableEq Query] [DecidableEq Local]

/-- The source update preserves each conditional row at its current allocated name. -/
theorem result_row (cursor : Cursor O) (before : ContextualClauseSourceState.World locals O Γ sort)
    (queries : Query → MetaArity S)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries before.declarations)) Γ sort))
    (picked : Selection O) (admitted : ContextualClauseSourceState.Admitted queries locals before plan picked)
    (occurrence : O) :
    (ContextualClauseSourceState.target queries locals (world locals cursor before) plan (cursor.rename picked)).rows
        ((cursor.advance picked).current occurrence) =
      (ContextualClauseSourceState.target queries locals before plan picked).rows occurrence := by
  have represented := admit_renamed cursor before queries plan picked admitted
  by_cases made : occurrence ∈ picked.made
  · obtain ⟨port, rfl⟩ := List.mem_iff_get.mp made
    let newPort : Fin (cursor.rename picked).made.length :=
      ⟨port.val, by simpa only [Cursor.rename, List.length_map] using port.isLt⟩
    have key : (cursor.advance picked).current (picked.made.get port) = (cursor.rename picked).made.get newPort := by
      change (if picked.made.get port ∈ picked.made then _ else _) = _
      rw [if_pos (List.get_mem _ _)]
      simp only [Cursor.rename, List.get_eq_getElem, List.getElem_map, newPort]
    rw [key, ContextualClauseSourceState.produced_at represented newPort,
      ContextualClauseSourceState.produced_at admitted port]
    exact produced_row cursor before queries plan picked ⟨port.val, admitted.output_shape ▸ port.isLt⟩
  · have oldKey : (cursor.advance picked).current occurrence = cursor.current occurrence := if_neg made
    have notNew : cursor.current occurrence ∉ (cursor.rename picked).made := by
      intro present
      change cursor.current occurrence ∈ picked.made.map (fresh cursor.next) at present
      obtain ⟨origin, _member, same⟩ := List.mem_map.mp present
      have impossible := cursor.older occurrence cursor.next origin same.symm
      omega
    rw [oldKey, ContextualClauseSourceState.retained_at _ notNew,
      ContextualClauseSourceState.retained_at _ made]
    simp only [ContextualClauseSourceState.retainedRow, world, cursor.projects]

end Results

section Native

variable [DecidableEq Query] [DecidableEq Local] [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]

/-- Every admitted renamed clause has an actual existing compiler firing at every finite budget. -/
theorem realize (cursor : Cursor O) (before : ContextualClauseSourceState.World locals O Γ sort)
    (queries : Query → MetaArity S)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries before.declarations)) Γ sort))
    (picked : Selection O) (admitted : ContextualClauseSourceState.Admitted queries locals before plan picked)
    (occupied : Finset Nat) (fuel : Nat) :
    ∃ compiled : ContextualConditionalClauses.Compiled queries locals
        (before := (world locals cursor before).native occupied) plan (cursor.rename picked),
      compiled.firing.fuel = fuel :=
  ContextualConditionalClauses.realize queries locals (before := (world locals cursor before).native occupied)
    plan (cursor.rename picked)
    (admit_renamed cursor before queries plan picked admitted) fuel

/-- Actual native publication has exactly the source's conditional row observations at allocated names. -/
theorem all_row_observations (cursor : Cursor O) (before : ContextualClauseSourceState.World locals O Γ sort)
    (queries : Query → MetaArity S)
    (plan : ContextualPublication.Plan (Term (signature S (queryFamily queries before.declarations)) Γ sort))
    (picked : Selection O) (admitted : ContextualClauseSourceState.Admitted queries locals before plan picked)
    (occupied : Finset Nat)
    (compiled : ContextualConditionalClauses.Compiled queries locals
      (before := (world locals cursor before).native occupied) plan (cursor.rename picked))
    (occurrence : O) {Next : Type} (next : Next → MetaArity S)
    (candidate : Assignment compiled.firing.target.declarations next) (pattern : Term (signature S next) Γ sort) :
    Matches (ContextualClauseSourceState.resultLocals queries locals before)
      (ContextualClauseSourceState.resultFamily queries locals before)
      (Assignment.compose candidate compiled.sourceFrame.assignment) pattern
      ((ContextualClauseSourceState.target queries locals before plan picked).rows occurrence) ↔
    Matches (ContextualPublication.privateFamily (ContextualClauseFrames.bank queries locals) compiled.firing.update.declaration)
      compiled.firing.target.declarations candidate pattern
      (compiled.firing.target.rows ((cursor.advance picked).current occurrence)) := by
  have actual := ContextualClauseStateRefinement.all_row_observations
    (before := world locals cursor before) (occupied := occupied) compiled
    ((cursor.advance picked).current occurrence) next candidate pattern
  rw [result_row cursor before queries plan picked admitted occurrence] at actual
  exact actual

end Native

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualClauseOccurrenceRenaming
