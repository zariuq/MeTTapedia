import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Reindex
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RegionQuerySupport

/-!
# Exact query data as an alphabet of the actual region-query step

The data carries its original exact queries and their image equation. The
step is the existing first-order step reindexed along the first projection;
effects and admission are inherited. Fixed sightings and staged instructions
use this explicit profile. No exact set is recovered from an arbitrary
acceptance predicate.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ExactQueryAlphabet

open AnnotatedRuns (Firing firstOrder)
open PredicateQueryAdmission (Query RegionQuery)

universe uT uS uO

variable {T : Type uT} {S : Type uS} {O : Type uO}

structure ExactData (firing : Firing T S O) where
  queries : List (Query T S O)
  image : firing.queries = queries.map Query.toRegion

abbrev Alphabet (T : Type uT) (S : Type uS) (O : Type uO) :=
  (firing : Firing T S O) × ExactData firing

/-- Supplied exact queries earn finite acceptance support from their actual seen sets. -/
def ExactData.supports {firing : Firing T S O} (data : ExactData firing) :
    Interface.RegionQuerySupport.Supports firing.queries := by
  rw [data.image]
  intro index
  have bounded : index.val < data.queries.length := by simpa only [List.length_map] using index.isLt
  change Interface.RegionQuerySupport.AcceptanceSupport
    ((data.queries.map Query.toRegion)[index.val]'index.isLt)
  rw [List.getElem_map]
  change Interface.RegionQuerySupport.AcceptanceSupport
    (RegionQuery.exact data.queries[index.val].region data.queries[index.val].seen)
  exact Interface.RegionQuerySupport.exact data.queries[index.val].region data.queries[index.val].seen

def ofQueries (rule : RuleInstance T) (queries : List (Query T S O)) (selection : Selection O) : Alphabet T S O :=
  ⟨⟨rule,queries.map Query.toRegion,selection⟩,⟨queries,rfl⟩⟩

def renameQuery (permutation : O ≃ O) (query : Query T S O) : Query T S O :=
  ⟨query.region,query.seen.map permutation.toEmbedding⟩

theorem renameQuery_toRegion (permutation : O ≃ O) (query : Query T S O) :
    (renameQuery permutation query).toRegion = query.toRegion.rename permutation := by
  rcases query with ⟨region,seen⟩
  change RegionQuery.mk region (fun _ found => found = seen.map permutation.toEmbedding) =
    RegionQuery.mk region (fun _ found => found.map permutation.symm.toEmbedding = seen)
  apply congrArg (RegionQuery.mk region)
  funext candidate found
  apply propext
  constructor
  · intro same
    rw [same,Finset.map_map,Function.Embedding.equiv_toEmbedding_trans_symm_toEmbedding,Finset.map_refl]
  · intro same
    have mapped := congrArg (Finset.map permutation.toEmbedding) same
    simpa only [Finset.map_map,Function.Embedding.equiv_symm_toEmbedding_trans_toEmbedding,Finset.map_refl] using mapped

theorem renameQuery_refl (query : Query T S O) : renameQuery (Equiv.refl O) query = query := by
  rcases query with ⟨region,seen⟩
  simp [renameQuery]

theorem renameQuery_trans (first second : O ≃ O) (query : Query T S O) :
    renameQuery second (renameQuery first query) = renameQuery (first.trans second) query := by
  rcases query with ⟨region,seen⟩
  simp [renameQuery,Finset.map_map,Equiv.trans_toEmbedding]

def rename (permutation : O ≃ O) (entry : Alphabet T S O) : Alphabet T S O :=
  ofQueries entry.1.rule (entry.2.queries.map (renameQuery permutation))
    (AnnotatedRuns.renameSelection permutation entry.1.selection)

theorem ofQueries_eta (entry : Alphabet T S O) :
    ofQueries entry.1.rule entry.2.queries entry.1.selection = entry := by
  rcases entry with ⟨⟨rule,regions,selection⟩,⟨queries,image⟩⟩
  dsimp only at image
  subst regions
  rfl

theorem rename_fst (permutation : O ≃ O) (entry : Alphabet T S O) :
    (rename permutation entry).1 = entry.1.rename permutation := by
  change (⟨entry.1.rule,(entry.2.queries.map (renameQuery permutation)).map Query.toRegion,
    AnnotatedRuns.renameSelection permutation entry.1.selection⟩ : Firing T S O) = _
  unfold AnnotatedRuns.Firing.rename
  rw [entry.2.image,List.map_map,List.map_map]
  congr 1
  exact List.map_congr_left fun query _ => renameQuery_toRegion permutation query

theorem rename_refl (entry : Alphabet T S O) : rename (Equiv.refl O) entry = entry := by
  unfold rename
  have queries : entry.2.queries.map (renameQuery (Equiv.refl O)) = entry.2.queries := by
    exact (List.map_congr_left fun query _ => renameQuery_refl query).trans (List.map_id entry.2.queries)
  have selection : AnnotatedRuns.renameSelection (Equiv.refl O) entry.1.selection = entry.1.selection := by
    rcases entry.1.selection with ⟨taken,read,made⟩
    simp [AnnotatedRuns.renameSelection]
  rw [queries,selection]
  exact ofQueries_eta entry

theorem rename_trans (first second : O ≃ O) (entry : Alphabet T S O) :
    rename second (rename first entry) = rename (first.trans second) entry := by
  change ofQueries entry.1.rule
      ((entry.2.queries.map (renameQuery first)).map (renameQuery second))
      (AnnotatedRuns.renameSelection second (AnnotatedRuns.renameSelection first entry.1.selection)) = _
  have selection : AnnotatedRuns.renameSelection second (AnnotatedRuns.renameSelection first entry.1.selection) =
      AnnotatedRuns.renameSelection (first.trans second) entry.1.selection := by
    rcases entry.1.selection with ⟨taken,read,made⟩
    simp [AnnotatedRuns.renameSelection,List.map_map]
  rw [List.map_map,selection]
  congr 1
  exact List.map_congr_left fun query _ => renameQuery_trans first second query

variable [DecidableEq O]

def step (A : SubstitutionAction T S) (label : O → T) :=
  (firstOrder A label).toStep.reindex (fun (entry : Alphabet T S O) => entry.1)

theorem admits_iff (A : SubstitutionAction T S) (label : O → T) (before : Configuration T O) (entry : Alphabet T S O) :
    (step A label).Admits (s := before) entry ↔ entry.1.Valid A label before := Iff.rfl

theorem admits_ofQueries_iff (A : SubstitutionAction T S) (label : O → T) (before : Configuration T O)
    (rule : RuleInstance T) (queries : List (Query T S O)) (selection : Selection O) :
    (step A label).Admits (s := before) (ofQueries rule queries selection) ↔
      PredicateQueryAdmission.Valid A label rule queries before selection :=
  PredicateQueryAdmission.valid_iff_regionValid.symm

theorem result_eq (A : SubstitutionAction T S) (label : O → T) (before : Configuration T O)
    (entry : Alphabet T S O) (admitted : (step A label).Admits (s := before) entry) :
    (step A label).result entry admitted = entry.1.result label before := rfl

def forgetRun (A : SubstitutionAction T S) (label : O → T) :
    {before : Configuration T O} → (step A label).Run before → (firstOrder A label).toStep.Run before
  | _, .nil before => .nil before
  | _, .cons entry admitted rest => .cons entry.1 admitted (forgetRun A label rest)

theorem forgetRun_last (A : SubstitutionAction T S) (label : O → T) :
    ∀ {before : Configuration T O} (run : (step A label).Run before), (forgetRun A label run).last = run.last
  | _, .nil _ => rfl
  | _, .cons _ _ rest => forgetRun_last A label rest

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ExactQueryAlphabet
