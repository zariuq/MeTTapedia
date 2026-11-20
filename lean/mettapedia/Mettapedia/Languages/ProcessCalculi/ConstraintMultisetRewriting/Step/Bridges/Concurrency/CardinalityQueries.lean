import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PredicateQueryAdmission

/-!
# Cardinality observations of actual candidate-dependent regions

The region is tested on supplied occurrence labels. Its successful identities
may vary between solutions. Write ignorance uses that same matching region,
rather than a table-validation predicate or a cached guard verdict.

This is an observation component for a richer annotated profile. The existing
fixed-collect query and round definitions are not changed here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.CardinalityQueries

open MeTTaCalculus.OccurrenceCommits (regionOf fire regionOf_fire_of_no_write)

universe uT uS uO

structure Query (T : Type uT) (S : Type uS) where
  region : S → T → Bool
  number : Nat

namespace Query

variable {T : Type uT} {S : Type uS} {O : Type uO}

def Holds (query : Query T S) (candidate : S) (label : O → T) (world : Finset O) : Prop :=
  (regionOf label world (query.region candidate)).card = query.number

def Ask (query : Query T S) (A : SubstitutionAction T S) (problem : EquationStore T)
    (label : O → T) (world : Finset O) : Prop :=
  A.Entails problem (fun candidate => query.Holds candidate label world)

def IgnoresWrites (query : Query T S) (A : SubstitutionAction T S) (problem : EquationStore T)
    (label : O → T) (writer : Selection O) : Prop :=
  A.Entails problem (fun candidate => ∀ occurrence ∈ writer.taken ++ writer.made,
    query.region candidate (label occurrence) = false)

theorem Ask.of_refines {query : Query T S} {A : SubstitutionAction T S}
    {stronger weaker : EquationStore T} {label : O → T} {world : Finset O}
    (refines : A.Refines stronger weaker) (asked : query.Ask A weaker label world) :
    query.Ask A stronger label world :=
  A.entails_of_refines refines asked

theorem IgnoresWrites.of_refines {query : Query T S} {A : SubstitutionAction T S}
    {stronger weaker : EquationStore T} {label : O → T} {writer : Selection O}
    (refines : A.Refines stronger weaker) (ignored : query.IgnoresWrites A weaker label writer) :
    query.IgnoresWrites A stronger label writer :=
  A.entails_of_refines refines ignored

def ofExact (query : PredicateQueryAdmission.Query T S O) : Query T S :=
  ⟨query.region, query.seen.card⟩

theorem ask_of_exact {query : PredicateQueryAdmission.Query T S O}
    {A : SubstitutionAction T S} {problem : EquationStore T} {label : O → T} {world : Finset O}
    (asked : query.Ask A problem label world) :
    (ofExact query).Ask A problem label world := by
  intro candidate solved
  exact asked.card solved

theorem ignoresWrites_ofExact_iff (query : PredicateQueryAdmission.Query T S O)
    (A : SubstitutionAction T S) (problem : EquationStore T) (label : O → T) (writer : Selection O) :
    (ofExact query).IgnoresWrites A problem label writer ↔
      query.IgnoresWrites A problem label writer := Iff.rfl

theorem holds_zero_iff (region : S → T → Bool) (candidate : S)
    (label : O → T) (world : Finset O) :
    (Query.mk region 0).Holds candidate label world ↔
      ((PredicateQueryAdmission.Query.mk region (∅ : Finset O)).atSolution candidate).Holds label world := by
  exact Finset.card_eq_zero

variable [DecidableEq O]

theorem holds_fire_iff (query : Query T S) (candidate : S) (label : O → T)
    (world : Finset O) (writer : Selection O)
    (ignored : ∀ occurrence ∈ writer.taken ++ writer.made,
      query.region candidate (label occurrence) = false) :
    query.Holds candidate label (fire world (writer.commit (T := T))) ↔
      query.Holds candidate label world := by
  have noWrite : ∀ occurrence ∈ (writer.commit (T := T)).taken ∪ (writer.commit (T := T)).made,
      query.region candidate (label occurrence) = false := by
    intro occurrence written
    apply ignored occurrence
    simpa only [Selection.commit, Finset.mem_union, List.mem_toFinset, List.mem_append] using written
  unfold Holds
  rw [regionOf_fire_of_no_write noWrite]

theorem Ask.after {query : Query T S} {A : SubstitutionAction T S}
    {stronger weaker : EquationStore T} {label : O → T} {world : Finset O} {writer : Selection O}
    (asked : query.Ask A weaker label world) (refines : A.Refines stronger weaker)
    (ignored : query.IgnoresWrites A stronger label writer) :
    query.Ask A stronger label (fire world (writer.commit (T := T))) := by
  intro candidate solved
  exact (holds_fire_iff query candidate label world writer (ignored candidate solved)).mpr
    (asked candidate (refines candidate solved))

end Query

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.Concurrency.CardinalityQueries
