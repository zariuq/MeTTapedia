import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiSumPrenexForms
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ContextLabels
import Mettapedia.Languages.ProcessCalculi.PiCalculus.SumsStore

/-!
# A store for the π-calculus with sums at the front door

A process of the π-calculus with sums is stored as its canonical block (`store`), and its reductions are read off the
store by the calculus's plan (`SumsStore.plan`): the sums on one channel, or with a silent summand, and what they
leave. When every replicated component of the store copies one component:

- **A successor of the store is a reduction** (`reduces_of_store`): it is equivalent to the contractum of a step of
  an unfolding of the store, a presentation of the canonical form.
- **A reduction is matched by a successor of the store** (`store_of_reduces`), to an equivalent process.

So the front door's step modalities are decided on the store (`decider`), with the exactness of the canonical forms
for named processes. Where a replicated component's copies carry restrictions the store gives no list, and the decider
gives no answer.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiSumStore

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Sums (piSumCalc PiSumRawStep)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.SumsSteps (piSumBlock piSumRepBlock step_block typed_of_raw)
open Mettapedia.Languages.ProcessCalculi.PiCalculus.SumsStore (plan)
open Mettapedia.GSLT.LanguageDef.RestrictionBlocks (Prenex canonP canonR canonFacts decompose_toPattern
  restrictionsBind_of_typed replicate_not_emptyUnit replicate_ne_restrict flatServers moleculeServers_of_flat
  toPattern_injective mem_unfoldings presentationDepth replicationPresentations)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiSumPrenexForms (reading domain canon presentations typed_of_domain
  domain_of_typed canonical step_iff_raw names_context domain_iff_of_equivalent objectEquivalent_of_equationEquiv
  presentation_process)

/-! ## Processes and reductions -/

/-- **The front door of the π-calculus with sums**, in its reading. -/
abbrev frontDoor : NativeStructure Pattern := referenceStructure RelationEnv.empty piSumCalc reading

/-- The processes: object processes with no free bound variable, their free variables names. -/
abbrev processes (term : Pattern) : Prop := domain term = true

theorem isState_of_process {term : Pattern} (admitted : processes term) : IsState term :=
  ⟨by simpa using (typed_of_domain admitted).1.isWellScopedAt, (typed_of_domain admitted).2⟩

theorem equivalent_of_canon_eq {first second : Pattern} (firstIn : processes first) (secondIn : processes second)
    (same : canon first = canon second) : ObjectEquivalent RelationEnv.empty piSumCalc reading first second :=
  .trans _ _ _ (canonical.equivalent firstIn) (same ▸ .symm _ _ (canonical.equivalent secondIn))

/-- **A reduction**: a plain step of the front door, a step of `piSumCalc` modulo its laws. -/
def Reduces (source target : Pattern) : Prop := frontDoor.step source .any target

theorem process_of_raw {source target : Pattern} (sourceIn : processes source) (step : PiSumRawStep source target) :
    processes target := by
  obtain ⟨steppedTyped, steppedObject⟩ := typed_of_raw step (typed_of_domain sourceIn).1 (typed_of_domain sourceIn).2
  exact domain_of_typed steppedTyped steppedObject

/-! ## The store -/

/-- **The store of a process**: its canonical block. -/
abbrev store (term : Pattern) : Prenex := canonP piSumRepBlock term

theorem decompose_canon {term : Pattern} (termIn : processes term) :
    Mettapedia.GSLT.LanguageDef.RestrictionBlocks.decompose piSumBlock (canon term) = store term := by
  have fresh := replicate_not_emptyUnit (block := piSumRepBlock) (language := piSumCalc)
  have restrictFresh := replicate_ne_restrict (block := piSumRepBlock) (language := piSumCalc)
  obtain ⟨typed, object⟩ := typed_of_domain termIn
  have facts := canonFacts fresh restrictFresh object (restrictionsBind_of_typed (block := piSumRepBlock) term typed)
  unfold canon canonR
  rw [if_pos termIn]
  exact decompose_toPattern facts.atomic facts.used

/-- **Equivalent processes have one store.** -/
theorem store_eq {first second : Pattern} (firstIn : processes first)
    (equivalent : ObjectEquivalent RelationEnv.empty piSumCalc reading first second) : store first = store second := by
  have fresh := replicate_not_emptyUnit (block := piSumRepBlock) (language := piSumCalc)
  have restrictFresh := replicate_ne_restrict (block := piSumRepBlock) (language := piSumCalc)
  have secondIn := (domain_iff_of_equivalent equivalent).mp firstIn
  have canonSame := canonical.same firstIn equivalent
  unfold canon at canonSame
  rw [if_pos firstIn, if_pos secondIn] at canonSame
  obtain ⟨firstTyped, firstObject⟩ := typed_of_domain firstIn
  obtain ⟨secondTyped, secondObject⟩ := typed_of_domain secondIn
  exact toPattern_injective
    (canonFacts fresh restrictFresh firstObject (restrictionsBind_of_typed (block := piSumRepBlock) first firstTyped)).atomic
    (canonFacts fresh restrictFresh secondObject
      (restrictionsBind_of_typed (block := piSumRepBlock) second secondTyped)).atomic
    canonSame

/-- **A successor of the store is a reduction**, when the store's replicated components copy one component each. -/
theorem reduces_of_store {source next : Pattern} (sourceIn : processes source)
    (flat : flatServers piSumRepBlock (store source) = true) (member : next ∈ plan.successors (store source)) :
    Reduces source next := by
  obtain ⟨typed, object⟩ := typed_of_domain sourceIn
  obtain ⟨⟨unfolded, unfolds, contracted, raw, contractedNext⟩, nextTyped, nextObject⟩ :=
    plan.successors_sound names_context typed object flat member
  -- the unfolding is a presentation of the canonical form
  have presented : unfolded.toPattern piSumBlock ∈ presentations (canon source) := by
    unfold presentations replicationPresentations
    rw [decompose_canon sourceIn]
    unfold presentationDepth
    rw [if_pos (moleculeServers_of_flat (replicate_not_emptyUnit (language := piSumCalc))
      (replicate_ne_restrict (language := piSumCalc)) flat)]
    exact List.mem_map_of_mem ((mem_unfoldings _ _ _).mpr unfolds)
  obtain ⟨shownIn, shownCanon⟩ := presentation_process sourceIn presented
  have contractedIn := process_of_raw shownIn raw
  have nextIn := domain_of_typed nextTyped nextObject
  obtain ⟨witness, valid⟩ := step_iff_raw.mpr raw
  exact ⟨isState_of_process sourceIn, isState_of_process nextIn, _, contracted, witness,
    equivalent_of_canon_eq sourceIn shownIn shownCanon.symm, isState_of_process shownIn, valid,
    isState_of_process contractedIn,
    objectEquivalent_of_equationEquiv RelationEnv.empty (typed_of_domain contractedIn).1 nextTyped
      (typed_of_domain contractedIn).2 nextObject contractedNext, rfl⟩

/-- **A reduction is matched by a successor of the store**, to an equivalent process, when the store's replicated
components copy one component each. -/
theorem store_of_reduces {source target : Pattern} (sourceIn : processes source)
    (flat : flatServers piSumRepBlock (store source) = true) (step : Reduces source target) :
    ∃ next ∈ plan.successors (store source), ObjectEquivalent RelationEnv.empty piSumCalc reading next target := by
  obtain ⟨-, -, redex, contractum, witness, before, -, valid, -, after, -⟩ := step
  have redexIn := (domain_iff_of_equivalent before).mp sourceIn
  have raw := step_iff_raw.mp ⟨witness, valid⟩
  obtain ⟨typed, object⟩ := typed_of_domain redexIn
  rw [store_eq sourceIn before] at flat ⊢
  obtain ⟨count, rdx, rest, reached⟩ := step_block raw names_context typed object
  obtain ⟨next, member, related⟩ := plan.successors_complete names_context reached typed object flat
  obtain ⟨-, nextTyped, nextObject⟩ := plan.successors_sound names_context typed object flat member
  have contractumIn := process_of_raw redexIn raw
  exact ⟨next, member, .trans _ _ _ (objectEquivalent_of_equationEquiv RelationEnv.empty nextTyped
    (typed_of_domain contractumIn).1 nextObject (typed_of_domain contractumIn).2 related) after⟩

/-! ## The decider on the store -/

/-- **The store's successors** under a plain label, when the store's replicated components copy one component each. -/
def successorList : StepLabel → Pattern → Option (List Pattern)
  | .any, term =>
      if domain term && flatServers piSumRepBlock (store term) then some (plan.successors (store term)) else none
  | _, _ => none

/-- **The successors of the π-calculus with sums by its store, complete up to the laws.** -/
def successors : Successors RelationEnv.empty piSumCalc reading where
  list := successorList
  sound := by
    intro label term next listed target member
    unfold successorList at listed
    split at listed
    · split_ifs at listed with conditions
      cases listed
      simp only [Bool.and_eq_true] at conditions
      exact reduces_of_store conditions.1 conditions.2 member
    · cases listed
  complete := by
    intro label term next listed target step
    unfold successorList at listed
    split at listed
    · split_ifs at listed with conditions
      cases listed
      simp only [Bool.and_eq_true] at conditions
      exact store_of_reduces conditions.1 conditions.2 step
    · cases listed

/-- **The modal decider of the π-calculus with sums on its store**: the step modalities evaluated at the store's
successors, over named terms by canonical forms. -/
def decider : Decider RelationEnv.empty piSumCalc reading :=
  modalDecider successors (namedDecider canon domain canonical)

theorem decided_holds {formula : Formula 0} {term : Pattern} (decided : decider.decide formula term = some true) :
    frontDoor.sat Env.closed formula term :=
  (decider.exact decided).mpr rfl

theorem decided_fails {formula : Formula 0} {term : Pattern} (decided : decider.decide formula term = some false) :
    ¬ frontDoor.sat Env.closed formula term :=
  fun holds => Bool.false_ne_true ((decider.exact decided).mp holds)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiSumStore
