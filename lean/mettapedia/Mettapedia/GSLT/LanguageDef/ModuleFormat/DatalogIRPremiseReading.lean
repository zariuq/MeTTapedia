import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRBodyCompilation
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRSnapshotReading

/-! Each compiled body query authorizes its source premise in one common
assignment. The snapshot correspondence concerns inputs, not inferred facts. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.PremiseReading

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax GeneralScopedMatch
open GeneralFirstOrderProjection

def SourceHolds (pools : Join.Pools) (known : List GroundFact)
    (chosen : ScopedRuleMatching.Assignment) : Mettapedia.Languages.Datalog.Premise → Prop
  | .atom atom => ∃ fact ∈ known, atom.Matches (FiringReading.sourceAssignment pools chosen) fact
  | .comparison comparison => Comparisons.Holds Executable.policy (FiringReading.sourceAssignment pools chosen) comparison

theorem one_sound (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) (known : List Pattern) (facts : List GroundFact)
    (represented : ∀ value ∈ known, ∃ fact ∈ facts, Executable.decodeFact? prepared value = some fact)
    {environment : GeneralPremise.Environment} {context : GeneralPremise.Context}
    (provider : environment.provider = (Executable.snapshot prepared known).provider)
    (source : Mettapedia.Languages.Datalog.Premise) (position : Nat) (native : Syntax.Premise)
    (compiled : Join.bodyPremise? prepared.vocabulary position source = some native)
    (used : ∀ comparison, source = .comparison comparison → comparison.operator ∈ Executable.operators prepared.source)
    {initial final chosen : ScopedRuleMatching.Assignment} {event : GeneralPremise.Event}
    (held : GeneralPremise.PremiseHolds environment context (Query.lowerPremise native) initial final event)
    (later : GeneralScopedMatch.Extends final chosen)
    (roots : GeneralPremise.RootValues context.bound.length chosen)
    (poolRead : ClauseReading.PoolsRead prepared.vocabulary (ClauseDictionary.expand prepared.vocabulary (ordinary chosen))) :
    SourceHolds prepared.vocabulary facts chosen source := by
  have static : environment.provider.dynamicRelations = [] := by rw [provider]; rfl
  cases source with
  | atom atom =>
    obtain ⟨code,atomCompiled,shape⟩ := BodyCompilation.atom_premise prepared.vocabulary position atom native compiled
    rw [shape] at held
    cases held with
    | query query =>
      have signature := SnapshotReading.fact_signature prepared known
      rw [← provider] at signature
      obtain ⟨value,row,matched⟩ := QueryReading.source_query_match prepared.vocabulary position atom code atomCompiled
        static signature query later roots poolRead
      have actualRow := row
      rw [provider] at actualRow
      have factAt := SnapshotReading.fact_row_position program seeds prepared accepted known _ value actualRow
      obtain ⟨fact,present,decoded⟩ := represented value (List.mem_of_getElem? factAt)
      exact ⟨fact,present,matched fact decoded⟩
  | comparison comparison =>
    obtain ⟨left,right,leftCode,rightCode,shape⟩ := BodyCompilation.guard_premise prepared.vocabulary position comparison native compiled
    rw [shape] at held
    cases held with
    | query query =>
      have signature := SnapshotReading.comparison_signature prepared known comparison.operator (used comparison rfl)
      rw [← provider] at signature
      have rows : environment.provider.rows = (Query.provider known).rows ++ Executable.comparisonRows program prepared.vocabulary := by
        rw [provider]
        change _ ++ prepared.staticRows = _
        rw [Executable.prepare_staticRows program seeds prepared accepted]
      exact GuardReading.source_guard_sound program prepared.vocabulary known position comparison left right
        leftCode rightCode rows static signature query later roots poolRead

theorem all_sound (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) (known : List Pattern) (facts : List GroundFact)
    (represented : ∀ value ∈ known, ∃ fact ∈ facts, Executable.decodeFact? prepared value = some fact)
    {environment : GeneralPremise.Environment}
    (provider : environment.provider = (Executable.snapshot prepared known).provider)
    (entries : List (Mettapedia.Languages.Datalog.Premise × Nat)) (native : List Syntax.Premise)
    (compiled : entries.mapM (fun entry => Join.bodyPremise? prepared.vocabulary entry.2 entry.1) = some native)
    (used : ∀ entry ∈ entries, ∀ comparison, entry.1 = .comparison comparison →
      comparison.operator ∈ Executable.operators prepared.source)
    {context : GeneralPremise.Context} {initial final chosen : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (held : GeneralPremise.PremisesHold environment context (native.map Query.lowerPremise) initial final history)
    (later : GeneralScopedMatch.Extends final chosen)
    (roots : GeneralPremise.RootValues context.bound.length chosen)
    (poolRead : ClauseReading.PoolsRead prepared.vocabulary (ClauseDictionary.expand prepared.vocabulary (ordinary chosen))) :
    ∀ entry ∈ entries, SourceHolds prepared.vocabulary facts chosen entry.1 := by
  induction entries generalizing native context initial history with
  | nil => simp
  | cons entry entries ih =>
    simp only [List.mapM_cons] at compiled
    change ((Join.bodyPremise? prepared.vocabulary entry.2 entry.1).bind fun first =>
      (entries.mapM fun item => Join.bodyPremise? prepared.vocabulary item.2 item.1).bind fun rest =>
        some (first :: rest)) = some native at compiled
    simp only [Option.bind_eq_some_iff,Option.some.injEq] at compiled
    obtain ⟨first,firstCompiled,rest,restCompiled,rfl⟩ := compiled
    cases held with
    | cons firstHeld restHeld =>
      have firstLater := restHeld.extension.trans later
      have firstSound := one_sound program seeds prepared accepted known facts represented provider entry.1 entry.2
        first firstCompiled (used entry List.mem_cons_self) firstHeld firstLater roots poolRead
      have restSound := ih rest restCompiled
        (fun other member => used other (List.mem_cons_of_mem _ member)) restHeld roots
      intro other member
      rcases List.mem_cons.mp member with rfl | member
      · exact firstSound
      · exact restSound other member

#print axioms one_sound
#print axioms all_sound

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.PremiseReading
