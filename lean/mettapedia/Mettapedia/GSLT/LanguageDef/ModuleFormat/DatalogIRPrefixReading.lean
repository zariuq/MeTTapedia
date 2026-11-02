import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRPremiseReading
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClosureMachine

/-! The finite key's premise list comes from the first positive queries,
with their exact row positions in the immutable fact snapshot. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.PrefixReading

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax GeneralScopedMatch
open GeneralFirstOrderProjection

theorem positive_prefix (program : Program) (seeds : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program seeds = .ok prepared) (known : List Pattern) (facts : List GroundFact)
    (represented : ∀ value ∈ known, ∃ fact ∈ facts, Executable.decodeFact? prepared value = some fact)
    {environment : GeneralPremise.Environment}
    (provider : environment.provider = (Executable.snapshot prepared known).provider)
    (count : Nat) (entries : List (Mettapedia.Languages.Datalog.Premise × Nat)) (native : List Syntax.Premise)
    (compiled : entries.mapM (fun entry => Join.bodyPremise? prepared.vocabulary entry.2 entry.1) = some native)
    (enough : count ≤ entries.length)
    (positive : ∀ entry ∈ entries.take count, ∃ atom, entry.1 = .atom atom)
    {context : GeneralPremise.Context} {initial final chosen : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (held : GeneralPremise.PremisesHold environment context (native.map Query.lowerPremise) initial final history)
    (quantifiers : context.quantifierDepth = 0)
    (later : GeneralScopedMatch.Extends final chosen)
    (roots : GeneralPremise.RootValues context.bound.length chosen)
    (poolRead : ClauseReading.PoolsRead prepared.vocabulary (ClauseDictionary.expand prepared.vocabulary (ordinary chosen))) :
    ∃ values decoded,
      ClosureMachine.premiseFacts? count history known = some values ∧
      values.mapM (Executable.decodeFact? prepared) = some decoded ∧
      List.Forall₂ (fun entry fact => ∃ atom, entry.1 = .atom atom ∧
        atom.Matches (FiringReading.sourceAssignment prepared.vocabulary chosen) fact) (entries.take count) decoded ∧
      ∀ fact ∈ decoded, fact ∈ facts := by
  induction count generalizing entries native context initial history with
  | zero => exact ⟨[],[],rfl,rfl,.nil,by simp⟩
  | succ count ih =>
    cases entries with
    | nil => simp at enough
    | cons entry entries =>
      simp only [List.mapM_cons] at compiled
      change ((Join.bodyPremise? prepared.vocabulary entry.2 entry.1).bind fun first =>
        (entries.mapM fun item => Join.bodyPremise? prepared.vocabulary item.2 item.1).bind fun rest =>
          some (first :: rest)) = some native at compiled
      simp only [Option.bind_eq_some_iff,Option.some.injEq] at compiled
      obtain ⟨first,firstCompiled,rest,restCompiled,rfl⟩ := compiled
      obtain ⟨atom,sourceEq⟩ := positive entry (by simp)
      have firstAtom : Join.bodyPremise? prepared.vocabulary entry.2 (.atom atom) = some first := by
        rw [← sourceEq]
        exact firstCompiled
      obtain ⟨code,atomCompiled,shape⟩ := BodyCompilation.atom_premise prepared.vocabulary entry.2 atom first firstAtom
      cases held with
      | cons firstHeld restHeld =>
        rw [shape] at firstHeld
        cases firstHeld with
        | query query =>
          have static : environment.provider.dynamicRelations = [] := by rw [provider]; rfl
          have signature := SnapshotReading.fact_signature prepared known
          rw [← provider] at signature
          obtain ⟨value,row,matched⟩ := QueryReading.source_query_match prepared.vocabulary entry.2 atom code atomCompiled
            static signature query (restHeld.extension.trans later) roots poolRead
          have actualRow := row
          rw [provider] at actualRow
          have factAt := SnapshotReading.fact_row_position program seeds prepared accepted known _ value actualRow
          obtain ⟨fact,present,decoded⟩ := represented value (List.mem_of_getElem? factAt)
          have remainingEnough : count ≤ entries.length := Nat.le_of_succ_le_succ enough
          have remainingPositive : ∀ other ∈ entries.take count, ∃ atom, other.1 = .atom atom := by
            intro other member
            exact positive other (List.mem_cons_of_mem _ member)
          obtain ⟨values,decodedRest,read,decodeRest,matchedRest,members⟩ :=
            ih entries rest restCompiled remainingEnough remainingPositive restHeld rfl roots
          refine ⟨value :: values,fact :: decodedRest,?_,?_,?_,?_⟩
          · simp [ClosureMachine.premiseFacts?,quantifiers,factAt,read]
          · simp [List.mapM_cons,decoded,decodeRest]
          · exact .cons ⟨atom,sourceEq,matched fact decoded⟩ matchedRest
          · intro other member
            rcases List.mem_cons.mp member with rfl | member
            · exact present
            · exact members other member

#print axioms positive_prefix

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.PrefixReading
