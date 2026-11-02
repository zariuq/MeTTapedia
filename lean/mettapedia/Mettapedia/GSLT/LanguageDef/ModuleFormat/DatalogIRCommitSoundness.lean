import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRReceiptSoundness
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRClosureCommitLaws

/-! The actual batch commit preserves independently derivable facts and
complete decoding. Receipt identities remain a separate observation. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.CommitSoundness

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax

theorem source_facts (program : Program) (seeds input : List GroundFact) (prepared : Executable.Prepared)
    (accepted : Executable.prepare program input = .ok prepared) (known : List Pattern) (facts : List GroundFact)
    (represented : ∀ value ∈ known, ∃ fact ∈ facts, Executable.decodeFact? prepared value = some fact)
    (derived : ∀ fact ∈ facts, Closure.Derives Executable.policy program seeds fact)
    (checked : GeneralPremise.Static.checkLanguage (GeneralPlanEnvironment.environment (Executable.plan prepared prepared.seedFacts)) = true)
    (batch : List GeneralOccurrenceSemantics.Receipt)
    (valid : ∀ receipt ∈ batch, receipt.Valid (Executable.plan prepared known) [] (.base "DlStatement")
      (Executable.request prepared.vocabulary))
    (keys : List ClosureMachine.Key) (resultFacts : List Pattern) (resultKeys : List ClosureMachine.Key)
    (committed : ClosureMachine.commit? prepared known batch known keys = some (resultFacts,resultKeys)) :
    ∀ value ∈ resultFacts, ∃ fact,
      Executable.decodeFact? prepared value = some fact ∧ Closure.Derives Executable.policy program seeds fact := by
  have observations := ClosureMachine.Conservation.commit_observations prepared known batch known keys resultFacts resultKeys committed
  intro value member
  rcases (observations.1 value).mp member with old | fresh
  · obtain ⟨fact,present,decoded⟩ := represented value old
    exact ⟨fact,decoded,derived fact present⟩
  · obtain ⟨receipt,present,same⟩ := List.mem_map.mp fresh
    obtain ⟨row,decoded,authorized⟩ := ReceiptSoundness.source_authorized program input prepared accepted known facts
      represented checked receipt (valid receipt present)
    refine ⟨row.conclusion,?_,?_⟩
    · simpa only [same] using decoded
    · exact .fire row (Closure.authorized_on_premises _ _ _ _ authorized)
        (fun premise member => derived premise (Closure.source_firing_premises authorized premise member))

#print axioms source_facts

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.CommitSoundness
