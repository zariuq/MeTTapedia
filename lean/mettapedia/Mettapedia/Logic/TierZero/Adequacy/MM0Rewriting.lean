import Mettapedia.Logic.TierZero.Adequacy.MM0RewritingConversionCompleteness

/-!
# Direct adequacy of MM0 on guarded rewriting's own calculus

The process consists of the finite rule catalog compiled from the admitted
MM0 theory. Proof certificates supply ordinary requests. Acceptance is
reachability of a proof value through that process's existing step relation.

Both directions are proved against independent MM0 derivability. The reverse
direction constructs actual runs, retaining hypotheses and all conversion
premises. Neither statement uses the Kernel2 proof interpreter.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting

open Mettapedia.Languages.MM0.Kernel
open MM0ContextualSupport

theorem derives_complete {theory : Theory} (wellFormed : theory.WellFormed) {target : Context}
    (formed : Context.WellFormed theory.sortSignature target) {keys : List RuleKey} (covers : Covers theory keys)
    {hypotheses : List Preterm} {expression : Preterm}
    (derived : Derives theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses expression) :
    ∀ initial : Multiset Tm, (∀ hypothesis ∈ hypotheses, proofValue target hypothesis ∈ initial) →
      ∃ block : Block theory target keys initial, proofValue target expression ∈ initial + block.produced := by
  induction derived using Derives.rec
      (motive_2 := fun expressions _ => ∀ initial : Multiset Tm,
        (∀ hypothesis ∈ hypotheses, proofValue target hypothesis ∈ initial) →
        ∃ block : Block theory target keys initial,
          ∀ expression ∈ expressions, proofValue target expression ∈ initial + block.produced) with
  | @hypothesis expression assumed =>
      intro initial available
      exact ⟨Block.empty initial, by simpa [Block.empty] using available expression assumed⟩
  | @theoremApp index declaration arguments instance_ known instantiated children ih =>
      intro initial available
      obtain ⟨prior, present⟩ := ih initial available
      let key := RuleKey.theorem_ index
      have compiled : ruleFor theory target key = some (theoremRule theory.termSignature target key.name declaration) := by
        simp [ruleFor, key, known]
      let last : Block theory target keys (initial + prior.produced) := Block.single
        (key.name, arguments.map (encode target)) (proofValue target instance_.conclusion)
        (process_step_of_key theory target keys (covers.theorem_ _ _ known) compiled
          (theoremRule_complete formed key.name declaration instantiated (initial + prior.produced) present))
      refine ⟨prior.append last, prior.append_contains_second last ?_⟩
      simp [last, Block.single]
  | @conversion left right sort converted child ih =>
      intro initial available
      obtain ⟨conversions, conversionPresent⟩ := conversion_complete wellFormed formed covers converted initial
      obtain ⟨proofs, proofPresent⟩ := ih (initial + conversions.produced)
        (fun hypothesis member => conversions.retains (available hypothesis member))
      let prior := conversions.append proofs
      have conversionAvailable := conversions.append_retains_first proofs conversionPresent
      have proofAvailable := conversions.append_contains_second proofs proofPresent
      let key := RuleKey.basic .transport sort
      have member := covers.basic sort (typed_sort_declared wellFormed formed converted.typed.1) .transport
      let last : Block theory target keys (initial + prior.produced) := Block.single
        (key.name, [encode target left, encode target right]) (proofValue target right)
        (process_step_of_key theory target keys member rfl
          (transport_step formed key.name converted (initial + prior.produced) conversionAvailable proofAvailable))
      refine ⟨prior.append last, prior.append_contains_second last ?_⟩
      simp [last, Block.single]
  | nil =>
      rename_i initial available
      exact ⟨Block.empty initial, by simp⟩
  | @cons expression expressions child children ihChild ihChildren =>
      rename_i initial available
      obtain ⟨first, firstPresent⟩ := ihChild initial available
      obtain ⟨rest, restPresent⟩ := ihChildren (initial + first.produced)
        (fun hypothesis member => first.retains (available hypothesis member))
      refine ⟨first.append rest, ?_⟩
      intro value member
      rcases List.mem_cons.mp member with rfl | member
      · exact first.append_retains_first rest firstPresent
      · exact first.append_contains_second rest (restPresent value member)

/-- The whole finite native catalog accepts exactly independent MM0
derivations, relative to the same theory and local hypotheses. -/
theorem rewriting_reaches_iff_derives {theory : Theory} (wellFormed : theory.WellFormed) {target : Context}
    (formed : Context.WellFormed theory.sortSignature target) (hypotheses : List Preterm) (expression : Preterm) :
    (∃ requests after,
      Relation.ReflTransGen (process theory target (catalog theory)).Step
        (requestBag requests + hypothesisBag target hypotheses) after ∧
      proofValue target expression ∈ after) ↔
    Derives theory.termSignature theory.definitionSignature theory.theoremSignature target hypotheses expression := by
  constructor
  · rintro ⟨requests, after, run, present⟩
    exact reachable_proof_sound wellFormed formed hypotheses (catalog theory) requests run present
  · intro derived
    obtain ⟨block, present⟩ := derives_complete wellFormed formed (catalog_covers theory) derived
      (hypothesisBag target hypotheses) (by
        intro hypothesis member
        exact List.mem_map.mpr ⟨hypothesis, member, rfl⟩)
    exact ⟨block.requests, hypothesisBag target hypotheses + block.produced, block.execution, present⟩

end Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting
