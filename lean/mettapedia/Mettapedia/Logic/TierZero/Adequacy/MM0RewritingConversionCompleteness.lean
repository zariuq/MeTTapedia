import Mettapedia.Logic.TierZero.Adequacy.MM0RewritingCatalog

/-!
# Every independent MM0 conversion has an actual guarded rewriting run

The construction assembles ordinary request packets and process firings. Each
subderivation leaves its conversion facts available to its parent. Ordered
argument conversions use the same finite shared-read list as congruence.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting

open Mettapedia.Languages.MM0.Kernel
open MM0ContextualSupport

theorem conversion_complete {theory : Theory} (wellFormed : theory.WellFormed) {target : Context}
    (formed : Context.WellFormed theory.sortSignature target) {keys : List RuleKey} (covers : Covers theory keys)
    {left right : Preterm} {sort : Nat}
    (converted : Converts theory.termSignature theory.definitionSignature target left right sort) :
    ∀ initial : Multiset Tm, ∃ block : Block theory target keys initial,
      conversionValue target sort left right ∈ initial + block.produced := by
  induction converted using Converts.rec
      (motive_2 := fun left right binders _ => ∀ initial : Multiset Tm,
        ∃ block : Block theory target keys initial,
          ∀ value ∈ conversionValues target left right binders, value ∈ initial + block.produced) with
  | @refl expression sort typed =>
      intro initial
      let key := RuleKey.basic .reflexivity sort
      have member := covers.basic sort (typed_sort_declared wellFormed formed typed) .reflexivity
      let block : Block theory target keys initial := Block.single
        (key.name, [encode target expression]) (conversionValue target sort expression expression)
        (process_step_of_key theory target keys member rfl (reflexivity_step formed key.name typed initial))
      exact ⟨block, by simp [block, Block.single]⟩
  | @symm left right sort child ih =>
      intro initial
      obtain ⟨first, present⟩ := ih initial
      let key := RuleKey.basic .symmetry sort
      have member := covers.basic sort (typed_sort_declared wellFormed formed child.typed.1) .symmetry
      let last : Block theory target keys (initial + first.produced) := Block.single
        (key.name, [encode target left, encode target right]) (conversionValue target sort right left)
        (process_step_of_key theory target keys member rfl
          (symmetry_step formed key.name child (initial + first.produced) present))
      refine ⟨first.append last, first.append_contains_second last ?_⟩
      simp [last, Block.single]
  | @trans left middle right sort firstConversion secondConversion ihFirst ihSecond =>
      intro initial
      obtain ⟨first, firstPresent⟩ := ihFirst initial
      obtain ⟨second, secondPresent⟩ := ihSecond (initial + first.produced)
      let prior := first.append second
      have firstAvailable := first.append_retains_first second firstPresent
      have secondAvailable := first.append_contains_second second secondPresent
      let key := RuleKey.basic .transitivity sort
      have member := covers.basic sort (typed_sort_declared wellFormed formed firstConversion.typed.1) .transitivity
      let last : Block theory target keys (initial + prior.produced) := Block.single
        (key.name, [encode target left, encode target middle, encode target right]) (conversionValue target sort left right)
        (process_step_of_key theory target keys member rfl
          (transitivity_step formed key.name firstConversion secondConversion (initial + prior.produced)
            firstAvailable secondAvailable))
      refine ⟨prior.append last, prior.append_contains_second last ?_⟩
      simp [last, Block.single]
  | @congruence symbol declaration left right known convertedArguments ih =>
      intro initial
      obtain ⟨prior, present⟩ := ih initial
      let key := RuleKey.congruence symbol
      have compiled : ruleFor theory target key = some (congruenceRule theory.termSignature target key.name symbol declaration) := by
        simp [ruleFor, key, known]
      let last : Block theory target keys (initial + prior.produced) := Block.single
        (key.name, (left ++ right).map (encode target))
        (conversionValue target declaration.resultSort (Preterm.applyArgs (.term symbol) left) (Preterm.applyArgs (.term symbol) right))
        (process_step_of_key theory target keys (covers.congruence _ _ known) compiled
          (congruenceRule_complete formed key.name symbol declaration left right convertedArguments
            (initial + prior.produced) present))
      refine ⟨prior.append last, prior.append_contains_second last ?_⟩
      simp [last, Block.single]
  | @unfold symbol declaration arguments images result known unfolded resultTyped =>
      intro initial
      obtain ⟨body, knownBody⟩ : ∃ body, theory.definitionSignature symbol = some body := by
        cases unfolded with
        | intro _ bodyLookup _ _ _ => exact ⟨_, bodyLookup⟩
      let key := RuleKey.unfolding symbol
      have compiled : ruleFor theory target key = some (unfoldingRule theory.termSignature target key.name symbol declaration body) := by
        simp [ruleFor, key, known, knownBody]
      let block : Block theory target keys initial := Block.single
        (key.name, (arguments ++ images.map Preterm.var).map (encode target))
        (conversionValue target declaration.resultSort (Preterm.applyArgs (.term symbol) arguments) result)
        (process_step_of_key theory target keys (covers.unfolding _ _ knownBody) compiled
          (independent_unfolding_step formed key.name known knownBody unfolded resultTyped initial))
      exact ⟨block, by simp [block, Block.single]⟩
  | nil =>
      rename_i initial
      exact ⟨Block.empty initial, by simp [conversionValues]⟩
  | @cons left right lefts rights binder binders leftFits rightFits child tail ihChild ihTail =>
      rename_i initial
      obtain ⟨first, firstPresent⟩ := ihChild initial
      obtain ⟨second, restPresent⟩ := ihTail (initial + first.produced)
      refine ⟨first.append second, ?_⟩
      intro value member
      rcases List.mem_cons.mp member with rfl | member
      · exact first.append_retains_first second firstPresent
      · exact first.append_contains_second second (restPresent value member)

end Mettapedia.Logic.TierZero.Adequacy.MM0Rewriting
