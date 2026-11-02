import Mettapedia.GSLT.LanguageDef.RestrictionBlocks.ReplicationContext

/-!
# What a raw instance of a replication law relates

The laws of replication bind no name and are read raw: a side matches a term by binding its metavariables, and the
other side is instantiated with those bindings. Each instance relates explicit shapes: `!p` and `{p, !p}` (the members
in either order), `!0` and `0`, `!!p` and `!p`, `!{p, q}` and `{!p, !q}`, `{!p, !p}` and `!p`
(`replicationLaw_instance`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RestrictionBlocks

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match (Bindings matchPattern applyBindings mergeBindings)
open Mettapedia.OSLF.MeTTaIL.MatchSpec (MatchRel MatchArgsRel MatchBagRel matchPattern_sound)

variable {block : ReplicationBlock}

/-! ## Matching the sides of the replication laws -/

theorem mergeBindings_nil_right (bindings : Bindings) : mergeBindings bindings [] = some bindings := rfl

/-- Merging two bindings of one metavariable succeeds exactly when they agree. -/
theorem mergeBindings_same (name : String) (first second : Pattern) {bindings : Bindings}
    (merged : mergeBindings [(name, first)] [(name, second)] = some bindings) :
    first = second ∧ bindings = [(name, first)] := by
  simp only [mergeBindings, List.foldlM_cons, List.foldlM_nil, List.find?_cons, beq_self_eq_true] at merged
  by_cases same : first = second
  · subst same
    simp [BEq.beq] at merged
    exact ⟨rfl, merged.symm⟩
  · simp [BEq.beq, same] at merged

/-- Merging bindings of two metavariables keeps both. -/
theorem mergeBindings_two {first second : String} (different : first ≠ second) (firstValue secondValue : Pattern)
    {bindings : Bindings} (merged : mergeBindings [(first, firstValue)] [(second, secondValue)] = some bindings) :
    bindings = [(second, secondValue), (first, firstValue)] := by
  simp only [mergeBindings, List.foldlM_cons, List.foldlM_nil, List.find?_cons, List.find?_nil] at merged
  have notSame : (first == second) = false := by simpa using different
  simp [notSame] at merged
  exact merged.symm

/-- A match of a metavariable binds it to the term. -/
theorem matchRel_fvar {name : String} {pattern : Pattern} {bindings : Bindings}
    (matched : MatchRel (.fvar name) pattern bindings) : bindings = [(name, pattern)] := by
  cases matched
  rfl

/-- A match of a constructor applied to one pattern is that constructor applied to one term matching it. -/
theorem matchRel_apply_single {label : String} {argument : Pattern} {pattern : Pattern} {bindings : Bindings}
    (matched : MatchRel (.apply label [argument]) pattern bindings) :
    ∃ term, pattern = .apply label [term] ∧ MatchRel argument term bindings := by
  cases matched with
  | apply arguments _ =>
      cases arguments with
      | cons head tail merged =>
          cases tail
          rw [mergeBindings_nil_right, Option.some.injEq] at merged
          subst merged
          exact ⟨_, rfl, head⟩

/-- A match of two patterns in a multiset of terms: two terms, each matched by one of the patterns, in either
order. -/
theorem matchBagRel_two {first second : Pattern} {members : List Pattern} {bindings : Bindings}
    (matched : MatchBagRel [first, second] none .hashBag members bindings) :
    ∃ a b firstBindings secondBindings, (members = [a, b] ∨ members = [b, a]) ∧
      MatchRel first a firstBindings ∧ MatchRel second b secondBindings ∧
        mergeBindings firstBindings secondBindings = some bindings := by
  cases matched with
  | cons index inside firstMatched others merged =>
      generalize erasedIs : members.eraseIdx index = erased at others
      cases others with
      | cons index' inside' secondMatched nothing merged' =>
          generalize remainingIs : erased.eraseIdx index' = remaining at nothing
          cases nothing
          rw [mergeBindings_nil_right, Option.some.injEq] at merged'
          subst merged'
          have erasedOne : erased.length = 1 := by
            have lengths := congrArg List.length remainingIs
            rw [List.length_eraseIdx_of_lt inside'] at lengths
            simp at lengths
            omega
          have twoMembers : members.length = 2 := by
            have lengths := congrArg List.length erasedIs
            rw [List.length_eraseIdx_of_lt inside] at lengths
            omega
          obtain ⟨x, y, rfl⟩ : ∃ x y, members = [x, y] := by
            match members, twoMembers with
            | [x, y], _ => exact ⟨x, y, rfl⟩
          obtain ⟨z, rfl⟩ : ∃ z, erased = [z] := by
            match erased, erasedOne with
            | [z], _ => exact ⟨z, rfl⟩
          have index'Zero : index' = 0 := by
            simp at inside'
            omega
          subst index'Zero
          have indexIs : index = 0 ∨ index = 1 := by
            simp at inside
            omega
          rcases indexIs with rfl | rfl
          · simp at erasedIs
            subst erasedIs
            exact ⟨x, _, _, _, .inl rfl, firstMatched, secondMatched, merged⟩
          · simp at erasedIs
            subst erasedIs
            exact ⟨y, _, _, _, .inr rfl, firstMatched, secondMatched, merged⟩

/-- A match of a bag of two patterns is a bag of two terms, each matched by one of them, in either order. -/
theorem matchRel_bag_two {first second : Pattern} {pattern : Pattern} {bindings : Bindings}
    (matched : MatchRel (.collection .hashBag [first, second] none) pattern bindings) :
    ∃ a b rest firstBindings secondBindings,
      (pattern = .collection .hashBag [a, b] rest ∨ pattern = .collection .hashBag [b, a] rest) ∧
        MatchRel first a firstBindings ∧ MatchRel second b secondBindings ∧
          mergeBindings firstBindings secondBindings = some bindings := by
  cases matched with
  | collection _ bag =>
      obtain ⟨a, b, firstBindings, secondBindings, shape, firstMatched, secondMatched, merged⟩ := matchBagRel_two bag
      rcases shape with rfl | rfl
      · exact ⟨a, b, _, firstBindings, secondBindings, .inl rfl, firstMatched, secondMatched, merged⟩
      · exact ⟨a, b, _, firstBindings, secondBindings, .inr rfl, firstMatched, secondMatched, merged⟩

/-! ## The instances of each law -/

theorem unfold_forward {bindings : Bindings} {source target : Pattern}
    (matched : bindings ∈ matchPattern (replicationUnfoldOf block).left source)
    (applied : applyBindings bindings (replicationUnfoldOf block).right = target) :
    ∃ process, source = .apply block.replicate [process] ∧
      target = .collection .hashBag [process, .apply block.replicate [process]] none := by
  obtain ⟨process, rfl, inner⟩ := matchRel_apply_single (matchPattern_sound matched)
  have bound := matchRel_fvar inner
  subst bound
  refine ⟨process, rfl, ?_⟩
  rw [← applied]
  simp [replicationUnfoldOf, applyBindings]

theorem unfold_reverse {bindings : Bindings} {source target : Pattern}
    (matched : bindings ∈ matchPattern (replicationUnfoldOf block).right source)
    (applied : applyBindings bindings (replicationUnfoldOf block).left = target) :
    ∃ process rest, (source = .collection .hashBag [process, .apply block.replicate [process]] rest ∨
      source = .collection .hashBag [.apply block.replicate [process], process] rest) ∧
        target = .apply block.replicate [process] := by
  obtain ⟨a, b, rest, firstBindings, secondBindings, shape, firstMatched, secondMatched, merged⟩ :=
    matchRel_bag_two (matchPattern_sound matched)
  have firstBound := matchRel_fvar firstMatched
  subst firstBound
  obtain ⟨argument, rfl, inner⟩ := matchRel_apply_single secondMatched
  have secondBound := matchRel_fvar inner
  subst secondBound
  obtain ⟨rfl, rfl⟩ := mergeBindings_same "P" a argument merged
  refine ⟨a, rest, shape, ?_⟩
  rw [← applied]
  simp [replicationUnfoldOf, applyBindings]

theorem nil_forward {bindings : Bindings} {source target : Pattern}
    (matched : bindings ∈ matchPattern (replicationNilOf block).left source)
    (applied : applyBindings bindings (replicationNilOf block).right = target) :
    source = .apply block.replicate [.apply block.unit []] ∧ target = .apply block.unit [] := by
  obtain ⟨argument, rfl, inner⟩ := matchRel_apply_single (matchPattern_sound matched)
  cases inner with
  | apply arguments _ =>
      cases arguments
      refine ⟨rfl, ?_⟩
      rw [← applied]
      simp [replicationNilOf, applyBindings]

theorem nil_reverse {bindings : Bindings} {source target : Pattern}
    (matched : bindings ∈ matchPattern (replicationNilOf block).right source)
    (applied : applyBindings bindings (replicationNilOf block).left = target) :
    source = .apply block.unit [] ∧ target = .apply block.replicate [.apply block.unit []] := by
  have related := matchPattern_sound matched
  simp only [replicationNilOf] at related
  cases related with
  | apply arguments _ =>
      cases arguments
      refine ⟨rfl, ?_⟩
      rw [← applied]
      simp [replicationNilOf, applyBindings]

theorem twice_forward {bindings : Bindings} {source target : Pattern}
    (matched : bindings ∈ matchPattern (replicationTwiceOf block).left source)
    (applied : applyBindings bindings (replicationTwiceOf block).right = target) :
    ∃ process, source = .apply block.replicate [.apply block.replicate [process]] ∧
      target = .apply block.replicate [process] := by
  obtain ⟨argument, rfl, inner⟩ := matchRel_apply_single (matchPattern_sound matched)
  obtain ⟨process, rfl, innermost⟩ := matchRel_apply_single inner
  have bound := matchRel_fvar innermost
  subst bound
  refine ⟨process, rfl, ?_⟩
  rw [← applied]
  simp [replicationTwiceOf, applyBindings]

theorem twice_reverse {bindings : Bindings} {source target : Pattern}
    (matched : bindings ∈ matchPattern (replicationTwiceOf block).right source)
    (applied : applyBindings bindings (replicationTwiceOf block).left = target) :
    ∃ process, source = .apply block.replicate [process] ∧
      target = .apply block.replicate [.apply block.replicate [process]] := by
  obtain ⟨process, rfl, inner⟩ := matchRel_apply_single (matchPattern_sound matched)
  have bound := matchRel_fvar inner
  subst bound
  refine ⟨process, rfl, ?_⟩
  rw [← applied]
  simp [replicationTwiceOf, applyBindings]

theorem par_forward {bindings : Bindings} {source target : Pattern}
    (matched : bindings ∈ matchPattern (replicationParOf block).left source)
    (applied : applyBindings bindings (replicationParOf block).right = target) :
    ∃ first second rest, (source = .apply block.replicate [.collection .hashBag [first, second] rest] ∨
      source = .apply block.replicate [.collection .hashBag [second, first] rest]) ∧
        target = .collection .hashBag [.apply block.replicate [first], .apply block.replicate [second]] none := by
  obtain ⟨argument, rfl, inner⟩ := matchRel_apply_single (matchPattern_sound matched)
  obtain ⟨a, b, rest, firstBindings, secondBindings, shape, firstMatched, secondMatched, merged⟩ :=
    matchRel_bag_two inner
  have firstBound := matchRel_fvar firstMatched
  have secondBound := matchRel_fvar secondMatched
  subst firstBound secondBound
  have bound := mergeBindings_two (by decide) a b merged
  subst bound
  refine ⟨a, b, rest, by rcases shape with rfl | rfl <;> simp, ?_⟩
  rw [← applied]
  simp [replicationParOf, applyBindings]

theorem par_reverse {bindings : Bindings} {source target : Pattern}
    (matched : bindings ∈ matchPattern (replicationParOf block).right source)
    (applied : applyBindings bindings (replicationParOf block).left = target) :
    ∃ first second rest,
      (source = .collection .hashBag [.apply block.replicate [first], .apply block.replicate [second]] rest ∨
        source = .collection .hashBag [.apply block.replicate [second], .apply block.replicate [first]] rest) ∧
        target = .apply block.replicate [.collection .hashBag [first, second] none] := by
  obtain ⟨a, b, rest, firstBindings, secondBindings, shape, firstMatched, secondMatched, merged⟩ :=
    matchRel_bag_two (matchPattern_sound matched)
  obtain ⟨first, rfl, firstInner⟩ := matchRel_apply_single firstMatched
  obtain ⟨second, rfl, secondInner⟩ := matchRel_apply_single secondMatched
  have firstBound := matchRel_fvar firstInner
  have secondBound := matchRel_fvar secondInner
  subst firstBound secondBound
  have bound := mergeBindings_two (by decide) first second merged
  subst bound
  refine ⟨first, second, rest, shape, ?_⟩
  rw [← applied]
  simp [replicationParOf, applyBindings]

theorem idempotent_forward {bindings : Bindings} {source target : Pattern}
    (matched : bindings ∈ matchPattern (replicationIdempotentOf block).left source)
    (applied : applyBindings bindings (replicationIdempotentOf block).right = target) :
    ∃ process rest, source = .collection .hashBag [.apply block.replicate [process], .apply block.replicate [process]]
      rest ∧ target = .apply block.replicate [process] := by
  obtain ⟨a, b, rest, firstBindings, secondBindings, shape, firstMatched, secondMatched, merged⟩ :=
    matchRel_bag_two (matchPattern_sound matched)
  obtain ⟨first, rfl, firstInner⟩ := matchRel_apply_single firstMatched
  obtain ⟨second, rfl, secondInner⟩ := matchRel_apply_single secondMatched
  have firstBound := matchRel_fvar firstInner
  have secondBound := matchRel_fvar secondInner
  subst firstBound secondBound
  obtain ⟨rfl, rfl⟩ := mergeBindings_same "P" first second merged
  refine ⟨first, rest, by rcases shape with rfl | rfl <;> rfl, ?_⟩
  rw [← applied]
  simp [replicationIdempotentOf, applyBindings]

theorem idempotent_reverse {bindings : Bindings} {source target : Pattern}
    (matched : bindings ∈ matchPattern (replicationIdempotentOf block).right source)
    (applied : applyBindings bindings (replicationIdempotentOf block).left = target) :
    ∃ process, source = .apply block.replicate [process] ∧
      target = .collection .hashBag [.apply block.replicate [process], .apply block.replicate [process]] none := by
  obtain ⟨process, rfl, inner⟩ := matchRel_apply_single (matchPattern_sound matched)
  have bound := matchRel_fvar inner
  subst bound
  refine ⟨process, rfl, ?_⟩
  rw [← applied]
  simp [replicationIdempotentOf, applyBindings]

end Mettapedia.GSLT.LanguageDef.RestrictionBlocks
