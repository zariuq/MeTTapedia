import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformPresentation
import Mettapedia.OSLF.MeTTaIL.DecimalNames
import Mettapedia.OSLF.Framework.GeneratedHypercube

/-!
# The generated slot family, at every arity

`PlatformPresentation` checks the redex-position generator on the platform's
joins at arities one, two and three, by computation.  That is a check of three
instances, not a law.  This module proves the law: for every arity the join of
that arity relies on the parallel remainder together with its channels and
values, and therefore carries `2n + 2` sort slots.

Three things have to be established and each is a real obligation.  The scan of
a redex's siblings has to be computed for a generated list rather than a fixed
one; the generated variable names have to be distinguishable, which is decimal
printing being injective; and the deduplication the generator applies has to be
shown to remove exactly the channel names the receiver repeats.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformSlotLaws

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.RedexPosition
open Mettapedia.OSLF.Framework.GeneratedHypercube
open Mettapedia.OSLF.MeTTaIL.DecimalNames
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformPresentation

/-! ## The generated names are distinguishable

Every pair the deduplication has to tell apart differs in its first character,
so one comparison settles each.  The decimal-name machinery is shared:
`MeTTaIL.DecimalNames` is where a generator's naming discipline lives. -/

theorem channelVar_ne_valueVar (first second : Nat) :
    ("chan" ++ toString first) ≠ ("val" ++ toString second) :=
  literal_ne rfl rfl (by intro _ _ same; simp at same) _ _

theorem channelVar_ne_continuationVar (index : Nat) :
    ("chan" ++ toString index) ≠ continuationVar := by
  have : continuationVar = "cont" ++ "" := rfl
  rw [this]
  exact literal_ne rfl rfl (by intro _ _ same; simp at same) _ _

theorem valueVar_ne_continuationVar (index : Nat) :
    ("val" ++ toString index) ≠ continuationVar := by
  have : continuationVar = "cont" ++ "" := rfl
  rw [this]
  exact literal_ne rfl rfl (by intro _ _ same; simp at same) _ _

theorem channelVar_ne_restVar (index : Nat) :
    ("chan" ++ toString index) ≠ restVar := by
  have : restVar = "rest" ++ "" := rfl
  rw [this]
  exact literal_ne rfl rfl (by intro _ _ same; simp at same) _ _

theorem valueVar_ne_restVar (index : Nat) :
    ("val" ++ toString index) ≠ restVar := by
  have : restVar = "rest" ++ "" := rfl
  rw [this]
  exact literal_ne rfl rfl (by intro _ _ same; simp at same) _ _

/-! ## The generated variable lists -/

theorem participantVars_succ (arity : Nat) :
    participantVars (arity + 1)
      = participantVars arity ++ ["chan" ++ toString arity, "val" ++ toString arity] := by
  simp [participantVars, List.range_succ, List.flatMap_append]

theorem channelVars_succ (arity : Nat) :
    channelVars (arity + 1) = channelVars arity ++ ["chan" ++ toString arity] := by
  simp [channelVars, List.range_succ]

theorem mem_participantVars_iff {name : String} {arity : Nat} :
    name ∈ participantVars arity ↔
      ∃ index, index < arity ∧
        (name = "chan" ++ toString index ∨ name = "val" ++ toString index) := by
  induction arity with
  | zero => simp [participantVars]
  | succ previous inductionHypothesis =>
      rw [participantVars_succ]
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
        inductionHypothesis]
      constructor
      · rintro (⟨index, lt, holds⟩ | holds | holds)
        · exact ⟨index, by omega, holds⟩
        · exact ⟨previous, by omega, Or.inl holds⟩
        · exact ⟨previous, by omega, Or.inr holds⟩
      · rintro ⟨index, lt, holds⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp lt with smaller | rfl
        · exact Or.inl ⟨index, smaller, holds⟩
        · rcases holds with holds | holds
          · exact Or.inr (Or.inl holds)
          · exact Or.inr (Or.inr holds)

theorem mem_channelVars_iff {name : String} {arity : Nat} :
    name ∈ channelVars arity ↔ ∃ index, index < arity ∧ name = "chan" ++ toString index := by
  simp [channelVars, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨index, lt, rfl⟩; exact ⟨index, lt, rfl⟩
  · rintro ⟨index, lt, rfl⟩; exact ⟨index, lt, rfl⟩

/-- **The participant list has no repetitions**, which is decimal printing being
injective and the two prefixes being different. -/
theorem participantVars_nodup (arity : Nat) : (participantVars arity).Nodup := by
  induction arity with
  | zero => simp [participantVars]
  | succ previous inductionHypothesis =>
      rw [participantVars_succ]
      refine List.Nodup.append inductionHypothesis ?_ ?_
      · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
          List.nodup_nil, and_true]
        exact ⟨channelVar_ne_valueVar previous previous, by simp⟩
      · intro name member fresh
        obtain ⟨index, lt, shape⟩ := mem_participantVars_iff.mp member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at fresh
        rcases shape with rfl | rfl
        · rcases fresh with same | same
          · have equal : index = previous := prefixed_injective "chan" same
            omega
          · exact channelVar_ne_valueVar index previous same
        · rcases fresh with same | same
          · exact channelVar_ne_valueVar previous index same.symm
          · have equal : index = previous := prefixed_injective "val" same
            omega

/-- Every channel name is a participant name. -/
theorem channelVars_subset_participantVars (arity : Nat) :
    ∀ name ∈ channelVars arity, name ∈ participantVars arity := by
  intro name member
  obtain ⟨index, lt, rfl⟩ := mem_channelVars_iff.mp member
  exact mem_participantVars_iff.mpr ⟨index, lt, Or.inl rfl⟩

theorem restVar_not_mem_participantVars (arity : Nat) :
    restVar ∉ participantVars arity := by
  intro member
  obtain ⟨index, -, shape⟩ := mem_participantVars_iff.mp member
  rcases shape with shape | shape
  · exact channelVar_ne_restVar index shape.symm
  · exact valueVar_ne_restVar index shape.symm

theorem continuationVar_not_mem_participantVars (arity : Nat) :
    continuationVar ∉ participantVars arity := by
  intro member
  obtain ⟨index, -, shape⟩ := mem_participantVars_iff.mp member
  rcases shape with shape | shape
  · exact channelVar_ne_continuationVar index shape.symm
  · exact valueVar_ne_continuationVar index shape.symm


/-! ## The sibling scan of a generated redex

The generator's context reads every child except the one it focuses.  Two
lemmas compute that scan for a list given by a generator rather than written
out: below the focus nothing is dropped, and at the focus exactly one element
is. -/

private theorem flatMap_zipIdx_of_lt (collect : Pattern → List String) (target : Nat) :
    ∀ (elements : List Pattern) (start : Nat), target < start →
      ((elements.zipIdx start).flatMap
          fun entry => if entry.2 = target then [] else collect entry.1)
        = elements.flatMap collect
  | [], _, _ => rfl
  | element :: rest, start, below => by
      simp only [List.zipIdx_cons, List.flatMap_cons,
        if_neg (by omega : ¬ start = target)]
      rw [flatMap_zipIdx_of_lt collect target rest (start + 1) (by omega)]

private theorem flatMap_zipIdx_skip (collect : Pattern → List String) :
    ∀ (before : List Pattern) (focus : Pattern) (after : List Pattern) (start target : Nat),
      target = start + before.length →
      (((before ++ focus :: after).zipIdx start).flatMap
          fun entry => if entry.2 = target then [] else collect entry.1)
        = before.flatMap collect ++ after.flatMap collect
  | [], focus, after, start, target, shape => by
      have same : start = target := by
        simp only [List.length_nil, Nat.add_zero] at shape; omega
      simp only [List.nil_append, List.zipIdx_cons, List.flatMap_cons, if_pos same,
        List.flatMap_nil, List.nil_append]
      rw [flatMap_zipIdx_of_lt collect target after (start + 1) (by omega)]
  | element :: rest, focus, after, start, target, shape => by
      have notHere : ¬ start = target := by simp only [List.length_cons] at shape; omega
      have deeper : target = (start + 1) + rest.length := by
        simp only [List.length_cons] at shape; omega
      simp only [List.cons_append, List.zipIdx_cons, List.flatMap_cons, if_neg notHere]
      rw [flatMap_zipIdx_skip collect rest focus after (start + 1) target deeper]
      simp

private theorem flatMap_zipIdx_head (collect : Pattern → List String)
    (focus : Pattern) (after : List Pattern) :
    (((focus :: after).zipIdx 0).flatMap
        fun entry => if entry.2 = 0 then [] else collect entry.1)
      = after.flatMap collect := by
  have skipped := flatMap_zipIdx_skip collect [] focus after 0 0 (by simp)
  simpa using skipped

/-! ## The generated lists, read by the generator -/

theorem channelPatterns_length (arity : Nat) : (channelPatterns arity).length = arity := by
  simp [channelPatterns, channelVars]

theorem outputs_succ (arity : Nat) :
    outputs (arity + 1) = outputs arity ++
      [.apply outLabel
        [.fvar ("chan" ++ toString arity), .fvar ("val" ++ toString arity)]] := by
  simp [outputs, List.range_succ]

theorem channelPatterns_succ (arity : Nat) :
    channelPatterns (arity + 1)
      = channelPatterns arity ++ [.fvar ("chan" ++ toString arity)] := by
  simp [channelPatterns, channelVars_succ]

theorem fvarNames_outputs (arity : Nat) :
    (outputs arity).flatMap fvarNames = participantVars arity := by
  induction arity with
  | zero => simp [outputs, participantVars]
  | succ previous inductionHypothesis =>
      rw [outputs_succ, List.flatMap_append, inductionHypothesis, participantVars_succ]
      simp [fvarNames, fvarNamesList]

theorem fvarNames_channelPatterns (arity : Nat) :
    (channelPatterns arity).flatMap fvarNames = channelVars arity := by
  induction arity with
  | zero => simp [channelPatterns, channelVars]
  | succ previous inductionHypothesis =>
      rw [channelPatterns_succ, List.flatMap_append, inductionHypothesis, channelVars_succ]
      simp [fvarNames]

/-! ## The context and focus of a generated join -/

theorem contextFreeVars_receiver (label : String) (arity : Nat) :
    contextFreeVars (receiver label arity) [arity] = channelVars arity := by
  have focusChild :
      (channelPatterns arity ++ [Pattern.lambda none (Pattern.fvar continuationVar)])[arity]?
        = some (Pattern.lambda none (Pattern.fvar continuationVar)) := by
    rw [List.getElem?_append_right (by rw [channelPatterns_length])]
    simp [channelPatterns_length]
  simp only [receiver, contextFreeVars, localVars, children, childAt]
  rw [flatMap_zipIdx_skip fvarNames (channelPatterns arity)
      (Pattern.lambda none (Pattern.fvar continuationVar)) [] 0 arity
      (by simp [channelPatterns_length]),
    focusChild]
  simp [fvarNames_channelPatterns]

theorem contextFreeVars_joinRule (arity : Nat) :
    contextFreeVars (joinRule arity).left (joinPos arity)
      = restVar :: (participantVars arity ++ channelVars arity) := by
  have head : childAt (joinRule arity).left 0 = some (receiver (joinLabel arity) arity) := rfl
  have childrenEq : children (joinRule arity).left
      = receiver (joinLabel arity) arity :: outputs arity := rfl
  have localEq : localVars (joinRule arity).left = [restVar] := rfl
  have unfolded : contextFreeVars (joinRule arity).left (joinPos arity)
      = localVars (joinRule arity).left
        ++ (((children (joinRule arity).left).zipIdx 0).flatMap
            fun ci => if ci.2 = 0 then [] else fvarNames ci.1)
        ++ (match childAt (joinRule arity).left 0 with
            | some child => contextFreeVars child [arity]
            | none => []) := rfl
  rw [unfolded, head, localEq, childrenEq,
    flatMap_zipIdx_head fvarNames (receiver (joinLabel arity) arity) (outputs arity),
    fvarNames_outputs]
  show [restVar] ++ participantVars arity
      ++ contextFreeVars (receiver (joinLabel arity) arity) [arity]
    = restVar :: (participantVars arity ++ channelVars arity)
  rw [contextFreeVars_receiver]
  simp

theorem focusFreeVars_joinRule (arity : Nat) :
    focusFreeVars (joinRule arity).left (joinPos arity) = [continuationVar] := by
  have head : childAt (joinRule arity).left 0 = some (receiver (joinLabel arity) arity) := rfl
  have focusChild : childAt (receiver (joinLabel arity) arity) arity
      = some (Pattern.lambda none (Pattern.fvar continuationVar)) := by
    simp only [receiver, childAt, children]
    rw [List.getElem?_append_right (by rw [channelPatterns_length])]
    simp [channelPatterns_length]
  have inner : subtermAt (joinRule arity).left (joinPos arity)
      = some (Pattern.lambda none (Pattern.fvar continuationVar)) := by
    have outerStep : subtermAt (joinRule arity).left (joinPos arity)
        = (childAt (joinRule arity).left 0).bind
            fun child => subtermAt child [arity] := rfl
    rw [outerStep, head]
    show subtermAt (receiver (joinLabel arity) arity) [arity] = _
    have innerStep : subtermAt (receiver (joinLabel arity) arity) [arity]
        = (childAt (receiver (joinLabel arity) arity) arity).bind
            fun child => subtermAt child [] := rfl
    rw [innerStep, focusChild]
    rfl
  rw [focusFreeVars, inner]
  simp [fvarNames]

/-! ## The rely parameters and the slot count

The generator deduplicates the context's free variables.  Here that removes
exactly the channel names the receiver repeats, and the receiver repeats all of
them: what is left is the parallel remainder together with each participant's
channel and value. -/

theorem eraseDups_of_nodup {α : Type} [DecidableEq α] :
    ∀ {list : List α}, list.Nodup → list.eraseDups = list
  | [], _ => rfl
  | head :: tail, nodup => by
      rw [List.eraseDups_cons]
      have notMem : head ∉ tail := (List.nodup_cons.mp nodup).1
      have filterEq : (tail.filter fun element => !element == head) = tail := by
        refine List.filter_eq_self.mpr ?_
        intro element member
        simp only [Bool.not_eq_eq_eq_not, Bool.not_true, beq_eq_false_iff_ne, ne_eq]
        rintro rfl
        exact notMem member
      rw [filterEq, eraseDups_of_nodup (List.nodup_cons.mp nodup).2]

/-- **The rely parameters of a generated join, at every arity.** -/
theorem joinRule_relyVars (arity : Nat) :
    relyVars (joinRule arity).left (joinPos arity) = restVar :: participantVars arity := by
  have nodup : (restVar :: participantVars arity).Nodup :=
    List.nodup_cons.mpr ⟨restVar_not_mem_participantVars arity, participantVars_nodup arity⟩
  have notContinuation : ∀ name ∈ restVar :: (participantVars arity ++ channelVars arity),
      name ≠ continuationVar := by
    intro name member
    simp only [List.mem_cons, List.mem_append] at member
    rcases member with rfl | member | member
    · decide
    · intro same
      exact continuationVar_not_mem_participantVars arity (same ▸ member)
    · intro same
      exact continuationVar_not_mem_participantVars arity
        (same ▸ channelVars_subset_participantVars arity name member)
  have kept : ((restVar :: (participantVars arity ++ channelVars arity)).filter
      (fun name => !([continuationVar].contains name)))
      = restVar :: (participantVars arity ++ channelVars arity) := by
    refine List.filter_eq_self.mpr ?_
    intro name member
    simp only [List.contains_cons, List.contains_nil, Bool.or_false, Bool.not_eq_eq_eq_not,
      Bool.not_true, beq_eq_false_iff_ne, ne_eq]
    exact fun same => notContinuation name member same
  have removed : (channelVars arity).removeAll (restVar :: participantVars arity) = [] := by
    refine List.filter_eq_nil_iff.mpr ?_
    intro name member
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Bool.not_eq_false, List.elem_eq_mem,
      decide_eq_true_eq]
    exact List.mem_cons_of_mem _ (channelVars_subset_participantVars arity name member)
  have split : restVar :: (participantVars arity ++ channelVars arity)
      = (restVar :: participantVars arity) ++ channelVars arity := by simp
  rw [relyVars, focusFreeVars_joinRule, contextFreeVars_joinRule, kept, split,
    List.eraseDups_append, eraseDups_of_nodup nodup, removed]
  simp

/-- **And the slot count: two per participant, plus the remainder and the
output.**  Checked at three arities before; proved at all of them now. -/
theorem joinRule_slotCount (arity : Nat) :
    slotCount (joinRule arity).left (joinPos arity) = 2 * arity + 2 := by
  rw [slotCount, joinRule_relyVars]
  simp [participantVars_length]

/-- **And no slot is minted for an undeclared variable, at any arity.**  The
generated rules declare every metavariable they use. -/
theorem joinRule_relyVars_declared (arity : Nat) :
    RelyVarsDeclared (joinRule arity) (joinPos arity) = true := by
  rw [RelyVarsDeclared, joinRule_relyVars]
  refine List.all_eq_true.mpr ?_
  intro name member
  refine List.any_eq_true.mpr ?_
  simp only [List.mem_cons] at member
  rcases member with rfl | member
  · exact ⟨(restVar, TypeExpr.proc), by simp [joinRule], by simp⟩
  · obtain ⟨index, lt, shape⟩ := mem_participantVars_iff.mp member
    rcases shape with rfl | rfl
    · exact ⟨("chan" ++ toString index, TypeExpr.name), by
        simp [joinRule, channelVars, List.mem_append, List.mem_map, List.mem_range]
        exact Or.inl ⟨index, lt, rfl⟩, by simp⟩
    · exact ⟨("val" ++ toString index, TypeExpr.proc), by
        simp [joinRule, valueVars, List.mem_append, List.mem_map, List.mem_range]
        exact Or.inr (Or.inl ⟨index, lt, rfl⟩), by simp⟩


/-! ## The generated constructor labels, at every arity list

`PlatformPresentation` checks that the presentation's labels are distinct at two
arity families.  Here that is a law: the three generated former families are
injective in the arity, pairwise distinct, and distinct from the five fixed
formers, so a presentation over any repetition-free arity list declares no name
twice.  This is what the arity indexing of the bundle former was introduced
for. -/

theorem joinLabel_injective {first second : Nat} (same : joinLabel first = joinLabel second) :
    first = second :=
  prefixed_injective "Join" same

theorem persistentJoinLabel_injective {first second : Nat}
    (same : persistentJoinLabel first = persistentJoinLabel second) : first = second :=
  prefixed_injective "PJoin" same

theorem tupleLabel_injective {first second : Nat}
    (same : tupleLabel first = tupleLabel second) : first = second :=
  prefixed_injective "Tuple" same

theorem joinLabel_ne_persistentJoinLabel (first second : Nat) :
    joinLabel first ≠ persistentJoinLabel second :=
  literal_ne rfl rfl (by intro _ _ same; simp at same) _ _

theorem joinLabel_ne_tupleLabel (first second : Nat) :
    joinLabel first ≠ tupleLabel second :=
  literal_ne rfl rfl (by intro _ _ same; simp at same) _ _

theorem persistentJoinLabel_ne_tupleLabel (first second : Nat) :
    persistentJoinLabel first ≠ tupleLabel second :=
  literal_ne rfl rfl (by intro _ _ same; simp at same) _ _

/-- The five formers the presentation declares outright. -/
def fixedLabels : List String := ["Stop", "NQuote", "PDrop", "Par", "Out"]

theorem joinLabel_not_fixed (arity : Nat) : joinLabel arity ∉ fixedLabels := by
  intro member
  simp only [fixedLabels, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h <;>
    exact prefixed_ne_literal "Join" _ (toString arity)
      (by intro tail same; simp at same) h

theorem persistentJoinLabel_not_fixed (arity : Nat) :
    persistentJoinLabel arity ∉ fixedLabels := by
  intro member
  simp only [fixedLabels, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h <;>
    exact prefixed_ne_literal "PJoin" _ (toString arity)
      (by intro tail same; simp at same) h

theorem tupleLabel_not_fixed (arity : Nat) : tupleLabel arity ∉ fixedLabels := by
  intro member
  simp only [fixedLabels, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with h | h | h | h | h <;>
    exact prefixed_ne_literal "Tuple" _ (toString arity)
      (by intro tail same; simp at same) h

/-- The labels a single arity generates. -/
def generatedLabels (arity : Nat) : List String :=
  [joinLabel arity, persistentJoinLabel arity, tupleLabel arity]

theorem mem_generatedLabels_iff {name : String} {arity : Nat} :
    name ∈ generatedLabels arity ↔
      name = joinLabel arity ∨ name = persistentJoinLabel arity ∨ name = tupleLabel arity := by
  simp [generatedLabels]

theorem generatedLabels_nodup (arity : Nat) : (generatedLabels arity).Nodup := by
  simp only [generatedLabels, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    List.nodup_nil, and_true]
  refine ⟨?_, ?_⟩
  · push_neg
    exact ⟨joinLabel_ne_persistentJoinLabel arity arity, joinLabel_ne_tupleLabel arity arity⟩
  · exact ⟨persistentJoinLabel_ne_tupleLabel arity arity, not_false⟩

theorem generatedLabels_disjoint {first second : Nat} (distinct : first ≠ second) :
    ∀ name ∈ generatedLabels first, name ∉ generatedLabels second := by
  intro name member fresh
  rcases mem_generatedLabels_iff.mp member with rfl | rfl | rfl <;>
    rcases mem_generatedLabels_iff.mp fresh with same | same | same
  · exact distinct (joinLabel_injective same)
  · exact joinLabel_ne_persistentJoinLabel first second same
  · exact joinLabel_ne_tupleLabel first second same
  · exact joinLabel_ne_persistentJoinLabel second first same.symm
  · exact distinct (persistentJoinLabel_injective same)
  · exact persistentJoinLabel_ne_tupleLabel first second same
  · exact joinLabel_ne_tupleLabel second first same.symm
  · exact persistentJoinLabel_ne_tupleLabel second first same.symm
  · exact distinct (tupleLabel_injective same)

theorem generated_not_fixed (arity : Nat) :
    ∀ name ∈ generatedLabels arity, name ∉ fixedLabels := by
  intro name member
  rcases mem_generatedLabels_iff.mp member with rfl | rfl | rfl
  · exact joinLabel_not_fixed arity
  · exact persistentJoinLabel_not_fixed arity
  · exact tupleLabel_not_fixed arity

theorem generatedLabels_flatMap_nodup :
    ∀ {arities : List Nat}, arities.Nodup → (arities.flatMap generatedLabels).Nodup
  | [], _ => by simp
  | arity :: rest, nodup => by
      have head : arity ∉ rest := (List.nodup_cons.mp nodup).1
      have tail : rest.Nodup := (List.nodup_cons.mp nodup).2
      simp only [List.flatMap_cons]
      refine List.Nodup.append (generatedLabels_nodup arity)
        (generatedLabels_flatMap_nodup tail) ?_
      intro name member fresh
      obtain ⟨other, otherMember, otherName⟩ := List.mem_flatMap.mp fresh
      have distinct : arity ≠ other := by
        intro same; exact head (same ▸ otherMember)
      exact generatedLabels_disjoint distinct name member otherName

/-- **The presentation declares no name twice**, over any repetition-free list
of arities. -/
theorem rhoPlatform_labels_nodup {arities : List Nat} (nodup : arities.Nodup) :
    ((rhoPlatform arities).terms.map GrammarRule.label).Nodup := by
  have shape : (rhoPlatform arities).terms.map GrammarRule.label
      = fixedLabels ++ arities.flatMap generatedLabels := by
    simp only [rhoPlatform, List.map_cons, List.map_flatMap, fixedLabels, generatedLabels,
      List.cons_append, List.nil_append]
    rfl
  rw [shape]
  refine List.Nodup.append (by decide) (generatedLabels_flatMap_nodup nodup) ?_
  intro name member fresh
  obtain ⟨arity, -, generated⟩ := List.mem_flatMap.mp fresh
  exact generated_not_fixed arity name generated member


end Mettapedia.Languages.ProcessCalculi.RhoCalculus.PlatformSlotLaws
