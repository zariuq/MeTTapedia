import Mettapedia.OSLF.MeTTaIL.MatchSpec

/-!
# Linear patterns always match

A rule a generator produces is *linear* in its metavariables: each stands at one
position and no name is minted twice.  Such a pattern imposes no consistency
condition when it is matched, so it matches any term of the right shape — and
that is what lets a generated rule be shown to *fire*, rather than only to
determine the shape of what it fired on.

The matcher merges the bindings of sibling positions and fails when two
positions bind one name to different terms.  With distinct names that failure is
unreachable, which is what the two results below say: merging fresh bindings
always succeeds, and a list of distinct metavariables matches any list of terms
of the same length.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.LinearMatch

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.MatchSpec

/-- **Merging fresh bindings always succeeds**, and the result is the extra
bindings in reverse order on top of the accumulator.  The exact shape is stated
rather than an existential, because the induction below needs to know which
names the merged list carries. -/
theorem mergeBindings_of_fresh :
    ∀ (extra accumulator : Bindings),
      (∀ name ∈ extra.map Prod.fst, name ∉ accumulator.map Prod.fst) →
      (extra.map Prod.fst).Nodup →
      mergeBindings accumulator extra = some (extra.reverse ++ accumulator)
  | [], accumulator, _, _ => by simp [mergeBindings]
  | (name, value) :: rest, accumulator, fresh, nodup => by
      have headFresh : name ∉ accumulator.map Prod.fst := fresh name (by simp)
      have notFound : accumulator.find? (fun entry => entry.1 == name) = none := by
        refine List.find?_eq_none.mpr ?_
        intro entry member
        simp only [beq_iff_eq]
        intro same
        exact headFresh (by rw [← same]; exact List.mem_map_of_mem member)
      have restFresh : ∀ other ∈ rest.map Prod.fst,
          other ∉ ((name, value) :: accumulator).map Prod.fst := by
        intro other member
        simp only [List.map_cons, List.mem_cons, not_or]
        refine ⟨?_, fresh other (by simp [member])⟩
        intro same
        exact (List.nodup_cons.mp (by simpa using nodup)).1 (same ▸ member)
      have restNodup : (rest.map Prod.fst).Nodup :=
        (List.nodup_cons.mp (by simpa using nodup)).2
      have restMerged :=
        mergeBindings_of_fresh rest ((name, value) :: accumulator) restFresh restNodup
      simp only [mergeBindings] at restMerged ⊢
      rw [List.foldlM_cons]
      simp only [notFound]
      simpa using restMerged

/-- **A list of distinct metavariables matches any list of terms of the same
length**, and the bindings it produces carry exactly those names, once each. -/
theorem matchArgs_fvars :
    ∀ (names : List String) (terms : List Pattern),
      names.Nodup → names.length = terms.length →
      ∃ bindings, bindings ∈ matchArgs (names.map Pattern.fvar) terms ∧
        (bindings.map Prod.fst).Nodup ∧
        (∀ name, name ∈ bindings.map Prod.fst ↔ name ∈ names) ∧
        (∀ pair ∈ names.zip terms, pair ∈ bindings)
  | [], [], _, _ => ⟨[], by simp [matchArgs], by simp, by simp, by simp⟩
  | [], _ :: _, _, lengths => by simp at lengths
  | _ :: _, [], _, lengths => by simp at lengths
  | name :: names, term :: terms, nodup, lengths => by
      obtain ⟨tail, tailMember, tailNodup, tailNames, tailPairs⟩ :=
        matchArgs_fvars names terms (List.nodup_cons.mp nodup).2
          (by simpa using lengths)
      have headFresh : name ∉ names := (List.nodup_cons.mp nodup).1
      have fresh : ∀ other ∈ tail.map Prod.fst,
          other ∉ ([(name, term)] : Bindings).map Prod.fst := by
        intro other member
        simp only [List.map_cons, List.map_nil, List.mem_singleton]
        intro same
        exact headFresh (same ▸ (tailNames other).mp member)
      have merged := mergeBindings_of_fresh tail [(name, term)] fresh tailNodup
      refine ⟨tail.reverse ++ [(name, term)], ?_, ?_, ?_, ?_⟩
      · simp only [List.map_cons, matchArgs, matchPattern, List.flatMap_cons,
          List.flatMap_nil, List.append_nil]
        exact List.mem_filterMap.mpr ⟨tail, tailMember, merged⟩
      · simp only [List.map_append, List.map_reverse, List.map_cons, List.map_nil]
        refine List.Nodup.append (by simpa using tailNodup) (by simp) ?_
        intro other member single
        simp only [List.mem_singleton] at single
        exact headFresh (single ▸ ((tailNames other).mp (by simpa using member)))
      · intro other
        simp only [List.map_append, List.map_reverse, List.map_cons, List.map_nil,
          List.mem_append, List.mem_reverse, List.mem_cons, List.not_mem_nil, or_false]
        constructor
        · rintro (member | rfl)
          · exact Or.inr ((tailNames other).mp member)
          · exact Or.inl rfl
        · rintro (rfl | member)
          · exact Or.inr rfl
          · exact Or.inl ((tailNames other).mpr member)
      · intro pair member
        simp only [List.zip_cons_cons, List.mem_cons] at member
        rcases member with rfl | member
        · simp
        · exact List.mem_append_left _ (List.mem_reverse.mpr (tailPairs pair member))

/-- **A binding list with distinct names is a lookup table.**  Membership of a
pair determines what the matcher's lookup returns, which is what lets a rule's
right-hand side be evaluated. -/
theorem find?_of_mem_of_nodup :
    ∀ (bindings : Bindings) {name : String} {value : Pattern},
      (bindings.map Prod.fst).Nodup → (name, value) ∈ bindings →
      bindings.find? (fun entry => entry.1 == name) = some (name, value)
  | [], _, _, _, member => by simp at member
  | (head, headValue) :: rest, name, value, nodup, member => by
      by_cases same : head = name
      · subst same
        have headOnly : (head, value) = (head, headValue) := by
          rcases List.mem_cons.mp member with equal | inTail
          · exact equal.symm ▸ rfl
          · exact absurd (List.mem_map_of_mem (f := Prod.fst) inTail)
              (List.nodup_cons.mp (by simpa using nodup)).1
        simp only [List.find?_cons, beq_self_eq_true]
        exact congrArg some (headOnly.symm)
      · have inTail : (name, value) ∈ rest := by
          rcases List.mem_cons.mp member with equal | inTail
          · exact absurd (congrArg Prod.fst equal).symm same
          · exact inTail
        have notEqual : (head == name) = false := by simpa using same
        simp only [List.find?_cons, notEqual]
        exact find?_of_mem_of_nodup rest
          (List.nodup_cons.mp (by simpa using nodup)).2 inTail

/-- **Applying the bindings a linear match produced returns the terms it
matched.**  A binding list with distinct names is a lookup table, so
substituting it into the very variables the rule minted recovers exactly what
stood at those positions.  This is what turns a match into a *step*: the rule's
right-hand side is built from those variables, and the target is therefore the
arguments themselves. -/
theorem applyBindings_fvars (bindings : Bindings)
    (nodup : (bindings.map Prod.fst).Nodup) :
    ∀ (names : List String) (terms : List Pattern),
      names.length = terms.length →
      (∀ pair ∈ names.zip terms, pair ∈ bindings) →
      (names.map Pattern.fvar).map (applyBindings bindings) = terms
  | [], [], _, _ => by simp
  | [], _ :: _, lengths, _ => by simp at lengths
  | _ :: _, [], lengths, _ => by simp at lengths
  | name :: names, term :: terms, lengths, pairs => by
      have headPair : (name, term) ∈ bindings := pairs (name, term) (by simp)
      have lookup : bindings.find? (fun entry => entry.1 == name) = some (name, term) :=
        find?_of_mem_of_nodup bindings nodup headPair
      have tail : (names.map Pattern.fvar).map (applyBindings bindings) = terms :=
        applyBindings_fvars bindings nodup names terms
          (by simpa using lengths)
          (fun pair member => pairs pair (by simp [member]))
      simp [applyBindings, lookup, tail]

/-- **A merge keeps everything the accumulator had.**  The fold only ever conses
onto its accumulator or leaves it alone, so no entry is lost.  This is the
membership counterpart of the labels bound proved in `OccurringLabels`, and it is
what an inversion needs when it has to find a particular pair in the result of a
match rather than merely bound its labels. -/
theorem mergeBindings_subset :
    ∀ (accumulator extra : Bindings) {result : Bindings},
      mergeBindings accumulator extra = some result → accumulator ⊆ result
  | accumulator, [], result, merged => by
      have same : result = accumulator := by
        simpa [mergeBindings] using merged.symm
      subst same
      exact fun _ member => member
  | accumulator, (name, value) :: rest, result, merged => by
      simp only [mergeBindings, List.foldlM_cons] at merged
      rcases found : accumulator.find? (fun pair => pair.1 == name) with _ | entry
      · rw [found] at merged
        have tail := mergeBindings_subset ((name, value) :: accumulator) rest merged
        exact fun _ member => tail (List.mem_cons_of_mem _ member)
      · rw [found] at merged
        rcases entry with ⟨entryName, existing⟩
        by_cases same : existing == value
        · simp only [same, if_pos] at merged
          exact mergeBindings_subset accumulator rest merged
        · simp only [same] at merged
          exact absurd merged (by simp)

/-! ## Inverting a linear match

`matchArgs_fvars` exhibits *a* match of a list of distinct metavariables and says
what it binds.  What an inversion needs is the other direction: that **every**
match of such a list binds the same thing.  Without it, a lemma describing one
binding list and a theorem supplying another are two different objects, and the
gap between them is exactly where an argument can go wrong unnoticed.

The three facts come out of one induction because each step needs the previous
two: freshness of the tail's names against the head needs the containment, and
`mergeBindings_of_fresh` needs the nodup as well. -/

/-- A metavariable pattern binds exactly one pair. -/
theorem matchRel_fvar_shape {name : String} {term : Pattern} {bindings : Bindings}
    (matched : MatchRel (.fvar name) term bindings) : bindings = [(name, term)] := by
  cases matched
  rfl

/-- **Every match of distinct metavariables binds each to the term at its
position**, binds nothing else, and binds no name twice. -/
theorem matchArgsRel_fvars_inversion :
    ∀ (names : List String) (terms : List Pattern) (bindings : Bindings),
      MatchArgsRel (names.map Pattern.fvar) terms bindings →
      names.Nodup →
      (∀ pair ∈ bindings, pair.1 ∈ names) ∧
        (bindings.map Prod.fst).Nodup ∧
        (∀ pair ∈ names.zip terms, pair ∈ bindings)
  | [], terms, bindings, matched, _ => by
      cases matched
      exact ⟨by simp, by simp, by simp⟩
  | name :: rest, terms, bindings, matched, nodup => by
      cases matched with
      | cons headMatch tailMatch merged =>
          rename_i term headBindings tailTerms tailBindings
          have headShape := matchRel_fvar_shape headMatch
          obtain ⟨tailNames, tailNodup, tailPairs⟩ :=
            matchArgsRel_fvars_inversion rest tailTerms tailBindings tailMatch
              (List.nodup_cons.mp nodup).2
          have headNotInRest : name ∉ rest := (List.nodup_cons.mp nodup).1
          have fresh : ∀ tailName ∈ tailBindings.map Prod.fst,
              tailName ∉ headBindings.map Prod.fst := by
            intro tailName member
            obtain ⟨pair, pairMember, pairName⟩ := List.mem_map.mp member
            rw [headShape]
            simp only [List.map_cons, List.map_nil, List.mem_singleton]
            intro same
            exact headNotInRest (same ▸ pairName ▸ tailNames pair pairMember)
          have exact := mergeBindings_of_fresh tailBindings headBindings fresh tailNodup
          rw [exact] at merged
          have shape : bindings = tailBindings.reverse ++ headBindings := by
            simpa using merged.symm
          subst shape
          rw [headShape]
          refine ⟨?_, ?_, ?_⟩
          · intro pair member
            rcases List.mem_append.mp member with inTail | inHead
            · exact List.mem_cons_of_mem _ (tailNames pair (List.mem_reverse.mp inTail))
            · simp only [List.mem_singleton] at inHead
              exact inHead ▸ List.mem_cons_self ..
          · simp only [List.map_append, List.map_reverse, List.map_cons, List.map_nil]
            refine List.Nodup.append (List.nodup_reverse.mpr tailNodup) (by simp) ?_
            intro candidate inReverse inSingleton
            simp only [List.mem_singleton] at inSingleton
            subst inSingleton
            obtain ⟨pair, pairMember, pairName⟩ :=
              List.mem_map.mp (List.mem_reverse.mp inReverse)
            exact headNotInRest (pairName ▸ tailNames pair pairMember)
          · intro pair member
            simp only [List.zip_cons_cons, List.mem_cons] at member
            rcases member with rfl | inTail
            · exact List.mem_append_right _ (by simp)
            · exact List.mem_append_left _ (List.mem_reverse.mpr (tailPairs pair inTail))

end Mettapedia.OSLF.MeTTaIL.LinearMatch
