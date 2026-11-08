import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Observation

/-!
# What private equivalence keeps: the client's view

Private equivalence for the escaped identities `E` is characterized by three readouts
(`privatelyEquivalent_iff`): the solutions of the knowledge, which escaped identities are present,
and the bag of the labels present. It forgets exactly the identities of the private present
occurrences, and keeps their labels and their number.

The proof moves one private occurrence at a time: an occurrence present only at the first state has
a partner of the same label present only at the second (the bags agree on the shared part), neither
has escaped, and swapping them shrinks the difference (`exists_private_map`).

## The two ends of the scale

* **Nothing escaped** (`privatelyEquivalent_empty_iff`): the knowledge and the bag of labels, which
  are the two components of R44's nominal end. The forget-all end is private equivalence for a
  client that has seen nothing, and only for such a client
  (`Observation.ObservationControls.forget_all_not_respected`).
* **Everything escaped** (`privatelyEquivalent_iff_sameUpTo`): when every present identity has
  escaped, private equivalence is equality up to solutions, the identity end of R41
  (`classEnd`), under which every made row is a record.

The client-respecting end interpolates between them, and a client's escaped identities decide where
on that scale its readout sits.

## Alternatives under fresh names

A firing and its alternative under a fresh name are privately equivalent exactly when neither name
has escaped (`fresh_alternative_equivalent_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation

open AnnotatedRuns
open GuardFreeProcessOrders (SameUpTo)

universe uT uS uO

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

section Views

variable {label : O → T} {E : Finset O}

/-- **The labels outside the shared part agree**: if two finite sets carry the same bag of labels,
so do the occurrences of each that the other lacks. -/
theorem labels_sdiff {P Q : Finset O} (bags : P.val.map label = Q.val.map label) :
    (P.val.filter fun o => o ∉ Q).map label = (Q.val.filter fun o => o ∉ P).map label := by
  have shared : P.val.filter (fun o => o ∈ Q) = Q.val.filter (fun o => o ∈ P) :=
    (Multiset.Nodup.ext (Multiset.Nodup.filter _ P.nodup) (Multiset.Nodup.filter _ Q.nodup)).mpr
      fun o => by simp only [Multiset.mem_filter, Finset.mem_val]; exact ⟨fun h => ⟨h.2, h.1⟩,
        fun h => ⟨h.2, h.1⟩⟩
  have whole := bags
  rw [← Multiset.filter_add_not (fun o => o ∈ Q) P.val,
    ← Multiset.filter_add_not (fun o => o ∈ P) Q.val, Multiset.map_add, Multiset.map_add,
    shared] at whole
  exact add_left_cancel whole

/-- **A partner for every unshared occurrence**: an occurrence present only in the first set has a
partner of the same label present only in the second. -/
theorem exists_partner {P Q : Finset O} (bags : P.val.map label = Q.val.map label) {c : O}
    (inP : c ∈ P) (notQ : c ∉ Q) : ∃ d, d ∈ Q ∧ d ∉ P ∧ label d = label c := by
  have mem : label c ∈ (P.val.filter fun o => o ∉ Q).map label :=
    Multiset.mem_map_of_mem label (Multiset.mem_filter.mpr ⟨inP, notQ⟩)
  rw [labels_sdiff bags] at mem
  obtain ⟨d, member, same⟩ := Multiset.mem_map.mp mem
  obtain ⟨inQ, notP⟩ := Multiset.mem_filter.mp member
  exact ⟨d, inQ, notP, same⟩

/-- **A private renaming carries one set onto the other** when they agree on the escaped identities
and carry the same bag of labels. -/
theorem exists_private_map :
    ∀ (n : ℕ) {P Q : Finset O}, (P \ Q).card = n → (∀ o ∈ E, o ∈ P ↔ o ∈ Q) →
      P.val.map label = Q.val.map label →
        ∃ π : O ≃ O, PrivateRenaming label E π ∧ P.map π.toEmbedding = Q
  | 0, P, Q, size, escaped, bags => by
      have sub : P ⊆ Q := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp size)
      have cards : P.card = Q.card := by
        have counted := congrArg Multiset.card bags
        simpa only [Multiset.card_map, Finset.card_val] using counted
      refine ⟨Equiv.refl O, .refl, ?_⟩
      rw [Equiv.refl_toEmbedding, Finset.map_refl]
      exact Finset.eq_of_subset_of_card_le sub cards.ge
  | n + 1, P, Q, size, escaped, bags => by
      obtain ⟨c, inDiff⟩ := Finset.card_pos.mp (by rw [size]; exact Nat.succ_pos n)
      obtain ⟨inP, notQ⟩ := Finset.mem_sdiff.mp inDiff
      obtain ⟨d, inQ, notP, same⟩ := exists_partner bags inP notQ
      have privateC : c ∉ E := fun escapedC => notQ ((escaped c escapedC).mp inP)
      have privateD : d ∉ E := fun escapedD => notP ((escaped d escapedD).mpr inQ)
      have swapPrivate : PrivateRenaming label E (Equiv.swap c d) :=
        ⟨swap_keeps same, fun o member => Equiv.swap_apply_of_ne_of_ne
          (fun isC => privateC (isC ▸ member)) (fun isD => privateD (isD ▸ member))⟩
      have moved : ∀ o, o ∈ P.map (Equiv.swap c d).toEmbedding ↔ Equiv.swap c d o ∈ P := by
        intro o
        rw [Finset.mem_map_equiv, Equiv.symm_swap]
      have smaller : (P.map (Equiv.swap c d).toEmbedding \ Q).card = n := by
        have diff : P.map (Equiv.swap c d).toEmbedding \ Q = (P \ Q).erase c := by
          ext o
          rw [Finset.mem_sdiff, moved, Finset.mem_erase, Finset.mem_sdiff]
          by_cases isC : o = c
          · subst isC
            rw [Equiv.swap_apply_left]
            exact ⟨fun h => absurd h.1 notP, fun h => absurd rfl h.1⟩
          · by_cases isD : o = d
            · subst isD
              rw [Equiv.swap_apply_right]
              exact ⟨fun h => absurd inQ h.2, fun h => absurd inQ h.2.2⟩
            · rw [Equiv.swap_apply_of_ne_of_ne isC isD]
              exact ⟨fun h => ⟨isC, h⟩, fun h => h.2⟩
        rw [diff, Finset.card_erase_of_mem inDiff, size]
        rfl
      have stillEscaped : ∀ o ∈ E, o ∈ P.map (Equiv.swap c d).toEmbedding ↔ o ∈ Q := by
        intro o member
        rw [moved, swapPrivate.fixes o member]
        exact escaped o member
      have stillBags : (P.map (Equiv.swap c d).toEmbedding).val.map label = Q.val.map label := by
        rw [labels_rename swapPrivate.keeps]
        exact bags
      obtain ⟨ρ, privateρ, onto⟩ := exists_private_map n smaller stillEscaped stillBags
      refine ⟨(Equiv.swap c d).trans ρ, swapPrivate.trans privateρ, ?_⟩
      rw [Equiv.trans_toEmbedding, ← Finset.map_map, onto]

end Views

section Characterization

variable (A : SubstitutionAction T S) (label : O → T) (E : Finset O)

/-- **The client's view characterizes private equivalence**: two configurations are privately
equivalent exactly when their knowledge has the same solutions, the same escaped identities are
present, and the same bag of labels is present. -/
theorem privatelyEquivalent_iff (C D : Configuration T O) :
    PrivatelyEquivalent A label E C D ↔
      A.Equivalent C.equations D.equations ∧ (∀ o ∈ E, o ∈ C.present ↔ o ∈ D.present) ∧
        C.present.val.map label = D.present.val.map label := by
  constructor
  · intro h
    exact ⟨h.solutions, fun o member => h.escaped_iff member, h.labels_eq⟩
  · rintro ⟨solutions, escaped, bags⟩
    obtain ⟨π, priv, onto⟩ := exists_private_map _ rfl escaped bags
    exact ⟨π, priv, solutions, onto⟩

/-- **Nothing escaped**: private equivalence is equality of the knowledge's solutions and of the bag
of labels, the two components of the nominal end. -/
theorem privatelyEquivalent_empty_iff (C D : Configuration T O) :
    PrivatelyEquivalent A label ∅ C D ↔
      A.Equivalent C.equations D.equations ∧ C.present.val.map label = D.present.val.map label := by
  rw [privatelyEquivalent_iff]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, fun o member => absurd member (Finset.notMem_empty o), h.2⟩⟩

omit [DecidableEq O] in
/-- **Everything escaped**: when every present identity has escaped, private equivalence is
equality up to solutions, the identity end. -/
theorem privatelyEquivalent_iff_sameUpTo {C D : Configuration T O}
    (escapedC : C.present ⊆ E) (escapedD : D.present ⊆ E) :
    PrivatelyEquivalent A label E C D ↔ SameUpTo A C D := by
  constructor
  · intro h
    refine ⟨h.solutions, ?_⟩
    ext o
    constructor
    · intro member
      exact (h.escaped_iff (escapedC member)).mp member
    · intro member
      exact (h.escaped_iff (escapedD member)).mpr member
  · exact PrivatelyEquivalent.of_sameUpTo

end Characterization

section Alternatives

variable {A : SubstitutionAction T S} {label : O → T} {E : Finset O}
  {f : Firing T S O} {C : Configuration T O} {r r' : O}

/-- **A firing and its alternative under a fresh name are privately equivalent exactly when neither
name has escaped.** -/
theorem fresh_alternative_equivalent_iff (valid : f.Valid A label C) (made : r ∈ f.selection.made)
    (absent : r' ∉ C.present) (same : label r' = label r) (new : r' ∉ f.names) :
    PrivatelyEquivalent A label E (f.result label C) ((f.rename (Equiv.swap r r')).result label C) ↔
      r ∉ E ∧ r' ∉ E := by
  constructor
  · intro h
    refine ⟨fun seen => fresh_alternative_separated valid made absent same new seen h,
      fun seen' => ?_⟩
    have there : r' ∈ ((f.rename (Equiv.swap r r')).result label C).present := by
      rw [fresh_alternative_result valid made absent same]
      exact Finset.mem_map.mpr ⟨r, result_present_iff.mpr (Or.inr made), by simp⟩
    rcases result_present_iff.mp ((h.escaped_iff seen').mpr there) with ⟨present, -⟩ | inMade
    · exact absent present
    · exact new (by simp [Firing.names, inMade])
  · rintro ⟨unseen, unseen'⟩
    exact fresh_alternative_equivalent valid made absent same unseen unseen'

end Alternatives

/-! ## Controls -/

namespace ViewControls

open ConstraintMultisetRewriting.Controls (A)
open AnnotatedRuns.Controls (label)
open ObservationControls (row holder)

/-- **Two private rows of one label against two others**: the states `{20, 21}` and `{22, 23}` are
equivalent for a client that has seen nothing, by the characterization. -/
theorem two_private_rows :
    PrivatelyEquivalent A label ∅ ⟨[], {20, 21}⟩ ⟨[], {22, 23}⟩ :=
  (privatelyEquivalent_empty_iff A label _ _).mpr ⟨fun _ => Iff.rfl, rfl⟩

/-- **One shared escaped row**: `{20, 21}` and `{20, 22}` are equivalent for the client holding
`20`, which sees `20` in both; `{20, 21}` and `{21, 22}` are not. -/
theorem shared_escaped_row :
    PrivatelyEquivalent A label holder.escaped ⟨[], {20, 21}⟩ ⟨[], {20, 22}⟩ ∧
      ¬ PrivatelyEquivalent A label holder.escaped ⟨[], {20, 21}⟩ ⟨[], {21, 22}⟩ := by
  have escapedSet : holder.escaped = {20} := by decide
  refine ⟨(privatelyEquivalent_iff A label _ _ _).mpr ⟨fun _ => Iff.rfl, ?_, rfl⟩, fun h => ?_⟩
  · intro o member
    rw [escapedSet, Finset.mem_singleton] at member
    subst member
    decide
  · have seen := (h.escaped_iff (o := 20) (by rw [escapedSet]; exact Finset.mem_singleton_self 20)).mp
      (by decide)
    exact absurd seen (by decide)

/-- **A different label is never private**: `{20}` and `{9}` carry the labels `2` and `9`, and are
not equivalent even for a client that has seen nothing. -/
theorem labels_not_renamed : ¬ PrivatelyEquivalent A label ∅ (row 20) (row 9) := by
  intro h
  have bags := h.labels_eq
  simp only [row, Finset.singleton_val, Multiset.map_singleton, Multiset.singleton_inj] at bags
  change (Mettapedia.Logic.LP.Term.const 2 :
    Mettapedia.Logic.LP.Term ConstraintMultisetRewriting.Controls.signature) = .const 9 at bags
  injection bags with heads
  exact absurd heads (by decide)

end ViewControls

#print axioms labels_sdiff
#print axioms exists_partner
#print axioms exists_private_map
#print axioms privatelyEquivalent_iff
#print axioms privatelyEquivalent_empty_iff
#print axioms privatelyEquivalent_iff_sameUpTo
#print axioms fresh_alternative_equivalent_iff
#print axioms ViewControls.two_private_rows
#print axioms ViewControls.shared_escaped_row
#print axioms ViewControls.labels_not_renamed

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Observation
