import Mettapedia.Languages.CHR.MachineSearchComplete

/-! Soundness of the machine's partner search. Matching adds each binding
once, for a variable of the matched terms; so a complete selection reached
from the empty environment binds only head variables, each once. Every
reached selection picks, for each head, the active constraint at its own
position or a store occurrence of the head's key elsewhere, all distinct, and
instantiates every head to its pick. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.Machine

theorem lookup_none_iff (environment : Environment) (index : Nat) :
    lookup environment index = none ↔ index ∉ environment.map Prod.fst := by
  simp only [lookup, Option.map_eq_none_iff, List.find?_eq_none, beq_iff_eq, List.mem_map, not_exists,
    not_and, Prod.forall]

/-- Matching keeps keys distinct and adds keys only for variables of the term. -/
structure Bindings (environment bound : Environment) (allowed : List Nat) : Prop where
  distinct : (environment.map Prod.fst).Nodup → (bound.map Prod.fst).Nodup
  only : ∀ binding ∈ bound, binding ∈ environment ∨ binding.1 ∈ allowed

theorem Bindings.refl (environment : Environment) (allowed : List Nat) :
    Bindings environment environment allowed := ⟨id, fun _ member => .inl member⟩

theorem Bindings.trans {first second third : Environment} {one two : List Nat}
    (outer : Bindings second third two) (inner : Bindings first second one) :
    Bindings first third (one ++ two) where
  distinct nodup := outer.distinct (inner.distinct nodup)
  only binding member := by
    rcases outer.only binding member with earlier | introduced
    · rcases inner.only binding earlier with original | early
      · exact .inl original
      · exact .inr (List.mem_append_left _ early)
    · exact .inr (List.mem_append_right _ introduced)

theorem Bindings.widen {environment bound : Environment} {small large : List Nat}
    (bindings : Bindings environment bound small) (subset : ∀ index ∈ small, index ∈ large) :
    Bindings environment bound large where
  distinct := bindings.distinct
  only binding member := (bindings.only binding member).imp id (subset binding.1)

mutual
  theorem matchTerm_bindings :
      (term : Term) → (value : Value) → (environment bound : Environment) →
        matchTerm term value environment = some bound → Bindings environment bound term.variables
    | .value datum, value, environment, bound, matched => by
      by_cases same : datum = value
      · simp only [matchTerm, same, if_true, Option.some.injEq] at matched
        subst matched
        exact Bindings.refl _ _
      · simp [matchTerm, same] at matched
    | .var index, value, environment, bound, matched => by
      cases present : lookup environment index with
      | none =>
        simp only [matchTerm, present, Option.some.injEq] at matched
        subst matched
        refine ⟨fun nodup => ?_, fun binding member => ?_⟩
        · rw [List.map_cons, List.nodup_cons]
          exact ⟨(lookup_none_iff environment index).mp present, nodup⟩
        · rcases List.mem_cons.mp member with rfl | old
          · exact .inr (by simp [Term.variables])
          · exact .inl old
      | some old =>
        by_cases same : old = value
        · simp only [matchTerm, present, same, if_true, Option.some.injEq] at matched
          subst matched
          exact Bindings.refl _ _
        · simp [matchTerm, present, same] at matched
    | .tuple terms, .tuple fields, environment, bound, matched => by
      simp only [matchTerm] at matched
      have inner := matchTerms_bindings terms fields environment bound matched
      exact inner.widen (fun index member => by simpa [Term.variables] using member)
    | .tuple _, .integer _, _, _, matched => by simp [matchTerm] at matched
    | .tuple _, .atom _, _, _, matched => by simp [matchTerm] at matched
  theorem matchTerms_bindings :
      (terms : List Term) → (values : List Value) → (environment bound : Environment) →
        matchTerms terms values environment = some bound →
        Bindings environment bound (terms.flatMap Term.variables)
    | [], [], environment, bound, matched => by
      simp only [matchTerms, Option.some.injEq] at matched
      subst matched
      exact Bindings.refl _ _
    | [], _ :: _, _, _, matched => by simp [matchTerms] at matched
    | _ :: _, [], _, _, matched => by simp [matchTerms] at matched
    | term :: terms, value :: values, environment, bound, matched => by
      simp only [matchTerms] at matched
      cases first : matchTerm term value environment with
      | none => rw [first] at matched; cases matched
      | some middle =>
        rw [first] at matched
        have one := matchTerm_bindings term value environment middle first
        have two := matchTerms_bindings terms values middle bound matched
        exact (two.trans one).widen (fun index member => by simpa [List.flatMap_cons] using member)
end

section Soundness

variable (store : Store) (position active : Nat) (values : List Value)

/-- What a reached selection guarantees about its picks and environment. -/
structure Reached (index : Nat) (heads : List Head) (environment : Environment) (picks : List Pick)
    (used : List Nat) (bound : Environment) (chosen : List Pick) : Prop where
  occurrences : ∃ occurrences : List Occ,
    chosen = picks ++ List.zipWith (fun head occurrence => ⟨Head.key head, occurrence.id⟩) heads occurrences ∧
    List.Forall₂ (fun head occurrence => instantiateTerms bound head.arguments = some occurrence.values)
      heads occurrences ∧
    AllFit store position active values index heads
      (List.zipWith (fun head occurrence => ⟨occurrence.id, ⟨head.name, occurrence.values⟩⟩) heads occurrences) ∧
    (occurrences.map Occ.id).Nodup ∧ (∀ occurrence ∈ occurrences, occurrence.id ∉ used)
  grown : Extends bound environment
  bindings : Bindings environment bound (heads.flatMap Head.variables)

theorem selections_sound :
    ∀ (index : Nat) (heads : List Head) (environment : Environment) (picks : List Pick)
      (used : List Nat) (bound : Environment) (chosen : List Pick),
      (bound, chosen) ∈ selections store position active values index heads environment picks used →
      Reached store position active values index heads environment picks used bound chosen
  | index, [], environment, picks, used, bound, chosen, reached => by
    simp only [selections, List.mem_singleton, Prod.mk.injEq] at reached
    obtain ⟨rfl, rfl⟩ := reached
    exact ⟨⟨[], by simp, .nil, trivial, List.nodup_nil, by simp⟩, Extends.refl _, Bindings.refl _ _⟩
  | index, head :: later, environment, picks, used, bound, chosen, reached => by
    rw [selections_cons, List.mem_flatMap] at reached
    obtain ⟨candidate, member, inside⟩ := reached
    unfold contribution at inside
    by_cases rejected : candidate.id ∈ used ∨ (index ≠ position ∧ candidate.id = active)
    · simp [rejected] at inside
    · simp only [rejected, if_false] at inside
      cases matched : matchTerms head.arguments candidate.values environment with
      | none => simp [matched] at inside
      | some middle =>
        simp only [matched] at inside
        have rest := selections_sound (index + 1) later middle (picks ++ [⟨Head.key head, candidate.id⟩])
          (candidate.id :: used) bound chosen inside
        obtain ⟨occurrences, chosenEq, instantiated, fitting, distinct, unused⟩ := rest.occurrences
        obtain ⟨grownFirst, instantiatedFirst⟩ := matchTerms_sound head.arguments candidate.values environment middle matched
        have bindingsFirst := matchTerms_bindings head.arguments candidate.values environment middle matched
        refine ⟨⟨candidate :: occurrences, by simp [chosenEq, List.append_assoc], ?_, ?_, ?_, ?_⟩,
          Extends.trans rest.grown grownFirst, ?_⟩
        · exact List.Forall₂.cons (instantiateTerms_extends rest.grown _ _ instantiatedFirst) instantiated
        · refine ⟨?_, fitting⟩
          unfold Fits
          by_cases here : index = position
          · simp only [here, if_true]
            unfold candidates at member
            simp only [here, if_true, List.mem_singleton] at member
            subst member
            exact ⟨rfl, rfl⟩
          · simp only [here, if_false]
            unfold candidates at member
            simp only [here, if_false] at member
            refine ⟨by simpa [Head.key] using member, fun same => rejected (.inr ⟨here, same⟩)⟩
        · rw [List.map_cons, List.nodup_cons]
          exact ⟨fun inside => unused _ (List.mem_map.mp inside).choose_spec.1
              (by rw [(List.mem_map.mp inside).choose_spec.2]; simp), distinct⟩
        · intro occurrence inside
          rcases List.mem_cons.mp inside with rfl | later'
          · exact fun old => rejected (.inl old)
          · exact fun old => unused occurrence later' (List.mem_cons_of_mem _ old)
        · exact (rest.bindings.trans bindingsFirst).widen (fun index member => by
            simpa [List.flatMap_cons, Head.variables] using member)

end Soundness

#print axioms matchTerms_bindings
#print axioms selections_sound

end Mettapedia.Languages.CHR.Machine
