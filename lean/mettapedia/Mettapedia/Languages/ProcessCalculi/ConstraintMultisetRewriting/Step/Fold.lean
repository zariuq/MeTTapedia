import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.EscapeTransport

/-!
# Folding up to isomorphism, and canonical keys for it

A search folds a descendant onto an ancestor when the two are in one state class. This module states
what a fold licenses and what it does not.

* **Canonical forms** (`Canonicalizer`): a choice of representative, related to its argument and equal
  on related arguments. Two elements have equal canonical forms exactly when they are related
  (`Canonicalizer.canon_eq_iff`), so a canonical form is a complete key. One exists for every
  equivalence (`Canonicalizer.choose`), by choice; computing one is the business of the profile.
* **A fold is sound for reachability** (`fold_reach`, `Canonicalizer.fold_reach`): from a state in the
  class of another, every run of the other is matched by a similar run, ending in the same class. So
  states with equal keys need to be explored once.
* **A fold of a descendant onto its ancestor replays forever** (`fold_iterate`): the loop between them
  is transported along the class isomorphism and run again, for any number of rounds, each ending in
  the ancestor's class.
* **In the escape-relative transport a fold is silent** (`escape_fold_quiet`,
  `escape_fold_iterates_quiet`): a run that ends in the class of its start recorded nothing, and every
  isomorphism closing it renames by an automorphism of the start's record. So folding with the
  observer's record as part of the state closes only loops that disclose nothing, and every replay of
  such a loop discloses nothing. A loop that discloses cannot be folded this way; matching its internal
  states while the record grows is a different relation, not established here as a stream
  equivalence.
* **Disclosure shrinks the folding group** (`record_automorphisms_append`, `automorphisms_append_le`):
  the automorphisms of a record extended by later entries are those of the record that also fix the
  later entries. A renaming that identifies states for one record may stop doing so after the next
  disclosure.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Observation (Record)

universe uO uT uH uOcc uS uF uI uA

/-! ## Canonical forms -/

section Canonicalizer

variable {α : Type uA}

/-- **A canonical form for an equivalence**: a representative of each element's class, chosen
equally on related elements. -/
structure Canonicalizer (R : Setoid α) where
  canon : α → α
  related : ∀ a, R.r (canon a) a
  respects : ∀ {a b : α}, R.r a b → canon a = canon b

namespace Canonicalizer

variable {R : Setoid α} (c : Canonicalizer R)

/-- **Equal canonical forms are exactly related elements.** -/
theorem canon_eq_iff {a b : α} : c.canon a = c.canon b ↔ R.r a b :=
  ⟨fun same => R.iseqv.trans (R.iseqv.symm (c.related a)) (by rw [same]; exact c.related b), c.respects⟩

/-- **Every equivalence has a canonical form**, by choice of representatives. -/
noncomputable def choose (R : Setoid α) : Canonicalizer R where
  canon a := (Quotient.mk R a).out
  related a := Quotient.mk_out (s := R) a
  respects related := congrArg Quotient.out (Quotient.sound (s := R) related)

end Canonicalizer

end Canonicalizer

/-! ## Folding along a transport -/

section Fold

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  {P : Step X O State Firing} (T : Transport P)

/-- **A fold is sound for reachability**: every run from a state is matched, from any state of its
class, by a similar run. -/
theorem fold_reach {s t : State} (same : T.Same s t) (r : P.Run t) : ∃ r' : P.Run s, T.Similar r' r := by
  obtain ⟨i⟩ := same
  exact ⟨T.moveRun (T.symm i) r, Transport.Similar.symm (Transport.Similar.moveRun (T.symm i) r)⟩

/-- **Equal canonical keys license a fold.** -/
theorem Canonicalizer.fold_reach (c : Canonicalizer T.classSetoid) {s t : State}
    (keys : c.canon s = c.canon t) (r : P.Run t) :
    ∃ r' : P.Run s, T.Similar r' r ∧ T.Same r'.last r.last := by
  obtain ⟨r', similar⟩ := Interface.fold_reach T ((c.canon_eq_iff).mp keys) r
  exact ⟨r', similar, Transport.Similar.same_last similar⟩

/-- **A fold of a descendant onto its ancestor replays forever**: for every number of rounds there is
a run of that many transported copies of the loop, ending in the ancestor's class. -/
theorem fold_iterate {s : State} (u : P.Run s) (fold : T.Same s u.last) :
    ∀ n : ℕ, ∃ r : P.Run s, r.word.length = n * u.word.length ∧ T.Same s r.last
  | 0 => ⟨.nil s, by simp [Step.Run.word], T.same_refl s⟩
  | n + 1 => by
      obtain ⟨r, length, back⟩ := fold_iterate u fold n
      obtain ⟨j⟩ := back
      refine ⟨r.append (T.moveRun j u), ?_, ?_⟩
      · rw [Step.Run.word_append, List.length_append, length,
          ← Transport.Similar.length_eq (Transport.Similar.moveRun j u), Nat.add_one_mul]
      · rw [Step.Run.last_append]
        exact fold.trans (Transport.Similar.same_last (Transport.Similar.moveRun j u))

/-! ## Folds in the escape-relative transport -/

variable {T} {natural : T.Natural} {D : T.Escape}

/-- **A fold in the escape-relative transport is silent**: a run that ends in the class of its start
recorded nothing, and every isomorphism closing it renames by an automorphism of the start's
record. -/
theorem escape_fold_quiet {x : Escaped P} (r : D.step.Run x) (fold : (T.escaping natural D).Same x r.last) :
    r.last.record = x.record ∧
      ∀ i : (T.escaping natural D).Iso x r.last, (T.toStateIso i.base).rename ∈ Record.automorphisms x.record := by
  obtain ⟨later, grown⟩ := D.record_last r
  have silent : ∀ i : (T.escaping natural D).Iso x r.last, later = [] := by
    intro i
    have lengths := congrArg List.length (i.record.trans grown)
    rw [Record.length_rename, List.length_append] at lengths
    exact List.eq_nil_of_length_eq_zero (by omega)
  obtain ⟨i⟩ := fold
  have none := silent i
  subst none
  rw [List.append_nil] at grown
  refine ⟨grown, fun i' => ?_⟩
  exact Record.mem_automorphisms.mpr (i'.record.trans grown)

/-- **Every replay of a folded loop is silent.** -/
theorem escape_fold_iterates_quiet {x : Escaped P} (u : D.step.Run x)
    (fold : (T.escaping natural D).Same x u.last) :
    ∀ n : ℕ, ∃ r : D.step.Run x, r.word.length = n * u.word.length ∧ r.last.record = x.record := by
  intro n
  obtain ⟨r, length, back⟩ := fold_iterate (T.escaping natural D) u fold n
  exact ⟨r, length, (escape_fold_quiet r back).1⟩

end Fold

/-! ## Disclosure shrinks the folding group -/

/-- **The automorphisms of an extended record** are the automorphisms of the record that fix the
extension. -/
theorem record_automorphisms_append {O : Type uOcc} (r s : Record O) :
    Record.automorphisms (r ++ s) = Record.automorphisms r ⊓ Record.automorphisms s := by
  ext π
  rw [Subgroup.mem_inf]
  exact Record.rename_append_eq_iff

/-- **Disclosure never enlarges the folding group.** -/
theorem automorphisms_append_le {O : Type uOcc} (r s : Record O) :
    Record.automorphisms (r ++ s) ≤ Record.automorphisms r := by
  rw [record_automorphisms_append]
  exact inf_le_left

#print axioms Canonicalizer.canon_eq_iff
#print axioms Canonicalizer.choose
#print axioms fold_reach
#print axioms Canonicalizer.fold_reach
#print axioms fold_iterate
#print axioms escape_fold_quiet
#print axioms escape_fold_iterates_quiet
#print axioms record_automorphisms_append
#print axioms automorphisms_append_le

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
