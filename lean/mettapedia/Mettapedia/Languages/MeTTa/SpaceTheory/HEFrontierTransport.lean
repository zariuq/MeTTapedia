import Mettapedia.Languages.MeTTa.SpaceTheory.HEInvocationEntry

/-!
# Transporting HE's ordered frontier evidence

A definition occurrence carries an ordinal in the evidence for complete
query coverage. Its work is the matched body and bindings. An ordered
alignment keeps occurrences individually, including equal copies;
insertions and removals must have an independent no-match proof. The
alignment changes ordinals without redoing matching or freshening.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.HEFrontierTransport

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationFrontierRel EquationRowResultsRel EquationWork)

variable {live : List Atom} {query : Atom} {incoming : Bindings}

abbrev Rejected (live : List Atom) (query : Atom) (incoming : Bindings) (atom : Atom) : Prop :=
  ∀ position, EquationRowResultsRel live query incoming position atom []

inductive Alignment (live : List Atom) (query : Atom) (incoming : Bindings) :
    List Atom → List Atom → Type where
  | empty : Alignment live query incoming [] []
  | keep (atom : Atom) {left right : List Atom} :
      Alignment live query incoming left right → Alignment live query incoming (atom :: left) (atom :: right)
  | remove {atom : Atom} {left right : List Atom} :
      Rejected live query incoming atom → Alignment live query incoming left right →
      Alignment live query incoming (atom :: left) right
  | insert {atom : Atom} {left right : List Atom} :
      Rejected live query incoming atom → Alignment live query incoming left right →
      Alignment live query incoming left (atom :: right)

def Alignment.stay : (atoms : List Atom) → Alignment live query incoming atoms atoms
  | [] => .empty
  | head :: tail => .keep head (stay tail)

def Alignment.reverse {left right : List Atom} :
    Alignment live query incoming left right → Alignment live query incoming right left
  | .empty => .empty
  | .keep atom rest => .keep atom rest.reverse
  | .remove miss rest => .insert miss rest.reverse
  | .insert miss rest => .remove miss rest.reverse

def Alignment.pairing {left right : List Atom} (alignment : Alignment live query incoming left right)
    (old fresh : Nat) : List (Nat × Nat) :=
  match alignment with
  | .empty => []
  | .keep _ tail => (old, fresh) :: tail.pairing (old + 1) (fresh + 1)
  | .remove _ tail => tail.pairing (old + 1) fresh
  | .insert _ tail => tail.pairing old (fresh + 1)

theorem Alignment.reverse_pairs {left right : List Atom} (alignment : Alignment live query incoming left right)
    (old fresh : Nat) :
    alignment.reverse.pairing fresh old = (alignment.pairing old fresh).map Prod.swap := by
  induction alignment generalizing old fresh with
  | empty => rfl
  | keep atom rest ih => simp only [Alignment.reverse, Alignment.pairing, List.map_cons, Prod.swap, ih]
  | remove miss rest ih => exact ih (old + 1) fresh
  | insert miss rest ih => exact ih old (fresh + 1)

private theorem old_bound {left right : List Atom} (alignment : Alignment live query incoming left right)
    (old fresh a b : Nat) (listed : (a, b) ∈ alignment.pairing old fresh) : old ≤ a := by
  induction alignment generalizing old fresh with
  | empty => cases listed
  | keep atom alignment ih =>
    rcases List.mem_cons.mp listed with first | later
    · exact Nat.le_of_eq (congrArg Prod.fst first).symm
    · exact (Nat.le_succ old).trans (ih _ _ later)
  | remove miss alignment ih => exact (Nat.le_succ old).trans (ih _ _ listed)
  | insert miss alignment ih => exact ih _ _ listed

theorem Alignment.pairs_functional {left right : List Atom} (alignment : Alignment live query incoming left right)
    (old fresh a b c : Nat) (first : (a, b) ∈ alignment.pairing old fresh)
    (second : (a, c) ∈ alignment.pairing old fresh) : b = c := by
  induction alignment generalizing old fresh with
  | empty => cases first
  | keep atom remaining ih =>
    rcases List.mem_cons.mp first with atHead | inRest
    · rcases List.mem_cons.mp second with another | shifted
      · exact congrArg Prod.snd (atHead.trans another.symm)
      · have bound := old_bound remaining _ _ _ _ shifted
        have index := congrArg Prod.fst atHead
        change a = old at index
        omega
    · rcases List.mem_cons.mp second with atHead | inBoth
      · have bound := old_bound remaining _ _ _ _ inRest
        have index := congrArg Prod.fst atHead
        change a = old at index
        omega
      · exact ih _ _ inRest inBoth
  | remove miss remaining ih => exact ih _ _ first second
  | insert miss remaining ih => exact ih _ _ first second

def atOrdinal (work : EquationWork) (position : Nat) : EquationWork := {work with position}

def PairedWork (pairs : List (Nat × Nat)) (old fresh : EquationWork) : Prop :=
  atOrdinal old fresh.position = fresh ∧ (old.position, fresh.position) ∈ pairs

private theorem flip_work {pairs : List (Nat × Nat)} {old fresh : EquationWork}
    (paired : PairedWork pairs old fresh) : PairedWork (pairs.map Prod.swap) fresh old := by
  refine ⟨?_, List.mem_map.mpr ⟨_, paired.2, rfl⟩⟩
  rw [← paired.1]
  cases old
  rfl

theorem rejected_results_empty {atom : Atom} {position : Nat} {result : List EquationWork}
    (miss : Rejected live query incoming atom)
    (complete : EquationRowResultsRel live query incoming position atom result) : result = [] := by
  cases complete with
  | irrelevant | miss => rfl
  | hit left right pattern body matched output fresh accepts agree =>
    have absent := miss position
    cases absent with
    | irrelevant _ notDefinition => exact (notDefinition left right rfl).elim
    | miss _ _ _ _ _ rejects => exact (rejects pattern body fresh matched output ⟨accepts, agree⟩).elim

private theorem shift_entry {atom : Atom} {position : Nat} {result : List EquationWork}
    (compiled : EquationRowResultsRel live query incoming position atom result)
    (next : Nat) (pairs : List (Nat × Nat)) (held : (position, next) ∈ pairs) :
    EquationRowResultsRel live query incoming next atom (result.map fun work => atOrdinal work next) ∧
      List.Forall₂ (PairedWork pairs) result (result.map fun work => atOrdinal work next) := by
  cases compiled with
  | irrelevant _ absent => exact ⟨.irrelevant _ _ absent, .nil⟩
  | miss _ _ _ _ fresh rejects => exact ⟨.miss _ _ _ _ _ fresh rejects, .nil⟩
  | hit _ _ _ _ _ _ fresh accepts agree =>
    exact ⟨.hit _ _ _ _ _ _ _ fresh accepts agree, .cons ⟨rfl, held⟩ .nil⟩

private theorem transport_blocks {left right : List Atom} (alignment : Alignment live query incoming left right)
    (old fresh : Nat) (blocks : List (List EquationWork))
    (held : List.Forall₂ (fun a block => EquationRowResultsRel live query incoming a.2 a.1 block)
      (left.zipIdx old) blocks) :
    ∃ next : List (List EquationWork),
      List.Forall₂ (fun a block => EquationRowResultsRel live query incoming a.2 a.1 block)
        (right.zipIdx fresh) next ∧
        List.Forall₂ (PairedWork (alignment.pairing old fresh)) blocks.flatten next.flatten := by
  induction alignment generalizing old fresh blocks with
  | empty => cases held; exact ⟨[], .nil, .nil⟩
  | keep atom remaining ih =>
    rw [List.zipIdx_cons] at held
    cases held with
    | @cons _ compiled _ tail atHead rest =>
      obtain ⟨moved, next, paired⟩ := ih (old + 1) (fresh + 1) tail rest
      have here := shift_entry atHead fresh ((Alignment.keep atom remaining).pairing old fresh) List.mem_cons_self
      have later : List.Forall₂ (PairedWork ((Alignment.keep atom remaining).pairing old fresh)) tail.flatten
          moved.flatten := paired.imp (fun _ _ agrees => ⟨agrees.1, List.mem_cons_of_mem _ agrees.2⟩)
      exact ⟨_ :: moved, .cons here.1 next, List.rel_append here.2 later⟩
  | remove miss remaining ih =>
    rw [List.zipIdx_cons] at held
    cases held with
    | @cons _ compiled _ tail atHead rest =>
      obtain rfl := rejected_results_empty miss atHead
      exact ih (old + 1) fresh tail rest
  | insert miss remaining ih =>
    obtain ⟨moved, next, paired⟩ := ih old (fresh + 1) blocks held
    exact ⟨[] :: moved, .cons (miss fresh) next, paired⟩

theorem transport {before after : Space} (alignment : Alignment live query incoming before.atoms after.atoms)
    {work : List EquationWork} (checked : EquationFrontierRel before live query incoming work) :
    ∃ next, EquationFrontierRel after live query incoming next ∧
      List.Forall₂ (PairedWork (alignment.pairing 0 0)) work next := by
  cases checked with
  | @completed blocks all =>
    obtain ⟨next, checked, paired⟩ := transport_blocks alignment 0 0 blocks all
    exact ⟨next.flatten, .completed checked, paired⟩

private theorem unique_transport {left right : List Atom} (alignment : Alignment live query incoming left right)
    (old fresh : Nat) {input first second : List EquationWork}
    (one : List.Forall₂ (PairedWork (alignment.pairing old fresh)) input first)
    (two : List.Forall₂ (PairedWork (alignment.pairing old fresh)) input second) : first = second := by
  induction one generalizing second with
  | nil => cases two; rfl
  | @cons x y xs ys here tail ih =>
    cases two with
    | @cons _ z _ zs there rest =>
      have positions := alignment.pairs_functional old fresh _ _ _ here.2 there.2
      have same : y = z := here.1.symm.trans (positions.symm ▸ there.1)
      exact congrArg₂ List.cons same (ih rest)

/-- The live complete frontier is exactly the transport of a complete
snapshot frontier. The comparison requires no hypothesis that the
old and new ordinals are equal. -/
theorem frontier_iff {before after : Space} (alignment : Alignment live query incoming before.atoms after.atoms)
    (work : List EquationWork) :
    EquationFrontierRel after live query incoming work ↔
      ∃ previous, EquationFrontierRel before live query incoming previous ∧
        List.Forall₂ (PairedWork (alignment.pairing 0 0)) previous work := by
  constructor
  · intro now
    obtain ⟨old, earlier, backward⟩ := transport alignment.reverse now
    rw [alignment.reverse_pairs] at backward
    have restored : ((alignment.pairing 0 0).map Prod.swap).map Prod.swap = alignment.pairing 0 0 := by
      simp only [List.map_map, show Prod.swap ∘ Prod.swap = id from funext fun (p : Nat × Nat) => rfl, List.map_id]
    refine ⟨old, earlier, ?_⟩
    rw [← restored]
    clear now earlier
    induction backward with
    | nil => exact .nil
    | cons matched _ ih => exact .cons (flip_work matched) ih
  · rintro ⟨old, earlier, reused⟩
    obtain ⟨next, verified, paired⟩ := transport alignment earlier
    exact unique_transport alignment 0 0 paired reused ▸ verified

def nextOrdinal (old : Nat) : List (Nat × Nat) → Option Nat
  | [] => none
  | (a, b) :: rest => if old = a then some b else nextOrdinal old rest

private theorem next_is_listed {pairs : List (Nat × Nat)} {old fresh : Nat}
    (found : nextOrdinal old pairs = some fresh) : (old, fresh) ∈ pairs := by
  induction pairs with
  | nil => cases found
  | cons pair rest ih =>
    obtain ⟨a, b⟩ := pair
    by_cases first : old = a
    · subst a
      have value : b = fresh := by simpa [nextOrdinal] using found
      subst fresh
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (ih (by simpa only [nextOrdinal, if_neg first] using found))

private theorem listed_is_next {pairs : List (Nat × Nat)} {old fresh : Nat}
    (unique : ∀ b c, (old, b) ∈ pairs → (old, c) ∈ pairs → b = c)
    (listed : (old, fresh) ∈ pairs) : nextOrdinal old pairs = some fresh := by
  induction pairs with
  | nil => cases listed
  | cons pair rest ih =>
    obtain ⟨a, b⟩ := pair
    by_cases first : old = a
    · subst a
      have value := unique b fresh List.mem_cons_self listed
      simp [nextOrdinal, value]
    · have tail := (List.mem_cons.mp listed).resolve_left (fun same => first (congrArg Prod.fst same))
      have found := ih (fun x y one two => unique x y (List.mem_cons_of_mem _ one) (List.mem_cons_of_mem _ two)) tail
      simpa only [nextOrdinal, if_neg first] using found

def relabel (pairs : List (Nat × Nat)) : List EquationWork → Option (List EquationWork)
  | [] => some []
  | first :: rest => do
    let ordinal ← nextOrdinal first.position pairs
    let pending ← relabel pairs rest
    pure (atOrdinal first ordinal :: pending)

private theorem relabel_iff {pairs : List (Nat × Nat)}
    (unique : ∀ a b c, (a, b) ∈ pairs → (a, c) ∈ pairs → b = c) (old next : List EquationWork) :
    relabel pairs old = some next ↔ List.Forall₂ (PairedWork pairs) old next := by
  induction old generalizing next with
  | nil =>
    constructor
    · intro noWork; have empty : [] = next := Option.some.inj noWork; subst next; exact .nil
    · intro paired; cases paired; rfl
  | cons item tail ih =>
    constructor
    · simp only [relabel, bind, Option.bind_eq_some_iff, pure, Option.some.injEq]
      rintro ⟨ordinal, found, rest, moved, rfl⟩
      exact .cons ⟨rfl, next_is_listed found⟩ ((ih rest).mp moved)
    · intro paired
      cases paired with
      | @cons _ output _ rest first later =>
        have found := listed_is_next (unique item.position) first.2
        simp only [relabel, bind, Option.bind_eq_some_iff, pure, Option.some.injEq]
        exact ⟨output.position, found, rest, (ih rest).mpr later, congrArg (· :: rest) first.1⟩

/-- Actual relabelling is a deterministic read on the old frontier.
Only the matched work's evidence is inspected, not its rule body or
fresh bindings. -/
theorem frontier_iff_relabel {before after : Space} (alignment : Alignment live query incoming before.atoms after.atoms)
    (work : List EquationWork) :
    EquationFrontierRel after live query incoming work ↔
      ∃ previous, EquationFrontierRel before live query incoming previous ∧
        relabel (alignment.pairing 0 0) previous = some work := by
  rw [frontier_iff alignment work]
  constructor
  · rintro ⟨old, certified, moved⟩
    exact ⟨old, certified, (relabel_iff (alignment.pairs_functional 0 0) old work).mpr moved⟩
  · rintro ⟨old, certified, moved⟩
    exact ⟨old, certified, (relabel_iff (alignment.pairs_functional 0 0) old work).mp moved⟩

section Examples

open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.FrontierControls (context work complete)

private def note : Atom := .symbol "note"
private def newSnapshot : Space := Space.ofList (note :: context.atoms)

private def inserted : Alignment [] (.symbol "a") Bindings.empty context.atoms newSnapshot.atoms :=
  .insert (fun n => .irrelevant n note (by intro a b impossible; cases impossible)) (.stay context.atoms)

theorem prepended_relabels_two_distinct_duplicates :
    relabel (inserted.pairing 0 0) [work 0, work 3] = some [work 1, work 4] := rfl

/-- The two identical definitions survive as distinct work occurrences
after a harmless atom is inserted before either of them. -/
theorem shifted_duplicates_keep_both_work_items :
    EquationFrontierRel newSnapshot [] (.symbol "a") Bindings.empty [work 1, work 4] := by
  apply (frontier_iff inserted _).mpr
  exact ⟨[work 0, work 3], complete, .cons ⟨rfl, List.mem_cons_self⟩
    (.cons ⟨rfl, by decide +kernel⟩ .nil)⟩

theorem matching_definition_cannot_be_removed_as_irrelevant :
    ¬Nonempty (Alignment [] (.symbol "a") Bindings.empty context.atoms Space.empty.atoms) := by
  rintro ⟨aligned⟩
  obtain ⟨new, done, paired⟩ := transport aligned complete
  have noWork : new = [] := by
    cases done with
    | completed checked => cases checked; rfl
  rw [noWork] at paired
  cases paired

end Examples

end Mettapedia.Languages.MeTTa.SpaceTheory.HEFrontierTransport
