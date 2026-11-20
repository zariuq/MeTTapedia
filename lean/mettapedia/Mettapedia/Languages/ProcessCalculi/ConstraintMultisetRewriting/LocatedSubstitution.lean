import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceStep

/-!
# Physical locations remain rigid under ordinary value unification

Pairing a location with an ordinary value gives a substitution action that
acts on values and fixes locations. This is a product action on the existing
step, not a new primitive or a classification inferred from a term's head.

Actual take/read equations then enforce their declared physical locations.
Equal or unifiable payloads in other spaces cannot supply those occurrences.
Publication rights and logical validity remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LocatedSubstitution

universe uT uS uN uO
variable {T : Type uT} {S : Type uS} {N : Type uN} {O : Type uO}

def action (base : SubstitutionAction T S) : SubstitutionAction (N × T) S where
  E left right := left.1 = right.1 ∧ base.E left.2 right.2
  equivalence :=
    ⟨fun _ => ⟨rfl, base.equivalence.refl _⟩,
      fun same => ⟨same.1.symm, base.equivalence.symm same.2⟩,
      fun first second => ⟨first.1.trans second.1, base.equivalence.trans first.2 second.2⟩⟩
  apply assignment value := (value.1, base.apply assignment value.2)
  identity := base.identity
  compose := base.compose
  apply_identity value := by simp only [base.apply_identity]
  apply_compose outer inner value := by simp only [base.apply_compose]
  preserves := fun assignment {_ _} same => ⟨same.1, base.preserves assignment same.2⟩

theorem location_is_fixed (base : SubstitutionAction T S) (assignment : S) (value : N × T) :
    ((action base).apply assignment value).1 = value.1 := rfl

theorem payload_uses_the_original_action (base : SubstitutionAction T S) (assignment : S) (value : N × T) :
    ((action base).apply assignment value).2 = base.apply assignment value.2 := rfl

theorem solving_requires_the_same_location (base : SubstitutionAction T S) (assignment : S)
    {left right : N × T} (solved : (action base).Solves assignment (left, right)) : left.1 = right.1 :=
  solved.1

theorem different_locations_cannot_be_unified (base : SubstitutionAction T S) (assignment : S)
    {left right : N × T} (apart : left.1 ≠ right.1) : ¬(action base).Solves assignment (left, right) :=
  fun solved => apart (solving_requires_the_same_location base assignment solved)

section Selections

variable [DecidableEq O]

omit [DecidableEq O] in
private theorem locations_of_forall₂ (location : O → N) (space : N)
    {patterns : List (N × T)} {selected : List O}
    (matched : List.Forall₂ (fun expected occurrence => expected.1 = location occurrence) patterns selected) :
    (∀ expected ∈ patterns, expected.1 = space) → ∀ occurrence ∈ selected, location occurrence = space := by
  induction matched with
  | nil => intro _ occurrence member; cases member
  | @cons expected occurrence patterns selected same rest earlier =>
      intro declared source member
      rcases List.mem_cons.mp member with rfl | member
      · exact same.symm.trans (declared expected (by simp))
      · exact earlier (fun other present => declared other (List.mem_cons_of_mem _ present)) source member

theorem take_locations (base : SubstitutionAction T S) (location : O → N) (payload : O → T)
    {rule : RuleInstance (N × T)} {before : Configuration (N × T) O} {picked : Selection O}
    (valid : picked.Valid (action base) (fun occurrence => (location occurrence, payload occurrence)) rule before) :
    List.Forall₂ (fun expected occurrence => expected.1 = location occurrence) rule.take picked.taken := by
  obtain ⟨assignment, models⟩ := valid.consistent
  have matched := (Selection.models_problem (action base) valid models).2.1
  exact matched.imp (fun _ _ same => same.1)

theorem read_locations (base : SubstitutionAction T S) (location : O → N) (payload : O → T)
    {rule : RuleInstance (N × T)} {before : Configuration (N × T) O} {picked : Selection O}
    (valid : picked.Valid (action base) (fun occurrence => (location occurrence, payload occurrence)) rule before) :
    List.Forall₂ (fun expected occurrence => expected.1 = location occurrence) rule.read picked.read := by
  obtain ⟨assignment, models⟩ := valid.consistent
  have matched := (Selection.models_problem (action base) valid models).2.2.1
  exact matched.imp (fun _ _ same => same.1)

theorem declared_read_space (base : SubstitutionAction T S) (location : O → N) (payload : O → T)
    {rule : RuleInstance (N × T)} {before : Configuration (N × T) O} {picked : Selection O}
    (valid : picked.Valid (action base) (fun occurrence => (location occurrence, payload occurrence)) rule before)
    (space : N) (declared : ∀ expected ∈ rule.read, expected.1 = space) :
    ∀ occurrence ∈ picked.read, location occurrence = space := by
  have matched := read_locations base location payload valid
  exact locations_of_forall₂ location space matched declared

theorem declared_output_space (base : SubstitutionAction T S) (location : O → N) (payload : O → T)
    {rule : RuleInstance (N × T)} {before : Configuration (N × T) O} {picked : Selection O}
    (valid : picked.Valid (action base) (fun occurrence => (location occurrence, payload occurrence)) rule before)
    (space : N) (declared : ∀ expected ∈ rule.produce, expected.1 = space) :
    ∀ occurrence ∈ picked.made, location occurrence = space := by
  intro occurrence member
  have produced : (location occurrence, payload occurrence) ∈ rule.produce := by
    rw [← valid.outputs]
    exact List.mem_map.mpr ⟨occurrence, member, rfl⟩
  exact declared _ produced

end Selections

/-! ## Rigid scope and return authority

Which row is at a site, and which occurrence owns a result, are resource
facts. Phases can change without changing the ticket. The ledger below
uses the ordinary occurrence commit, with an additional non-reuse
condition on logical identities. A physical allocator may recycle its
addresses by using generation-qualified occurrence identities.
-/

namespace Authority

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)

structure Ticket (Id : Type*) where
  key : Id
  owner : Id
  parent : Option Id
  deriving DecidableEq

inductive Mark (Id Phase : Type*) where
  | cell (place : Option Id)
  | control (ticket : Ticket Id) (phase : Phase)
  deriving DecidableEq

def Mark.ticket {Id Phase : Type*} : Mark Id Phase → Option (Ticket Id)
  | .cell _ => none
  | .control t _ => some t

structure Ledger (Id Phase : Type*) where
  mark : Id → Option (Mark Id Phase)
  issued : Finset Id

theorem Ledger.eq_of_parts {Id Phase : Type*} {left right : Ledger Id Phase}
    (marks : left.mark = right.mark) (history : left.issued = right.issued) : left = right := by
  cases left
  cases right
  cases marks
  cases history
  rfl

variable {Id Phase : Type*} [DecidableEq Id]

def Ledger.root (present : Finset Id) : Ledger Id Phase :=
  ⟨fun o => if o ∈ present then some (.cell none) else none, present⟩

def Ledger.Fresh (before : Ledger Id Phase) (selection : Selection Id) : Prop :=
  Disjoint selection.made.toFinset before.issued

/-- Install the tags on the actual produced identities in their selected
order, discard dead tags, and keep the issuance history even at a return. -/
def Ledger.advance (before : Ledger Id Phase) (present : Finset Id) (selection : Selection Id)
    (out : Vector (Mark Id Phase) selection.made.length) : Ledger Id Phase :=
  let after := fire present (selection.commit (T := Unit))
  let written := selection.made.zip out.toList
  ⟨fun o => if o ∈ after then (written.lookup o).orElse (fun _ => before.mark o) else none,
    before.issued ∪ selection.made.toFinset⟩

def Ledger.Covers (ledger : Ledger Id Phase) (present : Finset Id) : Prop :=
  present ⊆ ledger.issued ∧ ∀ o, o ∈ present ↔ (ledger.mark o).isSome

theorem Ledger.root_covers (present : Finset Id) :
    (Ledger.root (Phase := Phase) present).Covers present := by
  refine ⟨fun _ member => member, fun o => ?_⟩
  by_cases live : o ∈ present <;> simp [Ledger.root, live]

theorem Ledger.issued_mono (before : Ledger Id Phase) (present : Finset Id)
    (selection : Selection Id) (out : Vector (Mark Id Phase) selection.made.length) :
    before.issued ⊆ (before.advance present selection out).issued :=
  Finset.subset_union_left

theorem Ledger.fresh_not_issued {before : Ledger Id Phase} {selection : Selection Id}
    (fresh : before.Fresh selection) {o : Id} (made : o ∈ selection.made) : o ∉ before.issued :=
  fun prior => Finset.disjoint_left.mp fresh (List.mem_toFinset.mpr made) prior

omit [DecidableEq Id] in
private theorem written_keys (selection : Selection Id) (out : Vector (Mark Id Phase) selection.made.length) :
    (selection.made.zip out.toList).map Prod.fst = selection.made := by
  exact List.map_fst_zip (by simp)

omit [DecidableEq Id] in
/-- Reading an occurrence from an ordered, uniquely keyed publication. -/
theorem lookup_write [BEq Id] [LawfulBEq Id] {Value : Type*} {o : Id} {tag : Value} :
    ∀ (writes : List (Id × Value)), (writes.map Prod.fst).Nodup →
      (o, tag) ∈ writes → writes.lookup o = some tag
  | [], _, member => nomatch member
  | (key, value) :: writes, distinct, member => by
    rcases List.mem_cons.mp member with same | inside
    · cases same
      simp
    · have apart := List.nodup_cons.mp distinct
      have keyIn : o ∈ writes.map Prod.fst := List.mem_map_of_mem (f := Prod.fst) inside
      have other : o ≠ key := fun same => apart.1 (same ▸ keyIn)
      have unequal : (o == key) = false := by simpa using other
      simp only [List.lookup_cons, unequal, lookup_write writes apart.2 inside]

theorem Ledger.mark_installed (before : Ledger Id Phase) (present : Finset Id) {selection : Selection Id}
    (out : Vector (Mark Id Phase) selection.made.length) (distinct : selection.made.Nodup)
    {o : Id} {tag : Mark Id Phase} (written : (o, tag) ∈ selection.made.zip out.toList) :
    (before.advance present selection out).mark o = some tag := by
  have live : o ∈ fire present (selection.commit (T := Unit)) :=
    mem_fire.mpr (.inr (List.mem_toFinset.mpr (List.of_mem_zip written).1))
  have selected : (selection.made.zip out.toList).lookup o = some tag :=
    lookup_write _ (by rwa [written_keys]) written
  simp [Ledger.advance, live, selected]

/-- Independent of payload values, a live occurrence outside the made
set carries its old mark. -/
theorem Ledger.mark_retained (before : Ledger Id Phase) {present : Finset Id}
    {selection : Selection Id} (out : Vector (Mark Id Phase) selection.made.length) {o : Id}
    (live : o ∈ fire present (selection.commit (T := Unit))) (old : o ∉ selection.made) :
    (before.advance present selection out).mark o = before.mark o := by
  have unwritten : (selection.made.zip out.toList).lookup o = none := by
    apply List.lookup_eq_none_iff.mpr
    intro pair member
    have key := List.mem_map_of_mem (f := Prod.fst) member
    rw [written_keys] at key
    simpa using (fun equal : o = pair.1 => old (equal.symm ▸ key))
  simp [Ledger.advance, live, unwritten]

theorem Ledger.covers_advance {before : Ledger Id Phase} {present : Finset Id} {selection : Selection Id}
    (out : Vector (Mark Id Phase) selection.made.length) (covered : before.Covers present) :
    (before.advance present selection out).Covers (fire present (selection.commit (T := Unit))) := by
  refine ⟨?_, fun o => ?_⟩
  · intro o live
    rcases mem_fire.mp live with ⟨survived, _⟩ | made
    · exact Finset.mem_union_left _ (covered.1 survived)
    · exact Finset.mem_union_right _ (by simpa only [Selection.commit] using made)
  · by_cases live : o ∈ fire present (selection.commit (T := Unit))
    · by_cases made : o ∈ selection.made
      · have inKeys : o ∈ (selection.made.zip out.toList).map Prod.fst := by
          rwa [written_keys]
        obtain ⟨pair, existsPair, equal⟩ := List.mem_map.mp inKeys
        have found : ((selection.made.zip out.toList).lookup o).isSome :=
          List.lookup_isSome_iff.mpr ⟨pair, existsPair, by simp [equal]⟩
        cases checked : (selection.made.zip out.toList).lookup o with
        | none => simp [checked] at found
        | some mark => simp [Ledger.advance, live, checked]
      · have survived : o ∈ present := by
          rcases mem_fire.mp live with ⟨old, _⟩ | n
          · exact old
          · exact (made (by simpa only [Selection.commit, List.mem_toFinset] using n)).elim
        rw [Ledger.mark_retained before out live made]
        exact iff_of_true live ((covered.2 o).mp survived)
    · simp [Ledger.advance, live]

/-- Every live mark after a commit comes either from a fresh made
occurrence or from a retained one. In particular, advancing cannot
silently change the tag of a surviving old occurrence. -/
theorem Ledger.mark_advance_iff {before : Ledger Id Phase} {present : Finset Id} {selection : Selection Id}
    (out : Vector (Mark Id Phase) selection.made.length) (covered : before.Covers present)
    (fresh : before.Fresh selection) (distinct : selection.made.Nodup) {o : Id} {mark : Mark Id Phase} :
    (before.advance present selection out).mark o = some mark ↔
      (o, mark) ∈ selection.made.zip out.toList ∨
        (o ∈ present ∧ o ∉ selection.taken ∧ before.mark o = some mark) := by
  constructor
  · intro marked
    have live := ((Ledger.covers_advance out covered).2 o).mpr (by rw [marked]; rfl)
    rcases mem_fire.mp live with ⟨old, notTaken⟩ | new
    · have notMade : o ∉ selection.made := fun made => (Ledger.fresh_not_issued fresh made) (covered.1 old)
      exact .inr ⟨old, fun selected => notTaken (List.mem_toFinset.mpr selected),
        (Ledger.mark_retained before out live notMade).symm.trans marked⟩
    · have wrote : o ∈ (selection.made.zip out.toList).map Prod.fst := by
        rw [written_keys]
        exact List.mem_toFinset.mp new
      obtain ⟨⟨key, tag⟩, member, sameKey⟩ := List.mem_map.mp wrote
      change key = o at sameKey
      subst key
      have sameTag := Option.some.inj ((Ledger.mark_installed before present out distinct member).symm.trans marked)
      exact .inl (sameTag ▸ member)
  · rintro (made | ⟨old, notTaken, same⟩)
    · exact Ledger.mark_installed before present out distinct made
    · have live : o ∈ fire present (selection.commit (T := Unit)) :=
        mem_fire.mpr (.inl ⟨old, fun taken => notTaken (List.mem_toFinset.mp taken)⟩)
      have notMade : o ∉ selection.made := fun made => (Ledger.fresh_not_issued fresh made) (covered.1 old)
      exact (Ledger.mark_retained before out live notMade).trans same

end Authority

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LocatedSubstitution
