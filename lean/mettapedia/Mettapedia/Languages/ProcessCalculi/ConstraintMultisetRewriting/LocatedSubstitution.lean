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

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LocatedSubstitution
