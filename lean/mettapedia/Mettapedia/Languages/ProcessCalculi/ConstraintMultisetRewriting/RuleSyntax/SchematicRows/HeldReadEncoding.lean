import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.State

/-!
# Representing mixed rows by ordinary data and persistent held schemas

The two resource components partition the original occurrences. The source
knowledge and shared terms are unchanged; schematic code remains local and
only its captured arguments belong to the source interface. The label filler
is explicit and is used only outside the ordinary component's present set.
The code system supplies schema activation and ordinary rule unfolding; it
does not supply quoted-code installation or publication capabilities.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadEncoding

open RuleOccurrences

universe uO uT uOcc
variable {Obj : Type uO} {Tm : Obj → Type uT} {O : Type uOcc}

abbrev Code (Tm : Obj → Type uT) := Schema Tm ⊕ RuleSyntax.Rule Tm

def codes : Codes Tm (Code Tm) Unit where
  unfold code := match code with
    | .inl schema => schema.toSpec
    | .inr rule => Spec.ofRule rule
  denotes _ _ _ := False
  close _ _ _ := none

def sharedTag {a : Obj} : Row Tm a → Bool
  | .shared _ => true
  | .schematic _ => false

def closure {a : Obj} : Row Tm a → Closure Tm a
  | .shared term => Closure.captured term
  | .schematic row => row

def ordinaryLabel {a : Obj} (filler : Tm a) : Row Tm a → Tm a
  | .shared term => term
  | .schematic _ => filler

def encode (s : State Tm O) (filler : Tm s.frame) : RState Tm O O (Code Tm) Unit where
  frame := s.frame
  knowledge := s.knowledge
  present := s.present.filter fun o => sharedTag (s.label o) = true
  label o := ordinaryLabel filler (s.label o)
  rules := s.present.filter fun o => sharedTag (s.label o) = false
  held o := (closure (s.label o)).held (fun schema => (Sum.inl schema : Code Tm)) ()

theorem present_iff (s : State Tm O) (filler : Tm s.frame) (o : O) :
    o ∈ (encode s filler).present ↔ o ∈ s.present ∧ sharedTag (s.label o) = true :=
  Finset.mem_filter

theorem rules_iff (s : State Tm O) (filler : Tm s.frame) (o : O) :
    o ∈ (encode s filler).rules ↔ o ∈ s.present ∧ sharedTag (s.label o) = false :=
  Finset.mem_filter

theorem resource_partition [DecidableEq O] (s : State Tm O) (filler : Tm s.frame) :
    (encode s filler).present ∪ (encode s filler).rules = s.present ∧
      Disjoint (encode s filler).present (encode s filler).rules := by
  classical
  constructor
  · ext o
    rw [Finset.mem_union, present_iff, rules_iff]
    cases s.label o <;> simp [sharedTag]
  · apply Finset.disjoint_left.mpr
    intro o ordinary held
    have first := (present_iff s filler o).mp ordinary
    have second := (rules_iff s filler o).mp held
    have impossible : true = false := first.2.symm.trans second.2
    cases impossible

theorem label_shared (s : State Tm O) (filler : Tm s.frame) (o : O) (term : Tm s.frame)
    (row : s.label o = .shared term) : (encode s filler).label o = term := by
  simp only [encode, row, ordinaryLabel]

theorem held_schematic (s : State Tm O) (filler : Tm s.frame) (o : O)
    (datum : Closure Tm s.frame) (row : s.label o = .schematic datum) :
    (encode s filler).held o = datum.held (fun schema => (Sum.inl schema : Code Tm)) () := by
  simp only [encode, row, closure]

theorem schema_unfold (s : State Tm O) (filler : Tm s.frame) (o : O)
    (datum : Closure Tm s.frame) (row : s.label o = .schematic datum) :
    codes.unfold ((encode s filler).held o).code = datum.schema.toSpec := by
  rw [held_schematic s filler o datum row]
  rfl

theorem schema_arguments (s : State Tm O) (filler : Tm s.frame) (o : O)
    (datum : Closure Tm s.frame) (row : s.label o = .schematic datum) :
    ((encode s filler).held o).args = datum.args := by
  rw [held_schematic s filler o datum row]
  rfl

theorem schema_persistent (s : State Tm O) (filler : Tm s.frame) (o : O) :
    ((encode s filler).held o).mode = .persistent := rfl

theorem schematic_available (s : State Tm O) (filler : Tm s.frame) (o : O)
    (datum : Closure Tm s.frame) (row : s.label o = .schematic datum)
    (present : o ∈ s.present) : o ∈ (encode s filler).rules := by
  apply (rules_iff s filler o).mpr
  exact ⟨present, by rw [row]; rfl⟩

theorem scope_mentions_iff (s : State Tm O) (filler : Tm s.frame) (term : Tm s.frame) :
    (encode s filler).Mentions term ↔ s.scope.Mentions term := by
  rw [State.scope_mentions_iff]
  constructor
  · intro mentioned
    rcases mentioned with (left | right | ⟨o, present, labelled⟩) |
        ⟨o, present, argument⟩
    · exact Or.inl left
    · exact Or.inr (Or.inl right)
    · obtain ⟨inSource, ordinary⟩ := (present_iff s filler o).mp present
      cases row : s.label o with
      | shared value =>
        refine Or.inr (Or.inr ⟨o, inSource, ?_⟩)
        rw [row]
        exact List.mem_singleton.mpr
          ((label_shared s filler o value row).symm.trans labelled).symm
      | schematic datum => simp [row, sharedTag] at ordinary
    · obtain ⟨inSource, schematic⟩ := (rules_iff s filler o).mp present
      cases row : s.label o with
      | shared value => simp [row, sharedTag] at schematic
      | schematic datum =>
        refine Or.inr (Or.inr ⟨o, inSource, ?_⟩)
        rw [row]
        rw [held_schematic s filler o datum row] at argument
        exact argument
  · rintro (left | right | ⟨o, present, argument⟩)
    · exact Or.inl (Or.inl left)
    · exact Or.inl (Or.inr (Or.inl right))
    · cases row : s.label o with
      | shared value =>
        refine Or.inl (Or.inr (Or.inr ⟨o, ?_, ?_⟩))
        · exact (present_iff s filler o).mpr ⟨present, by rw [row]; rfl⟩
        · rw [label_shared s filler o value row]
          have same : term = value := by
            apply List.mem_singleton.mp
            simpa only [row, Row.ambientTerms] using argument
          exact same.symm
      | schematic datum =>
        refine Or.inr ⟨o, schematic_available s filler o datum row present, ?_⟩
        rw [held_schematic s filler o datum row]
        change term ∈ datum.args
        simpa only [row, Row.ambientTerms] using argument

#print axioms resource_partition
#print axioms schema_unfold
#print axioms schematic_available
#print axioms scope_mentions_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadEncoding
