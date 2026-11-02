import Mettapedia.Logic.CTLFixedPoints

/-!
# Nested existential CTL with independent path semantics

Formula meanings use finite until paths and infinite globally paths, not a
symbolic fixed-point implementation. Negation is relative to the declared
state domain. Existential next also requires its starting state in that
domain. A deadlock has no implicit successor; stuttering must be supplied
as an explicit different relation.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.CTLFormula

inductive Formula (Label : Type)
  | atom (label : Label)
  | truth
  | neg (body : Formula Label)
  | conj (left right : Formula Label)
  | disj (left right : Formula Label)
  | ex (body : Formula Label)
  | eu (holds goal : Formula Label)
  | eg (body : Formula Label)
  deriving DecidableEq, Repr

variable {Label State : Type}

def meaning (domain : Set State) (relation : State → State → Prop) (atoms : Label → Set State) :
    Formula Label → Set State
  | .atom label => domain ∩ atoms label
  | .truth => domain
  | .neg body => domain \ meaning domain relation atoms body
  | .conj left right => meaning domain relation atoms left ∩ meaning domain relation atoms right
  | .disj left right => meaning domain relation atoms left ∪ meaning domain relation atoms right
  | .ex body => domain ∩ CTLFixedPoints.pre relation (meaning domain relation atoms body)
  | .eu holds goal => {state | CTLFixedPoints.Until relation
      (meaning domain relation atoms holds) (meaning domain relation atoms goal) state}
  | .eg body => {state | CTLFixedPoints.Globally relation (meaning domain relation atoms body) state}

theorem meaning_within (domain : Set State) (relation : State → State → Prop)
    (atoms : Label → Set State) (formula : Formula Label) : meaning domain relation atoms formula ⊆ domain := by
  induction formula with
  | atom => exact Set.inter_subset_left
  | truth => exact Set.Subset.refl _
  | neg => exact Set.sdiff_subset
  | conj _ _ left _ => exact Set.inter_subset_left.trans left
  | disj _ _ left right => exact Set.union_subset left right
  | ex => exact Set.inter_subset_left
  | eu holds goal held reached =>
      intro state path
      cases path with
      | reached present => exact reached present
      | advance present _ _ => exact held present
  | eg body within =>
      rintro state ⟨path, start, valid⟩
      rw [← start]
      exact within (valid 0).1

def Formula.labels : Formula Label → List Label
  | .atom label => [label]
  | .truth => []
  | .neg body | .ex body | .eg body => body.labels
  | .conj left right | .disj left right | .eu left right => left.labels ++ right.labels

/-- Atom-label dependencies are local, but the transition relation is held
fixed. Changing edges is not an unrelated-label mutation. -/
theorem meaning_agrees (domain : Set State) (relation : State → State → Prop)
    (first second : Label → Set State) (formula : Formula Label)
    (agree : ∀ label ∈ formula.labels, first label = second label) :
    meaning domain relation first formula = meaning domain relation second formula := by
  induction formula with
  | atom label => simp only [meaning, agree label (by simp [Formula.labels])]
  | truth => rfl
  | neg body ih => simp only [meaning, ih agree]
  | ex body ih => simp only [meaning, ih agree]
  | eg body ih => simp only [meaning, ih agree]
  | conj left right ihl ihr | disj left right ihl ihr | eu left right ihl ihr =>
      simp only [meaning,
        ihl (fun label present => agree label (List.mem_append_left _ present)),
        ihr (fun label present => agree label (List.mem_append_right _ present))]

theorem boolean_reassociation (domain : Set State) (relation : State → State → Prop)
    (atoms : Label → Set State) (a b c : Formula Label) :
    meaning domain relation atoms (.conj (.conj a b) c) =
      meaning domain relation atoms (.conj a (.conj b c)) := Set.inter_assoc _ _ _

theorem double_negation (domain : Set State) (relation : State → State → Prop)
    (atoms : Label → Set State) (formula : Formula Label) :
    meaning domain relation atoms (.neg (.neg formula)) = meaning domain relation atoms formula := by
  ext state
  have within := meaning_within domain relation atoms formula
  simp only [meaning, Set.mem_sdiff]
  constructor
  · tauto
  · intro member
    exact ⟨within member, by tauto⟩

namespace Controls

theorem deadlock_policy_is_part_of_the_model :
    () ∉ meaning Set.univ (fun _ _ : Unit => False) (fun _ : Unit => Set.univ) (.eg .truth) ∧
    () ∈ meaning Set.univ (CTLFixedPoints.stutter (fun _ _ : Unit => False))
      (fun _ : Unit => Set.univ) (.eg .truth) :=
  CTLFixedPoints.Controls.deadlock_policy_changes_truth

theorem negation_cannot_invent_an_invalid_state :
    false ∉ meaning ({true} : Set Bool) (fun _ _ => False) (fun _ : Unit => ∅) (.neg (.atom ())) := by
  simp [meaning]

theorem goal_is_satisfied_at_a_deadlock :
    () ∈ meaning Set.univ (fun _ _ : Unit => False) (fun _ : Unit => Set.univ) (.eu (.neg .truth) .truth) :=
  CTLFixedPoints.Until.reached (by simp [meaning])

end Controls

end Mettapedia.Logic.CTLFormula
