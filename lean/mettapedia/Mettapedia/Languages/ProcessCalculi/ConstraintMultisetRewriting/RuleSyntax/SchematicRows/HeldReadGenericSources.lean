import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadEncoding
import Mathlib.Data.Finset.Sum

/-!
# A common mixed source without an arbitrary padding term

An existing ordinary state and a finite family of closures present the same
resources in two ways: ordinary/schematic row occurrences, or ordinary data
beside persistent held schemas. Disjoint occurrence tags retain both kinds of
identity. Both views use exactly the same source knowledge and captured terms.

The ordinary state already supplies its labels. No inhabitant of every term
frame, universal value variable or new code-installation capability is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericSources

open RuleOccurrences

universe uO uT uOcc uR
variable {Obj : Type uO} {Tm : Obj → Type uT} {O : Type uOcc} {R : Type uR}

def hosted (ordinary : RuleSyntax.State Tm O) (rows : Finset R)
    (closures : R → Closure Tm ordinary.frame) : RState Tm O R (HeldReadEncoding.Code Tm) Unit where
  toState := ordinary
  rules := rows
  held r := (closures r).held (fun schema => Sum.inl schema) ()

def mixed (ordinary : RuleSyntax.State Tm O) (rows : Finset R)
    (closures : R → Closure Tm ordinary.frame) : State Tm (O ⊕ R) where
  frame := ordinary.frame
  knowledge := ordinary.knowledge
  present := ordinary.present.disjSum rows
  label
    | .inl o => .shared (ordinary.label o)
    | .inr r => .schematic (closures r)

theorem ordinary_present (ordinary : RuleSyntax.State Tm O) (rows : Finset R)
    (closures : R → Closure Tm ordinary.frame) (o : O) :
    Sum.inl o ∈ (mixed ordinary rows closures).present ↔ o ∈ ordinary.present :=
  Finset.inl_mem_disjSum

theorem schematic_present (ordinary : RuleSyntax.State Tm O) (rows : Finset R)
    (closures : R → Closure Tm ordinary.frame) (r : R) :
    Sum.inr r ∈ (mixed ordinary rows closures).present ↔ r ∈ rows :=
  Finset.inr_mem_disjSum

theorem schema_specification (ordinary : RuleSyntax.State Tm O) (rows : Finset R)
    (closures : R → Closure Tm ordinary.frame) (r : R) :
    HeldReadEncoding.codes.unfold ((hosted ordinary rows closures).held r).code =
      (closures r).schema.toSpec := rfl

theorem schema_arguments (ordinary : RuleSyntax.State Tm O) (rows : Finset R)
    (closures : R → Closure Tm ordinary.frame) (r : R) :
    ((hosted ordinary rows closures).held r).args = (closures r).args := rfl

theorem scope_mentions_iff (ordinary : RuleSyntax.State Tm O) (rows : Finset R)
    (closures : R → Closure Tm ordinary.frame) (term : Tm ordinary.frame) :
    (mixed ordinary rows closures).scope.Mentions term ↔
      (hosted ordinary rows closures).Mentions term := by
  refine (State.scope_mentions_iff (mixed ordinary rows closures) term).trans ?_
  change (term ∈ ordinary.knowledge.map Prod.fst ∨ term ∈ ordinary.knowledge.map Prod.snd ∨
      ∃ occurrence ∈ ordinary.present.disjSum rows,
        term ∈ ((mixed ordinary rows closures).label occurrence).ambientTerms) ↔
    ordinary.Mentions term ∨ ∃ r ∈ rows, term ∈ (closures r).args
  constructor
  · rintro (left | right | ⟨occurrence, present, member⟩)
    · exact Or.inl (Or.inl left)
    · exact Or.inl (Or.inr (Or.inl right))
    · cases occurrence with
      | inl o =>
        have old := Finset.inl_mem_disjSum.mp present
        change term ∈ [ordinary.label o] at member
        exact Or.inl (Or.inr (Or.inr ⟨o, old, (List.mem_singleton.mp member).symm⟩))
      | inr r =>
        exact Or.inr ⟨r, Finset.inr_mem_disjSum.mp present, member⟩
  · rintro ((left | right | ⟨o, present, labelled⟩) | ⟨r, present, member⟩)
    · exact Or.inl left
    · exact Or.inr (Or.inl right)
    · exact Or.inr (Or.inr ⟨.inl o, Finset.inl_mem_disjSum.mpr present,
        List.mem_singleton.mpr labelled.symm⟩)
    · exact Or.inr (Or.inr ⟨.inr r, Finset.inr_mem_disjSum.mpr present, member⟩)

#print axioms ordinary_present
#print axioms schematic_present
#print axioms schema_specification
#print axioms scope_mentions_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericSources
