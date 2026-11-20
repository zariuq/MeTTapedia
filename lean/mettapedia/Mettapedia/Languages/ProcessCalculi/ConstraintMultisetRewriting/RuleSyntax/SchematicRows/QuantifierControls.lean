import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Schema
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Examples

/-!
# Fresh use, shared unknowns and the limit of generalization

One schematic row can instantiate differently at two uses under the same caller
assignment. A shared row cannot. This distinction persists even with no outside
rows or knowledge: none queries of an escaping variable alone does not prove that
changing an existential/shared datum into a universally reusable schema preserves
repeated-use observations. Automatic generalization needs an additional logical
licence; an explicit binder may deliberately choose the schematic reading.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.QuantifierControls

open Mettapedia.Logic.LP
open OneFrame (Terms frames)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls (atoms action)

abbrev Tm := Terms (Term atoms)
abbrev X := frames action

def c (n : Nat) : Term atoms := .const n
def point (n : Nat) : Subst atoms := fun _ => c n
def freeClosure : Closure Tm PUnit.unit := ⟨⟨PUnit.unit, [], [], .var 0⟩, []⟩
def schematic : Row Tm PUnit.unit := .schematic freeClosure
def shared : Row Tm PUnit.unit := .shared (.var 0)

theorem schematic_reads (σ : Subst atoms) (n : Nat) : Row.ReadsAt X (b := PUnit.unit) σ (c n) schematic := by
  refine ⟨point n, ?_, .nil, rfl⟩
  intro equation missing
  cases missing

theorem distinct_payloads : c 5 ≠ c 6 := by
  intro same
  have impossible : (5 : Nat) = 6 := Term.const.inj same
  omega

theorem shared_reads_first : Row.ReadsAt X (b := PUnit.unit) (point 5) (c 5) shared := rfl

theorem shared_refuses_second : ¬ Row.ReadsAt X (b := PUnit.unit) (point 5) (c 6) shared :=
  distinct_payloads

theorem schematic_and_shared_overlap_properly :
    Row.ReadsAt X (b := PUnit.unit) (point 5) (c 5) schematic ∧
      Row.ReadsAt X (b := PUnit.unit) (point 5) (c 6) schematic ∧
      Row.ReadsAt X (b := PUnit.unit) (point 5) (c 5) shared ∧
      ¬ Row.ReadsAt X (b := PUnit.unit) (point 5) (c 6) shared :=
  ⟨schematic_reads _ _, schematic_reads _ _, shared_reads_first, shared_refuses_second⟩

theorem a_shared_unknown_cannot_be_instantiated_twice :
    ¬ ∃ σ : Subst atoms, Row.ReadsAt X (b := PUnit.unit) σ (c 5) shared ∧
      Row.ReadsAt X (b := PUnit.unit) σ (c 6) shared := by
  rintro ⟨σ, first, second⟩
  have one : σ 0 = c 5 := first
  have two : σ 0 = c 6 := second
  exact distinct_payloads (one.symm.trans two)

theorem fresh_uses_do_not_preserve_shared_aliases :
    (∃ σ : Subst atoms, Row.ReadsAt X (b := PUnit.unit) σ (c 5) schematic ∧
      Row.ReadsAt X (b := PUnit.unit) σ (c 6) schematic) ∧
      ¬ ∃ σ : Subst atoms, Row.ReadsAt X (b := PUnit.unit) σ (c 5) shared ∧
        Row.ReadsAt X (b := PUnit.unit) σ (c 6) shared :=
  ⟨⟨point 5, schematic_reads _ _, schematic_reads _ _⟩, a_shared_unknown_cannot_be_instantiated_twice⟩

theorem arbitrary_local_instantiation_is_not_reversible :
    (freeClosure.instantiate X (b := PUnit.unit) (point 5)).ReadsAt X (b := PUnit.unit) (point 5) (c 5) ∧
      ¬ (freeClosure.instantiate X (b := PUnit.unit) (point 5)).ReadsAt X (b := PUnit.unit) (point 5) (c 6) ∧
      freeClosure.ReadsAt X (b := PUnit.unit) (point 5) (c 6) := by
  refine ⟨?_, ?_, schematic_reads _ _⟩
  · refine ⟨point 5, ?_, .nil, rfl⟩
    intro equation missing
    cases missing
  · rintro ⟨_, _, _, output⟩
    exact distinct_payloads output

#print axioms schematic_and_shared_overlap_properly
#print axioms fresh_uses_do_not_preserve_shared_aliases
#print axioms arbitrary_local_instantiation_is_not_reversible

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.QuantifierControls
