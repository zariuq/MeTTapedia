import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldFreshNamespaces
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.Materialization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationSyntax

/-!
# Consuming a privately materialized row through an actual held-rule step

The ambient copy rule takes exactly the temporary occurrence and publishes its
value at one new occurrence. It does not take the persistent schema. Its fresh
opening is derived from all terms retained by the current held-rule state.
These definition and resource laws do not assume that an arbitrary candidate
is admitted or that an observer can ignore intermediate protocol states.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldCopyConsumer

open Mettapedia.Logic.LP
open OneFrame (Terms frames ext)
open Presentation.Schematic (Tm rowSig)
open RuleOccurrences

universe uOcc uR uC uZ
variable {O : Type uOcc} {R : Type uR} {C : Type uC} {Z : Type uZ}

abbrev X := frames (FirstOrder.action rowSig)
abbrev E := ext (FirstOrder.action rowSig)
abbrev RowTerms := Terms Tm

def readerRule : RuleSyntax.Rule RowTerms :=
  ⟨PUnit.unit, ⟨[.var 0], [], [], [], [.var 0]⟩, []⟩

def readerSpec : Spec RowTerms C Z := Spec.ofRule readerRule

noncomputable def consumer (codes : Codes RowTerms C Z) (s : RState RowTerms O R C Z)
    (code : C) (temporary output : O) : RFiring O R E codes s where
  use := .ambient code
  ext := PUnit.unit
  opening := FreshNamespaces.opening (Equiv.refl Nat) (HeldFreshNamespaces.bound (Equiv.refl Nat) s) 0
  selection := ⟨[temporary], [], [output]⟩
  seen := []
  madeRules := []
  installed := []
  removedRules := []
  published := []

theorem consumer_spec (codes : Codes RowTerms C Z) (s : RState RowTerms O R C Z)
    (code : C) (temporary output : O) (declared : codes.unfold code = readerSpec) :
    (consumer codes s code temporary output).spec = readerSpec := declared

theorem consumer_fresh (codes : Codes RowTerms C Z) (s : RState RowTerms O R C Z)
    (code : C) (temporary output : O) : (consumer codes s code temporary output).Fresh X :=
  HeldFreshNamespaces.firing_fresh (Equiv.refl Nat) (consumer codes s code temporary output) 0 rfl

variable [DecidableEq O] [DecidableEq R]

theorem consumer_result_label (codes : Codes RowTerms C Z) (s : RState RowTerms O R C Z)
    (code : C) (temporary output : O) (declared : codes.unfold code = readerSpec) :
    ((consumer codes s code temporary output).result X).label output =
      (consumer codes s code temporary output).opening.applyTerm (.var 0) := by
  apply Materialization.result_label_single X (consumer codes s code temporary output) output (.var 0) rfl
  rw [consumer_spec codes s code temporary output declared]
  rfl

theorem temporary_is_consumed (codes : Codes RowTerms C Z) (s : RState RowTerms O R C Z)
    (code : C) (temporary output : O) (different : temporary ≠ output) :
    temporary ∉ ((consumer codes s code temporary output).result X).present := by
  apply Materialization.consumed_private_instance_is_absent X (consumer codes s code temporary output) temporary
  · exact List.mem_singleton_self temporary
  · simpa only [consumer, List.mem_singleton] using different

theorem consumer_keeps_held_rules (codes : Codes RowTerms C Z) (s : RState RowTerms O R C Z)
    (code : C) (temporary output : O) : ((consumer codes s code temporary output).result X).rules = s.rules := by
  change (s.rules \ (∅ : Finset R)) ∪ ∅ = s.rules
  simp only [Finset.sdiff_empty, Finset.union_empty]

#print axioms consumer_fresh
#print axioms consumer_result_label
#print axioms temporary_is_consumed
#print axioms consumer_keeps_held_rules

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldCopyConsumer
