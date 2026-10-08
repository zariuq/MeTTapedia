import Mettapedia.GSLT.Logic.ProgrammableSpaceMaterial
import Mettapedia.GSLT.Logic.ProgrammableSpaceReadings
import Mettapedia.GSLT.Logic.ProgrammableSpaceAtomCoding
import Mettapedia.GSLT.LanguageDef.ProgrammableSpaceInstances

/-!
# Concrete support and policy/outcome observers of shared executions

Both interpreters use the same fully constructed atom graph dictionary.
Current support has its exact membership kernel. A richer observer also sees
the ordered agenda's current requests, residuals, policy accounts and MM2
matching rows. Authored beta leaves current fact support unchanged while
changing this declared reading. Source receipts remain in the underlying
space even for an observer that forgets them.

Atom identity here is literal. The MM2 compact-key support quotient is a
separate source/storage comparison; its alpha-equivalent presentations are
not silently equated with arbitrary literal atom or receipt readings.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ProgrammableSpaceMaterialInstances

open _root_.CategoryTheory
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.Core.ProgrammableSpace
open Mettapedia.GSLT.LanguageDef
open ProgrammableSpaceInstances
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open PowerClassPresheafDescent.Controls
open ContextualCoalgebraLabelledGraph

abbrev coding := Mettapedia.GSLT.Logic.ProgrammableSpaceAtomCoding.coding
abbrev family := ProgrammableSpaceMaterial.states languages policies
abbrev coalgebra := ProgrammableSpaceMaterial.dynamics languages policies

def factRead (atom : Atom) (space : Workspace) : Prop := atom ∈ space.atoms
def factValue (space : Workspace) : HSet := ProgrammableSpaceReadings.support coding space.atoms

theorem fact_value_kernel (first second : Workspace) :
    factValue first = factValue second ↔ ∀ atom, factRead atom first ↔ factRead atom second :=
  ProgrammableSpaceReadings.support_eq_iff coding first.atoms second.atoms

abbrev factInterpretation := ProgrammableSpaceMaterial.interpretation languages policies factRead coding

theorem behaviour_preserves_support (point : Stagesᵒᵖ) (first second : family.obj point)
    (same : factInterpretation.app point first = factInterpretation.app point second) :
    factValue first.val = factValue second.val :=
  (fact_value_kernel first.val second.val).mpr fun atom =>
    ProgrammableSpaceMaterial.equality_preserves_readings languages policies factRead coding
      point first second same atom

def natural (value : Nat) : Atom := .grounded (.int (.ofNat value))

def rowView (row : Mettapedia.Languages.ProcessCalculi.MORK.MM2MatchingCursor.Row) : Atom :=
  .expression [.expression (row.1.map fun binding => .expression [.symbol binding.1, binding.2]),
    .expression (row.2.map fun witness => .expression [witness.1, natural witness.2])]

def transactionView : ProgrammableSpaceMM2.Residual → Atom
  | .pending request => .expression [.symbol "pending", request.directive.atom]
  | .committed receipt => .expression [.symbol "committed", receipt.request.directive.atom,
      .expression receipt.before, .expression receipt.after, .expression (receipt.rows.map rowView)]

def workView (work : Work languages policies) : Atom :=
  match work with
  | ⟨.rewrite, session⟩ => .expression [.symbol "rewrite",
      natural session.scope.ambient, ProgrammableSpaceSyntax.encode session.request,
      ProgrammableSpaceSyntax.encode session.residual, natural session.policyState]
  | ⟨.transaction, session⟩ => .expression [.symbol "transaction",
      .symbol (match session.scope with | .leaveInert => "leave-inert" | .consume => "consume"),
      session.request.directive.atom, transactionView session.residual, natural session.policyState]

def agendaView (space : Workspace) : Atom :=
  .expression [.symbol "agenda", .expression (space.pending.map workView)]

def observationList (space : Workspace) : List Atom :=
  space.atoms.map (fun atom => .expression [.symbol "fact", atom]) ++
    [agendaView space, .expression [.symbol "commits", natural space.history.length]]

def policyOutcomeRead (reading : Atom) (space : Workspace) : Prop :=
  reading ∈ observationList space

abbrev policyOutcomeInterpretation :=
  ProgrammableSpaceMaterial.interpretation languages policies policyOutcomeRead coding

theorem fact_read_is_declared (atom : Atom) (space : Workspace) :
    policyOutcomeRead (.expression [.symbol "fact", atom]) space ↔ factRead atom space := by
  simp [policyOutcomeRead, observationList, agendaView, factRead]

theorem policy_outcome_behaviour_preserves_support (point : Stagesᵒᵖ) (first second : family.obj point)
    (same : policyOutcomeInterpretation.app point first = policyOutcomeInterpretation.app point second) :
    factValue first.val = factValue second.val := by
  apply (fact_value_kernel first.val second.val).mpr
  intro atom
  rw [← fact_read_is_declared, ← fact_read_is_declared]
  exact ProgrammableSpaceMaterial.equality_preserves_readings languages policies
    policyOutcomeRead coding point first second same _

theorem registered_started : Started languages policies registered := by
  unfold registered
  apply start_started
  apply start_started
  exact initial_started languages policies atoms

def beforeState : family.obj (world 3) := ⟨registered, registered_started, by decide⟩
def afterState : family.obj (world 3) :=
  ⟨afterRewrite, step_started languages policies actual_rewrite_action registered_started, by decide⟩

theorem actual_computation_keeps_current_facts :
    factValue beforeState.val = factValue afterState.val := rfl

theorem actual_computation_changes_declared_account :
    policyOutcomeRead (.expression [.symbol "commits", natural 0]) beforeState.val ∧
      ¬ policyOutcomeRead (.expression [.symbol "commits", natural 0]) afterState.val := by
  unfold policyOutcomeRead
  decide +kernel

theorem current_facts_do_not_determine_observed_behaviour :
    factValue beforeState.val = factValue afterState.val ∧
      policyOutcomeInterpretation.app (world 3) beforeState ≠
        policyOutcomeInterpretation.app (world 3) afterState := by
  refine ⟨actual_computation_keeps_current_facts, ?_⟩
  intro same
  exact actual_computation_changes_declared_account.2
    ((ProgrammableSpaceMaterial.equality_preserves_readings languages policies
      policyOutcomeRead coding (world 3) beforeState afterState same _).mp
        actual_computation_changes_declared_account.1)

end Mettapedia.GSLT.ProgrammableSpaceMaterialInstances
