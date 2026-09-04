import Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionMatchExtension
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveSourceExecAdd

/-!
# Outputs of the decorated assertion launch

Each normal-verifier input and each continuation capability is produced by an
actual add sink of the compiler-derived decorated handler.  The proofs use a
generic reflective add interface rather than reopening the complete executor.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionPublication

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.Metamath.MM2CompressedProofAssertionContinuous
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionMatchExtension
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionFrame
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionLaunch
open Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedDirectAssertionSurface
open Mettapedia.Languages.Metamath.MM2CompressedProofExecution
open Mettapedia.Languages.Metamath.MM2CompressedProofOrderedActivation
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveComputable

private theorem sinks_context :
    decoratedDirectAssertionDirective.rule.tmpl.sinks =
      [.remove directAssertionPendingTemplate,
       .remove directAssertionLookupTemplate,
       .remove directAssertionMachineTemplate] ++
      .add directAssertionContextTemplate ::
        [.add directAssertionNormalControlTemplate,
         .add directAssertionNormalLabelTemplate,
         .add directAssertionReloadTemplate,
         .add (.var "compressed-assertion-rejoin-rule"),
         .add (.var "normal-bridge-rule")] := by
  rw [decoratedDirectAssertionDirective_sinks_exact]
  rfl

private theorem sinks_control :
    decoratedDirectAssertionDirective.rule.tmpl.sinks =
      [.remove directAssertionPendingTemplate,
       .remove directAssertionLookupTemplate,
       .remove directAssertionMachineTemplate,
       .add directAssertionContextTemplate] ++
      .add directAssertionNormalControlTemplate ::
        [.add directAssertionNormalLabelTemplate,
         .add directAssertionReloadTemplate,
         .add (.var "compressed-assertion-rejoin-rule"),
         .add (.var "normal-bridge-rule")] := by
  rw [decoratedDirectAssertionDirective_sinks_exact]
  rfl

private theorem sinks_label :
    decoratedDirectAssertionDirective.rule.tmpl.sinks =
      [.remove directAssertionPendingTemplate,
       .remove directAssertionLookupTemplate,
       .remove directAssertionMachineTemplate,
       .add directAssertionContextTemplate,
       .add directAssertionNormalControlTemplate] ++
      .add directAssertionNormalLabelTemplate ::
        [.add directAssertionReloadTemplate,
         .add (.var "compressed-assertion-rejoin-rule"),
         .add (.var "normal-bridge-rule")] := by
  rw [decoratedDirectAssertionDirective_sinks_exact]
  rfl

private theorem sinks_reload :
    decoratedDirectAssertionDirective.rule.tmpl.sinks =
      [.remove directAssertionPendingTemplate,
       .remove directAssertionLookupTemplate,
       .remove directAssertionMachineTemplate,
       .add directAssertionContextTemplate,
       .add directAssertionNormalControlTemplate,
       .add directAssertionNormalLabelTemplate] ++
      .add directAssertionReloadTemplate ::
        [.add (.var "compressed-assertion-rejoin-rule"),
         .add (.var "normal-bridge-rule")] := by
  rw [decoratedDirectAssertionDirective_sinks_exact]
  rfl

private theorem sinks_rejoin :
    decoratedDirectAssertionDirective.rule.tmpl.sinks =
      directAssertionSinks.dropLast ++
      .add (.var "compressed-assertion-rejoin-rule") ::
        [.add (.var "normal-bridge-rule")] := by
  rw [decoratedDirectAssertionDirective_sinks_exact]
  rfl

private theorem sinks_bridge :
    decoratedDirectAssertionDirective.rule.tmpl.sinks =
      directAssertionSinks ++ [.add (.var "normal-bridge-rule")] := by
  exact decoratedDirectAssertionDirective_sinks_exact

theorem fire_adds_context
    (context : DirectAssertionContext) (space : List Atom)
    (matched : ExactDecoratedDirectAssertionLaunch context space) :
    context.assertionContextRow ∈
      cFireReflectiveSourceExecFact space
        decoratedDirectAssertionDirective := by
  rcases matched with
    ⟨substitution, rowMember, _, _, _, contextRow, _, _, _, _, _⟩
  exact mem_cFireReflectiveSourceExecFact_of_add_sink space _ _ _ _ _
    sinks_context substitution rowMember contextRow (by
      intro sink member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩)

theorem fire_adds_normal_control
    (context : DirectAssertionContext) (space : List Atom)
    (matched : ExactDecoratedDirectAssertionLaunch context space) :
    context.normalControlRow ∈
      cFireReflectiveSourceExecFact space
        decoratedDirectAssertionDirective := by
  rcases matched with
    ⟨substitution, rowMember, _, _, _, _, control, _, _, _, _⟩
  exact mem_cFireReflectiveSourceExecFact_of_add_sink space _ _ _ _ _
    sinks_control substitution rowMember control (by
      intro sink member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> exact ⟨_, rfl⟩)

theorem fire_adds_normal_label
    (context : DirectAssertionContext) (space : List Atom)
    (matched : ExactDecoratedDirectAssertionLaunch context space) :
    context.normalLabelRow ∈
      cFireReflectiveSourceExecFact space
        decoratedDirectAssertionDirective := by
  rcases matched with
    ⟨substitution, rowMember, _, _, _, _, _, label, _, _, _⟩
  exact mem_cFireReflectiveSourceExecFact_of_add_sink space _ _ _ _ _
    sinks_label substitution rowMember label (by
      intro sink member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> exact ⟨_, rfl⟩)

theorem fire_adds_reload
    (context : DirectAssertionContext) (space : List Atom)
    (matched : ExactDecoratedDirectAssertionLaunch context space) :
    context.reloadRow ∈
      cFireReflectiveSourceExecFact space
        decoratedDirectAssertionDirective := by
  rcases matched with
    ⟨substitution, rowMember, _, _, _, _, _, _, reload, _, _⟩
  exact mem_cFireReflectiveSourceExecFact_of_add_sink space _ _ _ _ _
    sinks_reload substitution rowMember reload (by
      intro sink member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> exact ⟨_, rfl⟩)

theorem fire_adds_rejoin
    (context : DirectAssertionContext) (space : List Atom)
    (matched : ExactDecoratedDirectAssertionLaunch context space) :
    compressedAssertionRejoinRule ∈
      cFireReflectiveSourceExecFact space
        decoratedDirectAssertionDirective := by
  rcases matched with
    ⟨substitution, rowMember, _, _, _, _, _, _, _, rejoin, _⟩
  exact mem_cFireReflectiveSourceExecFact_of_add_sink space _ _ _ _ _
    sinks_rejoin substitution rowMember rejoin (by
      intro sink member
      simp only [List.mem_singleton] at member
      subst sink
      exact ⟨_, rfl⟩)

theorem fire_adds_bridge
    (context : DirectAssertionContext) (space : List Atom)
    (matched : ExactDecoratedDirectAssertionLaunch context space) :
    compressedNormalDispatchBridgeRule ∈
      cFireReflectiveSourceExecFact space
        decoratedDirectAssertionDirective := by
  rcases matched with
    ⟨substitution, rowMember, _, _, _, _, _, _, _, _, bridge⟩
  exact mem_cFireReflectiveSourceExecFact_of_last_add space _ _ _ _
    sinks_bridge substitution rowMember bridge

theorem decorated_direct_assertion_fire_adds_launch_rows
    (context : DirectAssertionContext) (space : List Atom)
    (matched : ExactDecoratedDirectAssertionLaunch context space) :
    ∀ row ∈ decoratedDirectAssertionLaunchRows context,
      row ∈ cFireReflectiveSourceExecFact space
        decoratedDirectAssertionDirective := by
  intro row member
  change row ∈
    [context.assertionContextRow, context.normalControlRow,
     context.normalLabelRow, context.reloadRow, compressedAssertionRejoinRule,
     compressedNormalDispatchBridgeRule] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact fire_adds_context context space matched
  · exact fire_adds_normal_control context space matched
  · exact fire_adds_normal_label context space matched
  · exact fire_adds_reload context space matched
  · exact fire_adds_rejoin context space matched
  · exact fire_adds_bridge context space matched

#print axioms fire_adds_context
#print axioms fire_adds_normal_control
#print axioms fire_adds_normal_label
#print axioms fire_adds_reload
#print axioms fire_adds_rejoin
#print axioms fire_adds_bridge
#print axioms decorated_direct_assertion_fire_adds_launch_rows

end Mettapedia.Languages.Metamath.MM2CompressedProofDecoratedAssertionPublication
