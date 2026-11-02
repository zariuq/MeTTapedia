import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingPermissionControls

/-!
# A real completed firing uses an explicitly granted capture

The source rule tells the passed capture zero, not a fresh rule-local name.
Its actual worklist result satisfies the structural permission protecting
capture one and a compound observation of it. The granted equality becomes
entailed; the protected joint interface remains covered by the general
firing theorem. No physical row is taken or made in this control.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingPermissionFiringControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualExecution ContextualSchedulePromotion
open ContextualBindingPermissions ContextualBindingPermissionFirings
open ContextualBindingPermissionControls (x protectY)
open ContextualSelectionViews.Controls (base locals captures active atom p pair)
open ContextualPathSnapshotControls (tell tellRule tellOutputs)

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) :=
  inferInstanceAs (DecidableEq ContextualFrame.Controls.Operator)

abbrev initial := ContextualProcessInterference.initial

theorem the_granted_capture_is_initially_unconstrained :
    ¬ ContextualGuardSemantics.Ask locals initial.inventory.configuration.equations initial.inventory.rows
      initial.inventory.configuration.present (.equal x (atom captures)) := by
  intro asked
  have equal := asked Nat captures (generator captures) (fun _ member => by cases member)
  change instantiate (generator captures) x = instantiate (generator captures) (atom captures) at equal
  rw [instantiate_identity, instantiate_identity] at equal
  have heads := (Term.op.inj equal).1
  cases heads

/-- The solver is actually run through its existing totality theorem. The
permission is checked structurally on that run's exact target equations. -/
theorem an_actual_firing_refines_the_granted_capture_and_protects_the_other :
    ∃ target : Endpoint locals Nat [] (), ∃ firing : Firing locals initial target,
      firing.rule = tellRule ∧ firing.selection = tell ∧
      let prepared := Prepared.ofFiring firing
      let granted : Set prepared.target.Names := {Sum.inl (Sum.inr (0 : Nat))}
      Permitted granted (incoming prepared) (additions prepared) (callerView prepared protectY) ∧
        ContextualGuardSemantics.Ask locals prepared.target.inventory.configuration.equations
          (inputRows prepared) initial.inventory.configuration.present
          (inputCheck prepared (.equal x (atom captures))) := by
  obtain ⟨fuel, solved | refused⟩ := ContextualTransportedActivation.solve_or_refute locals captures
    ContextualProcessInterference.tell_admitted ContextualProcessInterference.tell_patterned
  · obtain ⟨update, returned⟩ := solved
    let target := computedTarget locals initial tellRule tell tellOutputs
      ContextualProcessInterference.tell_rule_covered ContextualProcessInterference.tell_admitted update
    let firing : Firing locals initial target :=
      ⟨tellRule, ContextualProcessInterference.tell_rule_covered, tell, tellOutputs, fuel, update,
        ContextualProcessInterference.tell_admitted, returned.computed, returned.empty, rfl⟩
    let prepared := Prepared.ofFiring firing
    let zero : prepared.target.Names := Sum.inl (Sum.inr (0 : Nat))
    let one : prepared.target.Names := Sum.inl (Sum.inr (1 : Nat))
    have emptyIncoming : incoming prepared = [] := rfl
    have extra : additions prepared =
        [(generator prepared.target.declarations zero, atom prepared.target.declarations)] := by
      with_unfolding_all rfl
    have observations : callerView prepared protectY =
        [observe (generator prepared.target.declarations one),
          observe (p (generator prepared.target.declarations one))] := by
      with_unfolding_all rfl
    have check : inputCheck prepared (.equal x (atom captures)) =
        .equal (generator prepared.target.declarations zero) (atom prepared.target.declarations) := by
      with_unfolding_all rfl
    have zeroNames : equationNames (S := base) (declarations := prepared.target.declarations) (Γ := []) (sort := ())
        (generator prepared.target.declarations zero, atom prepared.target.declarations) = [zero] := by
      with_unfolding_all rfl
    have oneNames : support (generator prepared.target.declarations one) = [one] := by
      with_unfolding_all rfl
    have compoundNames : support (p (generator prepared.target.declarations one)) = [one] := by
      with_unfolding_all rfl
    refine ⟨target, firing, rfl, rfl, ?_, ?_⟩
    · change Permitted ({zero} : Set prepared.target.Names) (incoming prepared)
        (additions prepared) (callerView prepared protectY)
      rw [emptyIncoming, extra, observations]
      apply empty_store_permitted
      · intro equation present name member
        obtain rfl := List.mem_singleton.mp present
        have same : name = zero := by
          exact List.mem_singleton.mp (zeroNames ▸ member)
        exact same
      · intro name member atZero
        change name = zero at atZero
        change (∃ observation ∈ [observe (generator prepared.target.declarations one),
          observe (p (generator prepared.target.declarations one))],
          name ∈ support observation.2.2) at member
        have atOne : name = one := by
          obtain ⟨observation, chosen, named⟩ := member
          rcases List.mem_cons.mp chosen with rfl | remaining
          · exact List.mem_singleton.mp (oneNames ▸ named)
          · obtain rfl := List.mem_singleton.mp remaining
            exact List.mem_singleton.mp (compoundNames ▸ named)
        have impossible : (1 : Nat) = 0 := Sum.inr.inj (Sum.inl.inj (atOne.symm.trans atZero))
        omega
    · change ContextualGuardSemantics.Ask locals prepared.target.inventory.configuration.equations
        (inputRows prepared) initial.inventory.configuration.present
        (inputCheck prepared (.equal x (atom captures)))
      rw [check]
      apply ContextualGuardSemantics.Ask.equal_of_mem locals
      rw [target_equations_split, emptyIncoming, extra]
      exact List.mem_singleton_self _
  · obtain ⟨impossible, _computed⟩ := refused
    apply False.elim
    let constantModel : Assignment active active := fun name => match name with
      | .inl _ => atom active
      | .inr _ => atom active
    apply impossible active constantModel
    apply (ContextualResidual.models_observeProblem _ _).mpr
    intro equation member
    change equation ∈ [(generator active (.inr 0), atom active)] at member
    obtain rfl := List.mem_singleton.mp member
    rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualBindingPermissionFiringControls
