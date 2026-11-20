import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationOneStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationSubstitution

/-!
# One polymorphic datum can supply two independent application premises

The stored identity proof is read twice at different type instances in one
actual firing. The same two concrete readings cannot be supplied by one shared
unknown under any single caller assignment. This distinguishes independently
opened schematic data from merely unresolved shared data.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine.Controls

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig RowFunction args2 tail)
open ApplicationSyntax

def proposition : Tm := symbol 20
def identityProof : Tm := symbol 10
def identityValue : Tm := judgment 0 identityProof (arrow 1 (.var 0) (.var 0))
def identitySchema : Closure RowTerms PUnit.unit := ⟨⟨PUnit.unit, [], [], identityValue⟩, []⟩
def source : Store Nat := ⟨PUnit.unit, [], {0}, fun _ => .schematic identitySchema⟩

theorem identity_reading (chosen : Tm) :
    (Row.schematic identitySchema : Row RowTerms PUnit.unit).ReadsAt X (b := PUnit.unit)
      (Subst.id rowSig) (judgment 0 identityProof (arrow 1 chosen chosen)) := by
  refine ⟨Subst.single (σ := rowSig) 0 chosen,
    Interface.Frames.models_nil (X := X) (a := PUnit.unit) (b := PUnit.unit) (Subst.single (σ := rowSig) 0 chosen),
    List.Forall₂.nil, ?_⟩
  change (Subst.single (σ := rowSig) 0 chosen).applyTerm identityValue = judgment 0 identityProof (arrow 1 chosen chosen)
  simp only [identityValue, apply_judgment, apply_arrow, identityProof, apply_symbol, Subst.applyTerm]
  rfl

theorem one_occurrence_two_instances :
    ∃ f : Attempt 0 1 Nat source, (machine 0 1 Nat).Admits f ∧
      ∃ point : Subst rowSig, 1 ∈ f.result.present ∧
        (f.result.label 1).ReadsAt X (b := PUnit.unit) point
          (judgment 0 (app identityProof identityProof) (arrow 1 proposition proposition)) := by
  obtain ⟨f, admitted, _, point, _, _, present, reading⟩ :=
    application_realized 0 1 source (Subst.id rowSig)
      (Interface.Frames.models_nil (X := X) (a := PUnit.unit) (b := PUnit.unit) _)
      0 0 1 (by decide) (by decide) (by decide) identityProof identityProof
      (arrow 1 proposition proposition) (arrow 1 proposition proposition)
      (identity_reading (arrow 1 proposition proposition)) (identity_reading proposition)
  exact ⟨f, admitted, point, present, reading⟩

def rightArgument : Tm → Tm
  | .app .app children => children tail
  | other => other

theorem shared_cannot_supply_both (caller : Subst rowSig) :
    ¬ ((Row.shared identityValue : Row RowTerms PUnit.unit).ReadsAt X (b := PUnit.unit) caller
        (judgment 0 identityProof
          (arrow 1 (arrow 1 proposition proposition) (arrow 1 proposition proposition))) ∧
      (Row.shared identityValue : Row RowTerms PUnit.unit).ReadsAt X (b := PUnit.unit) caller
        (judgment 0 identityProof (arrow 1 proposition proposition))) := by
  rintro ⟨major, minor⟩
  change caller.applyTerm identityValue = _ at major minor
  simp only [identityValue, apply_judgment, apply_arrow, identityProof, apply_symbol, Subst.applyTerm] at major minor
  have majorType : caller 0 = arrow 1 proposition proposition :=
    congrArg (fun value => rightArgument (rightArgument value)) major
  have minorType : caller 0 = proposition :=
    congrArg (fun value => rightArgument (rightArgument value)) minor
  have impossible : proposition = arrow 1 proposition proposition := minorType.symm.trans majorType
  cases impossible

/-- Closed captured terms carry no caller-dependent information. This is a
reading-view law; it does not identify raw payload keys or named origins. -/
theorem ground_capture_elision (context : List Tm) (value : Tm)
    (ground : ∀ term ∈ context, term.isGround) (caller : Subst rowSig) (observed : Tm) :
    (ApplicationSemantics.generalized context value).ReadsAt X (b := PUnit.unit) caller observed ↔
      (ApplicationSemantics.generalized [] value).ReadsAt X (b := PUnit.unit) caller observed := by
  constructor
  · rintro ⟨locals, known, _, output⟩
    exact ⟨locals, known, List.Forall₂.nil, output⟩
  · rintro ⟨locals, known, _, output⟩
    refine ⟨locals, known, List.forall₂_same.mpr ?_, output⟩
    intro term inside
    change locals.applyTerm term = caller.applyTerm term
    rw [FirstOrder.ground_fixed locals term (ground term inside),
      FirstOrder.ground_fixed caller term (ground term inside)]

#print axioms identity_reading
#print axioms one_occurrence_two_instances
#print axioms shared_cannot_supply_both
#print axioms ground_capture_elision

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine.Controls
