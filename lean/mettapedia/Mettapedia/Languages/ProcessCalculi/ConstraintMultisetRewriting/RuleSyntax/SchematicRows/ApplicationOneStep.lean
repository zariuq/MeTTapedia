import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationCandidateAdmission

/-!
# Every compatible application is covered by an actual settled step

The existing total unifier supplies the attempt. Principality transports the
constructed candidate model to a result interpretation, retaining the source
context exactly. The result is read from the actual newly allocated occurrence,
not from an abstract consequence set or a separately defined logical output.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)
open ApplicationSyntax
open MeTTaCalculus.OccurrenceCommits (fire)

universe uOcc
variable {O : Type uOcc} [DecidableEq O]

theorem application_realized (judgmentTag arrowTag : Nat) (s : Store O) (caller : Subst rowSig)
    (known : X.Models (a := PUnit.unit) (b := PUnit.unit) caller s.knowledge)
    (major minor made : O) (majorPresent : major ∈ s.present) (minorPresent : minor ∈ s.present)
    (madeFresh : made ∉ s.present) (function argument domain codomain : Tm)
    (majorReading : (s.label major).ReadsAt X (b := PUnit.unit) caller
      (judgment judgmentTag function (arrow arrowTag domain codomain)))
    (minorReading : (s.label minor).ReadsAt X (b := PUnit.unit) caller
      (judgment judgmentTag argument domain)) :
    ∃ f : Attempt judgmentTag arrowTag O s,
      (machine judgmentTag arrowTag O).Admits f ∧
      f.raw = candidate judgmentTag arrowTag (sourceBound s) s major minor made ∧
      ∃ source : Subst rowSig,
        X.Models (a := PUnit.unit) (b := PUnit.unit) source f.result.knowledge ∧
        (∀ term ∈ context s, source.applyTerm (f.answer.applyTerm term) = caller.applyTerm term) ∧
        made ∈ f.result.present ∧
        (f.result.label made).ReadsAt X (b := PUnit.unit) source
          (judgment judgmentTag (app function argument) codomain) := by
  let raw := candidate judgmentTag arrowTag (sourceBound s) s major minor made
  obtain ⟨assignment, solved, agrees, output⟩ := candidate_model judgmentTag arrowTag s caller known
    major minor made majorPresent minorPresent function argument domain codomain majorReading minorReading
  obtain ⟨answer, accepted⟩ := (FirstOrder.accepted_iff_consistent (raw.information X)).mpr ⟨assignment, solved⟩
  let f : Attempt judgmentTag arrowTag O s := ⟨raw, answer, accepted⟩
  have admitted : (machine judgmentTag arrowTag O).Admits f :=
    candidate_admitted judgmentTag arrowTag s caller known major minor made majorPresent minorPresent
      madeFresh function argument domain codomain majorReading minorReading
  let template := (privateOpening (sourceBound s) 0).applyTerm
    (judgment judgmentTag (app (.var 0) (.var 3)) (.var 2))
  obtain ⟨source, interfaceAgreement, reading⟩ := PrincipalOutputs.solution_covered X
    (a := PUnit.unit) (m := PUnit.unit) (b := PUnit.unit)
    (raw.information X) answer f.principal (context s) template assignment solved
  have outputs : f.outputs = [Row.schematic
      (PrincipalOutputs.scheme X (a := PUnit.unit) (m := PUnit.unit) answer (context s) template)] := by
    rfl
  have labelled : f.result.label made = Row.schematic
      (PrincipalOutputs.scheme X (a := PUnit.unit) (m := PUnit.unit) answer (context s) template) := by
    change RuleSyntax.relabel (Tm := fun a => Row RowTerms a) f.retained [made] f.outputs made = _
    rw [outputs]
    simp [RuleSyntax.relabel]
  refine ⟨f, admitted, rfl, source,
    Interface.Frames.models_nil (X := X) (a := PUnit.unit) (b := PUnit.unit) source, ?_, ?_, ?_⟩
  · intro term inside
    have same := interfaceAgreement term inside
    change assignment.applyTerm term = source.applyTerm (answer.applyTerm term) at same
    exact same.symm.trans (agrees term inside)
  · change made ∈ fire s.present ((raw.selection).commit (T := Unit))
    simp [raw, candidate, Selection.commit, fire]
  · rw [labelled]
    change (PrincipalOutputs.scheme X (a := PUnit.unit) (m := PUnit.unit) answer (context s) template).ReadsAt
      X (b := PUnit.unit) source (assignment.applyTerm template) at reading
    change assignment.applyTerm template = _ at output
    rw [output] at reading
    exact reading

#print axioms application_realized

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine
