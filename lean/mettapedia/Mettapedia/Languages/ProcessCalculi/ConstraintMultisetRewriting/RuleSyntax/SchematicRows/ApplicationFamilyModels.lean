import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationFamilies

/-!
# Exact output families of a canonical pair application

A model of the actual candidate information supplies both ordered premise
readings. Conversely, every compatible pair is retained by the single made
scheme. The equality compares whole reading sets at one protected caller,
not independent singleton result interpretations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)
open ApplicationSyntax

universe uOcc
variable {judgmentTag arrowTag : Nat} {O : Type uOcc} [DecidableEq O] {s : Store O}

def pairFamily (judgmentTag arrowTag : Nat) (s : Store O) (caller : Subst rowSig)
    (major minor : O) : Set Tm :=
  {value | ∃ function argument domain codomain : Tm,
    (s.label major).ReadsAt X (b := PUnit.unit) caller
      (judgment judgmentTag function (arrow arrowTag domain codomain)) ∧
    (s.label minor).ReadsAt X (b := PUnit.unit) caller
      (judgment judgmentTag argument domain) ∧
    value = judgment judgmentTag (app function argument) codomain}

omit [DecidableEq O] in
theorem candidate_model_premises (judgmentTag arrowTag bound : Nat) (s : Store O)
    (major minor made : O) (assignment : Subst rowSig)
    (solved : X.Models (a := PUnit.unit) (b := PUnit.unit) assignment
      ((candidate judgmentTag arrowTag bound s major minor made).information X))
    (shapes : (candidate judgmentTag arrowTag bound s major minor made).Shapes X) :
    ∃ function argument domain codomain : Tm,
      (s.label major).ReadsAt X (b := PUnit.unit) assignment
        (judgment judgmentTag function (arrow arrowTag domain codomain)) ∧
      (s.label minor).ReadsAt X (b := PUnit.unit) assignment
        (judgment judgmentTag argument domain) ∧
      assignment.applyTerm (candidateTemplate judgmentTag bound) =
        judgment judgmentTag (app function argument) codomain := by
  have paired := (candidate judgmentTag arrowTag bound s major minor made).read_pattern_readings
    X assignment solved shapes
  have first := (List.forall₂_cons.mp paired).1
  have second := (List.forall₂_cons.mp (List.forall₂_cons.mp paired).2).1
  change (s.label major).ReadsAt X (b := PUnit.unit) (assignment.comp (Subst.id rowSig))
    (assignment.applyTerm ((privateOpening bound 0).applyTerm
      (judgment judgmentTag (.var 0) (arrow arrowTag (.var 1) (.var 2))))) at first
  change (s.label minor).ReadsAt X (b := PUnit.unit) (assignment.comp (Subst.id rowSig))
    (assignment.applyTerm ((privateOpening bound 0).applyTerm
      (judgment judgmentTag (.var 3) (.var 1)))) at second
  rw [Subst.comp_id_right] at first second
  simp only [apply_judgment, apply_arrow, Subst.applyTerm] at first second
  refine ⟨assignment.applyTerm (privateOpening bound 0 0),
    assignment.applyTerm (privateOpening bound 0 3),
    assignment.applyTerm (privateOpening bound 0 1),
    assignment.applyTerm (privateOpening bound 0 2), first, second, ?_⟩
  simp only [candidateTemplate, apply_judgment, apply_app, Subst.applyTerm]

theorem candidate_family_sound (f : Attempt judgmentTag arrowTag O s)
    (admitted : (machine judgmentTag arrowTag O).Admits f)
    (caller source : Subst rowSig)
    (agrees : ∀ term ∈ context s,
      source.applyTerm (f.answer.applyTerm term) = caller.applyTerm term)
    (major minor made : O) (majorPresent : major ∈ s.present)
    (minorPresent : minor ∈ s.present)
    (same : f.raw = candidate judgmentTag arrowTag (sourceBound s) s major minor made)
    (value : Tm)
    (reading : (f.result.label made).ReadsAt X (b := PUnit.unit) source value) :
    value ∈ pairFamily judgmentTag arrowTag s caller major minor := by
  rw [candidate_output_label f major minor made same] at reading
  obtain ⟨assignment, solved, captures, output⟩ :=
    (PrincipalOutputs.reading_iff X (a := PUnit.unit) (m := PUnit.unit) (b := PUnit.unit)
      (f.raw.information X) f.answer f.principal (context s)
      (candidateTemplate judgmentTag (sourceBound s)) source value).mp reading
  have shapes := admitted.1
  rw [same] at solved shapes
  obtain ⟨function, argument, domain, codomain, majorReading, minorReading, produced⟩ :=
    candidate_model_premises judgmentTag arrowTag (sourceBound s) s major minor made
      assignment solved shapes
  have agreement : ∀ term ∈ context s, assignment.applyTerm term = caller.applyTerm term := by
    intro term inside
    exact (captures term inside).trans (agrees term inside)
  refine ⟨function, argument, domain, codomain, ?_, ?_, output.symm.trans produced⟩
  · exact (Row.readsAt_source_congr X (s.label major) assignment caller
      (fun term inside => agreement term (ambient_in_context s major majorPresent term inside)) _).mp majorReading
  · exact (Row.readsAt_source_congr X (s.label minor) assignment caller
      (fun term inside => agreement term (ambient_in_context s minor minorPresent term inside)) _).mp minorReading

theorem candidate_family_iff (f : Attempt judgmentTag arrowTag O s)
    (admitted : (machine judgmentTag arrowTag O).Admits f)
    (caller source : Subst rowSig)
    (known : X.Models (a := PUnit.unit) (b := PUnit.unit) caller s.knowledge)
    (agrees : ∀ term ∈ context s,
      source.applyTerm (f.answer.applyTerm term) = caller.applyTerm term)
    (major minor made : O) (majorPresent : major ∈ s.present)
    (minorPresent : minor ∈ s.present) (madeFresh : made ∉ s.present)
    (same : f.raw = candidate judgmentTag arrowTag (sourceBound s) s major minor made)
    (value : Tm) :
    (f.result.label made).ReadsAt X (b := PUnit.unit) source value ↔
      value ∈ pairFamily judgmentTag arrowTag s caller major minor := by
  refine ⟨candidate_family_sound f admitted caller source agrees major minor made
    majorPresent minorPresent same value, ?_⟩
  rintro ⟨function, argument, domain, codomain, majorReading, minorReading, rfl⟩
  exact candidate_family_complete f caller source known agrees major minor made
    majorPresent minorPresent madeFresh same function argument domain codomain majorReading minorReading

#print axioms candidate_model_premises
#print axioms candidate_family_sound
#print axioms candidate_family_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine
