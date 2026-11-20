import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationOneStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationProtectedRuns

/-!
# One actual application retains its whole compatible result family

The canonical candidate and the total solver do not depend on which compatible
premise reading supplied a consistency witness. Its returned scheme captures
the actual source context. All result interpretations retaining that context
therefore give the same family, not merely one chosen output value.

These are laws of the existing prepared machine. They do not replace an
execution with an abstract consequence set or choose a scheduling default.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)
open ApplicationSyntax

universe uOcc
variable {judgmentTag arrowTag : Nat} {O : Type uOcc} {s : Store O}

theorem Attempt.eq_of_raw_eq (first second : Attempt judgmentTag arrowTag O s)
    (same : first.raw = second.raw) : first = second := by
  cases first with
  | mk firstRaw firstAnswer firstAccepted =>
    cases second with
    | mk secondRaw secondAnswer secondAccepted =>
      dsimp only at same
      cases same
      have answers := Option.some.inj (firstAccepted.symm.trans secondAccepted)
      cases answers
      rfl

def candidateTemplate (judgmentTag bound : Nat) : Tm :=
  (privateOpening bound 0).applyTerm
    (judgment judgmentTag (app (.var 0) (.var 3)) (.var 2))

variable [DecidableEq O]

theorem candidate_output_label (f : Attempt judgmentTag arrowTag O s)
    (major minor made : O)
    (same : f.raw = candidate judgmentTag arrowTag (sourceBound s) s major minor made) :
    f.result.label made = Row.schematic
      (PrincipalOutputs.scheme X (a := PUnit.unit) (m := PUnit.unit)
        f.answer (context s) (candidateTemplate judgmentTag (sourceBound s))) := by
  have madeWord : f.raw.selection.made = [made] := by rw [same]; rfl
  change RuleSyntax.relabel (Tm := fun a => Row RowTerms a) f.retained
    f.raw.selection.made f.outputs made = _
  rw [madeWord, f.outputs_singleton, same]
  simp [RuleSyntax.relabel, candidate, candidateTemplate]

theorem candidate_family_complete (f : Attempt judgmentTag arrowTag O s)
    (caller source : Subst rowSig)
    (known : X.Models (a := PUnit.unit) (b := PUnit.unit) caller s.knowledge)
    (agrees : ∀ term ∈ context s,
      source.applyTerm (f.answer.applyTerm term) = caller.applyTerm term)
    (major minor made : O) (majorPresent : major ∈ s.present)
    (minorPresent : minor ∈ s.present) (madeFresh : made ∉ s.present)
    (same : f.raw = candidate judgmentTag arrowTag (sourceBound s) s major minor made)
    (function argument domain codomain : Tm)
    (majorReading : (s.label major).ReadsAt X (b := PUnit.unit) caller
      (judgment judgmentTag function (arrow arrowTag domain codomain)))
    (minorReading : (s.label minor).ReadsAt X (b := PUnit.unit) caller
      (judgment judgmentTag argument domain)) :
    (f.result.label made).ReadsAt X (b := PUnit.unit) source
      (judgment judgmentTag (app function argument) codomain) := by
  obtain ⟨other, _, rawSame, otherSource, _, otherAgrees, _, reading⟩ :=
    application_realized judgmentTag arrowTag s caller known major minor made
      majorPresent minorPresent madeFresh function argument domain codomain
      majorReading minorReading
  have attempts : other = f := Attempt.eq_of_raw_eq other f (rawSame.trans same.symm)
  subst other
  rw [candidate_output_label f major minor made same] at reading ⊢
  apply (Closure.readsAt_source_congr X
    (PrincipalOutputs.scheme X (a := PUnit.unit) (m := PUnit.unit) f.answer
      (context s) (candidateTemplate judgmentTag (sourceBound s))) otherSource source ?_ _).mp reading
  intro captured member
  obtain ⟨original, inside, rfl⟩ := List.mem_map.mp member
  change otherSource.applyTerm (f.answer.applyTerm original) =
    source.applyTerm (f.answer.applyTerm original)
  exact (otherAgrees original inside).trans (agrees original inside).symm

theorem ProtectedRun.retained_reading_iff {caller : Subst rowSig}
    (execution : ProtectedRun judgmentTag arrowTag s caller)
    (o : O) (present : o ∈ s.present) (value : Tm) :
    (execution.run.last.label o).ReadsAt X (b := PUnit.unit) execution.source value ↔
      (s.label o).ReadsAt X (b := PUnit.unit) caller value := by
  refine (run_retained_reading_iff execution.run o present execution.source value).trans ?_
  apply Row.readsAt_source_congr X
  intro term inside
  change (execution.source.comp execution.run.toLast).applyTerm term = caller.applyTerm term
  rw [Subst.applyTerm_comp]
  exact execution.agrees term (ambient_in_context s o present term inside)

#print axioms Attempt.eq_of_raw_eq
#print axioms candidate_output_label
#print axioms candidate_family_complete
#print axioms ProtectedRun.retained_reading_iff

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine
