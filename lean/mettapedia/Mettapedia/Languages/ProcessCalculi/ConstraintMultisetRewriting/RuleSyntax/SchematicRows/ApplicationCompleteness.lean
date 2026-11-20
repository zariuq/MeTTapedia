import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationOneStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationProtectedRuns
import Mathlib.Data.Fintype.EquivFin

/-!
# Finitary DTL derivations are realized by actual application runs

The induction keeps both premises in one growing store. After deriving the
major premise, the minor-premise execution preserves it and the entry
hypotheses. The final application is a genuinely admitted solver-produced
attempt. An infinite occurrence supply provides its fresh physical identity;
no fair scheduler or termination of exhaustive saturation is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine

open Mettapedia.Logic.LP
open Presentation.Schematic (Tm rowSig)
open ApplicationSyntax
open ApplicationSemantics (Data Derives hypotheses)

universe uOcc
variable {judgmentTag arrowTag : Nat} {O : Type uOcc} [DecidableEq O]

omit [DecidableEq O] in
theorem hypothesis_occurrence (s : Store O) (source : Subst rowSig) (value : Tm) :
    value ∈ hypotheses (s.dataAt X (b := PUnit.unit) (Subst.id rowSig)) source ↔
      ∃ o ∈ s.present, (s.label o).ReadsAt X (b := PUnit.unit) source value := by
  have law := State.dataAt_model_reading_iff X (b := PUnit.unit) (c := PUnit.unit)
    s (Subst.id rowSig) source value
  change (value ∈ hypotheses (s.dataAt X (b := PUnit.unit) (Subst.id rowSig)) source ↔
    ∃ o ∈ s.present, (s.label o).ReadsAt X (b := PUnit.unit) (source.comp (Subst.id rowSig)) value) at law
  simpa only [Subst.comp_id_right] using law

variable [Infinite O]

theorem derivation_realization {data : Data} {source : Subst rowSig} {value : Tm}
    (derivation : Derives judgmentTag arrowTag data source value) :
    ∀ (current : Store O) (point : Subst rowSig),
      X.Models (a := PUnit.unit) (b := PUnit.unit) point current.knowledge →
      (∀ premise ∈ hypotheses data source,
        premise ∈ hypotheses (current.dataAt X (b := PUnit.unit) (Subst.id rowSig)) point) →
      ∃ execution : ProtectedRun judgmentTag arrowTag current point,
        ∃ o ∈ execution.run.last.present,
          (execution.run.last.label o).ReadsAt X (b := PUnit.unit) execution.source value := by
  induction derivation with
  | hypothesis assumed =>
    intro current point known covers
    obtain ⟨o, present, reading⟩ := (hypothesis_occurrence current point _).mp (covers _ assumed)
    exact ⟨ProtectedRun.start (s := current) (caller := point) known, o, present, reading⟩
  | @apply function argument domain codomain _ _ majorIH minorIH =>
    intro current point known covers
    obtain ⟨majorRun, majorOccurrence, majorPresent, majorReading⟩ := majorIH current point known covers
    have laterCovers : ∀ premise ∈ hypotheses data source,
        premise ∈ hypotheses (majorRun.run.last.dataAt X (b := PUnit.unit) (Subst.id rowSig)) majorRun.source :=
      fun premise assumed => majorRun.preserves_hypotheses premise (covers premise assumed)
    obtain ⟨minorRun, minorOccurrence, minorPresent, minorReading⟩ :=
      minorIH majorRun.run.last majorRun.source majorRun.known laterCovers
    have majorHypothesis : judgment judgmentTag function (arrow arrowTag domain codomain) ∈
        hypotheses (majorRun.run.last.dataAt X (b := PUnit.unit) (Subst.id rowSig)) majorRun.source :=
      (hypothesis_occurrence _ _ _).mpr ⟨majorOccurrence, majorPresent, majorReading⟩
    obtain ⟨retainedMajor, retainedPresent, retainedReading⟩ := (hypothesis_occurrence _ _ _).mp
      (minorRun.preserves_hypotheses _ majorHypothesis)
    obtain ⟨made, madeFresh⟩ := Infinite.exists_notMem_finset minorRun.run.last.present
    obtain ⟨f, admitted, _, resultSource, resultKnown, resultAgrees, madePresent, madeReading⟩ :=
      application_realized judgmentTag arrowTag minorRun.run.last minorRun.source minorRun.known
        retainedMajor minorOccurrence made retainedPresent minorPresent madeFresh
        function argument domain codomain retainedReading minorReading
    let finalRun : ProtectedRun judgmentTag arrowTag minorRun.run.last minorRun.source :=
      ProtectedRun.single f admitted resultSource resultKnown resultAgrees
    refine ⟨majorRun.append (minorRun.append finalRun), made, ?_, ?_⟩
    · rw [ProtectedRun.append_last, ProtectedRun.append_last]
      exact madePresent
    · rw [ProtectedRun.append_last, ProtectedRun.append_last]
      exact madeReading

theorem derives_realized (s : Store O) (source : Subst rowSig)
    (known : X.Models (a := PUnit.unit) (b := PUnit.unit) source s.knowledge)
    {value : Tm}
    (derivation : Derives judgmentTag arrowTag (s.dataAt X (b := PUnit.unit) (Subst.id rowSig)) source value) :
    ∃ execution : ProtectedRun judgmentTag arrowTag s source,
      ∃ o ∈ execution.run.last.present,
        (execution.run.last.label o).ReadsAt X (b := PUnit.unit) execution.source value :=
  derivation_realization derivation s source known (fun _ assumed => assumed)

#print axioms derivation_realization
#print axioms derives_realized

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ApplicationMachine
