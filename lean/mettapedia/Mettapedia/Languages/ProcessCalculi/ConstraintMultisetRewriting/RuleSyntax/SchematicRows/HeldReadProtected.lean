import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadGenericAgreement
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.ProtectedTwoStageCoherence

/-!
# Actual schematic reads as protected two-stage plans

One allocation function supplies the temporary for a logical request; it is
not an extra branching choice. Freshness, distinctness and private helper
access are per-request licences. The realizer derives both actual primitive
admissions from direct admission. Public firings use only the original
extension branch and the stated original ambient program.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadProtected

open Interface (Frames)
open RuleOccurrences HeldReadGenericSources HeldReadGenericFirings

universe uO uT uH uE uOcc uR
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} [DecidableEq O] {R : Type uR} [DecidableEq R]
  (X : Frames Tm Hom) (E : Extensions.{uO, uH, uE} Hom)
  (ambient : Set (HeldReadEncoding.Code Tm))
  (allocate : (ordinary : RuleSyntax.State Tm O) → O → O)

abbrev Native := RState Tm O R (HeldReadEncoding.Code Tm) Unit

inductive Plan : Native (Tm := Tm) (O := O) (R := R) → Type (max uO uT uH uE uOcc uR) where
  | read (ordinary : RuleSyntax.State Tm O) (rows : Finset R)
      (closures : R → Closure Tm ordinary.frame) (selected : R) (extension : E.Ext ordinary.frame)
      (ruleOpening datumOpening : Hom (closures selected).schema.locals (E.target extension)) (output : O)
      (available : Sum.inr (consumeRule (closures selected).schema) ∈ ambient)
      (temporaryFresh : allocate ordinary output ∉ ordinary.present)
      (different : allocate ordinary output ≠ output)
      (admitted : (direct ordinary rows closures selected extension ruleOpening datumOpening output).Admits X) :
      Plan (hosted ordinary rows closures)

noncomputable def realize : {source : Native (Tm := Tm) (O := O) (R := R)} →
    Plan X E ambient allocate source →
      ProtectedTwoStage.Pair (protocolMachine (E := E) (O := O) (R := R) X ambient) source
  | _, .read ordinary rows closures selected extension ruleOpening datumOpening output available fresh different admitted => by
      let stages := stages_of_direct_admitted X ordinary rows closures selected extension
        ruleOpening datumOpening (allocate ordinary output) output ambient available fresh different admitted
      exact ⟨HeldReadExtensionSum.liftHeld X E
          (datum ordinary rows closures selected extension datumOpening (allocate ordinary output)),
        (HeldReadExtensionSum.liftHeld_admission_iff X E ambient _).mpr stages.1,
        HeldReadExtensionSum.liftInternal X E
          (consumer ordinary rows closures selected extension ruleOpening datumOpening X (allocate ordinary output) output),
        (HeldReadExtensionSum.liftInternal_admission_iff X E ambient _).mpr stages.2⟩

def publicAllowed (originalAmbient : Set (HeldReadEncoding.Code Tm))
    {source : Native (Tm := Tm) (O := O) (R := R)}
    (firing : RFiring O R (HeldReadExtensionSum.withIdentity X E) HeldReadEncoding.codes source) : Prop :=
  (∃ extension : E.Ext source.frame, firing.ext = Sum.inl extension) ∧
    match firing.use with
    | .ambient code => code ∈ originalAmbient
    | .held _ => True

variable {Label : Type*}

noncomputable def configuration (originalAmbient : Set (HeldReadEncoding.Code Tm))
    (externalLabel : {source : Native (Tm := Tm) (O := O) (R := R)} →
      RFiring O R (HeldReadExtensionSum.withIdentity X E) HeldReadEncoding.codes source → Label)
    (readLabel : {source : Native (Tm := Tm) (O := O) (R := R)} → Plan X E ambient allocate source → Label) :
    ProtectedTwoStage.Configuration
      (protocolMachine (E := E) (O := O) (R := R) X ambient) (Plan X E ambient allocate) Label where
  realize := realize X E ambient allocate
  publicAllowed := publicAllowed X E originalAmbient
  externalLabel := externalLabel
  protocolLabel := readLabel

theorem realization_is_actual {source : Native (Tm := Tm) (O := O) (R := R)}
    (plan : Plan X E ambient allocate source) :
    ((realize X E ambient allocate plan).run).word.length = 2 :=
  ProtectedTwoStage.Pair.run_length _ _

theorem completion_not_public (originalAmbient : Set (HeldReadEncoding.Code Tm))
    {source : Native (Tm := Tm) (O := O) (R := R)} (plan : Plan X E ambient allocate source) :
    ¬ publicAllowed X E originalAmbient (realize X E ambient allocate plan).second := by
  cases plan with
  | read ordinary rows closures selected extension ruleOpening datumOpening output available fresh different admitted =>
    rintro ⟨⟨oldExtension, impossible⟩, _⟩
    cases impossible

#print axioms realize
#print axioms configuration
#print axioms realization_is_actual
#print axioms completion_not_public

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.HeldReadProtected
