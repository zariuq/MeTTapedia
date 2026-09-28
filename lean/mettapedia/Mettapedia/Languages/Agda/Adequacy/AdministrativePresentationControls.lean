import Mettapedia.Languages.Agda.Adequacy.AdministrativePresentationPreservation
import Mettapedia.Languages.Agda.Adequacy.AdministrativeBetaControls

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy.AdministrativePreservation.Controls

open Mettapedia.OSLF.Binding
open Structural
open Structural.Statics (RawTm RawTy RawContext)
open Structural.AdministrativeStatics
open BinderPreservationControls

def convertedBetaStep : Step
    (eliminate (lam (.var .zero)) (cons (apply administrativeArgument) nil))
    (eliminate administrativeArgument nil) :=
  .root (Root.beta (.var .zero) administrativeArgument nil)

noncomputable def convertedBetaTree : ComputationTree
    (eliminate (lam (.var .zero)) (cons (apply administrativeArgument) nil))
    (eliminate administrativeArgument nil) := stepToTree convertedBetaStep

noncomputable def convertedTreeEquality : CoreDerivation
    (Statics.termEqual empty (eliminate (lam (.var .zero)) (cons (apply administrativeArgument) nil))
      (eliminate administrativeArgument nil) PreservationControls.expandedUniverse) :=
  treeTermEquality convertedBetaTree convertedSource

noncomputable def convertedPath : ComputationPath
    (eliminate (lam (.var .zero)) (cons (apply administrativeArgument) nil)) administrativeArgument := by
  letI := IntrinsicScopedLocalPolynomial.derivationQuiver Authored.computationRules Authored.algebra
    (scope 0) Srt.term
  exact .cons (.cons .nil convertedBetaTree) (stepToTree (.root (Root.eliminateEmpty administrativeArgument)))

theorem converted_path_has_two_edges :
    IntrinsicScopedLocalPolynomial.pathLength Authored.computationRules Authored.algebra convertedPath = 2 := rfl

noncomputable def convertedPathEquality : CoreDerivation
    (Statics.termEqual empty (eliminate (lam (.var .zero)) (cons (apply administrativeArgument) nil))
      administrativeArgument PreservationControls.expandedUniverse) :=
  pathTermEquality convertedPath convertedSource

noncomputable def convertedPathTarget : CoreDerivation
    (Statics.typed empty administrativeArgument PreservationControls.expandedUniverse) :=
  pathTermPreservation convertedPath convertedSource

abbrev overlapSource : RawTm 0 := eliminate administrativeArgument nil
abbrev overlapTarget : RawTm 0 := administrativeArgument

def outerOccurrence : Step overlapSource overlapTarget := .root (Root.eliminateEmpty administrativeArgument)

def innerOccurrence : Step overlapSource overlapTarget :=
  CompatibleDerivations.Step.congr (R := Root) Op.eliminate
    (.head (.cons nil .nil) (.root (Root.eliminateEmpty (Statics.universeTerm 0))))

noncomputable def overlapTyped : CoreDerivation (Statics.typed empty overlapSource domain.code) :=
  Derivation.elimination PreservationControls.administrativeArgument (Derivation.nil empty domain.code)

noncomputable def outerCertificate := termCertificate outerOccurrence
noncomputable def innerCertificate := termCertificate innerOccurrence

noncomputable def outerTyped : CoreDerivation (Statics.typed empty overlapTarget domain.code) :=
  outerCertificate.typing overlapTyped

noncomputable def innerTyped : CoreDerivation (Statics.typed empty overlapTarget domain.code) :=
  innerCertificate.typing overlapTyped

theorem certificates_retain_distinct_occurrences : outerCertificate ≠ innerCertificate := by
  intro same
  have heights := congrArg (fun certificate : Preservation.TermCertificate overlapSource overlapTarget =>
    CompatibleDerivations.height certificate.step) same
  cases heights

theorem table_histories_retain_distinct_occurrences : stepToTree outerOccurrence ≠ stepToTree innerOccurrence := by
  intro same
  have steps := (treeToStep_stepToTree outerOccurrence).symm.trans
    ((congrArg (fun tree : ComputationTree overlapSource overlapTarget => treeToStep tree) same).trans
      (treeToStep_stepToTree innerOccurrence))
  have heights := congrArg CompatibleDerivations.height steps
  cases heights

noncomputable def malformedNil : Action empty Structural.AdministrativeStatics.Controls.unsupportedType nil
    Structural.AdministrativeStatics.Controls.unsupportedType := Derivation.nil empty _

noncomputable def malformedAppend : Action empty Structural.AdministrativeStatics.Controls.unsupportedType
    (append nil nil) Structural.AdministrativeStatics.Controls.unsupportedType :=
  Derivation.append malformedNil malformedNil

noncomputable def malformedSpineEquation : SpineEq empty Structural.AdministrativeStatics.Controls.unsupportedType
    (append nil nil) nil Structural.AdministrativeStatics.Controls.unsupportedType :=
  spineEquality (.root (Root.appendEmpty nil)) malformedAppend

theorem conditional_spine_equality_does_not_form_input :
    ¬ Nonempty (CoreDerivation (Statics.formed empty Structural.AdministrativeStatics.Controls.unsupportedType)) :=
  Structural.AdministrativeStatics.Controls.unsupported_type_unformed

end Mettapedia.Languages.Agda.StaticAdequacy.AdministrativePreservation.Controls
