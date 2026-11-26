import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalStateAdmission
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeNaturalAnnotatedConversionControls
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorJudgmentControls

/-!
# Admission controls at the source-checking / HOL-reading boundary

Literal source certificates admit zero and an annotated identity function.
Changing a binder domain cannot reuse a certificate with the same raw erasure.
A well-typed pair passes the larger source checker but has no reading in the
selected natural predicate fragment.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
namespace AnnotatedConversion.StateAdmission.Controls

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality.Annotated NativeNaturalVectorFamilies
open AnnotatedConversion.Controls Programs.Annotated

def zeroState : State operations profile ⟨[], .nil, .const natName, operations.number⟩ where
  contextFormed := .nil
  term := .const zeroName
  typed := Functions.zero_typed profile
  code := operations.zero
  reading := .zero

def identityState : State operations profile
    ⟨[], .nil, .pi (.const natName) (.const natName), .arr operations.number operations.number⟩ where
  contextFormed := .nil
  term := .lam (.const natName) (.var 0)
  typed := .lamIntro (Functions.natural_typed profile) (.sort _)
    (.piForm (Functions.natural_typed profile) (.sort _) (Functions.natural_typed profile)
      (.sort _) (.sorts _ _)) (.sort _) (.var 0)
  code := .lam (.var .vz)
  reading := .abstraction .natural (.var .vz)

theorem zero_admitted : readState? operations profile [] .nil (.const zeroName) (.const natName)
    .nil (JudgmentReplay.Controls.zero .nil) = some ⟨operations.number, zeroState⟩ :=
  readState?_of_checked zeroState .nil (JudgmentReplay.Controls.zero .nil) rfl (by decide)

theorem identity_admitted : readState? operations profile [] .nil
    (.lam (.const natName) (.var 0)) (.pi (.const natName) (.const natName))
    .nil JudgmentReplay.Controls.identity = some ⟨.arr operations.number operations.number, identityState⟩ :=
  readState?_of_checked identityState .nil JudgmentReplay.Controls.identity rfl JudgmentReplay.Controls.identity_checked

theorem changed_annotation_refused : (readState? operations profile [] .nil
    (.lam (.pi (.const natName) (.const natName)) (.var 0)) (.pi (.const natName) (.const natName))
    .nil JudgmentReplay.Controls.identity).isNone = true := by decide

theorem changed_context_refused : (readState? operations profile [operations.number]
    (.snoc .nil (.pi (.const natName) (.const natName))) (.var 0) (.const natName)
    JudgmentReplay.Controls.naturalContext JudgmentReplay.Controls.identityBody).isNone = true := by decide

/-- Source formation remains usable outside the interpreted fragment. Its
successful source certificate does not grant an unsupported HOL reading. -/
theorem formed_pair_not_read :
    JudgmentReplay.check profile JudgmentReplay.Controls.pair
      (.typing .nil (.pair (.const zeroName) (.const zeroName)) (.sigma (.const natName) (.const natName))) = true ∧
    (readState? operations profile [] .nil (.pair (.const zeroName) (.const zeroName))
      (.sigma (.const natName) (.const natName)) .nil JudgmentReplay.Controls.pair).isNone = true := by
  refine ⟨JudgmentReplay.Controls.pair_checked, ?_⟩
  have emptyContext : JudgmentReplay.checkContext profile .nil .nil = true := rfl
  have rejected : AnnotatedReading.read? operations [] (.pair (.const zeroName) (.const zeroName)) = none := by
    cases AnnotatedReading.read? operations [] (.pair (.const zeroName) (.const zeroName)) with
    | none => rfl
    | some result =>
        obtain ⟨⟨carrier, code⟩, reading⟩ := result
        cases reading
  simp only [readState?, emptyContext, dite_true, rejected]
  rfl

theorem open_row_state_has_certificates :
    ∃ (contextCertificate : JudgmentReplay.ContextCertificate profile operations.parameters.length)
      (typingCertificate : JudgmentReplay.Certificate profile),
      readState? operations profile operations.parameters (Row.zero.context operations)
        zeroInstance.source.term zeroInstance.index.sourceType contextCertificate typingCertificate =
        some ⟨operations.result, zeroInstance.source⟩ := complete zeroInstance.source

#print axioms zero_admitted
#print axioms identity_admitted
#print axioms formed_pair_not_read
#print axioms open_row_state_has_certificates

end AnnotatedConversion.StateAdmission.Controls
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalPredicateReading
