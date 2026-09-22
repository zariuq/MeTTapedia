import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionPaths
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Checking.NativeRelatorConversionChecking

/-!
# Executable path receipts for native conversion

The existing native decoder constructs a proof-retaining symmetric path from
exactly the conversion certificates it accepts. Native relational roots and
their binder contexts retain their actual raw step codes. Re-encoding the path
passes the original checker. Path conversion forgets tree parenthesization and
reflexivity nodes, not the selected edges or their orientation.

The auxiliary parallel joining operation is provided separately by
NativeParallelReceiptPaths. NativeConversionReceiptIngress maps this raw-step
graph into that receipt graph, and NativeConversionComponents computes
Pi/Sigma component certificates. Neither construction asserts a diamond for
authored one-step reduction.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeConversionPaths

open Presentation StructuralConversionCode Quiver

abbrev Vertex (n : Nat) := StepGraph Tower.HeadEq NativeRelatorRootConversionCode.decode n
abbrev Zigzag {n : Nat} (left right : Tower.Tm n) :=
  @Path (Symmetrify (Vertex n)) _ left right

def checkedPath {n : Nat} (code : NativeRelatorConversionChecking.Code n)
    (left right : Tower.Tm n) : Option (Zigzag left right) :=
  if accepted : NativeRelatorConversionChecking.check code left right = true then
    some (code.toZigzag Tower.HeadEq NativeRelatorRootConversionCode.decode (of_decide_eq_true accepted))
  else none

theorem checkedPath_domain {n : Nat} (code : NativeRelatorConversionChecking.Code n)
    (left right : Tower.Tm n) :
    (checkedPath code left right).isSome = NativeRelatorConversionChecking.check code left right := by
  unfold checkedPath
  split <;> simp_all

def encode {n : Nat} {left right : Tower.Tm n} (path : Zigzag left right) :
    NativeRelatorConversionChecking.Code n :=
  zigzagCode Tower.HeadEq NativeRelatorRootConversionCode.decode path

theorem encode_checked {n : Nat} {left right : Tower.Tm n} (path : Zigzag left right) :
    NativeRelatorConversionChecking.check (encode path) left right = true :=
  zigzagCode_checked Tower.HeadEq NativeRelatorRootConversionCode.decode path

namespace Controls

open NativeIndexedFamilies
open NativeRelatorConversionChecking.Examples

def relationalPath : Zigzag (.lam IntrinsicRelator.consIotaLeft) (.lam IntrinsicRelator.consIotaRight) :=
  (StructuralConversionCode.Code.single (.congLam relConsStep)).toZigzag
    Tower.HeadEq NativeRelatorRootConversionCode.decode
    (of_decide_eq_true relational_root_beneath_binder_checked)

theorem relational_path_has_actual_edge :
    relationalPath = .cons .nil (.inl ⟨.congLam relConsStep,
      by rfl⟩) := rfl

theorem relational_path_admitted :
    checkedPath (.single (.congLam relConsStep)) (.lam IntrinsicRelator.consIotaLeft)
      (.lam IntrinsicRelator.consIotaRight) = some relationalPath := by
  simp only [checkedPath, relational_root_beneath_binder_checked, ↓reduceDIte, relationalPath]

def reversedPath : Zigzag IntrinsicRelator.consIotaRight IntrinsicRelator.consIotaLeft :=
  (StructuralConversionCode.Code.symm (.single relConsStep)).toZigzag
    Tower.HeadEq NativeRelatorRootConversionCode.decode
    (of_decide_eq_true symmetric_relator_conversion_checked)

theorem reversed_path_keeps_orientation :
    reversedPath = .cons .nil (.inr ⟨relConsStep,
      by rfl⟩) := by
  simp only [reversedPath, Code.toZigzag, Code.decode, relConsStep, StepCode.decode,
    NativeRelatorRootConversionCode.Examples.relConsCode, NativeRelatorRootConversionCode.decode]
  rfl

theorem reversed_path_rechecks :
    NativeRelatorConversionChecking.check (encode reversedPath)
      IntrinsicRelator.consIotaRight IntrinsicRelator.consIotaLeft = true := encode_checked reversedPath

/-- A successful root step followed by its reverse is still two selected
steps, even though the source and target terms are identical. -/
def cancellationCode : NativeRelatorConversionChecking.Code 12 :=
  .trans (.single relConsStep) (.symm (.single relConsStep))

theorem cancellation_checked :
    NativeRelatorConversionChecking.check cancellationCode
      IntrinsicRelator.consIotaLeft IntrinsicRelator.consIotaLeft = true :=
  Code.check_trans Tower.HeadEq NativeRelatorRootConversionCode.decode relator_step_checked
    (Code.check_symm Tower.HeadEq NativeRelatorRootConversionCode.decode relator_step_checked)

def cancellationPath : Zigzag IntrinsicRelator.consIotaLeft IntrinsicRelator.consIotaLeft :=
  cancellationCode.toZigzag Tower.HeadEq NativeRelatorRootConversionCode.decode
    (of_decide_eq_true cancellation_checked)

theorem cancellation_retains_both_steps : cancellationPath.length = 2 :=
  Code.toZigzag_length Tower.HeadEq NativeRelatorRootConversionCode.decode cancellationCode
    (left := IntrinsicRelator.consIotaLeft) (right := IntrinsicRelator.consIotaLeft)
    (of_decide_eq_true cancellation_checked)

theorem cancellation_is_not_empty : cancellationPath ≠ .nil := by
  intro equal
  have lengths := congrArg Quiver.Path.length equal
  have impossible : 2 = 0 := cancellation_retains_both_steps.symm.trans lengths
  cases impossible

theorem mismatched_join_rejected :
    (checkedPath brokenJoin (.head firstHead) (.head secondHead)).isNone = true := by decide +kernel

theorem captured_endpoint_rejected :
    (checkedPath (.single beneathBinder) beneathBinderSource (.lam (.var 0))).isNone = true := by
  decide +kernel

theorem reflexivity_grouping_forgotten :
    checkedPath (.refl (ground : Tower.Tm 0)) ground ground =
      checkedPath (.trans (.refl ground) (.refl ground)) ground ground := by rfl

theorem source_trees_still_distinct :
    (StructuralConversionCode.Code.refl (ground : Tower.Tm 0) : NativeRelatorConversionChecking.Code 0) ≠
      .trans (.refl ground) (.refl ground) := by intro equal; cases equal

end Controls

#print axioms checkedPath_domain
#print axioms encode_checked
#print axioms Controls.relational_path_has_actual_edge
#print axioms Controls.relational_path_admitted
#print axioms Controls.reversed_path_keeps_orientation
#print axioms Controls.reversed_path_rechecks
#print axioms Controls.cancellation_checked
#print axioms Controls.cancellation_retains_both_steps
#print axioms Controls.cancellation_is_not_empty
#print axioms Controls.mismatched_join_rejected
#print axioms Controls.captured_endpoint_rejected
#print axioms Controls.reflexivity_grouping_forgotten
#print axioms Controls.source_trees_still_distinct

#eval (Controls.relationalPath.length, Controls.reversedPath.length, Controls.cancellationPath.length)

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeConversionPaths
