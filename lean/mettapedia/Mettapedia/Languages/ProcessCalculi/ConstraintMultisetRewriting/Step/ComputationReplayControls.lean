import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationReplay
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationControls

/-!
# Original ordinals and malformed replay submissions

Two copies of the actual vector-equation table have the same logical rules.
The addition row at ordinal seven and its copy at ordinal twenty-one produce
the same full-step firing, while their retained codes differ. Bounds, arity
and source mismatches are rejected. These root-only checks do not consult
the head-equality policy; no arbitrary-head decidability claim follows.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationReplay.Controls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization
open AlgebraicSchema
open NativeTypesOnTheStep.Computing
open TowerVectorsModel (zeroC addC)

abbrev initial := ComputationProfile.Controls.start
abbrev q := ComputationProfile.Controls.qualified
abbrev p := ComputationProfile.Controls.presentation
abbrev setting := ComputationProfile.Controls.setting

local instance headPolicy : DecidableRel setting.R.headEq := Classical.decRel _

def doubled : SchemaTable Tower.Head := Vectors.vectorEquations ++ Vectors.vectorEquations

theorem doubled_same {arity : Nat} (left right : Tower.Tm arity) : p.schema left right ↔ doubled.family left right := by
  change (⟨arity, left, right⟩ : Σ a : Nat, Tower.Tm a × Tower.Tm a) ∈ Vectors.vectorEquations ↔
    (⟨arity, left, right⟩ : Σ a : Nat, Tower.Tm a × Tower.Tm a) ∈ Vectors.vectorEquations ++ Vectors.vectorEquations
  simp only [List.mem_append, or_self]

def firstCode : Code (Head := Tower.Head) 0 := .root ⟨7, [addC zeroC zeroC]⟩
def copiedCode : Code (Head := Tower.Head) 0 := .root ⟨21, [addC zeroC zeroC]⟩
def outOfBounds : Code (Head := Tower.Head) 0 := .root ⟨28, [addC zeroC zeroC]⟩
def wrongArity : Code (Head := Tower.Head) 0 := .root ⟨7, []⟩
def wrongSource : Code (Head := Tower.Head) 0 := .root ⟨7, [zeroC]⟩

theorem first_accepted : (read? p doubled doubled_same initial firstCode).isSome = true := by decide +kernel
theorem copy_accepted : (read? p doubled doubled_same initial copiedCode).isSome = true := by decide +kernel
theorem bound_refused : (read? p doubled doubled_same initial outOfBounds).isSome = false := by decide +kernel
theorem arity_refused : (read? p doubled doubled_same initial wrongArity).isSome = false := by decide +kernel
theorem source_refused : (read? p doubled doubled_same initial wrongSource).isSome = false := by decide +kernel

def first : Submission p doubled doubled_same initial :=
  (read? p doubled doubled_same initial firstCode).get (by rw [first_accepted])

def copied : Submission p doubled doubled_same initial :=
  (read? p doubled doubled_same initial copiedCode).get (by rw [copy_accepted])

def row {n : Nat} : Code (Head := Tower.Head) n → Nat
  | .root code => code.row
  | _ => 0

theorem code_origins_differ : first.code ≠ copied.code := by
  intro equal
  have impossible : (7 : Nat) = 21 := congrArg row equal
  omega

theorem native_effects_agree : first.instruction.compile q 1 = copied.instruction.compile q 1 := rfl

theorem original_row_admitted :
    (DependentFull.step setting.levels Nat).Admits (first.instruction.compile q 1) :=
  (first.instruction.admitted_iff q 1).mpr ComputationProfile.Controls.one_fresh

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationReplay.Controls

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationReplay.Controls.code_origins_differ
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationReplay.Controls.native_effects_agree
