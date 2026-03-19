import Mettapedia.Logic.HOL.OriginalReflectionReduction

namespace Mettapedia.Logic.HOL

universe u

namespace HenkinConstInfinity

/-!
# Original Reflection Obstruction

This file certifies the concrete obstruction discovered in the current
original-signature reflection program.

If the original signature has no constants at a base type, the cumulative
Henkin signature still introduces fresh witness constants. As a result, the
cumulative language can prove some existential sentences that the source
semantics may still falsify when empty admissible base domains are allowed.
-/

/-- The empty source signature, indexed by HOL simple types over `Unit`. -/
abbrev EmptyConst : Ty Unit → Type := fun _ => PEmpty

/-- The distinguished base type used in the obstruction witness. -/
abbrev obstructionBaseTy : Ty Unit := .base ()

/-- The source-language sentence `∃ x : b, ⊤` over the empty signature. -/
def emptySignatureExistsTop : ClosedFormula EmptyConst :=
  .ex (.top : Formula EmptyConst [obstructionBaseTy])

/-- Its direct lifted form in the cumulative Henkin signature. -/
def emptySignatureExistsTopLifted : ClosedFormula (HInf Unit EmptyConst) :=
  .ex (.top : Formula (HInf Unit EmptyConst) [obstructionBaseTy])

@[simp] theorem liftBaseClosedFormula_emptySignatureExistsTop :
    liftBaseClosedFormula (Base := Unit) (Const := EmptyConst)
      emptySignatureExistsTop =
        emptySignatureExistsTopLifted := rfl

/--
In the cumulative Henkin language, the empty-signature sentence `∃ x : b, ⊤`
is already provable outright, because the cumulative signature contains a fresh
witness constant for the stage-`0` formula `⊤ : [b]`.
-/
theorem emptySignature_hInf_theorem_existsTop :
    ExtDerivation.Theorem
      (HInf Unit EmptyConst)
      emptySignatureExistsTopLifted := by
  refine ExtDerivation.exI ?_ ?_
  · exact
      .const
        (.exWitness
          (n := 0)
          (.top :
            Formula (HenkinConstStage Unit EmptyConst 0) [obstructionBaseTy]))
  · simpa [emptySignatureExistsTopLifted] using
      (ExtDerivation.topI :
        ExtDerivation (HInf Unit EmptyConst) [] (.top : ClosedFormula (HInf Unit EmptyConst)))

/--
The obstruction expressed at the exact bridge interface:

even with no original assumptions, the lifted empty-signature sentence
`∃ x : b, ⊤` is `OriginalLiftProvable` in the cumulative Henkin language.
-/
theorem emptySignature_originalLiftProvable_existsTop :
    OriginalLiftProvable
      (Base := Unit)
      (Const := EmptyConst)
      []
      emptySignatureExistsTop := by
  exact
    ClosedTheorySet.provable_of_closedTheory
      (Const := HInf Unit EmptyConst)
      (T := fun ψ =>
        ψ ∈ ([] : List (ClosedFormula EmptyConst)).map
            (liftBaseClosedFormula (Base := Unit) (Const := EmptyConst)) ∨
          ψ ∈ HenkinAxioms (Base := Unit) (Const := EmptyConst))
      (Δ := [])
      (hΔ := by
        intro ψ hψ
        cases hψ)
      (hφ := by
        rw [liftBaseClosedFormula_emptySignatureExistsTop]
        exact emptySignature_hInf_theorem_existsTop)

end HenkinConstInfinity

end Mettapedia.Logic.HOL
