import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Normalization

/-!
# Explicit structural-equivalence decision route

Structural equivalence is decided directly by the independent denotation.
Normalization is separately proved sound for that equivalence.  This module
names the connection explicitly; it does not replace the independent
denotation with equality of executable normal forms.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

def RawCostName.structurallyEquivalentCheck
    (left right : RawCostName) : Bool :=
  decide (left.StructurallyEquivalent right)

def RawCostProc.structurallyEquivalentCheck
    (left right : RawCostProc) : Bool :=
  decide (left.StructurallyEquivalent right)

def RawCostTerm.structurallyEquivalentCheck
    (left right : RawCostTerm) : Bool :=
  decide (left.StructurallyEquivalent right)

@[simp]
theorem RawCostName.structurallyEquivalentCheck_true_iff
    (left right : RawCostName) :
    left.structurallyEquivalentCheck right = true ↔
      left.StructurallyEquivalent right := by
  simp [RawCostName.structurallyEquivalentCheck]

@[simp]
theorem RawCostProc.structurallyEquivalentCheck_true_iff
    (left right : RawCostProc) :
    left.structurallyEquivalentCheck right = true ↔
      left.StructurallyEquivalent right := by
  simp [RawCostProc.structurallyEquivalentCheck]

@[simp]
theorem RawCostTerm.structurallyEquivalentCheck_true_iff
    (left right : RawCostTerm) :
    left.structurallyEquivalentCheck right = true ↔
      left.StructurallyEquivalent right := by
  simp [RawCostTerm.structurallyEquivalentCheck]

/-- Equal executable normal forms are sound evidence of independent name
equivalence. -/
theorem RawCostName.normalize_eq_implies_structurallyEquivalent
    {left right : RawCostName} (equal : left.normalize = right.normalize) :
    left.StructurallyEquivalent right := by
  unfold RawCostName.StructurallyEquivalent
  calc
    left.structuralDenote = left.normalize.structuralDenote :=
      (RawCostName.structuralDenote_normalize left).symm
    _ = right.normalize.structuralDenote := congrArg _ equal
    _ = right.structuralDenote :=
      RawCostName.structuralDenote_normalize right

/-- Equal executable normal forms are sound evidence of independent process
equivalence. -/
theorem RawCostProc.normalize_eq_implies_structurallyEquivalent
    {left right : RawCostProc} (equal : left.normalize = right.normalize) :
    left.StructurallyEquivalent right := by
  unfold RawCostProc.StructurallyEquivalent
  calc
    left.structuralDenote = left.normalize.structuralDenote :=
      (RawCostProc.structuralDenote_normalize left).symm
    _ = right.normalize.structuralDenote := congrArg _ equal
    _ = right.structuralDenote :=
      RawCostProc.structuralDenote_normalize right

/-- Equal executable normal forms are sound evidence of independent term
equivalence. -/
theorem RawCostTerm.normalize_eq_implies_structurallyEquivalent
    {left right : RawCostTerm} (equal : left.normalize = right.normalize) :
    left.StructurallyEquivalent right := by
  unfold RawCostTerm.StructurallyEquivalent
  calc
    left.structuralDenote = left.normalize.structuralDenote :=
      (RawCostTerm.structuralDenote_normalize left).symm
    _ = right.normalize.structuralDenote := congrArg _ equal
    _ = right.structuralDenote :=
      RawCostTerm.structuralDenote_normalize right

private def exampleSigned (atom : String) : RawCostTerm :=
  .signed .nil [atom]

/-- Parallel presentation order is invisible to structural equivalence. -/
example :
    RawCostTerm.structurallyEquivalentCheck
      (.par (exampleSigned "a") (exampleSigned "b"))
      (.par (exampleSigned "b") (exampleSigned "a")) = true := by
  simp [RawCostTerm.structurallyEquivalentCheck,
    RawCostTerm.StructurallyEquivalent, RawCostTerm.structuralDenote,
    RawTermStructuralDenotation.combine]
  constructor <;> ac_rfl

/-- Different spend labels remain structurally distinguishable. -/
example :
    RawCostTerm.nil.structurallyEquivalentCheck (exampleSigned "a") =
      false := by
  simp [RawCostTerm.structurallyEquivalentCheck,
    RawCostTerm.StructurallyEquivalent, exampleSigned,
    RawCostTerm.structuralDenote, RawTermStructuralDenotation.empty]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
