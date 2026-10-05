import Mettapedia.Languages.MM0.Kernel.ProofChecking
import Mettapedia.Languages.MM0.Presentation.ConversionCorrespondence

/-!
# MM0 supplied proofs and theorem declarations as data

The theorem store is an input to checking. Entries retain their formal
context, ordered hypotheses and conclusion. Admission of that store is a
separate operation; lookup never adds the requested conclusion to it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalProof

open Kernel ComputationalContext ComputationalArguments
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

abbrev TheoremTable := List (Nat × TheoremDecl)

def theoremsOf (table : TheoremTable) : TheoremSignature := fun index => table.lookup index

def encodeTheorem (declaration : TheoremDecl) : Term :=
  .list [.sym "MM0:Theorem", encodeContext declaration.arguments,
    encodeExpressions declaration.hypotheses, encode declaration.conclusion]

def encodeTheorems (table : TheoremTable) : Term := encodeNaturalTable encodeTheorem table

def encodeProof : ProofWitness → Term
  | .hyp index => .list [.sym "MM0:Hyp", natural index]
  | .theoremApp index arguments children =>
      .list [.sym "MM0:TheoremApp", natural index, encodeExpressions arguments,
        .list (children.map encodeProof)]
  | .conversion witness child =>
      .list [.sym "MM0:Conversion", ComputationalConversion.encodeWitness witness, encodeProof child]
termination_by witness => sizeOf witness

def encodeProofs (children : List ProofWitness) : Term := .list (children.map encodeProof)

def encodeResults : Option (List Preterm) → Term
  | none => .sym "None"
  | some expressions => .expr [.sym "MM0:Expressions", encodeExpressions expressions]

def encodeInstance : Option TheoremInstance → Term
  | none => .sym "None"
  | some instantiation => .expr [.sym "MM0:Instance", encodeExpressions instantiation.hypotheses,
      encode instantiation.conclusion]

theorem encodeResults_injective : Function.Injective encodeResults := by
  intro left right same
  cases left with
  | none => cases right <;> simp_all [encodeResults]
  | some left =>
      cases right with
      | none => simp [encodeResults] at same
      | some right =>
          simp only [encodeResults, Term.expr.injEq, List.cons.injEq, true_and, and_true] at same
          exact congrArg some (ComputationalConversion.encodeExpressions_injective same)

theorem encodeInstance_injective : Function.Injective encodeInstance := by
  intro left right same
  cases left with
  | none => cases right <;> simp_all [encodeInstance]
  | some left =>
      cases right with
      | none => simp [encodeInstance] at same
      | some right =>
          simp only [encodeInstance, Term.expr.injEq, List.cons.injEq, true_and, and_true] at same
          have premises := ComputationalConversion.encodeExpressions_injective same.1
          have conclusion := encode_injective same.2
          cases left; cases right
          simp_all

end Mettapedia.Languages.MM0.Presentation.ComputationalProof
