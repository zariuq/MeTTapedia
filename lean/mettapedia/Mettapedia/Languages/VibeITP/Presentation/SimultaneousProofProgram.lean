import Mettapedia.Languages.VibeITP.Presentation.ProofCorrespondence
import Mettapedia.Languages.VibeITP.Presentation.SimultaneousTraversal
import Mettapedia.Languages.VibeITP.Presentation.SimultaneousProofs
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ProgramInsertion

/-! Whole supplied v2 proofs as ordinary equations. The existing static proof
checker and simultaneous operation are shared components. New nodes retain
their actual children and replacements. Existing dispatch and every execution
outcome are preserved at the same fuel. -/

set_option autoImplicit false
namespace Mettapedia.Languages.VibeITP.Presentation.ComputationalProofsV2

open ComputationalData ComputationalShift ComputationalInference ComputationalLiterals ComputationalDefinitions
open ComputationalProofs ComputationalSimultaneous
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

def encodeWitness : SimultaneousProofs.Witness → Term
  | .base original => .list [.sym "Proof2:Base", ComputationalProofs.encodeWitness original]
  | .modusPonens implication premise =>
      .list [.sym "Proof2:MP", encodeWitness implication, encodeWitness premise]
  | .instantiateMany replacements child =>
      .list [.sym "Proof2:Many", encodeReplacements replacements, encodeWitness child]

private def call (head : String) (arguments : List Term) : Term := .expr (.sym head :: arguments)
private def slot (name : String) : Term := .var name
private def someResult (value : Term) : Term := call "Some" [value]
private def equation (name head : String) (arguments : List Term) (body : Term) : Equation :=
  ⟨name, head, arguments, body⟩

def proofEquationsV2 : Program := [
  equation "proof2-base" "vibe:proof-v2-query"
    [slot "table", slot "axioms", slot "definitions", .list [.sym "Proof2:Base", slot "original"]]
    (call "vibe:proof-query" [slot "table", slot "axioms", slot "definitions", slot "original"]),
  equation "proof2-mp" "vibe:proof-v2-query"
    [slot "table", slot "axioms", slot "definitions", .list [.sym "Proof2:MP", slot "implication", slot "premise"]]
    (call "vibe:proof-v2-mp-first" [
      call "vibe:proof-v2-query" [slot "table", slot "axioms", slot "definitions", slot "implication"],
      slot "table", slot "axioms", slot "definitions", slot "premise"]),
  equation "proof2-mp-missing-implication" "vibe:proof-v2-mp-first"
    [.sym "None", slot "table", slot "axioms", slot "definitions", slot "premise"] (.sym "None"),
  equation "proof2-mp-implication" "vibe:proof-v2-mp-first"
    [someResult (slot "implication"), slot "table", slot "axioms", slot "definitions", slot "premise"]
    (call "vibe:proof-v2-mp-second" [slot "implication",
      call "vibe:proof-v2-query" [slot "table", slot "axioms", slot "definitions", slot "premise"]]),
  equation "proof2-mp-missing-premise" "vibe:proof-v2-mp-second" [slot "implication", .sym "None"] (.sym "None"),
  equation "proof2-mp-premise" "vibe:proof-v2-mp-second" [slot "implication", someResult (slot "premise")]
    (call "vibe:modus-ponens" [slot "implication", slot "premise"]),
  equation "proof2-many" "vibe:proof-v2-query"
    [slot "table", slot "axioms", slot "definitions", .list [.sym "Proof2:Many", slot "replacements", slot "child"]]
    (call "vibe:proof-v2-many-child" [
      call "vibe:proof-v2-query" [slot "table", slot "axioms", slot "definitions", slot "child"],
      slot "table", slot "replacements"]),
  equation "proof2-many-missing-child" "vibe:proof-v2-many-child"
    [.sym "None", slot "table", slot "replacements"] (.sym "None"),
  equation "proof2-many-child" "vibe:proof-v2-many-child"
    [someResult (slot "statement"), slot "table", slot "replacements"]
    (call "vibe:thm-instantiate-many" [slot "table", slot "replacements", slot "statement"]),
  equation "proof2-unknown" "vibe:proof-v2-query"
    [slot "table", slot "axioms", slot "definitions", slot "unknown"] (.sym "None"),
  equation "proof2-check" "vibe:check-proof-v2"
    [slot "table", slot "axioms", slot "definitions", slot "witness", slot "claimed"]
    (call "vibe:proof-v2-check-result" [
      call "vibe:proof-v2-query" [slot "table", slot "axioms", slot "definitions", slot "witness"], slot "claimed"]),
  equation "proof2-check-refused" "vibe:proof-v2-check-result" [.sym "None", slot "claimed"] (.sym "False"),
  equation "proof2-check-computed" "vibe:proof-v2-check-result" [someResult (slot "actual"), slot "claimed"]
    (call "vibe:term-eq" [slot "actual", slot "claimed"]) ]

def coreProgram : Program := proofProgram ++ simultaneousEquations
def wholeProgram : Program := coreProgram ++ proofEquationsV2

private def inserted : Program := literalEquations ++ definitionEquations ++ proofEquations

theorem coreProgram_eq_inserted :
    coreProgram = inferenceProgram ++ inserted ++ simultaneousEquations := by
  simp only [coreProgram, proofProgram, definitionProgram, literalProgram, inserted, List.append_assoc]

theorem many_disjoint : ∀ equation ∈ simultaneousEquations, equation.head ∉ proofProgram.calledHeads := by
  have checked : simultaneousEquations.all (fun equation =>
      decide (equation.head ∉ proofProgram.calledHeads)) = true := by decide +kernel
  exact fun equation member => of_decide_eq_true (List.all_eq_true.mp checked equation member)

theorem inserted_disjoint : ∀ equation ∈ inserted, equation.head ∉ simultaneousProgram.calledHeads := by
  have checked : inserted.all (fun equation =>
      decide (equation.head ∉ simultaneousProgram.calledHeads)) = true := by decide +kernel
  exact fun equation member => of_decide_eq_true (List.all_eq_true.mp checked equation member)

theorem new_disjoint : ∀ equation ∈ proofEquationsV2, equation.head ∉ coreProgram.calledHeads := by
  have checked : proofEquationsV2.all (fun equation =>
      decide (equation.head ∉ coreProgram.calledHeads)) = true := by decide +kernel
  exact fun equation member => of_decide_eq_true (List.all_eq_true.mp checked equation member)

theorem simultaneous_host_agreement :
    computationalHost.AgreesOn productDivisionHost simultaneousProgram.calledHeads := by
  apply productDivisionHost_agrees
  decide +kernel

theorem coreProgram_leftLinear : LeftLinear coreProgram := by
  intro equation member
  rcases List.mem_append.mp member with original | many
  · exact proofProgram_leftLinear equation original
  · exact simultaneousProgram_leftLinear equation (List.mem_append_right _ many)

theorem wholeProgram_leftLinear : LeftLinear wholeProgram := by
  have added : LeftLinear proofEquationsV2 := by
    simp [LeftLinear, proofEquationsV2, equation, call, slot, someResult, patternVarsList, patternVars]
  intro equation member
  rcases List.mem_append.mp member with original | fresh
  · exact coreProgram_leftLinear equation original
  · exact added equation fresh

theorem wholeProgram_dataSeparated : DataSeparated wholeProgram productDivisionHost where
  undefined := by
    intro head member
    have old := proofProgram_dataSeparated.undefined head member
    have many : simultaneousEquations.defines head = false := by
      simp [constructorHeads] at member
      rcases member with rfl | rfl | rfl <;> decide +kernel
    have added : proofEquationsV2.defines head = false := by
      simp [constructorHeads] at member
      rcases member with rfl | rfl | rfl <;> decide +kernel
    change ((proofProgram ++ simultaneousEquations) ++ proofEquationsV2).any _ = false
    simp only [List.any_append]
    change ((proofProgram.defines head || simultaneousEquations.defines head) || proofEquationsV2.defines head) = false
    rw [old, many, added]
    rfl
  unhandled := proofProgram_dataSeparated.unhandled

theorem old_proof_execution (fuel : Nat) (head : String) (used : head ∈ proofProgram.calledHeads)
    (arguments : List Term) :
    apply wholeProgram productDivisionHost fuel head arguments =
      apply proofProgram productDivisionHost fuel head arguments := by
  have coreUsed : head ∈ coreProgram.calledHeads := by
    simp only [coreProgram, Program.calledHeads, List.flatMap_append, List.mem_append] at used ⊢
    exact Or.inl used
  rw [wholeProgram, apply_append_eq coreProgram proofEquationsV2 productDivisionHost new_disjoint fuel head coreUsed,
    coreProgram,
    apply_append_eq proofProgram simultaneousEquations productDivisionHost many_disjoint fuel head used]

theorem reuse_proof_call {head : String} {arguments : List Term} {result : Term}
    (used : head ∈ proofProgram.calledHeads)
    (computed : Applies proofProgram productDivisionHost head arguments result) :
    Applies wholeProgram productDivisionHost head arguments result := by
  obtain ⟨fuel, accepted⟩ := computed
  exact ⟨fuel, by rw [old_proof_execution fuel head used]; exact accepted⟩

theorem old_simultaneous_execution (fuel : Nat) (head : String)
    (used : head ∈ simultaneousProgram.calledHeads) (arguments : List Term) :
    apply wholeProgram productDivisionHost fuel head arguments =
      apply simultaneousProgram computationalHost fuel head arguments := by
  have coreUsed : head ∈ coreProgram.calledHeads := by
    simp only [coreProgram_eq_inserted, simultaneousProgram, Program.calledHeads,
      List.flatMap_append, List.mem_append] at used ⊢
    tauto
  rw [wholeProgram, apply_append_eq coreProgram proofEquationsV2 productDivisionHost new_disjoint fuel head coreUsed,
    coreProgram_eq_inserted,
    apply_insert_eq inferenceProgram simultaneousEquations inserted productDivisionHost inserted_disjoint
      fuel head used]
  exact (apply_host_eq simultaneousProgram simultaneous_host_agreement fuel head used arguments).symm

theorem reuse_simultaneous_call {head : String} {arguments : List Term} {result : Term}
    (used : head ∈ simultaneousProgram.calledHeads)
    (computed : Applies simultaneousProgram computationalHost head arguments result) :
    Applies wholeProgram productDivisionHost head arguments result := by
  obtain ⟨fuel, accepted⟩ := computed
  exact ⟨fuel, by rw [old_simultaneous_execution fuel head used]; exact accepted⟩

theorem whole_equation {head : String} {arguments : List Term} {equation : Equation}
    {environment : Env} {result : Term} (used : head ∈ proofEquationsV2.map Equation.head)
    (defined : proofEquationsV2.definesAt head arguments.length = true)
    (selected : proofEquationsV2.select head arguments = some (equation, environment))
    (body : Evaluates wholeProgram productDivisionHost environment equation.body result) :
    Applies wholeProgram productDivisionHost head arguments result :=
  Applies.suffix_equation new_disjoint used defined selected body

theorem whole_apply (head : String) (used : head ∈ proofEquationsV2.map Equation.head)
    (fuel : Nat) (arguments : List Term) :
    apply wholeProgram productDivisionHost fuel head arguments =
      applyWith proofEquationsV2 productDivisionHost (eval wholeProgram productDivisionHost fuel) head arguments :=
  apply_suffix_eq coreProgram proofEquationsV2 productDivisionHost new_disjoint head used fuel arguments

end Mettapedia.Languages.VibeITP.Presentation.ComputationalProofsV2
