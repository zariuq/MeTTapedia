import Mettapedia.Languages.MM0.Presentation.AdmissibleCorrespondence
import Mettapedia.Languages.MM0.Presentation.SubstitutionCorrespondence
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.HostExtension

/-!
# Authored admissible MM0 term instantiation

The operation checks admissibility and then reuses the established simultaneous
substitution equations. The two existing list encodings are connected by an
authored structural traversal, preserving replacement order and values. Neither
the admission decision nor term substitution is delegated to a host primitive.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Presentation.ComputationalInstantiation

open Kernel ComputationalContext ComputationalArguments ComputationalTyping
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

private def c (head : String) (arguments : List Term) : Term := .expr (.sym head :: arguments)
private def v (name : String) : Term := .var name

def instantiationEquations : Program := [
  ⟨"substitution-values", "mm0:substitution-values", [v "values"],
    c "mm0:substitution-values-view" [c "nik:list-view" [v "values"]]⟩,
  ⟨"substitution-values-empty", "mm0:substitution-values-view", [.sym "List:Nil"], .sym "LNil"⟩,
  ⟨"substitution-values-cons", "mm0:substitution-values-view",
    [c "List:Cons" [v "first", v "rest"]],
    c "LCons" [v "first", c "mm0:substitution-values" [v "rest"]]⟩,
  ⟨"instantiate-term", "mm0:instantiate-term",
    [v "table", v "formal", v "target", v "expressions", v "body"],
    c "mm0:instantiation-admitted" [c "mm0:check-admissible"
      [v "table", v "formal", v "target", v "expressions"], v "body", v "expressions"]⟩,
  ⟨"instantiate-refuses", "mm0:instantiation-admitted", [.sym "False", v "body", v "expressions"], .sym "None"⟩,
  ⟨"instantiate-admitted", "mm0:instantiation-admitted", [.sym "True", v "body", v "expressions"],
    c "mm0:subst" [v "body", c "mm0:substitution-values" [v "expressions"]]⟩]

def instantiationProgram : Program := ComputationalAdmissible.admissibleProgram ++
  (substitutionProgram ++ instantiationEquations)

theorem instantiationProgram_leftLinear : LeftLinear instantiationProgram := by
  simp only [instantiationProgram, LeftLinear, List.mem_append, or_imp, forall_and]
  refine ⟨ComputationalAdmissible.admissibleProgram_leftLinear, substitutionProgram_leftLinear, ?_⟩
  simp [instantiationEquations, c, v, patternVarsList, patternVars]

theorem instantiationProgram_dataSeparated : DataSeparated instantiationProgram computationalHost where
  undefined := by
    intro head member
    have prior := ComputationalAdmissible.admissibleProgram_dataSeparated.undefined head member
    have replacement := substitutionProgram_dataSeparated.undefined head member
    simp only [instantiationProgram, Program.defines, List.any_append]
    change (ComputationalAdmissible.admissibleProgram.defines head ||
      (substitutionProgram.defines head || instantiationEquations.defines head)) = false
    rw [prior, replacement]
    simp only [constructorHeads, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> rfl
  unhandled := ComputationalAdmissible.admissibleProgram_dataSeparated.unhandled

theorem substitution_host_agreement : naturalHost.AgreesOn computationalHost substitutionProgram.calledHeads := by
  intro head used arguments
  have catalogue : ∀ name ∈ substitutionProgram.calledHeads, name ∈
      ["mm0:subst", "mm0:lookup", "Some", "MM0:Term", "mm0:subst-function", "mm0:subst-argument",
        "MM0:App", "mm0:lookup-zero", "nik:nat-zero", "nik:nat-pred"] := by decide
  have cases' := catalogue head used
  simp only [List.mem_cons, List.not_mem_nil, or_false] at cases'
  rcases cases' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem substitution_reused (body : Preterm) (expressions : List Preterm) :
    Applies instantiationProgram computationalHost "mm0:subst" [encode body, encodeValues expressions]
      (encodeResult (body.substitute (Substitution.ofList expressions))) := by
  have host := (Applies.host_iff substitutionProgram substitution_host_agreement
    "mm0:subst" (by decide) _ _).mp (substitution_computes body expressions)
  exact (Applies.frame_iff substitutionProgram ComputationalAdmissible.admissibleProgram instantiationEquations
    computationalHost (by decide) (by decide) "mm0:subst" (by decide) _ _).mpr host

theorem admissible_reused (table : SignatureTable) (formal target : Context) (expressions : List Preterm) :
    Applies instantiationProgram computationalHost "mm0:check-admissible"
      [encodeTable table, encodeContext formal, encodeContext target, encodeExpressions expressions]
      (boolean (Substitution.checkAdmissible (signatureOf table) formal target expressions)) := by
  exact (Applies.append_iff ComputationalAdmissible.admissibleProgram (substitutionProgram ++ instantiationEquations)
    computationalHost (by decide) "mm0:check-admissible" (by decide) _ _).mpr
      (ComputationalAdmissible.admissible_computes table formal target expressions)

end Mettapedia.Languages.MM0.Presentation.ComputationalInstantiation
