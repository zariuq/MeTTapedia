import Mettapedia.GSLT.LanguageDef.DeterministicEquations.InstantiationAdmissibilityExtraction

/-! # Actual MM0 theorem instantiation through extracted dependencies

Declaration codecs retain the ordered premises and conclusion. The admission,
substitution and result construction are extracted from the existing kernel.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Instantiation

open Mettapedia.Languages
open MM0.Presentation.ComputationalContext

def encodeTheoremDecl (declaration : MM0.Kernel.TheoremDecl) : Term :=
  .list [.sym "MM0:Theorem", encodeList encodeBinder declaration.arguments,
    encodeList MM0.Presentation.encode declaration.hypotheses,
    MM0.Presentation.encode declaration.conclusion]

theorem encodeTheoremDecl_injective : Function.Injective encodeTheoremDecl := by
  intro left right same
  simp only [encodeTheoremDecl, Term.list.injEq, List.cons.injEq, true_and, and_true] at same
  have arguments := encodeList_injective encodeBinder_injective same.1
  have hypotheses := encodeList_injective MM0.Presentation.encode_injective same.2.1
  have conclusion := MM0.Presentation.encode_injective same.2.2
  cases left; cases right
  simp_all

def encodeTheoremInstance (instanceValue : MM0.Kernel.TheoremInstance) : Term :=
  .list [.sym "MM0:Instance", encodeList MM0.Presentation.encode instanceValue.hypotheses,
    MM0.Presentation.encode instanceValue.conclusion]

theorem encodeTheoremInstance_injective : Function.Injective encodeTheoremInstance := by
  intro left right same
  simp only [encodeTheoremInstance, Term.list.injEq, List.cons.injEq, true_and, and_true] at same
  have hypotheses := encodeList_injective MM0.Presentation.encode_injective same.1
  have conclusion := MM0.Presentation.encode_injective same.2
  cases left; cases right
  simp_all

run_cmd Lean.Elab.Command.liftTermElabM do
  registerCodec ⟨``MM0.Kernel.TheoremDecl, ``encodeTheoremDecl, ``encodeTheoremDecl_injective⟩
  registerCodec ⟨``MM0.Kernel.TheoremInstance, ``encodeTheoremInstance,
    ``encodeTheoremInstance_injective⟩
  registerDependency {
    sourceName := ``MM0.Kernel.Substitution.checkAdmissible
    programName := ``admissibleProgram
    certificateName := ``admissible_computes
    adapter := some ``Inference.termTable }
  registerDependency {
    sourceName := ``MM0.Kernel.Substitution.substituteList
    programName := ``Linked.listProgram
    certificateName := ``Linked.list_computes
    adapter := some ``MM0.Kernel.Substitution.ofList }

extract_specialized_candidate instantiateProgram from MM0.Kernel.TheoremDecl.instantiate?
  using Inference.termTable
prepare_extraction instantiateProgram
certify_specialized_extraction instantiateProgram from MM0.Kernel.TheoremDecl.instantiate?
  using Inference.termTable as instantiate_computes

def instantiateHead : String :=
  "nik:extracted:Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Instantiation.instantiateProgram"

/-- The extracted result is precisely the independent admitted instantiation. -/
theorem instantiate_accepts_iff (entries : List (Nat × MM0.Kernel.TermDecl))
    (target : MM0.Kernel.Context) (declaration : MM0.Kernel.TheoremDecl)
    (arguments : List MM0.Kernel.Preterm) (result : MM0.Kernel.TheoremInstance) :
    Applies instantiateProgram dataEqualityHost instantiateHead
      [encodeList (encodePair natural encodeDeclaration) entries, encodeList encodeBinder target,
        encodeTheoremDecl declaration, encodeList MM0.Presentation.encode arguments]
      (encodeOption encodeTheoremInstance (some result)) ↔
      MM0.Kernel.TheoremDecl.Instantiates (Inference.termTable entries) target declaration
        arguments result := by
  unfold instantiateHead
  rw [instantiate_computes_result_exact]
  constructor
  · intro same
    have source := (encodeOption_injective encodeTheoremInstance_injective same).symm
    exact (MM0.Kernel.TheoremDecl.instantiate_eq_some_iff _ _ _ _ _).mp source
  · intro instantiated
    rw [instantiated.eval]
    rfl

theorem instantiate_refuses_iff (entries : List (Nat × MM0.Kernel.TermDecl))
    (target : MM0.Kernel.Context) (declaration : MM0.Kernel.TheoremDecl)
    (arguments : List MM0.Kernel.Preterm) :
    Applies instantiateProgram dataEqualityHost instantiateHead
      [encodeList (encodePair natural encodeDeclaration) entries, encodeList encodeBinder target,
        encodeTheoremDecl declaration, encodeList MM0.Presentation.encode arguments] (.sym "None") ↔
      ¬ ∃ result, MM0.Kernel.TheoremDecl.Instantiates (Inference.termTable entries) target declaration
        arguments result := by
  unfold instantiateHead
  rw [instantiate_computes_result_exact]
  have encoding : (.sym "None" = encodeOption encodeTheoremInstance
      (MM0.Kernel.TheoremDecl.instantiate? (Inference.termTable entries) target declaration arguments)) ↔
      MM0.Kernel.TheoremDecl.instantiate? (Inference.termTable entries) target declaration arguments = none := by
    constructor
    · intro same
      change encodeOption encodeTheoremInstance none = encodeOption encodeTheoremInstance
        (MM0.Kernel.TheoremDecl.instantiate? (Inference.termTable entries) target declaration arguments) at same
      exact (encodeOption_injective encodeTheoremInstance_injective same).symm
    · intro refused
      rw [refused]
      rfl
  exact encoding.trans (MM0.Kernel.TheoremDecl.instantiate_none_iff _ _ _ _)

theorem theory_instantiate_accepts_iff (theory : MM0.Kernel.Theory)
    (target : MM0.Kernel.Context) (declaration : MM0.Kernel.TheoremDecl)
    (arguments : List MM0.Kernel.Preterm) (result : MM0.Kernel.TheoremInstance) :
    Applies instantiateProgram dataEqualityHost instantiateHead
      [encodeList (encodePair natural encodeDeclaration) theory.terms, encodeList encodeBinder target,
        encodeTheoremDecl declaration, encodeList MM0.Presentation.encode arguments]
      (encodeOption encodeTheoremInstance (some result)) ↔
      MM0.Kernel.TheoremDecl.Instantiates theory.termSignature target declaration arguments result :=
  instantiate_accepts_iff theory.terms target declaration arguments result

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Instantiation
