import Mettapedia.GSLT.LanguageDef.DeterministicEquations.EliminationExtraction
import Mettapedia.Languages.MM0.Kernel.TheoryAdmission

/-! # Complete MM0 inference from its checked source definition

The finite table is the actual association-list signature used by a theory.
The only new guest metadata is the existing injective declaration codec. The
algorithm and universal computation proof are produced from `Preterm.infer`.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Inference

open Mettapedia.Languages
open MM0.Presentation.ComputationalContext

def termTable (entries : List (Nat × MM0.Kernel.TermDecl)) : MM0.Kernel.TermSignature :=
  fun index => entries.lookup index

run_cmd Lean.Elab.Command.liftTermElabM do
  registerCodec ⟨``MM0.Kernel.TermDecl, ``encodeDeclaration, ``encodeDeclaration_injective⟩
  registerDependency {
    sourceName := ``MM0.Kernel.Binder.sort
    programName := ``Elimination.binderSortProgram
    certificateName := ``Elimination.binder_sort_computes }
  registerDependency {
    sourceName := ``MM0.Kernel.Preterm.boundSort?
    programName := ``Elimination.boundSortProgram
    certificateName := ``Elimination.bound_sort_computes }

extract_specialized_candidate inferProgram from MM0.Kernel.Preterm.infer using termTable
prepare_extraction inferProgram
certify_specialized_extraction inferProgram from MM0.Kernel.Preterm.infer using termTable
  as infer_computes

def inferHead : String :=
  "nik:extracted:Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Inference.inferProgram"

def encodeExpressionType : MM0.Kernel.ExpressionType → Term :=
  encodePair (encodeList encodeBinder) natural

theorem encodeExpressionType_injective : Function.Injective encodeExpressionType :=
  encodePair_injective (encodeList_injective encodeBinder_injective) natural_injective

/-- The generated result is exactly the independent typing judgment. -/
theorem infer_accepts_iff (entries : List (Nat × MM0.Kernel.TermDecl))
    (context : MM0.Kernel.Context) (expression : MM0.Kernel.Preterm)
    (remaining : MM0.Kernel.Context) (sort : Nat) :
    Applies inferProgram dataEqualityHost inferHead
      [encodeList (encodePair natural encodeDeclaration) entries, encodeList encodeBinder context,
        MM0.Presentation.encode expression]
      (encodeOption encodeExpressionType (some (remaining, sort))) ↔
      MM0.Kernel.Preterm.HasType (termTable entries) context expression remaining sort := by
  unfold inferHead
  rw [infer_computes_result_exact]
  constructor
  · intro equal
    have source := (encodeOption_injective encodeExpressionType_injective equal).symm
    exact (MM0.Kernel.Preterm.infer_eq_some_iff _ _ _ _ _).mp source
  · intro typing
    rw [typing.eval]
    rfl

/-- Optional refusal is a completed source result, separate from exhaustion. -/
theorem infer_refuses_iff (entries : List (Nat × MM0.Kernel.TermDecl))
    (context : MM0.Kernel.Context) (expression : MM0.Kernel.Preterm) :
    Applies inferProgram dataEqualityHost inferHead
      [encodeList (encodePair natural encodeDeclaration) entries, encodeList encodeBinder context,
        MM0.Presentation.encode expression] (.sym "None") ↔
      ¬ ∃ remaining sort,
        MM0.Kernel.Preterm.HasType (termTable entries) context expression remaining sort := by
  unfold inferHead
  rw [infer_computes_result_exact]
  have encoding : (.sym "None" = encodeOption encodeExpressionType
      (MM0.Kernel.Preterm.infer (termTable entries) context expression)) ↔
      MM0.Kernel.Preterm.infer (termTable entries) context expression = none := by
    constructor
    · intro equal
      change encodeOption encodeExpressionType none = encodeOption encodeExpressionType
        (MM0.Kernel.Preterm.infer (termTable entries) context expression) at equal
      exact (encodeOption_injective encodeExpressionType_injective equal).symm
    · intro refused
      rw [refused]
      rfl
  exact encoding.trans (MM0.Kernel.Preterm.infer_none_iff _ _ _)

theorem theory_infer_accepts_iff (theory : MM0.Kernel.Theory)
    (context : MM0.Kernel.Context) (expression : MM0.Kernel.Preterm)
    (remaining : MM0.Kernel.Context) (sort : Nat) :
    Applies inferProgram dataEqualityHost inferHead
      [encodeList (encodePair natural encodeDeclaration) theory.terms, encodeList encodeBinder context,
        MM0.Presentation.encode expression]
      (encodeOption encodeExpressionType (some (remaining, sort))) ↔
      MM0.Kernel.Preterm.HasType theory.termSignature context expression remaining sort :=
  infer_accepts_iff theory.terms context expression remaining sort

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Inference
