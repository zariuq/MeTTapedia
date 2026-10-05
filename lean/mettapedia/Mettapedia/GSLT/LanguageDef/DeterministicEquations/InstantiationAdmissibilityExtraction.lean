import Mettapedia.GSLT.LanguageDef.DeterministicEquations.InstantiationSupportExtraction

/-! # Full source-derived dependency admission

Argument typing precedes the entire ordered independence matrix. Internal row
fallbacks are retained, while the public check also enforces exact arity.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Instantiation

open Mettapedia.Languages
open MM0.Presentation.ComputationalContext

extract_candidate pairProgram from MM0.Kernel.Substitution.checkPair
prepare_extraction pairProgram
certify_extraction pairProgram from MM0.Kernel.Substitution.checkPair as pair_computes

run_cmd Lean.Elab.Command.liftTermElabM do
  registerDependency {
    sourceName := ``MM0.Kernel.Substitution.checkPair
    programName := ``pairProgram
    certificateName := ``pair_computes }

extract_candidate rowProgram from MM0.Kernel.Substitution.checkRow
prepare_extraction rowProgram
certify_extraction rowProgram from MM0.Kernel.Substitution.checkRow as row_computes

run_cmd Lean.Elab.Command.liftTermElabM do
  registerDependency {
    sourceName := ``MM0.Kernel.Substitution.checkRow
    programName := ``rowProgram
    certificateName := ``row_computes }

extract_candidate entriesProgram from MM0.Kernel.Substitution.entries
prepare_extraction entriesProgram
certify_extraction entriesProgram from MM0.Kernel.Substitution.entries as entries_computes

run_cmd Lean.Elab.Command.liftTermElabM do
  registerDependency {
    sourceName := ``MM0.Kernel.Substitution.entries
    programName := ``entriesProgram
    certificateName := ``entries_computes }
  registerDependency {
    sourceName := ``MM0.Kernel.Substitution.checkArguments
    programName := ``argumentsProgram
    certificateName := ``arguments_computes
    adapter := some ``Inference.termTable }

extract_specialized_candidate admissibleProgram from MM0.Kernel.Substitution.checkAdmissible
  using Inference.termTable
prepare_extraction admissibleProgram
certify_specialized_extraction admissibleProgram from MM0.Kernel.Substitution.checkAdmissible
  using Inference.termTable as admissible_computes

def admissibleHead : String :=
  "nik:extracted:Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Instantiation.admissibleProgram"

theorem admissible_accepts_iff (entries : List (Nat × MM0.Kernel.TermDecl))
    (formal target : MM0.Kernel.Context) (expressions : List MM0.Kernel.Preterm) :
    Applies admissibleProgram dataEqualityHost admissibleHead
      [encodeList (encodePair natural encodeDeclaration) entries, encodeList encodeBinder formal,
        encodeList encodeBinder target, encodeList MM0.Presentation.encode expressions] (.sym "True") ↔
      MM0.Kernel.Substitution.Admissible (Inference.termTable entries) formal target expressions := by
  unfold admissibleHead
  rw [admissible_computes_result_exact]
  change boolean true = boolean
    (MM0.Kernel.Substitution.checkAdmissible (Inference.termTable entries) formal target expressions) ↔ _
  rw [boolean_injective.eq_iff]
  exact eq_comm.trans (MM0.Kernel.Substitution.checkAdmissible_iff _ _ _ _)

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Instantiation
