import Mettapedia.GSLT.LanguageDef.DeterministicEquations.InferenceExtraction

/-! # Source-derived argument typing for theorem instantiation

The source binder check consumes the certified inference and bound-variable
computations. The finite association table is the actual theory signature.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Instantiation

open Mettapedia.Languages
open MM0.Presentation.ComputationalContext

run_cmd Lean.Elab.Command.liftTermElabM do
  registerDependency {
    sourceName := ``MM0.Kernel.Preterm.infer
    programName := ``Inference.inferProgram
    certificateName := ``Inference.infer_computes
    adapter := some ``Inference.termTable }

extract_specialized_candidate binderCheckProgram from MM0.Kernel.Preterm.checkBinder
  using Inference.termTable
prepare_extraction binderCheckProgram
certify_specialized_extraction binderCheckProgram from MM0.Kernel.Preterm.checkBinder
  using Inference.termTable as binder_check_computes

run_cmd Lean.Elab.Command.liftTermElabM do
  registerDependency {
    sourceName := ``MM0.Kernel.Preterm.checkBinder
    programName := ``binderCheckProgram
    certificateName := ``binder_check_computes
    adapter := some ``Inference.termTable }

extract_specialized_candidate argumentsProgram from MM0.Kernel.Substitution.checkArguments
  using Inference.termTable
prepare_extraction argumentsProgram
certify_specialized_extraction argumentsProgram from MM0.Kernel.Substitution.checkArguments
  using Inference.termTable as arguments_computes

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Instantiation
