import Mettapedia.GSLT.LanguageDef.DeterministicEquations.LeanExtractionProof
import Mettapedia.Languages.MM0.Presentation.Data
import Mettapedia.Languages.VibeITP.Spec.Basic

/-!
# Two source-derived computations with generated certificates

Both programs and all six observation theorems are produced by the same
extractor. The only guest registration supplies the existing injective MM0
data codec. No algorithm or correctness theorem is supplied by the guest.
The source definitions and their checked induction/equation theorems are
used directly. Runtime realization of the equation evaluator and primitives
is a separate boundary.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Paired

open Mettapedia.Languages

run_cmd Lean.Elab.Command.liftTermElabM do
  registerCodec ⟨``MM0.Kernel.Preterm, ``MM0.Presentation.encode, ``MM0.Presentation.encode_injective⟩

extract_candidate bytesProgram from VibeITP.Spec.leBytes
certify_extraction bytesProgram from VibeITP.Spec.leBytes as bytes_computes

extract_specialized_candidate substitutionProgram from MM0.Kernel.Preterm.substitute
  using MM0.Kernel.Substitution.ofList
certify_specialized_extraction substitutionProgram from MM0.Kernel.Preterm.substitute
  using MM0.Kernel.Substitution.ofList as substitution_computes

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Paired
