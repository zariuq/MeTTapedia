import Mettapedia.GSLT.LanguageDef.DeterministicEquations.PairedExtraction
import Mettapedia.Languages.MM0.Kernel.Proof

/-! # A generated source caller using a certified dependency

The source list traversal and its proof are extracted from the actual MM0
definition. The registered child supplies a checked computation theorem; no
caller algorithm or correspondence proof is supplied here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Linked

open Mettapedia.Languages

run_cmd Lean.Elab.Command.liftTermElabM do
  registerDependency {
    sourceName := ``MM0.Kernel.Preterm.substitute
    programName := ``Paired.substitutionProgram
    certificateName := ``Paired.substitution_computes
    adapter := some ``MM0.Kernel.Substitution.ofList }

extract_specialized_candidate listProgram from MM0.Kernel.Substitution.substituteList
  using MM0.Kernel.Substitution.ofList

certify_specialized_extraction listProgram from MM0.Kernel.Substitution.substituteList
  using MM0.Kernel.Substitution.ofList as list_computes

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Linked
