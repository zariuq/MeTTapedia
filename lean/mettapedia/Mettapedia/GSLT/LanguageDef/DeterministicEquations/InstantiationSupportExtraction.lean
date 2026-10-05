import Mettapedia.GSLT.LanguageDef.DeterministicEquations.InstantiationArgumentExtraction
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.NaturalSetExtraction

/-! # Complete occurrence support for theorem instantiation

The recursive source computation retains both application children and the
declared dependencies of target regular variables. Canonical set operations
are supplied by checked shared library lowering.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Instantiation

open Mettapedia.Languages
open MM0.Presentation.ComputationalContext

extract_candidate supportProgram from MM0.Kernel.Preterm.support?
prepare_extraction supportProgram
certify_extraction supportProgram from MM0.Kernel.Preterm.support? as support_computes

def supportHead : String :=
  "nik:extracted:Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Instantiation.supportProgram"

theorem support_accepts_iff (context : MM0.Kernel.Context) (source : MM0.Kernel.Preterm)
    (support : Finset Nat) :
    Applies supportProgram productDivisionHost supportHead
      [encodeList encodeBinder context, MM0.Presentation.encode source]
      (encodeOption encodeDependencies (some support)) ↔
      MM0.Kernel.Preterm.Supports context source support := by
  unfold supportHead
  rw [support_computes_result_exact]
  constructor
  · intro same
    have result := (encodeOption_injective Elimination.dependencySet_encoding_injective same).symm
    exact (MM0.Kernel.Preterm.support_eq_some_iff _ _ _).mp result
  · intro supported
    rw [supported.eval]
    rfl

run_cmd Lean.Elab.Command.liftTermElabM do
  registerDependency {
    sourceName := ``MM0.Kernel.Preterm.support?
    programName := ``supportProgram
    certificateName := ``support_computes }

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Instantiation
