import Mettapedia.GSLT.LanguageDef.DeterministicEquations.LinkedExtraction
import Mettapedia.Languages.MM0.Presentation.ContextData

/-! # Source-derived constructor elimination

The programs and their certificates are generated from actual kernel
definitions. The declarations below provide only injective data codecs.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Elimination

open Mettapedia.Languages
open MM0.Presentation.ComputationalContext

abbrev DependencySet := Finset Nat

theorem dependencySet_encoding_injective : Function.Injective encodeDependencies := by
  intro left right same
  have decoded := congrArg decodeDependencies same
  simpa only [decodeDependencies_encode, Option.some.injEq] using decoded

def encodeBuiltin (symbol : VibeITP.Spec.Builtin) : DeterministicEquations.Term :=
  natural symbol.slot

theorem encodeBuiltin_injective : Function.Injective encodeBuiltin := by
  intro left right same
  have slots := natural_injective same
  cases left <;> cases right <;> simp_all [VibeITP.Spec.Builtin.slot]

run_cmd Lean.Elab.Command.liftTermElabM do
  registerCodec ⟨``DependencySet, ``encodeDependencies, ``dependencySet_encoding_injective⟩
  registerCodec ⟨``MM0.Kernel.Binder, ``encodeBinder, ``encodeBinder_injective⟩
  registerCodec ⟨``VibeITP.Spec.Builtin, ``encodeBuiltin, ``encodeBuiltin_injective⟩

extract_candidate binderSortProgram from MM0.Kernel.Binder.sort
certify_extraction binderSortProgram from MM0.Kernel.Binder.sort as binder_sort_computes

extract_candidate boundSortProgram from MM0.Kernel.Preterm.boundSort?
certify_extraction boundSortProgram from MM0.Kernel.Preterm.boundSort? as bound_sort_computes

extract_candidate builtinArityProgram from VibeITP.Spec.Builtin.arity
certify_extraction builtinArityProgram from VibeITP.Spec.Builtin.arity as builtin_arity_computes

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.Extraction.Elimination
