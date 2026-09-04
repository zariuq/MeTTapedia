import Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.MM2NativeTypedRefinement
import Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.NativePreorderConstruction

/-!
# End-to-end MM2 GSLT-derived TGAD boundary

The hard decoder is the intersection of two independent checks:

1. the native preorder trace constructs exactly one program tree and resolves
   every task-local symbol reference;
2. the source-derived typed refinement accepts the same action trace.

The first check connects the tree to the generated MM2 reader and exact atom
lowering.  The second check constrains known execution and addressed heads by
the maintained execution/cursor presentations.  Keeping the witnesses
separate prevents typed refinement from validating its own serialization.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.MM2GSLTDerivedTGAD

open Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.MM2NativeActionCodec
open Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.MM2NativeTypedRefinement
open Mettapedia.Languages.MeTTa.OSLFCore
open Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface

/-- A trace accepted by the exact native construction machine, the generated
MM2 reader bridge, and the independently specified source-derived typed
refinement. -/
structure Admission
    (config : NativePreorderConstruction.Config)
    (symbols : List String) (actions : List Action) where
  structural : NativePreorderConstruction.Admission
    config symbols.length actions
  typed : Derives symbols .program actions
  reader : GSLTAdmission symbols actions

/-- The exact native codec and generated parser bridge compose with any
independent source-derived typed derivation of the same action trace. -/
theorem constructAdmission
    (config : NativePreorderConstruction.Config)
    (symbols : List String) {actions : List Action}
    (structural : NativePreorderConstruction.Admission
      config symbols.length actions)
    (typed : Derives symbols .program actions)
    (nativeProgram : List NativeAtom)
    (decoded : ParsesProgram actions nativeProgram)
    (atoms : List Atom)
    (resolved : realizeAtoms symbols nativeProgram = some atoms)
    (safe : programSafe atoms = true) :
    Nonempty (Admission config symbols actions) := by
  obtain ⟨reader⟩ := admits_through_mm2_gslt symbols nativeProgram decoded
    atoms resolved safe
  exact ⟨⟨structural, typed, reader⟩⟩

/-- Every prefix of an admitted trace survives both the native construction
machine and the source-derived typed layer. -/
theorem admitted_prefix_non_stranding
    {config : NativePreorderConstruction.Config} {symbols : List String}
    {actions leading : List Action}
    (admission : Admission config symbols actions)
    (isPrefix : leading <+: actions) :
    ∃ typedState structuralState,
      run? symbols initial leading = some typedState ∧
        NativePreorderConstruction.run? config symbols.length
          NativePreorderConstruction.initial leading = some structuralState := by
  obtain ⟨typedState, typedExact⟩ :=
    derived_program_prefix_non_stranding admission.typed isPrefix
  obtain ⟨structuralState, structuralExact⟩ :=
    NativePreorderConstruction.admitted_prefix_non_stranding
      admission.structural isPrefix
  exact ⟨typedState, structuralState, typedExact, structuralExact⟩

/-- Reader admission is not inferred from typed refinement: it is the exact
generated-parser derivation stored by the independent codec witness. -/
def admittedGeneratedParserDerivation
    {config : NativePreorderConstruction.Config} {symbols : List String}
    {actions : List Action} (admission : Admission config symbols actions) :
    Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxSemantics.ParsedProgram
      (Mettapedia.Languages.ProcessCalculi.MORK.MM2SyntaxSemantics.stringScalars
        admission.reader.rendered) :=
  admission.reader.parsed

/-! ## The new hard layer is strictly stronger than generic tree completion -/

private def wrongAritySymbols : List String := ["exec", "location"]

private def wrongArityProgram : List NativeAtom :=
  [.expression [.reference 0, .reference 1]]

/-- The generic native tree codec accepts an expression headed by `exec`
with only one argument.  This is precisely the class the old structural mask
could not distinguish. -/
theorem generic_tree_accepts_wrong_exec_arity :
    ParsesProgram (encodeProgram wrongArityProgram) wrongArityProgram :=
  encodeProgram_parses wrongArityProgram

/-- The generated MM2 reader also accepts that atom tree: ordinary MM2 syntax
is intentionally an open S-expression language. -/
theorem generated_reader_accepts_wrong_exec_arity :
    Nonempty
      (GSLTAdmission wrongAritySymbols (encodeProgram wrongArityProgram)) := by
  apply admits_through_mm2_gslt wrongAritySymbols wrongArityProgram
    (encodeProgram_parses wrongArityProgram)
    [.expression [.symbol "exec", .symbol "location"]]
  · rfl
  · decide +kernel

/-- The source-derived typed refinement rejects the same trace when the known
`exec` head is emitted, because its source work-shell has three arguments. -/
theorem typed_refinement_rejects_wrong_exec_arity :
    run? wrongAritySymbols initial (encodeProgram wrongArityProgram) = none := by
  decide +kernel

private def correctAritySymbols : List String :=
  ["exec", "location", ","]

private def correctArityProgram : List NativeAtom :=
  [.expression
    [.reference 0, .reference 1,
      .expression [.reference 2], .expression [.reference 2]]]

/-- Positive control: the source-declared work-shell arity completes the
typed prefix frontier. -/
theorem typed_refinement_accepts_correct_exec_arity :
    run? correctAritySymbols initial (encodeProgram correctArityProgram) =
      some [] := by
  decide +kernel

/-- The source-derived typed trace and the independently implemented strict
execution extractor agree on a compatibility-mode directive. -/
theorem typed_supported_shell_agrees_with_execution_parser :
    run? correctAritySymbols initial (encodeProgram correctArityProgram) =
        some [] ∧
      (Mettapedia.Languages.ProcessCalculi.MORK.extractSupportedSourceExecFact
        (.expression [.symbol "exec", .symbol "location",
          .expression [.symbol ","],
          .expression [.symbol ","]])).isSome = true := by
  decide +kernel

private def bareSpecProgram : List NativeAtom :=
  [.expression
    [.reference 0, .reference 1, .reference 2, .reference 2]]

/-- A reader-valid four-field expression with atomic input/output positions
is rejected by both the typed action layer and the strict execution parser.
This separates ordinary S-expression syntax from supported MM2 execution
syntax. -/
theorem bare_execution_specs_fail_typed_and_execution_admission :
    run? correctAritySymbols initial (encodeProgram bareSpecProgram) = none ∧
      Mettapedia.Languages.ProcessCalculi.MORK.extractSupportedSourceExecFact
        (.expression [.symbol "exec", .symbol "location",
          .symbol ",", .symbol ","]) = none := by
  decide +kernel

#print axioms constructAdmission
#print axioms admitted_prefix_non_stranding
#print axioms admittedGeneratedParserDerivation
#print axioms generic_tree_accepts_wrong_exec_arity
#print axioms generated_reader_accepts_wrong_exec_arity
#print axioms typed_refinement_rejects_wrong_exec_arity
#print axioms typed_refinement_accepts_correct_exec_arity
#print axioms typed_supported_shell_agrees_with_execution_parser
#print axioms bare_execution_specs_fail_typed_and_execution_admission

end Mettapedia.GSLT.LanguageDef.TypedGraphDecoding.MM2GSLTDerivedTGAD
