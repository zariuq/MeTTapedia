import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogCompleteForest
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogFrontendMeaning

/-! Complete source-reference reading from codepoints. The finite catalogue
retains every parser derivation before semantic projection. This is the
independent reference for the native reader, not a claim about its runtime
forest or a policy that silently chooses one ambiguous parse. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ReferenceReader

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.Datalog
open Mettapedia.GSLT.Parsing
open ClassAwareParserPackCertificate ClassAwareParserPackCorrespondence PresentationExprSemantics

def program? (tree : CST) : Option Program := do
  let source ← CSTToCore.lower? SourceReader.plan.lexical.startSort tree
  let projected ← ProgramProjection.Reference.projectProgram? source
  let normalized ← Frontend.normalize? projected
  IRCodec.program? normalized

def programs (input : List Nat) : List Program :=
  (SourceReader.completeCatalogue input).entries.filterMap fun entry => program? entry.2

def SourceProgram (input : List Nat) (program : Program) : Prop :=
  ∃ (tree : CST) (source : Pattern),
    Nonempty (LanguageDefScalarSyntax.DerivesAt CorePrinter.literalScalars? SourceViews.profile
      SourceViews.grammar input SourceReader.plan.lexical.startSort 0 input.length tree) ∧
    CSTToCore.lower? SourceReader.plan.lexical.startSort tree = some source ∧
    ((ProgramProjection.Reference.projectProgram? source).bind Frontend.normalize?).bind IRCodec.program? = some program

theorem programs_sound (input : List Nat) (program : Program) (member : program ∈ programs input) :
    SourceProgram input program := by
  obtain ⟨entry,present,read⟩ := List.mem_filterMap.mp member
  obtain ⟨replayed⟩ := (SourceReader.completeCatalogue input).replay entry present
  obtain ⟨sourceDerivation⟩ := SourceReader.source_of_replay replayed
  refine ⟨entry.2,SourceToCore.reify sourceDerivation,⟨sourceDerivation⟩,
    CSTToCore.lower_source sourceDerivation,?_⟩
  simpa only [program?,CSTToCore.lower_source sourceDerivation,Option.bind_eq_bind,Option.bind_some,
    Option.bind_assoc] using read

theorem programs_complete (input : List Nat) (program : Program) (source : SourceProgram input program) :
    program ∈ programs input := by
  obtain ⟨tree,pattern,⟨sourceDerivation⟩,lowered,read⟩ := source
  obtain ⟨sourcePlan⟩ := LanguageDefScalarSyntax.preserve SourceReader.rules_compiled sourceDerivation
  let derivation := preserveSourcePlanDerivation SourceReader.agreement sourcePlan
  have present := (SourceReader.completeCatalogue input).complete tree derivation
  apply List.mem_filterMap.mpr
  refine ⟨(Certificate.ofDerivation derivation,tree),present,?_⟩
  simpa only [program?,lowered,Option.bind_eq_bind,Option.bind_some,Option.bind_assoc] using read

theorem programs_exact (input : List Nat) (program : Program) :
    program ∈ programs input ↔ SourceProgram input program :=
  ⟨programs_sound input program, programs_complete input program⟩

theorem sourceProgram_denotes (environment : Engine.RelationEnv) (input : List Nat) (program : Program)
    (source : SourceProgram input program) :
    ∃ pattern, CorePrinter.printScalars? SourceReader.plan.lexical.startSort pattern = some input ∧
      SourceMeaning.Denotes environment pattern program := by
  obtain ⟨tree,pattern,⟨derivation⟩,lowered,read⟩ := source
  have same : pattern = SourceToCore.reify derivation :=
    Option.some.inj (lowered.symm.trans (CSTToCore.lower_source derivation))
  refine ⟨pattern,?_,?_⟩
  · rw [same]
    exact CorePrinter.full_scalars derivation
  · obtain ⟨normalized,normalRead,decoded⟩ := Option.bind_eq_some_iff.mp read
    obtain ⟨projected,projectedRead,normalizedRead⟩ := Option.bind_eq_some_iff.mp normalRead
    refine ⟨projected,ProgramProjection.Program.step_of_reference environment pattern projected projectedRead,?_⟩
    rw [IRCodec.program_inverse normalized program decoded]
    exact SourceMeaning.normalization_sound projected normalized normalizedRead

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.ReferenceReader
