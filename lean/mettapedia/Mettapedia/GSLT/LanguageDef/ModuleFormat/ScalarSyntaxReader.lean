import Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxCST
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SourceSyntaxExport
import Mettapedia.GSLT.Parsing.ClassAwareParserPackOutput

/-! Finite parser certificates are replayed against the actual compiled
grammar/profile before CST data reaches the retained syntax core. The
reader proves source soundness, source-derivation coverage, closed sorting
and independent full-source printing. Native forest production and selected
packet construction retain their own correctness obligations. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxCore

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.Parsing
open LanguageDefSyntaxCompiler LanguageDefScalarSyntax LanguageDefScalarPrinter PresentationExprSemantics
open ClassAwareParserPackCorrespondence ClassAwareParserPackCertificate

structure Parser (description : Description) where
  rules : List CompiledRule
  plan : CompiledParserPackPlan
  rulesCompiled : compileRules? (SourceSyntaxExport.binding description.profile) description.grammar = some rules
  planCompiled : compileParserPackPlan? SourceSyntaxExport.literalScalars? description.profile rules = some plan

def compileParser? (description : Description) : Option (Parser description) :=
  match compiled : compileRules? (SourceSyntaxExport.binding description.profile) description.grammar with
  | none => none
  | some rules =>
      match packed : compileParserPackPlan? SourceSyntaxExport.literalScalars? description.profile rules with
      | none => none
      | some plan => some ⟨rules, plan, compiled, packed⟩

theorem Parser.agreement {description : Description} (parser : Parser description) :
    ParserPackPlanAgreement SourceSyntaxExport.literalScalars? description.profile parser.rules parser.plan :=
  .of_compilation parser.planCompiled

theorem source_of_replay {description : Description} (parser : Parser description)
    {input : List Nat} {certificate : Certificate} {sort : String} {start stop : Nat} {tree : CST}
    (replayed : Replays description.profile parser.plan input certificate sort start stop tree) :
    Nonempty (DerivesAt SourceSyntaxExport.literalScalars? description.profile description.grammar input sort start stop tree) :=
  LanguageDefScalarSyntax.reflect parser.rulesCompiled (reflectSourcePlanDerivation parser.agreement replayed.derivation)

structure Reading (description : Description) (parser : Parser description) (shape : Shape description)
    (input : List Nat) (sort : String) (start stop : Nat) where
  certificate : Certificate
  tree : CST
  replayed : Replays description.profile parser.plan input certificate sort start stop tree
  source : Nonempty (DerivesAt SourceSyntaxExport.literalScalars? description.profile description.grammar input sort start stop tree)
  core : Pattern
  construction : lowerCST? description sort tree = some core
  closed : ClosedTermWellSorted (language description) ⟨sort, by
    obtain ⟨witness⟩ := source
    exact source_sort_declared description shape witness⟩ core

def readCertificate? (description : Description) (parser : Parser description) (shape : Shape description)
    (input : List Nat) (sort : String) (start stop : Nat) (certificate : Certificate) :
    Option (Reading description parser shape input sort start stop) := do
  let parsed ← ClassAwareParserPackReplay.replay description.profile parser.plan input sort start stop certificate
  let source := source_of_replay parser parsed.2
  let term := checkedTerm description shape parsed.1 source
  some ⟨certificate, parsed.1, parsed.2, source, term.val,
    checkedTerm_lower description shape parsed.1 source, term.property⟩

theorem readCertificate?_isSome_iff (description : Description) (parser : Parser description) (shape : Shape description)
    (input : List Nat) (sort : String) (start stop : Nat) (certificate : Certificate) :
    (readCertificate? description parser shape input sort start stop certificate).isSome = true ↔
      ∃ tree, Nonempty (Replays description.profile parser.plan input certificate sort start stop tree) := by
  rw [← ClassAwareParserPackReplay.replay_isSome_iff]
  unfold readCertificate?
  cases ClassAwareParserPackReplay.replay description.profile parser.plan input sort start stop certificate <;> rfl

theorem readCertificate?_certificate {description : Description} {parser : Parser description} {shape : Shape description}
    {input : List Nat} {sort : String} {start stop : Nat} {certificate : Certificate}
    {reading : Reading description parser shape input sort start stop}
    (read : readCertificate? description parser shape input sort start stop certificate = some reading) :
    reading.certificate = certificate := by
  obtain ⟨parsed, _, same⟩ := Option.bind_eq_some_iff.mp read
  exact Option.some.inj same ▸ rfl

/-- Enrich a replay with this realization's typing evidence, preserving both
its certificate and its tree. Selection policies remain a separate layer. -/
theorem reading_of_replay {description : Description} (parser : Parser description) (shape : Shape description)
    {input : List Nat} {sort : String} {start stop : Nat} {tree : CST} {certificate : Certificate}
    (replayed : Replays description.profile parser.plan input certificate sort start stop tree) :
    ∃ reading : Reading description parser shape input sort start stop,
      readCertificate? description parser shape input sort start stop certificate = some reading ∧
      reading.certificate = certificate ∧ reading.tree = tree := by
  simp only [readCertificate?, ClassAwareParserPackOutput.replay_exact replayed]
  exact ⟨_, rfl, rfl, rfl⟩

theorem Reading.core_exact {description : Description} {parser : Parser description} {shape : Shape description}
    {input : List Nat} {sort : String} {start stop : Nat} (reading : Reading description parser shape input sort start stop)
    (source : DerivesAt SourceSyntaxExport.literalScalars? description.profile description.grammar input sort start stop reading.tree) :
    reading.core = reify description source :=
  Option.some.inj (reading.construction.symm.trans (lowerCST_source description shape source))

theorem Reading.full_source {description : Description} {parser : Parser description} {shape : Shape description}
    {input : List Nat} {sort : String} (reading : Reading description parser shape input sort 0 input.length) :
    printScalars? description sort reading.core = some input := by
  obtain ⟨source⟩ := reading.source
  rw [reading.core_exact source]
  exact full_scalars description shape source

theorem source_has_reading {description : Description} (parser : Parser description) (shape : Shape description)
    {input : List Nat} {sort : String} {start stop : Nat} {tree : CST}
    (source : DerivesAt SourceSyntaxExport.literalScalars? description.profile description.grammar input sort start stop tree) :
    ∃ (certificate : Certificate) (reading : Reading description parser shape input sort start stop),
      readCertificate? description parser shape input sort start stop certificate = some reading ∧
      reading.tree = tree ∧ reading.core = reify description source := by
  obtain ⟨sourcePlan⟩ := LanguageDefScalarSyntax.preserve parser.rulesCompiled source
  let target := preserveSourcePlanDerivation parser.agreement sourcePlan
  obtain ⟨reading, read, _, treeSame⟩ := reading_of_replay parser shape (Replays.ofDerivation target)
  cases treeSame
  exact ⟨_, reading, read, rfl, reading.core_exact source⟩

def readPrintScalars? (description : Description) (parser : Parser description) (shape : Shape description)
    (input : List Nat) (sort : String) (certificate : Certificate) : Option (List Nat) := do
  let reading ← readCertificate? description parser shape input sort 0 input.length certificate
  printScalars? description sort reading.core

theorem readPrintScalars?_exact (description : Description) (parser : Parser description) (shape : Shape description)
    (input : List Nat) (sort : String) (certificate : Certificate) :
    readPrintScalars? description parser shape input sort certificate =
      if (readCertificate? description parser shape input sort 0 input.length certificate).isSome then some input else none := by
  cases read : readCertificate? description parser shape input sort 0 input.length certificate with
  | none => simp [readPrintScalars?, read]
  | some reading => simpa [readPrintScalars?, read] using reading.full_source

#print axioms source_of_replay
#print axioms readCertificate?_isSome_iff
#print axioms Reading.core_exact
#print axioms Reading.full_source
#print axioms source_has_reading
#print axioms readPrintScalars?_exact

end Mettapedia.GSLT.LanguageDef.ModuleFormat.ScalarSyntaxCore
