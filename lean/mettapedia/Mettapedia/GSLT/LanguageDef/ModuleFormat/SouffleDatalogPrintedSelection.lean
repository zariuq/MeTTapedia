import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterProgramPolicy
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogSelectedSource
import Mettapedia.GSLT.Parsing.LanguageDefScalarSpan

/-! Canonical program printing enters the actual selected source profile.
The proof transports the constructor invariant through original syntax,
exact spans and compiled occurrence certificates. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.Datalog
open Mettapedia.GSLT.Parsing
open LanguageDefScalarSyntax LanguageDefScalarPrinter PresentationExprSemantics
open ClassAwareParserPackCorrespondence ClassAwareParserPackCertificate

def Policy.span (input : List Nat) (label : String) (start stop : Nat) : Prop :=
  label = "dl-src:identifier-one" ∨ label = "dl-src:identifier-more" →
    ∃ name, (input.drop start).take (stop - start) = name.toList.map Char.toNat ∧
      name ∉ SourcePolicy.reservedWords

theorem Policy.span_selects {input : List Nat} {sort : String} {tree : CST}
    (derived : ParserPackDerivesAt SourceViews.profile SourceReader.plan input sort 0 input.length tree)
    (holds : SourceTreePolicy.Holds (Policy.span input) tree) :
    ∀ family ∈ ClassAwarePackedForest.certificateFamilies sort (Certificate.ofDerivation derived),
      SourcePacketSelection.allows SourcePolicy.filters input family = true := by
  apply (SourcePacketSelection.selected_iff _ _ _).mp
  apply SourceTreePolicy.selects SourcePolicy.filters (Policy.span input) _ _ derived holds
  · intro row member start stop _
    have different : row.resultSort ≠ "DlIdentifier" := by
      obtain ⟨index, same⟩ := List.mem_iff_get.mp member
      subst row
      fin_cases index <;> decide +kernel
    simp [SourcePolicy.filters, SourceSyntax.FamilyFilter.allows, different]
  · intro row member start stop policy
    by_cases identifier : row.resultSort = "DlIdentifier"
    · have label : row.label = "dl-src:identifier-one" ∨ row.label = "dl-src:identifier-more" := by
        obtain ⟨index, same⟩ := List.mem_iff_get.mp member
        subst row
        fin_cases index <;> simp_all +decide
      obtain ⟨name, word, notReserved⟩ := policy label
      simp only [SourcePolicy.filters, List.all_cons, List.all_nil, Bool.and_true,
        SourceSyntax.FamilyFilter.allows, identifier, bne_self_eq_false, Bool.false_or]
      change (!(SourcePolicy.reservedWords.any fun text => text.toList.map Char.toNat ==
        (input.drop start).take (stop - start))) = true
      simp only [Bool.not_eq_true', List.any_eq_false]
      intro reserved member
      rw [word]
      intro equal
      have equal := beq_iff_eq.mp equal
      have names : reserved = name := by
        have chars := congrArg (List.map Char.ofNat) equal
        simp only [List.map_map, Function.comp_def, Char.ofNat_toNat] at chars
        change reserved.toList.map id = name.toList.map id at chars
        rw [List.map_id, List.map_id] at chars
        exact String.toList_injective chars
      exact notReserved (names ▸ member)
    · simp [SourcePolicy.filters, SourceSyntax.FamilyFilter.allows, identifier]

theorem Policy.source_tree {input : List Nat} {sort : String} {start stop : Nat} {tree : CST}
    (derived : DerivesAt SourceSyntaxExport.literalScalars? description.profile description.grammar input sort start stop tree)
    (holds : Policy.Holds (ScalarSyntaxCore.reify description derived)) :
    SourceTreePolicy.Holds (Policy.span input) tree := by
  apply SourcePatternPolicy.reify_tree description Policy.root (Policy.span input) _ _ derived holds
  · intro row start stop
    have different : (description.profile.states.get row).ruleLabel ≠ "dl-src:identifier-one" ∧
        (description.profile.states.get row).ruleLabel ≠ "dl-src:identifier-more" := by
      fin_cases row <;> decide +kernel
    intro equal
    exact False.elim (equal.elim different.1 different.2)
  · intro row start stop children body rootPolicy identifier
    obtain ⟨name, printed, notReserved⟩ := rootPolicy identifier
    have category : (description.grammar.terms.get row).category = "DlIdentifier" := by
      fin_cases row <;> simp_all +decide [description]
    have common : ScalarSyntaxCore.printText? description "DlIdentifier"
        (ScalarSyntaxCore.reify description (.structural row body)) = some name :=
      (shared_print _ _).trans printed
    rw [← category] at common
    have points := ScalarSyntaxCore.printText_scalars description _ _ _ common
    have rendered := ScalarSyntaxCore.print_reify description description_shape (DerivesAt.structural row body)
    have scalarPoints := Option.some.inj (rendered.symm.trans points)
    exact ⟨name, (sequence_slice (renderItems_matches body)).trans scalarPoints, notReserved⟩

theorem printed_selected_source (environment : Engine.RelationEnv) (program : Program) (text : String)
    (printed : print? program = .ok text) : SelectedSource.ProgramMeaning environment text program := by
  cases built : programTree? program with
  | error reason => simp [print?, built, bind, Except.bind] at printed
  | ok pattern =>
    cases rendered : CorePrinter.printText? "DlProgram" pattern with
    | none => simp [print?, built, bind, Except.bind, rendered] at printed
    | some actual =>
      have same : actual = text := by simpa [print?, built, bind, Except.bind, rendered, pure, Except.pure] using printed
      subst actual
      obtain ⟨tree, ⟨derived⟩, lowered⟩ := ScalarSyntaxCore.printed_text_readback
        description description_shape "DlProgram" pattern text ((shared_print _ _).trans rendered)
      have coreSame : ScalarSyntaxCore.reify description derived = pattern :=
        Option.some.inj ((ScalarSyntaxCore.lowerCST_source description description_shape derived).symm.trans lowered)
      have treePolicy := Policy.source_tree derived (coreSame.symm ▸ Policy.program_holds program pattern built)
      obtain ⟨sourcePlan⟩ := LanguageDefScalarSyntax.preserve SelectedReader.parser.rulesCompiled derived
      let target := preserveSourcePlanDerivation SelectedReader.parser.agreement sourcePlan
      refine ⟨pattern, ⟨tree, target, Policy.span_selects target treePolicy, lowered⟩, ?_⟩
      have projected := program_tree_roundtrip program pattern built
      obtain ⟨normalized, normalRead, decoded⟩ := Option.bind_eq_some_iff.mp projected
      obtain ⟨body, bodyRead, normalizedRead⟩ := Option.bind_eq_some_iff.mp normalRead
      refine ⟨body, ProgramProjection.Program.step_of_reference environment pattern body bodyRead, ?_⟩
      rw [IRCodec.program_inverse normalized program decoded]
      exact SourceMeaning.normalization_sound body normalized normalizedRead

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter
