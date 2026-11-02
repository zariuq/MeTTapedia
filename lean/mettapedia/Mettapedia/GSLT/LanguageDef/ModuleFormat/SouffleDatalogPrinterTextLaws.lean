import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterLexicalLaws
import Mettapedia.GSLT.Parsing.DeclaredConstructorPrinterComposition

/-! Character sequences constructed by the source printer preserve their
text through the declared grammar, including names and decimal digits. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.GSLT.Parsing
open Mettapedia.OSLF.Framework.GrammarDerives
open DeclaredConstructorPrinter

theorem print_unary (sort label parameter childSort : String) (child : Pattern) (row : GrammarRule)
    (structural : CorePrinter.lexical sort = none)
    (selected : constructor? SourceViews.grammar ("dl-src:" ++ label) sort = some row)
    (layout : row.syntaxPattern = [.nonTerminal parameter])
    (parameterSort : paramSort? row parameter = some childSort) :
    CorePrinter.printText? sort (node label [child]) = CorePrinter.printText? childSort child := by
  unfold CorePrinter.printText? CorePrinter.printScalars? node
  rw [print?_unary _ _ _ _ _ _ _ _ _ structural selected layout parameterSort]

theorem print_binary (sort label firstParameter secondParameter firstSort secondSort : String)
    (first second : Pattern) (row : GrammarRule)
    (structural : CorePrinter.lexical sort = none)
    (selected : constructor? SourceViews.grammar ("dl-src:" ++ label) sort = some row)
    (layout : row.syntaxPattern = [.nonTerminal firstParameter,.nonTerminal secondParameter])
    (firstParameterSort : paramSort? row firstParameter = some firstSort)
    (secondParameterSort : paramSort? row secondParameter = some secondSort) :
    CorePrinter.printText? sort (node label [first,second]) = (do
      let left ← CorePrinter.printText? firstSort first
      let right ← CorePrinter.printText? secondSort second
      pure (left ++ right)) := by
  unfold CorePrinter.printText? CorePrinter.printScalars? node
  rw [print?_binary _ _ _ _ _ _ _ _ _ _ _ _ structural selected layout
    firstParameterSort secondParameterSort]
  cases firstRead : DeclaredConstructorPrinter.print? SourceViews.grammar LanguageDefScalarPrinter.stringScalars CorePrinter.lexical firstSort first <;>
    cases secondRead : DeclaredConstructorPrinter.print? SourceViews.grammar LanguageDefScalarPrinter.stringScalars CorePrinter.lexical secondSort second <;>
    simp [List.map_append]


theorem identifier_one (child : Pattern) :
    CorePrinter.printText? "DlIdentifier" (node "identifier-one" [child]) =
      CorePrinter.printText? "DlSingleIdentifierScalar" child := by
  exact print_unary _ _ "scalar" _ _ (SourceViews.grammar.terms.get ⟨51,by decide⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem identifier_tail_one (child : Pattern) :
    CorePrinter.printText? "DlIdentifierNonempty" (node "identifier-tail-one" [child]) =
      CorePrinter.printText? "DlIdentifierRestScalar" child := by
  exact print_unary _ _ "scalar" _ _ (SourceViews.grammar.terms.get ⟨53,by decide⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem digits_one (child : Pattern) :
    CorePrinter.printText? "DlDigits" (node "digits-one" [child]) =
      CorePrinter.printText? "DlDigitScalar" child := by
  exact print_unary _ _ "digit" _ _ (SourceViews.grammar.terms.get ⟨66,by decide⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem integer_decimal (child : Pattern) :
    CorePrinter.printText? "DlInteger" (node "integer-decimal" [child]) =
      CorePrinter.printText? "DlDigits" child := by
  exact print_unary _ _ "digits" _ _ (SourceViews.grammar.terms.get ⟨55,by decide⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem qualified_name_one (child : Pattern) :
    CorePrinter.printText? "DlQualifiedName" (node "qualified-name-one" [child]) =
      CorePrinter.printText? "DlIdentifier" child := by
  exact print_unary _ _ "identifier" _ _ (SourceViews.grammar.terms.get ⟨49,by decide⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem identifier_more (first second : Pattern) :
    CorePrinter.printText? "DlIdentifier" (node "identifier-more" [first,second]) = (do
      let left ← CorePrinter.printText? "DlIdentifierFirstScalar" first
      let right ← CorePrinter.printText? "DlIdentifierNonempty" second
      pure (left ++ right)) := by
  exact print_binary _ _ "head" "tail" _ _ _ _ (SourceViews.grammar.terms.get ⟨52,by decide⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem identifier_tail_more (first second : Pattern) :
    CorePrinter.printText? "DlIdentifierNonempty" (node "identifier-tail-more" [first,second]) = (do
      let left ← CorePrinter.printText? "DlIdentifierRestScalar" first
      let right ← CorePrinter.printText? "DlIdentifierNonempty" second
      pure (left ++ right)) := by
  exact print_binary _ _ "head" "tail" _ _ _ _ (SourceViews.grammar.terms.get ⟨54,by decide⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem digits_more (first second : Pattern) :
    CorePrinter.printText? "DlDigits" (node "digits-more" [first,second]) = (do
      let left ← CorePrinter.printText? "DlDigitScalar" first
      let right ← CorePrinter.printText? "DlDigits" second
      pure (left ++ right)) := by
  exact print_binary _ _ "head" "tail" _ _ _ _ (SourceViews.grammar.terms.get ⟨67,by decide⟩)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem digits_print (characters : List Char) (source : Pattern)
    (built : digits? characters = .ok source) :
    CorePrinter.printText? "DlDigits" source = some (String.ofList characters) := by
  induction characters generalizing source with
  | nil => cases built
  | cons character rest ih =>
      cases rest with
      | nil =>
          cases scalarRead : scalar? "DlDigitScalar" character with
          | error reason =>
              rw [digits?, scalarRead] at built
              cases built
          | ok leaf =>
              have same : node "digits-one" [leaf] = source := by simpa [digits?, scalarRead] using built
              subst source
              rw [digits_one, scalar_print _ _ _ scalarRead]
              rfl
      | cons second tail =>
          cases scalarRead : scalar? "DlDigitScalar" character with
          | error reason =>
              rw [digits?, scalarRead] at built <;> try simp
              cases built
          | ok leaf =>
              cases tailRead : digits? (second :: tail) with
              | error reason =>
                  rw [digits?, scalarRead, tailRead] at built <;> try simp
                  cases built
              | ok result =>
                  rw [digits?, scalarRead, tailRead] at built <;> try simp
                  have same : node "digits-more" [leaf,result] = source := Except.ok.inj built
                  subst source
                  rw [digits_more, scalar_print _ _ _ scalarRead, ih result tailRead]
                  simp


theorem identifier_tail_print (characters : List Char) (source : Pattern)
    (built : identifierTail? characters = .ok source) :
    CorePrinter.printText? "DlIdentifierNonempty" source = some (String.ofList characters) := by
  induction characters generalizing source with
  | nil => cases built
  | cons character rest ih =>
      cases rest with
      | nil =>
          cases scalarRead : scalar? "DlIdentifierRestScalar" character with
          | error reason =>
              rw [identifierTail?, scalarRead] at built
              cases built
          | ok leaf =>
              have same : node "identifier-tail-one" [leaf] = source := by simpa [identifierTail?, scalarRead] using built
              subst source
              rw [identifier_tail_one, scalar_print _ _ _ scalarRead]
              rfl
      | cons second tail =>
          cases scalarRead : scalar? "DlIdentifierRestScalar" character with
          | error reason =>
              rw [identifierTail?, scalarRead] at built <;> try simp
              cases built
          | ok leaf =>
              cases tailRead : identifierTail? (second :: tail) with
              | error reason =>
                  rw [identifierTail?, scalarRead, tailRead] at built <;> try simp
                  cases built
              | ok result =>
                  rw [identifierTail?, scalarRead, tailRead] at built <;> try simp
                  have same : node "identifier-tail-more" [leaf,result] = source := Except.ok.inj built
                  subst source
                  rw [identifier_tail_more, scalar_print _ _ _ scalarRead, ih result tailRead]
                  simp


theorem identifier_print (name : String) (source : Pattern)
    (built : identifier? name = .ok source) :
    CorePrinter.printText? "DlIdentifier" source = some name := by
  have notReserved := identifier_not_reserved name source built
  cases characters : name.toList with
  | nil => simp [identifier?, notReserved, characters] at built
  | cons character rest =>
      cases rest with
      | nil =>
          cases firstRead : scalar? "DlSingleIdentifierScalar" character with
          | error reason => simp [identifier?, notReserved, characters, firstRead] at built
          | ok leaf =>
              have same : node "identifier-one" [leaf] = source := by
                simpa [identifier?, notReserved, characters, firstRead] using built
              subst source
              rw [identifier_one, scalar_print _ _ _ firstRead]
              exact congrArg some (by simpa using (congrArg String.ofList characters).symm)
      | cons second tail =>
          cases firstRead : scalar? "DlIdentifierFirstScalar" character with
          | error reason =>
              simp only [identifier?, notReserved, characters, firstRead] at built
              cases built
          | ok leaf =>
              cases tailRead : identifierTail? (second :: tail) with
              | error reason =>
                  simp only [identifier?, notReserved, characters, firstRead, tailRead] at built
                  cases built
              | ok result =>
                  simp only [identifier?, notReserved, characters, firstRead, tailRead] at built
                  have same : node "identifier-more" [leaf,result] = source := Except.ok.inj built
                  subst source
                  rw [identifier_more, scalar_print _ _ _ firstRead, identifier_tail_print _ _ tailRead]
                  simp only [Option.pure_def]
                  simpa using (congrArg String.ofList characters).symm


theorem integer_negative (child : Pattern) :
    CorePrinter.printText? "DlInteger" (node "integer-negative" [child]) =
      (CorePrinter.printText? "DlDigits" child).map ("-" ++ ·) := by
  unfold CorePrinter.printText? CorePrinter.printScalars? node
  rw [print?_structural _ _ _ _ _ _ (SourceViews.grammar.terms.get ⟨56,by decide⟩)
    (by decide +kernel) (by decide +kernel)]
  have layout : (SourceViews.grammar.terms.get ⟨56,by decide⟩).syntaxPattern =
      [.terminal "-",.nonTerminal "digits"] := by decide +kernel
  have parameter : paramSort? (SourceViews.grammar.terms.get ⟨56,by decide⟩) "digits" =
      some "DlDigits" := by decide +kernel
  rw [layout]
  simp only [printItems?, parameter]

  cases read : DeclaredConstructorPrinter.print? SourceViews.grammar
    LanguageDefScalarPrinter.stringScalars CorePrinter.lexical "DlDigits" child <;> simp [read, LanguageDefScalarPrinter.stringScalars]

theorem unsigned_decimal (child : Pattern) :
    CorePrinter.printText? "DlUnsigned" (node "unsigned-decimal" [child]) =
      (CorePrinter.printText? "DlDigits" child).map (· ++ "u") := by
  unfold CorePrinter.printText? CorePrinter.printScalars? node
  rw [print?_structural _ _ _ _ _ _ (SourceViews.grammar.terms.get ⟨61,by decide⟩)
    (by decide +kernel) (by decide +kernel)]
  have layout : (SourceViews.grammar.terms.get ⟨61,by decide⟩).syntaxPattern =
      [.nonTerminal "digits",.terminal "u"] := by decide +kernel
  have parameter : paramSort? (SourceViews.grammar.terms.get ⟨61,by decide⟩) "digits" =
      some "DlDigits" := by decide +kernel
  rw [layout]
  simp only [printItems?, parameter]

  cases read : DeclaredConstructorPrinter.print? SourceViews.grammar
    LanguageDefScalarPrinter.stringScalars CorePrinter.lexical "DlDigits" child <;> simp [read, LanguageDefScalarPrinter.stringScalars]

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter
