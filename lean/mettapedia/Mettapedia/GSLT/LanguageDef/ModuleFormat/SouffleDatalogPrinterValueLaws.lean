import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterTextLaws
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterSymbolLaws
import Mettapedia.Languages.Datalog.NumericPrinting

/-! Every successfully printed scalar recovers the same independent value
through source projection and literal interpretation. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.Datalog

theorem source_integer_decimal (child : Pattern) :
    Frontend.sourceText? (node "integer-decimal" [child]) =
      CorePrinter.printText? "DlInteger" (node "integer-decimal" [child]) := by
  change Frontend.sourceText? (.apply "dl-src:integer-decimal" [child]) =
    CorePrinter.printText? "DlInteger" (.apply "dl-src:integer-decimal" [child])
  simp only [Frontend.sourceText?]
  have selected : SourceViews.grammar.terms.find? (·.label == "dl-src:integer-decimal") =
      some (SourceViews.grammar.terms.get ⟨55,by decide⟩) := by decide +kernel
  have category : (SourceViews.grammar.terms.get ⟨55,by decide⟩).category = "DlInteger" := by decide +kernel
  simp only [selected, Option.bind_eq_bind, Option.bind_some, category]

theorem source_integer_negative (child : Pattern) :
    Frontend.sourceText? (node "integer-negative" [child]) =
      CorePrinter.printText? "DlInteger" (node "integer-negative" [child]) := by
  change Frontend.sourceText? (.apply "dl-src:integer-negative" [child]) =
    CorePrinter.printText? "DlInteger" (.apply "dl-src:integer-negative" [child])
  simp only [Frontend.sourceText?]
  have selected : SourceViews.grammar.terms.find? (·.label == "dl-src:integer-negative") =
      some (SourceViews.grammar.terms.get ⟨56,by decide⟩) := by decide +kernel
  have category : (SourceViews.grammar.terms.get ⟨56,by decide⟩).category = "DlInteger" := by decide +kernel
  simp only [selected, Option.bind_eq_bind, Option.bind_some, category]

theorem source_unsigned_decimal (child : Pattern) :
    Frontend.sourceText? (node "unsigned-decimal" [child]) =
      CorePrinter.printText? "DlUnsigned" (node "unsigned-decimal" [child]) := by
  change Frontend.sourceText? (.apply "dl-src:unsigned-decimal" [child]) =
    CorePrinter.printText? "DlUnsigned" (.apply "dl-src:unsigned-decimal" [child])
  simp only [Frontend.sourceText?]
  have selected : SourceViews.grammar.terms.find? (·.label == "dl-src:unsigned-decimal") =
      some (SourceViews.grammar.terms.get ⟨61,by decide⟩) := by decide +kernel
  have category : (SourceViews.grammar.terms.get ⟨61,by decide⟩).category = "DlUnsigned" := by decide +kernel
  simp only [selected, Option.bind_eq_bind, Option.bind_some, category]

theorem read_negative_digits (number : Int) (digits : Pattern)
    (negative : number < 0) (fits : Mettapedia.Languages.Datalog.Value.fits64 (.number number) = true)
    (printed : CorePrinter.printText? "DlDigits" digits = some number.natAbs.repr) :
    Frontend.value? "IntegerValue" (node "integer-negative" [digits]) = some (IRCodec.value (.number number)) := by
  have signed : -Int.ofNat number.natAbs = number := (Int.eq_neg_natAbs_of_nonpos (by omega)).symm
  change ((Frontend.sourceText? (node "integer-negative" [digits])).bind fun spelling =>
    (NumericSpelling.readInteger? spelling).bind fun value =>
      if Mettapedia.Languages.Datalog.Value.fits64 (.number value) then some (IRCodec.value (.number value)) else none) = _
  rw [source_integer_negative, integer_negative, printed]
  simp only [Option.map_some, Option.bind_some, NumericSpelling.integer_negative_repr, signed, fits, ↓reduceIte]

theorem read_decimal_digits (number : Int) (digits : Pattern)
    (nonnegative : 0 ≤ number) (fits : Mettapedia.Languages.Datalog.Value.fits64 (.number number) = true)
    (printed : CorePrinter.printText? "DlDigits" digits = some number.natAbs.repr) :
    Frontend.value? "IntegerValue" (node "integer-decimal" [digits]) = some (IRCodec.value (.number number)) := by
  have signed : Int.ofNat number.natAbs = number := (Int.eq_natAbs_of_nonneg nonnegative).symm
  change ((Frontend.sourceText? (node "integer-decimal" [digits])).bind fun spelling =>
    (NumericSpelling.readInteger? spelling).bind fun value =>
      if Mettapedia.Languages.Datalog.Value.fits64 (.number value) then some (IRCodec.value (.number value)) else none) = _
  rw [source_integer_decimal, integer_decimal, printed]
  simp only [Option.bind_some, NumericSpelling.integer_nat_repr, signed, fits, ↓reduceIte]

theorem read_unsigned_digits (number : Nat) (digits : Pattern)
    (fits : Mettapedia.Languages.Datalog.Value.fits64 (.unsigned number) = true)
    (printed : CorePrinter.printText? "DlDigits" digits = some number.repr) :
    Frontend.value? "UnsignedValue" (node "unsigned-decimal" [digits]) = some (IRCodec.value (.unsigned number)) := by
  change ((Frontend.sourceText? (node "unsigned-decimal" [digits])).bind fun spelling =>
    (NumericSpelling.readUnsigned? spelling).bind fun value =>
      if Mettapedia.Languages.Datalog.Value.fits64 (.unsigned value) then some (IRCodec.value (.unsigned value)) else none) = _
  rw [source_unsigned_decimal, unsigned_decimal, printed]
  simp only [Option.map_some, Option.bind_some, NumericSpelling.unsigned_repr, fits, ↓reduceIte]

theorem value_read (value : Mettapedia.Languages.Datalog.Value) (source : Pattern) (built : value? value = .ok source) :
    (ProgramProjection.Reference.constant? source).bind Frontend.normalize? = some (IRCodec.value value) := by
  cases value with
  | symbol text =>
      cases bodyRead : symbolBody? text.toList with
      | error reason => simp [value?, bodyRead] at built
      | ok body =>
          have same : node "constant-symbol" [node "symbol" [body]] = source := by
            simpa [value?, bodyRead] using built
          subst source
          change Frontend.value? "SymbolValue" (.apply "dl-src:symbol" [body]) = _
          simp only [Frontend.value?, symbol_body_read _ _ bodyRead, Option.bind_eq_bind,
            Option.bind_some, String.ofList_toList]
          rfl
  | number number =>
      by_cases fits : Mettapedia.Languages.Datalog.Value.fits64 (.number number) = true
      · cases digitsRead : digits? number.natAbs.repr.toList with
        | error reason =>
            simp only [value?, fits, ↓reduceIte, digitsRead] at built
            cases built
        | ok digits =>
            simp only [value?, fits, ↓reduceIte, digitsRead] at built
            have same : node "constant-integer"
                [node (if number < 0 then "integer-negative" else "integer-decimal") [digits]] = source :=
              Except.ok.inj built
            subst source
            have printed : CorePrinter.printText? "DlDigits" digits = some number.natAbs.repr := by
              simpa only [String.ofList_toList] using digits_print _ _ digitsRead
            by_cases negative : number < 0
            · rw [if_pos negative]
              exact read_negative_digits number digits negative fits printed
            · rw [if_neg negative]
              exact read_decimal_digits number digits (by omega) fits printed
      · simp only [value?, fits] at built
        cases built
  | unsigned number =>
      by_cases fits : Mettapedia.Languages.Datalog.Value.fits64 (.unsigned number) = true
      · cases digitsRead : digits? number.repr.toList with
        | error reason =>
            simp only [value?, fits, ↓reduceIte, digitsRead] at built
            cases built
        | ok digits =>
            simp only [value?, fits, ↓reduceIte, digitsRead] at built
            have same : node "constant-unsigned" [node "unsigned-decimal" [digits]] = source := Except.ok.inj built
            subst source
            exact read_unsigned_digits number digits fits (by
              simpa only [String.ofList_toList] using digits_print _ _ digitsRead)
      · simp only [value?, fits] at built
        cases built
  | floating _ => cases built


theorem qualified_name_read (names : List String) (source : Pattern)
    (built : qualifiedName? names = .ok source) : Frontend.qualifiedName? source = some names := by
  induction names generalizing source with
  | nil => cases built
  | cons name rest ih =>
      cases rest with
      | nil =>
          cases read : identifier? name with
          | error reason => simp [qualifiedName?, read] at built
          | ok identifier =>
              have same : node "qualified-name-one" [identifier] = source := by
                simpa [qualifiedName?, read] using built
              subst source
              change (CorePrinter.printText? "DlIdentifier" identifier).bind (fun text => some [text]) = _
              rw [identifier_print _ _ read]
              rfl
      | cons second tail =>
          cases read : identifier? name with
          | error reason =>
              rw [qualifiedName?, read] at built <;> try simp
              cases built
          | ok identifier =>
              cases remaining : qualifiedName? (second :: tail) with
              | error reason =>
                  rw [qualifiedName?, read, remaining] at built <;> try simp
                  cases built
              | ok restSource =>
                  rw [qualifiedName?, read, remaining] at built <;> try simp
                  have same : node "qualified-name-more" [identifier,restSource] = source := Except.ok.inj built
                  subst source
                  change ((CorePrinter.printText? "DlIdentifier" identifier).bind fun text =>
                    (Frontend.qualifiedName? restSource).bind fun names => some (text :: names)) = _
                  rw [identifier_print _ _ read, ih _ remaining]
                  rfl

theorem source_identifier_one (first : Pattern) :
    Frontend.sourceText? (node "identifier-one" [first]) = CorePrinter.printText? "DlIdentifier" (node "identifier-one" [first]) := by
  change Frontend.sourceText? (.apply "dl-src:identifier-one" [first]) =
    CorePrinter.printText? "DlIdentifier" (.apply "dl-src:identifier-one" [first])
  simp only [Frontend.sourceText?]
  have selected : SourceViews.grammar.terms.find? (·.label == "dl-src:identifier-one") =
      some (SourceViews.grammar.terms.get ⟨51,by decide⟩) := by decide +kernel
  have category : (SourceViews.grammar.terms.get ⟨51,by decide⟩).category = "DlIdentifier" := by decide +kernel
  simp only [selected, Option.bind_eq_bind, Option.bind_some, category]

theorem source_identifier_more (first second : Pattern) :
    Frontend.sourceText? (node "identifier-more" [first,second]) = CorePrinter.printText? "DlIdentifier" (node "identifier-more" [first,second]) := by
  change Frontend.sourceText? (.apply "dl-src:identifier-more" [first,second]) =
    CorePrinter.printText? "DlIdentifier" (.apply "dl-src:identifier-more" [first,second])
  simp only [Frontend.sourceText?]
  have selected : SourceViews.grammar.terms.find? (·.label == "dl-src:identifier-more") =
      some (SourceViews.grammar.terms.get ⟨52,by decide⟩) := by decide +kernel
  have category : (SourceViews.grammar.terms.get ⟨52,by decide⟩).category = "DlIdentifier" := by decide +kernel
  simp only [selected, Option.bind_eq_bind, Option.bind_some, category]

theorem identifier_source_text (name : String) (source : Pattern)
    (built : identifier? name = .ok source) : Frontend.sourceText? source = some name := by
  have notReserved := identifier_not_reserved name source built
  have printed := identifier_print name source built
  cases chars : name.toList with
  | nil => simp [identifier?, notReserved, chars] at built
  | cons first rest =>
      cases rest with
      | nil =>
          cases head : scalar? "DlSingleIdentifierScalar" first with
          | error reason => simp [identifier?, notReserved, chars, head] at built
          | ok leaf =>
              have same : node "identifier-one" [leaf] = source := by simpa [identifier?, notReserved, chars, head] using built
              subst source
              rw [source_identifier_one]
              exact printed
      | cons second tail =>
          cases head : scalar? "DlIdentifierFirstScalar" first with
          | error reason =>
              simp only [identifier?, notReserved, chars, head] at built
              cases built
          | ok leaf =>
              cases restRead : identifierTail? (second :: tail) with
              | error reason =>
                  simp only [identifier?, notReserved, chars, head, restRead] at built
                  cases built
              | ok restSource =>
                  simp only [identifier?, notReserved, chars, head, restRead] at built
                  have same : node "identifier-more" [leaf,restSource] = source := Except.ok.inj built
                  subst source
                  rw [source_identifier_more]
                  exact printed

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter
