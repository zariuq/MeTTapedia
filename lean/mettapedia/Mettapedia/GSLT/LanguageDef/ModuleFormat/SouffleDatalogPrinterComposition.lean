import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogPrinterValueLaws
import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogNormalizationMeaning

/-! List and constructor composition for the independent-program source
printer. These laws retain field order and duplicate occurrences. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 200000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.Datalog

theorem mapM_read {α : Type} (build : α → Except String Pattern)
    (read : Pattern → Option Pattern) (encode : α → Pattern)
    (exact : ∀ value source, build value = .ok source → read source = some (encode value))
    (values : List α) (sources : List Pattern) (built : values.mapM build = .ok sources) :
    sources.mapM read = some (values.map encode) := by
  induction values generalizing sources with
  | nil => cases Except.ok.inj built; rfl
  | cons value rest ih =>
      cases first : build value with
      | error reason =>
          rw [List.mapM_cons, first] at built
          cases built
      | ok source =>
          cases remaining : rest.mapM build with
          | error reason =>
              rw [List.mapM_cons, first, remaining] at built
              cases built
          | ok tail =>
              rw [List.mapM_cons, first, remaining] at built
              have same : source :: tail = sources := Except.ok.inj built
              subst sources
              simp [exact value source first, ih tail remaining]

theorem normalize_children_mapM (sources : List Pattern) :
    Frontend.normalizeChildren? sources = sources.mapM Frontend.normalize? := by
  induction sources with
  | nil => rfl
  | cons first rest ih => simp [Frontend.normalizeChildren?, ih]

theorem separated_read (emptyName oneName moreName : String)
    (readList : Pattern → Option (List Pattern)) (read : Pattern → Option Pattern)
    (emptyRead : readList (node emptyName []) = some [])
    (oneRead : ∀ first, readList (node oneName [first,empty]) = (read first).map (· :: []))
    (moreRead : ∀ first tail, readList (node moreName [first,empty,space,tail]) = do
      let head ← read first
      let rest ← readList tail
      pure (head :: rest))
    (sources : List Pattern) : readList (separated emptyName oneName moreName sources) = sources.mapM read := by
  cases sources with
  | nil => exact emptyRead
  | cons first rest =>
      change readList (nonemptySeparated oneName moreName first rest) = (first :: rest).mapM read
      induction rest generalizing first with
      | nil =>
          rw [nonemptySeparated, oneRead]
          cases result : read first <;> simp [List.mapM_cons, result]
      | cons second tail ih => simp [nonemptySeparated, moreRead, ih]

theorem argument_read (argument : Argument) (source : Pattern) (built : argument? argument = .ok source) :
    (ProgramProjection.Reference.term? source).bind Frontend.normalize? = some (IRCodec.argument argument) := by
  cases argument with
  | anonymous =>
      cases Except.ok.inj built
      rfl
  | literal value =>
      cases valueRead : value? value with
      | error reason => simp [argument?, valueRead] at built
      | ok valueSource =>
          have same : node "term-constant" [valueSource] = source := by simpa [argument?, valueRead] using built
          subst source
          have read := value_read value valueSource valueRead
          cases projected : ProgramProjection.Reference.constant? valueSource with
          | none => simp [projected] at read
          | some valueCode =>
              simp only [projected, Option.bind_some] at read
              change ((ProgramProjection.Reference.constant? valueSource).map
                (fun code => Pattern.apply "ValueArgument" [code])).bind Frontend.normalize? = _
              rw [projected]
              change Frontend.normalize? (.apply "ValueArgument" [valueCode]) = _
              rw [SourceMeaning.plain_normalization _ _ (by simp [SourceMeaning.PlainNode])]
              simp only [Frontend.normalizeChildren?, read, Option.bind_eq_bind, Option.bind_some]
              rfl
  | var name =>
      cases nameRead : identifier? name with
      | error reason => simp [argument?, nameRead] at built
      | ok identifier =>
          have same : node "term-variable" [identifier] = source := by simpa [argument?, nameRead] using built
          subst source
          change (some (.apply "VariableArgument" [.apply "Variable" [identifier]])).bind Frontend.normalize? = _
          change Frontend.normalize? (.apply "VariableArgument" [.apply "Variable" [identifier]]) = _
          rw [SourceMeaning.plain_normalization _ _ (by simp [SourceMeaning.PlainNode])]
          have logical : Frontend.normalize? (.apply "Variable" [identifier]) =
              some (.apply "Variable" [IRCodec.atom name]) := by
            simp only [Frontend.normalize?, identifier_source_text name identifier nameRead,
              Option.bind_eq_bind, Option.bind_some]
            rfl
          simp only [Frontend.normalizeChildren?, logical, Option.bind_eq_bind, Option.bind_some]
          rfl


theorem mapM_bind {α β γ : Type} (first : α → Option β) (second : β → Option γ) (values : List α) :
    ((values.mapM first).bind fun intermediates => intermediates.mapM second) =
      values.mapM (fun value => (first value).bind second) := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp only [List.mapM_cons]
      cases head : first value with
      | none => simp
      | some intermediate =>
          cases tail : rest.mapM first with
          | none =>
              simp only [tail, Option.bind_none] at ih
              rw [← ih]
              cases next : second intermediate <;> simp [next]
          | some intermediates =>
              simp only [tail, Option.bind_some] at ih
              cases next : second intermediate <;> simp [ih, next]

theorem separated_normalize {α : Type} (emptyName oneName moreName : String)
    (readList : Pattern → Option (List Pattern)) (read : Pattern → Option Pattern)
    (listLaw : ∀ sources, readList (separated emptyName oneName moreName sources) = sources.mapM read)
    (build : α → Except String Pattern) (encode : α → Pattern)
    (itemLaw : ∀ value source, build value = .ok source → (read source).bind Frontend.normalize? = some (encode value))
    (values : List α) (sources : List Pattern) (built : values.mapM build = .ok sources) :
    (readList (separated emptyName oneName moreName sources)).bind Frontend.normalizeChildren? =
      some (values.map encode) := by
  rw [listLaw]
  simp_rw [normalize_children_mapM]
  rw [mapM_bind]
  exact mapM_read build _ encode itemLaw values sources built

theorem constants_read (values : List Mettapedia.Languages.Datalog.Value) (sources : List Pattern)
    (built : values.mapM value? = .ok sources) :
    (ProgramProjection.Reference.constants? (separated "constants-empty" "constants-one" "constants-more" sources)).bind
      Frontend.normalizeChildren? = some (values.map IRCodec.value) := by
  apply separated_normalize _ _ _ _ ProgramProjection.Reference.constant? _ value? IRCodec.value value_read values sources built
  intro items
  exact separated_read _ _ _ _ _ rfl (fun _ => rfl) (fun _ _ => rfl) items

theorem arguments_read (values : List Argument) (sources : List Pattern)
    (built : values.mapM argument? = .ok sources) :
    (ProgramProjection.Reference.terms? (separated "terms-empty" "terms-one" "terms-more" sources)).bind
      Frontend.normalizeChildren? = some (values.map IRCodec.argument) := by
  apply separated_normalize _ _ _ _ ProgramProjection.Reference.term? _ argument? IRCodec.argument argument_read values sources built
  intro items
  exact separated_read _ _ _ _ _ rfl (fun _ => rfl) (fun _ _ => rfl) items

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourcePrinter
