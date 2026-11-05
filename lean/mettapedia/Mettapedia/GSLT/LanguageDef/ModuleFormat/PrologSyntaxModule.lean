import Mettapedia.GSLT.LanguageDef.ModuleFormat.PrologSyntax

/-! Shared grammar plus separate ISO/SWI module profiles, emitted through
the ordinary module printer. Configuration is retained as an authored data
reply; no new module envelope or parser ABI is introduced. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.PrologSyntaxModule

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Logic.Prolog ReaderProfile ReaderOperator
open ModuleSource

def atom (text : String) : Pattern := .apply text []
def list (values : List Pattern) : Pattern := values.foldr (fun x xs => .apply "LCons" [x,xs]) (atom "LNil")
def quoted (mode : QuotedText) : Pattern := atom (match mode with
  | .atom => "atom" | .chars => "chars" | .codes => "codes" | .string => "string")
def fixity (mode : Specifier) : String := match mode with
  | .fx => "fx" | .fy => "fy" | .xf => "xf" | .yf => "yf"
  | .xfx => "xfx" | .xfy => "xfy" | .yfx => "yfx"

def profileData (profile : Profile) : Pattern := .apply "PrologReaderProfileV1" [
  atom (if profile.dialect == .iso then "iso" else "swi"), quoted profile.doubleQuotes,
  profile.backQuotes.elim (atom "none") (fun q => .apply "some" [quoted q]),
  atom (toString profile.zeroArityCompounds), atom (toString profile.digitSeparators),
  list (profile.operators.map fun op => .apply "Operator" [atom op.name, atom (toString op.priority.value), atom (fixity op.specifier)])]

private def quote? (data : Pattern) : Option QuotedText := match SourceSyntax.string? data with
  | some "atom" => some .atom | some "chars" => some .chars
  | some "codes" => some .codes | some "string" => some .string | _ => none
private def fixity? (data : Pattern) : Option Specifier := match SourceSyntax.string? data with
  | some "fx" => some .fx | some "fy" => some .fy | some "xf" => some .xf | some "yf" => some .yf
  | some "xfx" => some .xfx | some "xfy" => some .xfy | some "yfx" => some .yfx | _ => none
private def bool? (data : Pattern) : Option Bool := match SourceSyntax.string? data with
  | some "true" => some true | some "false" => some false | _ => none
private def operator? : Pattern → Option Declaration
  | .apply "Operator" [name, priority, specifier] => do
      let name ← SourceSyntax.string? name
      let p ← (SourceSyntax.string? priority).bind String.toNat?
      let mode ← fixity? specifier
      if positive : 0 < p then
        if bounded : p ≤ 1200 then some ⟨name, ⟨p, positive, bounded⟩, mode⟩ else none
      else none
  | _ => none

private def dialect? (data : Pattern) : Option Dialect := match SourceSyntax.string? data with
  | some "iso" => some .iso | some "swi" => some .swi | _ => none
private def back? : Pattern → Option (Option QuotedText)
  | .apply "none" [] => some none | .apply "some" [q] => some <$> quote? q | _ => none

def readProfile? : Pattern → Option Profile
  | .apply "PrologReaderProfileV1" [dialect, dq, bq, zero, separators, ops] => do
      let dialect ← dialect? dialect
      let doubleQuotes ← quote? dq
      let backQuotes ← back? bq
      pure ⟨dialect, doubleQuotes, backQuotes, ← bool? zero, ← bool? separators, ← SourceSyntax.list? operator? ops⟩
  | _ => none

private theorem operator_roundtrip (op : Declaration) : operator?
    (.apply "Operator" [atom op.name,atom (toString op.priority.value),atom (fixity op.specifier)]) = some op := by
  rcases op with ⟨name,⟨priority,positive,bounded⟩,mode⟩
  cases mode <;> simp [operator?, atom, SourceSyntax.string?, fixity, fixity?, positive, bounded]

private theorem list_roundtrip {α : Type} (encode : α → Pattern) (decode : Pattern → Option α)
    (exact : ∀ x, decode (encode x) = some x) (xs : List α) :
    SourceSyntax.list? decode (list (xs.map encode)) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      change (decode (encode x)).bind (fun head =>
        (SourceSyntax.list? decode (list (xs.map encode))).bind (fun tail => some (head :: tail))) = some (x :: xs)
      rw [exact x]
      change (SourceSyntax.list? decode (list (xs.map encode))).bind (fun tail => some (x :: tail)) = some (x :: xs)
      rw [ih]
      rfl

private theorem operators_roundtrip (ops : Table) : SourceSyntax.list? operator?
    (list (ops.map fun op => .apply "Operator" [atom op.name,atom (toString op.priority.value),atom (fixity op.specifier)])) =
      some ops := list_roundtrip _ _ operator_roundtrip ops

private theorem quoted_roundtrip (q : QuotedText) : quote? (quoted q) = some q := by cases q <;> rfl
private theorem bool_roundtrip (b : Bool) : bool? (atom (toString b)) = some b := by cases b <;> rfl

private theorem dialect_read (d : Dialect) :
    dialect? (atom (if d == .iso then "iso" else "swi")) = some d := by cases d <;> rfl

private theorem back_read (b : Option QuotedText) :
    back? (b.elim (atom "none") (fun q => .apply "some" [quoted q])) = some b := by
  cases b with
  | none => rfl
  | some q => change some <$> quote? (quoted q) = some (some q); rw [quoted_roundtrip]; rfl

theorem profile_roundtrip (profile : Profile) : readProfile? (profileData profile) = some profile := by
  rcases profile with ⟨dialect,dq,bq,zero,separators,ops⟩
  simp only [profileData, readProfile?, dialect_read, quoted_roundtrip, back_read,
    bool_roundtrip, operators_roundtrip]
  rfl

private def constructors : Pattern → List (String × Nat)
  | .apply label args => (label,args.length) :: args.flatMap constructors
  | _ => []

def dataTheory (name request port : String) (payload : Pattern) : Theory :=
  let symbols := ((request,0) :: constructors payload).eraseDups
  { name, params := [], body := .extend none [
      .types [TypeDecl.plain "ProfileData"],
      .terms (symbols.map fun (label, arity) =>
        {label, category := "ProfileData",
         params := (List.range arity).map fun i => .simple ("a" ++ toString i) (.base "ProfileData"),
         syntaxPattern := []}),
      .rewrites [⟨port, [], [], atom request, payload, none⟩]] }

def filterData : SourceSyntax.FamilyFilter → Pattern
  | .rejectWords sort words => .apply "RejectWords" [atom sort, list (words.map atom)]
  | .maximalToken sort points openers => .apply "MaximalToken" [atom sort,
      list (points.map (atom ∘ toString)), list (openers.map atom)]
  | .maximalExcept sort points openers => .apply "MaximalExcept" [atom sort,
      list (points.map (atom ∘ toString)), list (openers.map atom)]

def common : ModuleSource.Module := {
  name := "PrologCommonSyntax", imports := [], entry := some (["Grammar"], [])
  theories := [⟨"Grammar", [], .extend none [
    .types ((PrologSyntax.sorts PrologSyntax.commonRows).map TypeDecl.plain),
    .terms PrologSyntax.commonRows]⟩] }

def moduleWithRows (profile : Profile) (extra : List GrammarRule) (start name : String) : ModuleSource.Module :=
  let description := PrologSyntax.extended profile extra start name
  {
  name
  imports := [⟨"PrologCommonSyntax.module", "common"⟩], entry := some (["Grammar"], [])
  theories := [
    ⟨"Grammar", [], .extend (some (.apply ["common","Grammar"] [])) [
      .types ((description.grammar.types.filter
        (fun sort => !(PrologSyntax.sorts PrologSyntax.commonRows).contains sort.name))),
      .terms (PrologSyntax.extensionRows profile ++ PrologSyntax.operatorRows profile ++ extra)]⟩,
    dataTheory "LexicalProfile" "GetLexicalProfile" "ReturnLexicalProfile" (Portable.lexicalData description.profile),
    dataTheory "SourceSelection" "GetSourceSelection" "ReturnSourceSelection"
      (.apply "SourceSelectionV1" [list ((PrologSyntax.selection profile).map filterData)]),
    dataTheory "ReaderProfile" "GetPrologReaderProfile" "ReturnPrologReaderProfile" (profileData profile)] }

def module (profile : Profile) : ModuleSource.Module :=
  let name := if profile.dialect == .iso then "ISOSyntax" else "SWISyntax"
  { moduleWithRows profile [] "PlSentence" (PrologSyntax.grammar profile).name with name }

def profile? (library : List (String × ModuleSource.Module)) (module : ModuleSource.Module) : Option Profile := do
  let (_, payload) ← SourceSyntax.replyAt? library module "ReaderProfile" "ReturnPrologReaderProfile"
    (atom "GetPrologReaderProfile")
  readProfile? payload

#guard readProfile? (profileData iso) = some iso
#guard readProfile? (profileData swi) = some swi

end Mettapedia.GSLT.LanguageDef.ModuleFormat.PrologSyntaxModule
