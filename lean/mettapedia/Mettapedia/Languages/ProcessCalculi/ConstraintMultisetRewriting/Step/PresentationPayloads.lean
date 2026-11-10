import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Presentation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.BindingTrees
import Mettapedia.GSLT.Parsing.ExactPresentation
import Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler
import Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews

/-! # Canonical payload syntax from the authored transform module

`Tcalc.Syntax` in the same module presents binding trees, rule instances,
selections and configurations. This file interprets its binding-tree rows in
the existing signature-indexed ABT carrier. Object indices, structural heads,
schematic-hole tags and quoted-rule handles have distinct constructors.

Reading syntax does not instantiate a schematic hole or activate quoted code.
Scope and field-depth conformance are checked against an explicit signature
and ambient depth. The exact presentation here is the structural AST boundary;
raw source parsing and operational interpretation remain separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Payloads

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.ModuleSource
open Mettapedia.GSLT.Parsing
open scoped Mettapedia.GSLT.LanguageDef.ModuleSource.ComputedViews

abbrev ABT := Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.Term
abbrev ABTFields := Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.Fields

def dataLanguage : LanguageDef :=
  module_language_view% (elaborateTheory Tcalc.library Tcalc.module ["Syntax"]).toOption

theorem data_elaborates : elaborateTheory Tcalc.library Tcalc.module ["Syntax"] =
    .ok dataLanguage := rfl

def binding : LanguageDefSyntaxCompiler.Binding where
  literalRef token := some token
  lexicalSortRef _ := none
  categoryRef := id
  ruleRef := id

def rules : List LanguageDefSyntaxCompiler.CompiledRule :=
  (LanguageDefSyntaxCompiler.compileRules? binding dataLanguage).get (by decide +kernel)

theorem data_compiles : LanguageDefSyntaxCompiler.compileRules? binding dataLanguage =
    some rules := by decide +kernel

inductive Head where
  | symbol (index : Nat)
  | name (index : Nat)
  | hole (index : Nat)
  | quotedRule (index : Nat)
  deriving DecidableEq, Repr

abbrev Term := ABT Head
abbrev Fields := ABTFields Head

def indexPattern : Nat → Pattern
  | 0 => .apply "TcZero" []
  | n + 1 => .apply "TcSucc" [indexPattern n]

def readIndex : Pattern → Option Nat
  | .apply "TcZero" [] => some 0
  | .apply "TcSucc" [n] => Nat.succ <$> readIndex n
  | _ => none

theorem readIndex_pattern (index : Nat) : readIndex (indexPattern index) = some index := by
  induction index with
  | zero => rfl
  | succ index ih => simp [indexPattern, readIndex, ih]

def headPattern : Head → Pattern
  | .symbol n => .apply "TcSymbol" [indexPattern n]
  | .name n => .apply "TcName" [indexPattern n]
  | .hole n => .apply "TcHole" [indexPattern n]
  | .quotedRule n => .apply "TcQuotedRule" [indexPattern n]

def readHead : Pattern → Option Head
  | .apply "TcSymbol" [n] => Head.symbol <$> readIndex n
  | .apply "TcName" [n] => Head.name <$> readIndex n
  | .apply "TcHole" [n] => Head.hole <$> readIndex n
  | .apply "TcQuotedRule" [n] => Head.quotedRule <$> readIndex n
  | _ => none

theorem readHead_pattern (head : Head) : readHead (headPattern head) = some head := by
  cases head <;> simp [headPattern, readHead, readIndex_pattern]

mutual
  def termPattern : Term → Pattern
    | .idx index => .apply "TcVar" [indexPattern index]
    | .node head fields => .apply "TcNode" [headPattern head, fieldsPattern fields]

  def fieldsPattern : Fields → Pattern
    | .nil => .apply "TcFieldsNil" []
    | .cons depth term rest => .apply "TcFieldsCons"
        [indexPattern depth, termPattern term, fieldsPattern rest]
end

mutual
  def readTerm : Pattern → Option Term
    | .apply "TcVar" [index] => (fun value => (.idx value : Term)) <$> readIndex index
    | .apply "TcNode" [head, fields] => do
        return .node (← readHead head) (← readFields fields)
    | _ => none

  def readFields : Pattern → Option Fields
    | .apply "TcFieldsNil" [] => some .nil
    | .apply "TcFieldsCons" [depth, term, rest] => do
        return .cons (← readIndex depth) (← readTerm term) (← readFields rest)
    | _ => none
end

mutual
  theorem readTerm_pattern (term : Term) : readTerm (termPattern term) = some term := by
    cases term with
    | idx index => simp [termPattern, readTerm, readIndex_pattern]
    | node head fields => simp [termPattern, readTerm, readHead_pattern, readFields_pattern fields]
  termination_by sizeOf term

  theorem readFields_pattern (fields : Fields) : readFields (fieldsPattern fields) = some fields := by
    cases fields with
    | nil => rfl
    | cons depth term rest =>
      simp [fieldsPattern, readFields, readIndex_pattern, readTerm_pattern term, readFields_pattern rest]
  termination_by sizeOf fields
end

theorem termPattern_injective : Function.Injective termPattern := by
  intro first second same
  have decoded := congrArg readTerm same
  simpa only [readTerm_pattern, Option.some.injEq] using decoded

def rawPresentation : ExactPresentation.Presentation (fun _ : Unit => Term) (fun _ => Pattern) where
  key := ⟨"tcalc.binding-tree", 1⟩
  expand := readTerm
  view := termPattern
  expand_view := readTerm_pattern

def Admitted (signature : Head → List Nat) (depth : Nat) (term : Term) : Prop :=
  term.supportedAt depth = true ∧ term.conforms signature = true

instance (signature : Head → List Nat) (depth : Nat) (term : Term) :
    Decidable (Admitted signature depth term) :=
  inferInstanceAs (Decidable (term.supportedAt depth = true ∧ term.conforms signature = true))

def readAdmitted (signature : Head → List Nat) (depth : Nat) (pattern : Pattern) :
    Option {term : Term // Admitted signature depth term} := do
  let term ← readTerm pattern
  if admitted : Admitted signature depth term then some ⟨term, admitted⟩ else none

def checkedPresentation (signature : Head → List Nat) (depth : Nat) :
    ExactPresentation.Presentation (fun _ : Unit => {term : Term // Admitted signature depth term})
      (fun _ => Pattern) where
  key := ⟨"tcalc.checked-binding-tree", 1⟩
  expand := readAdmitted signature depth
  view term := termPattern term.1
  expand_view term := by
    simp [readAdmitted, readTerm_pattern, term.2]

theorem admitted_roundtrip (signature : Head → List Nat) (depth : Nat)
    (term : {term : Term // Admitted signature depth term}) :
    readAdmitted signature depth (termPattern term.1) = some term :=
  (checkedPresentation signature depth).expand_view (sort := ()) term

theorem stale_version_refused (term : Term) :
    ExactPresentation.expandDocument rawPresentation (sort := ())
      ⟨⟨"tcalc.binding-tree", 0⟩, termPattern term⟩ = none := rfl

theorem schematic_hole_is_not_object_index (index : Nat) :
    termPattern (.node (.hole index) .nil) ≠ termPattern (.idx index) := by
  intro same
  have impossible := termPattern_injective same
  cases impossible

theorem query_metavariable_is_not_payload : readTerm (.fvar "s") = none := rfl

theorem quoted_rule_tag_is_not_symbol (index : Nat) :
    headPattern (.quotedRule index) ≠ headPattern (.symbol index) := by
  intro same
  have decoded := congrArg readHead same
  simp only [readHead_pattern, Option.some.injEq] at decoded
  cases decoded

/-- A quoted-rule handle is inert data under the actual ambient substitution. -/
theorem quoted_rule_substitution_inert (index : Nat) (substitution : Nat → Term) :
    BindingTrees.action.apply substitution (.node (.quotedRule index) .nil) =
      .node (.quotedRule index) .nil := rfl

def unarySignature : Head → List Nat
  | .symbol _ => [1]
  | .name _ | .hole _ | .quotedRule _ => []

def boundIdentity : Term := .node (.symbol 0) (.cons 1 (.idx 0) .nil)
def wrongFieldDepth : Term := .node (.symbol 0) (.cons 0 (.idx 0) .nil)

theorem declared_binder_admitted : Admitted unarySignature 0 boundIdentity := by decide +kernel

theorem missing_binder_refused : readAdmitted unarySignature 0
    (termPattern wrongFieldDepth) = none := by
  simp [readAdmitted, readTerm_pattern, Admitted, wrongFieldDepth,
    Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.Term.supportedAt,
    Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.Term.Fields.supportedAt]

theorem extra_field_on_quoted_handle_refused : readAdmitted unarySignature 1
    (termPattern (.node (.quotedRule 0) (.cons 0 (.idx 0) .nil))) = none := by
  simp [readAdmitted, readTerm_pattern, Admitted, unarySignature,
    Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.Term.conforms,
    Mettapedia.GSLT.LanguageDef.SignatureIndexedABT.Term.Fields.conforms]

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Presentation.Payloads
