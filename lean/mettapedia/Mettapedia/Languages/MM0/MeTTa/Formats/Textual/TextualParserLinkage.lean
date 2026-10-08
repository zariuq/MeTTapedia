import Mettapedia.GSLT.Parsing.ParserPackSelectedValue
import Mettapedia.GSLT.Parsing.ParserPackTextArtifact
import Mettapedia.GSLT.Parsing.CanonicalSourceHornElaboration
import Mettapedia.Languages.MM0.MeTTa.Formats.Textual.TextualData

/-!
# MM0 authored syntax, fixed-head actions and included AST receipts

The syntax source and the ordered native ParserPack are quoted from their
actual artifacts. Their row identities and exact action shapes are retained.
The action bridge uses the existing fixed-head action decoder and executor;
raw `cons` / `cp` data is never evaluated into native expression containers.

The selected-receipt theorem has explicit exact-plan and complete-catalogue
premises. No such certificate is manufactured from a native accepted AST or
its digest. The actual MM0 guarded span and positive-peek extensions, native
forest export and byte/scalar inclusion transport require separate joins.
-/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000

namespace Mettapedia.Languages.MM0.MeTTa.TextualParserLinkage

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.Parsing
open ParserPackSelectedValue
open GrammarConstructorActions (Action)
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation
open scoped ParserPackTextArtifact

def syntaxSource : SExpr :=
  metta_sexpr_file% petta
    "../../../../../../../../../hyperon/cetta-mm0-metta-20261004/langdef/mm0/syntax_v1.metta"

def packSource : ParserPackTextArtifact.Artifact :=
  parser_pack_text_file%
    "../../../../../../../../../hyperon/cetta-mm0-metta-20261004/langdef/mm0/generated/parser_pack_v1.abi"

/-- Canonical structured source admission preserves the full authored rule
inventory. This is distinct from parsing an MM0 input with those rules. -/
def syntaxData : CanonicalSourceGSLT.Source :=
  (CanonicalSourceGSLT.decode syntaxSource).get (by rfl)

theorem actual_syntax_decoded :
    CanonicalSourceGSLT.decode syntaxSource = some syntaxData := by rfl

theorem actual_syntax_reencoded : CanonicalSourceGSLT.encode syntaxData = syntaxSource := by rfl

mutual
  /-- Structural interpretation of the existing wire carrier as PeTTa data. -/
  def value : CettaWire.Term → Atom
    | .symbol name => .symbol name
    | .string text => .grounded (.string text)
    | .natural number => .grounded (.int number)
    | .application head arguments => .expression (.symbol head :: values arguments)

  def values : List CettaWire.Term → List Atom
    | [] => []
    | first :: rest => value first :: values rest
end

mutual
  def lowerAction : Action → ConstructorAction
    | .slot index => .slot index
    | .constant literal => .constant (value literal)
    | .apply head arguments => .apply head (lowerArguments arguments)
    | .primitive impossible _ => nomatch impossible

  def lowerArguments : List Action → List ConstructorAction
    | [] => []
    | first :: rest => lowerAction first :: lowerArguments rest
end

mutual
  /-- Fixed-head execution commutes with raw data interpretation. -/
  theorem lowerAction_executes (slots : List CettaWire.Term) (action : Action) :
      execute (values slots) (lowerAction action) = (action.execute slots).map value := by
    cases action with
    | slot index =>
        simp [lowerAction, execute, Action.executeWith, Action.execute,
          show values slots = slots.map value by
            induction slots with
            | nil => rfl
            | cons first rest ih => simp [values, ih], List.getElem?_map]
    | constant literal => rfl
    | apply head arguments =>
        change (do let outputs ← executeArguments (values slots) (lowerArguments arguments)
                   pure (Atom.expression (.symbol head :: outputs))) = _
        rw [lowerArguments_execute]
        cases computed : GrammarConstructorActions.executeArguments slots arguments with
        | none => simp [Action.execute, computed]
        | some outputs => simp [Action.execute, computed, value]
    | primitive impossible _ => nomatch impossible

  theorem lowerArguments_execute (slots : List CettaWire.Term) (arguments : List Action) :
      executeArguments (values slots) (lowerArguments arguments) =
        (GrammarConstructorActions.executeArguments slots arguments).map values := by
    cases arguments with
    | nil => rfl
    | cons first rest =>
        change (do let output ← execute (values slots) (lowerAction first)
                   let outputs ← executeArguments (values slots) (lowerArguments rest)
                   pure (output :: outputs)) = _
        rw [lowerAction_executes, lowerArguments_execute]
        cases headEq : first.execute slots <;>
          cases tailEq : GrammarConstructorActions.executeArguments slots rest <;>
          simp [GrammarConstructorActions.executeArguments, headEq, tailEq, values]
end

mutual
  /-- The artifact's S-expression carrier uses canonical nonnegative integer
tokens. Symbol spellings remain symbols; strings and negative numbers are
outside this selected MM0 action artifact fragment. -/
  def wireTerm? : SExpr → Option CettaWire.Term
    | .atom token =>
        if CanonicalSourceHornElaboration.mayStartInteger token then
          match token.toNat? with
          | some number => if toString number = token then some (.natural number) else none
          | none => none
        else if token.startsWith "\"" then none else some (.symbol token)
    | .list (.atom head :: arguments) => do
        let rest ← wireTerms? arguments
        pure (.application head rest)
    | _ => none
  termination_by form => sizeOf form

  def wireTerms? : List SExpr → Option (List CettaWire.Term)
    | [] => some []
    | first :: rest => do
        let head ← wireTerm? first
        let tail ← wireTerms? rest
        pure (head :: tail)
  termination_by forms => sizeOf forms
end

def actionSyntax? : SExpr → Option SExpr
  | .list [.atom "pp-production", _, _, _, action] => some action
  | _ => none

/-- Admission invokes the existing fixed-head decoder, not a replacement
action language or a grammar-specific evaluator. -/
def productionAction? (production : SExpr) : Option ConstructorAction := do
  let form ← actionSyntax? production
  let wire ← wireTerm? form
  let action ← Action.decode wire
  pure (lowerAction action)

def sourceDefinition? (name : String) : Option SExpr :=
  match syntaxSource with
  | .list [.atom "gslt-presentation-v1", _, _, _, .list (.atom "rewrites" :: rows)] =>
      let definitions := rows.filterMap fun row =>
        match row with
        | .list [.atom "rule", _, .list [.atom "head", .list [.atom "definition", .atom candidate, body]],
            .list [.atom "body"]] => if candidate = name then some body else none
        | _ => none
      match definitions with
      | [definition] => some definition
      | _ => none
  | _ => none

theorem actual_pack_counts :
    packSource.productions.length = 557 ∧
    (ParserPackTextArtifact.rowsFor packSource "class-clause").length = 78 ∧
    (ParserPackTextArtifact.rowsFor packSource "production-evidence").length = 557 := by decide

theorem actual_pack_start :
    ParserPackTextArtifact.uniqueField? packSource "start" = some "(pp-def mm0-file)" ∧
    ParserPackTextArtifact.uniqueField? packSource "closure" = some "partial" := by decide

theorem actual_pack_digest :
    ParserPackTextArtifact.uniqueField? packSource "pack-digest" =
      some "36521f92f118f205a8a459034ceae58286601dc0a471630248ed2d8b9cd1b621" := by decide

/-- All actual base-pack rows have fixed-head actions in this fragment.
Guarded span extension rows are not covered by this base-table statement. -/
theorem actual_base_actions_admitted :
    (packSource.productions.map productionAction?).all Option.isSome = true := by
  simp [packSource, productionAction?, actionSyntax?, wireTerm?, wireTerms?,
    CanonicalSourceHornElaboration.mayStartInteger, Action.decode,
    GrammarConstructorActions.decodeArguments, GrammarConstructorActions.decodeIndex]

/-- Base actions are admitted as a whole ordered vector. A failed row is not
filtered from the vector, so every physical position remains stable. -/
def baseActions? : Option ActionTable :=
  (CanonicalSourceGSLT.decodeList productionAction? packSource.productions).map
    fun actions => ⟨[], actions⟩

theorem base_action_physical_position {actions : ActionTable}
    (admitted : baseActions? = some actions) (position : Nat) :
    actions.lexical = [] ∧ actions.structural[position]? =
      (packSource.productions[position]?).bind productionAction? := by
  obtain ⟨values, decoded, exactTable⟩ := Option.map_eq_some_iff.mp admitted
  subst actions
  exact ⟨rfl, CanonicalSourceGSLT.decodeList_getElem? productionAction? decoded position⟩

private theorem decoder_vector_isSome {β : Type} (decode : SExpr → Option β) (rows : List SExpr) :
    (CanonicalSourceGSLT.decodeList decode rows).isSome =
      (rows.map decode).all Option.isSome := by
  induction rows with
  | nil => rfl
  | cons first rest ih =>
      cases headEq : decode first <;>
        cases tailEq : CanonicalSourceGSLT.decodeList decode rest <;>
        simp_all [CanonicalSourceGSLT.decodeList]

theorem actual_base_action_vector_admitted : baseActions?.isSome = true := by
  simpa [baseActions?, decoder_vector_isSome] using actual_base_actions_admitted

theorem actual_file_definition :
    sourceDefinition? "mm0-file" = some
      (metta_sexpr% petta "(node mm0-file (right (ref mm0-skip) (left (star (ref mm0-statement)) eof)))") := by rfl

theorem actual_identifier_positive_peek :
    sourceDefinition? "mm0-identifier-lexeme" = some
      (metta_sexpr% petta "(left (ref mm0-identifier-raw) (peek (ref mm0-identifier-boundary)))") := by rfl

/-- The native receipt keeps the exact selected AST and opaque provenance.
The pack digest and canonical filename are metadata, not acceptance evidence. -/
def includedAst (canonical digest ast provenance : Atom) : Atom :=
  .expression [.symbol "MM0:IncludedAst", canonical, digest, ast, provenance]

def selectedIncludedAst? (actions : ActionTable) (input : List Nat) (rows : Catalogue)
    (canonical digest provenance : Atom) : Option Atom :=
  (selectCatalogue? actions input rows).map fun ast => includedAst canonical digest ast provenance

theorem selected_included_ast_reflects
    {literalScalars? : String → Option (List Nat)}
    {profile : ParserProfileSemantics.ParserProfileLayer}
    {rules : List LanguageDefSyntaxCompiler.CompiledRule}
    {plan : ClassAwareParserPackCorrespondence.CompiledParserPackPlan}
    {actions : ActionTable} {input : List Nat} {rows : Catalogue}
    {canonical digest provenance receipt : Atom}
    (agreement : ClassAwareParserPackCorrespondence.ParserPackPlanAgreement
      literalScalars? profile rules plan)
    (qualified : CompleteCatalogue profile plan input rows)
    (selected : selectedIncludedAst? actions input rows canonical digest provenance = some receipt) :
    ∃ ast, receipt = includedAst canonical digest ast provenance ∧
      (∃ row ∈ rows,
        Nonempty (ClassAwareParserPackCorrespondence.SourcePlanRootDerives
          literalScalars? profile rules input row.2) ∧ ValueReplays actions input row.1 ast) ∧
      UniqueRootValue profile plan actions input ast := by
  obtain ⟨ast, accepted, same⟩ := Option.map_eq_some_iff.mp selected
  refine ⟨ast, same.symm, (selectedCatalogue_reflects agreement qualified accepted).1, ?_⟩
  exact (selectCatalogue?_iff_uniqueRootValue qualified).mp accepted

theorem literal_raw_scalar_chain (number : Nat) :
    value (.application "cons" [.application "cp" [.natural number], .symbol "nil"]) =
      TextualData.scalarListValue [number] := rfl

theorem actual_file_action (body : Atom) :
    (((packSource.productions[20]?).bind productionAction?).bind fun action => execute [body] action) =
      some (Atom.expression [.symbol "node", .symbol "mm0-file", body]) := by
  simp [packSource, productionAction?, actionSyntax?, wireTerm?, wireTerms?,
    CanonicalSourceHornElaboration.mayStartInteger, Action.decode,
    GrammarConstructorActions.decodeArguments, GrammarConstructorActions.decodeIndex, lowerAction, lowerArguments,
    value, execute, Action.executeWith, GrammarConstructorActions.executeArgumentsWith]

theorem changed_file_action_has_changed_value (body : Atom) :
    execute [body] (.apply "node" [.constant (.symbol "wrong"), .slot 0]) ≠
      some (.expression [.symbol "node", .symbol "mm0-file", body]) := by simp [execute, Action.executeWith,
        GrammarConstructorActions.executeArgumentsWith]

theorem primitive_action_refused :
    productionAction? (metta_sexpr% petta
      "(pp-production LABEL STATE pp-items-nil (pa-primitive CONS pa-nil))") = none := by
  simp [productionAction?, actionSyntax?, wireTerm?, wireTerms?,
    CanonicalSourceHornElaboration.mayStartInteger, Action.decode]

#print axioms lowerAction_executes
#print axioms selected_included_ast_reflects
#print axioms actual_base_actions_admitted
#print axioms base_action_physical_position

end Mettapedia.Languages.MM0.MeTTa.TextualParserLinkage
