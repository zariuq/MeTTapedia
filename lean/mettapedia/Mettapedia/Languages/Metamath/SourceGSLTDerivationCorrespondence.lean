import Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
import Mettapedia.Languages.Metamath.SourceGSLTStatementAuthority
import Mettapedia.Languages.Metamath.SourceGSLTParserExport
import Mathlib.Tactic.IntervalCases

/-!
# Derivation correspondence: segmented statements are grammar derivations

Item 2's derivation legs.  The authored `sourceGrammar` carries no
token-sort productions — lexical leaves enter only through the generic
`lexicalizedLanguage` extension (one leaf rule per classified source
token), exactly as the checked parser path
(`admitLexicalDAGDefinition`) consumes them.  The correspondence is
therefore stated over any language satisfying the two honest
interfaces:

* `BaseRules L` — the authored productions are present;
* `TokenLeaf L sort tok` — a leaf rule derives the given token at the
  given lexical sort;

and the generic `lexicalizedLanguage` instantiates both
(`tokenLeaf_lexicalized`, `baseRule_mem_lexicalized`).  Statement-level
forward derivations are built per authored production; each statement's
`tokenStrings` is the exact ordered token image of the segmented
statement.
-/

set_option autoImplicit false
set_option maxRecDepth 100000

namespace Mettapedia.Languages.Metamath.SourceGSLTDerivationCorrespondence

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.GrammarDerives
open Mettapedia.GSLT.LanguageDef.GrammarInferenceExtraction
open Mettapedia.Languages.Metamath.SourceGSLT
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.Metamath.SourceGSLTStatementAuthority

/-! ## The two honest grammar interfaces -/

/-- The authored productions are present in `L`. -/
def BaseRules (L : LanguageDef) : Prop :=
  ∀ r ∈ sourceProductions, r ∈ L.terms

/-- Some leaf rule of `L` derives `tok` at lexical sort `sort`. -/
def TokenLeaf (L : LanguageDef) (sort tok : String) : Prop :=
  ∃ r ∈ L.terms, r.category = sort ∧ r.params = [] ∧
    r.syntaxPattern = [.terminal tok]

theorem TokenLeaf.derives {L : LanguageDef} {sort tok : String}
    (h : TokenLeaf L sort tok) :
    ∃ tree, Derives L sort [tok] tree := by
  obtain ⟨r, hr, hcat, hparams, hsyn⟩ := h
  refine ⟨.apply r.label [], Derives.rule r hr sort hcat [tok] [] ?_⟩
  rw [hsyn]
  exact DerivesItems.terminal r tok [] [] [] (DerivesItems.nil r)

/-! ## The generic lexicalized extension satisfies both interfaces -/

theorem baseRule_mem_lexicalized (language : LanguageDef)
    (declarations : List LexicalDeclaration)
    (source : ClassifiedSource) {r : GrammarRule}
    (h : r ∈ language.terms) :
    r ∈ (lexicalizedLanguage language declarations source).terms := by
  simp only [lexicalizedLanguage, List.mem_append]
  exact Or.inr h

theorem lexicalGrammarRulesFrom_mem
    (declarations : List LexicalDeclaration)
    (source : ClassifiedSource) :
    ∀ (tokens : List ClassifiedToken) (start : Nat)
      {token : ClassifiedToken} {sort : String},
      token ∈ tokens →
      lexicalSort? declarations token = some sort →
      ∃ index, lexicalGrammarRule source index token sort ∈
        lexicalGrammarRulesFrom declarations source tokens start := by
  intro tokens
  induction tokens with
  | nil =>
      intro start token sort htok _
      exact nomatch htok
  | cons t rest ih =>
      intro start token sort hmem hsortEq
      rcases List.mem_cons.mp hmem with rfl | htail
      · refine ⟨start, ?_⟩
        simp only [lexicalGrammarRulesFrom, hsortEq]
        exact List.Mem.head _
      · obtain ⟨index, hindex⟩ := ih (start + 1) htail hsortEq
        refine ⟨index, ?_⟩
        simp only [lexicalGrammarRulesFrom]
        cases hs : lexicalSort? declarations t with
        | none => exact hindex
        | some s => exact List.Mem.tail _ hindex

/-- **The lexicalized language leaf-covers its classified tokens.** -/
theorem tokenLeaf_lexicalized (language : LanguageDef)
    (declarations : List LexicalDeclaration)
    (source : ClassifiedSource) {token : ClassifiedToken} {sort : String}
    (htok : token ∈ source.tokens)
    (hsort : lexicalSort? declarations token = some sort) :
    TokenLeaf (lexicalizedLanguage language declarations source) sort
      token.serialized := by
  obtain ⟨index, hindex⟩ :=
    lexicalGrammarRulesFrom_mem declarations source source.tokens 0
      htok hsort
  refine ⟨lexicalGrammarRule source index token sort, ?_, rfl, rfl, rfl⟩
  simp only [lexicalizedLanguage, List.mem_append]
  exact Or.inl (by
    simpa [lexicalGrammarRules] using hindex)

/-! ## Authored production membership (positional, kernel-checked) -/

theorem symbols_one_mem :
    sourceProductions[0]? = some
      { label := "symbols_one", category := symbolListSort
        params := [.simple "symbol" (.base symbolTokenSort)]
        syntaxPattern := [.nonTerminal "symbol"] } := rfl

theorem symbols_more_mem :
    sourceProductions[1]? = some
      { label := "symbols_more", category := symbolListSort
        params := [.simple "symbol" (.base symbolTokenSort),
          .simple "rest" (.base symbolListSort)]
        syntaxPattern := [.nonTerminal "symbol", .nonTerminal "rest"] } :=
  rfl

theorem statement_var_mem :
    sourceProductions[13]? = some
      { label := "statement_var", category := statementSort
        params := [.simple "symbols" (.base symbolListSort)]
        syntaxPattern := [.terminal "$v", .nonTerminal "symbols",
          .terminal "$."] } := rfl

theorem statement_float_mem :
    sourceProductions[15]? = some
      { label := "statement_float", category := statementSort
        params := [.simple "label" (.base labelTokenSort),
          .simple "typecode" (.base symbolTokenSort),
          .simple "variable" (.base symbolTokenSort)]
        syntaxPattern := [.nonTerminal "label", .terminal "$f",
          .nonTerminal "typecode", .nonTerminal "variable",
          .terminal "$."] } := rfl

/-! ## Ordered token image of a segmented statement -/

/-- Ordered token strings of a proof payload. -/
def ProofPayload.tokenStrings : ProofPayload → List String
  | .normal steps => steps.map (·.name)
  | .compressed _ header _ words =>
      "(" :: header.map (·.name) ++
        ")" :: words.map (fun w => tokenText w.bytes)

/-- Ordered token strings of a segmented statement — the exact string
image of its retained spans. -/
def RawStatement.tokenStrings : RawStatement → List String
  | .openScope _ => ["${"]
  | .closeScope _ => ["$}"]
  | .constDecl _ names _ => "$c" :: names.map (·.name) ++ ["$."]
  | .varDecl _ names _ => "$v" :: names.map (·.name) ++ ["$."]
  | .djDecl _ names _ => "$d" :: names.map (·.name) ++ ["$."]
  | .floating _ label typecode variableName _ =>
      [label.name, "$f", typecode.name, variableName.name, "$."]
  | .essential _ label typecode body _ =>
      label.name :: "$e" :: typecode.name ::
        body.map (·.name) ++ ["$."]
  | .axiomatic _ label typecode body _ =>
      label.name :: "$a" :: typecode.name ::
        body.map (·.name) ++ ["$."]
  | .provable _ label typecode body proof _ _ =>
      label.name :: "$p" :: typecode.name :: body.map (·.name) ++
        "$=" :: ProofPayload.tokenStrings proof ++ ["$."]

/-! ## List-sort derivations -/

/-- Nonempty symbol lists derive `symbol_list`. -/
theorem symbolList_derives {L : LanguageDef} (hbase : BaseRules L) :
    ∀ (names : List String), names ≠ [] →
      (∀ n ∈ names, TokenLeaf L symbolTokenSort n) →
      ∃ tree, Derives L symbolListSort names tree
  | [], hne, _ => absurd rfl hne
  | [n], _, hleaf => by
      obtain ⟨sub, hsub⟩ := (hleaf n (List.Mem.head _)).derives
      refine ⟨.apply "symbols_one" [sub], ?_⟩
      refine Derives.rule _ (hbase _
        (List.mem_of_getElem? symbols_one_mem)) _ rfl [n] [sub] ?_
      show DerivesItems L _ [.nonTerminal "symbol"] [n] [sub]
      have := DerivesItems.nonTerminal
        (lang := L)
        { label := "symbols_one", category := symbolListSort
          params := [.simple "symbol" (.base symbolTokenSort)]
          syntaxPattern := [.nonTerminal "symbol"] }
        "symbol" symbolTokenSort rfl [n] sub hsub [] [] []
        (DerivesItems.nil _)
      simpa using this
  | n :: m :: rest, _, hleaf => by
      obtain ⟨sub, hsub⟩ := (hleaf n (List.Mem.head _)).derives
      obtain ⟨tail, htail⟩ := symbolList_derives hbase (m :: rest)
        (by simp) (fun x hx => hleaf x (List.Mem.tail _ hx))
      refine ⟨.apply "symbols_more" [sub, tail], ?_⟩
      refine Derives.rule _ (hbase _
        (List.mem_of_getElem? symbols_more_mem)) _ rfl
        (n :: m :: rest) [sub, tail] ?_
      show DerivesItems L _ [.nonTerminal "symbol", .nonTerminal "rest"]
        (n :: m :: rest) [sub, tail]
      have hrest := DerivesItems.nonTerminal
        (lang := L)
        { label := "symbols_more", category := symbolListSort
          params := [.simple "symbol" (.base symbolTokenSort),
            .simple "rest" (.base symbolListSort)]
          syntaxPattern := [.nonTerminal "symbol", .nonTerminal "rest"] }
        "rest" symbolListSort rfl (m :: rest) tail htail [] [] []
        (DerivesItems.nil _)
      have := DerivesItems.nonTerminal
        (lang := L)
        { label := "symbols_more", category := symbolListSort
          params := [.simple "symbol" (.base symbolTokenSort),
            .simple "rest" (.base symbolListSort)]
          syntaxPattern := [.nonTerminal "symbol", .nonTerminal "rest"] }
        "symbol" symbolTokenSort rfl [n] sub hsub
        [.nonTerminal "rest"] (m :: rest) [tail] (by simpa using hrest)
      simpa using this

/-! ## Statement-level forward derivations (first pair) -/

/-- A segmented `$v` statement derives the authored `statement_var`
production over exactly its token strings. -/
theorem varDecl_derives {L : LanguageDef} (hbase : BaseRules L)
    {site : Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical.LocatedByteSpan}
    {names : List LocatedName}
    {terminator : Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical.LocatedByteSpan}
    (hne : names ≠ [])
    (hleaf : ∀ n ∈ names, TokenLeaf L symbolTokenSort n.name) :
    ∃ tree, Derives L statementSort
      (RawStatement.tokenStrings (.varDecl site names terminator))
      tree := by
  obtain ⟨inner, hinner⟩ := symbolList_derives hbase
    (names.map (·.name))
    (by
      intro hmap
      exact hne (List.map_eq_nil_iff.mp hmap))
    (fun n hn => by
      obtain ⟨n₀, hn₀, rfl⟩ := List.mem_map.mp hn
      exact hleaf n₀ hn₀)
  refine ⟨.apply "statement_var" [inner], ?_⟩
  refine Derives.rule _ (hbase _
    (List.mem_of_getElem? statement_var_mem)) _ rfl
    (RawStatement.tokenStrings (.varDecl site names terminator))
    [inner] ?_
  show DerivesItems L _
    [.terminal "$v", .nonTerminal "symbols", .terminal "$."]
    ("$v" :: names.map (·.name) ++ ["$."]) [inner]
  refine DerivesItems.terminal _ "$v" _ _ _ ?_
  have hend := DerivesItems.terminal
    (lang := L)
    { label := "statement_var", category := statementSort
      params := [.simple "symbols" (.base symbolListSort)]
      syntaxPattern := [.terminal "$v", .nonTerminal "symbols",
        .terminal "$."] }
    "$." [] [] [] (DerivesItems.nil _)
  have := DerivesItems.nonTerminal
    (lang := L)
    { label := "statement_var", category := statementSort
      params := [.simple "symbols" (.base symbolListSort)]
      syntaxPattern := [.terminal "$v", .nonTerminal "symbols",
        .terminal "$."] }
    "symbols" symbolListSort rfl (names.map (·.name)) inner hinner
    [.terminal "$."] ["$."] [] hend
  simpa using this

/-- A segmented `$f` statement derives the authored `statement_float`
production over exactly its token strings. -/
theorem floating_derives {L : LanguageDef} (hbase : BaseRules L)
    {site terminator :
      Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical.LocatedByteSpan}
    {label typecode variableName : LocatedName}
    (hlabel : TokenLeaf L labelTokenSort label.name)
    (htype : TokenLeaf L symbolTokenSort typecode.name)
    (hvar : TokenLeaf L symbolTokenSort variableName.name) :
    ∃ tree, Derives L statementSort
      (RawStatement.tokenStrings
        (.floating site label typecode variableName terminator))
      tree := by
  obtain ⟨tl, htl⟩ := hlabel.derives
  obtain ⟨tt, htt⟩ := htype.derives
  obtain ⟨tv, htv⟩ := hvar.derives
  refine ⟨.apply "statement_float" [tl, tt, tv], ?_⟩
  refine Derives.rule _ (hbase _
    (List.mem_of_getElem? statement_float_mem)) _ rfl _ _ ?_
  show DerivesItems L _
    [.nonTerminal "label", .terminal "$f", .nonTerminal "typecode",
      .nonTerminal "variable", .terminal "$."]
    [label.name, "$f", typecode.name, variableName.name, "$."]
    [tl, tt, tv]
  let r : GrammarRule :=
    { label := "statement_float", category := statementSort
      params := [.simple "label" (.base labelTokenSort),
        .simple "typecode" (.base symbolTokenSort),
        .simple "variable" (.base symbolTokenSort)]
      syntaxPattern := [.nonTerminal "label", .terminal "$f",
        .nonTerminal "typecode", .nonTerminal "variable",
        .terminal "$."] }
  have hend := DerivesItems.terminal (lang := L) r "$." [] [] []
    (DerivesItems.nil _)
  have hv := DerivesItems.nonTerminal (lang := L) r
    "variable" symbolTokenSort rfl [variableName.name] tv htv
    [.terminal "$."] ["$."] [] hend
  have ht := DerivesItems.nonTerminal (lang := L) r
    "typecode" symbolTokenSort rfl [typecode.name] tt htt
    [.nonTerminal "variable", .terminal "$."]
    [variableName.name, "$."] [tv] (by simpa using hv)
  have hf := DerivesItems.terminal (lang := L) r "$f"
    [.nonTerminal "typecode", .nonTerminal "variable", .terminal "$."]
    [typecode.name, variableName.name, "$."] [tt, tv]
    (by simpa using ht)
  have := DerivesItems.nonTerminal (lang := L) r
    "label" labelTokenSort rfl [label.name] tl htl
    [.terminal "$f", .nonTerminal "typecode",
      .nonTerminal "variable", .terminal "$."]
    ["$f", typecode.name, variableName.name, "$."] [tt, tv] hf
  simpa using this

/-! ## Remaining production memberships -/

theorem disjoint_two_mem :
    sourceProductions[2]? = some
      { label := "disjoint_symbols_two", category := disjointSymbolListSort
        params := [.simple "first" (.base symbolTokenSort),
          .simple "second" (.base symbolTokenSort)]
        syntaxPattern := [.nonTerminal "first", .nonTerminal "second"] } :=
  rfl

theorem disjoint_more_mem :
    sourceProductions[3]? = some
      { label := "disjoint_symbols_more"
        category := disjointSymbolListSort
        params := [.simple "first" (.base symbolTokenSort),
          .simple "rest" (.base disjointSymbolListSort)]
        syntaxPattern := [.nonTerminal "first", .nonTerminal "rest"] } :=
  rfl

theorem proof_one_mem :
    sourceProductions[4]? = some
      { label := "proof_one", category := proofListSort
        params := [.simple "label" (.base proofLabelTokenSort)]
        syntaxPattern := [.nonTerminal "label"] } := rfl

theorem proof_more_mem :
    sourceProductions[5]? = some
      { label := "proof_more", category := proofListSort
        params := [.simple "label" (.base proofLabelTokenSort),
          .simple "rest" (.base proofListSort)]
        syntaxPattern := [.nonTerminal "label", .nonTerminal "rest"] } :=
  rfl

theorem proof_unknown_one_mem :
    sourceProductions[6]? = some
      { label := "proof_unknown_one", category := proofListSort
        params := []
        syntaxPattern := [.terminal "?"] } := rfl

theorem proof_unknown_more_mem :
    sourceProductions[7]? = some
      { label := "proof_unknown_more", category := proofListSort
        params := [.simple "rest" (.base proofListSort)]
        syntaxPattern := [.terminal "?", .nonTerminal "rest"] } := rfl

theorem header_empty_mem :
    sourceProductions[8]? = some
      { label := "header_empty", category := proofHeaderListSort
        params := []
        syntaxPattern := [] } := rfl

theorem header_more_mem :
    sourceProductions[9]? = some
      { label := "header_more", category := proofHeaderListSort
        params := [.simple "label" (.base proofLabelTokenSort),
          .simple "rest" (.base proofHeaderListSort)]
        syntaxPattern := [.nonTerminal "label", .nonTerminal "rest"] } :=
  rfl

theorem compressed_one_mem :
    sourceProductions[10]? = some
      { label := "compressed_one", category := compressedWordListSort
        params := [.simple "word" (.base compressedWordTokenSort)]
        syntaxPattern := [.nonTerminal "word"] } := rfl

theorem compressed_more_mem :
    sourceProductions[11]? = some
      { label := "compressed_more", category := compressedWordListSort
        params := [.simple "word" (.base compressedWordTokenSort),
          .simple "rest" (.base compressedWordListSort)]
        syntaxPattern := [.nonTerminal "word", .nonTerminal "rest"] } :=
  rfl

theorem statement_const_mem :
    sourceProductions[12]? = some
      { label := "statement_const", category := outerStatementSort
        params := [.simple "symbols" (.base symbolListSort)]
        syntaxPattern := [.terminal "$c", .nonTerminal "symbols",
          .terminal "$."] } := rfl

theorem statement_disjoint_mem :
    sourceProductions[14]? = some
      { label := "statement_disjoint", category := statementSort
        params := [.simple "symbols" (.base disjointSymbolListSort)]
        syntaxPattern := [.terminal "$d", .nonTerminal "symbols",
          .terminal "$."] } := rfl

theorem statement_essential_mem :
    sourceProductions[16]? = some
      { label := "statement_essential", category := statementSort
        params := [.simple "label" (.base labelTokenSort),
          .simple "formula" (.base symbolListSort)]
        syntaxPattern := [.nonTerminal "label", .terminal "$e",
          .nonTerminal "formula", .terminal "$."] } := rfl

theorem statement_axiom_mem :
    sourceProductions[17]? = some
      { label := "statement_axiom", category := statementSort
        params := [.simple "label" (.base labelTokenSort),
          .simple "formula" (.base symbolListSort)]
        syntaxPattern := [.nonTerminal "label", .terminal "$a",
          .nonTerminal "formula", .terminal "$."] } := rfl

theorem statement_theorem_normal_mem :
    sourceProductions[18]? = some
      { label := "statement_theorem_normal", category := statementSort
        params := [.simple "label" (.base labelTokenSort),
          .simple "formula" (.base symbolListSort),
          .simple "proof" (.base proofListSort)]
        syntaxPattern := [.nonTerminal "label", .terminal "$p",
          .nonTerminal "formula", .terminal "$=",
          .nonTerminal "proof", .terminal "$."] } := rfl

theorem statement_theorem_compressed_mem :
    sourceProductions[19]? = some
      { label := "statement_theorem_compressed"
        category := statementSort
        params := [.simple "label" (.base labelTokenSort),
          .simple "formula" (.base symbolListSort),
          .simple "header" (.base proofHeaderListSort),
          .simple "body" (.base compressedWordListSort)]
        syntaxPattern := [.nonTerminal "label", .terminal "$p",
          .nonTerminal "formula", .terminal "$=", .terminal "(",
          .nonTerminal "header", .terminal ")",
          .nonTerminal "body", .terminal "$."] } := rfl

theorem statement_block_mem :
    sourceProductions[21]? = some
      { label := "statement_block", category := statementSort
        params := [.simple "inside" (.base databaseSort)]
        syntaxPattern := [.terminal "${", .nonTerminal "inside",
          .terminal "$}"] } := rfl

theorem database_empty_mem :
    sourceProductions[22]? = some
      { label := "database_empty", category := databaseSort
        params := []
        syntaxPattern := [] } := rfl

theorem database_more_mem :
    sourceProductions[23]? = some
      { label := "database_more", category := databaseSort
        params := [.simple "statement" (.base statementSort),
          .simple "rest" (.base databaseSort)]
        syntaxPattern := [.nonTerminal "statement",
          .nonTerminal "rest"] } := rfl

theorem outer_statement_inner_mem :
    sourceProductions[24]? = some
      { label := "outer_statement_inner", category := outerStatementSort
        params := [.simple "statement" (.base statementSort)]
        syntaxPattern := [.nonTerminal "statement"] } := rfl

theorem outer_database_empty_mem :
    sourceProductions[25]? = some
      { label := "outer_database_empty", category := outerDatabaseSort
        params := []
        syntaxPattern := [] } := rfl

theorem outer_database_more_mem :
    sourceProductions[26]? = some
      { label := "outer_database_more", category := outerDatabaseSort
        params := [.simple "statement" (.base outerStatementSort),
          .simple "rest" (.base outerDatabaseSort)]
        syntaxPattern := [.nonTerminal "statement",
          .nonTerminal "rest"] } := rfl

/-! ## Remaining list-sort derivations -/

/-- Two-or-more symbol lists derive `disjoint_symbol_list`. -/
theorem disjointList_derives {L : LanguageDef} (hbase : BaseRules L) :
    ∀ (names : List String), 2 ≤ names.length →
      (∀ n ∈ names, TokenLeaf L symbolTokenSort n) →
      ∃ tree, Derives L disjointSymbolListSort names tree
  | [], hlen, _ => by simp at hlen
  | [_], hlen, _ => by simp at hlen
  | [a, b], _, hleaf => by
      obtain ⟨ta, hta⟩ := (hleaf a (by simp)).derives
      obtain ⟨tb, htb⟩ := (hleaf b (by simp)).derives
      refine ⟨.apply "disjoint_symbols_two" [ta, tb], ?_⟩
      refine Derives.rule _ (hbase _
        (List.mem_of_getElem? disjoint_two_mem)) _ rfl [a, b]
        [ta, tb] ?_
      let r : GrammarRule :=
        { label := "disjoint_symbols_two"
          category := disjointSymbolListSort
          params := [.simple "first" (.base symbolTokenSort),
            .simple "second" (.base symbolTokenSort)]
          syntaxPattern := [.nonTerminal "first",
            .nonTerminal "second"] }
      show DerivesItems L r
        [.nonTerminal "first", .nonTerminal "second"] [a, b] [ta, tb]
      have hb := DerivesItems.nonTerminal (lang := L) r
        "second" symbolTokenSort rfl [b] tb htb [] [] []
        (DerivesItems.nil _)
      have := DerivesItems.nonTerminal (lang := L) r
        "first" symbolTokenSort rfl [a] ta hta
        [.nonTerminal "second"] [b] [tb] (by simpa using hb)
      simpa using this
  | a :: b :: c :: rest, _, hleaf => by
      obtain ⟨ta, hta⟩ := (hleaf a (by simp)).derives
      obtain ⟨tail, htail⟩ := disjointList_derives hbase (b :: c :: rest)
        (by simp) (fun x hx => hleaf x (List.Mem.tail _ hx))
      refine ⟨.apply "disjoint_symbols_more" [ta, tail], ?_⟩
      refine Derives.rule _ (hbase _
        (List.mem_of_getElem? disjoint_more_mem)) _ rfl
        (a :: b :: c :: rest) [ta, tail] ?_
      let r : GrammarRule :=
        { label := "disjoint_symbols_more"
          category := disjointSymbolListSort
          params := [.simple "first" (.base symbolTokenSort),
            .simple "rest" (.base disjointSymbolListSort)]
          syntaxPattern := [.nonTerminal "first", .nonTerminal "rest"] }
      show DerivesItems L r
        [.nonTerminal "first", .nonTerminal "rest"]
        (a :: b :: c :: rest) [ta, tail]
      have hr := DerivesItems.nonTerminal (lang := L) r
        "rest" disjointSymbolListSort rfl (b :: c :: rest) tail htail
        [] [] [] (DerivesItems.nil _)
      have := DerivesItems.nonTerminal (lang := L) r
        "first" symbolTokenSort rfl [a] ta hta
        [.nonTerminal "rest"] (b :: c :: rest) [tail]
        (by simpa using hr)
      simpa using this

/-- Nonempty proof-step lists (labels or `?`) derive `proof_list`. -/
theorem proofList_derives {L : LanguageDef} (hbase : BaseRules L) :
    ∀ (steps : List String), steps ≠ [] →
      (∀ s ∈ steps,
        TokenLeaf L proofLabelTokenSort s ∨ s = "?") →
      ∃ tree, Derives L proofListSort steps tree
  | [], hne, _ => absurd rfl hne
  | [s], _, hstep => by
      rcases hstep s (by simp) with hleaf | rfl
      · obtain ⟨ts, hts⟩ := hleaf.derives
        refine ⟨.apply "proof_one" [ts], ?_⟩
        refine Derives.rule _ (hbase _
          (List.mem_of_getElem? proof_one_mem)) _ rfl [s] [ts] ?_
        let r : GrammarRule :=
          { label := "proof_one", category := proofListSort
            params := [.simple "label" (.base proofLabelTokenSort)]
            syntaxPattern := [.nonTerminal "label"] }
        show DerivesItems L r [.nonTerminal "label"] [s] [ts]
        have := DerivesItems.nonTerminal (lang := L) r
          "label" proofLabelTokenSort rfl [s] ts hts [] [] []
          (DerivesItems.nil _)
        simpa using this
      · refine ⟨.apply "proof_unknown_one" [], ?_⟩
        refine Derives.rule _ (hbase _
          (List.mem_of_getElem? proof_unknown_one_mem)) _ rfl ["?"]
          [] ?_
        exact DerivesItems.terminal _ "?" [] [] []
          (DerivesItems.nil _)
  | s :: t :: rest, _, hstep => by
      obtain ⟨tail, htail⟩ := proofList_derives hbase (t :: rest)
        (by simp) (fun x hx => hstep x (List.Mem.tail _ hx))
      rcases hstep s (by simp) with hleaf | rfl
      · obtain ⟨ts, hts⟩ := hleaf.derives
        refine ⟨.apply "proof_more" [ts, tail], ?_⟩
        refine Derives.rule _ (hbase _
          (List.mem_of_getElem? proof_more_mem)) _ rfl
          (s :: t :: rest) [ts, tail] ?_
        let r : GrammarRule :=
          { label := "proof_more", category := proofListSort
            params := [.simple "label" (.base proofLabelTokenSort),
              .simple "rest" (.base proofListSort)]
            syntaxPattern := [.nonTerminal "label",
              .nonTerminal "rest"] }
        show DerivesItems L r
          [.nonTerminal "label", .nonTerminal "rest"]
          (s :: t :: rest) [ts, tail]
        have hr := DerivesItems.nonTerminal (lang := L) r
          "rest" proofListSort rfl (t :: rest) tail htail [] [] []
          (DerivesItems.nil _)
        have := DerivesItems.nonTerminal (lang := L) r
          "label" proofLabelTokenSort rfl [s] ts hts
          [.nonTerminal "rest"] (t :: rest) [tail]
          (by simpa using hr)
        simpa using this
      · refine ⟨.apply "proof_unknown_more" [tail], ?_⟩
        refine Derives.rule _ (hbase _
          (List.mem_of_getElem? proof_unknown_more_mem)) _ rfl
          ("?" :: t :: rest) [tail] ?_
        let r : GrammarRule :=
          { label := "proof_unknown_more", category := proofListSort
            params := [.simple "rest" (.base proofListSort)]
            syntaxPattern := [.terminal "?", .nonTerminal "rest"] }
        show DerivesItems L r [.terminal "?", .nonTerminal "rest"]
          ("?" :: t :: rest) [tail]
        refine DerivesItems.terminal _ "?" _ _ _ ?_
        have := DerivesItems.nonTerminal (lang := L) r
          "rest" proofListSort rfl (t :: rest) tail htail [] [] []
          (DerivesItems.nil _)
        simpa using this

/-- Header label lists (possibly empty) derive `proof_header_list`. -/
theorem headerList_derives {L : LanguageDef} (hbase : BaseRules L) :
    ∀ (labels : List String),
      (∀ s ∈ labels, TokenLeaf L proofLabelTokenSort s) →
      ∃ tree, Derives L proofHeaderListSort labels tree
  | [], _ => by
      refine ⟨.apply "header_empty" [], ?_⟩
      refine Derives.rule _ (hbase _
        (List.mem_of_getElem? header_empty_mem)) _ rfl [] [] ?_
      exact DerivesItems.nil _
  | s :: rest, hleaf => by
      obtain ⟨ts, hts⟩ := (hleaf s (by simp)).derives
      obtain ⟨tail, htail⟩ := headerList_derives hbase rest
        (fun x hx => hleaf x (List.Mem.tail _ hx))
      refine ⟨.apply "header_more" [ts, tail], ?_⟩
      refine Derives.rule _ (hbase _
        (List.mem_of_getElem? header_more_mem)) _ rfl (s :: rest)
        [ts, tail] ?_
      let r : GrammarRule :=
        { label := "header_more", category := proofHeaderListSort
          params := [.simple "label" (.base proofLabelTokenSort),
            .simple "rest" (.base proofHeaderListSort)]
          syntaxPattern := [.nonTerminal "label",
            .nonTerminal "rest"] }
      show DerivesItems L r
        [.nonTerminal "label", .nonTerminal "rest"] (s :: rest)
        [ts, tail]
      have hr := DerivesItems.nonTerminal (lang := L) r
        "rest" proofHeaderListSort rfl rest tail htail [] [] []
        (DerivesItems.nil _)
      have := DerivesItems.nonTerminal (lang := L) r
        "label" proofLabelTokenSort rfl [s] ts hts
        [.nonTerminal "rest"] rest [tail] (by simpa using hr)
      simpa using this

/-- Nonempty compressed-word lists derive `compressed_word_list`. -/
theorem compressedList_derives {L : LanguageDef} (hbase : BaseRules L) :
    ∀ (words : List String), words ≠ [] →
      (∀ w ∈ words, TokenLeaf L compressedWordTokenSort w) →
      ∃ tree, Derives L compressedWordListSort words tree
  | [], hne, _ => absurd rfl hne
  | [w], _, hleaf => by
      obtain ⟨tw, htw⟩ := (hleaf w (by simp)).derives
      refine ⟨.apply "compressed_one" [tw], ?_⟩
      refine Derives.rule _ (hbase _
        (List.mem_of_getElem? compressed_one_mem)) _ rfl [w] [tw] ?_
      let r : GrammarRule :=
        { label := "compressed_one", category := compressedWordListSort
          params := [.simple "word" (.base compressedWordTokenSort)]
          syntaxPattern := [.nonTerminal "word"] }
      show DerivesItems L r [.nonTerminal "word"] [w] [tw]
      have := DerivesItems.nonTerminal (lang := L) r
        "word" compressedWordTokenSort rfl [w] tw htw [] [] []
        (DerivesItems.nil _)
      simpa using this
  | w :: x :: rest, _, hleaf => by
      obtain ⟨tw, htw⟩ := (hleaf w (by simp)).derives
      obtain ⟨tail, htail⟩ := compressedList_derives hbase (x :: rest)
        (by simp) (fun y hy => hleaf y (List.Mem.tail _ hy))
      refine ⟨.apply "compressed_more" [tw, tail], ?_⟩
      refine Derives.rule _ (hbase _
        (List.mem_of_getElem? compressed_more_mem)) _ rfl
        (w :: x :: rest) [tw, tail] ?_
      let r : GrammarRule :=
        { label := "compressed_more", category := compressedWordListSort
          params := [.simple "word" (.base compressedWordTokenSort),
            .simple "rest" (.base compressedWordListSort)]
          syntaxPattern := [.nonTerminal "word", .nonTerminal "rest"] }
      show DerivesItems L r
        [.nonTerminal "word", .nonTerminal "rest"] (w :: x :: rest)
        [tw, tail]
      have hr := DerivesItems.nonTerminal (lang := L) r
        "rest" compressedWordListSort rfl (x :: rest) tail htail
        [] [] [] (DerivesItems.nil _)
      have := DerivesItems.nonTerminal (lang := L) r
        "word" compressedWordTokenSort rfl [w] tw htw
        [.nonTerminal "rest"] (x :: rest) [tail] (by simpa using hr)
      simpa using this

/-! ## Additional statement-level forward derivations -/

/-- A segmented `$c` statement derives the authored (outer-only)
`statement_const` production. -/
theorem constDecl_derives {L : LanguageDef} (hbase : BaseRules L)
    {site terminator :
      Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical.LocatedByteSpan}
    {names : List LocatedName}
    (hne : names ≠ [])
    (hleaf : ∀ n ∈ names, TokenLeaf L symbolTokenSort n.name) :
    ∃ tree, Derives L outerStatementSort
      (RawStatement.tokenStrings (.constDecl site names terminator))
      tree := by
  obtain ⟨inner, hinner⟩ := symbolList_derives hbase
    (names.map (·.name))
    (by
      intro hmap
      exact hne (List.map_eq_nil_iff.mp hmap))
    (fun n hn => by
      obtain ⟨n₀, hn₀, rfl⟩ := List.mem_map.mp hn
      exact hleaf n₀ hn₀)
  refine ⟨.apply "statement_const" [inner], ?_⟩
  refine Derives.rule _ (hbase _
    (List.mem_of_getElem? statement_const_mem)) _ rfl _ [inner] ?_
  let r : GrammarRule :=
    { label := "statement_const", category := outerStatementSort
      params := [.simple "symbols" (.base symbolListSort)]
      syntaxPattern := [.terminal "$c", .nonTerminal "symbols",
        .terminal "$."] }
  show DerivesItems L r
    [.terminal "$c", .nonTerminal "symbols", .terminal "$."]
    ("$c" :: names.map (·.name) ++ ["$."]) [inner]
  refine DerivesItems.terminal _ "$c" _ _ _ ?_
  have hend := DerivesItems.terminal (lang := L) r "$." [] [] []
    (DerivesItems.nil _)
  have := DerivesItems.nonTerminal (lang := L) r
    "symbols" symbolListSort rfl (names.map (·.name)) inner hinner
    [.terminal "$."] ["$."] [] hend
  simpa using this

/-- A segmented `$d` statement derives `statement_disjoint`. -/
theorem djDecl_derives {L : LanguageDef} (hbase : BaseRules L)
    {site terminator :
      Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical.LocatedByteSpan}
    {names : List LocatedName}
    (hlen : 2 ≤ names.length)
    (hleaf : ∀ n ∈ names, TokenLeaf L symbolTokenSort n.name) :
    ∃ tree, Derives L statementSort
      (RawStatement.tokenStrings (.djDecl site names terminator))
      tree := by
  obtain ⟨inner, hinner⟩ := disjointList_derives hbase
    (names.map (·.name))
    (by simpa using hlen)
    (fun n hn => by
      obtain ⟨n₀, hn₀, rfl⟩ := List.mem_map.mp hn
      exact hleaf n₀ hn₀)
  refine ⟨.apply "statement_disjoint" [inner], ?_⟩
  refine Derives.rule _ (hbase _
    (List.mem_of_getElem? statement_disjoint_mem)) _ rfl _ [inner] ?_
  let r : GrammarRule :=
    { label := "statement_disjoint", category := statementSort
      params := [.simple "symbols" (.base disjointSymbolListSort)]
      syntaxPattern := [.terminal "$d", .nonTerminal "symbols",
        .terminal "$."] }
  show DerivesItems L r
    [.terminal "$d", .nonTerminal "symbols", .terminal "$."]
    ("$d" :: names.map (·.name) ++ ["$."]) [inner]
  refine DerivesItems.terminal _ "$d" _ _ _ ?_
  have hend := DerivesItems.terminal (lang := L) r "$." [] [] []
    (DerivesItems.nil _)
  have := DerivesItems.nonTerminal (lang := L) r
    "symbols" disjointSymbolListSort rfl (names.map (·.name)) inner
    hinner [.terminal "$."] ["$."] [] hend
  simpa using this

/-- Shared assembly for the `$e`/`$a` shapes. -/
private theorem labeledFormula_derives {L : LanguageDef}
    (hbase : BaseRules L)
    (rule : GrammarRule) (hrule : rule ∈ L.terms)
    (keyword : String)
    (hcat : rule.category = statementSort)
    (hsyn : rule.syntaxPattern =
      [.nonTerminal "label", .terminal keyword,
        .nonTerminal "formula", .terminal "$."])
    (hlabelSort : paramSort? rule "label" = some labelTokenSort)
    (hformulaSort : paramSort? rule "formula" = some symbolListSort)
    {label typecode : LocatedName} {body : List LocatedName}
    (hlabel : TokenLeaf L labelTokenSort label.name)
    (htype : TokenLeaf L symbolTokenSort typecode.name)
    (hbody : ∀ n ∈ body, TokenLeaf L symbolTokenSort n.name) :
    ∃ tree, Derives L statementSort
      (label.name :: keyword :: typecode.name ::
        body.map (·.name) ++ ["$."]) tree := by
  obtain ⟨tl, htl⟩ := hlabel.derives
  obtain ⟨inner, hinner⟩ := symbolList_derives hbase
    (typecode.name :: body.map (·.name)) (by simp)
    (fun n hn => by
      rcases List.mem_cons.mp hn with rfl | htail
      · exact htype
      · obtain ⟨n₀, hn₀, rfl⟩ := List.mem_map.mp htail
        exact hbody n₀ hn₀)
  refine ⟨.apply rule.label [tl, inner],
    Derives.rule rule hrule _ hcat _ [tl, inner] ?_⟩
  rw [hsyn]
  have hend := DerivesItems.terminal (lang := L) rule "$." [] [] []
    (DerivesItems.nil _)
  have hformula := DerivesItems.nonTerminal (lang := L) rule
    "formula" symbolListSort hformulaSort
    (typecode.name :: body.map (·.name)) inner hinner
    [.terminal "$."] ["$."] [] hend
  have hkw := DerivesItems.terminal (lang := L) rule keyword
    [.nonTerminal "formula", .terminal "$."]
    (typecode.name :: body.map (·.name) ++ ["$."]) [inner]
    (by simpa using hformula)
  have := DerivesItems.nonTerminal (lang := L) rule
    "label" labelTokenSort hlabelSort [label.name] tl htl
    [.terminal keyword, .nonTerminal "formula", .terminal "$."]
    (keyword :: typecode.name :: body.map (·.name) ++ ["$."])
    [inner] hkw
  simpa using this

/-- A segmented `$e` statement derives `statement_essential`. -/
theorem essential_derives {L : LanguageDef} (hbase : BaseRules L)
    {site terminator :
      Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical.LocatedByteSpan}
    {label typecode : LocatedName} {body : List LocatedName}
    (hlabel : TokenLeaf L labelTokenSort label.name)
    (htype : TokenLeaf L symbolTokenSort typecode.name)
    (hbody : ∀ n ∈ body, TokenLeaf L symbolTokenSort n.name) :
    ∃ tree, Derives L statementSort
      (RawStatement.tokenStrings
        (.essential site label typecode body terminator)) tree :=
  labeledFormula_derives hbase _
    (hbase _ (List.mem_of_getElem? statement_essential_mem)) "$e"
    rfl rfl rfl rfl hlabel htype hbody

/-- A segmented `$a` statement derives `statement_axiom`. -/
theorem axiomatic_derives {L : LanguageDef} (hbase : BaseRules L)
    {site terminator :
      Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical.LocatedByteSpan}
    {label typecode : LocatedName} {body : List LocatedName}
    (hlabel : TokenLeaf L labelTokenSort label.name)
    (htype : TokenLeaf L symbolTokenSort typecode.name)
    (hbody : ∀ n ∈ body, TokenLeaf L symbolTokenSort n.name) :
    ∃ tree, Derives L statementSort
      (RawStatement.tokenStrings
        (.axiomatic site label typecode body terminator)) tree :=
  labeledFormula_derives hbase _
    (hbase _ (List.mem_of_getElem? statement_axiom_mem)) "$a"
    rfl rfl rfl rfl hlabel htype hbody

/-- A segmented normal-proof `$p` statement derives
`statement_theorem_normal`. -/
theorem provable_normal_derives {L : LanguageDef} (hbase : BaseRules L)
    {site separator terminator :
      Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical.LocatedByteSpan}
    {label typecode : LocatedName}
    {body steps : List LocatedName}
    (hlabel : TokenLeaf L labelTokenSort label.name)
    (htype : TokenLeaf L symbolTokenSort typecode.name)
    (hbody : ∀ n ∈ body, TokenLeaf L symbolTokenSort n.name)
    (hne : steps ≠ [])
    (hsteps : ∀ s ∈ steps,
      TokenLeaf L proofLabelTokenSort s.name ∨ s.name = "?") :
    ∃ tree, Derives L statementSort
      (RawStatement.tokenStrings
        (.provable site label typecode body (.normal steps) separator
          terminator)) tree := by
  obtain ⟨tl, htl⟩ := hlabel.derives
  obtain ⟨inner, hinner⟩ := symbolList_derives hbase
    (typecode.name :: body.map (·.name)) (by simp)
    (fun n hn => by
      rcases List.mem_cons.mp hn with rfl | htail
      · exact htype
      · obtain ⟨n₀, hn₀, rfl⟩ := List.mem_map.mp htail
        exact hbody n₀ hn₀)
  obtain ⟨proofTree, hproof⟩ := proofList_derives hbase
    (steps.map (·.name))
    (by
      intro hmap
      exact hne (List.map_eq_nil_iff.mp hmap))
    (fun s hs => by
      obtain ⟨s₀, hs₀, rfl⟩ := List.mem_map.mp hs
      exact hsteps s₀ hs₀)
  refine ⟨.apply "statement_theorem_normal" [tl, inner, proofTree], ?_⟩
  refine Derives.rule _ (hbase _
    (List.mem_of_getElem? statement_theorem_normal_mem)) _ rfl _
    [tl, inner, proofTree] ?_
  let r : GrammarRule :=
    { label := "statement_theorem_normal", category := statementSort
      params := [.simple "label" (.base labelTokenSort),
        .simple "formula" (.base symbolListSort),
        .simple "proof" (.base proofListSort)]
      syntaxPattern := [.nonTerminal "label", .terminal "$p",
        .nonTerminal "formula", .terminal "$=",
        .nonTerminal "proof", .terminal "$."] }
  show DerivesItems L r
    [.nonTerminal "label", .terminal "$p", .nonTerminal "formula",
      .terminal "$=", .nonTerminal "proof", .terminal "$."]
    (label.name :: "$p" :: typecode.name :: body.map (·.name) ++
      "$=" :: steps.map (·.name) ++ ["$."])
    [tl, inner, proofTree]
  have hend := DerivesItems.terminal (lang := L) r "$." [] [] []
    (DerivesItems.nil _)
  have hproofItem := DerivesItems.nonTerminal (lang := L) r
    "proof" proofListSort rfl (steps.map (·.name)) proofTree hproof
    [.terminal "$."] ["$."] [] hend
  have hsep := DerivesItems.terminal (lang := L) r "$="
    [.nonTerminal "proof", .terminal "$."]
    (steps.map (·.name) ++ ["$."]) [proofTree]
    (by simpa using hproofItem)
  have hformula := DerivesItems.nonTerminal (lang := L) r
    "formula" symbolListSort rfl
    (typecode.name :: body.map (·.name)) inner hinner
    [.terminal "$=", .nonTerminal "proof", .terminal "$."]
    ("$=" :: steps.map (·.name) ++ ["$."]) [proofTree] hsep
  have hkw := DerivesItems.terminal (lang := L) r "$p"
    [.nonTerminal "formula", .terminal "$=",
      .nonTerminal "proof", .terminal "$."]
    (typecode.name :: body.map (·.name) ++
      "$=" :: steps.map (·.name) ++ ["$."]) [inner, proofTree]
    (by simpa using hformula)
  have := DerivesItems.nonTerminal (lang := L) r
    "label" labelTokenSort rfl [label.name] tl htl
    [.terminal "$p", .nonTerminal "formula", .terminal "$=",
      .nonTerminal "proof", .terminal "$."]
    ("$p" :: typecode.name :: body.map (·.name) ++
      "$=" :: steps.map (·.name) ++ ["$."]) [inner, proofTree] hkw
  simpa using this

/-- A segmented compressed `$p` statement derives
`statement_theorem_compressed`. -/
theorem provable_compressed_derives {L : LanguageDef}
    (hbase : BaseRules L)
    {site openParen closeParen separator terminator :
      Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical.LocatedByteSpan}
    {label typecode : LocatedName}
    {body header : List LocatedName} {words : List LocatedToken}
    (hlabel : TokenLeaf L labelTokenSort label.name)
    (htype : TokenLeaf L symbolTokenSort typecode.name)
    (hbody : ∀ n ∈ body, TokenLeaf L symbolTokenSort n.name)
    (hheader : ∀ n ∈ header, TokenLeaf L proofLabelTokenSort n.name)
    (hwne : words ≠ [])
    (hwords : ∀ w ∈ words,
      TokenLeaf L compressedWordTokenSort (tokenText w.bytes)) :
    ∃ tree, Derives L statementSort
      (RawStatement.tokenStrings
        (.provable site label typecode body
          (.compressed openParen header closeParen words) separator
          terminator)) tree := by
  obtain ⟨tl, htl⟩ := hlabel.derives
  obtain ⟨inner, hinner⟩ := symbolList_derives hbase
    (typecode.name :: body.map (·.name)) (by simp)
    (fun n hn => by
      rcases List.mem_cons.mp hn with rfl | htail
      · exact htype
      · obtain ⟨n₀, hn₀, rfl⟩ := List.mem_map.mp htail
        exact hbody n₀ hn₀)
  obtain ⟨headerTree, hheaderTree⟩ := headerList_derives hbase
    (header.map (·.name))
    (fun s hs => by
      obtain ⟨s₀, hs₀, rfl⟩ := List.mem_map.mp hs
      exact hheader s₀ hs₀)
  obtain ⟨wordsTree, hwordsTree⟩ := compressedList_derives hbase
    (words.map (fun w => tokenText w.bytes))
    (by
      intro hmap
      exact hwne (List.map_eq_nil_iff.mp hmap))
    (fun w hw => by
      obtain ⟨w₀, hw₀, rfl⟩ := List.mem_map.mp hw
      exact hwords w₀ hw₀)
  refine ⟨.apply "statement_theorem_compressed"
    [tl, inner, headerTree, wordsTree], ?_⟩
  refine Derives.rule _ (hbase _
    (List.mem_of_getElem? statement_theorem_compressed_mem)) _ rfl _
    [tl, inner, headerTree, wordsTree] ?_
  let r : GrammarRule :=
    { label := "statement_theorem_compressed"
      category := statementSort
      params := [.simple "label" (.base labelTokenSort),
        .simple "formula" (.base symbolListSort),
        .simple "header" (.base proofHeaderListSort),
        .simple "body" (.base compressedWordListSort)]
      syntaxPattern := [.nonTerminal "label", .terminal "$p",
        .nonTerminal "formula", .terminal "$=", .terminal "(",
        .nonTerminal "header", .terminal ")",
        .nonTerminal "body", .terminal "$."] }
  show DerivesItems L r
    [.nonTerminal "label", .terminal "$p", .nonTerminal "formula",
      .terminal "$=", .terminal "(", .nonTerminal "header",
      .terminal ")", .nonTerminal "body", .terminal "$."]
    (label.name :: "$p" :: typecode.name :: body.map (·.name) ++
      "$=" :: ("(" :: header.map (·.name) ++
        ")" :: words.map (fun w => tokenText w.bytes)) ++ ["$."])
    [tl, inner, headerTree, wordsTree]
  have hend := DerivesItems.terminal (lang := L) r "$." [] [] []
    (DerivesItems.nil _)
  have hwordsItem := DerivesItems.nonTerminal (lang := L) r
    "body" compressedWordListSort rfl
    (words.map (fun w => tokenText w.bytes)) wordsTree hwordsTree
    [.terminal "$."] ["$."] [] hend
  have hclose := DerivesItems.terminal (lang := L) r ")"
    [.nonTerminal "body", .terminal "$."]
    (words.map (fun w => tokenText w.bytes) ++ ["$."]) [wordsTree]
    (by simpa using hwordsItem)
  have hheaderItem := DerivesItems.nonTerminal (lang := L) r
    "header" proofHeaderListSort rfl
    (header.map (·.name)) headerTree hheaderTree
    [.terminal ")", .nonTerminal "body", .terminal "$."]
    (")" :: words.map (fun w => tokenText w.bytes) ++ ["$."])
    [wordsTree] hclose
  have hopen := DerivesItems.terminal (lang := L) r "("
    [.nonTerminal "header", .terminal ")",
      .nonTerminal "body", .terminal "$."]
    (header.map (·.name) ++
      ")" :: words.map (fun w => tokenText w.bytes) ++ ["$."])
    [headerTree, wordsTree] (by simpa using hheaderItem)
  have hsep := DerivesItems.terminal (lang := L) r "$="
    [.terminal "(", .nonTerminal "header", .terminal ")",
      .nonTerminal "body", .terminal "$."]
    ("(" :: header.map (·.name) ++
      ")" :: words.map (fun w => tokenText w.bytes) ++ ["$."])
    [headerTree, wordsTree] hopen
  have hformula := DerivesItems.nonTerminal (lang := L) r
    "formula" symbolListSort rfl
    (typecode.name :: body.map (·.name)) inner hinner
    [.terminal "$=", .terminal "(", .nonTerminal "header",
      .terminal ")", .nonTerminal "body", .terminal "$."]
    ("$=" :: "(" :: header.map (·.name) ++
      ")" :: words.map (fun w => tokenText w.bytes) ++ ["$."])
    [headerTree, wordsTree] hsep
  have hkw := DerivesItems.terminal (lang := L) r "$p"
    [.nonTerminal "formula", .terminal "$=", .terminal "(",
      .nonTerminal "header", .terminal ")",
      .nonTerminal "body", .terminal "$."]
    (typecode.name :: body.map (·.name) ++
      "$=" :: "(" :: header.map (·.name) ++
      ")" :: words.map (fun w => tokenText w.bytes) ++ ["$."])
    [inner, headerTree, wordsTree] (by simpa using hformula)
  have := DerivesItems.nonTerminal (lang := L) r
    "label" labelTokenSort rfl [label.name] tl htl
    [.terminal "$p", .nonTerminal "formula", .terminal "$=",
      .terminal "(", .nonTerminal "header", .terminal ")",
      .nonTerminal "body", .terminal "$."]
    ("$p" :: typecode.name :: body.map (·.name) ++
      "$=" :: "(" :: header.map (·.name) ++
      ")" :: words.map (fun w => tokenText w.bytes) ++ ["$."])
    [inner, headerTree, wordsTree] hkw
  simpa using this

/-! ## Statement classification and per-statement fact bundles -/

/-- Scope markers (`${` / `$}`). -/
def isMarker : RawStatement → Bool
  | .openScope _ => true
  | .closeScope _ => true
  | _ => false

/-- Constant declarations (`$c`), legal only at the outermost scope. -/
def isConst : RawStatement → Bool
  | .constDecl _ _ _ => true
  | _ => false

/-- Structural arity facts the grammar imposes on one statement.  The
fold's gates supply the `$c`/`$v`/`$d` facts; the segmenter supplies the
normal-proof and compressed-word facts by construction.  The latter is
pinned by the empty-compressed-body regression boundary below. -/
def StatementArity : RawStatement → Prop
  | .constDecl _ names _ => names ≠ []
  | .varDecl _ names _ => names ≠ []
  | .djDecl _ names _ => 2 ≤ names.length
  | .provable _ _ _ _ (.normal steps) _ _ => steps ≠ []
  | .provable _ _ _ _ (.compressed _ _ _ words) _ _ => words ≠ []
  | _ => True

/-- Leaf coverage for one proof payload. -/
def ProofLeaves (L : LanguageDef) : ProofPayload → Prop
  | .normal steps =>
      ∀ s ∈ steps, TokenLeaf L proofLabelTokenSort s.name ∨ s.name = "?"
  | .compressed _ header _ words =>
      (∀ n ∈ header, TokenLeaf L proofLabelTokenSort n.name) ∧
        ∀ w ∈ words, TokenLeaf L compressedWordTokenSort (tokenText w.bytes)

/-- Leaf coverage for one statement: every consumed name token has a
leaf rule at its lexical sort. -/
def StatementLeaves (L : LanguageDef) : RawStatement → Prop
  | .openScope _ => True
  | .closeScope _ => True
  | .constDecl _ names _ =>
      ∀ n ∈ names, TokenLeaf L symbolTokenSort n.name
  | .varDecl _ names _ =>
      ∀ n ∈ names, TokenLeaf L symbolTokenSort n.name
  | .djDecl _ names _ =>
      ∀ n ∈ names, TokenLeaf L symbolTokenSort n.name
  | .floating _ label typecode variableName _ =>
      TokenLeaf L labelTokenSort label.name ∧
        TokenLeaf L symbolTokenSort typecode.name ∧
        TokenLeaf L symbolTokenSort variableName.name
  | .essential _ label typecode body _ =>
      TokenLeaf L labelTokenSort label.name ∧
        TokenLeaf L symbolTokenSort typecode.name ∧
        ∀ n ∈ body, TokenLeaf L symbolTokenSort n.name
  | .axiomatic _ label typecode body _ =>
      TokenLeaf L labelTokenSort label.name ∧
        TokenLeaf L symbolTokenSort typecode.name ∧
        ∀ n ∈ body, TokenLeaf L symbolTokenSort n.name
  | .provable _ label typecode body proof _ _ =>
      TokenLeaf L labelTokenSort label.name ∧
        TokenLeaf L symbolTokenSort typecode.name ∧
        (∀ n ∈ body, TokenLeaf L symbolTokenSort n.name) ∧
        ProofLeaves L proof

/-! ## Database chains and the block production -/

theorem database_nil_derives {L : LanguageDef} (hbase : BaseRules L) :
    Derives L databaseSort [] (.apply "database_empty" []) := by
  refine Derives.rule _ (hbase _
    (List.mem_of_getElem? database_empty_mem)) _ rfl [] [] ?_
  exact DerivesItems.nil _

theorem outerDatabase_nil_derives {L : LanguageDef}
    (hbase : BaseRules L) :
    Derives L outerDatabaseSort [] (.apply "outer_database_empty" []) := by
  refine Derives.rule _ (hbase _
    (List.mem_of_getElem? outer_database_empty_mem)) _ rfl [] [] ?_
  exact DerivesItems.nil _

theorem database_cons_derives {L : LanguageDef} (hbase : BaseRules L)
    {stoks rtoks : List String} {stree rtree : Pattern}
    (hs : Derives L statementSort stoks stree)
    (hr : Derives L databaseSort rtoks rtree) :
    Derives L databaseSort (stoks ++ rtoks)
      (.apply "database_more" [stree, rtree]) := by
  refine Derives.rule _ (hbase _
    (List.mem_of_getElem? database_more_mem)) _ rfl _ _ ?_
  let r : GrammarRule :=
    { label := "database_more", category := databaseSort
      params := [.simple "statement" (.base statementSort),
        .simple "rest" (.base databaseSort)]
      syntaxPattern := [.nonTerminal "statement", .nonTerminal "rest"] }
  show DerivesItems L r
    [.nonTerminal "statement", .nonTerminal "rest"]
    (stoks ++ rtoks) [stree, rtree]
  have hrest := DerivesItems.nonTerminal (lang := L) r
    "rest" databaseSort rfl rtoks rtree hr [] [] []
    (DerivesItems.nil _)
  have := DerivesItems.nonTerminal (lang := L) r
    "statement" statementSort rfl stoks stree hs
    [.nonTerminal "rest"] rtoks [rtree] (by simpa using hrest)
  simpa using this

theorem outerDatabase_cons_derives {L : LanguageDef}
    (hbase : BaseRules L)
    {stoks rtoks : List String} {stree rtree : Pattern}
    (hs : Derives L outerStatementSort stoks stree)
    (hr : Derives L outerDatabaseSort rtoks rtree) :
    Derives L outerDatabaseSort (stoks ++ rtoks)
      (.apply "outer_database_more" [stree, rtree]) := by
  refine Derives.rule _ (hbase _
    (List.mem_of_getElem? outer_database_more_mem)) _ rfl _ _ ?_
  let r : GrammarRule :=
    { label := "outer_database_more", category := outerDatabaseSort
      params := [.simple "statement" (.base outerStatementSort),
        .simple "rest" (.base outerDatabaseSort)]
      syntaxPattern := [.nonTerminal "statement", .nonTerminal "rest"] }
  show DerivesItems L r
    [.nonTerminal "statement", .nonTerminal "rest"]
    (stoks ++ rtoks) [stree, rtree]
  have hrest := DerivesItems.nonTerminal (lang := L) r
    "rest" outerDatabaseSort rfl rtoks rtree hr [] [] []
    (DerivesItems.nil _)
  have := DerivesItems.nonTerminal (lang := L) r
    "statement" outerStatementSort rfl stoks stree hs
    [.nonTerminal "rest"] rtoks [rtree] (by simpa using hrest)
  simpa using this

theorem outer_inner_derives {L : LanguageDef} (hbase : BaseRules L)
    {toks : List String} {tree : Pattern}
    (h : Derives L statementSort toks tree) :
    Derives L outerStatementSort toks
      (.apply "outer_statement_inner" [tree]) := by
  refine Derives.rule _ (hbase _
    (List.mem_of_getElem? outer_statement_inner_mem)) _ rfl toks
    [tree] ?_
  let r : GrammarRule :=
    { label := "outer_statement_inner", category := outerStatementSort
      params := [.simple "statement" (.base statementSort)]
      syntaxPattern := [.nonTerminal "statement"] }
  show DerivesItems L r [.nonTerminal "statement"] toks [tree]
  have := DerivesItems.nonTerminal (lang := L) r
    "statement" statementSort rfl toks tree h [] [] []
    (DerivesItems.nil _)
  simpa using this

theorem block_derives {L : LanguageDef} (hbase : BaseRules L)
    {inner : List String} {tree : Pattern}
    (h : Derives L databaseSort inner tree) :
    Derives L statementSort ("${" :: inner ++ ["$}"])
      (.apply "statement_block" [tree]) := by
  refine Derives.rule _ (hbase _
    (List.mem_of_getElem? statement_block_mem)) _ rfl _ _ ?_
  let r : GrammarRule :=
    { label := "statement_block", category := statementSort
      params := [.simple "inside" (.base databaseSort)]
      syntaxPattern := [.terminal "${", .nonTerminal "inside",
        .terminal "$}"] }
  show DerivesItems L r
    [.terminal "${", .nonTerminal "inside", .terminal "$}"]
    ("${" :: inner ++ ["$}"]) [tree]
  refine DerivesItems.terminal _ "${" _ _ _ ?_
  have hend := DerivesItems.terminal (lang := L) r "$}" [] [] []
    (DerivesItems.nil _)
  have := DerivesItems.nonTerminal (lang := L) r
    "inside" databaseSort rfl inner tree h
    [.terminal "$}"] ["$}"] [] hend
  simpa using this

/-- Dispatcher: every non-marker, non-`$c` statement with leaf coverage
and grammar arity derives `statement`. -/
theorem atom_statement_derives {L : LanguageDef} (hbase : BaseRules L)
    {s : RawStatement}
    (hmarker : isMarker s = false) (hconst : isConst s = false)
    (hleaf : StatementLeaves L s) (harity : StatementArity s) :
    ∃ tree, Derives L statementSort (RawStatement.tokenStrings s)
      tree := by
  cases s with
  | openScope site => simp [isMarker] at hmarker
  | closeScope site => simp [isMarker] at hmarker
  | constDecl site names terminator => simp [isConst] at hconst
  | varDecl site names terminator =>
      exact varDecl_derives hbase harity hleaf
  | djDecl site names terminator =>
      exact djDecl_derives hbase harity hleaf
  | floating site label typecode variableName terminator =>
      obtain ⟨h1, h2, h3⟩ := hleaf
      exact floating_derives hbase h1 h2 h3
  | essential site label typecode body terminator =>
      obtain ⟨h1, h2, h3⟩ := hleaf
      exact essential_derives hbase h1 h2 h3
  | axiomatic site label typecode body terminator =>
      obtain ⟨h1, h2, h3⟩ := hleaf
      exact axiomatic_derives hbase h1 h2 h3
  | provable site label typecode body proof separator terminator =>
      obtain ⟨h1, h2, h3, hproof⟩ := hleaf
      cases proof with
      | normal steps =>
          exact provable_normal_derives hbase h1 h2 h3 harity hproof
      | compressed openParen header closeParen words =>
          obtain ⟨hheader, hwords⟩ := hproof
          exact provable_compressed_derives hbase h1 h2 h3 hheader
            harity hwords

/-! ## Nested statement sequences

`NestSeq true` is an outer-database stream (`$c` legal at this level);
`NestSeq false` is a block interior (`$c` illegal).  The block
constructor carries the flat form directly, so structural induction
walks exactly the segmenter's statement stream. -/

inductive NestSeq : Bool → List RawStatement → Prop where
  | nil (outer : Bool) : NestSeq outer []
  | atom (outer : Bool) (s : RawStatement) (rest : List RawStatement) :
      isMarker s = false → (isConst s = true → outer = true) →
      NestSeq outer rest → NestSeq outer (s :: rest)
  | block (outer : Bool)
      (openSite closeSite :
        Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical.LocatedByteSpan)
      (inner rest : List RawStatement) :
      NestSeq false inner → NestSeq outer rest →
      NestSeq outer
        (.openScope openSite :: (inner ++ .closeScope closeSite :: rest))

/-- **Forward nesting correspondence.**  A nested statement sequence
with leaf coverage and grammar arities derives the (outer) database
sort over exactly its concatenated token strings. -/
theorem nestSeq_derives {L : LanguageDef} (hbase : BaseRules L)
    {outer : Bool} {ss : List RawStatement} (h : NestSeq outer ss)
    (hfacts : ∀ s ∈ ss, StatementLeaves L s ∧ StatementArity s) :
    ∃ tree,
      Derives L (cond outer outerDatabaseSort databaseSort)
        (ss.flatMap RawStatement.tokenStrings) tree := by
  induction h with
  | nil outer =>
      cases outer
      · exact ⟨_, database_nil_derives hbase⟩
      · exact ⟨_, outerDatabase_nil_derives hbase⟩
  | atom outer s rest hmarker hconst hrest ih =>
      obtain ⟨hleaf, harity⟩ := hfacts s (by simp)
      obtain ⟨rtree, hrtree⟩ := ih
        (fun x hx => hfacts x (by simp [hx]))
      cases outer with
      | false =>
          have hconstF : isConst s = false := by
            cases hcs : isConst s with
            | false => rfl
            | true => exact nomatch (hconst hcs)
          obtain ⟨stree, hstree⟩ :=
            atom_statement_derives hbase hmarker hconstF hleaf harity
          exact ⟨_, by
            simpa using database_cons_derives hbase hstree hrtree⟩
      | true =>
          cases hcs : isConst s with
          | false =>
              obtain ⟨stree, hstree⟩ :=
                atom_statement_derives hbase hmarker hcs hleaf harity
              exact ⟨_, by
                simpa using outerDatabase_cons_derives hbase
                  (outer_inner_derives hbase hstree) hrtree⟩
          | true =>
              cases s with
              | constDecl site names terminator =>
                  obtain ⟨stree, hstree⟩ :=
                    constDecl_derives hbase harity hleaf
                  exact ⟨_, by
                    simpa using outerDatabase_cons_derives hbase hstree
                      hrtree⟩
              | openScope site => simp [isConst] at hcs
              | closeScope site => simp [isConst] at hcs
              | varDecl site names terminator => simp [isConst] at hcs
              | djDecl site names terminator => simp [isConst] at hcs
              | floating site label typecode variableName terminator =>
                  simp [isConst] at hcs
              | essential site label typecode body terminator =>
                  simp [isConst] at hcs
              | axiomatic site label typecode body terminator =>
                  simp [isConst] at hcs
              | provable site label typecode body proof separator
                  terminator =>
                  simp [isConst] at hcs
  | block outer openSite closeSite inner rest hinner hrest ih₁ ih₂ =>
      obtain ⟨itree, hitree⟩ := ih₁
        (fun x hx => hfacts x (by simp [hx]))
      obtain ⟨rtree, hrtree⟩ := ih₂
        (fun x hx => hfacts x (by simp [hx]))
      have hblock := block_derives hbase hitree
      cases outer with
      | false =>
          exact ⟨_, by
            simpa [RawStatement.tokenStrings, List.append_assoc]
              using database_cons_derives hbase hblock hrtree⟩
      | true =>
          exact ⟨_, by
            simpa [RawStatement.tokenStrings, List.append_assoc]
              using outerDatabase_cons_derives hbase
                (outer_inner_derives hbase hblock) hrtree⟩

/-! ## Depth-indexed bookkeeping: the fold's own scope discipline -/

/-- `SeqAt d ss`: reading `ss` at scope depth `d`, every close has a
matching open, the stream ends balanced, and `$c` occurs only at depth
zero.  This is exactly what the accepted fold guarantees. -/
inductive SeqAt : Nat → List RawStatement → Prop where
  | nil : SeqAt 0 []
  | atom (d : Nat) (s : RawStatement) (rest : List RawStatement) :
      isMarker s = false → (isConst s = true → d = 0) →
      SeqAt d rest → SeqAt d (s :: rest)
  | openScope (d : Nat)
      (site :
        Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical.LocatedByteSpan)
      (rest : List RawStatement) :
      SeqAt (d + 1) rest → SeqAt d (.openScope site :: rest)
  | closeScope (d : Nat)
      (site :
        Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical.LocatedByteSpan)
      (rest : List RawStatement) :
      SeqAt d rest → SeqAt (d + 1) (.closeScope site :: rest)

/-- Split a depth-`d + 1` stream at the close matching its opening. -/
theorem seqAt_split :
    ∀ {n : Nat} {ss : List RawStatement} {d : Nat},
      ss.length ≤ n → SeqAt (d + 1) ss →
      ∃ (inner : List RawStatement)
        (site :
          Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical.LocatedByteSpan)
        (past : List RawStatement),
        ss = inner ++ .closeScope site :: past ∧ NestSeq false inner ∧
          SeqAt d past := by
  intro n
  induction n with
  | zero =>
      intro ss d hlen hseq
      have : ss = [] := List.eq_nil_of_length_eq_zero
        (Nat.le_zero.mp hlen)
      subst this
      exact nomatch hseq
  | succ n ihn =>
      intro ss d hlen hseq
      cases hseq with
      | atom d s rest hmarker hconst hrest =>
          obtain ⟨inner, site, past, heq, hinner, hpast⟩ :=
            ihn (by simpa using Nat.le_of_succ_le_succ hlen) hrest
          refine ⟨s :: inner, site, past, by simp [heq],
            NestSeq.atom false s inner hmarker
              (fun hc => nomatch (hconst hc)) hinner, hpast⟩
      | openScope d site rest hrest =>
          have hlen' : rest.length ≤ n := by
            simpa using Nat.le_of_succ_le_succ hlen
          obtain ⟨inner₁, site₁, past₁, heq₁, hinner₁, hpast₁⟩ :=
            ihn hlen' hrest
          have hlen₁ : past₁.length ≤ n := by
            subst heq₁
            simp at hlen'
            omega
          obtain ⟨inner₂, site₂, past₂, heq₂, hinner₂, hpast₂⟩ :=
            ihn hlen₁ hpast₁
          refine ⟨.openScope site ::
            (inner₁ ++ .closeScope site₁ :: inner₂), site₂, past₂,
            by simp [heq₁, heq₂],
            NestSeq.block false site site₁ inner₁ inner₂ hinner₁
              hinner₂, hpast₂⟩
      | closeScope d site rest hrest =>
          exact ⟨[], site, rest, by simp, NestSeq.nil false, hrest⟩

/-- Balanced depth-zero streams regroup into nested sequences. -/
theorem nestSeq_of_seqAt :
    ∀ {n : Nat} {ss : List RawStatement},
      ss.length ≤ n → SeqAt 0 ss → NestSeq true ss := by
  intro n
  induction n with
  | zero =>
      intro ss hlen _
      have : ss = [] := List.eq_nil_of_length_eq_zero
        (Nat.le_zero.mp hlen)
      subst this
      exact NestSeq.nil true
  | succ n ihn =>
      intro ss hlen hseq
      cases hseq with
      | nil => exact NestSeq.nil true
      | atom d s rest hmarker hconst hrest =>
          exact NestSeq.atom true s rest hmarker (fun _ => rfl)
            (ihn (by simpa using Nat.le_of_succ_le_succ hlen) hrest)
      | openScope d site rest hrest =>
          have hlen' : rest.length ≤ n := by
            simpa using Nat.le_of_succ_le_succ hlen
          obtain ⟨inner, csite, past, heq, hinner, hpast⟩ :=
            seqAt_split hlen' hrest
          have hlenp : past.length ≤ n := by
            subst heq
            simp at hlen'
            omega
          subst heq
          exact NestSeq.block true site csite inner past hinner
            (ihn hlenp hpast)

/-- Entry form of the regrouping. -/
theorem seqAt_nestSeq {ss : List RawStatement} (h : SeqAt 0 ss) :
    NestSeq true ss :=
  nestSeq_of_seqAt le_rfl h

/-! ## Fold discharge: the accepted fold certifies its own structure -/

section FoldDischarge

open Mettapedia.Languages.Metamath.SourceGSLTState

private theorem bind_guard_some {c : Prop} [Decidable c] {α : Type _}
    {rest : Option α} {a : α}
    (h : (do guard c; rest) = some a) : c ∧ rest = some a := by
  by_cases hc : c
  · refine ⟨hc, ?_⟩
    simpa [guard, hc] using h
  · simp [guard, hc] at h

private theorem declareConstants?_inv {state after : SourceState}
    {names : List String}
    (h : declareConstants? state names = some after) :
    names ≠ [] ∧ state.scopes = [] := by
  unfold declareConstants? at h
  obtain ⟨-, h⟩ := bind_guard_some h
  obtain ⟨hne, h⟩ := bind_guard_some h
  obtain ⟨hempty, -⟩ := bind_guard_some h
  refine ⟨?_, ?_⟩
  · intro hnil
    rw [hnil] at hne
    simp at hne
  · cases hs : state.scopes with
    | nil => rfl
    | cons a l =>
        rw [hs] at hempty
        simp at hempty

private theorem declareVariables?_inv {state after : SourceState}
    {names : List String}
    (h : declareVariables? state names = some after) :
    names ≠ [] := by
  unfold declareVariables? at h
  obtain ⟨-, h⟩ := bind_guard_some h
  obtain ⟨hne, -⟩ := bind_guard_some h
  intro hnil
  rw [hnil] at hne
  simp at hne

private theorem declareDisjoint?_inv {state after : SourceState}
    {names : List String}
    (h : declareDisjoint? state names = some after) :
    2 ≤ names.length := by
  unfold declareDisjoint? at h
  obtain ⟨-, h⟩ := bind_guard_some h
  obtain ⟨hlen, -⟩ := bind_guard_some h
  exact hlen

/-- The gate facts the fold itself enforces per statement. -/
def FoldArity : RawStatement → Prop
  | .constDecl _ names _ => names ≠ []
  | .varDecl _ names _ => names ≠ []
  | .djDecl _ names _ => 2 ≤ names.length
  | _ => True

/-- **The accepted fold certifies its own scope discipline and gate
arities**: from any start state, an accepted fold whose final state has
no open scopes reads its statements at the start depth with matched
scopes and top-level-only `$c`, and every `$c`/`$v`/`$d` payload
satisfies its gate arity. -/
theorem foldStatements_seqAt_arity :
    ∀ {ss : List RawStatement} {state final : SourceState}
      {obligations : List TheoremObligation},
      foldStatements state ss = .ok (final, obligations) →
      final.scopes.length = 0 →
      SeqAt state.scopes.length ss ∧ ∀ s ∈ ss, FoldArity s := by
  intro ss
  induction ss with
  | nil =>
      intro state final obligations h hfin
      simp [foldStatements] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨?_, fun s hs => nomatch hs⟩
      rw [hfin]
      exact SeqAt.nil
  | cons stmt rest ih =>
      intro state final obligations h hfin
      cases happ : applyStatement state stmt with
      | rejected r =>
          simp [foldStatements, happ] at h
      | ok pair =>
          obtain ⟨next, obs₁⟩ := pair
          cases hrest : foldStatements next rest with
          | rejected r =>
              simp [foldStatements, happ, hrest] at h
          | ok pair₂ =>
              obtain ⟨final₂, obs₂⟩ := pair₂
              simp [foldStatements, happ, hrest] at h
              obtain ⟨rfl, rfl⟩ := h
              obtain ⟨hseq, harity⟩ := ih hrest hfin
              cases stmt with
              | openScope site =>
                  have hop : openScope? state = some next := by
                    cases hpay : applyLocalPayload? .openScope state with
                    | none => simp [applyStatement, hpay] at happ
                    | some nxt =>
                        simp [applyStatement, hpay] at happ
                        rw [← happ.1]
                        exact hpay
                  obtain ⟨hlen, -⟩ := openScope?_scopes_pending hop
                  refine ⟨SeqAt.openScope _ site rest ?_,
                    fun s hs => ?_⟩
                  · rw [← hlen]
                    exact hseq
                  · rcases List.mem_cons.mp hs with rfl | htail
                    · trivial
                    · exact harity s htail
              | closeScope site =>
                  have hcl : ∃ middle,
                      closeScope? state = some middle ∧
                        completeBlock? middle = some next := by
                    cases hpay : applyLocalPayload? .closeScope state with
                    | none => simp [applyStatement, hpay] at happ
                    | some middle =>
                        cases hpay₂ : applyLocalPayload? .completeBlock
                            middle with
                        | none =>
                            simp [applyStatement, hpay, hpay₂] at happ
                        | some nxt =>
                            simp [applyStatement, hpay, hpay₂] at happ
                            exact ⟨middle, hpay, by
                              rw [← happ.1]
                              exact hpay₂⟩
                  obtain ⟨middle, hclose, hcomplete⟩ := hcl
                  obtain ⟨hlen, -⟩ := closeScope?_scopes_pending hclose
                  obtain ⟨hscopes, -⟩ :=
                    completeBlock?_scopes_pending hcomplete
                  rw [hlen, ← hscopes]
                  refine ⟨SeqAt.closeScope _ site rest hseq,
                    fun s hs => ?_⟩
                  rcases List.mem_cons.mp hs with rfl | htail
                  · trivial
                  · exact harity s htail
              | constDecl site names terminator =>
                  have hpay : declareConstants? state
                      (names.map (·.name)) = some next := by
                    cases hpay : applyLocalPayload?
                        (.declareConstants (names.map (·.name)))
                        state with
                    | none => simp [applyStatement, hpay] at happ
                    | some nxt =>
                        simp [applyStatement, hpay] at happ
                        rw [← happ.1]
                        exact hpay
                  obtain ⟨hne, hempty⟩ := declareConstants?_inv hpay
                  obtain ⟨hscopes, -⟩ :=
                    declareConstants?_scopes_pending hpay
                  refine ⟨SeqAt.atom _ _ rest rfl
                    (fun _ => by simp [hempty]) ?_, fun s hs => ?_⟩
                  · rw [← hscopes]
                    exact hseq
                  · rcases List.mem_cons.mp hs with rfl | htail
                    · intro hnil
                      exact hne (by simp [hnil])
                    · exact harity s htail
              | varDecl site names terminator =>
                  have hpay : declareVariables? state
                      (names.map (·.name)) = some next := by
                    cases hpay : applyLocalPayload?
                        (.declareVariables (names.map (·.name)))
                        state with
                    | none => simp [applyStatement, hpay] at happ
                    | some nxt =>
                        simp [applyStatement, hpay] at happ
                        rw [← happ.1]
                        exact hpay
                  have hne := declareVariables?_inv hpay
                  obtain ⟨hscopes, -⟩ :=
                    declareVariables?_scopes_pending hpay
                  refine ⟨SeqAt.atom _ _ rest rfl
                    (fun hc => nomatch hc) ?_, fun s hs => ?_⟩
                  · rw [← hscopes]
                    exact hseq
                  · rcases List.mem_cons.mp hs with rfl | htail
                    · intro hnil
                      exact hne (by simp [hnil])
                    · exact harity s htail
              | djDecl site names terminator =>
                  have hpay : declareDisjoint? state
                      (names.map (·.name)) = some next := by
                    cases hpay : applyLocalPayload?
                        (.declareDisjoint (names.map (·.name)))
                        state with
                    | none => simp [applyStatement, hpay] at happ
                    | some nxt =>
                        simp [applyStatement, hpay] at happ
                        rw [← happ.1]
                        exact hpay
                  have hlen := declareDisjoint?_inv hpay
                  obtain ⟨hscopes, -⟩ :=
                    declareDisjoint?_scopes_pending hpay
                  refine ⟨SeqAt.atom _ _ rest rfl
                    (fun hc => nomatch hc) ?_, fun s hs => ?_⟩
                  · rw [← hscopes]
                    exact hseq
                  · rcases List.mem_cons.mp hs with rfl | htail
                    · show 2 ≤ names.length
                      simpa using hlen
                    · exact harity s htail
              | floating site label typecode variableName terminator =>
                  have hpay : declareFloating? state label.name
                      typecode.name variableName.name = some next := by
                    cases hpay : applyLocalPayload?
                        (.declareFloating label.name typecode.name
                          variableName.name) state with
                    | none => simp [applyStatement, hpay] at happ
                    | some nxt =>
                        simp [applyStatement, hpay] at happ
                        rw [← happ.1]
                        exact hpay
                  obtain ⟨hscopes, -⟩ :=
                    declareFloating?_scopes_pending hpay
                  refine ⟨SeqAt.atom _ _ rest rfl
                    (fun hc => nomatch hc) ?_, fun s hs => ?_⟩
                  · rw [← hscopes]
                    exact hseq
                  · rcases List.mem_cons.mp hs with rfl | htail
                    · trivial
                    · exact harity s htail
              | essential site label typecode body terminator =>
                  have hpay : ∃ syms,
                      declareEssential? state label.name
                        ⟨typecode.name, syms⟩ = some next := by
                    cases htag : tagBody state body with
                    | rejected r =>
                        simp [applyStatement, htag] at happ
                    | ok syms =>
                        cases hpay : applyLocalPayload?
                            (.declareEssential label.name
                              ⟨typecode.name, syms⟩) state with
                        | none =>
                            simp [applyStatement, htag, hpay] at happ
                        | some nxt =>
                            simp [applyStatement, htag, hpay] at happ
                            exact ⟨syms, by
                              rw [← happ.1]
                              exact hpay⟩
                  obtain ⟨syms, hpay⟩ := hpay
                  obtain ⟨hscopes, -⟩ :=
                    declareEssential?_scopes_pending hpay
                  refine ⟨SeqAt.atom _ _ rest rfl
                    (fun hc => nomatch hc) ?_, fun s hs => ?_⟩
                  · rw [← hscopes]
                    exact hseq
                  · rcases List.mem_cons.mp hs with rfl | htail
                    · trivial
                    · exact harity s htail
              | axiomatic site label typecode body terminator =>
                  have hpay : ∃ syms,
                      insertAssertion? state label.name
                        ⟨typecode.name, syms⟩ = some next := by
                    cases htag : tagBody state body with
                    | rejected r =>
                        simp [applyStatement, htag] at happ
                    | ok syms =>
                        cases hpay : applyLocalPayload?
                            (.declareAxiom label.name
                              ⟨typecode.name, syms⟩) state with
                        | none =>
                            simp [applyStatement, htag, hpay] at happ
                        | some nxt =>
                            simp [applyStatement, htag, hpay] at happ
                            exact ⟨syms, by
                              rw [← happ.1]
                              exact hpay⟩
                  obtain ⟨syms, hpay⟩ := hpay
                  obtain ⟨hscopes, -⟩ :=
                    insertAssertion?_scopes_pending hpay
                  refine ⟨SeqAt.atom _ _ rest rfl
                    (fun hc => nomatch hc) ?_, fun s hs => ?_⟩
                  · rw [← hscopes]
                    exact hseq
                  · rcases List.mem_cons.mp hs with rfl | htail
                    · trivial
                    · exact harity s htail
              | provable site label typecode body proof separator
                  terminator =>
                  have hpay : ∃ syms,
                      insertAssertion? state label.name
                        ⟨typecode.name, syms⟩ = some next := by
                    cases htag : tagBody state body with
                    | rejected r =>
                        simp [applyStatement, htag] at happ
                    | ok syms =>
                        cases hpay : insertAssertion? state label.name
                            ⟨typecode.name, syms⟩ with
                        | none =>
                            simp [applyStatement, htag, hpay] at happ
                        | some nxt =>
                            simp [applyStatement, htag, hpay] at happ
                            exact ⟨syms, by
                              rw [← happ.1]
                              exact hpay⟩
                  obtain ⟨syms, hpay⟩ := hpay
                  obtain ⟨hscopes, -⟩ :=
                    insertAssertion?_scopes_pending hpay
                  refine ⟨SeqAt.atom _ _ rest rfl
                    (fun hc => nomatch hc) ?_, fun s hs => ?_⟩
                  · rw [← hscopes]
                    exact hseq
                  · rcases List.mem_cons.mp hs with rfl | htail
                    · trivial
                    · exact harity s htail

end FoldDischarge

/-! ## Pipeline inversion and the segmenter's normal-proof arity -/

section PipelineInversion

open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceGSLTIncludeDAG in
/-- Invert an accepted composed run into its stage acceptances. -/
theorem runSource_ok_inv {files : FileMap} {policy : IncludePolicy}
    {root : String} {fuel : Nat} {state : SourceState}
    {obligations : List TheoremObligation}
    (h : runSource files policy root fuel = .ok state obligations) :
    ∃ (spans : List
        Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical.LocatedByteSpan)
      (tokens : List LocatedToken) (statements : List RawStatement),
      expandDatabase files policy root fuel = .ok spans ∧
        resolveTokens files spans = some tokens ∧
        segmentStatements tokens = .ok statements ∧
        foldStatements initialState statements =
          .ok (state, obligations) ∧
        sourceStateComplete state = true := by
  simp only [runSource] at h
  cases hexp : expandDatabase files policy root fuel with
  | rejected r => simp only [hexp] at h; exact nomatch h
  | ok spans =>
      simp only [hexp] at h
      cases hres : resolveTokens files spans with
      | none => simp only [hres] at h; exact nomatch h
      | some tokens =>
          simp only [hres] at h
          cases hseg : segmentStatements tokens with
          | rejected r => simp only [hseg] at h; exact nomatch h
          | ok statements =>
              simp only [hseg] at h
              cases hfold : foldStatements initialState statements with
              | rejected r => simp only [hfold] at h; exact nomatch h
              | ok pair =>
                  obtain ⟨final, obs⟩ := pair
                  simp only [hfold] at h
                  cases hcomplete : sourceStateComplete final with
                  | false =>
                      simp only [hcomplete] at h
                      cases hsites : scopeSites statements [] with
                      | nil => simp only [hsites] at h; exact nomatch h
                      | cons site rest =>
                          simp only [hsites] at h; exact nomatch h
                  | true =>
                      simp only [hcomplete, if_true] at h
                      simp at h
                      obtain ⟨rfl, rfl⟩ := h
                      exact ⟨spans, tokens, statements, rfl, hres,
                        hseg, hfold, hcomplete⟩

/-- `sourceStateComplete` forces an empty scope stack. -/
theorem sourceStateComplete_scopes_length {state : SourceState}
    (h : sourceStateComplete state = true) :
    state.scopes.length = 0 := by
  unfold sourceStateComplete at h
  cases hs : state.scopes with
  | nil => rfl
  | cons a l =>
      rw [Bool.and_assoc] at h
      obtain ⟨-, h⟩ := Bool.and_eq_true_iff.mp h
      obtain ⟨hempty, -⟩ := Bool.and_eq_true_iff.mp h
      rw [hs] at hempty
      simp at hempty

/-- Normal-proof arity: the segmenter only emits nonempty step lists. -/
def NormalStepsOK : RawStatement → Prop
  | .provable _ _ _ _ (.normal steps) _ _ => steps ≠ []
  | _ => True

/-- Mode invariant backing `NormalStepsOK`. -/
def ModeSteps : SegMode → Prop
  | .proofNormal _ _ _ _ acc => acc ≠ []
  | _ => True

set_option maxHeartbeats 1000000 in
theorem segmentStep_normalSteps {mode : SegMode} {tok : LocatedToken}
    {emitted : List RawStatement} {nextMode : SegMode}
    (hmode : ModeSteps mode)
    (h : segmentStep mode tok = .ok (emitted, nextMode)) :
    ModeSteps nextMode ∧ ∀ s ∈ emitted, NormalStepsOK s := by
  cases mode <;>
    simp only [segmentStep] at h <;>
    repeat' split at h
  all_goals first
    | contradiction
    | (simp only [SegResult.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨h1, h2⟩ := h
       subst h1
       subst h2
       try simp only [ModeSteps] at hmode
       refine ⟨by simp [ModeSteps], by simp [NormalStepsOK, hmode]⟩)

theorem segmentRun_normalSteps :
    ∀ {tokens : List LocatedToken} {mode : SegMode}
      {acc statements : List RawStatement},
      segmentRun tokens mode acc = .ok statements →
      ModeSteps mode → (∀ s ∈ acc, NormalStepsOK s) →
      ∀ s ∈ statements, NormalStepsOK s := by
  intro tokens
  induction tokens with
  | nil =>
      intro mode acc statements h hmode hacc
      cases hsite : mode.site with
      | none =>
          simp only [segmentRun, hsite] at h
          cases h
          intro s hs
          exact hacc s (by simpa using hs)
      | some site =>
          simp only [segmentRun, hsite] at h
          exact absurd h (by simp)
  | cons tok rest ih =>
      intro mode acc statements h hmode hacc
      cases hstep : segmentStep mode tok with
      | rejected r =>
          simp only [segmentRun, hstep] at h
          exact absurd h (by simp)
      | ok pair =>
          obtain ⟨emitted, nextMode⟩ := pair
          simp only [segmentRun, hstep] at h
          obtain ⟨hnext, hemit⟩ := segmentStep_normalSteps hmode hstep
          refine ih h hnext ?_
          intro s hs
          rcases List.mem_append.mp hs with hrev | hold
          · exact hemit s (by simpa using hrev)
          · exact hacc s hold

/-- Every accepted segmentation emits only nonempty normal proofs. -/
theorem segmentStatements_normalSteps
    {tokens : List LocatedToken} {statements : List RawStatement}
    (h : segmentStatements tokens = .ok statements) :
    ∀ s ∈ statements, NormalStepsOK s :=
  segmentRun_normalSteps h trivial (fun _ hs => nomatch hs)

/-- Nonempty compressed bodies, enforced by the segmenter's
`.proofWords` terminator guard. -/
def CompressedWordsOK : RawStatement → Prop
  | .provable _ _ _ _ (.compressed _ _ _ words) _ _ => words ≠ []
  | _ => True

set_option maxHeartbeats 1000000 in
theorem segmentStep_compressedWords {mode : SegMode}
    {tok : LocatedToken} {emitted : List RawStatement}
    {nextMode : SegMode}
    (h : segmentStep mode tok = .ok (emitted, nextMode)) :
    ∀ s ∈ emitted, CompressedWordsOK s := by
  cases mode <;>
    simp only [segmentStep] at h <;>
    repeat' split at h
  all_goals first
    | contradiction
    | (simp only [SegResult.ok.injEq, Prod.mk.injEq] at h
       obtain ⟨h1, h2⟩ := h
       subst h1
       subst h2
       simp_all [CompressedWordsOK])

theorem segmentRun_compressedWords :
    ∀ {tokens : List LocatedToken} {mode : SegMode}
      {acc statements : List RawStatement},
      segmentRun tokens mode acc = .ok statements →
      (∀ s ∈ acc, CompressedWordsOK s) →
      ∀ s ∈ statements, CompressedWordsOK s := by
  intro tokens
  induction tokens with
  | nil =>
      intro mode acc statements h hacc
      cases hsite : mode.site with
      | none =>
          simp only [segmentRun, hsite] at h
          cases h
          intro s hs
          exact hacc s (by simpa using hs)
      | some site =>
          simp only [segmentRun, hsite] at h
          exact absurd h (by simp)
  | cons tok rest ih =>
      intro mode acc statements h hacc
      cases hstep : segmentStep mode tok with
      | rejected r =>
          simp only [segmentRun, hstep] at h
          exact absurd h (by simp)
      | ok pair =>
          obtain ⟨emitted, nextMode⟩ := pair
          simp only [segmentRun, hstep] at h
          refine ih h ?_
          intro s hs
          rcases List.mem_append.mp hs with hrev | hold
          · exact segmentStep_compressedWords hstep s
              (by simpa using hrev)
          · exact hacc s hold

/-- Every accepted segmentation emits only nonempty compressed
bodies. -/
theorem segmentStatements_compressedWords
    {tokens : List LocatedToken} {statements : List RawStatement}
    (h : segmentStatements tokens = .ok statements) :
    ∀ s ∈ statements, CompressedWordsOK s :=
  segmentRun_compressedWords h (fun _ hs => nomatch hs)

end PipelineInversion

/-! ## Reflection: rule dispatch for the lexicalized source grammar -/

theorem statement_include_mem :
    sourceProductions[20]? = some
      { label := "statement_include", category := outerStatementSort
        params := [.simple "path" (.base includePathTokenSort)]
        syntaxPattern := [.terminal "$[", .nonTerminal "path",
          .terminal "$]"] } := rfl

/-- Every leaf rule produced by the generic extraction has the
single-terminal shape. -/
theorem lexicalGrammarRulesFrom_shape
    (declarations : List LexicalDeclaration)
    (source : ClassifiedSource) :
    ∀ (tokens : List ClassifiedToken) (start : Nat) {r : GrammarRule},
      r ∈ lexicalGrammarRulesFrom declarations source tokens start →
      ∃ (index : Nat) (token : ClassifiedToken) (sort : String),
        lexicalSort? declarations token = some sort ∧
          r = lexicalGrammarRule source index token sort := by
  intro tokens
  induction tokens with
  | nil =>
      intro start r hr
      simp [lexicalGrammarRulesFrom] at hr
  | cons t rest ih =>
      intro start r hr
      simp only [lexicalGrammarRulesFrom] at hr
      cases hs : lexicalSort? declarations t with
      | none =>
          simp only [hs] at hr
          exact ih (start + 1) hr
      | some s =>
          simp only [hs] at hr
          rcases List.mem_cons.mp hr with rfl | htail
          · exact ⟨start, t, s, hs, rfl⟩
          · exact ih (start + 1) htail

private theorem lexicalDeclarationSort?_lexicalClass {c s : String}
    {token : ClassifiedToken} {sort : String}
    (h : lexicalDeclarationSort? (.lexicalClass c s) token =
      some sort) :
    sort = s := by
  simp only [lexicalDeclarationSort?] at h
  split at h
  · exact (Option.some.inj h).symm
  · exact absurd h (by simp)

/-- The authored lexical declarations classify only into the five token
sorts. -/
theorem lexicalSort?_cases {token : ClassifiedToken} {sort : String}
    (h : lexicalSort? lexicalDeclarations token = some sort) :
    sort = labelTokenSort ∨ sort = symbolTokenSort ∨
      sort = proofLabelTokenSort ∨ sort = compressedWordTokenSort ∨
      sort = includePathTokenSort := by
  simp only [lexicalDeclarations, lexicalSort?] at h
  cases h₁ : lexicalDeclarationSort?
      (.lexicalClass "mm-label" labelTokenSort) token with
  | some s =>
      simp only [h₁] at h
      obtain rfl := Option.some.inj h
      exact Or.inl (lexicalDeclarationSort?_lexicalClass h₁)
  | none =>
  simp only [h₁] at h
  cases h₂ : lexicalDeclarationSort?
      (.lexicalClass "mm-symbol" symbolTokenSort) token with
  | some s =>
      simp only [h₂] at h
      obtain rfl := Option.some.inj h
      exact Or.inr (Or.inl (lexicalDeclarationSort?_lexicalClass h₂))
  | none =>
  simp only [h₂] at h
  cases h₃ : lexicalDeclarationSort?
      (.lexicalClass "mm-proof-label" proofLabelTokenSort) token with
  | some s =>
      simp only [h₃] at h
      obtain rfl := Option.some.inj h
      exact Or.inr (Or.inr (Or.inl
        (lexicalDeclarationSort?_lexicalClass h₃)))
  | none =>
  simp only [h₃] at h
  cases h₄ : lexicalDeclarationSort?
      (.lexicalClass "mm-compressed-word" compressedWordTokenSort)
      token with
  | some s =>
      simp only [h₄] at h
      obtain rfl := Option.some.inj h
      exact Or.inr (Or.inr (Or.inr (Or.inl
        (lexicalDeclarationSort?_lexicalClass h₄))))
  | none =>
  simp only [h₄] at h
  cases h₅ : lexicalDeclarationSort?
      (.lexicalClass "mm-include-path" includePathTokenSort) token with
  | some s =>
      simp only [h₅] at h
      obtain rfl := Option.some.inj h
      exact Or.inr (Or.inr (Or.inr (Or.inr
        (lexicalDeclarationSort?_lexicalClass h₅))))
  | none =>
      simp only [h₅] at h
      exact absurd h (by simp)

/-- Rule dispatch: every rule of the lexicalized source language is a
lexical leaf or an authored production. -/
theorem lexicalized_rule_cases {source : ClassifiedSource}
    {r : GrammarRule}
    (hr : r ∈ (lexicalizedLanguage sourceGrammar lexicalDeclarations
      source).terms) :
    (∃ (index : Nat) (token : ClassifiedToken) (sort : String),
        lexicalSort? lexicalDeclarations token = some sort ∧
          r = lexicalGrammarRule source index token sort) ∨
      r ∈ sourceProductions := by
  simp only [lexicalizedLanguage, lexicalGrammarRules,
    List.mem_append] at hr
  rcases hr with hleaf | hprod
  · exact Or.inl
      (lexicalGrammarRulesFrom_shape lexicalDeclarations source
        source.tokens 0 hleaf)
  · exact Or.inr hprod

/-! ## Authored rules by category (kernel-enumerated) -/

section CategoryInventories

private theorem mem_enum {r : GrammarRule} (hr : r ∈ sourceProductions) :
    ∃ i, i < 27 ∧ sourceProductions[i]? = some r := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hr
  obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hi
  have h27 : sourceProductions.length = 27 := rfl
  rw [h27] at hlt
  exact ⟨i, hlt, hi⟩

/-- Skeleton discharge used by every category inventory below. -/
local macro "category_enum" hr:ident hcat:ident : tactic =>
  `(tactic|
    (obtain ⟨i, hlt, hi⟩ := mem_enum $hr
     interval_cases i <;>
       simp only [symbols_one_mem, symbols_more_mem, disjoint_two_mem,
         disjoint_more_mem, proof_one_mem, proof_more_mem,
         proof_unknown_one_mem, proof_unknown_more_mem,
         header_empty_mem, header_more_mem, compressed_one_mem,
         compressed_more_mem, statement_const_mem, statement_var_mem,
         statement_disjoint_mem, statement_float_mem,
         statement_essential_mem, statement_axiom_mem,
         statement_theorem_normal_mem,
         statement_theorem_compressed_mem, statement_include_mem,
         statement_block_mem, database_empty_mem, database_more_mem,
         outer_statement_inner_mem, outer_database_empty_mem,
         outer_database_more_mem, Option.some.injEq] at hi <;>
       subst hi <;>
       revert $hcat <;>
       simp [labelTokenSort, symbolTokenSort, proofLabelTokenSort,
         compressedWordTokenSort, includePathTokenSort, symbolListSort,
         disjointSymbolListSort, proofListSort, proofHeaderListSort,
         compressedWordListSort, statementSort, databaseSort,
         outerStatementSort, outerDatabaseSort]))

set_option maxHeartbeats 1000000 in
/-- No authored production carries a token-sort category. -/
theorem no_authored_token_rule {r : GrammarRule}
    (hr : r ∈ sourceProductions)
    (hcat : r.category = labelTokenSort ∨
      r.category = symbolTokenSort ∨
      r.category = proofLabelTokenSort ∨
      r.category = compressedWordTokenSort ∨
      r.category = includePathTokenSort) : False := by
  category_enum hr hcat

set_option maxHeartbeats 1000000 in
private theorem symbolListRules_cases {r : GrammarRule}
    (hr : r ∈ sourceProductions) (hcat : r.category = symbolListSort) :
    r = { label := "symbols_one", category := symbolListSort
          params := [.simple "symbol" (.base symbolTokenSort)]
          syntaxPattern := [.nonTerminal "symbol"] } ∨
      r = { label := "symbols_more", category := symbolListSort
            params := [.simple "symbol" (.base symbolTokenSort),
              .simple "rest" (.base symbolListSort)]
            syntaxPattern := [.nonTerminal "symbol",
              .nonTerminal "rest"] } := by
  category_enum hr hcat

set_option maxHeartbeats 1000000 in
private theorem disjointListRules_cases {r : GrammarRule}
    (hr : r ∈ sourceProductions)
    (hcat : r.category = disjointSymbolListSort) :
    r = { label := "disjoint_symbols_two"
          category := disjointSymbolListSort
          params := [.simple "first" (.base symbolTokenSort),
            .simple "second" (.base symbolTokenSort)]
          syntaxPattern := [.nonTerminal "first",
            .nonTerminal "second"] } ∨
      r = { label := "disjoint_symbols_more"
            category := disjointSymbolListSort
            params := [.simple "first" (.base symbolTokenSort),
              .simple "rest" (.base disjointSymbolListSort)]
            syntaxPattern := [.nonTerminal "first",
              .nonTerminal "rest"] } := by
  category_enum hr hcat

set_option maxHeartbeats 1000000 in
private theorem proofListRules_cases {r : GrammarRule}
    (hr : r ∈ sourceProductions) (hcat : r.category = proofListSort) :
    r = { label := "proof_one", category := proofListSort
          params := [.simple "label" (.base proofLabelTokenSort)]
          syntaxPattern := [.nonTerminal "label"] } ∨
      r = { label := "proof_more", category := proofListSort
            params := [.simple "label" (.base proofLabelTokenSort),
              .simple "rest" (.base proofListSort)]
            syntaxPattern := [.nonTerminal "label",
              .nonTerminal "rest"] } ∨
      r = { label := "proof_unknown_one", category := proofListSort
            params := []
            syntaxPattern := [.terminal "?"] } ∨
      r = { label := "proof_unknown_more", category := proofListSort
            params := [.simple "rest" (.base proofListSort)]
            syntaxPattern := [.terminal "?", .nonTerminal "rest"] } := by
  category_enum hr hcat

set_option maxHeartbeats 1000000 in
private theorem headerListRules_cases {r : GrammarRule}
    (hr : r ∈ sourceProductions)
    (hcat : r.category = proofHeaderListSort) :
    r = { label := "header_empty", category := proofHeaderListSort
          params := []
          syntaxPattern := [] } ∨
      r = { label := "header_more", category := proofHeaderListSort
            params := [.simple "label" (.base proofLabelTokenSort),
              .simple "rest" (.base proofHeaderListSort)]
            syntaxPattern := [.nonTerminal "label",
              .nonTerminal "rest"] } := by
  category_enum hr hcat

set_option maxHeartbeats 1000000 in
private theorem compressedListRules_cases {r : GrammarRule}
    (hr : r ∈ sourceProductions)
    (hcat : r.category = compressedWordListSort) :
    r = { label := "compressed_one", category := compressedWordListSort
          params := [.simple "word" (.base compressedWordTokenSort)]
          syntaxPattern := [.nonTerminal "word"] } ∨
      r = { label := "compressed_more"
            category := compressedWordListSort
            params := [.simple "word" (.base compressedWordTokenSort),
              .simple "rest" (.base compressedWordListSort)]
            syntaxPattern := [.nonTerminal "word",
              .nonTerminal "rest"] } := by
  category_enum hr hcat

set_option maxHeartbeats 1000000 in
private theorem statementRules_cases {r : GrammarRule}
    (hr : r ∈ sourceProductions) (hcat : r.category = statementSort) :
    r = { label := "statement_var", category := statementSort
          params := [.simple "symbols" (.base symbolListSort)]
          syntaxPattern := [.terminal "$v", .nonTerminal "symbols",
            .terminal "$."] } ∨
      r = { label := "statement_disjoint", category := statementSort
            params := [.simple "symbols" (.base disjointSymbolListSort)]
            syntaxPattern := [.terminal "$d", .nonTerminal "symbols",
              .terminal "$."] } ∨
      r = { label := "statement_float", category := statementSort
            params := [.simple "label" (.base labelTokenSort),
              .simple "typecode" (.base symbolTokenSort),
              .simple "variable" (.base symbolTokenSort)]
            syntaxPattern := [.nonTerminal "label", .terminal "$f",
              .nonTerminal "typecode", .nonTerminal "variable",
              .terminal "$."] } ∨
      r = { label := "statement_essential", category := statementSort
            params := [.simple "label" (.base labelTokenSort),
              .simple "formula" (.base symbolListSort)]
            syntaxPattern := [.nonTerminal "label", .terminal "$e",
              .nonTerminal "formula", .terminal "$."] } ∨
      r = { label := "statement_axiom", category := statementSort
            params := [.simple "label" (.base labelTokenSort),
              .simple "formula" (.base symbolListSort)]
            syntaxPattern := [.nonTerminal "label", .terminal "$a",
              .nonTerminal "formula", .terminal "$."] } ∨
      r = { label := "statement_theorem_normal", category := statementSort
            params := [.simple "label" (.base labelTokenSort),
              .simple "formula" (.base symbolListSort),
              .simple "proof" (.base proofListSort)]
            syntaxPattern := [.nonTerminal "label", .terminal "$p",
              .nonTerminal "formula", .terminal "$=",
              .nonTerminal "proof", .terminal "$."] } ∨
      r = { label := "statement_theorem_compressed"
            category := statementSort
            params := [.simple "label" (.base labelTokenSort),
              .simple "formula" (.base symbolListSort),
              .simple "header" (.base proofHeaderListSort),
              .simple "body" (.base compressedWordListSort)]
            syntaxPattern := [.nonTerminal "label", .terminal "$p",
              .nonTerminal "formula", .terminal "$=", .terminal "(",
              .nonTerminal "header", .terminal ")",
              .nonTerminal "body", .terminal "$."] } ∨
      r = { label := "statement_block", category := statementSort
            params := [.simple "inside" (.base databaseSort)]
            syntaxPattern := [.terminal "${", .nonTerminal "inside",
              .terminal "$}"] } := by
  category_enum hr hcat

set_option maxHeartbeats 1000000 in
private theorem outerStatementRules_cases {r : GrammarRule}
    (hr : r ∈ sourceProductions)
    (hcat : r.category = outerStatementSort) :
    r = { label := "statement_const", category := outerStatementSort
          params := [.simple "symbols" (.base symbolListSort)]
          syntaxPattern := [.terminal "$c", .nonTerminal "symbols",
            .terminal "$."] } ∨
      r = { label := "statement_include", category := outerStatementSort
            params := [.simple "path" (.base includePathTokenSort)]
            syntaxPattern := [.terminal "$[", .nonTerminal "path",
              .terminal "$]"] } ∨
      r = { label := "outer_statement_inner"
            category := outerStatementSort
            params := [.simple "statement" (.base statementSort)]
            syntaxPattern := [.nonTerminal "statement"] } := by
  category_enum hr hcat

set_option maxHeartbeats 1000000 in
private theorem databaseRules_cases {r : GrammarRule}
    (hr : r ∈ sourceProductions) (hcat : r.category = databaseSort) :
    r = { label := "database_empty", category := databaseSort
          params := []
          syntaxPattern := [] } ∨
      r = { label := "database_more", category := databaseSort
            params := [.simple "statement" (.base statementSort),
              .simple "rest" (.base databaseSort)]
            syntaxPattern := [.nonTerminal "statement",
              .nonTerminal "rest"] } := by
  category_enum hr hcat

set_option maxHeartbeats 1000000 in
private theorem outerDatabaseRules_cases {r : GrammarRule}
    (hr : r ∈ sourceProductions)
    (hcat : r.category = outerDatabaseSort) :
    r = { label := "outer_database_empty", category := outerDatabaseSort
          params := []
          syntaxPattern := [] } ∨
      r = { label := "outer_database_more"
            category := outerDatabaseSort
            params := [.simple "statement" (.base outerStatementSort),
              .simple "rest" (.base outerDatabaseSort)]
            syntaxPattern := [.nonTerminal "statement",
              .nonTerminal "rest"] } := by
  category_enum hr hcat

end CategoryInventories

/-! ## Leaf reflection at the token sorts -/

theorem tokenLeaf_reflects {source : ClassifiedSource} {sort : String}
    (hsort : sort = labelTokenSort ∨ sort = symbolTokenSort ∨
      sort = proofLabelTokenSort ∨ sort = compressedWordTokenSort ∨
      sort = includePathTokenSort)
    {toks : List String} {tree : Pattern}
    (h : Derives (lexicalizedLanguage sourceGrammar lexicalDeclarations
      source) sort toks tree) :
    ∃ t, toks = [t] ∧
      TokenLeaf
        (lexicalizedLanguage sourceGrammar lexicalDeclarations source)
        sort t := by
  cases h with
  | rule r hr sort' hcat toks' kids hitems =>
      rcases lexicalized_rule_cases hr with
        ⟨idx, token, s', hs', rfl⟩ | hprod
      · have hsyn :
            (lexicalGrammarRule source idx token s').syntaxPattern =
              [.terminal token.serialized] := rfl
        rw [hsyn] at hitems
        cases hitems with
        | terminal _ tok rest toks₀ kids₀ htail =>
            cases htail
            exact ⟨token.serialized, rfl, ⟨_, hr, hcat, rfl, rfl⟩⟩
      · exact absurd hcat (by
          intro hcontra
          exact no_authored_token_rule hprod (by
            rcases hsort with rfl | rfl | rfl | rfl | rfl
            · exact Or.inl hcontra
            · exact Or.inr (Or.inl hcontra)
            · exact Or.inr (Or.inr (Or.inl hcontra))
            · exact Or.inr (Or.inr (Or.inr (Or.inl hcontra)))
            · exact Or.inr (Or.inr (Or.inr (Or.inr hcontra)))))

/-! ## List-sort reflections -/

private theorem pattern_sizeOf_pos (tree : Pattern) : 0 < sizeOf tree := by
  cases tree <;> simp

private theorem leaf_not_internal {source : ClassifiedSource}
    {idx : Nat} {token : ClassifiedToken} {s' target : String}
    (hs' : lexicalSort? lexicalDeclarations token = some s')
    (hcat : (lexicalGrammarRule source idx token s').category = target)
    (htarget : target = symbolListSort ∨
      target = disjointSymbolListSort ∨ target = proofListSort ∨
      target = proofHeaderListSort ∨ target = compressedWordListSort ∨
      target = statementSort ∨ target = databaseSort ∨
      target = outerStatementSort ∨ target = outerDatabaseSort) :
    False := by
  have hcat' : s' = target := hcat
  rcases lexicalSort?_cases hs' with rfl | rfl | rfl | rfl | rfl <;>
    rcases htarget with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [labelTokenSort, symbolTokenSort, proofLabelTokenSort,
      compressedWordTokenSort, includePathTokenSort, symbolListSort,
      disjointSymbolListSort, proofListSort, proofHeaderListSort,
      compressedWordListSort, statementSort, databaseSort,
      outerStatementSort, outerDatabaseSort] at hcat'

theorem symbolList_reflects {source : ClassifiedSource} :
    ∀ (n : Nat) (tree : Pattern), sizeOf tree ≤ n →
      ∀ {toks : List String},
        Derives (lexicalizedLanguage sourceGrammar lexicalDeclarations
          source) symbolListSort toks tree →
        toks ≠ [] ∧ ∀ t ∈ toks,
          TokenLeaf (lexicalizedLanguage sourceGrammar
            lexicalDeclarations source) symbolTokenSort t := by
  intro n
  induction n with
  | zero =>
      intro tree hsize
      have := pattern_sizeOf_pos tree
      omega
  | succ n ihn =>
      intro tree hsize toks h
      cases h with
      | rule r hr sort' hcat toks' kids hitems =>
          rcases lexicalized_rule_cases hr with
            ⟨idx, token, s', hs', rfl⟩ | hprod
          · exact absurd hcat (fun hcontra =>
              leaf_not_internal hs' hcontra (Or.inl rfl))
          · rcases symbolListRules_cases hprod hcat with rfl | rfl
            · cases hitems with
              | nonTerminal _ nm srt hsrt sub tsub hsub rest' toks₂
                  kids₂ hrest =>
                  cases hrest
                  obtain rfl := Option.some.inj hsrt
                  obtain ⟨t, rfl, hleaf⟩ :=
                    tokenLeaf_reflects (Or.inr (Or.inl rfl)) hsub
                  refine ⟨by simp, ?_⟩
                  intro x hx
                  simp only [List.append_nil, List.mem_singleton] at hx
                  subst hx
                  exact hleaf
            · cases hitems with
              | nonTerminal _ nm₁ srt₁ hsrt₁ sub₁ tsub₁ hsub₁ rest₁
                  toks₂ kids₂ hrest₁ =>
              cases hrest₁ with
              | nonTerminal _ nm₂ srt₂ hsrt₂ sub₂ tsub₂ hsub₂ rest₂
                  toks₃ kids₃ hrest₂ =>
              cases hrest₂
              obtain rfl := Option.some.inj hsrt₁
              obtain rfl := Option.some.inj hsrt₂
              obtain ⟨t, rfl, hleaf⟩ :=
                tokenLeaf_reflects (Or.inr (Or.inl rfl)) hsub₁
              have hlt : sizeOf tsub₂ ≤ n := by
                have hmem : tsub₂ ∈ [tsub₁, tsub₂] := by simp
                have := List.sizeOf_lt_of_mem hmem
                simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec,
                  Pattern.apply.sizeOf_spec] at hsize this
                omega
              obtain ⟨hne, hleaves⟩ := ihn tsub₂ hlt hsub₂
              refine ⟨by simp, ?_⟩
              intro x hx
              simp only [List.append_nil, List.cons_append,
                List.nil_append, List.mem_cons] at hx
              rcases hx with rfl | hx₂
              · exact hleaf
              · exact hleaves x hx₂

theorem disjointList_reflects {source : ClassifiedSource} :
    ∀ (n : Nat) (tree : Pattern), sizeOf tree ≤ n →
      ∀ {toks : List String},
        Derives (lexicalizedLanguage sourceGrammar lexicalDeclarations
          source) disjointSymbolListSort toks tree →
        2 ≤ toks.length ∧ ∀ t ∈ toks,
          TokenLeaf (lexicalizedLanguage sourceGrammar
            lexicalDeclarations source) symbolTokenSort t := by
  intro n
  induction n with
  | zero =>
      intro tree hsize
      have := pattern_sizeOf_pos tree
      omega
  | succ n ihn =>
      intro tree hsize toks h
      cases h with
      | rule r hr sort' hcat toks' kids hitems =>
          rcases lexicalized_rule_cases hr with
            ⟨idx, token, s', hs', rfl⟩ | hprod
          · exact absurd hcat (fun hcontra =>
              leaf_not_internal hs' hcontra (Or.inr (Or.inl rfl)))
          · rcases disjointListRules_cases hprod hcat with rfl | rfl
            · cases hitems with
              | nonTerminal _ nm₁ srt₁ hsrt₁ sub₁ tsub₁ hsub₁ rest₁
                  toks₂ kids₂ hrest₁ =>
              cases hrest₁ with
              | nonTerminal _ nm₂ srt₂ hsrt₂ sub₂ tsub₂ hsub₂ rest₂
                  toks₃ kids₃ hrest₂ =>
              cases hrest₂
              obtain rfl := Option.some.inj hsrt₁
              obtain rfl := Option.some.inj hsrt₂
              obtain ⟨t₁, rfl, hleaf₁⟩ :=
                tokenLeaf_reflects (Or.inr (Or.inl rfl)) hsub₁
              obtain ⟨t₂, rfl, hleaf₂⟩ :=
                tokenLeaf_reflects (Or.inr (Or.inl rfl)) hsub₂
              refine ⟨by simp, ?_⟩
              intro x hx
              simp only [List.append_nil, List.cons_append,
                List.nil_append, List.mem_cons] at hx
              rcases hx with rfl | rfl | hx
              · exact hleaf₁
              · exact hleaf₂
              · exact absurd hx (List.not_mem_nil)
            · cases hitems with
              | nonTerminal _ nm₁ srt₁ hsrt₁ sub₁ tsub₁ hsub₁ rest₁
                  toks₂ kids₂ hrest₁ =>
              cases hrest₁ with
              | nonTerminal _ nm₂ srt₂ hsrt₂ sub₂ tsub₂ hsub₂ rest₂
                  toks₃ kids₃ hrest₂ =>
              cases hrest₂
              obtain rfl := Option.some.inj hsrt₁
              obtain rfl := Option.some.inj hsrt₂
              obtain ⟨t, rfl, hleaf⟩ :=
                tokenLeaf_reflects (Or.inr (Or.inl rfl)) hsub₁
              have hlt : sizeOf tsub₂ ≤ n := by
                have hmem : tsub₂ ∈ [tsub₁, tsub₂] := by simp
                have := List.sizeOf_lt_of_mem hmem
                simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec,
                  Pattern.apply.sizeOf_spec] at hsize this
                omega
              obtain ⟨hlen, hleaves⟩ := ihn tsub₂ hlt hsub₂
              refine ⟨by simp; omega, ?_⟩
              intro x hx
              simp only [List.append_nil, List.cons_append,
                List.nil_append, List.mem_cons] at hx
              rcases hx with rfl | hx₂
              · exact hleaf
              · exact hleaves x hx₂

theorem proofList_reflects {source : ClassifiedSource} :
    ∀ (n : Nat) (tree : Pattern), sizeOf tree ≤ n →
      ∀ {toks : List String},
        Derives (lexicalizedLanguage sourceGrammar lexicalDeclarations
          source) proofListSort toks tree →
        toks ≠ [] ∧ ∀ t ∈ toks,
          TokenLeaf (lexicalizedLanguage sourceGrammar
            lexicalDeclarations source) proofLabelTokenSort t ∨
            t = "?" := by
  intro n
  induction n with
  | zero =>
      intro tree hsize
      have := pattern_sizeOf_pos tree
      omega
  | succ n ihn =>
      intro tree hsize toks h
      cases h with
      | rule r hr sort' hcat toks' kids hitems =>
          rcases lexicalized_rule_cases hr with
            ⟨idx, token, s', hs', rfl⟩ | hprod
          · exact absurd hcat (fun hcontra =>
              leaf_not_internal hs' hcontra
                (Or.inr (Or.inr (Or.inl rfl))))
          · rcases proofListRules_cases hprod hcat with
              rfl | rfl | rfl | rfl
            · cases hitems with
              | nonTerminal _ nm srt hsrt sub tsub hsub rest' toks₂
                  kids₂ hrest =>
                  cases hrest
                  obtain rfl := Option.some.inj hsrt
                  obtain ⟨t, rfl, hleaf⟩ :=
                    tokenLeaf_reflects
                      (Or.inr (Or.inr (Or.inl rfl))) hsub
                  refine ⟨by simp, ?_⟩
                  intro x hx
                  simp only [List.append_nil, List.mem_singleton] at hx
                  subst hx
                  exact Or.inl hleaf
            · cases hitems with
              | nonTerminal _ nm₁ srt₁ hsrt₁ sub₁ tsub₁ hsub₁ rest₁
                  toks₂ kids₂ hrest₁ =>
              cases hrest₁ with
              | nonTerminal _ nm₂ srt₂ hsrt₂ sub₂ tsub₂ hsub₂ rest₂
                  toks₃ kids₃ hrest₂ =>
              cases hrest₂
              obtain rfl := Option.some.inj hsrt₁
              obtain rfl := Option.some.inj hsrt₂
              obtain ⟨t, rfl, hleaf⟩ :=
                tokenLeaf_reflects (Or.inr (Or.inr (Or.inl rfl))) hsub₁
              have hlt : sizeOf tsub₂ ≤ n := by
                have hmem : tsub₂ ∈ [tsub₁, tsub₂] := by simp
                have := List.sizeOf_lt_of_mem hmem
                simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec,
                  Pattern.apply.sizeOf_spec] at hsize this
                omega
              obtain ⟨hne, hsteps⟩ := ihn tsub₂ hlt hsub₂
              refine ⟨by simp, ?_⟩
              intro x hx
              simp only [List.append_nil, List.cons_append,
                List.nil_append, List.mem_cons] at hx
              rcases hx with rfl | hx₂
              · exact Or.inl hleaf
              · exact hsteps x hx₂
            · cases hitems with
              | terminal _ tok rest' toks₂ kids₂ htail =>
                  cases htail
                  exact ⟨by simp, by simp⟩
            · cases hitems with
              | terminal _ tok rest' toks₂ kids₂ htail =>
              cases htail with
              | nonTerminal _ nm srt hsrt sub tsub hsub rest₂ toks₃
                  kids₃ hrest =>
                  cases hrest
                  obtain rfl := Option.some.inj hsrt
                  have hlt : sizeOf tsub ≤ n := by
                    have hmem : tsub ∈ [tsub] := by simp
                    have := List.sizeOf_lt_of_mem hmem
                    simp only [List.cons.sizeOf_spec,
                      List.nil.sizeOf_spec,
                      Pattern.apply.sizeOf_spec] at hsize this
                    omega
                  obtain ⟨hne, hsteps⟩ := ihn tsub hlt hsub
                  refine ⟨by simp, ?_⟩
                  intro x hx
                  simp only [List.append_nil, List.mem_cons] at hx
                  rcases hx with rfl | hx₂
                  · exact Or.inr rfl
                  · exact hsteps x hx₂

theorem headerList_reflects {source : ClassifiedSource} :
    ∀ (n : Nat) (tree : Pattern), sizeOf tree ≤ n →
      ∀ {toks : List String},
        Derives (lexicalizedLanguage sourceGrammar lexicalDeclarations
          source) proofHeaderListSort toks tree →
        ∀ t ∈ toks,
          TokenLeaf (lexicalizedLanguage sourceGrammar
            lexicalDeclarations source) proofLabelTokenSort t := by
  intro n
  induction n with
  | zero =>
      intro tree hsize
      have := pattern_sizeOf_pos tree
      omega
  | succ n ihn =>
      intro tree hsize toks h
      cases h with
      | rule r hr sort' hcat toks' kids hitems =>
          rcases lexicalized_rule_cases hr with
            ⟨idx, token, s', hs', rfl⟩ | hprod
          · exact absurd hcat (fun hcontra =>
              leaf_not_internal hs' hcontra
                (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
          · rcases headerListRules_cases hprod hcat with rfl | rfl
            · cases hitems
              simp
            · cases hitems with
              | nonTerminal _ nm₁ srt₁ hsrt₁ sub₁ tsub₁ hsub₁ rest₁
                  toks₂ kids₂ hrest₁ =>
              cases hrest₁ with
              | nonTerminal _ nm₂ srt₂ hsrt₂ sub₂ tsub₂ hsub₂ rest₂
                  toks₃ kids₃ hrest₂ =>
              cases hrest₂
              obtain rfl := Option.some.inj hsrt₁
              obtain rfl := Option.some.inj hsrt₂
              obtain ⟨t, rfl, hleaf⟩ :=
                tokenLeaf_reflects (Or.inr (Or.inr (Or.inl rfl))) hsub₁
              have hlt : sizeOf tsub₂ ≤ n := by
                have hmem : tsub₂ ∈ [tsub₁, tsub₂] := by simp
                have := List.sizeOf_lt_of_mem hmem
                simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec,
                  Pattern.apply.sizeOf_spec] at hsize this
                omega
              have hlabels := ihn tsub₂ hlt hsub₂
              intro x hx
              simp only [List.append_nil, List.cons_append,
                List.nil_append, List.mem_cons] at hx
              rcases hx with rfl | hx₂
              · exact hleaf
              · exact hlabels x hx₂

theorem compressedList_reflects {source : ClassifiedSource} :
    ∀ (n : Nat) (tree : Pattern), sizeOf tree ≤ n →
      ∀ {toks : List String},
        Derives (lexicalizedLanguage sourceGrammar lexicalDeclarations
          source) compressedWordListSort toks tree →
        toks ≠ [] ∧ ∀ t ∈ toks,
          TokenLeaf (lexicalizedLanguage sourceGrammar
            lexicalDeclarations source) compressedWordTokenSort t := by
  intro n
  induction n with
  | zero =>
      intro tree hsize
      have := pattern_sizeOf_pos tree
      omega
  | succ n ihn =>
      intro tree hsize toks h
      cases h with
      | rule r hr sort' hcat toks' kids hitems =>
          rcases lexicalized_rule_cases hr with
            ⟨idx, token, s', hs', rfl⟩ | hprod
          · exact absurd hcat (fun hcontra =>
              leaf_not_internal hs' hcontra
                (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
          · rcases compressedListRules_cases hprod hcat with rfl | rfl
            · cases hitems with
              | nonTerminal _ nm srt hsrt sub tsub hsub rest' toks₂
                  kids₂ hrest =>
                  cases hrest
                  obtain rfl := Option.some.inj hsrt
                  obtain ⟨t, rfl, hleaf⟩ :=
                    tokenLeaf_reflects
                      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hsub
                  refine ⟨by simp, ?_⟩
                  intro x hx
                  simp only [List.append_nil, List.mem_singleton] at hx
                  subst hx
                  exact hleaf
            · cases hitems with
              | nonTerminal _ nm₁ srt₁ hsrt₁ sub₁ tsub₁ hsub₁ rest₁
                  toks₂ kids₂ hrest₁ =>
              cases hrest₁ with
              | nonTerminal _ nm₂ srt₂ hsrt₂ sub₂ tsub₂ hsub₂ rest₂
                  toks₃ kids₃ hrest₂ =>
              cases hrest₂
              obtain rfl := Option.some.inj hsrt₁
              obtain rfl := Option.some.inj hsrt₂
              obtain ⟨t, rfl, hleaf⟩ :=
                tokenLeaf_reflects
                  (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hsub₁
              have hlt : sizeOf tsub₂ ≤ n := by
                have hmem : tsub₂ ∈ [tsub₁, tsub₂] := by simp
                have := List.sizeOf_lt_of_mem hmem
                simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec,
                  Pattern.apply.sizeOf_spec] at hsize this
                omega
              obtain ⟨hne, hwords⟩ := ihn tsub₂ hlt hsub₂
              refine ⟨by simp, ?_⟩
              intro x hx
              simp only [List.append_nil, List.cons_append,
                List.nil_append, List.mem_cons] at hx
              rcases hx with rfl | hx₂
              · exact hleaf
              · exact hwords x hx₂

/-! ## Reflection carriers: dummy provenance and byte-clean strings

Reflection recovers statement *content* from a grammar derivation;
provenance spans are not grammar data, so recovered statements carry a
dummy span.  Compressed words are byte-anchored in `RawStatement`, so
their reflection needs each token string to be byte-representable —
automatic for anything lexed from bytes. -/

/-- Every character fits in one byte. -/
def ByteClean (t : String) : Prop := ∀ c ∈ t.toList, c.toNat < 256

/-- Byte image of a byte-clean string. -/
def stringBytes (t : String) : List UInt8 :=
  t.toList.map (fun c => UInt8.ofNat c.toNat)

theorem tokenText_stringBytes {t : String} (h : ByteClean t) :
    tokenText (stringBytes t) = t := by
  unfold tokenText stringBytes
  rw [List.map_map]
  have hmap : t.toList.map ((fun b => Char.ofNat b.toNat) ∘
      fun c => UInt8.ofNat c.toNat) = t.toList.map id := by
    apply List.map_congr_left
    intro c hc
    simp only [Function.comp_apply, id]
    have hlt : c.toNat < 256 := h c hc
    have hbyte : (UInt8.ofNat c.toNat).toNat = c.toNat := by
      simp [Nat.mod_eq_of_lt hlt]
    rw [hbyte]
    exact Char.ofNat_toNat c
  rw [hmap, List.map_id]
  exact String.ofList_toList

private def dummySpan :
    Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical.LocatedByteSpan :=
  ⟨"", 0, 0⟩

private def locName (t : String) : LocatedName := ⟨dummySpan, t⟩

private def locToken (t : String) : LocatedToken :=
  ⟨dummySpan, stringBytes t⟩

private theorem map_locName_name (ts : List String) :
    (ts.map locName).map (·.name) = ts := by
  induction ts with
  | nil => rfl
  | cons t rest ih => simp [locName, ih]

private theorem map_locToken_text {ts : List String}
    (h : ∀ t ∈ ts, ByteClean t) :
    (ts.map locToken).map (fun w => tokenText w.bytes) = ts := by
  induction ts with
  | nil => rfl
  | cons t rest ih =>
      have hrest := ih (fun x hx => h x (by simp [hx]))
      simp only [List.map_cons, List.map_map] at hrest ⊢
      rw [show tokenText (locToken t).bytes = tokenText (stringBytes t)
          from rfl, tokenText_stringBytes (h t (by simp)), hrest]

private theorem name_comp_locName :
    ((fun x : LocatedName => x.name) ∘ locName) = id :=
  funext fun _ => rfl

private theorem map_text_comp_locToken {ts : List String}
    (h : ∀ t ∈ ts, ByteClean t) :
    ts.map ((fun w => tokenText w.bytes) ∘ locToken) = ts := by
  have := map_locToken_text h
  simpa [List.map_map] using this

/-! ## Nested-sequence algebra -/

theorem nestSeq_append {outer : Bool} {ss₁ ss₂ : List RawStatement}
    (h₁ : NestSeq outer ss₁) (h₂ : NestSeq outer ss₂) :
    NestSeq outer (ss₁ ++ ss₂) := by
  revert h₂
  induction h₁ with
  | nil _ =>
      intro h₂
      simpa using h₂
  | atom _ s rest hm hc _ ih =>
      intro h₂
      exact NestSeq.atom _ s _ hm hc (ih h₂)
  | block _ o cl inner rest hinner _ _ih₁ ih₂ =>
      intro h₂
      have := NestSeq.block _ o cl inner (rest ++ ss₂) hinner (ih₂ h₂)
      simpa using this

private theorem nestSeq_false_any_aux :
    ∀ {b : Bool} {ss : List RawStatement}, NestSeq b ss → b = false →
      ∀ (outer : Bool), NestSeq outer ss := by
  intro b ss h
  induction h with
  | nil _ =>
      intro _ outer
      exact NestSeq.nil _
  | atom c s rest hm hc _ ih =>
      intro hb outer
      subst hb
      exact NestSeq.atom _ s _ hm (fun hcs => nomatch (hc hcs))
        (ih rfl outer)
  | block c o cl inner rest hinner _ _ih₁ ih₂ =>
      intro hb outer
      subst hb
      exact NestSeq.block _ o cl inner rest hinner (ih₂ rfl outer)

theorem nestSeq_false_any {outer : Bool} {ss : List RawStatement}
    (h : NestSeq false ss) : NestSeq outer ss :=
  nestSeq_false_any_aux h rfl outer

/-! ## The four-sort reflection bundle -/

/-- Facts recovered alongside a reflected statement stream. -/
def ReflectFacts (source : ClassifiedSource)
    (ss : List RawStatement) : Prop :=
  ∀ s ∈ ss,
    StatementLeaves
      (lexicalizedLanguage sourceGrammar lexicalDeclarations source)
      s ∧ StatementArity s

set_option maxHeartbeats 4000000 in
/-- **Reflection**: every lexicalized derivation at the four structural
sorts is the token image of a nested raw-statement stream carrying its
own leaf coverage and arities.  Include statements are outside the
segmented stream (`"$["` excluded); compressed words need byte-clean
tokens (automatic for byte-lexed sources). -/
theorem reflect_bundle {source : ClassifiedSource} :
    ∀ (n : Nat) (tree : Pattern), sizeOf tree ≤ n →
      ((∀ {toks : List String}, (∀ t ∈ toks, ByteClean t) →
        Derives (lexicalizedLanguage sourceGrammar lexicalDeclarations
          source) statementSort toks tree →
        ∃ ss, toks = ss.flatMap RawStatement.tokenStrings ∧
          NestSeq false ss ∧ ReflectFacts source ss) ∧
      (∀ {toks : List String}, (∀ t ∈ toks, ByteClean t) →
        Derives (lexicalizedLanguage sourceGrammar lexicalDeclarations
          source) databaseSort toks tree →
        ∃ ss, toks = ss.flatMap RawStatement.tokenStrings ∧
          NestSeq false ss ∧ ReflectFacts source ss) ∧
      (∀ {toks : List String}, "$[" ∉ toks →
        (∀ t ∈ toks, ByteClean t) →
        Derives (lexicalizedLanguage sourceGrammar lexicalDeclarations
          source) outerStatementSort toks tree →
        ∃ ss, toks = ss.flatMap RawStatement.tokenStrings ∧
          NestSeq true ss ∧ ReflectFacts source ss) ∧
      (∀ {toks : List String}, "$[" ∉ toks →
        (∀ t ∈ toks, ByteClean t) →
        Derives (lexicalizedLanguage sourceGrammar lexicalDeclarations
          source) outerDatabaseSort toks tree →
        ∃ ss, toks = ss.flatMap RawStatement.tokenStrings ∧
          NestSeq true ss ∧ ReflectFacts source ss)) := by
  intro n
  induction n with
  | zero =>
      intro tree hsize
      have := pattern_sizeOf_pos tree
      omega
  | succ n ihn =>
      intro tree hsize
      refine ⟨?_, ?_, ?_, ?_⟩
      -- statement arm
      · intro toks hclean h
        cases h with
        | rule r hr sort' hcat toks' kids hitems =>
        rcases lexicalized_rule_cases hr with
          ⟨idx, token, s', hs', rfl⟩ | hprod
        · exact absurd hcat (fun hcontra =>
            leaf_not_internal hs' hcontra
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl rfl)))))))
        · rcases statementRules_cases hprod hcat with
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          -- statement_var
          · cases hitems with
            | terminal _ _ _ _ _ h₁ =>
            cases h₁ with
            | nonTerminal _ nm srt hsrt sub tsub hsub rest₂ toks₂
                kids₂ h₂ =>
            cases h₂ with
            | terminal _ _ _ _ _ h₃ =>
            cases h₃
            obtain rfl := Option.some.inj hsrt
            obtain ⟨hne, hleaves⟩ :=
              symbolList_reflects (sizeOf tsub) tsub le_rfl hsub
            refine ⟨[.varDecl dummySpan (sub.map locName) dummySpan],
              ?_, ?_, ?_⟩
            · simp [RawStatement.tokenStrings, name_comp_locName]
            · exact NestSeq.atom false _ [] rfl (fun hc => nomatch hc)
                (NestSeq.nil false)
            · intro s hs
              simp only [List.mem_singleton] at hs
              subst hs
              refine ⟨?_, ?_⟩
              · intro x hx
                obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
                exact hleaves t ht
              · exact fun hnil =>
                  hne (List.map_eq_nil_iff.mp hnil)
          -- statement_disjoint
          · cases hitems with
            | terminal _ _ _ _ _ h₁ =>
            cases h₁ with
            | nonTerminal _ nm srt hsrt sub tsub hsub rest₂ toks₂
                kids₂ h₂ =>
            cases h₂ with
            | terminal _ _ _ _ _ h₃ =>
            cases h₃
            obtain rfl := Option.some.inj hsrt
            obtain ⟨hlen, hleaves⟩ :=
              disjointList_reflects (sizeOf tsub) tsub le_rfl hsub
            refine ⟨[.djDecl dummySpan (sub.map locName) dummySpan],
              ?_, ?_, ?_⟩
            · simp [RawStatement.tokenStrings, name_comp_locName]
            · exact NestSeq.atom false _ [] rfl (fun hc => nomatch hc)
                (NestSeq.nil false)
            · intro s hs
              simp only [List.mem_singleton] at hs
              subst hs
              refine ⟨?_, ?_⟩
              · intro x hx
                obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
                exact hleaves t ht
              · show 2 ≤ (sub.map locName).length
                simpa using hlen
          -- statement_float
          · cases hitems with
            | nonTerminal _ nm₁ srt₁ hsrt₁ sub₁ tsub₁ hsub₁ rest₁
                toks₁ kids₁ h₁ =>
            cases h₁ with
            | terminal _ _ _ _ _ h₂ =>
            cases h₂ with
            | nonTerminal _ nm₂ srt₂ hsrt₂ sub₂ tsub₂ hsub₂ rest₂
                toks₂ kids₂ h₃ =>
            cases h₃ with
            | nonTerminal _ nm₃ srt₃ hsrt₃ sub₃ tsub₃ hsub₃ rest₃
                toks₃ kids₃ h₄ =>
            cases h₄ with
            | terminal _ _ _ _ _ h₅ =>
            cases h₅
            obtain rfl := Option.some.inj hsrt₁
            obtain rfl := Option.some.inj hsrt₂
            obtain rfl := Option.some.inj hsrt₃
            obtain ⟨l, rfl, hl⟩ :=
              tokenLeaf_reflects (Or.inl rfl) hsub₁
            obtain ⟨tc, rfl, htc⟩ :=
              tokenLeaf_reflects (Or.inr (Or.inl rfl)) hsub₂
            obtain ⟨v, rfl, hv⟩ :=
              tokenLeaf_reflects (Or.inr (Or.inl rfl)) hsub₃
            refine ⟨[.floating dummySpan (locName l) (locName tc)
              (locName v) dummySpan], ?_, ?_, ?_⟩
            · simp [RawStatement.tokenStrings, locName]
            · exact NestSeq.atom false _ [] rfl (fun hc => nomatch hc)
                (NestSeq.nil false)
            · intro s hs
              simp only [List.mem_singleton] at hs
              subst hs
              exact ⟨⟨hl, htc, hv⟩, trivial⟩
          -- statement_essential
          · cases hitems with
            | nonTerminal _ nm₁ srt₁ hsrt₁ sub₁ tsub₁ hsub₁ rest₁
                toks₁ kids₁ h₁ =>
            cases h₁ with
            | terminal _ _ _ _ _ h₂ =>
            cases h₂ with
            | nonTerminal _ nm₂ srt₂ hsrt₂ sub₂ tsub₂ hsub₂ rest₂
                toks₂ kids₂ h₃ =>
            cases h₃ with
            | terminal _ _ _ _ _ h₄ =>
            cases h₄
            obtain rfl := Option.some.inj hsrt₁
            obtain rfl := Option.some.inj hsrt₂
            obtain ⟨l, rfl, hl⟩ :=
              tokenLeaf_reflects (Or.inl rfl) hsub₁
            obtain ⟨hne, hleaves⟩ :=
              symbolList_reflects (sizeOf tsub₂) tsub₂ le_rfl hsub₂
            obtain ⟨tc, body, rfl⟩ := List.exists_cons_of_ne_nil hne
            refine ⟨[.essential dummySpan (locName l) (locName tc)
              (body.map locName) dummySpan], ?_, ?_, ?_⟩
            · simp [RawStatement.tokenStrings, name_comp_locName,
                locName]
            · exact NestSeq.atom false _ [] rfl (fun hc => nomatch hc)
                (NestSeq.nil false)
            · intro s hs
              simp only [List.mem_singleton] at hs
              subst hs
              refine ⟨⟨hl, hleaves tc (by simp), ?_⟩, trivial⟩
              intro x hx
              obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
              exact hleaves t (by simp [ht])
          -- statement_axiom
          · cases hitems with
            | nonTerminal _ nm₁ srt₁ hsrt₁ sub₁ tsub₁ hsub₁ rest₁
                toks₁ kids₁ h₁ =>
            cases h₁ with
            | terminal _ _ _ _ _ h₂ =>
            cases h₂ with
            | nonTerminal _ nm₂ srt₂ hsrt₂ sub₂ tsub₂ hsub₂ rest₂
                toks₂ kids₂ h₃ =>
            cases h₃ with
            | terminal _ _ _ _ _ h₄ =>
            cases h₄
            obtain rfl := Option.some.inj hsrt₁
            obtain rfl := Option.some.inj hsrt₂
            obtain ⟨l, rfl, hl⟩ :=
              tokenLeaf_reflects (Or.inl rfl) hsub₁
            obtain ⟨hne, hleaves⟩ :=
              symbolList_reflects (sizeOf tsub₂) tsub₂ le_rfl hsub₂
            obtain ⟨tc, body, rfl⟩ := List.exists_cons_of_ne_nil hne
            refine ⟨[.axiomatic dummySpan (locName l) (locName tc)
              (body.map locName) dummySpan], ?_, ?_, ?_⟩
            · simp [RawStatement.tokenStrings, name_comp_locName,
                locName]
            · exact NestSeq.atom false _ [] rfl (fun hc => nomatch hc)
                (NestSeq.nil false)
            · intro s hs
              simp only [List.mem_singleton] at hs
              subst hs
              refine ⟨⟨hl, hleaves tc (by simp), ?_⟩, trivial⟩
              intro x hx
              obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
              exact hleaves t (by simp [ht])
          -- statement_theorem_normal
          · cases hitems with
            | nonTerminal _ nm₁ srt₁ hsrt₁ sub₁ tsub₁ hsub₁ rest₁
                toks₁ kids₁ h₁ =>
            cases h₁ with
            | terminal _ _ _ _ _ h₂ =>
            cases h₂ with
            | nonTerminal _ nm₂ srt₂ hsrt₂ sub₂ tsub₂ hsub₂ rest₂
                toks₂ kids₂ h₃ =>
            cases h₃ with
            | terminal _ _ _ _ _ h₄ =>
            cases h₄ with
            | nonTerminal _ nm₃ srt₃ hsrt₃ sub₃ tsub₃ hsub₃ rest₃
                toks₃ kids₃ h₅ =>
            cases h₅ with
            | terminal _ _ _ _ _ h₆ =>
            cases h₆
            obtain rfl := Option.some.inj hsrt₁
            obtain rfl := Option.some.inj hsrt₂
            obtain rfl := Option.some.inj hsrt₃
            obtain ⟨l, rfl, hl⟩ :=
              tokenLeaf_reflects (Or.inl rfl) hsub₁
            obtain ⟨hne, hleaves⟩ :=
              symbolList_reflects (sizeOf tsub₂) tsub₂ le_rfl hsub₂
            obtain ⟨tc, body, rfl⟩ := List.exists_cons_of_ne_nil hne
            obtain ⟨hpne, hsteps⟩ :=
              proofList_reflects (sizeOf tsub₃) tsub₃ le_rfl hsub₃
            refine ⟨[.provable dummySpan (locName l) (locName tc)
              (body.map locName) (.normal (sub₃.map locName))
              dummySpan dummySpan], ?_, ?_, ?_⟩
            · simp [RawStatement.tokenStrings,
                ProofPayload.tokenStrings, name_comp_locName, locName]
            · exact NestSeq.atom false _ [] rfl (fun hc => nomatch hc)
                (NestSeq.nil false)
            · intro s hs
              simp only [List.mem_singleton] at hs
              subst hs
              refine ⟨⟨hl, hleaves tc (by simp), ?_, ?_⟩, ?_⟩
              · intro x hx
                obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
                exact hleaves t (by simp [ht])
              · intro x hx
                obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
                exact hsteps t ht
              · show sub₃.map locName ≠ []
                exact fun hnil => hpne (List.map_eq_nil_iff.mp hnil)
          -- statement_theorem_compressed
          · cases hitems with
            | nonTerminal _ nm₁ srt₁ hsrt₁ sub₁ tsub₁ hsub₁ rest₁
                toks₁ kids₁ h₁ =>
            cases h₁ with
            | terminal _ _ _ _ _ h₂ =>
            cases h₂ with
            | nonTerminal _ nm₂ srt₂ hsrt₂ sub₂ tsub₂ hsub₂ rest₂
                toks₂ kids₂ h₃ =>
            cases h₃ with
            | terminal _ _ _ _ _ h₄ =>
            cases h₄ with
            | terminal _ _ _ _ _ h₅ =>
            cases h₅ with
            | nonTerminal _ nm₃ srt₃ hsrt₃ sub₃ tsub₃ hsub₃ rest₃
                toks₃ kids₃ h₆ =>
            cases h₆ with
            | terminal _ _ _ _ _ h₇ =>
            cases h₇ with
            | nonTerminal _ nm₄ srt₄ hsrt₄ sub₄ tsub₄ hsub₄ rest₄
                toks₄ kids₄ h₈ =>
            cases h₈ with
            | terminal _ _ _ _ _ h₉ =>
            cases h₉
            obtain rfl := Option.some.inj hsrt₁
            obtain rfl := Option.some.inj hsrt₂
            obtain rfl := Option.some.inj hsrt₃
            obtain rfl := Option.some.inj hsrt₄
            obtain ⟨l, rfl, hl⟩ :=
              tokenLeaf_reflects (Or.inl rfl) hsub₁
            obtain ⟨hne, hleaves⟩ :=
              symbolList_reflects (sizeOf tsub₂) tsub₂ le_rfl hsub₂
            obtain ⟨tc, body, rfl⟩ := List.exists_cons_of_ne_nil hne
            have hheads :=
              headerList_reflects (sizeOf tsub₃) tsub₃ le_rfl hsub₃
            obtain ⟨hwne, hwords⟩ :=
              compressedList_reflects (sizeOf tsub₄) tsub₄ le_rfl hsub₄
            have hcleanW : ∀ t ∈ sub₄, ByteClean t := fun t ht =>
              hclean t (by simp [ht])
            refine ⟨[.provable dummySpan (locName l) (locName tc)
              (body.map locName)
              (.compressed dummySpan (sub₃.map locName) dummySpan
                (sub₄.map locToken)) dummySpan dummySpan], ?_, ?_, ?_⟩
            · simp [RawStatement.tokenStrings,
                ProofPayload.tokenStrings, name_comp_locName,
                map_text_comp_locToken hcleanW, locName]
            · exact NestSeq.atom false _ [] rfl (fun hc => nomatch hc)
                (NestSeq.nil false)
            · intro s hs
              simp only [List.mem_singleton] at hs
              subst hs
              refine ⟨⟨hl, hleaves tc (by simp), ?_, ?_, ?_⟩, ?_⟩
              · intro x hx
                obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
                exact hleaves t (by simp [ht])
              · intro x hx
                obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
                exact hheads t ht
              · intro w hw
                obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hw
                rw [show (locToken t).bytes = stringBytes t from rfl,
                  tokenText_stringBytes (hcleanW t ht)]
                exact hwords t ht
              · show sub₄.map locToken ≠ []
                exact fun hnil => hwne (List.map_eq_nil_iff.mp hnil)
          -- statement_block
          · cases hitems with
            | terminal _ _ _ _ _ h₁ =>
            cases h₁ with
            | nonTerminal _ nm srt hsrt sub tsub hsub rest₂ toks₂
                kids₂ h₂ =>
            cases h₂ with
            | terminal _ _ _ _ _ h₃ =>
            cases h₃
            obtain rfl := Option.some.inj hsrt
            have hlt : sizeOf tsub ≤ n := by
              have hmem : tsub ∈ [tsub] := by simp
              have := List.sizeOf_lt_of_mem hmem
              simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec,
                Pattern.apply.sizeOf_spec] at hsize this
              omega
            have hcleanI : ∀ t ∈ sub, ByteClean t := fun t ht =>
              hclean t (by simp [ht])
            obtain ⟨ssI, htoksI, hnest, hfacts⟩ :=
              (ihn tsub hlt).2.1 hcleanI hsub
            refine ⟨.openScope dummySpan ::
              (ssI ++ [.closeScope dummySpan]), ?_, ?_, ?_⟩
            · subst htoksI
              simp [RawStatement.tokenStrings]
            · exact NestSeq.block false dummySpan dummySpan ssI []
                hnest (NestSeq.nil false)
            · intro s hs
              simp at hs
              rcases hs with rfl | hs | rfl
              · exact ⟨trivial, trivial⟩
              · exact hfacts s hs
              · exact ⟨trivial, trivial⟩
      -- database arm
      · intro toks hclean h
        cases h with
        | rule r hr sort' hcat toks' kids hitems =>
        rcases lexicalized_rule_cases hr with
          ⟨idx, token, s', hs', rfl⟩ | hprod
        · exact absurd hcat (fun hcontra =>
            leaf_not_internal hs' hcontra
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl rfl))))))))
        · rcases databaseRules_cases hprod hcat with rfl | rfl
          · cases hitems
            exact ⟨[], by simp, NestSeq.nil false,
              fun s hs => absurd hs List.not_mem_nil⟩
          · cases hitems with
            | nonTerminal _ nm₁ srt₁ hsrt₁ sub₁ tsub₁ hsub₁ rest₁
                toks₁ kids₁ h₁ =>
            cases h₁ with
            | nonTerminal _ nm₂ srt₂ hsrt₂ sub₂ tsub₂ hsub₂ rest₂
                toks₂ kids₂ h₃ =>
            cases h₃
            obtain rfl := Option.some.inj hsrt₁
            obtain rfl := Option.some.inj hsrt₂
            have hlt₁ : sizeOf tsub₁ ≤ n := by
              have hmem : tsub₁ ∈ [tsub₁, tsub₂] := by simp
              have := List.sizeOf_lt_of_mem hmem
              simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec,
                Pattern.apply.sizeOf_spec] at hsize this
              omega
            have hlt₂ : sizeOf tsub₂ ≤ n := by
              have hmem : tsub₂ ∈ [tsub₁, tsub₂] := by simp
              have := List.sizeOf_lt_of_mem hmem
              simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec,
                Pattern.apply.sizeOf_spec] at hsize this
              omega
            have hclean₁ : ∀ t ∈ sub₁, ByteClean t := fun t ht =>
              hclean t (by simp [ht])
            have hclean₂ : ∀ t ∈ sub₂, ByteClean t := fun t ht =>
              hclean t (by simp [ht])
            obtain ⟨ss₁, htoks₁, hnest₁, hfacts₁⟩ :=
              (ihn tsub₁ hlt₁).1 hclean₁ hsub₁
            obtain ⟨ss₂, htoks₂, hnest₂, hfacts₂⟩ :=
              (ihn tsub₂ hlt₂).2.1 hclean₂ hsub₂
            refine ⟨ss₁ ++ ss₂, ?_, nestSeq_append hnest₁ hnest₂, ?_⟩
            · subst htoks₁ htoks₂
              simp
            · intro s hs
              rcases List.mem_append.mp hs with hs₁ | hs₂
              · exact hfacts₁ s hs₁
              · exact hfacts₂ s hs₂
      -- outer statement arm
      · intro toks hnoinc hclean h
        cases h with
        | rule r hr sort' hcat toks' kids hitems =>
        rcases lexicalized_rule_cases hr with
          ⟨idx, token, s', hs', rfl⟩ | hprod
        · exact absurd hcat (fun hcontra =>
            leaf_not_internal hs' hcontra
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl rfl)))))))))
        · rcases outerStatementRules_cases hprod hcat with
            rfl | rfl | rfl
          -- statement_const
          · cases hitems with
            | terminal _ _ _ _ _ h₁ =>
            cases h₁ with
            | nonTerminal _ nm srt hsrt sub tsub hsub rest₂ toks₂
                kids₂ h₂ =>
            cases h₂ with
            | terminal _ _ _ _ _ h₃ =>
            cases h₃
            obtain rfl := Option.some.inj hsrt
            obtain ⟨hne, hleaves⟩ :=
              symbolList_reflects (sizeOf tsub) tsub le_rfl hsub
            refine ⟨[.constDecl dummySpan (sub.map locName) dummySpan],
              ?_, ?_, ?_⟩
            · simp [RawStatement.tokenStrings, name_comp_locName]
            · exact NestSeq.atom true _ [] rfl (fun _ => rfl)
                (NestSeq.nil true)
            · intro s hs
              simp only [List.mem_singleton] at hs
              subst hs
              refine ⟨?_, ?_⟩
              · intro x hx
                obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
                exact hleaves t ht
              · exact fun hnil => hne (List.map_eq_nil_iff.mp hnil)
          -- statement_include: excluded by the no-include hypothesis
          · cases hitems with
            | terminal _ _ _ _ _ h₁ =>
                exact absurd (by simp) hnoinc
          -- outer_statement_inner
          · cases hitems with
            | nonTerminal _ nm srt hsrt sub tsub hsub rest₂ toks₂
                kids₂ h₂ =>
            cases h₂
            obtain rfl := Option.some.inj hsrt
            have hlt : sizeOf tsub ≤ n := by
              have hmem : tsub ∈ [tsub] := by simp
              have := List.sizeOf_lt_of_mem hmem
              simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec,
                Pattern.apply.sizeOf_spec] at hsize this
              omega
            have hcleanI : ∀ t ∈ sub, ByteClean t := fun t ht =>
              hclean t (by simp [ht])
            obtain ⟨ss, htoks, hnest, hfacts⟩ :=
              (ihn tsub hlt).1 hcleanI hsub
            exact ⟨ss, by simp [htoks], nestSeq_false_any hnest,
              hfacts⟩
      -- outer database arm
      · intro toks hnoinc hclean h
        cases h with
        | rule r hr sort' hcat toks' kids hitems =>
        rcases lexicalized_rule_cases hr with
          ⟨idx, token, s', hs', rfl⟩ | hprod
        · exact absurd hcat (fun hcontra =>
            leaf_not_internal hs' hcontra
              (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inr rfl)))))))))
        · rcases outerDatabaseRules_cases hprod hcat with rfl | rfl
          · cases hitems
            exact ⟨[], by simp, NestSeq.nil true,
              fun s hs => absurd hs List.not_mem_nil⟩
          · cases hitems with
            | nonTerminal _ nm₁ srt₁ hsrt₁ sub₁ tsub₁ hsub₁ rest₁
                toks₁ kids₁ h₁ =>
            cases h₁ with
            | nonTerminal _ nm₂ srt₂ hsrt₂ sub₂ tsub₂ hsub₂ rest₂
                toks₂ kids₂ h₃ =>
            cases h₃
            obtain rfl := Option.some.inj hsrt₁
            obtain rfl := Option.some.inj hsrt₂
            have hlt₁ : sizeOf tsub₁ ≤ n := by
              have hmem : tsub₁ ∈ [tsub₁, tsub₂] := by simp
              have := List.sizeOf_lt_of_mem hmem
              simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec,
                Pattern.apply.sizeOf_spec] at hsize this
              omega
            have hlt₂ : sizeOf tsub₂ ≤ n := by
              have hmem : tsub₂ ∈ [tsub₁, tsub₂] := by simp
              have := List.sizeOf_lt_of_mem hmem
              simp only [List.cons.sizeOf_spec, List.nil.sizeOf_spec,
                Pattern.apply.sizeOf_spec] at hsize this
              omega
            have hnoinc₁ : "$[" ∉ sub₁ := fun hm =>
              hnoinc (by simp [hm])
            have hnoinc₂ : "$[" ∉ sub₂ := fun hm =>
              hnoinc (by simp [hm])
            have hclean₁ : ∀ t ∈ sub₁, ByteClean t := fun t ht =>
              hclean t (by simp [ht])
            have hclean₂ : ∀ t ∈ sub₂, ByteClean t := fun t ht =>
              hclean t (by simp [ht])
            obtain ⟨ss₁, htoks₁, hnest₁, hfacts₁⟩ :=
              (ihn tsub₁ hlt₁).2.2.1 hnoinc₁ hclean₁ hsub₁
            obtain ⟨ss₂, htoks₂, hnest₂, hfacts₂⟩ :=
              (ihn tsub₂ hlt₂).2.2.2 hnoinc₂ hclean₂ hsub₂
            refine ⟨ss₁ ++ ss₂, ?_, nestSeq_append hnest₁ hnest₂, ?_⟩
            · subst htoks₁ htoks₂
              simp
            · intro s hs
              rcases List.mem_append.mp hs with hs₁ | hs₂
              · exact hfacts₁ s hs₁
              · exact hfacts₂ s hs₂

/-! ## Universal correspondence and pipeline consequences -/

private theorem statementArity_of_parts {s : RawStatement}
    (hfold : FoldArity s) (hnorm : NormalStepsOK s)
    (hcomp : CompressedWordsOK s) : StatementArity s := by
  cases s with
  | provable site label typecode body proof separator terminator =>
      cases proof with
      | normal steps => exact hnorm
      | compressed openParen header closeParen words => exact hcomp
  | openScope site => trivial
  | closeScope site => trivial
  | constDecl site names terminator => exact hfold
  | varDecl site names terminator => exact hfold
  | djDecl site names terminator => exact hfold
  | floating site label typecode variableName terminator => trivial
  | essential site label typecode body terminator => trivial
  | axiomatic site label typecode body terminator => trivial

/-- **The universal correspondence** at the outer database sort: a
lexicalized grammar derivation of an include-free, byte-clean token
stream exists exactly when the stream is the token image of a nested
raw-statement stream carrying leaf coverage and grammar arities. -/
theorem derivation_correspondence {source : ClassifiedSource}
    {toks : List String}
    (hnoinc : "$[" ∉ toks) (hclean : ∀ t ∈ toks, ByteClean t) :
    (∃ tree, Derives
      (lexicalizedLanguage sourceGrammar lexicalDeclarations source)
      outerDatabaseSort toks tree) ↔
      ∃ ss : List RawStatement,
        toks = ss.flatMap RawStatement.tokenStrings ∧ NestSeq true ss ∧
          ReflectFacts source ss := by
  constructor
  · rintro ⟨tree, h⟩
    exact (reflect_bundle (sizeOf tree) tree le_rfl).2.2.2 hnoinc
      hclean h
  · rintro ⟨ss, rfl, hnest, hfacts⟩
    have hbase : BaseRules (lexicalizedLanguage sourceGrammar
        lexicalDeclarations source) := fun r hr =>
      baseRule_mem_lexicalized sourceGrammar lexicalDeclarations
        source hr
    exact nestSeq_derives hbase hnest hfacts

/-- Forward theorem over the fold: an accepted fold with balanced start
and end derives the outer database sort over exactly its statement
token image, from leaf coverage plus the two segmenter-owned arities
(both discharged by `segmentStatements_normalSteps` and
`segmentStatements_compressedWords` when the statements come from the
segmenter, as in `runSource_derives_outerDatabase`). -/
theorem statements_derive_outerDatabase {L : LanguageDef}
    (hbase : BaseRules L) {statements : List RawStatement}
    {state final : Mettapedia.Languages.Metamath.SourceGSLTState.SourceState}
    {obligations : List TheoremObligation}
    (hfold : foldStatements state statements = .ok (final, obligations))
    (hstart : state.scopes.length = 0)
    (hfin : final.scopes.length = 0)
    (hnormal : ∀ s ∈ statements, NormalStepsOK s)
    (hcompressed : ∀ s ∈ statements, CompressedWordsOK s)
    (hleaves : ∀ s ∈ statements, StatementLeaves L s) :
    ∃ tree, Derives L outerDatabaseSort
      (statements.flatMap RawStatement.tokenStrings) tree := by
  obtain ⟨hseq, harity⟩ := foldStatements_seqAt_arity hfold hfin
  rw [hstart] at hseq
  exact nestSeq_derives hbase (seqAt_nestSeq hseq)
    (fun s hs => ⟨hleaves s hs,
      statementArity_of_parts (harity s hs) (hnormal s hs)
        (hcompressed s hs)⟩)

open Mettapedia.Languages.Metamath.SourceGSLTIncludeDAG in
/-- Forward theorem over the composed pipeline: every accepted
`runSource` exposes its statement stream, whose token image derives
the outer database sort from leaf coverage alone; the fold discharges
balance, `$c` scoping, and the `$c`/`$v`/`$d` arities, and the
segmenter discharges normal-proof and compressed-body nonemptiness. -/
theorem runSource_derives_outerDatabase {files : FileMap}
    {policy : IncludePolicy} {root : String} {fuel : Nat}
    {state : Mettapedia.Languages.Metamath.SourceGSLTState.SourceState}
    {obligations : List TheoremObligation}
    (h : runSource files policy root fuel = .ok state obligations)
    {L : LanguageDef} (hbase : BaseRules L) :
    ∃ (tokens : List LocatedToken) (statements : List RawStatement),
      segmentStatements tokens = .ok statements ∧
        foldStatements
          Mettapedia.Languages.Metamath.SourceGSLTState.initialState
          statements = .ok (state, obligations) ∧
        ((∀ s ∈ statements, StatementLeaves L s) →
          ∃ tree, Derives L outerDatabaseSort
            (statements.flatMap RawStatement.tokenStrings) tree) := by
  obtain ⟨spans, tokens, statements, hexp, hres, hseg, hfold,
    hcomplete⟩ := runSource_ok_inv h
  refine ⟨tokens, statements, hseg, hfold, fun hleaves => ?_⟩
  exact statements_derive_outerDatabase hbase hfold rfl
    (sourceStateComplete_scopes_length hcomplete)
    (segmentStatements_normalSteps hseg)
    (segmentStatements_compressedWords hseg) hleaves

/-! ## Empty-compressed-body regression boundary -/

/-- **Grammar side (theorem):** an empty compressed body has no
derivation — `compressed_word_list` requires at least one word. -/
theorem emptyCompressedWords_not_derivable {source : ClassifiedSource}
    {tree : Pattern}
    (h : Derives
      (lexicalizedLanguage sourceGrammar lexicalDeclarations source)
      compressedWordListSort [] tree) : False :=
  (compressedList_reflects (sizeOf tree) tree le_rfl h).1 rfl

private def wSpan (start stop : Nat) :
    Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical.LocatedByteSpan :=
  ⟨"w", start, stop⟩

/-- `$c wff $. th $p wff $= ( ) $.` as located tokens. -/
private def emptyCompressedTokens : List LocatedToken :=
  [⟨wSpan 0 2, [36, 99]⟩,
   ⟨wSpan 3 6, [119, 102, 102]⟩,
   ⟨wSpan 7 9, [36, 46]⟩,
   ⟨wSpan 10 12, [116, 104]⟩,
   ⟨wSpan 13 15, [36, 112]⟩,
   ⟨wSpan 16 19, [119, 102, 102]⟩,
   ⟨wSpan 20 22, [36, 61]⟩,
   ⟨wSpan 23 24, [40]⟩,
   ⟨wSpan 25 26, [41]⟩,
   ⟨wSpan 27 29, [36, 46]⟩]

/-- **Segmenter side (kernel witness):** the segmenter now rejects the
stream — the `.proofWords` terminator guard enforces the grammar's
nonempty compressed body, and `mm-lean4` rejects the same stream at
proof finality (`stack.size == 1` in `finishProof`). -/
theorem emptyCompressedWords_segmenter_rejects_exact :
    segmentStatements emptyCompressedTokens =
      .rejected ⟨wSpan 27 29, .invalidCompressedWord⟩ := by decide

/-- Boolean-facing form of the exact rejection boundary. -/
theorem emptyCompressedWords_segmenter_rejects :
    (match segmentStatements emptyCompressedTokens with
      | .ok _ => false
      | .rejected _ => true) = true := by
  rw [emptyCompressedWords_segmenter_rejects_exact]

/-! ## Boundary compositions -/

/-- Authored derivations survive lexicalization. -/
theorem derives_lexicalized_of_source {source : ClassifiedSource} :
    ∀ (n : Nat) (tree : Pattern), sizeOf tree ≤ n →
      ∀ {sort : String} {toks : List String},
        Derives sourceGrammar sort toks tree →
        Derives
          (lexicalizedLanguage sourceGrammar lexicalDeclarations
            source) sort toks tree := by
  intro n
  induction n with
  | zero =>
      intro tree hsize
      have := pattern_sizeOf_pos tree
      omega
  | succ n ihn =>
      intro tree hsize sort toks h
      cases h with
      | rule r hr sort hcat toks kids hitems =>
          refine Derives.rule r
            (baseRule_mem_lexicalized sourceGrammar lexicalDeclarations
              source hr) _ hcat _ _ ?_
          have hkids : ∀ k ∈ kids, sizeOf k ≤ n := by
            intro k hk
            have h1 := List.sizeOf_lt_of_mem hk
            simp only [Pattern.apply.sizeOf_spec] at hsize
            omega
          have walk : ∀ (pat : List SyntaxItem) (toksW : List String)
              (kidsW : List Pattern), (∀ k ∈ kidsW, sizeOf k ≤ n) →
              DerivesItems sourceGrammar r pat toksW kidsW →
              DerivesItems (lexicalizedLanguage sourceGrammar
                lexicalDeclarations source) r pat toksW kidsW := by
            intro pat
            induction pat with
            | nil =>
                intro toksW kidsW hk hwalk
                cases hwalk
                exact DerivesItems.nil _
            | cons item rest ihp =>
                intro toksW kidsW hk hwalk
                cases hwalk with
                | terminal _ tok _ toks₀ kids₀ htail =>
                    exact DerivesItems.terminal _ tok _ _ _
                      (ihp _ _ hk htail)
                | nonTerminal _ nm srt hsrt sub tsub hsub rest₀ toks₀
                    kids₀ htail =>
                    exact DerivesItems.nonTerminal _ nm srt hsrt sub
                      tsub (ihn tsub (hk tsub (by simp)) hsub) _ _ _
                      (ihp _ _ (fun k hkm => hk k (by simp [hkm]))
                        htail)
          exact walk _ _ _ hkids hitems


open Mettapedia.Languages.Metamath.SourceGSLTParserExport
  Mettapedia.GSLT.Parsing.LanguageDefSyntaxCorrespondence
  Mettapedia.GSLT.Parsing.LanguageDefSyntaxCompiler in
/-- The compiled structural-rule boundary embeds into the lexicalized
judgment: `RawStatement ↔ GrammarDerives` composes with
`CompiledDerives ↔ GrammarDerives` at the shared bare-grammar spine. -/
theorem compiledDerivation_lexicalized {source : ClassifiedSource}
    {toks : List String} {tree : Pattern}
    (h : CompiledDerives compiledSourceRules outerDatabaseSort toks
      tree) :
    Derives
      (lexicalizedLanguage sourceGrammar lexicalDeclarations source)
      outerDatabaseSort toks tree :=
  derives_lexicalized_of_source (sizeOf tree) tree le_rfl
    ((compiledDerivation_iff_sourceDerivation outerDatabaseSort toks
      tree).mp h)

/-- With ordered-ledger alignment, the segmented statement stream
certifies the same lexicalized judgment the checked DAG boundary
certifies (`checkedMetamathSourceBlocks_sound`). -/
theorem statements_certify_ledger_judgment {source : ClassifiedSource}
    {statements : List RawStatement}
    {state final : Mettapedia.Languages.Metamath.SourceGSLTState.SourceState}
    {obligations : List TheoremObligation}
    (hfold : foldStatements state statements = .ok (final, obligations))
    (hstart : state.scopes.length = 0)
    (hfin : final.scopes.length = 0)
    (hnormal : ∀ s ∈ statements, NormalStepsOK s)
    (hcompressed : ∀ s ∈ statements, CompressedWordsOK s)
    (hleaves : ∀ s ∈ statements, StatementLeaves
      (lexicalizedLanguage sourceGrammar lexicalDeclarations source) s)
    (halign : statements.flatMap RawStatement.tokenStrings =
      source.ledger.tokens) :
    ∃ tree, Derives
      (lexicalizedLanguage sourceGrammar lexicalDeclarations source)
      outerDatabaseSort source.ledger.tokens tree := by
  obtain ⟨tree, htree⟩ := statements_derive_outerDatabase
    (fun r hr => baseRule_mem_lexicalized sourceGrammar
      lexicalDeclarations source hr)
    hfold hstart hfin hnormal hcompressed hleaves
  exact ⟨tree, halign ▸ htree⟩

end Mettapedia.Languages.Metamath.SourceGSLTDerivationCorrespondence
