import Mettapedia.Languages.Metamath.SourceGSLTDerivationCorrespondence

/-!
# Lexical closure: the accepted run lexicalizes itself

The structural correspondence in `SourceGSLTDerivationCorrespondence` consumes
leaf coverage (`StatementLeaves`).  This module derives that coverage
with no external premise: the accepted statement stream determines its
own `ClassifiedSource` — each consumed name occurrence classified by
the role the segmenter consumed it in, keywords carrying no lexical
class — and every leaf the derivation needs is present in the
lexicalized language of that source by construction.  The
classification is not free-floating: the charset-grounding theorems
below tie every class to the authored raw-byte codepoint classes and
every keyword to the authored literal spellings.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

namespace Mettapedia.Languages.Metamath.SourceGSLTLexicalClosure

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.GrammarDerives
open Mettapedia.GSLT.LanguageDef.GrammarInferenceExtraction
open Mettapedia.Languages.Metamath.SourceGSLT
open Mettapedia.Languages.Metamath.SourceGSLTRawSourceComposition
open Mettapedia.Languages.Metamath.SourceGSLTDerivationCorrespondence

/-! ## The pipeline's own classified source -/

/-- A keyword occurrence: no lexical class, no leaf rule. -/
def keywordToken (s : String) : ClassifiedToken :=
  { serialized := s, literalName := none, className := "" }

/-- A name occurrence classified by its consumption role. -/
def classifiedName (className : String) (n : LocatedName) :
    ClassifiedToken :=
  { serialized := n.name, literalName := none, className := className }

/-- Normal proof steps: `?` is the authored unknown-step literal, every
other step is a proof label. -/
def proofStepToken (n : LocatedName) : ClassifiedToken :=
  if n.name = "?" then keywordToken "?"
  else classifiedName "mm-proof-label" n

/-- Classified tokens of a proof payload, in source order. -/
def payloadTokens : ProofPayload → List ClassifiedToken
  | .normal steps => steps.map proofStepToken
  | .compressed _ header _ words =>
      keywordToken "(" ::
        header.map (classifiedName "mm-proof-label") ++
          keywordToken ")" ::
            words.map (fun w =>
              classifiedName "mm-compressed-word"
                ⟨w.span, tokenText w.bytes⟩)

/-- Classified tokens of one statement, in source order — the exact
classified image of `RawStatement.tokenStrings`. -/
def statementTokens : RawStatement → List ClassifiedToken
  | .openScope _ => [keywordToken "${"]
  | .closeScope _ => [keywordToken "$}"]
  | .constDecl _ names _ =>
      keywordToken "$c" ::
        names.map (classifiedName "mm-symbol") ++ [keywordToken "$."]
  | .varDecl _ names _ =>
      keywordToken "$v" ::
        names.map (classifiedName "mm-symbol") ++ [keywordToken "$."]
  | .djDecl _ names _ =>
      keywordToken "$d" ::
        names.map (classifiedName "mm-symbol") ++ [keywordToken "$."]
  | .floating _ label typecode variableName _ =>
      [classifiedName "mm-label" label, keywordToken "$f",
        classifiedName "mm-symbol" typecode,
        classifiedName "mm-symbol" variableName, keywordToken "$."]
  | .essential _ label typecode body _ =>
      classifiedName "mm-label" label :: keywordToken "$e" ::
        classifiedName "mm-symbol" typecode ::
          body.map (classifiedName "mm-symbol") ++ [keywordToken "$."]
  | .axiomatic _ label typecode body _ =>
      classifiedName "mm-label" label :: keywordToken "$a" ::
        classifiedName "mm-symbol" typecode ::
          body.map (classifiedName "mm-symbol") ++ [keywordToken "$."]
  | .provable _ label typecode body proof _ _ =>
      classifiedName "mm-label" label :: keywordToken "$p" ::
        classifiedName "mm-symbol" typecode ::
          body.map (classifiedName "mm-symbol") ++
            keywordToken "$=" ::
              payloadTokens proof ++ [keywordToken "$."]

/-- The classified image of a statement stream. -/
def pipelineTokens (statements : List RawStatement) :
    List ClassifiedToken :=
  statements.flatMap statementTokens

/-- The accepted run's own classified source. -/
def pipelineSource (statements : List RawStatement) : ClassifiedSource :=
  { identity := "metamath-run-source"
    tokens := pipelineTokens statements }

/-! ## The classified image serializes to the token image -/

private theorem payloadTokens_serialized (proof : ProofPayload) :
    (payloadTokens proof).map ClassifiedToken.serialized =
      ProofPayload.tokenStrings proof := by
  cases proof with
  | normal steps =>
      simp only [payloadTokens, ProofPayload.tokenStrings,
        List.map_map]
      apply List.map_congr_left
      intro n _
      by_cases hq : n.name = "?"
      · simp [proofStepToken, keywordToken, hq, Function.comp]
      · simp [proofStepToken, classifiedName, hq, Function.comp]
  | compressed openParen header closeParen words =>
      simp [payloadTokens, ProofPayload.tokenStrings, keywordToken,
        classifiedName, List.map_map, Function.comp_def]

theorem statementTokens_serialized (s : RawStatement) :
    (statementTokens s).map ClassifiedToken.serialized =
      RawStatement.tokenStrings s := by
  cases s <;>
    simp [statementTokens, RawStatement.tokenStrings, keywordToken,
      classifiedName, payloadTokens_serialized, List.map_map,
      Function.comp]

/-- The pipeline source's ordered ledger is exactly the statement
stream's token image — the alignment premise of
`statements_certify_ledger_judgment` holds by construction. -/
theorem pipelineSource_ledger (statements : List RawStatement) :
    (pipelineSource statements).ledger.tokens =
      statements.flatMap RawStatement.tokenStrings := by
  show (pipelineTokens statements).map ClassifiedToken.serialized = _
  unfold pipelineTokens
  induction statements with
  | nil => rfl
  | cons s rest ih =>
      simp only [List.flatMap_cons, List.map_append, ih,
        statementTokens_serialized]

/-! ## Leaf coverage by construction -/

private theorem tokenLeaf_of_mem {statements : List RawStatement}
    {token : ClassifiedToken} {sort : String}
    (hmem : token ∈ pipelineTokens statements)
    (hsort : lexicalSort? lexicalDeclarations token = some sort) :
    TokenLeaf
      (lexicalizedLanguage sourceGrammar lexicalDeclarations
        (pipelineSource statements)) sort token.serialized :=
  tokenLeaf_lexicalized sourceGrammar lexicalDeclarations
    (pipelineSource statements) hmem hsort

/-- **Self-supplied leaf coverage**: every statement of the stream has
its full leaf coverage in the lexicalized language of the stream's own
classified source. -/
theorem pipelineSource_statementLeaves (statements : List RawStatement) :
    ∀ s ∈ statements,
      StatementLeaves
        (lexicalizedLanguage sourceGrammar lexicalDeclarations
          (pipelineSource statements)) s := by
  intro s hs
  cases s with
  | openScope site => trivial
  | closeScope site => trivial
  | constDecl site names terminator =>
      intro n hn
      have hmem : classifiedName "mm-symbol" n ∈
          statementTokens (.constDecl site names terminator) :=
        List.mem_cons_of_mem _
          (List.mem_append_left _ (List.mem_map_of_mem hn))
      exact tokenLeaf_of_mem (List.mem_flatMap.mpr ⟨_, hs, hmem⟩) rfl
  | varDecl site names terminator =>
      intro n hn
      have hmem : classifiedName "mm-symbol" n ∈
          statementTokens (.varDecl site names terminator) :=
        List.mem_cons_of_mem _
          (List.mem_append_left _ (List.mem_map_of_mem hn))
      exact tokenLeaf_of_mem (List.mem_flatMap.mpr ⟨_, hs, hmem⟩) rfl
  | djDecl site names terminator =>
      intro n hn
      have hmem : classifiedName "mm-symbol" n ∈
          statementTokens (.djDecl site names terminator) :=
        List.mem_cons_of_mem _
          (List.mem_append_left _ (List.mem_map_of_mem hn))
      exact tokenLeaf_of_mem (List.mem_flatMap.mpr ⟨_, hs, hmem⟩) rfl
  | floating site label typecode variableName terminator =>
      refine ⟨?_, ?_, ?_⟩
      · have hmem : classifiedName "mm-label" label ∈
            statementTokens
              (.floating site label typecode variableName
                terminator) := by
          simp [statementTokens]
        exact tokenLeaf_of_mem (List.mem_flatMap.mpr ⟨_, hs, hmem⟩) rfl
      · have hmem : classifiedName "mm-symbol" typecode ∈
            statementTokens
              (.floating site label typecode variableName
                terminator) := by
          simp [statementTokens]
        exact tokenLeaf_of_mem (List.mem_flatMap.mpr ⟨_, hs, hmem⟩) rfl
      · have hmem : classifiedName "mm-symbol" variableName ∈
            statementTokens
              (.floating site label typecode variableName
                terminator) := by
          simp [statementTokens]
        exact tokenLeaf_of_mem (List.mem_flatMap.mpr ⟨_, hs, hmem⟩) rfl
  | essential site label typecode body terminator =>
      refine ⟨?_, ?_, ?_⟩
      · have hmem : classifiedName "mm-label" label ∈
            statementTokens
              (.essential site label typecode body terminator) := by
          simp [statementTokens]
        exact tokenLeaf_of_mem (List.mem_flatMap.mpr ⟨_, hs, hmem⟩) rfl
      · have hmem : classifiedName "mm-symbol" typecode ∈
            statementTokens
              (.essential site label typecode body terminator) := by
          simp [statementTokens]
        exact tokenLeaf_of_mem (List.mem_flatMap.mpr ⟨_, hs, hmem⟩) rfl
      · intro n hn
        have hmem : classifiedName "mm-symbol" n ∈
            statementTokens
              (.essential site label typecode body terminator) :=
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_append_left _
              (List.mem_map_of_mem hn))))
        exact tokenLeaf_of_mem (List.mem_flatMap.mpr ⟨_, hs, hmem⟩) rfl
  | axiomatic site label typecode body terminator =>
      refine ⟨?_, ?_, ?_⟩
      · have hmem : classifiedName "mm-label" label ∈
            statementTokens
              (.axiomatic site label typecode body terminator) := by
          simp [statementTokens]
        exact tokenLeaf_of_mem (List.mem_flatMap.mpr ⟨_, hs, hmem⟩) rfl
      · have hmem : classifiedName "mm-symbol" typecode ∈
            statementTokens
              (.axiomatic site label typecode body terminator) := by
          simp [statementTokens]
        exact tokenLeaf_of_mem (List.mem_flatMap.mpr ⟨_, hs, hmem⟩) rfl
      · intro n hn
        have hmem : classifiedName "mm-symbol" n ∈
            statementTokens
              (.axiomatic site label typecode body terminator) :=
          List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_append_left _
              (List.mem_map_of_mem hn))))
        exact tokenLeaf_of_mem (List.mem_flatMap.mpr ⟨_, hs, hmem⟩) rfl
  | provable site label typecode body proof separator terminator =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · have hmem : classifiedName "mm-label" label ∈
            statementTokens
              (.provable site label typecode body proof separator
                terminator) := by
          simp [statementTokens]
        exact tokenLeaf_of_mem (List.mem_flatMap.mpr ⟨_, hs, hmem⟩) rfl
      · have hmem : classifiedName "mm-symbol" typecode ∈
            statementTokens
              (.provable site label typecode body proof separator
                terminator) := by
          simp [statementTokens]
        exact tokenLeaf_of_mem (List.mem_flatMap.mpr ⟨_, hs, hmem⟩) rfl
      · intro n hn
        have hmem : classifiedName "mm-symbol" n ∈
            statementTokens
              (.provable site label typecode body proof separator
                terminator) :=
          List.mem_append_left _ (List.mem_append_left _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
              (List.mem_cons_of_mem _ (List.mem_map_of_mem hn)))))
        exact tokenLeaf_of_mem (List.mem_flatMap.mpr ⟨_, hs, hmem⟩) rfl
      · cases proof with
        | normal steps =>
            intro st hst
            by_cases hq : st.name = "?"
            · exact Or.inr hq
            · refine Or.inl ?_
              have hform : proofStepToken st =
                  classifiedName "mm-proof-label" st := by
                simp [proofStepToken, hq]
              have hmem : proofStepToken st ∈
                  statementTokens
                    (.provable site label typecode body
                      (.normal steps) separator terminator) :=
                List.mem_append_left _ (List.mem_append_right _
                  (List.mem_cons_of_mem _ (List.mem_map_of_mem hst)))
              rw [hform] at hmem
              exact tokenLeaf_of_mem
                (List.mem_flatMap.mpr ⟨_, hs, hmem⟩) rfl
        | compressed openParen header closeParen words =>
            refine ⟨?_, ?_⟩
            · intro n hn
              have hmem : classifiedName "mm-proof-label" n ∈
                  statementTokens
                    (.provable site label typecode body
                      (.compressed openParen header closeParen words)
                      separator terminator) :=
                List.mem_append_left _ (List.mem_append_right _
                  (List.mem_cons_of_mem _ (List.mem_append_left _
                    (List.mem_cons_of_mem _
                      (List.mem_map_of_mem hn)))))
              exact tokenLeaf_of_mem
                (List.mem_flatMap.mpr ⟨_, hs, hmem⟩) rfl
            · intro w hw
              have hmem : classifiedName "mm-compressed-word"
                  ⟨w.span, tokenText w.bytes⟩ ∈
                  statementTokens
                    (.provable site label typecode body
                      (.compressed openParen header closeParen words)
                      separator terminator) :=
                List.mem_append_left _ (List.mem_append_right _
                  (List.mem_cons_of_mem _ (List.mem_append_right _
                    (List.mem_cons_of_mem _
                      (List.mem_map_of_mem hw)))))
              exact tokenLeaf_of_mem
                (List.mem_flatMap.mpr ⟨_, hs, hmem⟩) rfl

/-! ## Hypothesis-free structural derivation -/

open Mettapedia.Languages.Metamath.SourceGSLTIncludeDAG in
/-- Every accepted composed run's statement
stream derives the outer database sort in the lexicalized language of
its own classified source.  No lexical-leaf or ordered-token-agreement
premise is supplied: the fold discharges balance, scoping, and gate
arities; the segmenter discharges proof-shape arities; leaf coverage is
self-supplied by `pipelineSource`. -/
theorem runSource_selfLexicalized_derives {files : FileMap}
    {policy : IncludePolicy} {root : String} {fuel : Nat}
    {state : Mettapedia.Languages.Metamath.SourceGSLTState.SourceState}
    {obligations : List TheoremObligation}
    (h : runSource files policy root fuel = .ok state obligations) :
    ∃ (tokens : List LocatedToken) (statements : List RawStatement),
      segmentStatements tokens = .ok statements ∧
        foldStatements
          Mettapedia.Languages.Metamath.SourceGSLTState.initialState
          statements = .ok (state, obligations) ∧
        ∃ tree,
          Derives
            (lexicalizedLanguage sourceGrammar lexicalDeclarations
              (pipelineSource statements)) outerDatabaseSort
            (statements.flatMap RawStatement.tokenStrings) tree := by
  obtain ⟨spans, tokens, statements, hexp, hres, hseg, hfold,
    hcomplete⟩ := runSource_ok_inv h
  refine ⟨tokens, statements, hseg, hfold, ?_⟩
  exact statements_derive_outerDatabase
    (fun r hr => baseRule_mem_lexicalized sourceGrammar
      lexicalDeclarations (pipelineSource statements) hr)
    hfold rfl (sourceStateComplete_scopes_length hcomplete)
    (segmentStatements_normalSteps hseg)
    (segmentStatements_compressedWords hseg)
    (pipelineSource_statementLeaves statements)

open Mettapedia.Languages.Metamath.SourceGSLTIncludeDAG in
/-- The same theorem at the source's ordered ledger — the exact judgment
shape certified by the checked DAG boundary
(`checkedMetamathSourceBlocks_sound`), with the alignment holding by
construction rather than by premise. -/
theorem runSource_selfLexicalized_ledger {files : FileMap}
    {policy : IncludePolicy} {root : String} {fuel : Nat}
    {state : Mettapedia.Languages.Metamath.SourceGSLTState.SourceState}
    {obligations : List TheoremObligation}
    (h : runSource files policy root fuel = .ok state obligations) :
    ∃ (tokens : List LocatedToken) (statements : List RawStatement),
      segmentStatements tokens = .ok statements ∧
        foldStatements
          Mettapedia.Languages.Metamath.SourceGSLTState.initialState
          statements = .ok (state, obligations) ∧
        ∃ tree,
          Derives
            (lexicalizedLanguage sourceGrammar lexicalDeclarations
              (pipelineSource statements)) outerDatabaseSort
            (pipelineSource statements).ledger.tokens tree := by
  obtain ⟨tokens, statements, hseg, hfold, tree, htree⟩ :=
    runSource_selfLexicalized_derives h
  exact ⟨tokens, statements, hseg, hfold, tree, by
    rw [pipelineSource_ledger]
    exact htree⟩

/-! ## Charset grounding: the classification answers to the raw bytes

Every classified name occurrence in an accepted stream was consumed
through the segmenter's byte guards, so its text is the `tokenText`
image of a byte list satisfying the authored charset for its class. -/

/-- The token's text is the image of charset-valid bytes. -/
def NameCharset (charset : List UInt8 → Bool) (n : LocatedName) : Prop :=
  ∃ bs, charset bs = true ∧ n.name = tokenText bs

/-- Charset provenance for one proof payload. -/
def PayloadCharsets : ProofPayload → Prop
  | .normal steps => ∀ st ∈ steps, NameCharset proofTokenValid st
  | .compressed _ header _ words =>
      (∀ n ∈ header, NameCharset labelBytesValid n) ∧
        ∀ w ∈ words, compressedWordValid w.bytes = true

/-- Charset provenance for one statement. -/
def StatementCharsets : RawStatement → Prop
  | .openScope _ => True
  | .closeScope _ => True
  | .constDecl _ names _ => ∀ n ∈ names, NameCharset mathBytesValid n
  | .varDecl _ names _ => ∀ n ∈ names, NameCharset mathBytesValid n
  | .djDecl _ names _ => ∀ n ∈ names, NameCharset mathBytesValid n
  | .floating _ label typecode variableName _ =>
      NameCharset labelBytesValid label ∧
        NameCharset mathBytesValid typecode ∧
        NameCharset mathBytesValid variableName
  | .essential _ label typecode body _ =>
      NameCharset labelBytesValid label ∧
        NameCharset mathBytesValid typecode ∧
        ∀ n ∈ body, NameCharset mathBytesValid n
  | .axiomatic _ label typecode body _ =>
      NameCharset labelBytesValid label ∧
        NameCharset mathBytesValid typecode ∧
        ∀ n ∈ body, NameCharset mathBytesValid n
  | .provable _ label typecode body proof _ _ =>
      NameCharset labelBytesValid label ∧
        NameCharset mathBytesValid typecode ∧
        (∀ n ∈ body, NameCharset mathBytesValid n) ∧
        PayloadCharsets proof

/-- Mode invariant carrying charset provenance for every accumulator. -/
def ModeCharsets : SegMode → Prop
  | .top => True
  | .pendingLabel label => NameCharset labelBytesValid label
  | .collecting _ _ acc => ∀ n ∈ acc, NameCharset mathBytesValid n
  | .floatBody _ label acc =>
      NameCharset labelBytesValid label ∧
        ∀ n ∈ acc, NameCharset mathBytesValid n
  | .essentialBody _ label acc =>
      NameCharset labelBytesValid label ∧
        ∀ n ∈ acc, NameCharset mathBytesValid n
  | .axiomBody _ label acc =>
      NameCharset labelBytesValid label ∧
        ∀ n ∈ acc, NameCharset mathBytesValid n
  | .provableBody _ label acc =>
      NameCharset labelBytesValid label ∧
        ∀ n ∈ acc, NameCharset mathBytesValid n
  | .proofDecide _ label formula _ =>
      NameCharset labelBytesValid label ∧
        ∀ n ∈ formula, NameCharset mathBytesValid n
  | .proofNormal _ label formula _ acc =>
      NameCharset labelBytesValid label ∧
        (∀ n ∈ formula, NameCharset mathBytesValid n) ∧
        ∀ st ∈ acc, NameCharset proofTokenValid st
  | .proofHeader _ label formula _ _ acc =>
      NameCharset labelBytesValid label ∧
        (∀ n ∈ formula, NameCharset mathBytesValid n) ∧
        ∀ n ∈ acc, NameCharset labelBytesValid n
  | .proofWords _ label formula _ _ _ header acc =>
      NameCharset labelBytesValid label ∧
        (∀ n ∈ formula, NameCharset mathBytesValid n) ∧
        (∀ n ∈ header, NameCharset labelBytesValid n) ∧
        ∀ w ∈ acc, compressedWordValid w.bytes = true

set_option maxHeartbeats 2000000 in
theorem segmentStep_charsets {mode : SegMode} {tok : LocatedToken}
    {emitted : List RawStatement} {nextMode : SegMode}
    (hmode : ModeCharsets mode)
    (h : segmentStep mode tok = .ok (emitted, nextMode)) :
    ModeCharsets nextMode ∧ ∀ s ∈ emitted, StatementCharsets s := by
  cases mode with
  | top =>
      simp only [segmentStep] at h
      repeat' split at h
      all_goals cases h
      all_goals first
        | exact And.intro trivial (fun s hs => by
            rcases List.mem_singleton.mp hs with rfl
            trivial)
        | exact And.intro (fun n hn => absurd hn List.not_mem_nil)
            (fun s hs => absurd hs List.not_mem_nil)
        | exact And.intro ⟨tok.bytes, by assumption, rfl⟩
            (fun s hs => absurd hs List.not_mem_nil)
  | pendingLabel label =>
      simp only [segmentStep] at h
      repeat' split at h
      all_goals cases h
      all_goals
        exact ⟨⟨hmode, fun n hn => nomatch hn⟩,
          fun s hs => nomatch hs⟩
  | collecting kind site acc =>
      simp only [segmentStep] at h
      repeat' split at h
      all_goals cases h
      all_goals first
        | exact And.intro trivial (fun s hs => by
            rcases List.mem_singleton.mp hs with rfl
            exact fun n hn => hmode n (List.mem_reverse.mp hn))
        | exact And.intro (fun n hn => by
            rcases List.mem_cons.mp hn with rfl | htail
            · exact ⟨tok.bytes, by assumption, rfl⟩
            · exact hmode n htail)
            (fun s hs => absurd hs List.not_mem_nil)
  | floatBody site label acc =>
      simp only [segmentStep] at h
      by_cases hterm : tok.bytes = statementEndBytes
      · rw [if_pos hterm] at h
        cases hrev : acc.reverse with
        | nil =>
            rw [hrev] at h
            exact nomatch h
        | cons typecode rest1 =>
            cases rest1 with
            | nil =>
                rw [hrev] at h
                exact nomatch h
            | cons variableName rest2 =>
                cases rest2 with
                | nil =>
                    rw [hrev] at h
                    cases h
                    refine ⟨trivial, fun s hs => ?_⟩
                    rcases List.mem_singleton.mp hs with rfl
                    have htc : typecode ∈ acc := by
                      rw [← List.mem_reverse, hrev]
                      simp
                    have hv : variableName ∈ acc := by
                      rw [← List.mem_reverse, hrev]
                      simp
                    exact ⟨hmode.1, hmode.2 typecode htc,
                      hmode.2 variableName hv⟩
                | cons w rest3 =>
                    rw [hrev] at h
                    exact nomatch h
      · rw [if_neg hterm] at h
        repeat' split at h
        all_goals cases h
        all_goals
          exact ⟨⟨hmode.1, fun n hn => by
            rcases List.mem_cons.mp hn with rfl | htail
            · exact ⟨tok.bytes, by assumption, rfl⟩
            · exact hmode.2 n htail⟩,
            fun s hs => nomatch hs⟩
  | essentialBody site label acc =>
      simp only [segmentStep] at h
      by_cases hterm : tok.bytes = statementEndBytes
      · rw [if_pos hterm] at h
        cases hsp : splitFormula site acc with
        | rejected r =>
            simp only [hsp] at h
            exact nomatch h
        | ok pair =>
            obtain ⟨typecode, body⟩ := pair
            simp only [hsp] at h
            cases h
            have hrev := splitFormula_ok hsp
            refine ⟨trivial, fun s hs => ?_⟩
            rcases List.mem_singleton.mp hs with rfl
            refine ⟨hmode.1, ?_, ?_⟩
            · refine hmode.2 typecode ?_
              rw [← List.mem_reverse, hrev]
              simp
            · intro n hn
              refine hmode.2 n ?_
              rw [← List.mem_reverse, hrev]
              simp [hn]
      · rw [if_neg hterm] at h
        repeat' split at h
        all_goals cases h
        all_goals
          exact ⟨⟨hmode.1, fun n hn => by
            rcases List.mem_cons.mp hn with rfl | htail
            · exact ⟨tok.bytes, by assumption, rfl⟩
            · exact hmode.2 n htail⟩,
            fun s hs => nomatch hs⟩
  | axiomBody site label acc =>
      simp only [segmentStep] at h
      by_cases hterm : tok.bytes = statementEndBytes
      · rw [if_pos hterm] at h
        cases hsp : splitFormula site acc with
        | rejected r =>
            simp only [hsp] at h
            exact nomatch h
        | ok pair =>
            obtain ⟨typecode, body⟩ := pair
            simp only [hsp] at h
            cases h
            have hrev := splitFormula_ok hsp
            refine ⟨trivial, fun s hs => ?_⟩
            rcases List.mem_singleton.mp hs with rfl
            refine ⟨hmode.1, ?_, ?_⟩
            · refine hmode.2 typecode ?_
              rw [← List.mem_reverse, hrev]
              simp
            · intro n hn
              refine hmode.2 n ?_
              rw [← List.mem_reverse, hrev]
              simp [hn]
      · rw [if_neg hterm] at h
        repeat' split at h
        all_goals cases h
        all_goals
          exact ⟨⟨hmode.1, fun n hn => by
            rcases List.mem_cons.mp hn with rfl | htail
            · exact ⟨tok.bytes, by assumption, rfl⟩
            · exact hmode.2 n htail⟩,
            fun s hs => nomatch hs⟩
  | provableBody site label acc =>
      simp only [segmentStep] at h
      repeat' split at h
      all_goals cases h
      all_goals first
        | exact And.intro ⟨hmode.1, hmode.2⟩
            (fun s hs => absurd hs List.not_mem_nil)
        | exact And.intro ⟨hmode.1, fun n hn => by
            rcases List.mem_cons.mp hn with rfl | htail
            · exact ⟨tok.bytes, by assumption, rfl⟩
            · exact hmode.2 n htail⟩
            (fun s hs => absurd hs List.not_mem_nil)
  | proofDecide site label formula separator =>
      simp only [segmentStep] at h
      repeat' split at h
      all_goals cases h
      all_goals first
        | exact And.intro
            ⟨hmode.1, hmode.2, fun n hn => absurd hn List.not_mem_nil⟩
            (fun s hs => absurd hs List.not_mem_nil)
        | exact And.intro ⟨hmode.1, hmode.2, fun st hst => by
            rcases List.mem_singleton.mp hst with rfl
            exact ⟨tok.bytes, by assumption, rfl⟩⟩
            (fun s hs => absurd hs List.not_mem_nil)
  | proofNormal site label formula separator acc =>
      simp only [segmentStep] at h
      by_cases hterm : tok.bytes = statementEndBytes
      · rw [if_pos hterm] at h
        cases hsp : splitFormula site formula with
        | rejected r =>
            simp only [hsp] at h
            exact nomatch h
        | ok pair =>
            obtain ⟨typecode, body⟩ := pair
            simp only [hsp] at h
            cases h
            have hrev := splitFormula_ok hsp
            refine ⟨trivial, fun s hs => ?_⟩
            rcases List.mem_singleton.mp hs with rfl
            refine ⟨hmode.1, ?_, ?_, ?_⟩
            · refine hmode.2.1 typecode ?_
              rw [← List.mem_reverse, hrev]
              simp
            · intro n hn
              refine hmode.2.1 n ?_
              rw [← List.mem_reverse, hrev]
              simp [hn]
            · intro st hst
              exact hmode.2.2 st (List.mem_reverse.mp hst)
      · rw [if_neg hterm] at h
        repeat' split at h
        all_goals cases h
        all_goals
          exact ⟨⟨hmode.1, hmode.2.1, fun st hst => by
            rcases List.mem_cons.mp hst with rfl | htail
            · exact ⟨tok.bytes, by assumption, rfl⟩
            · exact hmode.2.2 st htail⟩,
            fun s hs => nomatch hs⟩
  | proofHeader site label formula separator openParen acc =>
      simp only [segmentStep] at h
      repeat' split at h
      all_goals cases h
      all_goals first
        | exact And.intro
            ⟨hmode.1, hmode.2.1, fun n hn =>
              hmode.2.2 n (List.mem_reverse.mp hn),
              fun w hw => absurd hw List.not_mem_nil⟩
            (fun s hs => absurd hs List.not_mem_nil)
        | exact And.intro ⟨hmode.1, hmode.2.1, fun n hn => by
            rcases List.mem_cons.mp hn with rfl | htail
            · exact ⟨tok.bytes, by assumption, rfl⟩
            · exact hmode.2.2 n htail⟩
            (fun s hs => absurd hs List.not_mem_nil)
  | proofWords site label formula separator openParen closeParen
      header acc =>
      simp only [segmentStep] at h
      by_cases hterm : tok.bytes = statementEndBytes
      · rw [if_pos hterm] at h
        by_cases hacc : acc.isEmpty
        · rw [if_pos hacc] at h
          exact nomatch h
        · rw [if_neg hacc] at h
          cases hsp : splitFormula site formula with
          | rejected r =>
              simp only [hsp] at h
              exact nomatch h
          | ok pair =>
              obtain ⟨typecode, body⟩ := pair
              simp only [hsp] at h
              cases h
              have hrev := splitFormula_ok hsp
              refine ⟨trivial, fun s hs => ?_⟩
              rcases List.mem_singleton.mp hs with rfl
              refine ⟨hmode.1, ?_, ?_, ?_, ?_⟩
              · refine hmode.2.1 typecode ?_
                rw [← List.mem_reverse, hrev]
                simp
              · intro n hn
                refine hmode.2.1 n ?_
                rw [← List.mem_reverse, hrev]
                simp [hn]
              · exact hmode.2.2.1
              · intro w hw
                exact hmode.2.2.2 w (List.mem_reverse.mp hw)
      · rw [if_neg hterm] at h
        repeat' split at h
        all_goals cases h
        all_goals
          exact ⟨⟨hmode.1, hmode.2.1, hmode.2.2.1, fun w hw => by
            rcases List.mem_cons.mp hw with rfl | htail
            · assumption
            · exact hmode.2.2.2 w htail⟩,
            fun s hs => nomatch hs⟩

theorem segmentRun_charsets :
    ∀ {tokens : List LocatedToken} {mode : SegMode}
      {acc statements : List RawStatement},
      segmentRun tokens mode acc = .ok statements →
      ModeCharsets mode → (∀ s ∈ acc, StatementCharsets s) →
      ∀ s ∈ statements, StatementCharsets s := by
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
          obtain ⟨hnext, hemit⟩ := segmentStep_charsets hmode hstep
          refine ih h hnext ?_
          intro s hs
          rcases List.mem_append.mp hs with hrev | hold
          · exact hemit s (by simpa using hrev)
          · exact hacc s hold

/-- Every accepted segmentation carries charset provenance for every
consumed name. -/
theorem segmentStatements_charsets
    {tokens : List LocatedToken} {statements : List RawStatement}
    (h : segmentStatements tokens = .ok statements) :
    ∀ s ∈ statements, StatementCharsets s :=
  segmentRun_charsets h trivial (fun _ hs => nomatch hs)

/-- The classification only emits the five class strings. -/
theorem pipelineTokens_class {statements : List RawStatement}
    {t : ClassifiedToken} (ht : t ∈ pipelineTokens statements)
    (h1 : ¬t.className = "mm-label") (h2 : ¬t.className = "mm-symbol")
    (h3 : ¬t.className = "mm-proof-label")
    (h4 : ¬t.className = "mm-compressed-word") : t.className = "" := by
  obtain ⟨s, _hs, hts⟩ := List.mem_flatMap.mp ht
  cases s with
  | openScope site =>
      rcases List.mem_singleton.mp hts with rfl
      rfl
  | closeScope site =>
      rcases List.mem_singleton.mp hts with rfl
      rfl
  | constDecl site names terminator =>
      rcases List.mem_append.mp hts with hin | hin
      · rcases List.mem_cons.mp hin with rfl | hmap
        · rfl
        · obtain ⟨n, _, rfl⟩ := List.mem_map.mp hmap
          exact absurd rfl h2
      · rcases List.mem_singleton.mp hin with rfl
        rfl
  | varDecl site names terminator =>
      rcases List.mem_append.mp hts with hin | hin
      · rcases List.mem_cons.mp hin with rfl | hmap
        · rfl
        · obtain ⟨n, _, rfl⟩ := List.mem_map.mp hmap
          exact absurd rfl h2
      · rcases List.mem_singleton.mp hin with rfl
        rfl
  | djDecl site names terminator =>
      rcases List.mem_append.mp hts with hin | hin
      · rcases List.mem_cons.mp hin with rfl | hmap
        · rfl
        · obtain ⟨n, _, rfl⟩ := List.mem_map.mp hmap
          exact absurd rfl h2
      · rcases List.mem_singleton.mp hin with rfl
        rfl
  | floating site label typecode variableName terminator =>
      rcases List.mem_cons.mp hts with rfl | hts
      · exact absurd rfl h1
      rcases List.mem_cons.mp hts with rfl | hts
      · rfl
      rcases List.mem_cons.mp hts with rfl | hts
      · exact absurd rfl h2
      rcases List.mem_cons.mp hts with rfl | hts
      · exact absurd rfl h2
      rcases List.mem_singleton.mp hts with rfl
      rfl
  | essential site label typecode body terminator =>
      rcases List.mem_append.mp hts with hin | hin
      · rcases List.mem_cons.mp hin with rfl | hin
        · exact absurd rfl h1
        rcases List.mem_cons.mp hin with rfl | hin
        · rfl
        rcases List.mem_cons.mp hin with rfl | hin
        · exact absurd rfl h2
        obtain ⟨n, _, rfl⟩ := List.mem_map.mp hin
        exact absurd rfl h2
      · rcases List.mem_singleton.mp hin with rfl
        rfl
  | axiomatic site label typecode body terminator =>
      rcases List.mem_append.mp hts with hin | hin
      · rcases List.mem_cons.mp hin with rfl | hin
        · exact absurd rfl h1
        rcases List.mem_cons.mp hin with rfl | hin
        · rfl
        rcases List.mem_cons.mp hin with rfl | hin
        · exact absurd rfl h2
        obtain ⟨n, _, rfl⟩ := List.mem_map.mp hin
        exact absurd rfl h2
      · rcases List.mem_singleton.mp hin with rfl
        rfl
  | provable site label typecode body proof separator terminator =>
      rcases List.mem_append.mp hts with hin | hin
      · rcases List.mem_append.mp hin with hin | hpay
        · rcases List.mem_cons.mp hin with rfl | hin
          · exact absurd rfl h1
          rcases List.mem_cons.mp hin with rfl | hin
          · rfl
          rcases List.mem_cons.mp hin with rfl | hin
          · exact absurd rfl h2
          obtain ⟨n, _, rfl⟩ := List.mem_map.mp hin
          exact absurd rfl h2
        · rcases List.mem_cons.mp hpay with rfl | hpay
          · rfl
          cases proof with
          | normal steps =>
              obtain ⟨n, _, rfl⟩ := List.mem_map.mp hpay
              by_cases hq : n.name = "?"
              · simp [proofStepToken, hq, keywordToken]
              · exact absurd
                  (by simp [proofStepToken, hq, classifiedName]) h3
          | compressed openParen header closeParen words =>
              rcases List.mem_append.mp hpay with hp | hp
              · rcases List.mem_cons.mp hp with rfl | hp
                · rfl
                obtain ⟨n, _, rfl⟩ := List.mem_map.mp hp
                exact absurd rfl h3
              · rcases List.mem_cons.mp hp with rfl | hp
                · rfl
                obtain ⟨w, _, rfl⟩ := List.mem_map.mp hp
                exact absurd rfl h4
      · rcases List.mem_singleton.mp hin with rfl
        rfl

/-! ## Grounding in the authored raw-byte GSLT -/

open Mettapedia.Languages.Metamath.SourceGSLTStatementAuthority

/-- The keyword spellings the classification can emit. -/
def pipelineKeywords : List String :=
  ["${", "$}", "$c", "$v", "$d", "$f", "$e", "$a", "$p", "$=", "$.",
   "(", ")", "?"]

/-- Every emitted keyword is an authored literal spelling. -/
theorem pipelineKeywords_authored :
    ∀ s ∈ pipelineKeywords, s ∈ literalBindings.map (·.spelling) := by
  decide

/-- One classified token, grounded in the authored raw-byte GSLT:
lexical classes carry charset-valid byte provenance; keywords are
drawn from the fixed authored spellings. -/
def TokenGrounded (t : ClassifiedToken) : Prop :=
  (t.className = "mm-label" →
    ∃ bs, labelBytesValid bs = true ∧ t.serialized = tokenText bs) ∧
  (t.className = "mm-symbol" →
    ∃ bs, mathBytesValid bs = true ∧ t.serialized = tokenText bs) ∧
  (t.className = "mm-proof-label" →
    ∃ bs, labelBytesValid bs = true ∧ t.serialized = tokenText bs) ∧
  (t.className = "mm-compressed-word" →
    ∃ bs, compressedWordValid bs = true ∧
      t.serialized = tokenText bs) ∧
  (t.className = "" → t.serialized ∈ pipelineKeywords)

private theorem grounded_keyword {s : String}
    (h : s ∈ pipelineKeywords) : TokenGrounded (keywordToken s) :=
  ⟨fun hc => absurd hc (by simp [keywordToken]),
    fun hc => absurd hc (by simp [keywordToken]),
    fun hc => absurd hc (by simp [keywordToken]),
    fun hc => absurd hc (by simp [keywordToken]),
    fun _ => h⟩

private theorem grounded_label {n : LocatedName}
    (h : NameCharset labelBytesValid n) :
    TokenGrounded (classifiedName "mm-label" n) := by
  obtain ⟨bs, hbs, hname⟩ := h
  exact ⟨fun _ => ⟨bs, hbs, hname⟩,
    fun hc => absurd hc (by simp [classifiedName]),
    fun hc => absurd hc (by simp [classifiedName]),
    fun hc => absurd hc (by simp [classifiedName]),
    fun hc => absurd hc (by simp [classifiedName])⟩

private theorem grounded_symbol {n : LocatedName}
    (h : NameCharset mathBytesValid n) :
    TokenGrounded (classifiedName "mm-symbol" n) := by
  obtain ⟨bs, hbs, hname⟩ := h
  exact ⟨fun hc => absurd hc (by simp [classifiedName]),
    fun _ => ⟨bs, hbs, hname⟩,
    fun hc => absurd hc (by simp [classifiedName]),
    fun hc => absurd hc (by simp [classifiedName]),
    fun hc => absurd hc (by simp [classifiedName])⟩

private theorem grounded_proofLabel {n : LocatedName}
    (h : NameCharset labelBytesValid n) :
    TokenGrounded (classifiedName "mm-proof-label" n) := by
  obtain ⟨bs, hbs, hname⟩ := h
  exact ⟨fun hc => absurd hc (by simp [classifiedName]),
    fun hc => absurd hc (by simp [classifiedName]),
    fun _ => ⟨bs, hbs, hname⟩,
    fun hc => absurd hc (by simp [classifiedName]),
    fun hc => absurd hc (by simp [classifiedName])⟩

private theorem grounded_word {w : LocatedToken}
    (h : compressedWordValid w.bytes = true) :
    TokenGrounded
      (classifiedName "mm-compressed-word"
        ⟨w.span, tokenText w.bytes⟩) := by
  exact ⟨fun hc => absurd hc (by simp [classifiedName]),
    fun hc => absurd hc (by simp [classifiedName]),
    fun hc => absurd hc (by simp [classifiedName]),
    fun _ => ⟨w.bytes, h, rfl⟩,
    fun hc => absurd hc (by simp [classifiedName])⟩

/-- A normal step token: `?` is an authored keyword; anything else is a
label-charset proof label. -/
private theorem proofTokenValid_ne_question {bs : List UInt8}
    (h : proofTokenValid bs = true) (hne : tokenText bs ≠ "?") :
    labelBytesValid bs = true := by
  have h' : labelBytesValid bs = true ∨
      bs = List.map UInt8.ofNat
        Mettapedia.Languages.Metamath.SourceGSLTStatementPlan.sourceStatementPlan.unknownProof.codepoints := by
    simpa [proofTokenValid] using h
  rcases h' with hlab | hq
  · exact hlab
  · exfalso
    apply hne
    rw [hq]
    rfl

private theorem grounded_proofStep {n : LocatedName}
    (h : NameCharset proofTokenValid n) :
    TokenGrounded (proofStepToken n) := by
  obtain ⟨bs, hbs, hname⟩ := h
  by_cases hq : n.name = "?"
  · rw [proofStepToken, if_pos hq]
    exact grounded_keyword (by decide)
  · rw [proofStepToken, if_neg hq]
    refine grounded_proofLabel ⟨bs, ?_, hname⟩
    exact proofTokenValid_ne_question hbs (by
      rw [← hname]
      exact hq)

/-- **Grounding**: every classified token of an accepted stream answers
to the authored raw-byte GSLT. -/
theorem pipelineSource_grounded {tokens : List LocatedToken}
    {statements : List RawStatement}
    (hseg : segmentStatements tokens = .ok statements) :
    ∀ t ∈ pipelineTokens statements, TokenGrounded t := by
  intro t ht
  obtain ⟨s, hs, hts⟩ := List.mem_flatMap.mp ht
  have hcs := segmentStatements_charsets hseg s hs
  clear ht hseg
  cases s with
  | openScope site =>
      rcases List.mem_singleton.mp hts with rfl
      exact grounded_keyword (by decide)
  | closeScope site =>
      rcases List.mem_singleton.mp hts with rfl
      exact grounded_keyword (by decide)
  | constDecl site names terminator =>
      rcases List.mem_append.mp hts with h1 | h2
      · rcases List.mem_cons.mp h1 with rfl | hmap
        · exact grounded_keyword (by decide)
        · obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hmap
          exact grounded_symbol (hcs n hn)
      · rcases List.mem_singleton.mp h2 with rfl
        exact grounded_keyword (by decide)
  | varDecl site names terminator =>
      rcases List.mem_append.mp hts with h1 | h2
      · rcases List.mem_cons.mp h1 with rfl | hmap
        · exact grounded_keyword (by decide)
        · obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hmap
          exact grounded_symbol (hcs n hn)
      · rcases List.mem_singleton.mp h2 with rfl
        exact grounded_keyword (by decide)
  | djDecl site names terminator =>
      rcases List.mem_append.mp hts with h1 | h2
      · rcases List.mem_cons.mp h1 with rfl | hmap
        · exact grounded_keyword (by decide)
        · obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hmap
          exact grounded_symbol (hcs n hn)
      · rcases List.mem_singleton.mp h2 with rfl
        exact grounded_keyword (by decide)
  | floating site label typecode variableName terminator =>
      rcases List.mem_cons.mp hts with rfl | hts
      · exact grounded_label hcs.1
      rcases List.mem_cons.mp hts with rfl | hts
      · exact grounded_keyword (by decide)
      rcases List.mem_cons.mp hts with rfl | hts
      · exact grounded_symbol hcs.2.1
      rcases List.mem_cons.mp hts with rfl | hts
      · exact grounded_symbol hcs.2.2
      rcases List.mem_singleton.mp hts with rfl
      exact grounded_keyword (by decide)
  | essential site label typecode body terminator =>
      rcases List.mem_append.mp hts with h1 | h2
      · rcases List.mem_cons.mp h1 with rfl | h1
        · exact grounded_label hcs.1
        rcases List.mem_cons.mp h1 with rfl | h1
        · exact grounded_keyword (by decide)
        rcases List.mem_cons.mp h1 with rfl | h1
        · exact grounded_symbol hcs.2.1
        obtain ⟨n, hn, rfl⟩ := List.mem_map.mp h1
        exact grounded_symbol (hcs.2.2 n hn)
      · rcases List.mem_singleton.mp h2 with rfl
        exact grounded_keyword (by decide)
  | axiomatic site label typecode body terminator =>
      rcases List.mem_append.mp hts with h1 | h2
      · rcases List.mem_cons.mp h1 with rfl | h1
        · exact grounded_label hcs.1
        rcases List.mem_cons.mp h1 with rfl | h1
        · exact grounded_keyword (by decide)
        rcases List.mem_cons.mp h1 with rfl | h1
        · exact grounded_symbol hcs.2.1
        obtain ⟨n, hn, rfl⟩ := List.mem_map.mp h1
        exact grounded_symbol (hcs.2.2 n hn)
      · rcases List.mem_singleton.mp h2 with rfl
        exact grounded_keyword (by decide)
  | provable site label typecode body proof separator terminator =>
      rcases List.mem_append.mp hts with h1 | h2
      · rcases List.mem_append.mp h1 with h1 | hpay
        · rcases List.mem_cons.mp h1 with rfl | h1
          · exact grounded_label hcs.1
          rcases List.mem_cons.mp h1 with rfl | h1
          · exact grounded_keyword (by decide)
          rcases List.mem_cons.mp h1 with rfl | h1
          · exact grounded_symbol hcs.2.1
          obtain ⟨n, hn, rfl⟩ := List.mem_map.mp h1
          exact grounded_symbol (hcs.2.2.1 n hn)
        · rcases List.mem_cons.mp hpay with rfl | hpay
          · exact grounded_keyword (by decide)
          cases proof with
          | normal steps =>
              obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hpay
              exact grounded_proofStep (hcs.2.2.2 n hn)
          | compressed openParen header closeParen words =>
              rcases List.mem_append.mp hpay with hp | hp
              · rcases List.mem_cons.mp hp with rfl | hp
                · exact grounded_keyword (by decide)
                obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hp
                exact grounded_proofLabel (hcs.2.2.2.1 n hn)
              · rcases List.mem_cons.mp hp with rfl | hp
                · exact grounded_keyword (by decide)
                obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hp
                exact grounded_word (hcs.2.2.2.2 w hw)
      · rcases List.mem_singleton.mp h2 with rfl
        exact grounded_keyword (by decide)

/-! ## Byte-clean and include-free, derived -/

private theorem char_toNat_ofNat {n : Nat} (h : n < 256) :
    (Char.ofNat n).toNat = n := by
  have hvalid : n.isValidChar := Or.inl (by omega)
  simp [Char.ofNat, hvalid, Char.ofNatAux, Char.toNat]

theorem tokenText_byteClean (bs : List UInt8) :
    ByteClean (tokenText bs) := by
  intro c hc
  unfold tokenText at hc
  rw [String.toList_ofList] at hc
  obtain ⟨b, -, rfl⟩ := List.mem_map.mp hc
  have h256 : b.toNat < 256 := b.toBitVec.isLt
  rw [char_toNat_ofNat h256]
  exact h256

private theorem keywords_byteClean :
    ∀ s ∈ pipelineKeywords, ByteClean s := by
  have h : ∀ s ∈ pipelineKeywords, ∀ c ∈ s.toList, c.toNat < 256 := by
    decide
  exact h

/-- Every token string of an accepted stream is byte-clean. -/
theorem statements_byteClean {tokens : List LocatedToken}
    {statements : List RawStatement}
    (hseg : segmentStatements tokens = .ok statements) :
    ∀ t ∈ statements.flatMap RawStatement.tokenStrings, ByteClean t := by
  intro t ht
  rw [← pipelineSource_ledger] at ht
  obtain ⟨ct, hct, rfl⟩ := List.mem_map.mp ht
  have hg := pipelineSource_grounded hseg ct hct
  by_cases h0 : ct.className = ""
  · exact keywords_byteClean _ (hg.2.2.2.2 h0)
  by_cases h1 : ct.className = "mm-label"
  · obtain ⟨bs, -, heq⟩ := hg.1 h1
    rw [heq]
    exact tokenText_byteClean bs
  by_cases h2 : ct.className = "mm-symbol"
  · obtain ⟨bs, -, heq⟩ := hg.2.1 h2
    rw [heq]
    exact tokenText_byteClean bs
  by_cases h3 : ct.className = "mm-proof-label"
  · obtain ⟨bs, -, heq⟩ := hg.2.2.1 h3
    rw [heq]
    exact tokenText_byteClean bs
  by_cases h4 : ct.className = "mm-compressed-word"
  · obtain ⟨bs, -, heq⟩ := hg.2.2.2.1 h4
    rw [heq]
    exact tokenText_byteClean bs
  · exfalso
    exact h0 (pipelineTokens_class hct h1 h2 h3 h4)

/-- Charset bytes never begin with `$`. -/
private theorem tokenText_ne_include {bs : List UInt8}
    (hne : ∀ b ∈ bs, b.toNat ≠ 36) : tokenText bs ≠ "$[" := by
  intro heq
  have hlist := congrArg String.toList heq
  unfold tokenText at hlist
  rw [String.toList_ofList] at hlist
  have h2 : "$[".toList = ['$', '['] := rfl
  rw [h2] at hlist
  cases bs with
  | nil => simp at hlist
  | cons b rest =>
      simp only [List.map_cons, List.cons.injEq] at hlist
      have hb : (Char.ofNat b.toNat).toNat = '$'.toNat :=
        congrArg Char.toNat hlist.1
      have h256 : b.toNat < 256 := b.toBitVec.isLt
      rw [char_toNat_ofNat h256] at hb
      exact hne b (by simp) (by simpa using hb)

private theorem label_no_dollar {bs : List UInt8}
    (h : labelBytesValid bs = true) : ∀ b ∈ bs, b.toNat ≠ 36 := by
  intro b hb
  have h' : ¬bs = [] ∧ ∀ x ∈ bs, labelByte x = true := by
    simpa [labelBytesValid] using h
  have := (labelByte_authored b).mp (h'.2 b hb)
  intro hcontra
  rw [hcontra] at this
  exact absurd this (by decide)

private theorem math_no_dollar {bs : List UInt8}
    (h : mathBytesValid bs = true) : ∀ b ∈ bs, b.toNat ≠ 36 := by
  intro b hb
  have h' : ¬bs = [] ∧ ∀ x ∈ bs, mathByte x = true := by
    simpa [mathBytesValid] using h
  have := (mathByte_authored b).mp (h'.2 b hb)
  intro hcontra
  rw [hcontra] at this
  exact absurd this (by decide)

private theorem word_no_dollar {bs : List UInt8}
    (h : compressedWordValid bs = true) : ∀ b ∈ bs, b.toNat ≠ 36 := by
  intro b hb
  have h' : ¬bs = [] ∧ ∀ x ∈ bs, compressedWordByte x = true := by
    simpa [compressedWordValid] using h
  have := (compressedWordByte_authored b).mp (h'.2 b hb)
  intro hcontra
  rw [hcontra] at this
  exact absurd this (by decide)

/-- The include opener never occurs in an accepted stream's token
image: the include layer is discharged before segmentation, and no
charset or keyword can spell it. -/
theorem statements_no_include {tokens : List LocatedToken}
    {statements : List RawStatement}
    (hseg : segmentStatements tokens = .ok statements) :
    "$[" ∉ statements.flatMap RawStatement.tokenStrings := by
  intro ht
  rw [← pipelineSource_ledger] at ht
  obtain ⟨ct, hct, heq⟩ := List.mem_map.mp ht
  have hg := pipelineSource_grounded hseg ct hct
  by_cases h0 : ct.className = ""
  · have := hg.2.2.2.2 h0
    rw [heq] at this
    exact absurd this (by decide)
  by_cases h1 : ct.className = "mm-label"
  · obtain ⟨bs, hbs, hser⟩ := hg.1 h1
    rw [hser] at heq
    exact tokenText_ne_include (label_no_dollar hbs) heq
  by_cases h2 : ct.className = "mm-symbol"
  · obtain ⟨bs, hbs, hser⟩ := hg.2.1 h2
    rw [hser] at heq
    exact tokenText_ne_include (math_no_dollar hbs) heq
  by_cases h3 : ct.className = "mm-proof-label"
  · obtain ⟨bs, hbs, hser⟩ := hg.2.2.1 h3
    rw [hser] at heq
    exact tokenText_ne_include (label_no_dollar hbs) heq
  by_cases h4 : ct.className = "mm-compressed-word"
  · obtain ⟨bs, hbs, hser⟩ := hg.2.2.2.1 h4
    rw [hser] at heq
    exact tokenText_ne_include (word_no_dollar hbs) heq
  · exact h0 (pipelineTokens_class hct h1 h2 h3 h4)

/-! ## The premise-free correspondence at the pipeline source -/

open Mettapedia.Languages.Metamath.SourceGSLTIncludeDAG in
/-- **Premise-free universal correspondence**: for every accepted
composed run, derivability of the statement stream's token image in
its own lexicalization is equivalent to the nested-stream
characterization — with the include-free and byte-clean side conditions
derived from the authored raw-byte GSLT, not supplied. -/
theorem runSource_selfLexicalized_correspondence {files : FileMap}
    {policy : IncludePolicy} {root : String} {fuel : Nat}
    {state : Mettapedia.Languages.Metamath.SourceGSLTState.SourceState}
    {obligations : List TheoremObligation}
    (h : runSource files policy root fuel = .ok state obligations) :
    ∃ (tokens : List LocatedToken) (statements : List RawStatement),
      segmentStatements tokens = .ok statements ∧
        foldStatements
          Mettapedia.Languages.Metamath.SourceGSLTState.initialState
          statements = .ok (state, obligations) ∧
        ((∃ tree, Derives
            (lexicalizedLanguage sourceGrammar lexicalDeclarations
              (pipelineSource statements)) outerDatabaseSort
            (statements.flatMap RawStatement.tokenStrings) tree) ↔
          ∃ ss : List RawStatement,
            statements.flatMap RawStatement.tokenStrings =
                ss.flatMap RawStatement.tokenStrings ∧
              NestSeq true ss ∧
              ReflectFacts (pipelineSource statements) ss) := by
  obtain ⟨spans, tokens, statements, hexp, hres, hseg, hfold,
    hcomplete⟩ := runSource_ok_inv h
  exact ⟨tokens, statements, hseg, hfold,
    derivation_correspondence (statements_no_include hseg)
      (statements_byteClean hseg)⟩

/-! ## Kernel fixtures for the new joints -/

private def fSpan :
    Mettapedia.Languages.Metamath.SourceGSLTRawByteLexical.LocatedByteSpan :=
  ⟨"f", 0, 0⟩

/-- `$c wff $. ax $a wff $.` as a segmented stream. -/
private def axFixtureStatements : List RawStatement :=
  [.constDecl fSpan [⟨fSpan, "wff"⟩] fSpan,
   .axiomatic fSpan ⟨fSpan, "ax"⟩ ⟨fSpan, "wff"⟩ [] fSpan]

/-- Positive: the classification of the fixture stream, computed. -/
theorem axFixture_tokens :
    pipelineTokens axFixtureStatements =
      [keywordToken "$c", classifiedName "mm-symbol" ⟨fSpan, "wff"⟩,
        keywordToken "$.", classifiedName "mm-label" ⟨fSpan, "ax"⟩,
        keywordToken "$a", classifiedName "mm-symbol" ⟨fSpan, "wff"⟩,
        keywordToken "$."] := rfl

/-- Positive: the fixture stream derives the outer database sort in
its own lexicalization, leaf coverage self-supplied. -/
theorem axFixture_derives :
    ∃ tree, Derives
      (lexicalizedLanguage sourceGrammar lexicalDeclarations
        (pipelineSource axFixtureStatements)) outerDatabaseSort
      (axFixtureStatements.flatMap RawStatement.tokenStrings) tree := by
  have hnest : NestSeq true axFixtureStatements :=
    NestSeq.atom true _ _ rfl (fun _ => rfl)
      (NestSeq.atom true _ _ rfl (fun hc => nomatch hc)
        (NestSeq.nil true))
  exact nestSeq_derives
    (fun r hr => baseRule_mem_lexicalized sourceGrammar
      lexicalDeclarations (pipelineSource axFixtureStatements) hr)
    hnest
    (fun s hs => ⟨pipelineSource_statementLeaves _ s hs, by
      rcases List.mem_cons.mp hs with rfl | hs
      · exact List.cons_ne_nil _ _
      rcases List.mem_singleton.mp hs with rfl
      trivial⟩)

/-- Negative: keywords carry no lexical class, hence no leaf rule. -/
theorem keyword_no_leaf :
    lexicalSort? lexicalDeclarations (keywordToken "$c") = none := rfl

/-- Negative: keyword spellings fail the label charset — the
classification cannot launder a keyword into a name. -/
theorem keyword_not_labelToken :
    labelBytesValid (stringBytes "$c") = false := by decide

/-- Negative: the include opener fails every lexical charset, so no
classified name of an accepted stream can spell it. -/
theorem include_opener_unclassifiable :
    mathBytesValid (stringBytes "$[") = false ∧
      labelBytesValid (stringBytes "$[") = false ∧
      compressedWordValid (stringBytes "$[") = false := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end Mettapedia.Languages.Metamath.SourceGSLTLexicalClosure
