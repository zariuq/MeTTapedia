import Mettapedia.GSLT.LanguageDef.InferenceChecker
import Mettapedia.GSLT.LanguageDef.CalculusLanguageDef

/-!
# PeTTa typecheck-v2 determinism and effect system as a rooted GSLT (stage 1)

Companion to `TypeSystemGSLT.lean`: the determinism/effect half of PeTTa's
`typecheck-v2` branch (reference revision `e038e4d`, repository
`trueagi-io/PeTTa`) as one `CalculusLanguageDef` — mode atoms, the analysis-verdict
lattice, effect join, overload aggregation, clause-head overlap,
closed-domain exhaustiveness, and the syntax-directed body walker.  The
generic V2 checker contains no branch for this fixture; every acceptance
and rejection below is decided by the definition data alone.

Provenance discipline: each rule's doc-comment cites the reference clause it
was extracted from (paths relative to the reference repository at the pinned
revision).  The prose companion is CeTTa's `docs/petta_type_system_spec.md`
section 7.

Stage-1 scope notes (deliberate, tracked deltas — not oversights):
- Analysis verdicts carry diagnostic reason payloads in the reference
  (`may_fail(R)` etc., `det_analysis.pl:294-321`); the lattice order does
  not depend on them, so verdicts are atoms here.
- The literal-`(cut)` overlap escape (`det_validate.pl:232-240`), the
  builtin-table override at call sites (`det_builtins.pl:74-89`), the
  recursive-edge det resolution (`det_proofs.pl:916-920`), and the boundness
  provisos that compile to runtime checks (`translator.pl:200-219`) are
  call-site environment, recorded in the spec document, not rules here.
- One canonical effect variable models `-[$e]->` (the chainer corpus uses a
  single effect variable); named multi-variable effect rows are stage 1.1.
- Exhaustiveness is presented at the closed Bool key domain; the
  infinite-domain literal case (Number/String, `det_analysis.pl:719-748`)
  is stage 1.1.  The judgment is deliberately asymmetric: derivability
  means COVERED; the reference errors only on provable incompleteness and
  stays silent otherwise (open-world nominal types), so no rule concludes a
  negative — rejection is non-derivability of coverage on a closed domain.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTDeterminism

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceExtension
open Mettapedia.GSLT.LanguageDef

/-- Single carrier sort: modes, verdicts, clause heads, and bodies live in
one abstract term algebra, exactly as the reference manipulates them as
untyped Prolog terms. -/
private def termType : TypeDecl := TypeDecl.plain "DtTerm"

private def termConstructor (head : String) (arity : Nat) : GrammarRule :=
  { label := head
    category := "DtTerm"
    params := (List.range arity).map fun index =>
      .simple s!"argument{index}" (.base "DtTerm")
    syntaxPattern := [] }

/-! ## Mode atoms (`flags_arrows.pl:72-92`) -/

/-- Uncommitted arrow `->`. -/
private def mPlain : Pattern := .apply "MPlain" []
private def mDet : Pattern := .apply "MDet" []
private def mSemidet : Pattern := .apply "MSemidet" []
private def mNondet : Pattern := .apply "MNondet" []
/-- No declaration and no builtin row: never assumed det
(`det_proofs.pl:23-45`). -/
private def mUnspecified : Pattern := .apply "MUnspecified" []
/-- The effect variable of `-[$e]->` (`flags_arrows.pl:85-92`). -/
private def mEffectVar : Pattern := .apply "MEffectVar" []

/-! ## Analysis verdicts (`det_analysis.pl:294-321`) -/

private def verOk : Pattern := .apply "VerOk" []
private def verMayFail : Pattern := .apply "VerMayFail" []
private def verNondet : Pattern := .apply "VerNondet" []
private def verUnknown : Pattern := .apply "VerUnknown" []

/-! ## Clause-head skeletons (overlap and exhaustiveness carriers) -/

/-- A variable argument position. -/
private def hVarHead : Pattern := .apply "HVarHead" []
/-- The two Bool pattern keys (closed key domain,
`det_analysis.pl:660-676`). -/
private def hTrue : Pattern := .apply "HTrue" []
private def hFalse : Pattern := .apply "HFalse" []
private def hPair (a b : Pattern) : Pattern := .apply "HPair" [a, b]

/-! ## Body skeletons (`det_proofs.pl:1031-1162`).  One witness constructor
per walker class; the doc-comment on each rule lists the family. -/

private def bCollapse : Pattern := .apply "BCollapse" []
private def bSuperpose : Pattern := .apply "BSuperpose" []
private def bEval : Pattern := .apply "BEval" []
private def bOnce (b : Pattern) : Pattern := .apply "BOnce" [b]
private def bSeq (a b : Pattern) : Pattern := .apply "BSeq" [a, b]
private def bCall (m : Pattern) : Pattern := .apply "BCall" [m]

/-! ## Lists -/

private def dNil : Pattern := .apply "DNil" []
private def dCons (head tail : Pattern) : Pattern := .apply "DCons" [head, tail]

/-! ## Judgment applications -/

private def modeLe (a b : Pattern) : Pattern := .apply "ModeLe" [a, b]
private def committed (m : Pattern) : Pattern := .apply "Committed" [m]
private def effectJoin (a b c : Pattern) : Pattern :=
  .apply "EffectJoin" [a, b, c]
private def modeInstance (a b : Pattern) : Pattern :=
  .apply "ModeInstance" [a, b]
private def overloadAgg (a b c : Pattern) : Pattern :=
  .apply "OverloadAgg" [a, b, c]
private def conflictingDecls (a b : Pattern) : Pattern :=
  .apply "ConflictingDecls" [a, b]
private def verdictLe (a b : Pattern) : Pattern := .apply "VerdictLe" [a, b]
private def verdictJoin (a b c : Pattern) : Pattern :=
  .apply "VerdictJoin" [a, b, c]
private def modeVerdict (m v : Pattern) : Pattern :=
  .apply "ModeVerdict" [m, v]
private def bodyVerdict (b v : Pattern) : Pattern :=
  .apply "BodyVerdict" [b, v]
private def clauseSetMode (v m : Pattern) : Pattern :=
  .apply "ClauseSetMode" [v, m]
private def arrowAdmits (d v : Pattern) : Pattern :=
  .apply "ArrowAdmits" [d, v]
private def overlapHeads (a b : Pattern) : Pattern :=
  .apply "OverlapHeads" [a, b]
private def covers (hs k : Pattern) : Pattern := .apply "Covers" [hs, k]
private def exhaustiveBool (hs : Pattern) : Pattern :=
  .apply "ExhaustiveBool" [hs]

private def ruleId (value : String) : RuleId := ⟨value⟩

/-! ## Commitment order on modes.  `det < semidet < nondet` is the
weakening direction: a body certified at mode `m` satisfies any declared
arrow at or above `m`. -/

private def modeLeRefl : RuleSchema :=
  { id := ruleId "mode-le-refl"
    metavariables := [("m", 0)]
    premises := []
    conclusion := modeLe (.fvar "m") (.fvar "m") }

private def modeLeDetSemidet : RuleSchema :=
  { id := ruleId "mode-le-det-semidet"
    metavariables := []
    premises := []
    conclusion := modeLe mDet mSemidet }

private def modeLeSemidetNondet : RuleSchema :=
  { id := ruleId "mode-le-semidet-nondet"
    metavariables := []
    premises := []
    conclusion := modeLe mSemidet mNondet }

private def modeLeDetNondet : RuleSchema :=
  { id := ruleId "mode-le-det-nondet"
    metavariables := []
    premises := []
    conclusion := modeLe mDet mNondet }

/-! ## Commitment (`flags_arrows.pl:115-116`): det and semidet keep the
clause-entry cut; semidet merely adds the right to fail. -/

private def committedDet : RuleSchema :=
  { id := ruleId "committed-det"
    metavariables := []
    premises := []
    conclusion := committed mDet }

private def committedSemidet : RuleSchema :=
  { id := ruleId "committed-semidet"
    metavariables := []
    premises := []
    conclusion := committed mSemidet }

/-! ## Effect join (`det_analysis.pl:158-164`, `det_proofs.pl:66-72`):
`unspecified` absorbs; otherwise the join moves toward the weaker
commitment. -/

private def effectJoinUnspecLeft : RuleSchema :=
  { id := ruleId "effect-join-unspec-left"
    metavariables := [("m", 0)]
    premises := []
    conclusion := effectJoin mUnspecified (.fvar "m") mUnspecified }

private def effectJoinUnspecRight : RuleSchema :=
  { id := ruleId "effect-join-unspec-right"
    metavariables := [("m", 0)]
    premises := []
    conclusion := effectJoin (.fvar "m") mUnspecified mUnspecified }

private def effectJoinLeft : RuleSchema :=
  { id := ruleId "effect-join-left"
    metavariables := [("a", 0), ("b", 0)]
    premises := [modeLe (.fvar "a") (.fvar "b")]
    conclusion := effectJoin (.fvar "a") (.fvar "b") (.fvar "b") }

private def effectJoinRight : RuleSchema :=
  { id := ruleId "effect-join-right"
    metavariables := [("a", 0), ("b", 0)]
    premises := [modeLe (.fvar "b") (.fvar "a")]
    conclusion := effectJoin (.fvar "a") (.fvar "b") (.fvar "a") }

/-! ## Effect-polymorphic instantiation (`det_proofs.pl:23-45`, priority
step 2): an effect variable instantiates to any concrete mode. -/

private def modeInstanceVar : RuleSchema :=
  { id := ruleId "mode-instance-var"
    metavariables := [("m", 0)]
    premises := []
    conclusion := modeInstance mEffectVar (.fvar "m") }

private def modeInstanceRefl : RuleSchema :=
  { id := ruleId "mode-instance-refl"
    metavariables := [("m", 0)]
    premises := []
    conclusion := modeInstance (.fvar "m") (.fvar "m") }

/-! ## Overload aggregation (`det_validate.pl:22`): the declared tops of an
overload set aggregate to the weakest committed member;
`{det, semidet} -> semidet`.  Mixing committed with `nondet` never
aggregates — it is the hard error `conflicting_determinism_declarations`
(the `ConflictingDecls` judgment below). -/

private def overloadAggRefl : RuleSchema :=
  { id := ruleId "overload-agg-refl"
    metavariables := [("m", 0)]
    premises := []
    conclusion := overloadAgg (.fvar "m") (.fvar "m") (.fvar "m") }

private def overloadAggDetSemidet : RuleSchema :=
  { id := ruleId "overload-agg-det-semidet"
    metavariables := []
    premises := []
    conclusion := overloadAgg mDet mSemidet mSemidet }

private def overloadAggSemidetDet : RuleSchema :=
  { id := ruleId "overload-agg-semidet-det"
    metavariables := []
    premises := []
    conclusion := overloadAgg mSemidet mDet mSemidet }

/-- `conflicting_determinism_declarations` (`det_validate.pl:22`,
error side). -/
private def conflictCommittedNondetRight : RuleSchema :=
  { id := ruleId "conflict-committed-nondet-right"
    metavariables := [("m", 0)]
    premises := [committed (.fvar "m")]
    conclusion := conflictingDecls (.fvar "m") mNondet }

private def conflictCommittedNondetLeft : RuleSchema :=
  { id := ruleId "conflict-committed-nondet-left"
    metavariables := [("m", 0)]
    premises := [committed (.fvar "m")]
    conclusion := conflictingDecls mNondet (.fvar "m") }

/-! ## Verdict lattice (`det_analysis.pl:294-321`):
`ok < may_fail < nondeterministic | unknown`; the two rank-2 verdicts are
final and mutually incomparable (the analysis short-circuits at rank 2,
so their join is never demanded). -/

private def verdictLeRefl : RuleSchema :=
  { id := ruleId "verdict-le-refl"
    metavariables := [("v", 0)]
    premises := []
    conclusion := verdictLe (.fvar "v") (.fvar "v") }

private def verdictLeOkMayFail : RuleSchema :=
  { id := ruleId "verdict-le-ok-may-fail"
    metavariables := []
    premises := []
    conclusion := verdictLe verOk verMayFail }

private def verdictLeMayFailNondet : RuleSchema :=
  { id := ruleId "verdict-le-may-fail-nondet"
    metavariables := []
    premises := []
    conclusion := verdictLe verMayFail verNondet }

private def verdictLeOkNondet : RuleSchema :=
  { id := ruleId "verdict-le-ok-nondet"
    metavariables := []
    premises := []
    conclusion := verdictLe verOk verNondet }

private def verdictLeMayFailUnknown : RuleSchema :=
  { id := ruleId "verdict-le-may-fail-unknown"
    metavariables := []
    premises := []
    conclusion := verdictLe verMayFail verUnknown }

private def verdictLeOkUnknown : RuleSchema :=
  { id := ruleId "verdict-le-ok-unknown"
    metavariables := []
    premises := []
    conclusion := verdictLe verOk verUnknown }

private def verdictJoinLeft : RuleSchema :=
  { id := ruleId "verdict-join-left"
    metavariables := [("a", 0), ("b", 0)]
    premises := [verdictLe (.fvar "a") (.fvar "b")]
    conclusion := verdictJoin (.fvar "a") (.fvar "b") (.fvar "b") }

private def verdictJoinRight : RuleSchema :=
  { id := ruleId "verdict-join-right"
    metavariables := [("a", 0), ("b", 0)]
    premises := [verdictLe (.fvar "b") (.fvar "a")]
    conclusion := verdictJoin (.fvar "a") (.fvar "b") (.fvar "a") }

/-! ## Mode-to-verdict at call sites (`det_proofs.pl:23-45`).  A plain
arrow contributes `unknown` — unlisted callees are `unspecified` and never
assumed det. -/

private def modeVerdictDet : RuleSchema :=
  { id := ruleId "mode-verdict-det"
    metavariables := []
    premises := []
    conclusion := modeVerdict mDet verOk }

private def modeVerdictSemidet : RuleSchema :=
  { id := ruleId "mode-verdict-semidet"
    metavariables := []
    premises := []
    conclusion := modeVerdict mSemidet verMayFail }

private def modeVerdictNondet : RuleSchema :=
  { id := ruleId "mode-verdict-nondet"
    metavariables := []
    premises := []
    conclusion := modeVerdict mNondet verNondet }

private def modeVerdictPlain : RuleSchema :=
  { id := ruleId "mode-verdict-plain"
    metavariables := []
    premises := []
    conclusion := modeVerdict mPlain verUnknown }

/-! ## Body walker (`det_proofs.pl:1031-1162`) -/

/-- `collapse`/`quote`/`forall`/`foldall` class: always `ok`. -/
private def bodyCollapse : RuleSchema :=
  { id := ruleId "body-collapse"
    metavariables := []
    premises := []
    conclusion := bodyVerdict bCollapse verOk }

/-- `superpose`/`match`/`hyperpose` class: `nondeterministic`. -/
private def bodySuperpose : RuleSchema :=
  { id := ruleId "body-superpose"
    metavariables := []
    premises := []
    conclusion := bodyVerdict bSuperpose verNondet }

/-- `eval`/`reduce` class: `unknown`. -/
private def bodyEval : RuleSchema :=
  { id := ruleId "body-eval"
    metavariables := []
    premises := []
    conclusion := bodyVerdict bEval verUnknown }

/-- `once` caps at `may_fail` (`det_proofs.pl:1094-1100`): an `ok` body
stays `ok`; every worse verdict caps to `may_fail` (one solution at most,
possibly none). -/
private def bodyOnceOk : RuleSchema :=
  { id := ruleId "body-once-ok"
    metavariables := [("b", 0)]
    premises := [bodyVerdict (.fvar "b") verOk]
    conclusion := bodyVerdict (bOnce (.fvar "b")) verOk }

private def bodyOnceMayFail : RuleSchema :=
  { id := ruleId "body-once-may-fail"
    metavariables := [("b", 0)]
    premises := [bodyVerdict (.fvar "b") verMayFail]
    conclusion := bodyVerdict (bOnce (.fvar "b")) verMayFail }

private def bodyOnceNondet : RuleSchema :=
  { id := ruleId "body-once-nondet"
    metavariables := [("b", 0)]
    premises := [bodyVerdict (.fvar "b") verNondet]
    conclusion := bodyVerdict (bOnce (.fvar "b")) verMayFail }

private def bodyOnceUnknown : RuleSchema :=
  { id := ruleId "body-once-unknown"
    metavariables := [("b", 0)]
    premises := [bodyVerdict (.fvar "b") verUnknown]
    conclusion := bodyVerdict (bOnce (.fvar "b")) verMayFail }

/-- Sequential composition takes the worst constituent verdict
(`det_proofs.pl:1031-1046`). -/
private def bodySeq : RuleSchema :=
  { id := ruleId "body-seq"
    metavariables := [("a", 0), ("b", 0), ("va", 0), ("vb", 0), ("v", 0)]
    premises :=
      [ bodyVerdict (.fvar "a") (.fvar "va"),
        bodyVerdict (.fvar "b") (.fvar "vb"),
        verdictJoin (.fvar "va") (.fvar "vb") (.fvar "v") ]
    conclusion := bodyVerdict (bSeq (.fvar "a") (.fvar "b")) (.fvar "v") }

/-- A call contributes its callee's mode verdict (`det_proofs.pl:23-45`). -/
private def bodyCall : RuleSchema :=
  { id := ruleId "body-call"
    metavariables := [("m", 0), ("v", 0)]
    premises := [modeVerdict (.fvar "m") (.fvar "v")]
    conclusion := bodyVerdict (bCall (.fvar "m")) (.fvar "v") }

/-! ## Clause-set certification (`det_proofs.pl:990-1010`): worst body
verdict; `may_fail` certifies semidet; `ok` certifies det.  `unknown`
certifies nothing — no rule, matching the reference's refusal to assume
det for what it cannot analyze. -/

private def clauseSetOkDet : RuleSchema :=
  { id := ruleId "clause-set-ok-det"
    metavariables := []
    premises := []
    conclusion := clauseSetMode verOk mDet }

private def clauseSetMayFailSemidet : RuleSchema :=
  { id := ruleId "clause-set-may-fail-semidet"
    metavariables := []
    premises := []
    conclusion := clauseSetMode verMayFail mSemidet }

private def clauseSetNondet : RuleSchema :=
  { id := ruleId "clause-set-nondet"
    metavariables := []
    premises := []
    conclusion := clauseSetMode verNondet mNondet }

/-- The acceptance capstone: a declared arrow admits a clause-set verdict
iff the certified mode is at or below the declaration in the commitment
order (`det_validate.pl:220-260`: bodies worse than the arrow allows are
rejected). -/
private def arrowAdmitsRule : RuleSchema :=
  { id := ruleId "arrow-admits"
    metavariables := [("d", 0), ("v", 0), ("m", 0)]
    premises :=
      [ clauseSetMode (.fvar "v") (.fvar "m"),
        modeLe (.fvar "m") (.fvar "d") ]
    conclusion := arrowAdmits (.fvar "d") (.fvar "v") }

/-! ## Clause-head overlap (`det_validate.pl:245`, enforced at 220):
unifiable-on-copies — a syntactic-unifiability test, not a normal-form
disjointness approximation.  Violation under commitment is
`overlapping_deterministic_clauses`. -/

private def overlapVarLeft : RuleSchema :=
  { id := ruleId "overlap-var-left"
    metavariables := [("h", 0)]
    premises := []
    conclusion := overlapHeads hVarHead (.fvar "h") }

private def overlapVarRight : RuleSchema :=
  { id := ruleId "overlap-var-right"
    metavariables := [("h", 0)]
    premises := []
    conclusion := overlapHeads (.fvar "h") hVarHead }

private def overlapEqual : RuleSchema :=
  { id := ruleId "overlap-equal"
    metavariables := [("h", 0)]
    premises := []
    conclusion := overlapHeads (.fvar "h") (.fvar "h") }

private def overlapPair : RuleSchema :=
  { id := ruleId "overlap-pair"
    metavariables := [("a", 0), ("b", 0), ("c", 0), ("d", 0)]
    premises :=
      [ overlapHeads (.fvar "a") (.fvar "c"),
        overlapHeads (.fvar "b") (.fvar "d") ]
    conclusion :=
      overlapHeads (hPair (.fvar "a") (.fvar "b"))
        (hPair (.fvar "c") (.fvar "d")) }

/-! ## Closed-domain exhaustiveness (`det_analysis.pl:618-817`), presented
at the Bool key domain.  Derivability = covered; the asymmetric error
(`det_nonexhaustive`) is exactly failure to derive coverage of some key of
a closed domain. -/

private def coversHereVar : RuleSchema :=
  { id := ruleId "covers-here-var"
    metavariables := [("hs", 0), ("k", 0)]
    premises := []
    conclusion := covers (dCons hVarHead (.fvar "hs")) (.fvar "k") }

private def coversHereMatch : RuleSchema :=
  { id := ruleId "covers-here-match"
    metavariables := [("k", 0), ("hs", 0)]
    premises := []
    conclusion := covers (dCons (.fvar "k") (.fvar "hs")) (.fvar "k") }

private def coversThere : RuleSchema :=
  { id := ruleId "covers-there"
    metavariables := [("h", 0), ("hs", 0), ("k", 0)]
    premises := [covers (.fvar "hs") (.fvar "k")]
    conclusion := covers (dCons (.fvar "h") (.fvar "hs")) (.fvar "k") }

private def exhaustiveBoolRule : RuleSchema :=
  { id := ruleId "exhaustive-bool"
    metavariables := [("hs", 0)]
    premises := [covers (.fvar "hs") hTrue, covers (.fvar "hs") hFalse]
    conclusion := exhaustiveBool (.fvar "hs") }

/-! ## The complete authored definition -/

private abbrev definition : CalculusLanguageDef :=
  { name := "petta-typecheck-v2-determinism"
    types := [termType]
    terms :=
      [ termConstructor "MPlain" 0,
        termConstructor "MDet" 0,
        termConstructor "MSemidet" 0,
        termConstructor "MNondet" 0,
        termConstructor "MUnspecified" 0,
        termConstructor "MEffectVar" 0,
        termConstructor "VerOk" 0,
        termConstructor "VerMayFail" 0,
        termConstructor "VerNondet" 0,
        termConstructor "VerUnknown" 0,
        termConstructor "HVarHead" 0,
        termConstructor "HTrue" 0,
        termConstructor "HFalse" 0,
        termConstructor "HPair" 2,
        termConstructor "BCollapse" 0,
        termConstructor "BSuperpose" 0,
        termConstructor "BEval" 0,
        termConstructor "BOnce" 1,
        termConstructor "BSeq" 2,
        termConstructor "BCall" 1,
        termConstructor "DNil" 0,
        termConstructor "DCons" 2 ]
    equations := []
    rewrites := []
    judgments :=
      [ { head := "ModeLe", arity := 2 },
        { head := "Committed", arity := 1 },
        { head := "EffectJoin", arity := 3 },
        { head := "ModeInstance", arity := 2 },
        { head := "OverloadAgg", arity := 3 },
        { head := "ConflictingDecls", arity := 2 },
        { head := "VerdictLe", arity := 2 },
        { head := "VerdictJoin", arity := 3 },
        { head := "ModeVerdict", arity := 2 },
        { head := "BodyVerdict", arity := 2 },
        { head := "ClauseSetMode", arity := 2 },
        { head := "ArrowAdmits", arity := 2 },
        { head := "OverlapHeads", arity := 2 },
        { head := "Covers", arity := 2 },
        { head := "ExhaustiveBool", arity := 1 } ]
    rules :=
      [ modeLeRefl, modeLeDetSemidet, modeLeSemidetNondet, modeLeDetNondet,
        committedDet, committedSemidet,
        effectJoinUnspecLeft, effectJoinUnspecRight,
        effectJoinLeft, effectJoinRight,
        modeInstanceVar, modeInstanceRefl,
        overloadAggRefl, overloadAggDetSemidet, overloadAggSemidetDet,
        conflictCommittedNondetRight, conflictCommittedNondetLeft,
        verdictLeRefl, verdictLeOkMayFail, verdictLeMayFailNondet,
        verdictLeOkNondet, verdictLeMayFailUnknown, verdictLeOkUnknown,
        verdictJoinLeft, verdictJoinRight,
        modeVerdictDet, modeVerdictSemidet, modeVerdictNondet,
        modeVerdictPlain,
        bodyCollapse, bodySuperpose, bodyEval,
        bodyOnceOk, bodyOnceMayFail, bodyOnceNondet, bodyOnceUnknown,
        bodySeq, bodyCall,
        clauseSetOkDet, clauseSetMayFailSemidet, clauseSetNondet,
        arrowAdmitsRule,
        overlapVarLeft, overlapVarRight, overlapEqual, overlapPair,
        coversHereVar, coversHereMatch, coversThere,
        exhaustiveBoolRule ] }

private def language : LanguageDef := definition.toLanguageDef
private def calculus : ProofCalculus := definition.toCalculus
/-! ## Receipts -/

theorem language_validate : language.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly language <;>
    simp [language, termType, termConstructor,
      LanguageDef.typeNames, TypeDecl.plain, TermParam.typeExpr,
      TypeExpr.baseNames]

theorem definition_valid : definition.isValid = true := by
  have hvalidate : definition.toLanguageDef.validate = [] := by
    simpa [definition, language] using language_validate
  unfold CalculusLanguageDef.isValid CalculusLanguageDef.hasValidLocalRules
  rw [hvalidate]
  simp [definition,
    CalculusLanguageDef.ruleIds, CalculusLanguageDef.judgmentSignatureValid,
    CalculusLanguageDef.judgmentHeads, CalculusLanguageDef.conversionDeclarationValid,
    CalculusLanguageDef.lookupJudgment?, RuleSchema.isValidIn,
    RuleSchema.isLocallyValid,
    RuleSchema.metavariableNames, RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    CalculusLanguageDef.judgmentSchemaValid, fixedConstructorsValid,
    fixedConstructorListsValid, languageHasConstructorArity,
    Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, Pattern.zipHead, Pattern.mapHead,
    Pattern.evalHead, termType, termConstructor,
    modeLeRefl, modeLeDetSemidet, modeLeSemidetNondet, modeLeDetNondet,
    committedDet, committedSemidet, effectJoinUnspecLeft,
    effectJoinUnspecRight, effectJoinLeft, effectJoinRight,
    modeInstanceVar, modeInstanceRefl, overloadAggRefl,
    overloadAggDetSemidet, overloadAggSemidetDet,
    conflictCommittedNondetRight, conflictCommittedNondetLeft,
    verdictLeRefl, verdictLeOkMayFail, verdictLeMayFailNondet,
    verdictLeOkNondet, verdictLeMayFailUnknown, verdictLeOkUnknown,
    verdictJoinLeft, verdictJoinRight, modeVerdictDet, modeVerdictSemidet,
    modeVerdictNondet, modeVerdictPlain, bodyCollapse, bodySuperpose,
    bodyEval, bodyOnceOk, bodyOnceMayFail, bodyOnceNondet,
    bodyOnceUnknown, bodySeq, bodyCall, clauseSetOkDet,
    clauseSetMayFailSemidet, clauseSetNondet, arrowAdmitsRule,
    overlapVarLeft, overlapVarRight, overlapEqual, overlapPair,
    coversHereVar, coversHereMatch, coversThere, exhaustiveBoolRule,
    modeLe, committed, effectJoin, modeInstance, overloadAgg,
    conflictingDecls, verdictLe, verdictJoin, modeVerdict, bodyVerdict,
    clauseSetMode, arrowAdmits, overlapHeads, covers, exhaustiveBool,
    mPlain, mDet, mSemidet, mNondet, mUnspecified, mEffectVar, verOk,
    verMayFail, verNondet, verUnknown, hVarHead, hTrue, hFalse, hPair,
    bCollapse, bSuperpose, bEval, bOnce, bSeq, bCall, dCons, ruleId]
  decide

/-- The determinism/effect language and its fifty rules as one GSLT. -/
def totalTheory : Mettapedia.GSLT.GSLT :=
  definition.toGSLTOfEquationFree definition_valid rfl

theorem totalTheory_Term : totalTheory.Term = (Pattern ⊕ List Pattern) := by
  unfold totalTheory CalculusLanguageDef.toGSLTOfEquationFree
  rfl

def checked : ValidatedCalculusLanguageDef := ⟨definition, definition_valid⟩

/-- Inventory pin: 22 constructors. -/
theorem language_constructor_count : language.terms.length = 22 := by decide

/-- Inventory pin: 50 inference rules. -/
theorem calculus_rule_count : calculus.rules.length = 50 := by decide

/-! ## Positive acceptance theorems -/

private def detNondetLeProof : RawProof :=
  .node { ruleId := ruleId "mode-le-det-nondet", arguments := [] } []

/-- The commitment order: det certifies under a nondet arrow. -/
theorem mode_le_det_nondet :
    checkRaw checked (modeLe mDet mNondet)
      detNondetLeProof = true := by
  simp [checkRaw, checkRawChildren, checked, definition,
    detNondetLeProof, modeLeRefl, modeLeDetSemidet, modeLeSemidetNondet,
    modeLeDetNondet, committedDet, committedSemidet, effectJoinUnspecLeft,
    effectJoinUnspecRight, effectJoinLeft, effectJoinRight,
    modeInstanceVar, modeInstanceRefl, overloadAggRefl,
    overloadAggDetSemidet, overloadAggSemidetDet,
    conflictCommittedNondetRight, conflictCommittedNondetLeft,
    verdictLeRefl, verdictLeOkMayFail, verdictLeMayFailNondet,
    verdictLeOkNondet, verdictLeMayFailUnknown, verdictLeOkUnknown,
    verdictJoinLeft, verdictJoinRight, modeVerdictDet, modeVerdictSemidet,
    modeVerdictNondet, modeVerdictPlain, bodyCollapse, bodySuperpose,
    bodyEval, bodyOnceOk, bodyOnceMayFail, bodyOnceNondet,
    bodyOnceUnknown, bodySeq, bodyCall, clauseSetOkDet,
    clauseSetMayFailSemidet, clauseSetNondet, arrowAdmitsRule,
    overlapVarLeft, overlapVarRight, overlapEqual, overlapPair,
    coversHereVar, coversHereMatch, coversThere, exhaustiveBoolRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    modeLe, committed, effectJoin, modeInstance,
    overloadAgg, conflictingDecls, verdictLe, verdictJoin, modeVerdict,
    bodyVerdict, clauseSetMode, arrowAdmits, overlapHeads, covers,
    exhaustiveBool, mPlain, mDet, mSemidet, mNondet, mUnspecified,
    mEffectVar, verOk, verMayFail, verNondet, verUnknown, hVarHead, hTrue,
    hFalse, hPair, bCollapse, bSuperpose, bEval, bOnce, bSeq, bCall,
    dCons, ruleId]

private def detSemidetLeProof : RawProof :=
  .node { ruleId := ruleId "mode-le-det-semidet", arguments := [] } []

private def joinDetSemidetProof : RawProof :=
  .node
    { ruleId := ruleId "effect-join-left", arguments := [mDet, mSemidet] }
    [detSemidetLeProof]

/-- Effect join moves toward the weaker commitment
(`det_analysis.pl:158-164`). -/
theorem effect_join_det_semidet :
    checkRaw checked (effectJoin mDet mSemidet mSemidet)
      joinDetSemidetProof = true := by
  simp [checkRaw, checkRawChildren, checked, definition,
    joinDetSemidetProof, detSemidetLeProof, modeLeRefl, modeLeDetSemidet,
    modeLeSemidetNondet, modeLeDetNondet, committedDet, committedSemidet,
    effectJoinUnspecLeft, effectJoinUnspecRight, effectJoinLeft,
    effectJoinRight, modeInstanceVar, modeInstanceRefl, overloadAggRefl,
    overloadAggDetSemidet, overloadAggSemidetDet,
    conflictCommittedNondetRight, conflictCommittedNondetLeft,
    verdictLeRefl, verdictLeOkMayFail, verdictLeMayFailNondet,
    verdictLeOkNondet, verdictLeMayFailUnknown, verdictLeOkUnknown,
    verdictJoinLeft, verdictJoinRight, modeVerdictDet, modeVerdictSemidet,
    modeVerdictNondet, modeVerdictPlain, bodyCollapse, bodySuperpose,
    bodyEval, bodyOnceOk, bodyOnceMayFail, bodyOnceNondet,
    bodyOnceUnknown, bodySeq, bodyCall, clauseSetOkDet,
    clauseSetMayFailSemidet, clauseSetNondet, arrowAdmitsRule,
    overlapVarLeft, overlapVarRight, overlapEqual, overlapPair,
    coversHereVar, coversHereMatch, coversThere, exhaustiveBoolRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, modeLe, committed, effectJoin, modeInstance,
    overloadAgg, conflictingDecls, verdictLe, verdictJoin, modeVerdict,
    bodyVerdict, clauseSetMode, arrowAdmits, overlapHeads, covers,
    exhaustiveBool, mPlain, mDet, mSemidet, mNondet, mUnspecified,
    mEffectVar, verOk, verMayFail, verNondet, verUnknown, hVarHead, hTrue,
    hFalse, hPair, bCollapse, bSuperpose, bEval, bOnce, bSeq, bCall,
    dCons, ruleId, Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

private def joinUnspecProof : RawProof :=
  .node
    { ruleId := ruleId "effect-join-unspec-left", arguments := [mDet] } []

/-- `unspecified` absorbs in the effect join (`det_proofs.pl:66-72`). -/
theorem effect_join_unspecified_absorbs :
    checkRaw checked (effectJoin mUnspecified mDet mUnspecified)
      joinUnspecProof = true := by
  simp [checkRaw, checkRawChildren, checked, definition,
    joinUnspecProof, modeLeRefl, modeLeDetSemidet, modeLeSemidetNondet,
    modeLeDetNondet, committedDet, committedSemidet, effectJoinUnspecLeft,
    effectJoinUnspecRight, effectJoinLeft, effectJoinRight,
    modeInstanceVar, modeInstanceRefl, overloadAggRefl,
    overloadAggDetSemidet, overloadAggSemidetDet,
    conflictCommittedNondetRight, conflictCommittedNondetLeft,
    verdictLeRefl, verdictLeOkMayFail, verdictLeMayFailNondet,
    verdictLeOkNondet, verdictLeMayFailUnknown, verdictLeOkUnknown,
    verdictJoinLeft, verdictJoinRight, modeVerdictDet, modeVerdictSemidet,
    modeVerdictNondet, modeVerdictPlain, bodyCollapse, bodySuperpose,
    bodyEval, bodyOnceOk, bodyOnceMayFail, bodyOnceNondet,
    bodyOnceUnknown, bodySeq, bodyCall, clauseSetOkDet,
    clauseSetMayFailSemidet, clauseSetNondet, arrowAdmitsRule,
    overlapVarLeft, overlapVarRight, overlapEqual, overlapPair,
    coversHereVar, coversHereMatch, coversThere, exhaustiveBoolRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, modeLe, committed, effectJoin, modeInstance,
    overloadAgg, conflictingDecls, verdictLe, verdictJoin, modeVerdict,
    bodyVerdict, clauseSetMode, arrowAdmits, overlapHeads, covers,
    exhaustiveBool, mPlain, mDet, mSemidet, mNondet, mUnspecified,
    mEffectVar, verOk, verMayFail, verNondet, verUnknown, hVarHead, hTrue,
    hFalse, hPair, bCollapse, bSuperpose, bEval, bOnce, bSeq, bCall,
    dCons, ruleId, Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

private def effectVarProof : RawProof :=
  .node { ruleId := ruleId "mode-instance-var", arguments := [mDet] } []

/-- Effect polymorphism: `-[$e]->` instantiates to a concrete mode
(`det_proofs.pl:23-45`). -/
theorem effect_var_instantiates_to_det :
    checkRaw checked (modeInstance mEffectVar mDet)
      effectVarProof = true := by
  simp [checkRaw, checkRawChildren, checked, definition,
    effectVarProof, modeLeRefl, modeLeDetSemidet, modeLeSemidetNondet,
    modeLeDetNondet, committedDet, committedSemidet, effectJoinUnspecLeft,
    effectJoinUnspecRight, effectJoinLeft, effectJoinRight,
    modeInstanceVar, modeInstanceRefl, overloadAggRefl,
    overloadAggDetSemidet, overloadAggSemidetDet,
    conflictCommittedNondetRight, conflictCommittedNondetLeft,
    verdictLeRefl, verdictLeOkMayFail, verdictLeMayFailNondet,
    verdictLeOkNondet, verdictLeMayFailUnknown, verdictLeOkUnknown,
    verdictJoinLeft, verdictJoinRight, modeVerdictDet, modeVerdictSemidet,
    modeVerdictNondet, modeVerdictPlain, bodyCollapse, bodySuperpose,
    bodyEval, bodyOnceOk, bodyOnceMayFail, bodyOnceNondet,
    bodyOnceUnknown, bodySeq, bodyCall, clauseSetOkDet,
    clauseSetMayFailSemidet, clauseSetNondet, arrowAdmitsRule,
    overlapVarLeft, overlapVarRight, overlapEqual, overlapPair,
    coversHereVar, coversHereMatch, coversThere, exhaustiveBoolRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, modeLe, committed, effectJoin, modeInstance,
    overloadAgg, conflictingDecls, verdictLe, verdictJoin, modeVerdict,
    bodyVerdict, clauseSetMode, arrowAdmits, overlapHeads, covers,
    exhaustiveBool, mPlain, mDet, mSemidet, mNondet, mUnspecified,
    mEffectVar, verOk, verMayFail, verNondet, verUnknown, hVarHead, hTrue,
    hFalse, hPair, bCollapse, bSuperpose, bEval, bOnce, bSeq, bCall,
    dCons, ruleId, Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

private def overloadWeakenProof : RawProof :=
  .node
    { ruleId := ruleId "overload-agg-det-semidet", arguments := [] } []

/-- Overload aggregation weakens to the weakest committed top:
`{det, semidet} -> semidet` (`det_validate.pl:22`). -/
theorem overload_det_semidet_weakens :
    checkRaw checked (overloadAgg mDet mSemidet mSemidet)
      overloadWeakenProof = true := by
  simp [checkRaw, checkRawChildren, checked, definition,
    overloadWeakenProof, modeLeRefl, modeLeDetSemidet,
    modeLeSemidetNondet, modeLeDetNondet, committedDet, committedSemidet,
    effectJoinUnspecLeft, effectJoinUnspecRight, effectJoinLeft,
    effectJoinRight, modeInstanceVar, modeInstanceRefl, overloadAggRefl,
    overloadAggDetSemidet, overloadAggSemidetDet,
    conflictCommittedNondetRight, conflictCommittedNondetLeft,
    verdictLeRefl, verdictLeOkMayFail, verdictLeMayFailNondet,
    verdictLeOkNondet, verdictLeMayFailUnknown, verdictLeOkUnknown,
    verdictJoinLeft, verdictJoinRight, modeVerdictDet, modeVerdictSemidet,
    modeVerdictNondet, modeVerdictPlain, bodyCollapse, bodySuperpose,
    bodyEval, bodyOnceOk, bodyOnceMayFail, bodyOnceNondet,
    bodyOnceUnknown, bodySeq, bodyCall, clauseSetOkDet,
    clauseSetMayFailSemidet, clauseSetNondet, arrowAdmitsRule,
    overlapVarLeft, overlapVarRight, overlapEqual, overlapPair,
    coversHereVar, coversHereMatch, coversThere, exhaustiveBoolRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    modeLe, committed, effectJoin, modeInstance,
    overloadAgg, conflictingDecls, verdictLe, verdictJoin, modeVerdict,
    bodyVerdict, clauseSetMode, arrowAdmits, overlapHeads, covers,
    exhaustiveBool, mPlain, mDet, mSemidet, mNondet, mUnspecified,
    mEffectVar, verOk, verMayFail, verNondet, verUnknown, hVarHead, hTrue,
    hFalse, hPair, bCollapse, bSuperpose, bEval, bOnce, bSeq, bCall,
    dCons, ruleId]

private def committedDetProof : RawProof :=
  .node { ruleId := ruleId "committed-det", arguments := [] } []

private def conflictProof : RawProof :=
  .node
    { ruleId := ruleId "conflict-committed-nondet-right"
      arguments := [mDet] }
    [committedDetProof]

/-- Mixing a committed declaration with `nondet` is the hard error
`conflicting_determinism_declarations` (`det_validate.pl:22`). -/
theorem conflicting_declarations_det_nondet :
    checkRaw checked (conflictingDecls mDet mNondet)
      conflictProof = true := by
  simp [checkRaw, checkRawChildren, checked, definition,
    conflictProof, committedDetProof, modeLeRefl, modeLeDetSemidet,
    modeLeSemidetNondet, modeLeDetNondet, committedDet, committedSemidet,
    effectJoinUnspecLeft, effectJoinUnspecRight, effectJoinLeft,
    effectJoinRight, modeInstanceVar, modeInstanceRefl, overloadAggRefl,
    overloadAggDetSemidet, overloadAggSemidetDet,
    conflictCommittedNondetRight, conflictCommittedNondetLeft,
    verdictLeRefl, verdictLeOkMayFail, verdictLeMayFailNondet,
    verdictLeOkNondet, verdictLeMayFailUnknown, verdictLeOkUnknown,
    verdictJoinLeft, verdictJoinRight, modeVerdictDet, modeVerdictSemidet,
    modeVerdictNondet, modeVerdictPlain, bodyCollapse, bodySuperpose,
    bodyEval, bodyOnceOk, bodyOnceMayFail, bodyOnceNondet,
    bodyOnceUnknown, bodySeq, bodyCall, clauseSetOkDet,
    clauseSetMayFailSemidet, clauseSetNondet, arrowAdmitsRule,
    overlapVarLeft, overlapVarRight, overlapEqual, overlapPair,
    coversHereVar, coversHereMatch, coversThere, exhaustiveBoolRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, modeLe, committed, effectJoin, modeInstance,
    overloadAgg, conflictingDecls, verdictLe, verdictJoin, modeVerdict,
    bodyVerdict, clauseSetMode, arrowAdmits, overlapHeads, covers,
    exhaustiveBool, mPlain, mDet, mSemidet, mNondet, mUnspecified,
    mEffectVar, verOk, verMayFail, verNondet, verUnknown, hVarHead, hTrue,
    hFalse, hPair, bCollapse, bSuperpose, bEval, bOnce, bSeq, bCall,
    dCons, ruleId, Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

private def collapseOkProof : RawProof :=
  .node { ruleId := ruleId "body-collapse", arguments := [] } []

private def superposeNondetProof : RawProof :=
  .node { ruleId := ruleId "body-superpose", arguments := [] } []

private def okNondetLeProof : RawProof :=
  .node { ruleId := ruleId "verdict-le-ok-nondet", arguments := [] } []

private def okNondetJoinProof : RawProof :=
  .node
    { ruleId := ruleId "verdict-join-left"
      arguments := [verOk, verNondet] }
    [okNondetLeProof]

private def seqBodyProof : RawProof :=
  .node
    { ruleId := ruleId "body-seq"
      arguments := [bCollapse, bSuperpose, verOk, verNondet, verNondet] }
    [collapseOkProof, superposeNondetProof, okNondetJoinProof]

/-- Composition takes the worst constituent: an `ok` step followed by a
`superpose` step is `nondeterministic` (`det_proofs.pl:1031-1046`). -/
theorem body_composition_superpose_nondet :
    checkRaw checked (bodyVerdict (bSeq bCollapse bSuperpose) verNondet)
      seqBodyProof = true := by
  simp [checkRaw, checkRawChildren, checked, definition,
    seqBodyProof, collapseOkProof, superposeNondetProof,
    okNondetJoinProof, okNondetLeProof, modeLeRefl, modeLeDetSemidet,
    modeLeSemidetNondet, modeLeDetNondet, committedDet, committedSemidet,
    effectJoinUnspecLeft, effectJoinUnspecRight, effectJoinLeft,
    effectJoinRight, modeInstanceVar, modeInstanceRefl, overloadAggRefl,
    overloadAggDetSemidet, overloadAggSemidetDet,
    conflictCommittedNondetRight, conflictCommittedNondetLeft,
    verdictLeRefl, verdictLeOkMayFail, verdictLeMayFailNondet,
    verdictLeOkNondet, verdictLeMayFailUnknown, verdictLeOkUnknown,
    verdictJoinLeft, verdictJoinRight, modeVerdictDet, modeVerdictSemidet,
    modeVerdictNondet, modeVerdictPlain, bodyCollapse, bodySuperpose,
    bodyEval, bodyOnceOk, bodyOnceMayFail, bodyOnceNondet,
    bodyOnceUnknown, bodySeq, bodyCall, clauseSetOkDet,
    clauseSetMayFailSemidet, clauseSetNondet, arrowAdmitsRule,
    overlapVarLeft, overlapVarRight, overlapEqual, overlapPair,
    coversHereVar, coversHereMatch, coversThere, exhaustiveBoolRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, modeLe, committed, effectJoin, modeInstance,
    overloadAgg, conflictingDecls, verdictLe, verdictJoin, modeVerdict,
    bodyVerdict, clauseSetMode, arrowAdmits, overlapHeads, covers,
    exhaustiveBool, mPlain, mDet, mSemidet, mNondet, mUnspecified,
    mEffectVar, verOk, verMayFail, verNondet, verUnknown, hVarHead, hTrue,
    hFalse, hPair, bCollapse, bSuperpose, bEval, bOnce, bSeq, bCall,
    dCons, ruleId, Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

private def onceCapProof : RawProof :=
  .node
    { ruleId := ruleId "body-once-nondet", arguments := [bSuperpose] }
    [superposeNondetProof]

/-- `once` caps a nondeterministic body at `may_fail`
(`det_proofs.pl:1094-1100`). -/
theorem once_caps_nondet_to_may_fail :
    checkRaw checked (bodyVerdict (bOnce bSuperpose) verMayFail)
      onceCapProof = true := by
  simp [checkRaw, checkRawChildren, checked, definition,
    onceCapProof, superposeNondetProof, modeLeRefl, modeLeDetSemidet,
    modeLeSemidetNondet, modeLeDetNondet, committedDet, committedSemidet,
    effectJoinUnspecLeft, effectJoinUnspecRight, effectJoinLeft,
    effectJoinRight, modeInstanceVar, modeInstanceRefl, overloadAggRefl,
    overloadAggDetSemidet, overloadAggSemidetDet,
    conflictCommittedNondetRight, conflictCommittedNondetLeft,
    verdictLeRefl, verdictLeOkMayFail, verdictLeMayFailNondet,
    verdictLeOkNondet, verdictLeMayFailUnknown, verdictLeOkUnknown,
    verdictJoinLeft, verdictJoinRight, modeVerdictDet, modeVerdictSemidet,
    modeVerdictNondet, modeVerdictPlain, bodyCollapse, bodySuperpose,
    bodyEval, bodyOnceOk, bodyOnceMayFail, bodyOnceNondet,
    bodyOnceUnknown, bodySeq, bodyCall, clauseSetOkDet,
    clauseSetMayFailSemidet, clauseSetNondet, arrowAdmitsRule,
    overlapVarLeft, overlapVarRight, overlapEqual, overlapPair,
    coversHereVar, coversHereMatch, coversThere, exhaustiveBoolRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, modeLe, committed, effectJoin, modeInstance,
    overloadAgg, conflictingDecls, verdictLe, verdictJoin, modeVerdict,
    bodyVerdict, clauseSetMode, arrowAdmits, overlapHeads, covers,
    exhaustiveBool, mPlain, mDet, mSemidet, mNondet, mUnspecified,
    mEffectVar, verOk, verMayFail, verNondet, verUnknown, hVarHead, hTrue,
    hFalse, hPair, bCollapse, bSuperpose, bEval, bOnce, bSeq, bCall,
    dCons, ruleId, Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

private def clauseSetDetProof : RawProof :=
  .node { ruleId := ruleId "clause-set-ok-det", arguments := [] } []

private def detReflLeProof : RawProof :=
  .node { ruleId := ruleId "mode-le-refl", arguments := [mDet] } []

private def detAdmitsProof : RawProof :=
  .node
    { ruleId := ruleId "arrow-admits"
      arguments := [mDet, verOk, mDet] }
    [clauseSetDetProof, detReflLeProof]

/-- An `ok` clause set certifies det and satisfies a `-[det]->`
declaration (`det_proofs.pl:990-1010`). -/
theorem det_body_admits_det_arrow :
    checkRaw checked (arrowAdmits mDet verOk)
      detAdmitsProof = true := by
  simp [checkRaw, checkRawChildren, checked, definition,
    detAdmitsProof, clauseSetDetProof, detReflLeProof, modeLeRefl,
    modeLeDetSemidet, modeLeSemidetNondet, modeLeDetNondet, committedDet,
    committedSemidet, effectJoinUnspecLeft, effectJoinUnspecRight,
    effectJoinLeft, effectJoinRight, modeInstanceVar, modeInstanceRefl,
    overloadAggRefl, overloadAggDetSemidet, overloadAggSemidetDet,
    conflictCommittedNondetRight, conflictCommittedNondetLeft,
    verdictLeRefl, verdictLeOkMayFail, verdictLeMayFailNondet,
    verdictLeOkNondet, verdictLeMayFailUnknown, verdictLeOkUnknown,
    verdictJoinLeft, verdictJoinRight, modeVerdictDet, modeVerdictSemidet,
    modeVerdictNondet, modeVerdictPlain, bodyCollapse, bodySuperpose,
    bodyEval, bodyOnceOk, bodyOnceMayFail, bodyOnceNondet,
    bodyOnceUnknown, bodySeq, bodyCall, clauseSetOkDet,
    clauseSetMayFailSemidet, clauseSetNondet, arrowAdmitsRule,
    overlapVarLeft, overlapVarRight, overlapEqual, overlapPair,
    coversHereVar, coversHereMatch, coversThere, exhaustiveBoolRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, modeLe, committed, effectJoin, modeInstance,
    overloadAgg, conflictingDecls, verdictLe, verdictJoin, modeVerdict,
    bodyVerdict, clauseSetMode, arrowAdmits, overlapHeads, covers,
    exhaustiveBool, mPlain, mDet, mSemidet, mNondet, mUnspecified,
    mEffectVar, verOk, verMayFail, verNondet, verUnknown, hVarHead, hTrue,
    hFalse, hPair, bCollapse, bSuperpose, bEval, bOnce, bSeq, bCall,
    dCons, ruleId, Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

private def clauseSetNondetProof : RawProof :=
  .node { ruleId := ruleId "clause-set-nondet", arguments := [] } []

private def nondetReflLeProof : RawProof :=
  .node { ruleId := ruleId "mode-le-refl", arguments := [mNondet] } []

private def nondetAdmitsProof : RawProof :=
  .node
    { ruleId := ruleId "arrow-admits"
      arguments := [mNondet, verNondet, mNondet] }
    [clauseSetNondetProof, nondetReflLeProof]

/-- A nondeterministic clause set is admissible under a `-[nondet]->`
declaration: weakening is downgraded, never rejected. -/
theorem nondet_arrow_admits_nondet_body :
    checkRaw checked (arrowAdmits mNondet verNondet)
      nondetAdmitsProof = true := by
  simp [checkRaw, checkRawChildren, checked, definition,
    nondetAdmitsProof, clauseSetNondetProof, nondetReflLeProof,
    modeLeRefl, modeLeDetSemidet, modeLeSemidetNondet, modeLeDetNondet,
    committedDet, committedSemidet, effectJoinUnspecLeft,
    effectJoinUnspecRight, effectJoinLeft, effectJoinRight,
    modeInstanceVar, modeInstanceRefl, overloadAggRefl,
    overloadAggDetSemidet, overloadAggSemidetDet,
    conflictCommittedNondetRight, conflictCommittedNondetLeft,
    verdictLeRefl, verdictLeOkMayFail, verdictLeMayFailNondet,
    verdictLeOkNondet, verdictLeMayFailUnknown, verdictLeOkUnknown,
    verdictJoinLeft, verdictJoinRight, modeVerdictDet, modeVerdictSemidet,
    modeVerdictNondet, modeVerdictPlain, bodyCollapse, bodySuperpose,
    bodyEval, bodyOnceOk, bodyOnceMayFail, bodyOnceNondet,
    bodyOnceUnknown, bodySeq, bodyCall, clauseSetOkDet,
    clauseSetMayFailSemidet, clauseSetNondet, arrowAdmitsRule,
    overlapVarLeft, overlapVarRight, overlapEqual, overlapPair,
    coversHereVar, coversHereMatch, coversThere, exhaustiveBoolRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, modeLe, committed, effectJoin, modeInstance,
    overloadAgg, conflictingDecls, verdictLe, verdictJoin, modeVerdict,
    bodyVerdict, clauseSetMode, arrowAdmits, overlapHeads, covers,
    exhaustiveBool, mPlain, mDet, mSemidet, mNondet, mUnspecified,
    mEffectVar, verOk, verMayFail, verNondet, verUnknown, hVarHead, hTrue,
    hFalse, hPair, bCollapse, bSuperpose, bEval, bOnce, bSeq, bCall,
    dCons, ruleId, Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

private def varOverlapProof : RawProof :=
  .node { ruleId := ruleId "overlap-var-left", arguments := [hTrue] } []

/-- A variable argument position overlaps everything:
unifiable-on-copies (`det_validate.pl:245`). -/
theorem variable_head_overlaps :
    checkRaw checked (overlapHeads hVarHead hTrue)
      varOverlapProof = true := by
  simp [checkRaw, checkRawChildren, checked, definition,
    varOverlapProof, modeLeRefl, modeLeDetSemidet, modeLeSemidetNondet,
    modeLeDetNondet, committedDet, committedSemidet, effectJoinUnspecLeft,
    effectJoinUnspecRight, effectJoinLeft, effectJoinRight,
    modeInstanceVar, modeInstanceRefl, overloadAggRefl,
    overloadAggDetSemidet, overloadAggSemidetDet,
    conflictCommittedNondetRight, conflictCommittedNondetLeft,
    verdictLeRefl, verdictLeOkMayFail, verdictLeMayFailNondet,
    verdictLeOkNondet, verdictLeMayFailUnknown, verdictLeOkUnknown,
    verdictJoinLeft, verdictJoinRight, modeVerdictDet, modeVerdictSemidet,
    modeVerdictNondet, modeVerdictPlain, bodyCollapse, bodySuperpose,
    bodyEval, bodyOnceOk, bodyOnceMayFail, bodyOnceNondet,
    bodyOnceUnknown, bodySeq, bodyCall, clauseSetOkDet,
    clauseSetMayFailSemidet, clauseSetNondet, arrowAdmitsRule,
    overlapVarLeft, overlapVarRight, overlapEqual, overlapPair,
    coversHereVar, coversHereMatch, coversThere, exhaustiveBoolRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, modeLe, committed, effectJoin, modeInstance,
    overloadAgg, conflictingDecls, verdictLe, verdictJoin, modeVerdict,
    bodyVerdict, clauseSetMode, arrowAdmits, overlapHeads, covers,
    exhaustiveBool, mPlain, mDet, mSemidet, mNondet, mUnspecified,
    mEffectVar, verOk, verMayFail, verNondet, verUnknown, hVarHead, hTrue,
    hFalse, hPair, bCollapse, bSuperpose, bEval, bOnce, bSeq, bCall,
    dCons, ruleId, Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

private def boolHeads : Pattern := dCons hTrue (dCons hFalse dNil)

private def coversTrueProof : RawProof :=
  .node
    { ruleId := ruleId "covers-here-match"
      arguments := [hTrue, dCons hFalse dNil] } []

private def coversFalseInnerProof : RawProof :=
  .node
    { ruleId := ruleId "covers-here-match"
      arguments := [hFalse, dNil] } []

private def coversFalseProof : RawProof :=
  .node
    { ruleId := ruleId "covers-there"
      arguments := [hTrue, dCons hFalse dNil, hFalse] }
    [coversFalseInnerProof]

private def exhaustiveProof : RawProof :=
  .node
    { ruleId := ruleId "exhaustive-bool", arguments := [boolHeads] }
    [coversTrueProof, coversFalseProof]

/-- Both Bool keys covered: exhaustive over the closed domain
(`det_analysis.pl:660-676`). -/
theorem exhaustive_bool_with_both_keys :
    checkRaw checked (exhaustiveBool boolHeads)
      exhaustiveProof = true := by
  simp [checkRaw, checkRawChildren, checked, definition,
    exhaustiveProof, boolHeads, coversTrueProof, coversFalseInnerProof,
    coversFalseProof, modeLeRefl, modeLeDetSemidet, modeLeSemidetNondet,
    modeLeDetNondet, committedDet, committedSemidet, effectJoinUnspecLeft,
    effectJoinUnspecRight, effectJoinLeft, effectJoinRight,
    modeInstanceVar, modeInstanceRefl, overloadAggRefl,
    overloadAggDetSemidet, overloadAggSemidetDet,
    conflictCommittedNondetRight, conflictCommittedNondetLeft,
    verdictLeRefl, verdictLeOkMayFail, verdictLeMayFailNondet,
    verdictLeOkNondet, verdictLeMayFailUnknown, verdictLeOkUnknown,
    verdictJoinLeft, verdictJoinRight, modeVerdictDet, modeVerdictSemidet,
    modeVerdictNondet, modeVerdictPlain, bodyCollapse, bodySuperpose,
    bodyEval, bodyOnceOk, bodyOnceMayFail, bodyOnceNondet,
    bodyOnceUnknown, bodySeq, bodyCall, clauseSetOkDet,
    clauseSetMayFailSemidet, clauseSetNondet, arrowAdmitsRule,
    overlapVarLeft, overlapVarRight, overlapEqual, overlapPair,
    coversHereVar, coversHereMatch, coversThere, exhaustiveBoolRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, modeLe, committed, effectJoin, modeInstance,
    overloadAgg, conflictingDecls, verdictLe, verdictJoin, modeVerdict,
    bodyVerdict, clauseSetMode, arrowAdmits, overlapHeads, covers,
    exhaustiveBool, mPlain, mDet, mSemidet, mNondet, mUnspecified,
    mEffectVar, verOk, verMayFail, verNondet, verUnknown, hVarHead, hTrue,
    hFalse, hPair, bCollapse, bSuperpose, bEval, bOnce, bSeq, bCall, dNil,
    dCons, ruleId, Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

/-! ## Negative theorems: candidate derivations the checker rejects.
Exhaustive impossibility (quantifying over all proofs) is the stage-2
soundness layer's obligation and is deliberately not claimed here. -/

private def nondetIntoDetCandidate : RawProof :=
  .node
    { ruleId := ruleId "arrow-admits"
      arguments := [mDet, verNondet, mNondet] }
    [clauseSetNondetProof, nondetReflLeProof]

/-- A nondeterministic clause set does NOT satisfy a `-[det]->`
declaration: the required premise `ModeLe MNondet MDet` has no rule
(rejection class `overlapping_deterministic_clauses` /
`det_nonexhaustive` family, `det_validate.pl:220-260`).  The candidate
supplies a refl derivation, which concludes the wrong inequality. -/
theorem det_arrow_rejects_nondet_body :
    checkRaw checked (arrowAdmits mDet verNondet)
      nondetIntoDetCandidate = false := by
  simp [checkRaw, checkRawChildren, checked, definition,
    nondetIntoDetCandidate, clauseSetNondetProof, nondetReflLeProof,
    modeLeRefl, modeLeDetSemidet, modeLeSemidetNondet, modeLeDetNondet,
    committedDet, committedSemidet, effectJoinUnspecLeft,
    effectJoinUnspecRight, effectJoinLeft, effectJoinRight,
    modeInstanceVar, modeInstanceRefl, overloadAggRefl,
    overloadAggDetSemidet, overloadAggSemidetDet,
    conflictCommittedNondetRight, conflictCommittedNondetLeft,
    verdictLeRefl, verdictLeOkMayFail, verdictLeMayFailNondet,
    verdictLeOkNondet, verdictLeMayFailUnknown, verdictLeOkUnknown,
    verdictJoinLeft, verdictJoinRight, modeVerdictDet, modeVerdictSemidet,
    modeVerdictNondet, modeVerdictPlain, bodyCollapse, bodySuperpose,
    bodyEval, bodyOnceOk, bodyOnceMayFail, bodyOnceNondet,
    bodyOnceUnknown, bodySeq, bodyCall, clauseSetOkDet,
    clauseSetMayFailSemidet, clauseSetNondet, arrowAdmitsRule,
    overlapVarLeft, overlapVarRight, overlapEqual, overlapPair,
    coversHereVar, coversHereMatch, coversThere, exhaustiveBoolRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, modeLe, committed, effectJoin, modeInstance,
    overloadAgg, conflictingDecls, verdictLe, verdictJoin, modeVerdict,
    bodyVerdict, clauseSetMode, arrowAdmits, overlapHeads, covers,
    exhaustiveBool, mPlain, mDet, mSemidet, mNondet, mUnspecified,
    mEffectVar, verOk, verMayFail, verNondet, verUnknown, hVarHead, hTrue,
    hFalse, hPair, bCollapse, bSuperpose, bEval, bOnce, bSeq, bCall,
    dCons, ruleId, Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

private def overloadConflictCandidate : RawProof :=
  .node
    { ruleId := ruleId "overload-agg-refl", arguments := [mNondet] } []

/-- `{det, nondet}` never aggregates (the reference throws
`conflicting_determinism_declarations` instead — the positive
`conflicting_declarations_det_nondet` above is its twin). -/
theorem overload_refl_rejects_det_nondet :
    checkRaw checked (overloadAgg mDet mNondet mNondet)
      overloadConflictCandidate = false := by
  simp [checkRaw, checkRawChildren, checked, definition,
    overloadConflictCandidate, modeLeRefl, modeLeDetSemidet,
    modeLeSemidetNondet, modeLeDetNondet, committedDet, committedSemidet,
    effectJoinUnspecLeft, effectJoinUnspecRight, effectJoinLeft,
    effectJoinRight, modeInstanceVar, modeInstanceRefl, overloadAggRefl,
    overloadAggDetSemidet, overloadAggSemidetDet,
    conflictCommittedNondetRight, conflictCommittedNondetLeft,
    verdictLeRefl, verdictLeOkMayFail, verdictLeMayFailNondet,
    verdictLeOkNondet, verdictLeMayFailUnknown, verdictLeOkUnknown,
    verdictJoinLeft, verdictJoinRight, modeVerdictDet, modeVerdictSemidet,
    modeVerdictNondet, modeVerdictPlain, bodyCollapse, bodySuperpose,
    bodyEval, bodyOnceOk, bodyOnceMayFail, bodyOnceNondet,
    bodyOnceUnknown, bodySeq, bodyCall, clauseSetOkDet,
    clauseSetMayFailSemidet, clauseSetNondet, arrowAdmitsRule,
    overlapVarLeft, overlapVarRight, overlapEqual, overlapPair,
    coversHereVar, coversHereMatch, coversThere, exhaustiveBoolRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, modeLe, committed, effectJoin, modeInstance,
    overloadAgg, conflictingDecls, verdictLe, verdictJoin, modeVerdict,
    bodyVerdict, clauseSetMode, arrowAdmits, overlapHeads, covers,
    exhaustiveBool, mPlain, mDet, mSemidet, mNondet, mUnspecified,
    mEffectVar, verOk, verMayFail, verNondet, verUnknown, hVarHead, hTrue,
    hFalse, hPair, bCollapse, bSuperpose, bEval, bOnce, bSeq, bCall,
    dCons, ruleId, Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

private def overlapReflCandidate : RawProof :=
  .node { ruleId := ruleId "overlap-equal", arguments := [hTrue] } []

/-- Distinct literal keys are not unifiable: the equality candidate
instantiates to the wrong pair (`det_validate.pl:245`). -/
theorem distinct_literal_heads_do_not_overlap :
    checkRaw checked (overlapHeads hTrue hFalse)
      overlapReflCandidate = false := by
  simp [checkRaw, checkRawChildren, checked, definition,
    overlapReflCandidate, modeLeRefl, modeLeDetSemidet,
    modeLeSemidetNondet, modeLeDetNondet, committedDet, committedSemidet,
    effectJoinUnspecLeft, effectJoinUnspecRight, effectJoinLeft,
    effectJoinRight, modeInstanceVar, modeInstanceRefl, overloadAggRefl,
    overloadAggDetSemidet, overloadAggSemidetDet,
    conflictCommittedNondetRight, conflictCommittedNondetLeft,
    verdictLeRefl, verdictLeOkMayFail, verdictLeMayFailNondet,
    verdictLeOkNondet, verdictLeMayFailUnknown, verdictLeOkUnknown,
    verdictJoinLeft, verdictJoinRight, modeVerdictDet, modeVerdictSemidet,
    modeVerdictNondet, modeVerdictPlain, bodyCollapse, bodySuperpose,
    bodyEval, bodyOnceOk, bodyOnceMayFail, bodyOnceNondet,
    bodyOnceUnknown, bodySeq, bodyCall, clauseSetOkDet,
    clauseSetMayFailSemidet, clauseSetNondet, arrowAdmitsRule,
    overlapVarLeft, overlapVarRight, overlapEqual, overlapPair,
    coversHereVar, coversHereMatch, coversThere, exhaustiveBoolRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, modeLe, committed, effectJoin, modeInstance,
    overloadAgg, conflictingDecls, verdictLe, verdictJoin, modeVerdict,
    bodyVerdict, clauseSetMode, arrowAdmits, overlapHeads, covers,
    exhaustiveBool, mPlain, mDet, mSemidet, mNondet, mUnspecified,
    mEffectVar, verOk, verMayFail, verNondet, verUnknown, hVarHead, hTrue,
    hFalse, hPair, bCollapse, bSuperpose, bEval, bOnce, bSeq, bCall,
    dCons, ruleId, Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

private def overlapVarCandidate : RawProof :=
  .node { ruleId := ruleId "overlap-var-left", arguments := [hFalse] } []

/-- The variable-overlap rule requires a literal `HVarHead` position;
it cannot be instantiated at `HTrue`. -/
theorem distinct_literal_heads_var_candidate_rejects :
    checkRaw checked (overlapHeads hTrue hFalse)
      overlapVarCandidate = false := by
  simp [checkRaw, checkRawChildren, checked, definition,
    overlapVarCandidate, modeLeRefl, modeLeDetSemidet,
    modeLeSemidetNondet, modeLeDetNondet, committedDet, committedSemidet,
    effectJoinUnspecLeft, effectJoinUnspecRight, effectJoinLeft,
    effectJoinRight, modeInstanceVar, modeInstanceRefl, overloadAggRefl,
    overloadAggDetSemidet, overloadAggSemidetDet,
    conflictCommittedNondetRight, conflictCommittedNondetLeft,
    verdictLeRefl, verdictLeOkMayFail, verdictLeMayFailNondet,
    verdictLeOkNondet, verdictLeMayFailUnknown, verdictLeOkUnknown,
    verdictJoinLeft, verdictJoinRight, modeVerdictDet, modeVerdictSemidet,
    modeVerdictNondet, modeVerdictPlain, bodyCollapse, bodySuperpose,
    bodyEval, bodyOnceOk, bodyOnceMayFail, bodyOnceNondet,
    bodyOnceUnknown, bodySeq, bodyCall, clauseSetOkDet,
    clauseSetMayFailSemidet, clauseSetNondet, arrowAdmitsRule,
    overlapVarLeft, overlapVarRight, overlapEqual, overlapPair,
    coversHereVar, coversHereMatch, coversThere, exhaustiveBoolRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, modeLe, committed, effectJoin, modeInstance,
    overloadAgg, conflictingDecls, verdictLe, verdictJoin, modeVerdict,
    bodyVerdict, clauseSetMode, arrowAdmits, overlapHeads, covers,
    exhaustiveBool, mPlain, mDet, mSemidet, mNondet, mUnspecified,
    mEffectVar, verOk, verMayFail, verNondet, verUnknown, hVarHead, hTrue,
    hFalse, hPair, bCollapse, bSuperpose, bEval, bOnce, bSeq, bCall,
    dCons, ruleId, Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

private def missingKeyCandidate : RawProof :=
  .node
    { ruleId := ruleId "covers-here-match"
      arguments := [hFalse, dNil] } []

/-- A clause list matching only `HTrue` does not cover the `HFalse` key:
the closed Bool domain makes this the provable-incompleteness error
`det_nonexhaustive` (`det_analysis.pl:618-676`; asymmetric by design —
the error is exactly a failed coverage derivation on a closed domain). -/
theorem missing_false_key_not_covered :
    checkRaw checked (covers (dCons hTrue dNil) hFalse)
      missingKeyCandidate = false := by
  simp [checkRaw, checkRawChildren, checked, definition,
    missingKeyCandidate, modeLeRefl, modeLeDetSemidet,
    modeLeSemidetNondet, modeLeDetNondet, committedDet, committedSemidet,
    effectJoinUnspecLeft, effectJoinUnspecRight, effectJoinLeft,
    effectJoinRight, modeInstanceVar, modeInstanceRefl, overloadAggRefl,
    overloadAggDetSemidet, overloadAggSemidetDet,
    conflictCommittedNondetRight, conflictCommittedNondetLeft,
    verdictLeRefl, verdictLeOkMayFail, verdictLeMayFailNondet,
    verdictLeOkNondet, verdictLeMayFailUnknown, verdictLeOkUnknown,
    verdictJoinLeft, verdictJoinRight, modeVerdictDet, modeVerdictSemidet,
    modeVerdictNondet, modeVerdictPlain, bodyCollapse, bodySuperpose,
    bodyEval, bodyOnceOk, bodyOnceMayFail, bodyOnceNondet,
    bodyOnceUnknown, bodySeq, bodyCall, clauseSetOkDet,
    clauseSetMayFailSemidet, clauseSetNondet, arrowAdmitsRule,
    overlapVarLeft, overlapVarRight, overlapEqual, overlapPair,
    coversHereVar, coversHereMatch, coversThere, exhaustiveBoolRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, modeLe, committed, effectJoin, modeInstance,
    overloadAgg, conflictingDecls, verdictLe, verdictJoin, modeVerdict,
    bodyVerdict, clauseSetMode, arrowAdmits, overlapHeads, covers,
    exhaustiveBool, mPlain, mDet, mSemidet, mNondet, mUnspecified,
    mEffectVar, verOk, verMayFail, verNondet, verUnknown, hVarHead, hTrue,
    hFalse, hPair, bCollapse, bSuperpose, bEval, bOnce, bSeq, bCall, dNil,
    dCons, ruleId, Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

private def onceLaunderCandidate : RawProof :=
  .node
    { ruleId := ruleId "body-once-ok", arguments := [bSuperpose] }
    [superposeNondetProof]

/-- `once` never restores `ok` from a nondeterministic body — the cap is
`may_fail`, not `ok` (`det_proofs.pl:1094-1100`). -/
theorem once_does_not_launder_nondet_to_ok :
    checkRaw checked (bodyVerdict (bOnce bSuperpose) verOk)
      onceLaunderCandidate = false := by
  simp [checkRaw, checkRawChildren, checked, definition,
    onceLaunderCandidate, superposeNondetProof, modeLeRefl,
    modeLeDetSemidet, modeLeSemidetNondet, modeLeDetNondet, committedDet,
    committedSemidet, effectJoinUnspecLeft, effectJoinUnspecRight,
    effectJoinLeft, effectJoinRight, modeInstanceVar, modeInstanceRefl,
    overloadAggRefl, overloadAggDetSemidet, overloadAggSemidetDet,
    conflictCommittedNondetRight, conflictCommittedNondetLeft,
    verdictLeRefl, verdictLeOkMayFail, verdictLeMayFailNondet,
    verdictLeOkNondet, verdictLeMayFailUnknown, verdictLeOkUnknown,
    verdictJoinLeft, verdictJoinRight, modeVerdictDet, modeVerdictSemidet,
    modeVerdictNondet, modeVerdictPlain, bodyCollapse, bodySuperpose,
    bodyEval, bodyOnceOk, bodyOnceMayFail, bodyOnceNondet,
    bodyOnceUnknown, bodySeq, bodyCall, clauseSetOkDet,
    clauseSetMayFailSemidet, clauseSetNondet, arrowAdmitsRule,
    overlapVarLeft, overlapVarRight, overlapEqual, overlapPair,
    coversHereVar, coversHereMatch, coversThere, exhaustiveBoolRule,
    instantiateRule?, CalculusLanguageDef.lookupRule?, argumentsValidAt,
    argumentValidAt, RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, modeLe, committed, effectJoin, modeInstance,
    overloadAgg, conflictingDecls, verdictLe, verdictJoin, modeVerdict,
    bodyVerdict, clauseSetMode, arrowAdmits, overlapHeads, covers,
    exhaustiveBool, mPlain, mDet, mSemidet, mNondet, mUnspecified,
    mEffectVar, verOk, verMayFail, verNondet, verUnknown, hVarHead, hTrue,
    hFalse, hPair, bCollapse, bSuperpose, bEval, bOnce, bSeq, bCall,
    dCons, ruleId, Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

end Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTDeterminism
