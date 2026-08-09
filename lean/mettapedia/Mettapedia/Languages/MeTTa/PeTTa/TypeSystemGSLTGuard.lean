import Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLT

/-!
# PeTTa typecheck-v2 guard judgments (stage: dynamic checker root, phase 3)

Extends the core typecheck-v2 presentation with the DEFINITE-CONFLICT
half the runtime guards enforce: sort conflicts with declaration
resolution, the definite-mismatch judgment over reified values, the
placeable-quantifier over reified declaration lists (an unplaceable
declaration vetoes by non-derivability), the boundness proviso for
committed arrows, and the four-way verdict vocabulary.

Humility discipline (`value_checks.pl:493-520` read through success
typing): every rule concludes a PROVABLE conflict; whatever the judgment
cannot place stays underivable, so the guard passes.  Undeclared nominal
formals have no rule at all — base PeTTa's `get-type` is user-extensible,
so nominal-vs-nominal is never definite.

ENVIRONMENT judgments (`EnvDeclared`, `EnvDeclaredList`) have NO rules in
the export presentation: at runtime the generated artifact binds them to
logic-free primitives over the environment snapshot (a `match` on the
user space's `(: subject type)` atoms), the same binding discipline as
the Metamath grammar's lexical classes.  The RECEIPT presentation adds
fixture facts as rules so the checkRaw receipts can exercise the
resolution paths; the delta between the two rule lists is pinned by
`export_rules_are_receipt_prefix` below.

The deterministic verdict wrapper (refuted before established before
undetermined) is NOT a judgment here: a total non-monotone case split is
not positive-rule content.  It is the generated harness's contract,
checked by the probe-parity and corpus gates.

Fuel (`FZ`/`FS`) bounds declaration-resolution recursion (cyclic
`Newtype`/`Alias` chains), mirroring the depth cutoff of the runtime
realization it replaces.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTGuard

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLT

/-! ## Guard-layer constructors -/

private def fz : Pattern := .apply "FZ" []
private def fs (fuel : Pattern) : Pattern := .apply "FS" [fuel]
private def dNil : Pattern := .apply "DNil" []
private def dCons (head tail : Pattern) : Pattern := .apply "DCons" [head, tail]
/-- One reified declaration `(: name type)`. -/
private def declOf (name type : Pattern) : Pattern := .apply "Decl" [name, type]
private def verRefuted : Pattern := .apply "VerRefuted" []
private def verEstablished : Pattern := .apply "VerEstablished" []
private def verUndetermined : Pattern := .apply "VerUndetermined" []
private def verIncomplete : Pattern := .apply "VerIncomplete" []
/-- A nominal type NAME occurrence (resolved through the environment). -/
private def tNominal (name : Pattern) : Pattern := .apply "TNominal" [name]
/-- Declaration bodies: `(Newtype R)` and `(Alias R)`. -/
private def tNewtype (repr : Pattern) : Pattern := .apply "TNewtype" [repr]
private def tAlias (repr : Pattern) : Pattern := .apply "TAlias" [repr]
/-- A constructor-shaped type member (fixed head and arity). -/
private def tCtor (name arity : Pattern) : Pattern := .apply "TCtor" [name, arity]
/-- A nominal symbol VALUE and an applied-head value (head + arity; the
mismatch judgment needs no field content). -/
private def vSym (name : Pattern) : Pattern := .apply "VSym" [name]
private def vApp (head arity : Pattern) : Pattern := .apply "VApp" [head, arity]
/-- Witness atoms for receipts. -/
private def nomA : Pattern := .apply "NomA" []
private def nomB : Pattern := .apply "NomB" []
private def symA : Pattern := .apply "SymA" []

/-! ## Judgment applications -/

private def baseSortOf (v s : Pattern) : Pattern := .apply "BaseSortOf" [v, s]
private def sortConflicts (f s t : Pattern) : Pattern :=
  .apply "SortConflicts" [f, s, t]
private def conflictsAll (f s ms : Pattern) : Pattern :=
  .apply "ConflictsAll" [f, s, ms]
private def conflictsAllL (f ms t : Pattern) : Pattern :=
  .apply "ConflictsAllL" [f, ms, t]
private def definiteMismatch (f v t : Pattern) : Pattern :=
  .apply "DefiniteMismatch" [f, v, t]
private def mismatchAll (f v ms : Pattern) : Pattern :=
  .apply "MismatchAll" [f, v, ms]
private def declaredConflictSome (f ds t : Pattern) : Pattern :=
  .apply "DeclaredConflictSome" [f, ds, t]
private def declaredConflictRest (f ds t : Pattern) : Pattern :=
  .apply "DeclaredConflictRest" [f, ds, t]
private def headConflictSome (f ds k t : Pattern) : Pattern :=
  .apply "HeadConflictSome" [f, ds, k, t]
private def headConflictRest (f ds k t : Pattern) : Pattern :=
  .apply "HeadConflictRest" [f, ds, k, t]
private def argListLen (as k : Pattern) : Pattern :=
  .apply "ArgListLen" [as, k]
private def argListLenDiffers (as k : Pattern) : Pattern :=
  .apply "ArgListLenDiffers" [as, k]
private def boundnessRefuted (m t : Pattern) : Pattern :=
  .apply "BoundnessRefuted" [m, t]
private def envDeclared (n d : Pattern) : Pattern :=
  .apply "EnvDeclared" [n, d]
private def envDeclaredList (n ds : Pattern) : Pattern :=
  .apply "EnvDeclaredList" [n, ds]

/-! ## Base sorts of literal witnesses (`value_checks.pl:497-499`) -/

private def baseSortNum : RuleSchema :=
  { id := ruleId "base-sort-num", metavariables := [], premises := []
    conclusion := baseSortOf vNum tNum }
private def baseSortStr : RuleSchema :=
  { id := ruleId "base-sort-str", metavariables := [], premises := []
    conclusion := baseSortOf vStr tStr }
private def baseSortTrue : RuleSchema :=
  { id := ruleId "base-sort-true", metavariables := [], premises := []
    conclusion := baseSortOf vTrue tBool }
private def baseSortFalse : RuleSchema :=
  { id := ruleId "base-sort-false", metavariables := [], premises := []
    conclusion := baseSortOf vFalse tBool }

/-! ## Sort conflicts.  Base-vs-base distinct pairs are definite; unions
conflict when every member conflicts; nominal names resolve through the
environment with fuel.  Nominal-vs-nominal and base-vs-undeclared-nominal
have NO rules (open world). -/
private def scNumStr : RuleSchema :=
  { id := ruleId "sc-num-str"
    metavariables := [("f", 0)]
    premises := []
    conclusion := sortConflicts (.fvar "f") tNum tStr }

private def scNumBool : RuleSchema :=
  { id := ruleId "sc-num-bool"
    metavariables := [("f", 0)]
    premises := []
    conclusion := sortConflicts (.fvar "f") tNum tBool }

private def scStrNum : RuleSchema :=
  { id := ruleId "sc-str-num"
    metavariables := [("f", 0)]
    premises := []
    conclusion := sortConflicts (.fvar "f") tStr tNum }

private def scStrBool : RuleSchema :=
  { id := ruleId "sc-str-bool"
    metavariables := [("f", 0)]
    premises := []
    conclusion := sortConflicts (.fvar "f") tStr tBool }

private def scBoolNum : RuleSchema :=
  { id := ruleId "sc-bool-num"
    metavariables := [("f", 0)]
    premises := []
    conclusion := sortConflicts (.fvar "f") tBool tNum }

private def scBoolStr : RuleSchema :=
  { id := ruleId "sc-bool-str"
    metavariables := [("f", 0)]
    premises := []
    conclusion := sortConflicts (.fvar "f") tBool tStr }

private def scUnionRight : RuleSchema :=
  { id := ruleId "sc-union-right"
    metavariables := [("f", 0), ("s", 0), ("ms", 0)]
    premises :=
      [ conflictsAll (.fvar "f") (.fvar "s") (.fvar "ms") ]
    conclusion := sortConflicts (fs (.fvar "f")) (.fvar "s") (tUnion (.fvar "ms")) }

private def scUnionLeft : RuleSchema :=
  { id := ruleId "sc-union-left"
    metavariables := [("f", 0), ("ms", 0), ("t", 0)]
    premises :=
      [ conflictsAllL (.fvar "f") (.fvar "ms") (.fvar "t") ]
    conclusion := sortConflicts (fs (.fvar "f")) (tUnion (.fvar "ms")) (.fvar "t") }

private def scNewtypeFormal : RuleSchema :=
  { id := ruleId "sc-newtype-formal"
    metavariables := [("f", 0), ("s", 0), ("n", 0), ("r", 0)]
    premises :=
      [ envDeclared (.fvar "n") (tNewtype (.fvar "r")),
        sortConflicts (.fvar "f") (.fvar "s") (.fvar "r") ]
    conclusion := sortConflicts (fs (.fvar "f")) (.fvar "s") (tNominal (.fvar "n")) }

private def scAliasFormal : RuleSchema :=
  { id := ruleId "sc-alias-formal"
    metavariables := [("f", 0), ("s", 0), ("n", 0), ("r", 0)]
    premises :=
      [ envDeclared (.fvar "n") (tAlias (.fvar "r")),
        sortConflicts (.fvar "f") (.fvar "s") (.fvar "r") ]
    conclusion := sortConflicts (fs (.fvar "f")) (.fvar "s") (tNominal (.fvar "n")) }

private def scNewtypeSort : RuleSchema :=
  { id := ruleId "sc-newtype-sort"
    metavariables := [("f", 0), ("n", 0), ("r", 0), ("t", 0)]
    premises :=
      [ envDeclared (.fvar "n") (tNewtype (.fvar "r")),
        sortConflicts (.fvar "f") (.fvar "r") (.fvar "t") ]
    conclusion := sortConflicts (fs (.fvar "f")) (tNominal (.fvar "n")) (.fvar "t") }

private def scAliasSort : RuleSchema :=
  { id := ruleId "sc-alias-sort"
    metavariables := [("f", 0), ("n", 0), ("r", 0), ("t", 0)]
    premises :=
      [ envDeclared (.fvar "n") (tAlias (.fvar "r")),
        sortConflicts (.fvar "f") (.fvar "r") (.fvar "t") ]
    conclusion := sortConflicts (fs (.fvar "f")) (tNominal (.fvar "n")) (.fvar "t") }

private def caNil : RuleSchema :=
  { id := ruleId "ca-nil"
    metavariables := [("f", 0), ("s", 0)]
    premises := []
    conclusion := conflictsAll (.fvar "f") (.fvar "s") tNil }

private def caCons : RuleSchema :=
  { id := ruleId "ca-cons"
    metavariables := [("f", 0), ("s", 0), ("m", 0), ("ms", 0)]
    premises :=
      [ sortConflicts (.fvar "f") (.fvar "s") (.fvar "m"),
        conflictsAll (.fvar "f") (.fvar "s") (.fvar "ms") ]
    conclusion := conflictsAll (.fvar "f") (.fvar "s") (tCons (.fvar "m") (.fvar "ms")) }

private def calNil : RuleSchema :=
  { id := ruleId "cal-nil"
    metavariables := [("f", 0), ("t", 0)]
    premises := []
    conclusion := conflictsAllL (.fvar "f") tNil (.fvar "t") }

private def calCons : RuleSchema :=
  { id := ruleId "cal-cons"
    metavariables := [("f", 0), ("m", 0), ("ms", 0), ("t", 0)]
    premises :=
      [ sortConflicts (.fvar "f") (.fvar "m") (.fvar "t"),
        conflictsAllL (.fvar "f") (.fvar "ms") (.fvar "t") ]
    conclusion := conflictsAllL (.fvar "f") (tCons (.fvar "m") (.fvar "ms")) (.fvar "t") }

/-! ## Definite mismatch of reified values (`runtime_type_ok`'s refutation
face; the condemned C realization's semantics as authored rules) -/

private def dmBase : RuleSchema :=
  { id := ruleId "dm-base"
    metavariables := [("f", 0), ("v", 0), ("s", 0), ("t", 0)]
    premises :=
      [ baseSortOf (.fvar "v") (.fvar "s"),
        sortConflicts (.fvar "f") (.fvar "s") (.fvar "t") ]
    conclusion := definiteMismatch (fs (.fvar "f")) (.fvar "v") (.fvar "t") }

private def dmCtor : RuleSchema :=
  { id := ruleId "dm-ctor"
    metavariables := [("f", 0), ("v", 0), ("s", 0), ("n", 0), ("k", 0)]
    premises :=
      [ baseSortOf (.fvar "v") (.fvar "s") ]
    conclusion := definiteMismatch (fs (.fvar "f")) (.fvar "v") (tCtor (.fvar "n") (.fvar "k")) }

private def dmUnion : RuleSchema :=
  { id := ruleId "dm-union"
    metavariables := [("f", 0), ("v", 0), ("ms", 0)]
    premises :=
      [ mismatchAll (.fvar "f") (.fvar "v") (.fvar "ms") ]
    conclusion := definiteMismatch (fs (.fvar "f")) (.fvar "v") (tUnion (.fvar "ms")) }

private def dmListLiteral : RuleSchema :=
  { id := ruleId "dm-list-literal"
    metavariables := [("f", 0), ("v", 0), ("s", 0), ("t", 0)]
    premises :=
      [ baseSortOf (.fvar "v") (.fvar "s") ]
    conclusion := definiteMismatch (fs (.fvar "f")) (.fvar "v") (tList (.fvar "t")) }

private def dmListHere : RuleSchema :=
  { id := ruleId "dm-list-here"
    metavariables := [("f", 0), ("v", 0), ("vs", 0), ("t", 0)]
    premises :=
      [ definiteMismatch (.fvar "f") (.fvar "v") (.fvar "t") ]
    conclusion := definiteMismatch (fs (.fvar "f")) (vCons (.fvar "v") (.fvar "vs")) (tList (.fvar "t")) }

private def dmListThere : RuleSchema :=
  { id := ruleId "dm-list-there"
    metavariables := [("f", 0), ("v", 0), ("vs", 0), ("t", 0)]
    premises :=
      [ definiteMismatch (.fvar "f") (.fvar "vs") (tList (.fvar "t")) ]
    conclusion := definiteMismatch (fs (.fvar "f")) (vCons (.fvar "v") (.fvar "vs")) (tList (.fvar "t")) }

private def dmNewtypeFormal : RuleSchema :=
  { id := ruleId "dm-newtype-formal"
    metavariables := [("f", 0), ("v", 0), ("n", 0), ("r", 0)]
    premises :=
      [ envDeclared (.fvar "n") (tNewtype (.fvar "r")),
        definiteMismatch (.fvar "f") (.fvar "v") (.fvar "r") ]
    conclusion := definiteMismatch (fs (.fvar "f")) (.fvar "v") (tNominal (.fvar "n")) }

private def dmAliasFormal : RuleSchema :=
  { id := ruleId "dm-alias-formal"
    metavariables := [("f", 0), ("v", 0), ("n", 0), ("r", 0)]
    premises :=
      [ envDeclared (.fvar "n") (tAlias (.fvar "r")),
        definiteMismatch (.fvar "f") (.fvar "v") (.fvar "r") ]
    conclusion := definiteMismatch (fs (.fvar "f")) (.fvar "v") (tNominal (.fvar "n")) }

private def dmDeclaredSymbol : RuleSchema :=
  { id := ruleId "dm-declared-symbol"
    metavariables := [("f", 0), ("n", 0), ("ds", 0), ("t", 0)]
    premises :=
      [ envDeclaredList (.fvar "n") (.fvar "ds"),
        declaredConflictSome (.fvar "f") (.fvar "ds") (.fvar "t") ]
    conclusion := definiteMismatch (fs (.fvar "f")) (vSym (.fvar "n")) (.fvar "t") }

private def dmAppliedHead : RuleSchema :=
  { id := ruleId "dm-applied-head"
    metavariables := [("f", 0), ("h", 0), ("k", 0), ("ds", 0), ("t", 0)]
    premises :=
      [ envDeclaredList (.fvar "h") (.fvar "ds"),
        headConflictSome (.fvar "f") (.fvar "ds") (.fvar "k") (.fvar "t") ]
    conclusion := definiteMismatch (fs (.fvar "f")) (vApp (.fvar "h") (.fvar "k")) (.fvar "t") }

private def maNil : RuleSchema :=
  { id := ruleId "ma-nil"
    metavariables := [("f", 0), ("v", 0)]
    premises := []
    conclusion := mismatchAll (.fvar "f") (.fvar "v") tNil }

private def maCons : RuleSchema :=
  { id := ruleId "ma-cons"
    metavariables := [("f", 0), ("v", 0), ("m", 0), ("ms", 0)]
    premises :=
      [ definiteMismatch (.fvar "f") (.fvar "v") (.fvar "m"),
        mismatchAll (.fvar "f") (.fvar "v") (.fvar "ms") ]
    conclusion := mismatchAll (.fvar "f") (.fvar "v") (tCons (.fvar "m") (.fvar "ms")) }

/-! ## The placeable quantifier over reified declaration lists
(`petta_guard_declared_conflict`'s semantics as rules).  `Some` demands a
conflicting head declaration and a conforming rest; a declaration whose
sort cannot be judged has no applicable rule, so the whole derivation
fails — the veto is non-derivability, matching the humility contract. -/

private def dcsCons : RuleSchema :=
  { id := ruleId "dcs-cons"
    metavariables := [("f", 0), ("n", 0), ("d", 0), ("ds", 0), ("t", 0)]
    premises :=
      [ sortConflicts (.fvar "f") (.fvar "d") (.fvar "t"),
        declaredConflictRest (.fvar "f") (.fvar "ds") (.fvar "t") ]
    conclusion := declaredConflictSome (.fvar "f") (dCons (declOf (.fvar "n") (.fvar "d")) (.fvar "ds")) (.fvar "t") }

private def dcrNil : RuleSchema :=
  { id := ruleId "dcr-nil"
    metavariables := [("f", 0), ("t", 0)]
    premises := []
    conclusion := declaredConflictRest (.fvar "f") dNil (.fvar "t") }

private def dcrCons : RuleSchema :=
  { id := ruleId "dcr-cons"
    metavariables := [("f", 0), ("n", 0), ("d", 0), ("ds", 0), ("t", 0)]
    premises :=
      [ sortConflicts (.fvar "f") (.fvar "d") (.fvar "t"),
        declaredConflictRest (.fvar "f") (.fvar "ds") (.fvar "t") ]
    conclusion := declaredConflictRest (.fvar "f") (dCons (declOf (.fvar "n") (.fvar "d")) (.fvar "ds")) (.fvar "t") }

private def hcsHere : RuleSchema :=
  { id := ruleId "hcs-here"
    metavariables := [("f", 0), ("n", 0), ("m", 0), ("as", 0), ("r", 0), ("ds", 0), ("k", 0), ("t", 0)]
    premises :=
      [ argListLen (.fvar "as") (.fvar "k"),
        sortConflicts (.fvar "f") (.fvar "r") (.fvar "t"),
        headConflictRest (.fvar "f") (.fvar "ds") (.fvar "k") (.fvar "t") ]
    conclusion := headConflictSome (.fvar "f") (dCons (declOf (.fvar "n") (tArrow (.fvar "m") (.fvar "as") (.fvar "r"))) (.fvar "ds")) (.fvar "k") (.fvar "t") }

private def hcsSkip : RuleSchema :=
  { id := ruleId "hcs-skip"
    metavariables := [("f", 0), ("n", 0), ("m", 0), ("as", 0), ("r", 0), ("ds", 0), ("k", 0), ("t", 0)]
    premises :=
      [ argListLenDiffers (.fvar "as") (.fvar "k"),
        headConflictSome (.fvar "f") (.fvar "ds") (.fvar "k") (.fvar "t") ]
    conclusion := headConflictSome (.fvar "f") (dCons (declOf (.fvar "n") (tArrow (.fvar "m") (.fvar "as") (.fvar "r"))) (.fvar "ds")) (.fvar "k") (.fvar "t") }

private def hcrNil : RuleSchema :=
  { id := ruleId "hcr-nil"
    metavariables := [("f", 0), ("k", 0), ("t", 0)]
    premises := []
    conclusion := headConflictRest (.fvar "f") dNil (.fvar "k") (.fvar "t") }

private def hcrCons : RuleSchema :=
  { id := ruleId "hcr-cons"
    metavariables := [("f", 0), ("n", 0), ("m", 0), ("as", 0), ("r", 0), ("ds", 0), ("k", 0), ("t", 0)]
    premises :=
      [ argListLen (.fvar "as") (.fvar "k"),
        sortConflicts (.fvar "f") (.fvar "r") (.fvar "t"),
        headConflictRest (.fvar "f") (.fvar "ds") (.fvar "k") (.fvar "t") ]
    conclusion := headConflictRest (.fvar "f") (dCons (declOf (.fvar "n") (tArrow (.fvar "m") (.fvar "as") (.fvar "r"))) (.fvar "ds")) (.fvar "k") (.fvar "t") }

private def hcrSkip : RuleSchema :=
  { id := ruleId "hcr-skip"
    metavariables := [("f", 0), ("n", 0), ("m", 0), ("as", 0), ("r", 0), ("ds", 0), ("k", 0), ("t", 0)]
    premises :=
      [ argListLenDiffers (.fvar "as") (.fvar "k"),
        headConflictRest (.fvar "f") (.fvar "ds") (.fvar "k") (.fvar "t") ]
    conclusion := headConflictRest (.fvar "f") (dCons (declOf (.fvar "n") (tArrow (.fvar "m") (.fvar "as") (.fvar "r"))) (.fvar "ds")) (.fvar "k") (.fvar "t") }

private def allNil : RuleSchema :=
  { id := ruleId "all-nil"
    metavariables := []
    premises := []
    conclusion := argListLen tNil fz }

private def allCons : RuleSchema :=
  { id := ruleId "all-cons"
    metavariables := [("a", 0), ("as", 0), ("k", 0)]
    premises :=
      [ argListLen (.fvar "as") (.fvar "k") ]
    conclusion := argListLen (tCons (.fvar "a") (.fvar "as")) (fs (.fvar "k")) }

private def aldNilSucc : RuleSchema :=
  { id := ruleId "ald-nil-succ"
    metavariables := [("k", 0)]
    premises := []
    conclusion := argListLenDiffers tNil (fs (.fvar "k")) }

private def aldConsZero : RuleSchema :=
  { id := ruleId "ald-cons-zero"
    metavariables := [("a", 0), ("as", 0)]
    premises := []
    conclusion := argListLenDiffers (tCons (.fvar "a") (.fvar "as")) fz }

private def aldConsRec : RuleSchema :=
  { id := ruleId "ald-cons-rec"
    metavariables := [("a", 0), ("as", 0), ("k", 0)]
    premises :=
      [ argListLenDiffers (.fvar "as") (.fvar "k") ]
    conclusion := argListLenDiffers (tCons (.fvar "a") (.fvar "as")) (fs (.fvar "k")) }

/-! ## Boundness proviso (`translator.pl:200-219`): a committed arrow with
a base-literal formal demands a bound argument. -/

private def brDetNum : RuleSchema :=
  { id := ruleId "br-det-num", metavariables := [], premises := []
    conclusion := boundnessRefuted mDet tNum }

private def brDetStr : RuleSchema :=
  { id := ruleId "br-det-str", metavariables := [], premises := []
    conclusion := boundnessRefuted mDet tStr }

private def brDetBool : RuleSchema :=
  { id := ruleId "br-det-bool", metavariables := [], premises := []
    conclusion := boundnessRefuted mDet tBool }

private def brSemidetNum : RuleSchema :=
  { id := ruleId "br-semidet-num", metavariables := [], premises := []
    conclusion := boundnessRefuted mSemidet tNum }

private def brSemidetStr : RuleSchema :=
  { id := ruleId "br-semidet-str", metavariables := [], premises := []
    conclusion := boundnessRefuted mSemidet tStr }

private def brSemidetBool : RuleSchema :=
  { id := ruleId "br-semidet-bool", metavariables := [], premises := []
    conclusion := boundnessRefuted mSemidet tBool }

/-! ## Receipt fixtures (NOT exported): environment facts exercising the
resolution paths.  The export/receipt delta is pinned below. -/

private def fixtureNomNewtype : RuleSchema :=
  { id := ruleId "fixture-nom-newtype", metavariables := [], premises := []
    conclusion := envDeclared nomA (tNewtype tNum) }
private def fixtureNomAlias : RuleSchema :=
  { id := ruleId "fixture-nom-alias", metavariables := [], premises := []
    conclusion := envDeclared nomB (tAlias tStr) }
private def fixtureSymDecls : RuleSchema :=
  { id := ruleId "fixture-sym-decls", metavariables := [], premises := []
    conclusion :=
      envDeclaredList symA (dCons (declOf symA tStr) dNil) }

/-! ## The guard language: one extended definition -/

def newTerms : List GrammarRule :=
  [ termConstructor "FZ" 0, termConstructor "FS" 1,
    termConstructor "DNil" 0, termConstructor "DCons" 2,
    termConstructor "Decl" 2,
    termConstructor "VerRefuted" 0, termConstructor "VerEstablished" 0,
    termConstructor "VerUndetermined" 0, termConstructor "VerIncomplete" 0,
    termConstructor "TNominal" 1, termConstructor "TNewtype" 1,
    termConstructor "TAlias" 1, termConstructor "TCtor" 2,
    termConstructor "VSym" 1, termConstructor "VApp" 2,
    termConstructor "NomA" 0, termConstructor "NomB" 0,
    termConstructor "SymA" 0 ]

def newJudgments : List JudgmentDecl :=
  [ { head := "BaseSortOf", arity := 2 },
    { head := "SortConflicts", arity := 3 },
    { head := "ConflictsAll", arity := 3 },
    { head := "ConflictsAllL", arity := 3 },
    { head := "DefiniteMismatch", arity := 3 },
    { head := "MismatchAll", arity := 3 },
    { head := "DeclaredConflictSome", arity := 3 },
    { head := "DeclaredConflictRest", arity := 3 },
    { head := "HeadConflictSome", arity := 4 },
    { head := "HeadConflictRest", arity := 4 },
    { head := "ArgListLen", arity := 2 },
    { head := "ArgListLenDiffers", arity := 2 },
    { head := "BoundnessRefuted", arity := 2 },
    { head := "EnvDeclared", arity := 2 },
    { head := "EnvDeclaredList", arity := 2 } ]

def exportRules : List RuleSchema :=
  [ baseSortNum, baseSortStr, baseSortTrue, baseSortFalse, scNumStr,
    scNumBool, scStrNum, scStrBool, scBoolNum, scBoolStr, scUnionRight,
    scUnionLeft, scNewtypeFormal, scAliasFormal, scNewtypeSort,
    scAliasSort, caNil, caCons, calNil, calCons, dmBase, dmCtor,
    dmUnion, dmListLiteral, dmListHere, dmListThere, dmNewtypeFormal,
    dmAliasFormal, dmDeclaredSymbol, dmAppliedHead, maNil, maCons,
    dcsCons, dcrNil, dcrCons, hcsHere, hcsSkip, hcrNil, hcrCons,
    hcrSkip, allNil, allCons, aldNilSucc, aldConsZero, aldConsRec,
    brDetNum, brDetStr, brDetBool, brSemidetNum, brSemidetStr,
    brSemidetBool ]

private def fixtureRules : List RuleSchema :=
  [ fixtureNomNewtype, fixtureNomAlias, fixtureSymDecls ]

/-- The complete EXPORT definition consumed by the artifact generator.  The
core grammar and calculus grow together in one flat record. -/
abbrev guardDefinition : CalculusLanguageDef :=
  { TypeSystemGSLT.definition with
    name := "petta-typecheck-v2-guard"
    terms := TypeSystemGSLT.definition.terms ++ newTerms
    judgments := TypeSystemGSLT.definition.judgments ++ newJudgments
    rules := TypeSystemGSLT.definition.rules ++ exportRules }

/-- Object-language view retained for existing consumers. -/
abbrev guardLanguage : LanguageDef := guardDefinition.toLanguageDef

/-- Calculus view retained for existing consumers. -/
abbrev guardCalculus :
    Mettapedia.GSLT.LanguageDef.InferenceExtension.ProofCalculus :=
  guardDefinition.toCalculus

/-- The RECEIPT definition adds only the environment fixtures. -/
private abbrev receiptDefinition : CalculusLanguageDef :=
  { guardDefinition with
    rules := guardDefinition.rules ++ fixtureRules }

private abbrev receiptLanguage : LanguageDef :=
  receiptDefinition.toLanguageDef

private abbrev receiptCalculus :
    Mettapedia.GSLT.LanguageDef.InferenceExtension.ProofCalculus :=
  receiptDefinition.toCalculus

abbrev guardPresentation : Presentation := guardDefinition.toNested
private abbrev receiptPresentation : Presentation := receiptDefinition.toNested

/-! ## Receipts -/

theorem guard_language_validate : guardLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly guardLanguage <;>
    simp [newTerms, termType,
      termConstructor, LanguageDef.typeNames, TypeDecl.plain,
      TermParam.typeExpr, TypeExpr.baseNames]

theorem receipt_language_validate : receiptLanguage.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorOnly receiptLanguage <;>
    simp [newTerms, termType, termConstructor,
      LanguageDef.typeNames, TypeDecl.plain, TermParam.typeExpr,
      TypeExpr.baseNames]

/-- The export rule list is literally a prefix of the receipt rule list;
the delta is exactly the three environment fixtures. -/
theorem export_rules_are_receipt_prefix :
    receiptCalculus.rules = guardCalculus.rules ++ fixtureRules := by rfl

/-- Inventory pins. -/
theorem guard_constructor_count : guardLanguage.terms.length = 43 := by decide
theorem guard_rule_count : guardCalculus.rules.length = 72 := by decide

set_option maxRecDepth 32768 in
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
theorem guard_presentation_valid : guardPresentation.isValidV2 = true := by
  have hvalidate : guardPresentation.language.validate = [] := by
    exact guard_language_validate
  unfold Presentation.isValidV2 Presentation.isValidV1
  rw [hvalidate]
  simp [guardPresentation,
    Presentation.ruleIds, Presentation.judgmentSignatureValid,
    Presentation.judgmentHeads, Presentation.conversionDeclarationValid,
    Presentation.lookupJudgment?, RuleSchema.isValidIn,
    RuleSchema.isValidV1,
    RuleSchema.metavariableNames, RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Presentation.judgmentSchemaValid, fixedConstructorsValid,
    fixedConstructorListsValid, languageHasConstructorArity,
    Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, Pattern.zipHead, Pattern.mapHead,
    Pattern.evalHead,
    newTerms, newJudgments, exportRules, termType,
    termConstructor, consistentRefl, consistentDynLeft,
    consistentDynRight, consistentUnionRight, consistentUnionLeft,
    consistentBrand, consistentArrow, consistentListNil,
    consistentListCons, unionMemberHere, unionMemberThere, hasTypeNum,
    hasTypeStr, hasTypeTrue, hasTypeFalse, hasTypeWildcard, hasTypeUnion,
    hasTypeBrand, hasTypeNilList, hasTypeConsList, guardPassesRule, tNum,
    tStr, tBool, tUndefined, tNil, tCons, tUnion, tArrow, tBrand, tList,
    mDet, mSemidet, edgeExact, edgeStructural,
    edgeDynamic, vNum, vStr, vTrue, vFalse, vNil, vCons,
    consistent, consistentList, unionMember, valueHasType, guardPasses,
    baseSortNum, baseSortStr, baseSortTrue, baseSortFalse, scNumStr,
    scNumBool, scStrNum, scStrBool, scBoolNum, scBoolStr, scUnionRight,
    scUnionLeft, scNewtypeFormal, scAliasFormal, scNewtypeSort,
    scAliasSort, caNil, caCons, calNil, calCons, dmBase, dmCtor, dmUnion,
    dmListLiteral, dmListHere, dmListThere, dmNewtypeFormal,
    dmAliasFormal, dmDeclaredSymbol, dmAppliedHead, maNil, maCons,
    dcsCons, dcrNil, dcrCons, hcsHere, hcsSkip, hcrNil, hcrCons, hcrSkip,
    allNil, allCons, aldNilSucc, aldConsZero, aldConsRec, brDetNum,
    brDetStr, brDetBool, brSemidetNum, brSemidetStr, brSemidetBool,
    baseSortOf,
    sortConflicts, conflictsAll, conflictsAllL, definiteMismatch,
    mismatchAll, declaredConflictSome, declaredConflictRest,
    headConflictSome, headConflictRest, argListLen, argListLenDiffers,
    boundnessRefuted, envDeclared, envDeclaredList, fz, fs, dNil, dCons,
    declOf,
    tNominal, tNewtype, tAlias, tCtor, vSym, vApp,
    ruleId]
  decide

/-- Admission stated on the one flat definition rather than its derived
checker view. -/
theorem guard_definition_admitted : guardDefinition.isAdmitted = true :=
  guard_presentation_valid

/-- The complete guard language as one GSLT. -/
def guardTotalTheory : Mettapedia.GSLT.GSLT :=
  guardDefinition.toGSLTOfNoEquations guard_definition_admitted rfl

/-- The total carrier contains authored object patterns and proof-obligation
states. -/
theorem guardTotalTheory_Term :
    guardTotalTheory.Term = (Pattern ⊕ List Pattern) :=
  rfl

set_option maxRecDepth 32768 in
set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxHeartbeats 2000000 in
theorem receipt_presentation_valid : receiptPresentation.isValidV2 = true := by
  have hvalidate : receiptPresentation.language.validate = [] := by
    exact receipt_language_validate
  unfold Presentation.isValidV2 Presentation.isValidV1
  rw [hvalidate]
  simp [receiptPresentation,
    Presentation.ruleIds, Presentation.judgmentSignatureValid,
    Presentation.judgmentHeads, Presentation.conversionDeclarationValid,
    Presentation.lookupJudgment?, RuleSchema.isValidIn,
    RuleSchema.isValidV1,
    RuleSchema.metavariableNames, RuleSchema.occurrences, RuleSchema.patterns,
    patternMetavariableOccurrencesAt, patternsMetavariableOccurrencesAt,
    patternHasNoCollectionRest, patternsHaveNoCollectionRest,
    Presentation.judgmentSchemaValid, fixedConstructorsValid,
    fixedConstructorListsValid, languageHasConstructorArity,
    Pattern.isWellScoped, Pattern.isWellScopedAt, Pattern.isWellScopedListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList, Pattern.zipHead, Pattern.mapHead,
    Pattern.evalHead,
    newTerms, newJudgments, exportRules, fixtureRules, termType,
    termConstructor, consistentRefl, consistentDynLeft,
    consistentDynRight, consistentUnionRight, consistentUnionLeft,
    consistentBrand, consistentArrow, consistentListNil,
    consistentListCons, unionMemberHere, unionMemberThere, hasTypeNum,
    hasTypeStr, hasTypeTrue, hasTypeFalse, hasTypeWildcard, hasTypeUnion,
    hasTypeBrand, hasTypeNilList, hasTypeConsList, guardPassesRule, tNum,
    tStr, tBool, tUndefined, tNil, tCons, tUnion, tArrow, tBrand, tList,
    mDet, mSemidet, edgeExact, edgeStructural,
    edgeDynamic, vNum, vStr, vTrue, vFalse, vNil, vCons,
    consistent, consistentList, unionMember, valueHasType, guardPasses,
    baseSortNum, baseSortStr, baseSortTrue, baseSortFalse, scNumStr,
    scNumBool, scStrNum, scStrBool, scBoolNum, scBoolStr, scUnionRight,
    scUnionLeft, scNewtypeFormal, scAliasFormal, scNewtypeSort,
    scAliasSort, caNil, caCons, calNil, calCons, dmBase, dmCtor, dmUnion,
    dmListLiteral, dmListHere, dmListThere, dmNewtypeFormal,
    dmAliasFormal, dmDeclaredSymbol, dmAppliedHead, maNil, maCons,
    dcsCons, dcrNil, dcrCons, hcsHere, hcsSkip, hcrNil, hcrCons, hcrSkip,
    allNil, allCons, aldNilSucc, aldConsZero, aldConsRec, brDetNum,
    brDetStr, brDetBool, brSemidetNum, brSemidetStr, brSemidetBool,
    fixtureNomNewtype, fixtureNomAlias, fixtureSymDecls, baseSortOf,
    sortConflicts, conflictsAll, conflictsAllL, definiteMismatch,
    mismatchAll, declaredConflictSome, declaredConflictRest,
    headConflictSome, headConflictRest, argListLen, argListLenDiffers,
    boundnessRefuted, envDeclared, envDeclaredList, fz, fs, dNil, dCons,
    declOf,
    tNominal, tNewtype, tAlias, tCtor, vSym, vApp, nomA, nomB, symA,
    ruleId]
  decide

def guardChecked : ValidatedPresentation :=
  ⟨guardPresentation, guard_presentation_valid⟩
private def receiptChecked : ValidatedPresentation :=
  ⟨receiptPresentation, receipt_presentation_valid⟩

private def sortNumStrProof : RawProof :=
  .node { ruleId := ruleId "sc-num-str", arguments := [fz] } []

private def baseStrProof : RawProof :=
  .node { ruleId := ruleId "base-sort-str", arguments := [] } []

private def strNotNumProof : RawProof :=
  .node
    { ruleId := ruleId "dm-base", arguments := [fz, vStr, tStr, tNum] }
    [baseStrProof,
     .node { ruleId := ruleId "sc-str-num", arguments := [fz] } []]

/-- A string literal provably mismatches `Number` (the\n`fail_declared_sentinel_param` class). -/
theorem string_literal_mismatches_number :
    checkRaw receiptChecked (definiteMismatch (fs fz) vStr tNum)
      strNotNumProof = true := by
  simp [checkRaw, checkRawChildren, receiptChecked, receiptPresentation,
    exportRules, fixtureRules,
    strNotNumProof, baseStrProof, consistentRefl,
    consistentDynLeft, consistentDynRight, consistentUnionRight,
    consistentUnionLeft, consistentBrand, consistentArrow,
    consistentListNil, consistentListCons, unionMemberHere,
    unionMemberThere, hasTypeNum, hasTypeStr, hasTypeTrue, hasTypeFalse,
    hasTypeWildcard, hasTypeUnion, hasTypeBrand, hasTypeNilList,
    hasTypeConsList, guardPassesRule, baseSortNum, baseSortStr,
    baseSortTrue, baseSortFalse, scNumStr, scNumBool, scStrNum, scStrBool,
    scBoolNum, scBoolStr, scUnionRight, scUnionLeft, scNewtypeFormal,
    scAliasFormal, scNewtypeSort, scAliasSort, caNil, caCons, calNil,
    calCons, dmBase, dmCtor, dmUnion, dmListLiteral, dmListHere,
    dmListThere, dmNewtypeFormal, dmAliasFormal, dmDeclaredSymbol,
    dmAppliedHead, maNil, maCons, dcsCons, dcrNil, dcrCons, hcsHere,
    hcsSkip, hcrNil, hcrCons, hcrSkip, allNil, allCons, aldNilSucc,
    aldConsZero, aldConsRec, brDetNum, brDetStr, brDetBool, brSemidetNum,
    brSemidetStr, brSemidetBool, fixtureNomNewtype, fixtureNomAlias,
    fixtureSymDecls, instantiateRule?, Presentation.lookupRule?,
    argumentsValidAt, argumentValidAt, RuleSchema.sideConditionsHold,
    instantiateSchema?, instantiateSchemaAt?, instantiateSchemas?,
    instantiateSchemasAt?, lookupArgumentAt?, consistent, consistentList,
    unionMember, valueHasType, guardPasses, baseSortOf, sortConflicts,
    conflictsAll, conflictsAllL, definiteMismatch, mismatchAll,
    declaredConflictSome, declaredConflictRest, headConflictSome,
    headConflictRest, argListLen, argListLenDiffers, boundnessRefuted,
    envDeclared, envDeclaredList, tNum, tStr, tBool, tUndefined, tNil,
    tCons, tUnion, tArrow, tBrand, tList, mDet, mSemidet,
    edgeExact, edgeStructural, edgeDynamic, vNum, vStr, vTrue, vFalse,
    vNil, vCons, fz, fs, dNil, dCons, declOf,
    tNominal, tNewtype,
    tAlias, tCtor, vSym, vApp, nomA, nomB, symA, ruleId,
    Pattern.isGroundAt, Pattern.isGroundListAt,
    Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

private def baseNumProof : RawProof :=
  .node { ruleId := ruleId "base-sort-num", arguments := [] } []

private def literalCtorProof : RawProof :=
  .node
    { ruleId := ruleId "dm-ctor", arguments := [fz, vNum, tNum, nomA, fs fz] }
    [baseNumProof]

/-- A base literal never inhabits a constructor-shaped member (the\n`fail_union_type_mismatch` class). -/
theorem literal_never_constructor_shaped :
    checkRaw receiptChecked (definiteMismatch (fs fz) vNum (tCtor nomA (fs fz)))
      literalCtorProof = true := by
  simp [checkRaw, checkRawChildren, receiptChecked, receiptPresentation,
    exportRules, fixtureRules,
    literalCtorProof, baseNumProof, consistentRefl, consistentDynLeft,
    consistentDynRight, consistentUnionRight, consistentUnionLeft,
    consistentBrand, consistentArrow, consistentListNil,
    consistentListCons, unionMemberHere, unionMemberThere, hasTypeNum,
    hasTypeStr, hasTypeTrue, hasTypeFalse, hasTypeWildcard, hasTypeUnion,
    hasTypeBrand, hasTypeNilList, hasTypeConsList, guardPassesRule,
    baseSortNum, baseSortStr, baseSortTrue, baseSortFalse, scNumStr,
    scNumBool, scStrNum, scStrBool, scBoolNum, scBoolStr, scUnionRight,
    scUnionLeft, scNewtypeFormal, scAliasFormal, scNewtypeSort,
    scAliasSort, caNil, caCons, calNil, calCons, dmBase, dmCtor, dmUnion,
    dmListLiteral, dmListHere, dmListThere, dmNewtypeFormal,
    dmAliasFormal, dmDeclaredSymbol, dmAppliedHead, maNil, maCons,
    dcsCons, dcrNil, dcrCons, hcsHere, hcsSkip, hcrNil, hcrCons, hcrSkip,
    allNil, allCons, aldNilSucc, aldConsZero, aldConsRec, brDetNum,
    brDetStr, brDetBool, brSemidetNum, brSemidetStr, brSemidetBool,
    fixtureNomNewtype, fixtureNomAlias, fixtureSymDecls, instantiateRule?,
    Presentation.lookupRule?, argumentsValidAt, argumentValidAt,
    RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, consistent, consistentList, unionMember,
    valueHasType, guardPasses, baseSortOf, sortConflicts, conflictsAll,
    conflictsAllL, definiteMismatch, mismatchAll, declaredConflictSome,
    declaredConflictRest, headConflictSome, headConflictRest, argListLen,
    argListLenDiffers, boundnessRefuted, envDeclared, envDeclaredList,
    tNum, tStr, tBool, tUndefined, tNil, tCons, tUnion, tArrow, tBrand,
    tList, mDet, mSemidet, edgeExact, edgeStructural,
    edgeDynamic, vNum, vStr, vTrue, vFalse, vNil, vCons,
    fz, fs, dNil, dCons, declOf,
    tNominal, tNewtype, tAlias, tCtor,
    vSym, vApp, nomA, nomB, symA, ruleId, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

private def unionMembers : Pattern := tCons tStr (tCons tBool tNil)

private def numStrMismatchProof : RawProof :=
  .node
    { ruleId := ruleId "dm-base", arguments := [fz, vNum, tNum, tStr] }
    [baseNumProof,
     .node { ruleId := ruleId "sc-num-str", arguments := [fz] } []]

private def numBoolMismatchProof : RawProof :=
  .node
    { ruleId := ruleId "dm-base", arguments := [fz, vNum, tNum, tBool] }
    [baseNumProof,
     .node { ruleId := ruleId "sc-num-bool", arguments := [fz] } []]

private def maTailProof : RawProof :=
  .node
    { ruleId := ruleId "ma-cons"
      arguments := [fs fz, vNum, tBool, tNil] }
    [numBoolMismatchProof,
     .node { ruleId := ruleId "ma-nil", arguments := [fs fz, vNum] } []]

private def unionAllProof : RawProof :=
  .node
    { ruleId := ruleId "dm-union", arguments := [fs fz, vNum, unionMembers] }
    [.node
       { ruleId := ruleId "ma-cons"
         arguments := [fs fz, vNum, tStr, tCons tBool tNil] }
       [numStrMismatchProof, maTailProof]]

/-- A number mismatches `(| String Bool)`: every member provably\nconflicts. -/
theorem union_all_members_mismatch :
    checkRaw receiptChecked (definiteMismatch (fs (fs fz)) vNum (tUnion unionMembers))
      unionAllProof = true := by
  simp [checkRaw, checkRawChildren, receiptChecked, receiptPresentation,
    exportRules, fixtureRules, unionAllProof,
    unionMembers, numStrMismatchProof, numBoolMismatchProof, maTailProof,
    baseNumProof, consistentRefl, consistentDynLeft, consistentDynRight,
    consistentUnionRight, consistentUnionLeft, consistentBrand,
    consistentArrow, consistentListNil, consistentListCons,
    unionMemberHere, unionMemberThere, hasTypeNum, hasTypeStr,
    hasTypeTrue, hasTypeFalse, hasTypeWildcard, hasTypeUnion,
    hasTypeBrand, hasTypeNilList, hasTypeConsList, guardPassesRule,
    baseSortNum, baseSortStr, baseSortTrue, baseSortFalse, scNumStr,
    scNumBool, scStrNum, scStrBool, scBoolNum, scBoolStr, scUnionRight,
    scUnionLeft, scNewtypeFormal, scAliasFormal, scNewtypeSort,
    scAliasSort, caNil, caCons, calNil, calCons, dmBase, dmCtor, dmUnion,
    dmListLiteral, dmListHere, dmListThere, dmNewtypeFormal,
    dmAliasFormal, dmDeclaredSymbol, dmAppliedHead, maNil, maCons,
    dcsCons, dcrNil, dcrCons, hcsHere, hcsSkip, hcrNil, hcrCons, hcrSkip,
    allNil, allCons, aldNilSucc, aldConsZero, aldConsRec, brDetNum,
    brDetStr, brDetBool, brSemidetNum, brSemidetStr, brSemidetBool,
    fixtureNomNewtype, fixtureNomAlias, fixtureSymDecls, instantiateRule?,
    Presentation.lookupRule?, argumentsValidAt, argumentValidAt,
    RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, consistent, consistentList, unionMember,
    valueHasType, guardPasses, baseSortOf, sortConflicts, conflictsAll,
    conflictsAllL, definiteMismatch, mismatchAll, declaredConflictSome,
    declaredConflictRest, headConflictSome, headConflictRest, argListLen,
    argListLenDiffers, boundnessRefuted, envDeclared, envDeclaredList,
    tNum, tStr, tBool, tUndefined, tNil, tCons, tUnion, tArrow, tBrand,
    tList, mDet, mSemidet, edgeExact, edgeStructural,
    edgeDynamic, vNum, vStr, vTrue, vFalse, vNil, vCons,
    fz, fs, dNil, dCons, declOf,
    tNominal, tNewtype, tAlias, tCtor,
    vSym, vApp, nomA, nomB, symA, ruleId, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

private def fixtureNewtypeProof : RawProof :=
  .node { ruleId := ruleId "fixture-nom-newtype", arguments := [] } []

private def newtypeResolvedProof : RawProof :=
  .node
    { ruleId := ruleId "dm-newtype-formal"
      arguments := [fs fz, vStr, nomA, tNum] }
    [fixtureNewtypeProof, strNotNumProof]

/-- A declared newtype formal resolves to its representation before the\nmismatch is judged (fixture environment). -/
theorem newtype_resolves_before_judging :
    checkRaw receiptChecked (definiteMismatch (fs (fs fz)) vStr (tNominal nomA))
      newtypeResolvedProof = true := by
  simp [checkRaw, checkRawChildren, receiptChecked, receiptPresentation,
    exportRules, fixtureRules,
    newtypeResolvedProof, fixtureNewtypeProof, strNotNumProof,
    baseStrProof, consistentRefl, consistentDynLeft, consistentDynRight,
    consistentUnionRight, consistentUnionLeft, consistentBrand,
    consistentArrow, consistentListNil, consistentListCons,
    unionMemberHere, unionMemberThere, hasTypeNum, hasTypeStr,
    hasTypeTrue, hasTypeFalse, hasTypeWildcard, hasTypeUnion,
    hasTypeBrand, hasTypeNilList, hasTypeConsList, guardPassesRule,
    baseSortNum, baseSortStr, baseSortTrue, baseSortFalse, scNumStr,
    scNumBool, scStrNum, scStrBool, scBoolNum, scBoolStr, scUnionRight,
    scUnionLeft, scNewtypeFormal, scAliasFormal, scNewtypeSort,
    scAliasSort, caNil, caCons, calNil, calCons, dmBase, dmCtor, dmUnion,
    dmListLiteral, dmListHere, dmListThere, dmNewtypeFormal,
    dmAliasFormal, dmDeclaredSymbol, dmAppliedHead, maNil, maCons,
    dcsCons, dcrNil, dcrCons, hcsHere, hcsSkip, hcrNil, hcrCons, hcrSkip,
    allNil, allCons, aldNilSucc, aldConsZero, aldConsRec, brDetNum,
    brDetStr, brDetBool, brSemidetNum, brSemidetStr, brSemidetBool,
    fixtureNomNewtype, fixtureNomAlias, fixtureSymDecls, instantiateRule?,
    Presentation.lookupRule?, argumentsValidAt, argumentValidAt,
    RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, consistent, consistentList, unionMember,
    valueHasType, guardPasses, baseSortOf, sortConflicts, conflictsAll,
    conflictsAllL, definiteMismatch, mismatchAll, declaredConflictSome,
    declaredConflictRest, headConflictSome, headConflictRest, argListLen,
    argListLenDiffers, boundnessRefuted, envDeclared, envDeclaredList,
    tNum, tStr, tBool, tUndefined, tNil, tCons, tUnion, tArrow, tBrand,
    tList, mDet, mSemidet, edgeExact, edgeStructural,
    edgeDynamic, vNum, vStr, vTrue, vFalse, vNil, vCons,
    fz, fs, dNil, dCons, declOf,
    tNominal, tNewtype, tAlias, tCtor,
    vSym, vApp, nomA, nomB, symA, ruleId, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

private def fixtureSymProof : RawProof :=
  .node { ruleId := ruleId "fixture-sym-decls", arguments := [] } []

private def symDeclConflictProof : RawProof :=
  .node
    { ruleId := ruleId "dcs-cons"
      arguments := [fz, symA, tStr, dNil, tNum] }
    [.node { ruleId := ruleId "sc-str-num", arguments := [fz] } [],
     .node { ruleId := ruleId "dcr-nil", arguments := [fz, tNum] } []]

private def declaredSymbolProof : RawProof :=
  .node
    { ruleId := ruleId "dm-declared-symbol"
      arguments := [fz, symA, dCons (declOf symA tStr) dNil, tNum] }
    [fixtureSymProof, symDeclConflictProof]

/-- A symbol whose every declaration conflicts with the formal is a\nprovable mismatch (the declared-promise conflict). -/
theorem declared_symbol_conflict :
    checkRaw receiptChecked (definiteMismatch (fs fz) (vSym symA) tNum)
      declaredSymbolProof = true := by
  simp [checkRaw, checkRawChildren, receiptChecked, receiptPresentation,
    exportRules, fixtureRules,
    declaredSymbolProof, fixtureSymProof, symDeclConflictProof,
    consistentRefl, consistentDynLeft, consistentDynRight,
    consistentUnionRight, consistentUnionLeft, consistentBrand,
    consistentArrow, consistentListNil, consistentListCons,
    unionMemberHere, unionMemberThere, hasTypeNum, hasTypeStr,
    hasTypeTrue, hasTypeFalse, hasTypeWildcard, hasTypeUnion,
    hasTypeBrand, hasTypeNilList, hasTypeConsList, guardPassesRule,
    baseSortNum, baseSortStr, baseSortTrue, baseSortFalse, scNumStr,
    scNumBool, scStrNum, scStrBool, scBoolNum, scBoolStr, scUnionRight,
    scUnionLeft, scNewtypeFormal, scAliasFormal, scNewtypeSort,
    scAliasSort, caNil, caCons, calNil, calCons, dmBase, dmCtor, dmUnion,
    dmListLiteral, dmListHere, dmListThere, dmNewtypeFormal,
    dmAliasFormal, dmDeclaredSymbol, dmAppliedHead, maNil, maCons,
    dcsCons, dcrNil, dcrCons, hcsHere, hcsSkip, hcrNil, hcrCons, hcrSkip,
    allNil, allCons, aldNilSucc, aldConsZero, aldConsRec, brDetNum,
    brDetStr, brDetBool, brSemidetNum, brSemidetStr, brSemidetBool,
    fixtureNomNewtype, fixtureNomAlias, fixtureSymDecls, instantiateRule?,
    Presentation.lookupRule?, argumentsValidAt, argumentValidAt,
    RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, consistent, consistentList, unionMember,
    valueHasType, guardPasses, baseSortOf, sortConflicts, conflictsAll,
    conflictsAllL, definiteMismatch, mismatchAll, declaredConflictSome,
    declaredConflictRest, headConflictSome, headConflictRest, argListLen,
    argListLenDiffers, boundnessRefuted, envDeclared, envDeclaredList,
    tNum, tStr, tBool, tUndefined, tNil, tCons, tUnion, tArrow, tBrand,
    tList, mDet, mSemidet, edgeExact, edgeStructural,
    edgeDynamic, vNum, vStr, vTrue, vFalse, vNil, vCons,
    fz, fs, dNil, dCons, declOf,
    tNominal, tNewtype, tAlias, tCtor,
    vSym, vApp, nomA, nomB, symA, ruleId, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

private def boundnessProof : RawProof :=
  .node { ruleId := ruleId "br-det-bool", arguments := [] } []

/-- A `-[det]->` Bool formal demands a bound argument (the\n`fail_unbound_det_argument` class). -/
theorem committed_bool_requires_bound :
    checkRaw receiptChecked (boundnessRefuted mDet tBool)
      boundnessProof = true := by
  simp [checkRaw, checkRawChildren, receiptChecked, receiptPresentation,
    exportRules, fixtureRules,
    boundnessProof, consistentRefl, consistentDynLeft, consistentDynRight,
    consistentUnionRight, consistentUnionLeft, consistentBrand,
    consistentArrow, consistentListNil, consistentListCons,
    unionMemberHere, unionMemberThere, hasTypeNum, hasTypeStr,
    hasTypeTrue, hasTypeFalse, hasTypeWildcard, hasTypeUnion,
    hasTypeBrand, hasTypeNilList, hasTypeConsList, guardPassesRule,
    baseSortNum, baseSortStr, baseSortTrue, baseSortFalse, scNumStr,
    scNumBool, scStrNum, scStrBool, scBoolNum, scBoolStr, scUnionRight,
    scUnionLeft, scNewtypeFormal, scAliasFormal, scNewtypeSort,
    scAliasSort, caNil, caCons, calNil, calCons, dmBase, dmCtor, dmUnion,
    dmListLiteral, dmListHere, dmListThere, dmNewtypeFormal,
    dmAliasFormal, dmDeclaredSymbol, dmAppliedHead, maNil, maCons,
    dcsCons, dcrNil, dcrCons, hcsHere, hcsSkip, hcrNil, hcrCons, hcrSkip,
    allNil, allCons, aldNilSucc, aldConsZero, aldConsRec, brDetNum,
    brDetStr, brDetBool, brSemidetNum, brSemidetStr, brSemidetBool,
    fixtureNomNewtype, fixtureNomAlias, fixtureSymDecls, instantiateRule?,
    Presentation.lookupRule?, argumentsValidAt,
    RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    consistent, consistentList, unionMember,
    valueHasType, guardPasses, baseSortOf, sortConflicts, conflictsAll,
    conflictsAllL, definiteMismatch, mismatchAll, declaredConflictSome,
    declaredConflictRest, headConflictSome, headConflictRest, argListLen,
    argListLenDiffers, boundnessRefuted, envDeclared, envDeclaredList,
    tNum, tStr, tBool, tUndefined, tNil, tCons, tUnion, tArrow, tBrand,
    tList, mDet, mSemidet, edgeExact, edgeStructural,
    edgeDynamic, vNum, vStr, vTrue, vFalse, vNil, vCons,
    fz, fs, dNil, dCons, declOf,
    tNominal, tNewtype, tAlias, tCtor,
    vSym, vApp, nomA, nomB, symA, ruleId]

/-! ## Negative receipts: humility preserved.  Exhaustive impossibility
remains the stage-2 soundness layer's obligation. -/

private def undeclaredNominalCandidate : RawProof :=
  .node
    { ruleId := ruleId "dm-newtype-formal"
      arguments := [fz, vNum, nomB, tNum] }
    [.node { ruleId := ruleId "fixture-nom-newtype", arguments := [] } [],
     .node { ruleId := ruleId "base-sort-num", arguments := [] } []]

/-- `NomB` is declared as an Alias fixture, not a Newtype: the newtype\nresolution candidate cannot instantiate, so the nominal stays open\n(humility: no false trip). -/
theorem undeclared_nominal_stays_open :
    checkRaw receiptChecked (definiteMismatch (fs fz) vNum (tNominal nomB))
      undeclaredNominalCandidate = false := by
  simp [checkRaw, checkRawChildren, receiptChecked, receiptPresentation,
    exportRules, fixtureRules,
    undeclaredNominalCandidate, consistentRefl, consistentDynLeft,
    consistentDynRight, consistentUnionRight, consistentUnionLeft,
    consistentBrand, consistentArrow, consistentListNil,
    consistentListCons, unionMemberHere, unionMemberThere, hasTypeNum,
    hasTypeStr, hasTypeTrue, hasTypeFalse, hasTypeWildcard, hasTypeUnion,
    hasTypeBrand, hasTypeNilList, hasTypeConsList, guardPassesRule,
    baseSortNum, baseSortStr, baseSortTrue, baseSortFalse, scNumStr,
    scNumBool, scStrNum, scStrBool, scBoolNum, scBoolStr, scUnionRight,
    scUnionLeft, scNewtypeFormal, scAliasFormal, scNewtypeSort,
    scAliasSort, caNil, caCons, calNil, calCons, dmBase, dmCtor, dmUnion,
    dmListLiteral, dmListHere, dmListThere, dmNewtypeFormal,
    dmAliasFormal, dmDeclaredSymbol, dmAppliedHead, maNil, maCons,
    dcsCons, dcrNil, dcrCons, hcsHere, hcsSkip, hcrNil, hcrCons, hcrSkip,
    allNil, allCons, aldNilSucc, aldConsZero, aldConsRec, brDetNum,
    brDetStr, brDetBool, brSemidetNum, brSemidetStr, brSemidetBool,
    fixtureNomNewtype, fixtureNomAlias, fixtureSymDecls, instantiateRule?,
    Presentation.lookupRule?, argumentsValidAt, argumentValidAt,
    RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, consistent, consistentList, unionMember,
    valueHasType, guardPasses, baseSortOf, sortConflicts, conflictsAll,
    conflictsAllL, definiteMismatch, mismatchAll, declaredConflictSome,
    declaredConflictRest, headConflictSome, headConflictRest, argListLen,
    argListLenDiffers, boundnessRefuted, envDeclared, envDeclaredList,
    tNum, tStr, tBool, tUndefined, tNil, tCons, tUnion, tArrow, tBrand,
    tList, mDet, mSemidet, edgeExact, edgeStructural,
    edgeDynamic, vNum, vStr, vTrue, vFalse, vNil, vCons,
    fz, fs, dNil, dCons, declOf,
    tNominal, tNewtype, tAlias, tCtor,
    vSym, vApp, nomA, nomB, symA, ruleId, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

private def sameBaseCandidate : RawProof :=
  .node
    { ruleId := ruleId "dm-base", arguments := [fz, vNum, tNum, tNum] }
    [.node { ruleId := ruleId "base-sort-num", arguments := [] } [],
     .node { ruleId := ruleId "sc-num-str", arguments := [fz] } []]

/-- `Number` against `Number`: the conflict premise cannot be discharged\nby any base rule (the candidate's child concludes the wrong pair). -/
theorem same_base_sort_never_mismatches :
    checkRaw receiptChecked (definiteMismatch (fs fz) vNum tNum)
      sameBaseCandidate = false := by
  simp [checkRaw, checkRawChildren, receiptChecked, receiptPresentation,
    exportRules, fixtureRules,
    sameBaseCandidate, consistentRefl, consistentDynLeft,
    consistentDynRight, consistentUnionRight, consistentUnionLeft,
    consistentBrand, consistentArrow, consistentListNil,
    consistentListCons, unionMemberHere, unionMemberThere, hasTypeNum,
    hasTypeStr, hasTypeTrue, hasTypeFalse, hasTypeWildcard, hasTypeUnion,
    hasTypeBrand, hasTypeNilList, hasTypeConsList, guardPassesRule,
    baseSortNum, baseSortStr, baseSortTrue, baseSortFalse, scNumStr,
    scNumBool, scStrNum, scStrBool, scBoolNum, scBoolStr, scUnionRight,
    scUnionLeft, scNewtypeFormal, scAliasFormal, scNewtypeSort,
    scAliasSort, caNil, caCons, calNil, calCons, dmBase, dmCtor, dmUnion,
    dmListLiteral, dmListHere, dmListThere, dmNewtypeFormal,
    dmAliasFormal, dmDeclaredSymbol, dmAppliedHead, maNil, maCons,
    dcsCons, dcrNil, dcrCons, hcsHere, hcsSkip, hcrNil, hcrCons, hcrSkip,
    allNil, allCons, aldNilSucc, aldConsZero, aldConsRec, brDetNum,
    brDetStr, brDetBool, brSemidetNum, brSemidetStr, brSemidetBool,
    fixtureNomNewtype, fixtureNomAlias, fixtureSymDecls, instantiateRule?,
    Presentation.lookupRule?, argumentsValidAt, argumentValidAt,
    RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, consistent, consistentList, unionMember,
    valueHasType, guardPasses, baseSortOf, sortConflicts, conflictsAll,
    conflictsAllL, definiteMismatch, mismatchAll, declaredConflictSome,
    declaredConflictRest, headConflictSome, headConflictRest, argListLen,
    argListLenDiffers, boundnessRefuted, envDeclared, envDeclaredList,
    tNum, tStr, tBool, tUndefined, tNil, tCons, tUnion, tArrow, tBrand,
    tList, mDet, mSemidet, edgeExact, edgeStructural,
    edgeDynamic, vNum, vStr, vTrue, vFalse, vNil, vCons,
    fz, fs, dNil, dCons, declOf,
    tNominal, tNewtype, tAlias, tCtor,
    vSym, vApp, nomA, nomB, symA, ruleId, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

private def vetoCandidate : RawProof :=
  .node
    { ruleId := ruleId "dcs-cons"
      arguments := [fz, symA, tUndefined, dNil, tNum] }
    [.node { ruleId := ruleId "sc-num-str", arguments := [fz] } [],
     .node { ruleId := ruleId "dcr-nil", arguments := [fz, tNum] } []]

/-- A wildcard-typed declaration cannot conflict: `SortConflicts` has no\nrule with `%Undefined%` on the left, so the placeable quantifier's\npremise fails and the guard passes. -/
theorem unplaceable_declaration_vetoes :
    checkRaw receiptChecked (declaredConflictSome fz (dCons (declOf symA tUndefined) dNil) tNum)
      vetoCandidate = false := by
  simp [checkRaw, checkRawChildren, receiptChecked, receiptPresentation,
    exportRules, fixtureRules, vetoCandidate,
    consistentRefl, consistentDynLeft, consistentDynRight,
    consistentUnionRight, consistentUnionLeft, consistentBrand,
    consistentArrow, consistentListNil, consistentListCons,
    unionMemberHere, unionMemberThere, hasTypeNum, hasTypeStr,
    hasTypeTrue, hasTypeFalse, hasTypeWildcard, hasTypeUnion,
    hasTypeBrand, hasTypeNilList, hasTypeConsList, guardPassesRule,
    baseSortNum, baseSortStr, baseSortTrue, baseSortFalse, scNumStr,
    scNumBool, scStrNum, scStrBool, scBoolNum, scBoolStr, scUnionRight,
    scUnionLeft, scNewtypeFormal, scAliasFormal, scNewtypeSort,
    scAliasSort, caNil, caCons, calNil, calCons, dmBase, dmCtor, dmUnion,
    dmListLiteral, dmListHere, dmListThere, dmNewtypeFormal,
    dmAliasFormal, dmDeclaredSymbol, dmAppliedHead, maNil, maCons,
    dcsCons, dcrNil, dcrCons, hcsHere, hcsSkip, hcrNil, hcrCons, hcrSkip,
    allNil, allCons, aldNilSucc, aldConsZero, aldConsRec, brDetNum,
    brDetStr, brDetBool, brSemidetNum, brSemidetStr, brSemidetBool,
    fixtureNomNewtype, fixtureNomAlias, fixtureSymDecls, instantiateRule?,
    Presentation.lookupRule?, argumentsValidAt, argumentValidAt,
    RuleSchema.sideConditionsHold, instantiateSchema?,
    instantiateSchemaAt?, instantiateSchemas?, instantiateSchemasAt?,
    lookupArgumentAt?, consistent, consistentList, unionMember,
    valueHasType, guardPasses, baseSortOf, sortConflicts, conflictsAll,
    conflictsAllL, definiteMismatch, mismatchAll, declaredConflictSome,
    declaredConflictRest, headConflictSome, headConflictRest, argListLen,
    argListLenDiffers, boundnessRefuted, envDeclared, envDeclaredList,
    tNum, tStr, tBool, tUndefined, tNil, tCons, tUnion, tArrow, tBrand,
    tList, mDet, mSemidet, edgeExact, edgeStructural,
    edgeDynamic, vNum, vStr, vTrue, vFalse, vNil, vCons,
    fz, fs, dNil, dCons, declOf,
    tNominal, tNewtype, tAlias, tCtor,
    vSym, vApp, nomA, nomB, symA, ruleId, Pattern.isGroundAt,
    Pattern.isGroundListAt, Pattern.hasCanonicalBinderMetadata,
    Pattern.hasCanonicalBinderMetadataList]

/-! ## Syntax-mapping tables (root-carried; the exporter GENERATES the
runtime reifier from these, so syntax-to-algebra bridging is data of the
presentation, never hand-written runtime semantics) -/

/-- Base syntax type names and their root constructors. -/
def syntaxBaseTypeTable : List (String × String) :=
  [("Number", "TNum"), ("String", "TStr"), ("Bool", "TBool"),
   ("%Undefined%", "TUndefined")]

/-- Source arrow heads and their root mode atoms
(`flags_arrows.pl:72-92`). -/
def syntaxModeTable : List (String × String) :=
  [("->", "MPlain"), ("-[det]->", "MDet"), ("-[semidet]->", "MSemidet"),
   ("-[nondet]->", "MNondet")]

theorem syntax_base_table_length : syntaxBaseTypeTable.length = 4 := by
  decide
theorem syntax_mode_table_length : syntaxModeTable.length = 4 := by decide

/-- Every base-table target is a declared 0-ary constructor of the guard
language: the lexical table is CONNECTED to the presentation, not adjacent
to it. -/
theorem syntax_base_targets_are_constructors :
    syntaxBaseTypeTable.all (fun entry =>
      guardLanguage.terms.any (fun term =>
        term.label == entry.2 && term.params.length == 0)) = true := by
  decide

/-- Every mode-table target is a declared 0-ary constructor of the guard
language. -/
theorem syntax_mode_targets_are_constructors :
    syntaxModeTable.all (fun entry =>
      guardLanguage.terms.any (fun term =>
        term.label == entry.2 && term.params.length == 0)) = true := by
  decide

/-! ## Audit interface: receipt presentation + sample derivations for the
operational generic checker (the guard-level GIC projection) -/

def auditPresentation : Presentation := receiptPresentation
def auditSampleMismatchGoal : Pattern := definiteMismatch (fs fz) vStr tNum
def auditSampleMismatchProof : RawProof := strNotNumProof
def auditSampleBoundnessGoal : Pattern := boundnessRefuted mDet tBool
def auditSampleBoundnessProof : RawProof := boundnessProof
def auditSampleNewtypeGoal : Pattern :=
  definiteMismatch (fs (fs fz)) vStr (tNominal nomA)
def auditSampleNewtypeProof : RawProof := newtypeResolvedProof
def auditSampleVetoGoal : Pattern :=
  declaredConflictSome fz (dCons (declOf symA tUndefined) dNil) tNum
def auditSampleVetoProof : RawProof := vetoCandidate
def auditSampleSameBaseGoal : Pattern := definiteMismatch (fs fz) vNum tNum
def auditSampleSameBaseProof : RawProof := sameBaseCandidate

end Mettapedia.Languages.MeTTa.PeTTa.TypeSystemGSLTGuard
