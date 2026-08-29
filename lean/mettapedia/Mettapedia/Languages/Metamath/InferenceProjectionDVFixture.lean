import Mettapedia.Languages.Metamath.InferenceProjection

/-!
# Real Metamath disjoint-variable projection fixture

This fixture embeds the exact upstream 532-byte
`test_dv_yz_required.mm`.  Its parser prefix stops immediately after the
active `th.1` essential hypothesis, before `th` is inserted.  The open block
is intentional: `feedAll` exposes the live pre-insertion database, while
calling `done` there would report an unclosed block.

The generated presentation is then used directly to check a proof tree for
the source token sequence `wy wz th.1 ax-yz`.  A second tree represents the
real mutation `wy wy th.1 ax-yz`; all of its non-DV computations target the
substituted result `|- y`, and its explicit DV subtree fails only when it tries
to establish the absent self-pair `(y,y)`.
-/

namespace Mettapedia.Languages.Metamath.InferenceProjectionDVFixture

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceEncoding.Builder
open Mettapedia.Languages.Metamath.InferenceSideConditions
open Mettapedia.Languages.Metamath.InferenceProjection

/-! ## Exact source and live parser prefix -/

def fixturePrefix : String :=
  "$( Test for DV pairwise expansion: $d x y z $. should create pair (y,z)\n" ++
  "   This test REQUIRES (y,z) to be disjoint - will FAIL if pairwise expansion broken $)\n" ++
  "\n" ++
  "$c wff |- $.\n" ++
  "$v x y z $.\n" ++
  "\n" ++
  "wx $f wff x $.\n" ++
  "wy $f wff y $.\n" ++
  "wz $f wff z $.\n" ++
  "\n" ++
  "$( Key axiom: requires y and z to be disjoint $)\n" ++
  "${\n" ++
  "  $d y z $.\n" ++
  "  ax-yz.1 $e |- y $.\n" ++
  "  ax-yz $a |- z $.\n" ++
  "$}\n" ++
  "\n" ++
  "$( Theorem using multi-variable $d declaration\n" ++
  "   The $d x y z $. MUST expand to include (y,z) for this to verify! $)\n" ++
  "${\n" ++
  "  $d x y z $.\n" ++
  "  th.1 $e |- y $.\n"

def fixtureSuffix : String :=
  "  th $p |- z $= wy wz th.1 ax-yz $.\n" ++
  "$}\n"

def fixtureSource : String := fixturePrefix ++ fixtureSuffix

#guard fixturePrefix.toUTF8.size == 493
#guard fixtureSuffix.toUTF8.size == 39
#guard fixtureSource.toUTF8.size == 532

def initialParserState : Metamath.Verify.ParserState :=
  { (default : Metamath.Verify.ParserState) with
    db := { (default : RuntimeDB) with config := .soundDefault } }

/-- The actual live state obtained by parsing the exact source prefix. -/
def prefixState : Metamath.Verify.ParserState :=
  initialParserState.feedAll 0 fixturePrefix.toUTF8

def prefixDB : RuntimeDB := prefixState.db

def expectedCallerDV : Array (String × String) :=
  #[ ("x", "y"), ("x", "z"), ("y", "z") ]

def expectedCallerHyps : Array String :=
  #["wx", "wy", "wz", "th.1"]

def expectedAxYZDV : Array (String × String) := #[ ("y", "z") ]
def expectedAxYZHyps : Array String := #["wy", "wz", "ax-yz.1"]

def axYZObjectMatches : Bool :=
  match prefixDB.find? "ax-yz" with
  | some (.assert formula frame embeddedLabel) =>
      formula == #[.const "|-", .var "z"] &&
        frame.dj == expectedAxYZDV &&
        frame.hyps == expectedAxYZHyps &&
        embeddedLabel == "ax-yz"
  | _ => false

#guard prefixDB.error?.isNone
#guard (prefixDB.find? "th").isNone
#guard prefixDB.frame.dj == expectedCallerDV
#guard prefixDB.frame.hyps == expectedCallerHyps
#guard axYZObjectMatches
#guard (projectForFreshTarget? prefixDB "th").isSome

def fullFixtureDB : RuntimeDB :=
  Metamath.Verify.checkBytes fixtureSource.toUTF8 .soundDefault

#guard fullFixtureDB.error?.isNone
#guard (fullFixtureDB.find? "th").isSome

/-! ## Generated source-rule inspection -/

private def rid (value : String) : RuleId := { value }

def axYZRule? : Option RuleSchema := do
  let presentation ← rawDefinition? prefixDB
  presentation.lookupRule? (rid "ax-yz")

private def name (value : String) : Pattern := encodeString value
private def bodyVar (value : String) : Pattern :=
  Builder.cons (Builder.varSym (name value)) Builder.nil

def expectedAxYZProvesPremises : List Pattern :=
  [ proves (Builder.formula (name "wff") (.fvar (hypothesisBodyFormalName 0)))
  , proves (Builder.formula (name "wff") (.fvar (hypothesisBodyFormalName 1)))
  , proves (Builder.formula (name "|-") (.fvar (hypothesisBodyFormalName 2))) ]

def axYZRuleShapeMatches : Bool :=
  match axYZRule? with
  | some rule =>
      rule.id.value == "ax-yz" &&
        rule.metavariables ==
          [ (hypothesisBodyFormalName 0, 0)
          , (hypothesisBodyFormalName 1, 0)
          , (hypothesisBodyFormalName 2, 0)
          , (conclusionBodyFormalName, 0) ] &&
        rule.premises.take 3 == expectedAxYZProvesPremises
  | none => false

#guard axYZRuleShapeMatches

/-! ## Explicit lowering of `wy wz th.1 ax-yz` -/

def proofTokens : List String := ["wy", "wz", "th.1", "ax-yz"]
def mutatedProofTokens : List String := ["wy", "wy", "th.1", "ax-yz"]

private def proofNode (rule : String) (arguments : List Pattern)
    (children : List RawProof := []) : RawProof :=
  .node { ruleId := rid rule, arguments } children

private def tcWff : Pattern := name "wff"
private def tcProvable : Pattern := name "|-"
private def yName : Pattern := name "y"
private def zName : Pattern := name "z"
private def ySymbol : Pattern := Builder.varSym yName
private def zSymbol : Pattern := Builder.varSym zName
private def bodyY : Pattern := bodyVar "y"
private def bodyZ : Pattern := bodyVar "z"

private def formulaWffY : Pattern := Builder.formula tcWff bodyY
private def formulaWffZ : Pattern := Builder.formula tcWff bodyZ
private def formulaProvableY : Pattern := Builder.formula tcProvable bodyY
private def formulaProvableZ : Pattern := Builder.formula tcProvable bodyZ

private def bindingY : Pattern := Builder.binding yName formulaWffY
private def bindingZWith (imageBody : Pattern) : Pattern :=
  Builder.binding zName (Builder.formula tcWff imageBody)
private def bindingsTailWith (zImageBody : Pattern) : Pattern :=
  Builder.cons (bindingZWith zImageBody) Builder.nil
private def bindingsWith (zImageBody : Pattern) : Pattern :=
  Builder.cons bindingY (bindingsTailWith zImageBody)
private def substitutionWith (zImageBody : Pattern) : Pattern :=
  Builder.substitution (bindingsWith zImageBody)

private def positiveSubstitution : Pattern := substitutionWith bodyZ
private def mutatedSubstitution : Pattern := substitutionWith bodyY

private def wyProof : RawProof := proofNode "wy" []
private def wzProof : RawProof := proofNode "wz" []
private def thEssentialProof : RawProof := proofNode "th.1" []

private def appendSingletonProof (symbol : Pattern) : RawProof :=
  proofNode "$mm.append.cons"
    [symbol, Builder.nil, Builder.nil, Builder.nil]
    [proofNode "$mm.append.nil" [Builder.nil]]

private def lookupYProof (zImageBody : Pattern) : RawProof :=
  proofNode "$mm.lookup.here"
    [yName, tcWff, bodyY, bindingsTailWith zImageBody]

private def lookupZProof (zImageBody : Pattern) : RawProof :=
  proofNode "$mm.lookup.there"
    [ bindingsTailWith zImageBody, zName, tcWff, zImageBody
    , yName, tcWff, bodyY ]
    [proofNode "$mm.lookup.here"
      [zName, tcWff, zImageBody, Builder.nil]]

private def substBodyYProof (zImageBody : Pattern) : RawProof :=
  let substitution := substitutionWith zImageBody
  proofNode "$mm.subst-body.var"
    [ substitution, yName, tcWff, bodyY
    , Builder.nil, Builder.nil, bodyY ]
    [ lookupYProof zImageBody
    , proofNode "$mm.subst-body.nil" [substitution]
    , appendSingletonProof ySymbol ]

private def substBodyZProof (zImageBody imageSymbol : Pattern) : RawProof :=
  let substitution := substitutionWith zImageBody
  proofNode "$mm.subst-body.var"
    [ substitution, zName, tcWff, zImageBody
    , Builder.nil, Builder.nil, zImageBody ]
    [ lookupZProof zImageBody
    , proofNode "$mm.subst-body.nil" [substitution]
    , appendSingletonProof imageSymbol ]

private def applyYProof (zImageBody : Pattern) : RawProof :=
  let substitution := substitutionWith zImageBody
  proofNode "$mm.apply-subst.formula"
    [substitution, tcProvable, bodyY, bodyY]
    [substBodyYProof zImageBody]

private def applyZProof (zImageBody imageSymbol : Pattern) : RawProof :=
  let substitution := substitutionWith zImageBody
  proofNode "$mm.apply-subst.formula"
    [substitution, tcProvable, bodyZ, zImageBody]
    [substBodyZProof zImageBody imageSymbol]

private def pairXY : Pattern := Builder.dvPair (name "x") yName
private def pairXZ : Pattern := Builder.dvPair (name "x") zName
private def pairYZ : Pattern := Builder.dvPair yName zName
private def pairYY : Pattern := Builder.dvPair yName yName

private def singleton (value : Pattern) : Pattern :=
  Builder.cons value Builder.nil

private def callerDVTailAfterXY : Pattern :=
  Builder.cons pairXZ (singleton pairYZ)
private def callerDVTailAfterXZ : Pattern := singleton pairYZ
private def callerDV : Pattern :=
  Builder.cons pairXY callerDVTailAfterXY
private def calleeDV : Pattern := singleton pairYZ

private def callerHyps : Pattern :=
  encodeListWith encodeString expectedCallerHyps.toList
private def calleeHyps : Pattern :=
  encodeListWith encodeString expectedAxYZHyps.toList

private def varsSingletonProof (variableName : Pattern) : RawProof :=
  proofNode "$mm.vars.var"
    [variableName, Builder.nil, Builder.nil]
    [proofNode "$mm.vars.nil" []]

private def memberYZProof : RawProof :=
  proofNode "$mm.member.there" [pairYZ, pairXY, callerDVTailAfterXY]
    [proofNode "$mm.member.there" [pairYZ, pairXZ, callerDVTailAfterXZ]
      [proofNode "$mm.member.here" [pairYZ, Builder.nil]]]

private def allPairsYZProof : RawProof :=
  proofNode "$mm.all-pairs.cons"
    [callerDV, yName, Builder.nil, singleton zName]
    [ proofNode "$mm.all-with.cons"
        [callerDV, yName, zName, Builder.nil]
        [ proofNode "$mm.dv-rel.forward" [callerDV, yName, zName]
            [memberYZProof]
        , proofNode "$mm.all-with.nil" [callerDV, yName] ]
    , proofNode "$mm.all-pairs.nil" [callerDV, singleton zName] ]

private def positiveDVListsProof : RawProof :=
  proofNode "$mm.dv-lists.cons"
    [ positiveSubstitution, callerDV, yName, zName, Builder.nil
    , tcWff, bodyY, tcWff, bodyZ, singleton yName, singleton zName ]
    [ lookupYProof bodyZ
    , lookupZProof bodyZ
    , varsSingletonProof yName
    , varsSingletonProof zName
    , allPairsYZProof
    , proofNode "$mm.dv-lists.nil" [positiveSubstitution, callerDV] ]

private def positiveDVProof : RawProof :=
  proofNode "$mm.dv-ok.frames"
    [positiveSubstitution, callerDV, callerHyps, calleeDV, calleeHyps]
    [positiveDVListsProof]

/-- The proof tree obtained from the real four normal-proof tokens. -/
def loweredProof : RawProof :=
  proofNode "ax-yz" [bodyY, bodyZ, bodyY, bodyZ]
    [ wyProof, wzProof, thEssentialProof
    , applyYProof bodyZ
    , positiveDVProof
    , applyZProof bodyZ zSymbol ]

def checkWithProjectedPrefix (goal : Pattern) (proof : RawProof) : Bool :=
  match projectForFreshTarget? prefixDB "th" with
  | some presentation => checkRaw presentation goal proof
  | none => false

#guard checkWithProjectedPrefix (proves formulaProvableY) thEssentialProof
#guard checkWithProjectedPrefix
  (applySubst positiveSubstitution formulaProvableY formulaProvableY)
  (applyYProof bodyZ)
#guard checkWithProjectedPrefix
  (dvOK positiveSubstitution
    (Builder.frame callerDV callerHyps)
    (Builder.frame calleeDV calleeHyps))
  positiveDVProof
#guard checkWithProjectedPrefix (proves formulaProvableZ) loweredProof

/-! ## DV-localized rejection of `wy wy th.1 ax-yz` -/

/-- This candidate `member.here` instance would prove membership only in a
singleton whose head really is `(y,y)`. -/
private def failedMemberYYHereProof : RawProof :=
  proofNode "$mm.member.here" [pairYY, Builder.nil]

/-- This deliberately traverses the real caller-DV list and finally supplies
`failedMemberYYHereProof` where the remaining stored head is `(y,z)`.  That
last child-goal mismatch is the precise failure; no DV child is omitted. -/
private def failedMemberYYProof : RawProof :=
  proofNode "$mm.member.there" [pairYY, pairXY, callerDVTailAfterXY]
    [proofNode "$mm.member.there" [pairYY, pairXZ, callerDVTailAfterXZ]
      [failedMemberYYHereProof]]

private def failedAllPairsYYProof : RawProof :=
  proofNode "$mm.all-pairs.cons"
    [callerDV, yName, Builder.nil, singleton yName]
    [ proofNode "$mm.all-with.cons"
        [callerDV, yName, yName, Builder.nil]
        [ proofNode "$mm.dv-rel.forward" [callerDV, yName, yName]
            [failedMemberYYProof]
        , proofNode "$mm.all-with.nil" [callerDV, yName] ]
    , proofNode "$mm.all-pairs.nil" [callerDV, singleton yName] ]

private def mutatedDVListsProof : RawProof :=
  proofNode "$mm.dv-lists.cons"
    [ mutatedSubstitution, callerDV, yName, zName, Builder.nil
    , tcWff, bodyY, tcWff, bodyY, singleton yName, singleton yName ]
    [ lookupYProof bodyY
    , lookupZProof bodyY
    , varsSingletonProof yName
    , varsSingletonProof yName
    , failedAllPairsYYProof
    , proofNode "$mm.dv-lists.nil" [mutatedSubstitution, callerDV] ]

def mutatedDVProof : RawProof :=
  proofNode "$mm.dv-ok.frames"
    [mutatedSubstitution, callerDV, callerHyps, calleeDV, calleeHyps]
    [mutatedDVListsProof]

/-- Every non-DV computation follows the real mutated token stack.  The goal
is `|- y`, the result obtained by substituting the second `wy` for formal `z`;
therefore rejection cannot be attributed to the conclusion substitution. -/
def loweredMutatedProof : RawProof :=
  proofNode "ax-yz" [bodyY, bodyY, bodyY, bodyY]
    [ wyProof, wyProof, thEssentialProof
    , applyYProof bodyY
    , mutatedDVProof
    , applyZProof bodyY ySymbol ]

/-- Child checks in the generated `ax-yz` premise order.  The unique `false`
is the fifth child, `DVOK`; both the essential and conclusion substitutions
remain accepted. -/
def mutatedChildChecks : List Bool :=
  [ checkWithProjectedPrefix (proves formulaWffY) wyProof
  , checkWithProjectedPrefix (proves formulaWffY) wyProof
  , checkWithProjectedPrefix (proves formulaProvableY) thEssentialProof
  , checkWithProjectedPrefix
      (applySubst mutatedSubstitution formulaProvableY formulaProvableY)
      (applyYProof bodyY)
  , checkWithProjectedPrefix
      (dvOK mutatedSubstitution
        (Builder.frame callerDV callerHyps)
        (Builder.frame calleeDV calleeHyps))
      mutatedDVProof
  , checkWithProjectedPrefix
      (applySubst mutatedSubstitution formulaProvableZ formulaProvableY)
      (applyZProof bodyY ySymbol) ]

#guard mutatedChildChecks == [true, true, true, true, false, true]

#guard checkWithProjectedPrefix
  (applySubst mutatedSubstitution formulaProvableY formulaProvableY)
  (applyYProof bodyY)
#guard checkWithProjectedPrefix
  (applySubst mutatedSubstitution formulaProvableZ formulaProvableY)
  (applyZProof bodyY ySymbol)
#guard checkWithProjectedPrefix
  (member pairYY (singleton pairYY)) failedMemberYYHereProof
#guard !checkWithProjectedPrefix
  (member pairYY (singleton pairYZ)) failedMemberYYHereProof
#guard !checkWithProjectedPrefix
  (member pairYY callerDV) failedMemberYYProof
#guard !checkWithProjectedPrefix
  (dvOK mutatedSubstitution
    (Builder.frame callerDV callerHyps)
    (Builder.frame calleeDV calleeHyps))
  mutatedDVProof
#guard !checkWithProjectedPrefix (proves formulaProvableY) loweredMutatedProof

end Mettapedia.Languages.Metamath.InferenceProjectionDVFixture
