import Mettapedia.OSLF.NativeTypes.Product.AcceptanceRows
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.InstanceControls
import Mettapedia.OSLF.NativeTypes.Instances.Dedukti.FrontDoorControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PetriControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPrenexControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.PiPartnerControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientNuControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRepControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSRecPartnerControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.AmbientContextControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.CCSPartnerControls
import Mettapedia.OSLF.NativeTypes.Instances.Rho.CanonicalControls

/-!
# The instance languages' rows for the executable

The tree's authored languages, asked as the executable asks them (`answerWith`), with the answers the library's own
controls prove with the kernel:

- **the λ-calculus** with β at the root (`InstanceControls`): the identity applied to itself ends at the identity,
  every run from `Ω` goes on forever, and the constant function discards `Ω`;
- **TinyML** (`InstanceControls`): a conditional on `true`, forcing a thunk, a projection, and a conditional on a
  function that is stuck;
- **a Petri net** modulo its bag laws (`PetriControls`): `{A, B}` steps and `{A, D}` does not, some run from `{A, B}`
  reaches a stuck marking, and every marking it reaches is one of three; the executable gives the bag language its
  canonical forms;
- **the π-calculus** modulo its restriction laws and its laws of replication (`PiPrenexControls`,
  `PiPartnerControls`): extrusion lets a guarded input meet an output, an unused restriction is garbage, a private
  channel stays private, a server serves once and stays, and the replicated forwarder runs forever; beside an output
  on its channel an input steps, and beside one on another channel it does not, which π's certified decider answers
  at its partners' labels;
- **CCS with replication** modulo its restriction laws and its laws of replication (`CCSRepControls`): a replicated
  action serves once and stays, replicated partners run forever, and a private replicated action stays private;
- **mobile ambients with restriction and replication** modulo their restriction, replication and boundary laws
  (`AmbientNuControls`): entering ends inside the other ambient, opening an ambient releases one that then enters a
  sibling, a private ambient cannot be entered from outside its scope, and a restricted ambient leaves its parent;
- **mobile ambients with communication** in two-level contexts (`AmbientContextControls`): `in b.0` steps inside an
  ambient beside `b[0]`, and `0` does not; `out b.0` enters `b` with its ambient and leaves it in two steps, and `0`
  only enters; `out b.0` leaves a grandparent `b`. The ambient decider certified for these labels answers them;
- **π's parallel fragment** modulo its flattening algebra (`PiControls`): a communication ends at inaction, and a
  server waits without the laws of replication;
- **CCS** modulo its sums and restriction laws (`CCSControls`, `CCSPartnerControls`): a partner resolves a choice and
  the other summand is discarded, a private pair reacts, a private action stays private; beside `~a.0`, `a.0` steps,
  and beside `~b.0` it does not, which CCS's certified decider answers at its partners' labels;
- **the ρ-calculus** modulo its equations (`Rho.Canonical.Controls`): a communication steps, and so does a
  communication on the equivalent channels `@*@0` and `@0`, which only its canonical forms see; an input guarded by an
  input waits.

The product's answer gives the π-calculi, CCS, mobile ambients and ρ the canonical forms and deciders their own
theorems certify (`certifiedFormsOf`, `certifiedDeciderOf`). Their files read back as these very languages
(`FileRoundTrip`), so the executable answers them from their files as the library does;
- **Peano arithmetic in the λΠ-calculus modulo** (`Dedukti.Controls`): `2` has no step, `2 + 3` steps, and it ends at
  `5`; the congruences reach the depth of these terms with premise fuel eight.
- **CCS with recursion** in the environment of its definitions (`CCSRecControls`, `CCSRecPartnerControls`), asked
  with the forms and the decider certified for that environment (`askRecursive`): the server `A(a)` beside `~a.0` ends
  at `A(a)`, and alone it waits; beside the least partner `~a.k.0`, `a.0 | D` steps to `D` beside the sentinel `k.0`,
  which `D` does not, and the server steps to itself beside it. The executable asks them from the language's file and
  the definitions file beside it (`recursiveMatrixRows`).

Each row's text reads back as its formula and term, and the library answers each row as written (`#guard`).
-/

namespace Mettapedia.OSLF.NativeTypes.Product

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.GeneratedLogic
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.InstanceControls (endsAt forever steps identity omega constant app
  lam inject yes no thunkBody)

/-- A language row: the language's file, the language, the formula, the term, the budget, the expected answer in
brief, and the premise fuel. -/
abbrev LanguageRow := String × LanguageDef × Formula 0 × Pattern × ℕ × String × ℕ

def LanguageRow.matrixRow : LanguageRow → MatrixRow
  | (file, _, formula, term, budget, expected, fuel) =>
    (file, formulaText formula, patternText term, budget, expected, [s!"fuel={fuel}", "hints=1"])

/-- The library's answer to a row, as the executable computes it. -/
def LanguageRow.answer : LanguageRow → Answer
  | (_, language, formula, term, budget, _, fuel) => answerWith { fuel := fuel } language formula term budget

def LanguageRow.agrees (row : LanguageRow) : Bool := asExpected row.2.2.2.2.2.1 row.answer

def lambdaCalc : LanguageDef := Mettapedia.OSLF.Framework.LambdaInstance.lambdaCalc
def tinyML : LanguageDef := Mettapedia.OSLF.Framework.TinyMLInstance.tinyML
def peano : LanguageDef :=
  Mettapedia.GSLT.Dedukti.Language.dkLanguage Instances.Dedukti.Controls.names
    Mettapedia.GSLT.Dedukti.PeanoFiber.peanoRules

def numeral (n : ℕ) : Pattern :=
  Mettapedia.GSLT.Dedukti.Language.encode (Mettapedia.GSLT.Dedukti.PeanoFiber.numeral n)

def sum : Pattern :=
  Mettapedia.GSLT.Dedukti.Language.encode
    (Mettapedia.GSLT.Dedukti.PeanoFiber.plus (Mettapedia.GSLT.Dedukti.PeanoFiber.numeral 2)
      (Mettapedia.GSLT.Dedukti.PeanoFiber.numeral 3))

def lambdaLanguageRows : List LanguageRow :=
  [("Lambda.module", lambdaCalc, endsAt identity, app identity identity, 4, "P closed", 2),
   ("Lambda.module", lambdaCalc, forever, omega, 4, "P closed", 2),
   ("Lambda.module", lambdaCalc, endsAt (lam omega), app constant omega, 6, "P closed", 2),
   ("Lambda.module", lambdaCalc, steps, identity, 4, "R closed", 2)]

def tinyMLRows : List LanguageRow :=
  [("TinyML.module", tinyML, endsAt (inject no), .apply "If" [inject yes, inject no, inject yes], 4, "P closed", 2),
   ("TinyML.module", tinyML, .possibly .any (.is thunkBody), inject (.apply "Thunk" [thunkBody]), 6,
     "P exploration", 2),
   ("TinyML.module", tinyML, endsAt (inject yes), inject (.apply "Thunk" [thunkBody]), 6, "R closed", 2),
   ("TinyML.module", tinyML, endsAt (inject yes), .apply "Fst" [inject (.apply "PairV" [yes, no])], 4, "P closed", 2),
   ("TinyML.module", tinyML, steps,
     .apply "If" [inject (.apply "Lam" [.lambda none (inject (.bvar 0))]), inject yes, inject no], 8,
     "R closed", 2)]

def peanoRows : List LanguageRow :=
  [("Peano.module", peano, .necessarily .any .bot, numeral 2, 8, "P closed", 8),
   ("Peano.module", peano, .possibly .any .top, sum, 8, "P exploration", 8),
   ("Peano.module", peano, .necessarily .any .bot, sum, 8, "R exploration", 8),
   ("Peano.module", peano, Instances.Dedukti.Controls.endsAt (numeral 5), sum, 8, "P closed", 8)]

def petriRows : List LanguageRow :=
  [("Petri.module", PetriControls.petriCore, PetriControls.steps, PetriControls.ab, 4, "P exploration", 2),
   ("Petri.module", PetriControls.petriCore, PetriControls.steps, PetriControls.ad, 4, "R canonical", 2),
   ("Petri.module", PetriControls.petriCore, PetriControls.reachesDeadlock, PetriControls.ab, 6, "P canonical", 2),
   ("Petri.module", PetriControls.petriCore, PetriControls.onlyThreeMarkings, PetriControls.ab, 6, "P canonical", 2),
   ("Petri.module", PetriControls.petriCore, .is PetriControls.ab, PetriControls.ba, 4, "P canonical", 2)]

/-- π's parallel fragment: its rules without its restriction laws, the language its certified forms are for. -/
def piParallel : LanguageDef := Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance.piParallelFragment

def piRows : List LanguageRow :=
  [("PiParallel.module", piParallel, PiControls.endsAt PiControls.zero,
     PiControls.par [PiControls.input PiControls.a PiControls.zero, PiControls.output PiControls.a PiControls.b],
     4, "P canonical", 3),
   ("PiParallel.module", piParallel, PiControls.endsAt PiControls.zero,
     PiControls.par [PiControls.par [PiControls.input PiControls.a PiControls.zero, PiControls.zero],
       PiControls.output PiControls.a PiControls.b], 4, "P canonical", 3),
   ("PiParallel.module", piParallel, PiControls.steps,
     PiControls.par [PiControls.server PiControls.a PiControls.zero, PiControls.output PiControls.a PiControls.b],
     4, "R canonical", 3)]

/-- The π-calculus with its restriction laws. -/
def piFull : LanguageDef := Mettapedia.Languages.ProcessCalculi.PiCalculus.PiCalcInstance.piCalc

def piFullRows : List LanguageRow :=
  [("Pi.module", piFull, PiControls.endsAt (PiControls.restrict (PiControls.output (.bvar 0) PiPrenexControls.w)),
     PiPrenexControls.guarded, 4, "P canonical", 3),
   ("Pi.module", piFull, PiControls.endsAt PiControls.zero, PiPrenexControls.unused, 4, "P canonical", 3),
   ("Pi.module", piFull, PiControls.steps, PiPrenexControls.private_, 4, "R canonical", 3),
   ("Pi.module", piFull, PiControls.forever, PiPrenexControls.forwarder, 4, "P canonical", 3),
   ("Pi.module", piFull, PiControls.endsAt (PiControls.server PiPrenexControls.x PiControls.zero),
     PiPrenexControls.serving, 4, "P canonical", 3),
   ("Pi.module", piFull, .possibly (PiPartnerControls.beside PiPartnerControls.sender) .top,
     PiPartnerControls.receiver, 4, "P decided", 3),
   ("Pi.module", piFull, .possibly (PiPartnerControls.beside (PiControls.output PiPrenexControls.w PiPrenexControls.w))
     .top, PiPartnerControls.receiver, 4, "R decided", 3)]

def ccsRepCalc : LanguageDef := Mettapedia.Languages.ProcessCalculi.CCS.Replicated.ccsRepCalc

def ccsRepRows : List LanguageRow :=
  [("CCSRep.module", ccsRepCalc,
     CCSControls.endsAt (CCSRepControls.replicate (Mettapedia.Languages.ProcessCalculi.CCS.sum
       [Mettapedia.Languages.ProcessCalculi.CCS.act CCSControls.a Mettapedia.Languages.ProcessCalculi.CCS.nil])),
     CCSRepControls.server, 4, "P canonical", 3),
   ("CCSRep.module", ccsRepCalc, PiControls.forever, CCSRepControls.partners, 4, "P canonical", 3),
   ("CCSRep.module", ccsRepCalc, CCSControls.steps, CCSRepControls.privateServer, 4, "R canonical", 3)]

def ambientNuCalc : LanguageDef := Mettapedia.Languages.ProcessCalculi.Ambient.Full.ambientNuCalc

def ambientNuRows : List LanguageRow :=
  [("AmbientNu.module", ambientNuCalc,
     AmbientNuControls.endsAt (AmbientNuControls.amb AmbientNuControls.b
       (AmbientNuControls.amb AmbientNuControls.a AmbientNuControls.zero)),
     AmbientNuControls.par [AmbientNuControls.amb AmbientNuControls.a
       (AmbientNuControls.enter AmbientNuControls.b AmbientNuControls.zero),
       AmbientNuControls.amb AmbientNuControls.b AmbientNuControls.zero], 3, "P canonical", 8),
   ("AmbientNu.module", ambientNuCalc,
     AmbientNuControls.finallyAt (AmbientNuControls.amb AmbientNuControls.b
       (AmbientNuControls.amb AmbientNuControls.c AmbientNuControls.zero)),
     AmbientNuControls.par [AmbientNuControls.dissolve AmbientNuControls.a AmbientNuControls.zero,
       AmbientNuControls.amb AmbientNuControls.a (AmbientNuControls.amb AmbientNuControls.c
         (AmbientNuControls.enter AmbientNuControls.b AmbientNuControls.zero)),
       AmbientNuControls.amb AmbientNuControls.b AmbientNuControls.zero], 4, "P canonical", 8),
   ("AmbientNu.module", ambientNuCalc, AmbientNuControls.steps,
     AmbientNuControls.par [AmbientNuControls.restrict (AmbientNuControls.amb AmbientNuControls.x
       AmbientNuControls.zero), AmbientNuControls.amb AmbientNuControls.a
       (AmbientNuControls.enter AmbientNuControls.n AmbientNuControls.zero)], 3, "R canonical", 8),
   ("AmbientNu.module", ambientNuCalc,
     AmbientNuControls.endsAt (AmbientNuControls.par [AmbientNuControls.restrict
       (AmbientNuControls.amb AmbientNuControls.x AmbientNuControls.zero),
       AmbientNuControls.amb AmbientNuControls.b AmbientNuControls.zero]),
     AmbientNuControls.amb AmbientNuControls.b (AmbientNuControls.restrict (AmbientNuControls.amb AmbientNuControls.x
       (AmbientNuControls.leave AmbientNuControls.b AmbientNuControls.zero))), 3, "P canonical", 8)]

def ambientCommCalc : LanguageDef := Mettapedia.Languages.ProcessCalculi.Ambient.Comm.ambientCommCalc

/-- Mobile ambients with communication, in two-level contexts. -/
def ambientCommRows : List LanguageRow :=
  [("AmbientComm.module", ambientCommCalc, AmbientContextControls.stepsIn (.sibling "a" AmbientContextControls.zero "b"
      AmbientContextControls.zero), AmbientContextControls.enter AmbientContextControls.b AmbientContextControls.zero, 4,
      "P decided", 2),
   ("AmbientComm.module", ambientCommCalc, AmbientContextControls.stepsIn (.sibling "a" AmbientContextControls.zero "b"
      AmbientContextControls.zero), AmbientContextControls.zero, 4, "R decided", 2),
   ("AmbientComm.module", ambientCommCalc, AmbientContextControls.twoStepsIn (.sibling "a"
      (AmbientContextControls.enter AmbientContextControls.b AmbientContextControls.zero) "b" AmbientContextControls.zero),
      AmbientContextControls.leave AmbientContextControls.b AmbientContextControls.zero, 4, "P decided", 2),
   ("AmbientComm.module", ambientCommCalc, AmbientContextControls.twoStepsIn (.sibling "a"
      (AmbientContextControls.enter AmbientContextControls.b AmbientContextControls.zero) "b" AmbientContextControls.zero),
      AmbientContextControls.zero, 4, "R decided", 2),
   ("AmbientComm.module", ambientCommCalc, AmbientContextControls.stepsIn (.grandparent "b" AmbientContextControls.zero
      "a" AmbientContextControls.zero), AmbientContextControls.leave AmbientContextControls.b AmbientContextControls.zero,
      4, "P decided", 2)]

def ccsCalc : LanguageDef := Mettapedia.Languages.ProcessCalculi.CCS.ccsCalc

open Mettapedia.Languages.ProcessCalculi.CCS (nil act coact) in
/-- CCS with its sums and restriction laws. -/
def ccsRows : List LanguageRow :=
  [("CCS.module", ccsCalc, CCSControls.endsAt nil, CCSControls.choice, 3, "P canonical", 4),
   ("CCS.module", ccsCalc, CCSControls.endsAt (Mettapedia.Languages.ProcessCalculi.CCS.sum [act CCSControls.b nil]), CCSControls.choice, 3, "R canonical", 4),
   ("CCS.module", ccsCalc, CCSControls.endsAt nil, CCSControls.privatePair, 3, "P canonical", 4),
   ("CCS.module", ccsCalc, CCSControls.steps, CCSControls.privateApart, 3, "R canonical", 4),
   ("CCS.module", ccsCalc, .possibly (CCSPartnerControls.beside CCSPartnerControls.coaction) .top,
     CCSPartnerControls.action, 3, "P decided", 4),
   ("CCS.module", ccsCalc, .possibly (CCSPartnerControls.beside (Mettapedia.Languages.ProcessCalculi.CCS.sum [coact CCSControls.b nil])) .top,
     CCSPartnerControls.action, 3, "R decided", 4)]

/-- The ρ-calculus with its equations. -/
def rhoCalc : LanguageDef := Mettapedia.OSLF.MeTTaIL.Syntax.rhoCalc

/-- ρ, at the premise fuel its forms are certified for. -/
def rhoRows : List LanguageRow :=
  [("Rho.module", rhoCalc, PiControls.steps, Instances.Rho.Canonical.Controls.redex, 3, "P canonical", 1),
   ("Rho.module", rhoCalc, PiControls.steps, Instances.Rho.Canonical.Controls.equivalentChannelRedex, 3,
     "P canonical", 1),
   ("Rho.module", rhoCalc, PiControls.steps, Instances.Rho.Canonical.Controls.guardedRedex, 3, "R canonical", 1)]

/-- The instance languages' rows. -/
def languageRows : List LanguageRow :=
  lambdaLanguageRows ++ tinyMLRows ++ petriRows ++ piFullRows ++ piRows ++ ccsRows ++ ccsRepRows ++ ambientNuRows ++
    ambientCommRows ++ rhoRows ++ peanoRows

/-- **The instance languages' rows as the executable's matrix rows**: every language's rows run from its file. -/
def languageMatrixRows : List MatrixRow := languageRows.map LanguageRow.matrixRow

/-- The instance languages written as files, by file name. -/
def instanceLanguages : List (String × LanguageDef) :=
  [("Lambda", lambdaCalc), ("TinyML", tinyML), ("Petri", { GeneratedLogic.PetriControls.petriCore with «name» := "Petri" }),
   ("Peano", peano), ("Pi", piFull), ("PiParallel", piParallel), ("CCS", ccsCalc), ("CCSRep", ccsRepCalc),
   ("AmbientNu", ambientNuCalc), ("AmbientComm", ambientCommCalc), ("Rho", rhoCalc),
   ("CCSRec", Mettapedia.Languages.ProcessCalculi.CCS.Recursive.ccsRecCalc)]

#guard languageRows.all LanguageRow.agrees
#guard languageRows.all fun (_, _, formula, term, _, _, _) => readsBack formula term

-- The certified forms make the difference: the communication on the equivalent channels `@*@0` and `@0`, which
-- ρ's certified forms establish, stays open for a copy of ρ under another name, which has none.
#guard Verdicts.answerSummary (answerWith { fuel := 1 } { rhoCalc with «name» := "UncertifiedRho" } PiControls.steps
  Instances.Rho.Canonical.Controls.equivalentChannelRedex 3) == "open"

/-! ## CCS with recursion, in the environment of its definitions -/

open Mettapedia.Languages.ProcessCalculi.CCS (nil coact)
open Mettapedia.Languages.ProcessCalculi.CCS.Recursive (call)

/-- **A row of CCS with recursion**: formula, term, budget, expected answer and premise fuel, asked in the environment
of the controls' definitions. -/
abbrev RecursiveRow := Formula 0 × Pattern × ℕ × String × ℕ

def RecursiveRow.answer : RecursiveRow → Answer
  | (formula, term, budget, _, fuel) =>
    askRecursive CCSRecControls.definitions CCSRecControls.admitted fuel formula term 1 budget

def RecursiveRow.agrees (row : RecursiveRow) : Bool := asExpected row.2.2.2.1 row.answer

/-- CCS with recursion's rows. -/
def recursiveRows : List RecursiveRow :=
  [(CCSRecControls.endsAt (call 0 [.fvar "a"]), .collection .hashBag [call 0 [.fvar "a"],
      Mettapedia.Languages.ProcessCalculi.CCS.sum [coact (.fvar "a") nil]]
      none, 4, "P canonical", 3),
   (CCSRecControls.steps, call 0 [.fvar "a"], 4, "R canonical", 2),
   (CCSRecPartnerControls.performs CCSRecPartnerControls.loopCall,
      CCSRecPartners.par CCSRecPartnerControls.actNil CCSRecPartnerControls.loopCall, 4, "P decided", 2),
   (CCSRecPartnerControls.performs CCSRecPartnerControls.loopCall, CCSRecPartnerControls.loopCall, 4, "R decided", 2),
   (CCSRecPartnerControls.performs CCSRecPartnerControls.server, CCSRecPartnerControls.server, 4, "P decided", 2)]

#guard recursiveRows.all RecursiveRow.agrees
#guard recursiveRows.all fun (formula, term, _, _, _) => readsBack formula term

/-- **CCS with recursion's rows as the executable's matrix rows**: its language read from its file, asked in the
environment of the definitions file beside it. -/
def recursiveMatrixRows : List MatrixRow :=
  recursiveRows.map fun (formula, term, budget, expected, fuel) =>
    ("CCSRec.module", formulaText formula, patternText term, budget, expected,
      [s!"fuel={fuel}", "hints=1", "definitions=CCSRec.defs"])

/-- The controls' definitions as the definitions file writes them. -/
def recursiveDefinitionsText : String := definitionsText CCSRecControls.definitions

-- The definitions file reads back as the definitions.
#guard match readDefinitions recursiveDefinitionsText with
  | .ok read => read == CCSRecControls.definitions
  | .error _ => false
-- A definitions file that is not a list of definitions is refused.
#guard match readDefinitions "x | (CTau CNil)" with
  | .ok _ => false
  | .error _ => true

end Mettapedia.OSLF.NativeTypes.Product
