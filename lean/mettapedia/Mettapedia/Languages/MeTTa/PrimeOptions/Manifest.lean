import Lean.Data.Json
import Lean.Elab.Command
import Lean.Meta
import Lean.Util.CollectAxioms
import Mettapedia.Logic.KernelFoundationManifest
import Mettapedia.GSLT.LanguageDef.TheoryGraph
import Mettapedia.Languages.MeTTa.PrimeOptions.Graph
import Mettapedia.SetTheory.Profiles
import Mettapedia.SetTheory.AntiFoundation.GeneralReadouts
import Mettapedia.GSLT.Distinction.DemandStrategies
import Mettapedia.GSLT.Distinction.DemandStrategiesControls
import Mettapedia.GSLT.Dynamics.OrderedDemand
import Mettapedia.GSLT.Causality.Hierarchy
import Mettapedia.GSLT.Logic.ReflectiveBubble
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingSpine
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoQuotedCompilerObserverControls
import Mettapedia.GSLT.Logic.ContextualObservedCoalgebra
import Mettapedia.GSLT.Logic.ContextualObservedCoalgebraTransport
import Mettapedia.GSLT.Logic.ContextualObservedCoalgebraQuotient
import Mettapedia.GSLT.Logic.ContextualObservedMaterialFamily
import Mettapedia.GSLT.Logic.ContextualObservedCoalgebraControls

/-!
# The Prime option graph joined to the checked foundation manifest

Every declaration the registry `primeOptions` cites is read from the checked
environment through `KernelFoundationManifest` schema 2. A citation is accepted
when the declaration exists, is safe, depends on no admission, and depends on no
axiom beyond `propext`, `Classical.choice` and `Quot.sound`; when the binders it
must take are in its telescope and the binders it must avoid are not; and when it
is free of host choice if it is required to be.

A grade claim with a vocabulary (`GradeClaim.vocabulary`) is accepted when one of
the declarations its arrow cites mentions that vocabulary in its statement. An
exact kernel, readout, quotient or extension claim is accepted when one of them concludes in
the shape its form requires (`ExactForm.shape`).

Three qualifications are read off every cited declaration. **Host dependency**:
whether host choice enters its statement or only its proof, and through which
first constants outside the library (multisets and finite sets, real numbers and
suprema, classical logic, or other). **Declared laws**: the propositions it takes
as hypotheses that are laws: their head is a principle of the library and they
speak of no element the statement binds (a premise about given elements, such as
two related states, is a side condition), together with the assumption structures
the registry's ledgers name, taken as arguments. **Observer
restriction**: the observer types it quantifies over, and the constants of its
statement whose values are admissible classes, observations, tolerances or
weights.

A principle ledger is read from its structures: the fields of the assumption
structure are the assumed principles, and each field of the ledger structure is a
derived fact, or a refuted principle when its statement is a negation. The proof
of the ledger must conclude in the ledger structure.

A closed theory named by an option must be an object of a fibre of the theory
graph (`TheoryGraph.fibre`), a `PiInstitution.TheoryObject`.

Every arrow's contract is checked: an entry saying the arrow preserves something,
or does not, cites theorems, and an entry marked unknown cites nothing
(`checkContract`); a preservation claim contradicted by a counterexample recorded
for the same passage refuses the graph (`checkConsistent`).

**Applicability.** For two arrow kinds whose contracts have a uniform shape, the proposition
an entry claims is generated from the actual endpoints, without looking at the citations: for
a restriction preserving membership, membership preserved and reflected along the arrow's map
and the map injective; for an observational quotient, the factorization of a reading through
the target's denotation, or the failure of the source's denotation, or of its reading of
distinctions, to factor through the arrow's readout map or else the target's denotation. A
cited declaration is then elaborated against that proposition (`checkApplicable`). Every
other entry is checked for validity only and is not promoted.

**Replay pins.** Every cited fixture has a pin with the SHA-256 of its files, and every external
checker run the SHA-256 of its file, preamble and binary (`checkPins`). Whether the files still
have those hashes is checked by the generator, which reads them.

**Obligations.** A proved obligation cites a declaration concluding in its statement, a
refuted one a theorem concluding in its negation (`checkObligation`).

A named hypothesis of an option exists, and each declaration said to prove it concludes in
it (`checkHypothesis`). A refutation's theorems conclude in the negation of its proposition,
up to definitional unfolding (`checkRefutation`). No option is conditional on a hypothesis the
registry records as refuted (`checkUnrefuted`), and no option's ledger proof takes a refuted
proposition as an argument (`checkLedgerUnrefuted`); a ledger a correction replaced is kept
as history.

`#prime_option_graph_controls` reports the census and fails on the first
rejected citation; `#prime_option_graph_refusals` shows that each check refuses a
bad citation; `#prime_option_graph_contract_control` shows why a claim that the
two-valued reading at a point preserves bounded formulas is refused, and
`#prime_option_graph_hypothesis_control` why an option conditional on a refuted
hypothesis, and a ledger whose proof assumes one, are refused,
`#prime_option_graph_applicability_control` why `True.intro` cited for a negation and a real
theorem about other endpoints are refused, and `#prime_option_graph_pin_control` why a fixture
without a replay pin is refused. `#prime_option_graph_json` prints the whole graph with the
manifest of every cited declaration, the ledgers, the two checks and the
frontier, for the generator of the published graph.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeOptions.Manifest

open Lean Elab Command Meta
open Mettapedia.Logic.KernelFoundationManifest
open Mettapedia.GSLT.Distinction.OptionGraph

/-- The axioms a cited declaration may depend on. -/
def acceptedAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

/-- The declaration that makes a closed theory an object of the theory graph. -/
def theoryObjectType : Name := ``Mettapedia.GSLT.LanguageDef.NIKMetalogic.PiInstitution.TheoryObject

/-- The theory graph's inclusion of the closed theories of one institution. -/
def theoryGraphFibre : Name := ``Mettapedia.GSLT.LanguageDef.TheoryGraph.fibre

private def names (items : List Name) : Json :=
  .arr (items.toArray.map fun name => .str name.toString)

private def strings (items : List String) : Json :=
  .arr (items.toArray.map .str)

private def binderNames (name : Name) : MetaM (Array Name) := do
  let info ← getConstInfo name
  forallTelescope info.type fun binders _ => binders.mapM fun binder => binder.fvarId!.getUserName

private def statementText (type : Expr) : MetaM String := do
  return toString (← ppExpr type)

/-- Check one declaration through the schema-2 manifest; return its summary. -/
def checkDeclaration (name : Name) : MetaM Json := do
  let info ← getConstInfo name
  if info.isUnsafe || info.isPartial then
    throwError "{name} is unsafe or partial"
  let manifest ← declarationManifest name
  let axioms ← collectAxioms name
  if axioms.contains ``sorryAx then
    throwError "{name} depends on sorryAx"
  for axiomName in axioms do
    unless acceptedAxioms.contains axiomName do
      throwError "{name} depends on the axiom {axiomName}"
  let summary ← match manifest.getObjVal? "declaration" with
    | .ok summary => pure summary
    | .error err => throwError "{name}: {err}"
  let field (key : String) : Json := (summary.getObjVal? key).toOption.getD .null
  return Json.mkObj [
    ("name", .str name.toString),
    ("originModule", field "originModule"),
    ("kind", field "kind"),
    ("checkingRole", field "checkingRole"),
    ("hasCheckedBody", field "hasCheckedBody"),
    ("universeParameters", field "universeParameters"),
    ("transitiveAxioms", names axioms.toList),
    ("containsAdmission", .bool false),
    ("statement", .str (← statementText info.type))
  ]

/-- Check a citation's binder and host-choice requirements. -/
def checkCitation (citation : Citation) : MetaM Unit := do
  let binders ← binderNames citation.declaration
  for binder in citation.binds do
    unless binders.contains binder do
      throwError "{citation.declaration} does not take the binder {binder}. Telescope: {binders}"
  for binder in citation.avoids do
    if binders.contains binder then
      throwError "{citation.declaration} takes the binder {binder}"
  if citation.choiceFree then
    let axioms ← collectAxioms citation.declaration
    if axioms.contains ``Classical.choice then
      throwError "{citation.declaration} is required to be free of host choice"

/-- Whether a declaration's statement concludes in the shape an exact form requires. A same
extension claim takes an equivalence, an equality, a bijection, or a unique isomorphism: one
direction, a bare isomorphism class, or an equivalence of types, which says only that they have
the same size, is not enough. -/
def concludesIn (form : ExactForm) (name : Name) : MetaM Bool := do
  let info ← getConstInfo name
  forallTelescope info.type fun _ body => do
    let isEquality (expr : Expr) : Bool := expr.isAppOfArity ``Eq 3
    let equivalenceWithEquality := body.isAppOfArity ``Iff 2 &&
      (isEquality body.appFn!.appArg! || isEquality body.appArg!)
    let uniqueIsomorphism := body.isAppOfArity ``ExistsUnique 2 &&
      body.appFn!.appArg!.isAppOfArity ``CategoryTheory.Iso 4
    return match form with
      | .kernel => equivalenceWithEquality
      | .readout => isEquality body
      | .quotient => body.isAppOfArity ``Function.Injective 3 || equivalenceWithEquality
      | .extension => body.isAppOfArity ``Iff 2 || isEquality body ||
          body.isAppOfArity ``Function.Bijective 3 || uniqueIsomorphism

/-- One of the cited declarations mentions one of the vocabulary, and, for an exact
kernel claim, concludes in the required shape. -/
def checkVocabulary (arrow : Arrow) (claim : GradeClaim) : MetaM Unit := do
  let cited := arrow.evidence.flatMap (·.declarations)
  if let some form := claim.exactForm? then
    for name in cited do
      if ← concludesIn form name then return
    throwError "arrow {arrow.id}: no cited statement concludes in {form.shape}"
  let vocabulary := claim.vocabulary
  if vocabulary.isEmpty then return
  for name in cited do
    let info ← getConstInfo name
    if vocabulary.any info.type.getUsedConstants.contains then return
  throwError "arrow {arrow.id}: no cited statement mentions {vocabulary} for the claim {claim.label}"

/-! ## Qualifications read off a declaration -/

/-- The types whose values restrict what a claim observes. -/
def observerTypes : List Name := [
  ``Mettapedia.GSLT.AdmissibleContextCongruence.AdmissibleClass,
  ``Mettapedia.GSLT.MinimalEnablingContext.ContextualRules.Observations,
  ``Mettapedia.GSLT.HennessyMilner.System,
  ``Mettapedia.Cybernetics.DistinctionCalculus.Tolerance,
  ``Mettapedia.GSLT.Distinction.DemandStrategies.Weights]

/-- Whether a constant belongs to a module of this library. -/
def ownedHere (name : Name) : MetaM Bool := do
  let env ← getEnv
  match env.getModuleIdxFor? name with
  | some index =>
    return match env.header.moduleNames[index.toNat]? with
      | some moduleName => (`Mettapedia).isPrefixOf moduleName
      | none => false
  | none => return (`Mettapedia).isPrefixOf name

/-- The constants a declaration's kernel entry refers to, as `collectAxioms` reads them. -/
def constantsOf (info : ConstantInfo) : Array Name :=
  let fromType := info.type.getUsedConstants
  match info with
  | .defnInfo value => fromType ++ value.value.getUsedConstants
  | .thmInfo value => fromType ++ value.value.getUsedConstants
  | .opaqueInfo value => fromType ++ value.value.getUsedConstants
  | .inductInfo value => fromType ++ value.ctors.toArray
  | _ => fromType

/-- The state of one depth-first pass over the constants: Tarjan's numbering of
the strongly connected components, the answer for every finished constant, the
partial answer of every constant on the stack, and for each library constant the
library constants it refers to and the outside constants it refers to that reach
host choice. -/
structure ChoiceState where
  counter : Nat := 0
  index : Std.HashMap Name Nat := {}
  lowlink : Std.HashMap Name Nat := {}
  stack : Array Name := #[]
  onStack : NameSet := {}
  partial_ : Std.HashMap Name Bool := {}
  known : Std.HashMap Name Bool := {}
  edges : Std.HashMap Name (Array Name × Array Name) := {}

/-- Tarjan's pass: whether host choice is reachable from a constant. Every
constant is entered once; a component's answer is the disjunction of its
members' answers and is recorded for all of them when the component closes. -/
partial def visitChoice (name : Name) : StateT ChoiceState MetaM Unit := do
  let number := (← get).counter
  modify fun state => { state with
    counter := number + 1
    index := state.index.insert name number
    lowlink := state.lowlink.insert name number
    stack := state.stack.push name
    onStack := state.onStack.insert name }
  let mut reaches := name == ``Classical.choice
  if let some info := (← getEnv).find? name then
    for used in constantsOf info do
      if let some answer := (← get).known[used]? then
        reaches := reaches || answer
      else if (← get).onStack.contains used then
        let usedIndex := ((← get).index[used]?).getD 0
        modify fun state => { state with
          lowlink := state.lowlink.insert name (min ((state.lowlink[name]?).getD 0) usedIndex) }
        reaches := reaches || ((← get).partial_[used]?).getD false
      else
        visitChoice used
        if let some answer := (← get).known[used]? then
          reaches := reaches || answer
        else
          let usedLow := ((← get).lowlink[used]?).getD 0
          modify fun state => { state with
            lowlink := state.lowlink.insert name (min ((state.lowlink[name]?).getD 0) usedLow) }
          reaches := reaches || ((← get).partial_[used]?).getD false
  modify fun state => { state with partial_ := state.partial_.insert name reaches }
  if ((← get).lowlink[name]?).getD 0 == number then
    let mut members : Array Name := #[]
    let mut component := false
    repeat
      let state ← get
      let member := state.stack.back!
      set { state with stack := state.stack.pop, onStack := state.onStack.erase member }
      members := members.push member
      component := component || ((← get).partial_[member]?).getD false
      if member == name then break
    for member in members do
      modify fun state => { state with
        known := state.known.insert member component
        partial_ := state.partial_.erase member }

/-- Whether host choice is reachable from a constant. -/
def usesChoice (name : Name) : StateT ChoiceState MetaM (Bool × Bool) := do
  unless (← get).known.contains name do
    visitChoice name
  return (((← get).known[name]?).getD false, false)

/-- The class of a constant through which host choice enters, read from its name. -/
def entryClass (name : Name) : String :=
  let text := name.toString
  let has (part : String) : Bool := (text.splitOn part).length > 1
  if has "Multiset" || has "Finset" || has "Fintype" || has "Finite" || has "Finsupp" then
    "multisets and finite sets"
  else if has "Real" || has "NNReal" || has "ENNReal" || has "EReal" || has "sSup" || has "sInf" ||
      has "iSup" || has "iInf" || has "csSup" || has "ciSup" || has "csInf" || has "ciInf" ||
      has "ConditionallyComplete" then
    "real numbers and suprema"
  else if has "Classical" || has "Exists.choose" || has "Nonempty.some" then
    "classical logic"
  else if (`Mathlib.Tactic).isPrefixOf name then
    "tactic lemmas"
  else if has "Rat" || has "Int." || has "Ordered" || has "Field" || has "Ring" || has "Group" ||
      has "Monoid" || has "Lattice" then
    "rational numbers and ordered algebra"
  else
    "other"

/-- The library constants a library constant refers to, and the outside constants
it refers to that reach host choice; remembered. -/
def edgesOf (name : Name) : StateT ChoiceState MetaM (Array Name × Array Name) := do
  if let some known := (← get).edges[name]? then return known
  let some info := (← getEnv).find? name | return (#[], #[])
  let mut owned : Array Name := #[]
  let mut entries : Array Name := #[]
  for used in constantsOf info do
    if ← ownedHere used then
      owned := owned.push used
    else if (← usesChoice used).1 then
      entries := entries.push used
  modify fun state => { state with edges := state.edges.insert name (owned, entries) }
  return (owned, entries)

/-- The first constants outside the library through which host choice enters a
declaration. -/
def choiceEntries (start : Name) : StateT ChoiceState MetaM (Array Name) := do
  let mut visited : NameSet := NameSet.empty.insert start
  let mut stack : Array Name := #[start]
  let mut entries : NameSet := {}
  while !stack.isEmpty do
    let current := stack.back!
    stack := stack.pop
    let (owned, outside) ← edgesOf current
    for entry in outside do
      entries := entries.insert entry
    for used in owned do
      unless visited.contains used do
        visited := visited.insert used
        stack := stack.push used
  return entries.toArray.qsort Name.lt

/-- Host dependency of a declaration: choice in its statement, in its proof, and
where it enters. -/
def hostDependency (name : Name) : StateT ChoiceState MetaM Json := do
  let info ← getConstInfo name
  let proofChoice := (← usesChoice name).1
  let mut statementChoice := false
  for used in info.type.getUsedConstants do
    if (← usesChoice used).1 then
      statementChoice := true
      break
  let entries ← if proofChoice then choiceEntries name else pure #[]
  let classes := ["multisets and finite sets", "real numbers and suprema",
    "rational numbers and ordered algebra", "classical logic", "tactic lemmas", "other"]
  let grouped := classes.map fun group =>
    (group, Json.arr ((entries.filter fun entry => entryClass entry == group).map
      fun entry => .str entry.toString))
  return Json.mkObj [
    ("choiceInProof", .bool proofChoice),
    ("choiceInStatement", .bool statementChoice),
    ("entries", Json.mkObj grouped)
  ]

/-- Declared laws and observer restriction of a declaration's statement. -/
def statementQualifiers (bundles : List Name) (name : Name) : MetaM (Json × Json) := do
  let info ← getConstInfo name
  forallTelescope info.type fun binders _ => do
    let mut principles : Array Json := #[]
    let mut sideConditions : Nat := 0
    let mut every : Array Json := #[]
    let mut elements : Array Expr := #[]
    for binder in binders do
      let type ← inferType binder
      let head := type.getAppFn.constName?
      let binderName ← binder.fvarId!.getUserName
      if ← isProp type then
        let aboutElements := elements.any fun element => type.containsFVar element.fvarId!
        match head with
        | some headName =>
          if (← ownedHere headName) && !aboutElements then
            principles := principles.push (Json.mkObj [("binder", .str binderName.toString),
              ("principle", .str headName.toString)])
          else sideConditions := sideConditions + 1
        | none => sideConditions := sideConditions + 1
      else if head.any bundles.contains then
        principles := principles.push (Json.mkObj [("binder", .str binderName.toString),
          ("principle", .str head.get!.toString)])
      else
        let shape ← whnfR type
        unless shape.isSort || shape.isForall do
          elements := elements.push binder
        if let some headName := head then
          if observerTypes.contains headName then
            every := every.push (Json.mkObj [("binder", .str binderName.toString),
              ("type", .str headName.toString)])
    let mut relative : Array Name := #[]
    let mut mentions : Array Name := #[]
    for used in info.type.getUsedConstants do
      if observerTypes.contains used then
        mentions := mentions.push used
        continue
      let usedInfo ← getConstInfo used
      let observing ← forallTelescope usedInfo.type fun _ codomain =>
        pure (codomain.getUsedConstants.any observerTypes.contains)
      if observing then relative := relative.push used
    let declared := Json.mkObj [("principles", .arr principles),
      ("sideConditions", toJson sideConditions)]
    let restriction := Json.mkObj [("every", .arr every),
      ("relativeTo", .arr ((relative.qsort Name.lt).map fun item => .str item.toString)),
      ("mentions", .arr ((mentions.qsort Name.lt).map fun item => .str item.toString))]
    return (declared, restriction)

private def fieldsOf (structure_ : Name) : MetaM (Array Json) := do
  let env ← getEnv
  unless isStructure env structure_ do
    throwError "{structure_} is not a structure"
  let parameters := (← getConstInfoInduct structure_).numParams
  let fields := getStructureFieldsFlattened env structure_ (includeSubobjectFields := false)
  fields.mapM fun field => do
    let projection := structure_ ++ field
    let info ← getConstInfo projection
    forallBoundedTelescope info.type (some (parameters + 1)) fun _ body => do
      let refuted := body.isAppOfArity ``Not 1
      return Json.mkObj [
        ("field", .str field.toString),
        ("statement", .str (← statementText body)),
        ("refuted", .bool refuted)
      ]

/-- Read a ledger from its structures and check its proof. -/
def ledgerJson (ledger : LedgerRef) : MetaM Json := do
  let assumed ← match ledger.assumptions with
    | some structure_ => fieldsOf structure_
    | none => pure #[]
  let facts ← fieldsOf ledger.ledger
  let proof ← getConstInfo ledger.proof
  let concludes ← forallTelescope proof.type fun _ body =>
    pure (body.getAppFn.constName? == some ledger.ledger)
  unless concludes do
    throwError "{ledger.proof} does not conclude in {ledger.ledger}"
  let derived := facts.filter fun fact => (fact.getObjValAs? Bool "refuted").toOption != some true
  let refuted := facts.filter fun fact => (fact.getObjValAs? Bool "refuted").toOption == some true
  return Json.mkObj [
    ("assumptions", match ledger.assumptions with
      | some structure_ => .str structure_.toString
      | none => .null),
    ("ledger", .str ledger.ledger.toString),
    ("proof", .str ledger.proof.toString),
    ("assumed", .arr assumed),
    ("derived", .arr derived),
    ("refuted", .arr refuted)
  ]

/-- A named closed theory is an object of a fibre of the theory graph. -/
def checkTheory (name : Name) : MetaM Unit := do
  let _ ← getConstInfo theoryGraphFibre
  let info ← getConstInfo name
  let head ← forallTelescope info.type fun _ body => pure body.getAppFn.constName?
  unless head == some theoryObjectType do
    throwError "{name} is not a closed theory of an institution"

/-! ## Contracts -/

/-- An entry that says an arrow preserves something, or does not, cites theorems; an
entry marked unknown cites nothing; a named hypothesis is a declaration. -/
def checkContract (arrow : Arrow) : MetaM Unit := do
  for entry in arrow.contract.entries do
    unless entry.wellCited do
      throwError "{arrow.id}: the entry on {entry.aspect.label} ({entry.status.label}) \
        is not cited as its status requires"
    for name in entry.citations do
      let info ← getConstInfo name
      unless info matches .thmInfo _ do
        throwError "{arrow.id}: {name}, cited for {entry.aspect.label}, is not a theorem"
  for name in arrow.contract.hypotheses do
    discard <| getConstInfo name

/-- A named hypothesis of an option exists, and every declaration said to prove it is a
theorem concluding in it. -/
def checkHypothesis (hypothesis : NamedHypothesis) : MetaM Unit := do
  discard <| getConstInfo hypothesis.name
  for name in hypothesis.provedBy do
    let info ← getConstInfo name
    unless (info matches .thmInfo _) || (← isProp info.type) do
      throwError "{name}, said to prove {hypothesis.name}, is not a proof"
    let head ← forallTelescope info.type fun _ body => pure body.getAppFn.constName?
    unless head == some hypothesis.name do
      throwError "{name} does not conclude in {hypothesis.name}"

def hypothesisJson (hypothesis : NamedHypothesis) : Json :=
  Json.mkObj [("name", .str hypothesis.name.toString), ("conditions", .str hypothesis.conditions),
    ("provedBy", names hypothesis.provedBy)]

/-- The proposition a refutation records, at fresh universe levels. -/
def refutedProposition (refutation : Refutation) : MetaM Expr := do
  let info ← getConstInfo refutation.hypothesis
  unless (← whnf info.type).isProp do
    throwError "{refutation.hypothesis} is not a proposition"
  return mkConst refutation.hypothesis (← mkFreshLevelMVars info.levelParams.length)

/-- A refutation: every refuting declaration is a theorem whose statement is the negation of
the recorded proposition. -/
def checkRefutation (refutation : Refutation) : MetaM Unit := do
  for name in refutation.refutedBy do
    let info ← getConstInfo name
    unless info matches .thmInfo _ do
      throwError "{name}, said to refute {refutation.hypothesis}, is not a theorem"
    let refutes ← forallTelescope info.type fun _ body => do
      let some refuted := body.not? | return false
      withoutModifyingState do isDefEq refuted (← refutedProposition refutation)
    unless refutes do
      throwError "{name} does not refute {refutation.hypothesis}"

def refutationJson (refutation : Refutation) : Json :=
  Json.mkObj [("hypothesis", .str refutation.hypothesis.toString),
    ("scope", .str refutation.scope), ("refutedBy", names refutation.refutedBy)]

/-- A ledger whose proof assumes no proposition the registry records as refuted: no argument of
the proof has the type of a recorded refutation. -/
def checkLedgerUnrefuted (refutations : List Refutation) (ledger : LedgerRef) : MetaM Unit := do
  let info ← getConstInfo ledger.proof
  forallTelescope info.type fun binders _ => do
    for binder in binders do
      let type ← inferType binder
      unless ← isProp type do continue
      for refutation in refutations do
        if ← withoutModifyingState do isDefEq type (← refutedProposition refutation) then
          throwError "the ledger proof {ledger.proof} assumes {refutation.hypothesis}, refuted by \
            {", ".intercalate (refutation.refutedBy.map toString)}"

/-- An obligation: a proving declaration concludes in its statement, a refuting one in the
negation of its statement; its named hypotheses are checked as an option's are. -/
def checkObligation (obligation : Obligation) : MetaM Unit := do
  for hypothesis in obligation.hypotheses do
    checkHypothesis hypothesis
  let some statement := obligation.statement | return
  discard <| getConstInfo statement
  match obligation.status with
  | .proved =>
    let mut concludes := false
    for name in obligation.evidence do
      let info ← getConstInfo name
      let head ← forallTelescope info.type fun _ body => pure body.getAppFn.constName?
      if head == some statement then concludes := true
    unless concludes do
      throwError "{obligation.id}: no cited declaration concludes in {statement}"
  | .refuted =>
    let mut refutes := false
    for name in obligation.evidence do
      let info ← getConstInfo name
      let head ← forallTelescope info.type fun _ body =>
        pure ((body.not?.map (·.getAppFn.constName?)).join)
      if head == some statement then refutes := true
    unless refutes do
      throwError "{obligation.id}: no cited theorem refutes {statement}"
  | .«open» => pure ()

def obligationJson (obligation : Obligation) : Json :=
  Json.mkObj [("id", .str obligation.id), ("title", .str obligation.title),
    ("feeds", strings obligation.feeds), ("source", .str obligation.source),
    ("status", .str obligation.status.label),
    ("statement", match obligation.statement with | some name => .str name.toString | none => .null),
    ("evidence", names obligation.evidence),
    ("hypotheses", .arr (obligation.hypotheses.toArray.map hypothesisJson)),
    ("note", .str obligation.note)]

/-- The frontier map covers the frontier exactly, with ratings in percent. -/
def checkFrontierMap (graph : Graph) (pairs : List (String × String) := graph.frontier) :
    MetaM Unit := do
  if let (first, second) :: _ := graph.unmappedFrontier pairs then
    throwError "the frontier pair {first} and {second} has no target in the frontier map"
  if let target :: _ := graph.staleTargets pairs then
    throwError "the target for {target.first} and {target.second} names a pair that is not on \
      the frontier"
  unless graph.frontierTargets.all (fun target => target.confidence ≤ 100 && target.value ≤ 100) do
    throwError "a frontier target has a rating above 100"

def frontierTargetJson (graph : Graph) (target : FrontierTarget) : Json :=
  Json.mkObj [("question", .str ((graph.questionOf target.first).getD "")),
    ("first", .str target.first), ("second", .str target.second),
    ("outcome", .str target.outcome.label), ("kind", .str target.kind.label),
    ("statement", .str target.statement), ("firstVerdict", .str target.firstVerdict),
    ("secondVerdict", .str target.secondVerdict), ("module", .str target.module),
    ("confidence", toJson target.confidence), ("value", toJson target.value)]

/-- Refuse a graph in which an option is conditional on a hypothesis the registry records as
refuted. -/
def checkUnrefuted (graph : Graph) : MetaM Unit := do
  if let (node, hypothesis, refutedBy) :: _ := graph.refutedHypotheses then
    throwError "{node} is conditional on {hypothesis}, which the registry records as refuted by \
      {", ".intercalate (refutedBy.map toString)}"

/-- The negative control for refuted hypotheses: why the small-map option as first recorded is
refused, or `accepted`. -/
def hypothesisControl : MetaM String := do
  try
    checkUnrefuted withTypeRepresentabilityAssumed
    return "accepted"
  catch error =>
    return s!"refused: {← error.toMessageData.toString}"

/-- The same control read off the first ledger's proof: why it is refused, or `accepted`. -/
def ledgerControl : MetaM String := do
  try
    checkLedgerUnrefuted primeOptions.refutations CarveOutSheaves.conditionalCoalgebraLedger
    return "accepted"
  catch error =>
    return s!"refused: {← error.toMessageData.toString}"

/-- Refuse a graph in which a recorded counterexample contradicts a preservation
claim on the same passage. -/
def checkConsistent (graph : Graph) : MetaM Unit := do
  if let (id, aspect, counterexamples) :: _ := graph.contractConflicts then
    throwError "{id} claims to preserve {aspect.label}; the counterexample \
      {", ".intercalate (counterexamples.map toString)} contradicts it"

/-- The negative control: why the claim that the two-valued reading at a point
preserves bounded formulas is refused, or `accepted`. -/
def contractControl : MetaM String := do
  try
    checkConsistent withPointReadingClaim
    return "accepted"
  catch error =>
    return s!"refused: {← error.toMessageData.toString}"

/-- The group an aspect belongs to. -/
def aspectGroup : Aspect → String
  | .formulas _ => "formulas"
  | .operation _ => "dependent operations"
  | .evidence _ => "evidence"
  | .commitment _ => "commitments"
  | _ => "readings"

/-! ## Applicability: contract entries checked at the actual instance -/

/-- Whether a cited declaration proves the expected proposition, by elaboration: the
declaration is elaborated against the proposition as its expected type, as in
`example : expected := cited`, with its implicit arguments filled by unification; failing that,
as `example : expected := @cited`, its statement unfolded against the proposition. -/
def elaboratesAs (cited : Name) (expected : Expr) : MetaM Bool := do
  let attempt : TermElabM Bool := Term.withoutErrToSorry do
    let term ← Term.elabTermEnsuringType (mkCIdent cited) expected
    Term.synthesizeSyntheticMVarsNoPostponing
    let term ← instantiateMVars term
    return !term.hasExprMVar && !term.hasSorry && (← isDefEq (← inferType term) expected)
  if ← (try withoutModifyingState attempt.run' catch _ => pure false) then
    return true
  try
    withoutModifyingState do
      let term ← mkConstWithFreshMVarLevels cited
      isDefEq (← inferType term) expected
  catch _ => return false

/-- `Factors shadow invariant`: the invariant is a function of the shadow. -/
def factorsExpected (shadow invariant : Name) : MetaM Expr := do
  mkAppM ``Mettapedia.GSLT.Core.NonFactorization.Factors
    #[← mkConstWithFreshMVarLevels shadow, ← mkConstWithFreshMVarLevels invariant]

/-- For a restriction realized by `map` from the target's carrier into the source's:
`∀ x y, memTarget x y ↔ memSource (map x) (map y)` and `Function.Injective map`. -/
def membershipExpected (memSource memTarget map : Name) : MetaM (List Expr) := do
  let memSource ← mkConstWithFreshMVarLevels memSource
  let memTarget ← mkConstWithFreshMVarLevels memTarget
  let map ← mkConstWithFreshMVarLevels map
  let .forallE _ carrier _ _ ← whnf (← inferType map)
    | throwError "{map} is not a function"
  let preserved ← withLocalDeclD `x carrier fun x => withLocalDeclD `y carrier fun y => do
    mkForallFVars #[x, y] (← mkAppM ``Iff
      #[mkApp2 memTarget x y, mkApp2 memSource (mkApp map x) (mkApp map y)])
  return [preserved, ← mkAppM ``Function.Injective #[map]]

/-- The propositions a contract entry claims at the arrow's actual endpoints, generated from
the options' denotations, memberships and readings and from the arrow's map, without looking
at the citations. Two shapes are generated: a restriction preserving membership, and an
observational quotient whose entry is a factorization or its failure. Every other entry gives
`none`: it is checked for validity only. -/
def expectedPropositions (graph : Graph) (arrow : Arrow) (entry : ContractEntry) :
    MetaM (Option (List Expr)) := do
  let some source := graph.nodes.find? (·.id == arrow.source) | return none
  let some target := graph.nodes.find? (·.id == arrow.target) | return none
  match arrow.kind, entry.status, entry.aspect with
  | .restriction, .preserved, .formulas .atomic =>
    match source.membership, target.membership, arrow.map with
    | some memSource, some memTarget, some map =>
      return some (← membershipExpected memSource memTarget map)
    | _, _, _ => return none
  | .observationalQuotient, .notPreserved, .distinctions =>
    let coarse := arrow.map.orElse fun _ => target.denotation
    let fine := ((source.readings.find? (·.1 == .distinctions)).map (·.2)).orElse
      fun _ => source.denotation
    match fine, coarse with
    | some fine, some coarse => return some [mkNot (← factorsExpected coarse fine)]
    | _, _ => return none
  | .observationalQuotient, .preserved, aspect =>
    match target.denotation, (source.readings.find? (·.1 == aspect)).map (·.2) with
    | some coarse, some reading => return some [← factorsExpected coarse reading]
    | _, _ => return none
  | _, _, _ => return none

/-- An entry checked at its instance: the expected propositions, and for each the cited
declaration that proves it. -/
structure Applicability where
  expected : List String
  provedBy : List Name

/-- Check an entry at its instance. `none`: no expected proposition is generated, so the entry
is checked for validity only. Fails when a generated proposition is proved by none of the
entry's citations. -/
def checkApplicable (graph : Graph) (arrow : Arrow) (entry : ContractEntry) :
    MetaM (Option Applicability) := do
  let some expected ← expectedPropositions graph arrow entry | return none
  let mut shown : Array String := #[]
  let mut provers : Array Name := #[]
  for proposition in expected do
    let mut prover : Option Name := none
    for cited in entry.citations do
      if ← elaboratesAs cited proposition then
        prover := some cited
        break
    let some cited := prover
      | throwError "{arrow.id}: no citation of the entry on {entry.aspect.label} proves \
          {← ppExpr proposition}"
    shown := shown.push (toString (← ppExpr proposition))
    provers := provers.push cited
  return some { expected := shown.toList, provedBy := provers.toList }

def contractJson (contract : Contract) (applicability : List (Option Applicability)) : Json :=
  Json.mkObj [
    ("entries", .arr ((contract.entries.zip applicability).toArray.map fun (entry, checked) =>
      Json.mkObj [("group", .str (aspectGroup entry.aspect)),
        ("aspect", .str entry.aspect.label), ("status", .str entry.status.label),
        ("citations", names entry.citations), ("scope", .str entry.scope),
        ("applicability", .str (match entry.status, checked with
          | .unknown, _ => "unknown"
          | _, some _ => "elaborated at the instance"
          | _, none => "validity only")),
        ("expected", match checked with | some c => strings c.expected | none => .null),
        ("provedBy", match checked with | some c => names c.provedBy | none => .null)])),
    ("hypotheses", names contract.hypotheses)]

/-! ## Replay pins -/

/-- Sixty-four lowercase hexadecimal digits. -/
def isSha256 (hash : String) : Bool :=
  hash.length == 64 && hash.all fun c => c.isDigit || ('a' ≤ c && c ≤ 'f')

/-- Every cited fixture has a replay pin naming its files with their SHA-256, and every external
checker run records the SHA-256 of its file, preamble and binary. Whether the hashes still
match the files is checked by the generator, which reads them. -/
def checkPins (graph : Graph) : MetaM Unit := do
  for (suite, test) in graph.fixtureKeys do
    unless graph.fixturePins.any (fun pin => pin.suite == suite && pin.test == test) do
      throwError "fixture {suite} {test} has no replay pin"
  for pin in graph.fixturePins do
    if pin.files.isEmpty then
      throwError "the replay pin of {pin.suite} {pin.test} names no file"
    for file in pin.files do
      unless isSha256 file.sha256 do
        throwError "the replay pin of {pin.suite} {pin.test} gives {file.path} no SHA-256"
  for evidence in graph.evidence do
    if let .external check := evidence then
      for (path, hash) in [(check.file, check.fileSha256), (check.preamble, check.preambleSha256),
          (check.binary, check.binarySha256)] do
        unless isSha256 hash do
          throwError "the {check.checker} run gives {path} no SHA-256"

/-! ## JSON of the registry -/

def citationJson (citation : Citation) : Json :=
  Json.mkObj [
    ("declaration", .str citation.declaration.toString),
    ("binds", names citation.binds),
    ("avoids", names citation.avoids),
    ("choiceFree", .bool citation.choiceFree)
  ]

def evidenceJson : Evidence → Json
  | .«theorem» citations => Json.mkObj [("kind", .str "theorem"),
      ("citations", .arr (citations.toArray.map citationJson))]
  | .fixture suite test expected => Json.mkObj [("kind", .str "fixture"), ("suite", .str suite),
      ("test", .str test), ("expected", strings expected)]
  | .argument document anchor claim => Json.mkObj [("kind", .str "argument"),
      ("document", .str document), ("anchor", .str anchor), ("claim", .str claim)]
  | .decision date quotation recordedIn => Json.mkObj [("kind", .str "decision"),
      ("date", .str date), ("quotation", .str quotation), ("recordedIn", .str recordedIn)]
  | .external check => Json.mkObj [("kind", .str "external"), ("checker", .str check.checker),
      ("directory", .str check.directory), ("command", .str check.command),
      ("file", .str check.file), ("fileSha256", .str check.fileSha256),
      ("preamble", .str check.preamble), ("preambleSha256", .str check.preambleSha256),
      ("theorems", strings check.theorems),
      ("preambleDeclarations", strings check.preambleDeclarations),
      ("binary", .str check.binary), ("binarySha256", .str check.binarySha256)]

def evidenceList (items : List Evidence) : Json :=
  .arr (items.toArray.map evidenceJson)

def verdictJson (verdict : Verdict) : Json :=
  Json.mkObj [("reading", .str verdict.reading), ("evidence", evidenceList verdict.evidence),
    ("kernelChecked", .bool verdict.kernelChecked),
    ("superseded", evidenceList verdict.superseded)]

/-- The checked graph as JSON. Fails on the first rejected citation. -/
def graphJson (graph : Graph) (qualify : Bool := true) : MetaM Json := do
  -- every citation, once per declaration
  let citations := graph.evidence.flatMap fun
    | .«theorem» items => items
    | _ => []
  for citation in citations do
    checkCitation citation
  let mut declared : Array Name := #[]
  for name in graph.declarations do
    unless declared.contains name do declared := declared.push name
  let mut ledgers : Array Json := #[]
  let ledgerRefs := graph.questions.filterMap (·.ledger) ++ graph.nodes.filterMap (·.ledger)
  for ledger in ledgerRefs do
    for name in ledger.assumptions.toList ++ [ledger.ledger, ledger.proof] do
      unless declared.contains name do declared := declared.push name
  for question in graph.questions do
    if let some ledger := question.ledger then
      ledgers := ledgers.push (Json.mkObj [("owner", .str question.id), ("ledger", ← ledgerJson ledger)])
  for node in graph.nodes do
    if let some ledger := node.ledger then
      ledgers := ledgers.push (Json.mkObj [("owner", .str node.id), ("ledger", ← ledgerJson ledger)])
    if let some theory := node.theory then
      checkTheory theory
      unless declared.contains theory do declared := declared.push theory
    for hypothesis in node.hypotheses do
      checkHypothesis hypothesis
    for refutation in node.refuted do
      checkRefutation refutation
    if let some ledger := node.ledger then
      checkLedgerUnrefuted graph.refutations ledger
    for ledger in node.supersededLedgers do
      for name in [ledger.ledger, ledger.proof] do
        unless declared.contains name do declared := declared.push name
  checkUnrefuted graph
  let pairs := graph.frontier
  checkFrontierMap graph pairs
  unless graph.obligationsCited do
    throwError "an obligation is not cited as its status requires"
  for obligation in graph.obligations do
    checkObligation obligation
  for arrow in graph.arrows do
    for claim in arrow.grades do
      checkVocabulary arrow claim
    checkContract arrow
  checkConsistent graph
  let checked ← declared.mapM checkDeclaration
  let bundles := ledgerRefs.filterMap (·.assumptions)
  let mut manifests : Array Json := checked
  if qualify then
    let (hosts, _) ← (declared.mapM fun name => withCurrHeartbeats (hostDependency name)).run {}
    manifests := #[]
    for ((name, entry), host) in (declared.zip checked).zip hosts do
      let (laws, restriction) ← withCurrHeartbeats (statementQualifiers bundles name)
      manifests := manifests.push (entry.mergeObj (Json.mkObj [
        ("hostDependency", host), ("declaredLaws", laws),
        ("observerRestriction", restriction)]))
  let documents := graph.documents.toArray.map fun document =>
    Json.mkObj [("key", .str document.key), ("title", .str document.title),
      ("date", .str document.date)]
  let questions := graph.questions.toArray.map fun question =>
    Json.mkObj [("id", .str question.id), ("title", .str question.title),
      ("summary", .str question.summary), ("facts", evidenceList question.facts)]
  let nodes := graph.nodes.toArray.map fun node =>
    Json.mkObj [("id", .str node.id), ("question", .str node.question),
      ("title", .str node.title), ("summary", .str node.summary),
      ("standings", .arr (node.standings.toArray.map fun record =>
        Json.mkObj [("standing", .str record.standing.label),
          ("evidence", evidenceList record.evidence)])),
      ("ruledOut", .bool node.ruledOut),
      ("cProfile", match node.cProfile with | some profile => .str profile | none => .null),
      ("theory", match node.theory with | some theory => .str theory.toString | none => .null),
      ("facts", evidenceList node.facts),
      ("denotation", match node.denotation with | some name => .str name.toString | none => .null),
      ("membership", match node.membership with | some name => .str name.toString | none => .null),
      ("readings", .arr (node.readings.toArray.map fun (aspect, name) =>
        Json.mkObj [("aspect", .str aspect.label), ("reading", .str name.toString)])),
      ("hypotheses", .arr (node.hypotheses.toArray.map hypothesisJson)),
      ("refuted", .arr (node.refuted.toArray.map refutationJson)),
      ("supersededLedgers", .arr (node.supersededLedgers.toArray.map fun ledger =>
        Json.mkObj [("ledger", .str ledger.ledger.toString), ("proof", .str ledger.proof.toString)]))]
  checkPins graph
  let mut applicable : Array (List (Option Applicability)) := #[]
  for arrow in graph.arrows do
    applicable := applicable.push (← arrow.contract.entries.mapM (checkApplicable graph arrow))
  let arrows := (graph.arrows.toArray.zip applicable).map fun (arrow, checked) =>
    Json.mkObj [("id", .str arrow.id), ("source", .str arrow.source),
      ("target", .str arrow.target), ("kind", .str arrow.kind.label),
      ("grades", .arr (arrow.grades.toArray.map fun claim =>
        Json.mkObj [("claim", .str claim.label),
          ("bound", match claim with | .defect bound => .str bound | _ => .null),
          ("vocabulary", names claim.vocabulary),
          ("shape", match claim.exactForm? with | some form => .str form.shape | none => .null)])),
      ("summary", .str arrow.summary), ("evidence", evidenceList arrow.evidence),
      ("contract", contractJson arrow.contract checked),
      ("map", match arrow.map with | some name => .str name.toString | none => .null)]
  let observers := graph.observers.toArray.map fun observer =>
    Json.mkObj [("id", .str observer.id), ("title", .str observer.title),
      ("reads", .str observer.reads), ("kind", .str observer.kind.label),
      ("desideratum", .bool observer.desideratum), ("identifies", .bool observer.identifies)]
  let witnesses := graph.witnesses.toArray.map fun witness =>
    Json.mkObj [("id", .str witness.id), ("observer", .str witness.observer),
      ("left", .str witness.left), ("right", .str witness.right), ("case", .str witness.case),
      ("leftVerdict", verdictJson witness.leftVerdict),
      ("rightVerdict", verdictJson witness.rightVerdict),
      ("kernelChecked", .bool witness.kernelChecked),
      ("pending", names witness.pending)]
  let frontier := pairs.toArray.map fun (first, second) =>
    Json.mkObj [("question", .str ((graph.questionOf first).getD "")),
      ("first", .str first), ("second", .str second)]
  return Json.mkObj [
    ("schemaVersion", toJson (1 : Nat)),
    ("manifestSchemaVersion", toJson (2 : Nat)),
    ("checkingEnvironment", ← checkingEnvironment),
    ("documents", .arr documents),
    ("questions", .arr questions),
    ("nodes", .arr nodes),
    ("arrows", .arr arrows),
    ("observers", .arr observers),
    ("witnesses", .arr witnesses),
    ("ledgers", .arr ledgers),
    ("declarations", .arr manifests),
    ("checks", Json.mkObj [
      ("wellFormed", .bool graph.wellFormed),
      ("rejectedWitnessed", .bool graph.rejectedWitnessed),
      ("contractsCited", .bool graph.contractsCited),
      ("quotientsHonest", .bool graph.quotientsHonest),
      ("contractsConsistent", .bool graph.contractsConsistent),
      ("lossyCounterexampled", .bool graph.lossyCounterexampled),
      ("hypothesesUnrefuted", .bool graph.hypothesesUnrefuted),
      ("obligationsCited", .bool graph.obligationsCited),
      ("fixturesPinned", .bool graph.fixturesPinned),
      ("frontierMapped", .bool ((graph.unmappedFrontier pairs).isEmpty &&
        (graph.staleTargets pairs).isEmpty))]),
    ("obligations", .arr (graph.obligations.toArray.map obligationJson)),
    ("frontierTargets", .arr (graph.frontierTargets.toArray.map (frontierTargetJson graph))),
    ("fixturePins", .arr (graph.fixturePins.toArray.map fun pin =>
      Json.mkObj [("suite", .str pin.suite), ("test", .str pin.test),
        ("files", .arr (pin.files.toArray.map fun file =>
          Json.mkObj [("path", .str file.path), ("sha256", .str file.sha256)]))])),
    ("frontier", .arr frontier),
    ("equivalences", .arr (graph.equivalences.toArray.map fun (first, second) =>
      Json.mkObj [("question", .str ((graph.questionOf first).getD "")),
        ("first", .str first), ("second", .str second)])),
    ("qualifications", strings (Qualification.all.map (·.label))),
    ("crossChecks", .arr (CarveOuts.crossChecks.toArray.map fun row =>
      Json.mkObj [("id", .str row.id), ("graph", .str row.graph), ("shape", .str row.shape),
        ("relation", .str row.relation), ("megalodonVerdict", .str row.megalodonVerdict),
        ("megalodonTheorems", strings row.megalodonTheorems),
        ("leanVerdict", .str row.leanVerdict), ("leanUpdate", .str row.leanUpdate),
        ("leanDeclarations", names row.leanCited)]))
  ]

/-- The census the controls report. -/
def census (graph : Graph) : MetaM String := do
  let json ← graphJson graph (qualify := false)
  let declarations := match json.getObjVal? "declarations" with
    | .ok (.arr items) => items.size
    | _ => 0
  let frontierPairs := match json.getObjVal? "frontier" with
    | .ok (.arr items) => items.size
    | _ => 0
  let kernelChecked := (graph.witnesses.filter (·.kernelChecked)).length
  let externalItems := (graph.evidence.filter (·.kind == .external)).length
  unless graph.wellFormed do throwError "the graph is not well formed"
  unless graph.rejectedWitnessed do throwError "an option ruled out carries no witness"
  unless graph.contractsCited do throwError "a contract entry is not cited as its status requires"
  unless graph.quotientsHonest do
    throwError "an observational quotient claims first-order formulas without a theorem"
  unless graph.hypothesesUnrefuted do
    throwError "an option is conditional on a hypothesis recorded as refuted"
  unless graph.lossyCounterexampled do
    throwError "an arrow claims to forget a distinction and names no counterexample"
  let kinds := ArrowKind.all.filterMap fun kind =>
    match (graph.arrows.filter (·.kind == kind)).length with
    | 0 => none
    | count => some s!"{count} {kind.label}"
  let entries := graph.arrows.flatMap (·.contract.entries)
  let entryCount (status : ContractStatus) := (entries.filter (·.status == status)).length
  let contracted := (graph.arrows.filter (!·.contract.entries.isEmpty)).length
  let mut elaborated := 0
  let mut validityOnly := 0
  for arrow in graph.arrows do
    for entry in arrow.contract.entries do
      if entry.status != .unknown then
        match ← checkApplicable graph arrow entry with
        | some _ => elaborated := elaborated + 1
        | none => validityOnly := validityOnly + 1
  return s!"{graph.questions.length} questions, {graph.nodes.length} options, \
    {graph.arrows.length} arrows, {graph.observers.length} observers, \
    {graph.witnesses.length} witnesses ({kernelChecked} kernel-checked), \
    {declarations} declarations checked, {frontierPairs} frontier pairs, \
    {graph.equivalences.length} exact equivalences, {externalItems} external checker evidence items; \
    arrows by kind: {", ".intercalate kinds}; {contracted} contracts with \
    {entryCount .preserved} entries citing theorems, {entryCount .notPreserved} citing \
    counterexamples, {entryCount .unknown} unknown; applicability: {elaborated} entries elaborated \
    at the instance, {validityOnly} validity only; {graph.fixturePins.length} fixtures pinned; \
    {graph.frontierTargets.length} frontier targets"

elab "#prime_option_graph_controls" : command => do
  let line ← liftTermElabM (census primeOptions)
  logInfo m!"prime option graph: {line}"

elab "#prime_option_graph_json" : command => do
  let json ← liftTermElabM do
    let json ← graphJson primeOptions
    return json.mergeObj (Json.mkObj [("contractControl", Json.mkObj [
      ("arrow", .str pointReadingClaim.id), ("outcome", .str (← contractControl))]),
      ("hypothesisControl", Json.mkObj [
        ("option", .str "cantor-sheaf-small-maps"), ("outcome", .str (← hypothesisControl))])])
  logInfo m!"OPTION-GRAPH-JSON-BEGIN\n{json.compress}\nOPTION-GRAPH-JSON-END"

/-- Run a check that should fail; report whether it failed. -/
def refuses (check : MetaM Unit) : MetaM Bool := do
  try
    check
    return false
  catch _ =>
    return true

/-- An arrow claiming an exact grade from a factorization. -/
def exactFromFactorization : Arrow where
  id := "control"
  source := "bafa"
  target := "fafa"
  kind := .observationalQuotient
  grades := [.exact]
  summary := "control"
  evidence := [cites [``Mettapedia.SetTheory.AntiFoundation.factors_bafa_fafa]]

/-- An arrow claiming an exact kernel from a factorization. -/
def exactKernelFromFactorization : Arrow :=
  { exactFromFactorization with grades := [.exactKernel .kernel] }

/-- An arrow claiming that small maps and pullbacks of the universal small map are the same
extension from one direction only: every small map is such a pullback. -/
def extensionFromOneDirection : Arrow where
  id := "control-one-direction"
  source := "small-maps-of-sheaves"
  target := "pullbacks-of-generic-membership"
  kind := .equivalence
  grades := [.exactKernel .extension]
  summary := "control"
  evidence := [cites [``Mettapedia.SetTheory.CarveOuts.Sheaves.small_isPullback_universal]]

/-- A ledger whose proof concludes in another ledger. -/
def mismatchedLedger : LedgerRef where
  assumptions := none
  ledger := ``Mettapedia.SetTheory.Profiles.HypersetLedger
  proof := ``Mettapedia.SetTheory.Profiles.megalodonLedger

/-- A contract citing a structure, not a theorem, for a preservation claim. -/
def contractCitingStructure : Arrow :=
  { exactFromFactorization with
    grades := [.factors]
    contract := { entries := [.keeps (.formulas .atomic) [``Mettapedia.SetTheory.Profiles.HypersetLedger]] } }

/-- A named hypothesis said to be proved by a theorem that concludes in something else. -/
def misprovedHypothesis : NamedHypothesis where
  name := ``Mettapedia.SetTheory.CarveOuts.Sheaves.BaseCollection
  provedBy := [``Mettapedia.SetTheory.CarveOuts.Sheaves.sheafSmall_collection]

/-- **Applicability control.** `True.intro` cited for the failure of a factorization, a
negation. -/
def trueIntroClaim : Arrow where
  id := "control-true-intro"
  source := "bafa"
  target := "fafa"
  kind := .observationalQuotient
  grades := [.lossy]
  summary := "control"
  evidence := [cites [``True.intro]]
  contract := { entries := [.loses .distinctions [``True.intro]] }

/-- **Applicability control.** A real theorem about other endpoints: the failure of
factorization between Finsler's and Boffa's readings, cited for Scott's against Finsler's. -/
def wrongEndpointsClaim : Arrow where
  id := "control-wrong-endpoints"
  source := "fafa"
  target := "safa"
  kind := .observationalQuotient
  grades := [.lossy]
  summary := "control"
  evidence := [cites [``Mettapedia.SetTheory.AntiFoundation.not_factors_fafa_bafa]]
  contract := {
    entries := [.loses .distinctions [``Mettapedia.SetTheory.AntiFoundation.not_factors_fafa_bafa]] }

/-- Check every entry of an arrow at its instance in the registry. -/
def checkArrowApplicable (arrow : Arrow) : MetaM Unit := do
  for entry in arrow.contract.entries do
    discard <| checkApplicable primeOptions arrow entry

/-- Why a control is refused, or `accepted`. -/
def outcome (check : MetaM Unit) : MetaM String := do
  try
    check
    return "accepted"
  catch error =>
    return s!"refused: {← error.toMessageData.toString}"

/-- Each check refuses a citation it should refuse. -/
def refusals : MetaM Nat := do
  let outcomes : List Bool := [
    -- a declaration that does not exist
    ← refuses (discard <| checkDeclaration `Mettapedia.Languages.MeTTa.PrimeOptions.NoSuchDeclaration),
    -- a binder the statement does not take
    ← refuses (checkCitation
      { declaration := ``Mettapedia.SetTheory.Profiles.unorderedPair, binds := [`eps] }),
    -- host choice where it is excluded
    ← refuses (checkCitation
      { declaration := ``Mettapedia.SetTheory.Profiles.bareLedger, choiceFree := true }),
    -- an exact grade claimed from a factorization
    ← refuses (checkVocabulary exactFromFactorization .exact),
    -- an exact kernel claimed from a factorization
    ← refuses (checkVocabulary exactKernelFromFactorization (.exactKernel .kernel)),
    -- the same extension claimed from one direction
    ← refuses (checkVocabulary extensionFromOneDirection (.exactKernel .extension)),
    -- a ledger whose proof concludes elsewhere
    ← refuses (discard <| ledgerJson mismatchedLedger),
    -- a theorem named as a closed theory
    ← refuses (checkTheory ``Mettapedia.SetTheory.Profiles.bare_implication_refl),
    -- a preservation claim citing a structure, not a theorem
    ← refuses (checkContract contractCitingStructure),
    -- the two-valued reading at a point claimed to preserve bounded formulas
    ← refuses (checkConsistent withPointReadingClaim),
    -- a named hypothesis said to be proved by a theorem concluding elsewhere
    ← refuses (checkHypothesis misprovedHypothesis),
    -- an option conditional on a hypothesis the registry records as refuted
    ← refuses (checkUnrefuted withTypeRepresentabilityAssumed),
    -- a ledger whose proof assumes a hypothesis the registry records as refuted
    ← refuses (checkLedgerUnrefuted primeOptions.refutations
      CarveOutSheaves.conditionalCoalgebraLedger),
    -- a fixture with no replay pin
    ← refuses (checkPins withUnpinnedFixture),
    -- `True.intro` cited for a negation at the actual endpoints
    ← refuses (checkArrowApplicable trueIntroClaim),
    -- a real theorem about other endpoints
    ← refuses (checkArrowApplicable wrongEndpointsClaim)]
  return (outcomes.filter id).length

elab "#prime_option_graph_refusals" : command => do
  let refused ← liftTermElabM refusals
  logInfo m!"refused {refused} of 16 bad citations"

/-- info: refused 16 of 16 bad citations -/
#guard_msgs in
#prime_option_graph_refusals

elab "#prime_option_graph_contract_control" : command => do
  let reason ← liftTermElabM contractControl
  logInfo m!"{reason}"

/--
info: refused: points-preserve-bounded claims to preserve bounded formulas; the counterexample Mettapedia.SetTheory.CarveOuts.HeytingValued.free_point_ball_gap contradicts it
-/
#guard_msgs in
#prime_option_graph_contract_control

elab "#prime_option_graph_applicability_control" : command => do
  logInfo m!"{← liftTermElabM (outcome (checkArrowApplicable trueIntroClaim))}"
  logInfo m!"{← liftTermElabM (outcome (checkArrowApplicable wrongEndpointsClaim))}"

/--
info: refused: control-true-intro: no citation of the entry on distinctions proves ¬GSLT.Core.NonFactorization.Factors
    SetTheory.AntiFoundation.denoteFAFA SetTheory.AntiFoundation.denoteBAFA
---
info: refused: control-wrong-endpoints: no citation of the entry on distinctions proves ¬GSLT.Core.NonFactorization.Factors
    SetTheory.AntiFoundation.denoteSAFA SetTheory.AntiFoundation.denoteFAFA
-/
#guard_msgs in
#prime_option_graph_applicability_control

elab "#prime_option_graph_pin_control" : command => do
  logInfo m!"{← liftTermElabM (outcome (checkPins withUnpinnedFixture))}"

/-- info: refused: fixture c-draft tests/prime/causal/unpinned_control.metta has no replay pin -/
#guard_msgs in
#prime_option_graph_pin_control

elab "#prime_option_graph_hypothesis_control" : command => do
  let reason ← liftTermElabM hypothesisControl
  logInfo m!"{reason}"
  let ledger ← liftTermElabM ledgerControl
  logInfo m!"{ledger}"

/--
info: refused: cantor-sheaf-small-maps is conditional on Mettapedia.Languages.MeTTa.PrimeOptions.CarveOutSheaves.CantorTypeRepresentability, which the registry records as refuted by Mettapedia.SetTheory.CarveOuts.Sheaves.cantor_sheaf_not_representable
---
info: refused: the ledger proof Mettapedia.SetTheory.CarveOuts.Sheaves.cantor_sheaf_basicSmallMapAxioms assumes Mettapedia.Languages.MeTTa.PrimeOptions.CarveOutSheaves.CantorTypeRepresentability, refuted by Mettapedia.SetTheory.CarveOuts.Sheaves.cantor_sheaf_not_representable
-/
#guard_msgs in
#prime_option_graph_hypothesis_control

/--
info: prime option graph: 44 questions, 122 options, 71 arrows, 47 observers, 101 witnesses (76 kernel-checked), 604 declarations checked, 37 frontier pairs, 11 exact equivalences, 17 external checker evidence items; arrows by kind: 12 restriction, 22 observational quotient, 1 booleanization, 18 interpretation, 13 equivalence, 5 unclassified; 71 contracts with 82 entries citing theorems, 36 citing counterexamples, 47 unknown; applicability: 9 entries elaborated at the instance, 109 validity only; 14 fixtures pinned; 37 frontier targets
-/
#guard_msgs in
#prime_option_graph_controls

end Mettapedia.Languages.MeTTa.PrimeOptions.Manifest
