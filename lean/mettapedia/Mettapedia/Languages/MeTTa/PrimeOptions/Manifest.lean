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
exact kernel, readout or quotient claim is accepted when one of them concludes in
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

`#prime_option_graph_controls` reports the census and fails on the first
rejected citation; `#prime_option_graph_refusals` shows that each check refuses a
bad citation. `#prime_option_graph_json` prints the whole graph with the
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

/-- Whether a declaration's statement concludes in the shape an exact form requires. -/
def concludesIn (form : ExactForm) (name : Name) : MetaM Bool := do
  let info ← getConstInfo name
  forallTelescope info.type fun _ body => do
    let isEquality (expr : Expr) : Bool := expr.isAppOfArity ``Eq 3
    let equivalenceWithEquality := body.isAppOfArity ``Iff 2 &&
      (isEquality body.appFn!.appArg! || isEquality body.appArg!)
    return match form with
      | .kernel => equivalenceWithEquality
      | .readout => isEquality body
      | .quotient => body.isAppOfArity ``Function.Injective 3 || equivalenceWithEquality

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
        let usedIndex := (← get).index[used]!
        modify fun state => { state with
          lowlink := state.lowlink.insert name (min state.lowlink[name]! usedIndex) }
        reaches := reaches || ((← get).partial_[used]?).getD false
      else
        visitChoice used
        if let some answer := (← get).known[used]? then
          reaches := reaches || answer
        else
          let usedLow := (← get).lowlink[used]!
          modify fun state => { state with
            lowlink := state.lowlink.insert name (min state.lowlink[name]! usedLow) }
          reaches := reaches || ((← get).partial_[used]?).getD false
  modify fun state => { state with partial_ := state.partial_.insert name reaches }
  if (← get).lowlink[name]! == number then
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

def evidenceList (items : List Evidence) : Json :=
  .arr (items.toArray.map evidenceJson)

def verdictJson (verdict : Verdict) : Json :=
  Json.mkObj [("reading", .str verdict.reading), ("evidence", evidenceList verdict.evidence),
    ("kernelChecked", .bool verdict.kernelChecked)]

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
  for arrow in graph.arrows do
    for claim in arrow.grades do
      checkVocabulary arrow claim
  let checked ← declared.mapM checkDeclaration
  let bundles := ledgerRefs.filterMap (·.assumptions)
  let mut manifests : Array Json := checked
  if qualify then
    let (hosts, _) ← (declared.mapM hostDependency).run {}
    manifests := #[]
    for index in [0:declared.size] do
      let (laws, restriction) ← statementQualifiers bundles declared[index]!
      manifests := manifests.push (checked[index]!.mergeObj (Json.mkObj [
        ("hostDependency", hosts[index]!), ("declaredLaws", laws),
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
      ("facts", evidenceList node.facts)]
  let arrows := graph.arrows.toArray.map fun arrow =>
    Json.mkObj [("id", .str arrow.id), ("source", .str arrow.source),
      ("target", .str arrow.target), ("kind", .str arrow.kind.label),
      ("grades", .arr (arrow.grades.toArray.map fun claim =>
        Json.mkObj [("claim", .str claim.label),
          ("bound", match claim with | .defect bound => .str bound | _ => .null),
          ("vocabulary", names claim.vocabulary),
          ("shape", match claim.exactForm? with | some form => .str form.shape | none => .null)])),
      ("summary", .str arrow.summary), ("evidence", evidenceList arrow.evidence)]
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
  let frontier := graph.frontier.toArray.map fun (first, second) =>
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
      ("rejectedWitnessed", .bool graph.rejectedWitnessed)]),
    ("frontier", .arr frontier),
    ("equivalences", .arr (graph.equivalences.toArray.map fun (first, second) =>
      Json.mkObj [("question", .str ((graph.questionOf first).getD "")),
        ("first", .str first), ("second", .str second)])),
    ("qualifications", strings (Qualification.all.map (·.label)))
  ]

/-- The census the controls report. -/
def census (graph : Graph) : MetaM String := do
  let json ← graphJson graph (qualify := false)
  let declarations := match json.getObjVal? "declarations" with
    | .ok (.arr items) => items.size
    | _ => 0
  let kernelChecked := (graph.witnesses.filter (·.kernelChecked)).length
  unless graph.wellFormed do throwError "the graph is not well formed"
  unless graph.rejectedWitnessed do throwError "an option ruled out carries no witness"
  return s!"{graph.questions.length} questions, {graph.nodes.length} options, \
    {graph.arrows.length} arrows, {graph.observers.length} observers, \
    {graph.witnesses.length} witnesses ({kernelChecked} kernel-checked), \
    {declarations} declarations checked, {graph.frontier.length} frontier pairs, \
    {graph.equivalences.length} exact equivalences"

elab "#prime_option_graph_controls" : command => do
  let line ← liftTermElabM (census primeOptions)
  logInfo m!"prime option graph: {line}"

elab "#prime_option_graph_json" : command => do
  let json ← liftTermElabM (graphJson primeOptions)
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
  kind := .view
  grades := [.exact]
  summary := "control"
  evidence := [cites [``Mettapedia.SetTheory.AntiFoundation.factors_bafa_fafa]]

/-- An arrow claiming an exact kernel from a factorization. -/
def exactKernelFromFactorization : Arrow :=
  { exactFromFactorization with grades := [.exactKernel .kernel] }

/-- A ledger whose proof concludes in another ledger. -/
def mismatchedLedger : LedgerRef where
  assumptions := none
  ledger := ``Mettapedia.SetTheory.Profiles.HypersetLedger
  proof := ``Mettapedia.SetTheory.Profiles.megalodonLedger

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
    -- a ledger whose proof concludes elsewhere
    ← refuses (discard <| ledgerJson mismatchedLedger),
    -- a theorem named as a closed theory
    ← refuses (checkTheory ``Mettapedia.SetTheory.Profiles.bare_implication_refl)]
  return (outcomes.filter id).length

elab "#prime_option_graph_refusals" : command => do
  let refused ← liftTermElabM refusals
  logInfo m!"refused {refused} of 7 bad citations"

/-- info: refused 7 of 7 bad citations -/
#guard_msgs in
#prime_option_graph_refusals

/-- info: prime option graph: 17 questions, 45 options, 32 arrows, 18 observers, 37 witnesses (21 kernel-checked), 176 declarations checked, 1 frontier pairs, 6 exact equivalences -/
#guard_msgs in
#prime_option_graph_controls

end Mettapedia.Languages.MeTTa.PrimeOptions.Manifest
