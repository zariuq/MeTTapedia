import Mettapedia.Logic.Prolog.ReaderUnitClosure

/-!
# Static module-aware linking on the canonical Prolog representation

`ReaderUnitClosure.linkDisjoint` intentionally rejects predicate collisions.
This linker handles the strictly smaller SWI module fragment needed by the
pinned parser closure: one optional module declaration per unit, predicate and
DCG exports, ordinary import lists, and unambiguous lookup in the loaded export
index.  It rewrites only relation symbols in the existing `SourceSignature`;
it introduces no term language or evaluator.

Meta-predicate argument qualification inside named modules, reexports, runtime
module creation, and execution of retained loader goals remain outside this
fragment. Direct calls in retained declarations and loader goals are qualified
by the same plan as clause bodies. For the finite collection of module-less
units that share SWI's `user` context, imported predicates additionally receive
one canonical forwarding clause. This makes ground predicate reflection and a
runtime-built unqualified call observe the same import without teaching the
runtime a second module resolver. Because a qualified executable clause no
longer reclassifies from its original source term without module context,
linked and forwarding clauses deliberately clear `sourceTerm`. The original
source units remain in the result as the provenance authority.
-/

namespace Mettapedia.Logic.Prolog.ReaderModuleLink

open ReaderUnit ReaderUnitClosure SourceSignature

inductive Error where
  | multipleModuleDeclarations (key : String)
  | malformedModuleName (key : String)
  | malformedExportList (key : String)
  | malformedExport (key : String)
  | malformedImportSelection (key : String)
  | unexportedSelection (key target : String)
      (symbol : SourceSignature.PredicateIndicator)
  | ambiguousImport (key : String) (symbol : SourceSignature.PredicateIndicator)
      (first second : String)
  | qualifiedNameCollision (symbol : SourceSignature.PredicateIndicator)
  | predicateCollision (symbol : SourceSignature.PredicateIndicator)
deriving Repr

private def atomName? : SourceSignature.Term → Option String
  | .const (.atom name) => some name
  | _ => none

private def properListAux : Nat → SourceSignature.Term →
    Option (List SourceSignature.Term)
  | 0, _ => none
  | _ + 1, .const .nil => some []
  | fuel + 1, .app indicator arguments =>
      match indicator.name, List.ofFn arguments with
      | "[|]", [head, tail] => do
          let rest ← properListAux fuel tail
          pure (head :: rest)
      | _, _ => none
  | _ + 1, _ => none

private def properList? (term : SourceSignature.Term) :
    Option (List SourceSignature.Term) :=
  properListAux (term.size + 1) term

private def natural? : SourceSignature.Term → Option Nat
  | .const (.integer value) =>
      if value < 0 then none else some value.toNat
  | _ => none

private def predicateIndicator? : SourceSignature.Term →
    Option SourceSignature.PredicateIndicator
  | .app indicator arguments =>
      match indicator.name, List.ofFn arguments with
      | "/", [nameTerm, arityTerm] => do
          let name ← atomName? nameTerm
          let arity ← natural? arityTerm
          pure { name, arity }
      | "//", [nameTerm, arityTerm] => do
          let name ← atomName? nameTerm
          let arity ← natural? arityTerm
          pure { name, arity := arity + 2 }
      | _, _ => none
  | _ => none

private structure ModuleInfo where
  name : String
  exports : List SourceSignature.PredicateIndicator

private structure Plan where
  key : String
  unit : ReaderUnit.Unit
  moduleInfo : Option ModuleInfo
  localSymbols : List SourceSignature.PredicateIndicator

private def moduleInfo (key : String) (unit : ReaderUnit.Unit) :
    Except Error (Option ModuleInfo) :=
  match unit.moduleDecls with
  | [] => pure none
  | [declaration] => do
      let name ← match atomName? declaration.name with
        | some name => pure name
        | none => .error (.malformedModuleName key)
      let entries ← match properList? declaration.exports with
        | some entries => pure entries
        | none => .error (.malformedExportList key)
      let exports ← entries.mapM fun entry =>
        match predicateIndicator? entry with
        | some symbol => pure symbol
        | none => .error (.malformedExport key)
      pure (some { name, exports })
  | _ => .error (.multipleModuleDeclarations key)

private def planOf (named : ReaderUnitClosure.NamedUnit String) :
    Except Error Plan := do
  pure {
    key := named.key
    unit := named.unit
    moduleInfo := ← moduleInfo named.key named.unit
    localSymbols := ReaderUnitClosure.definedSymbols named.unit.program
  }

private def qualify (moduleName : Option String)
    (symbol : SourceSignature.PredicateIndicator) :
    SourceSignature.PredicateIndicator :=
  match moduleName with
  | none => symbol
  | some name => { symbol with name := name ++ ":" ++ symbol.name }

private structure ImportBinding where
  source : SourceSignature.PredicateIndicator
  target : SourceSignature.PredicateIndicator
  moduleName : String

private def findPlan? (plans : List Plan) (key : String) : Option Plan :=
  plans.find? fun plan => plan.key = key

private def selectedExports (plan target : Plan) (request : ReaderUnit.Import) :
    Except Error (List SourceSignature.PredicateIndicator) := do
  let info ← match target.moduleInfo with
    | some info => pure info
    | none => pure { name := "", exports := [] }
  match request.options with
  | [] => pure info.exports
  | [selection] => do
      let entries ← match properList? selection with
        | some entries => pure entries
        | none => .error (.malformedImportSelection plan.key)
      entries.mapM fun entry => do
        let symbol ← match predicateIndicator? entry with
          | some symbol => pure symbol
          | none => .error (.malformedImportSelection plan.key)
        if symbol ∈ info.exports then pure symbol
        else .error (.unexportedSelection plan.key target.key symbol)
  | _ => .error (.malformedImportSelection plan.key)

private def bindingsForImport
    (sourceKey? : SourceSignature.Term → Option String)
    (plans : List Plan) (plan : Plan) (request : ReaderUnit.Import) :
    Except Error (List ImportBinding) := do
  let some key := sourceKey? request.source | pure []
  let some target := findPlan? plans key | pure []
  let some info := target.moduleInfo | pure []
  let exports ← selectedExports plan target request
  pure (exports.map fun symbol => {
    source := symbol
    target := qualify (some info.name) symbol
    moduleName := info.name
  })

private def insertBinding (key : String) (bindings : List ImportBinding)
    (next : ImportBinding) : Except Error (List ImportBinding) :=
  match bindings.find? fun binding => binding.source = next.source with
  | none => pure (bindings ++ [next])
  | some previous =>
      if previous.target = next.target then pure bindings
      else .error (.ambiguousImport key next.source previous.moduleName
        next.moduleName)

private def importBindings
    (sourceKey? : SourceSignature.Term → Option String)
    (plans : List Plan) (plan : Plan) : Except Error (List ImportBinding) := do
  let groups ← plan.unit.imports.mapM
    (bindingsForImport sourceKey? plans plan)
  groups.flatten.foldlM (insertBinding plan.key) []

private def calledSymbols : SourceSignature.Goal →
    List SourceSignature.PredicateIndicator
  | .call atom => [atom.symbol]
  | .conj left right | .disj left right =>
      calledSymbols left ++ calledSymbols right
  | .ifThenElse condition thenBranch elseBranch
  | .softIfThenElse condition thenBranch elseBranch =>
      calledSymbols condition ++ calledSymbols thenBranch ++
        calledSymbols elseBranch
  | .once goal | .transaction goal | .neg goal => calledSymbols goal
  | .findall _ generator _ => calledSymbols generator
  | .catch guarded _ recovery =>
      calledSymbols guarded ++ calledSymbols recovery
  | _ => []

private def usedSymbols (plan : Plan) :
    List SourceSignature.PredicateIndicator :=
  ((plan.unit.program.flatMap fun clause => calledSymbols clause.body) ++
    (plan.unit.declarations.flatMap calledSymbols) ++
    (plan.unit.pendingGoals.flatMap calledSymbols)).eraseDups

private def exportedProviders (plans : List Plan)
    (symbol : SourceSignature.PredicateIndicator) : List ImportBinding :=
  plans.filterMap fun candidate => do
    let info ← candidate.moduleInfo
    if symbol ∈ info.exports then some {
      source := symbol
      target := qualify (some info.name) symbol
      moduleName := info.name
    } else none

/-- SWI's autoloader resolves an otherwise-unbound call from the export index.
For a finite source slice we accept only the deterministic case: exactly one
loaded module exports the called predicate.  Private predicates are never
candidates, and ambiguous exports fail rather than depending on host search
order. -/
private def addUniqueExportBinding (plans : List Plan) (plan : Plan)
    (bindings : List ImportBinding)
    (symbol : SourceSignature.PredicateIndicator) :
    Except Error (List ImportBinding) :=
  if symbol ∈ plan.localSymbols ||
      bindings.any (fun binding => binding.source = symbol) then
    pure bindings
  else
    match exportedProviders plans symbol with
    | [] => pure bindings
    | [binding] => pure (bindings ++ [binding])
    | first :: second :: _ =>
        .error (.ambiguousImport plan.key symbol first.moduleName
          second.moduleName)

private def symbolBindings
    (sourceKey? : SourceSignature.Term → Option String)
    (plans : List Plan) (plan : Plan) : Except Error (List ImportBinding) := do
  let explicit ← importBindings sourceKey? plans plan
  (usedSymbols plan).foldlM (addUniqueExportBinding plans plan) explicit

private def sourceSymbols (plans : List Plan) :
    List SourceSignature.PredicateIndicator :=
  (plans.flatMap fun plan => plan.localSymbols ++ usedSymbols plan).eraseDups

/-- The canonical source signature currently stores relation names as strings.
Fail if a generated `module:name` spelling is already used literally by the
finite source slice; this keeps static qualification injective on the linked
program instead of silently conflating a quoted atom with a module target. -/
private def validateQualifiedNames (plans : List Plan) :
    Except Error _root_.Unit := do
  let original := sourceSymbols plans
  for plan in plans do
    match plan.moduleInfo with
    | none => pure ()
    | some info =>
        for symbol in plan.localSymbols do
          let qualified := qualify (some info.name) symbol
          if qualified ∈ original then
            .error (.qualifiedNameCollision qualified)
          else pure ()

private def resolveSymbol (plan : Plan) (bindings : List ImportBinding)
    (symbol : SourceSignature.PredicateIndicator) :
    SourceSignature.PredicateIndicator :=
  if symbol ∈ plan.localSymbols then
    qualify (plan.moduleInfo.map (fun info => info.name)) symbol
  else
    match bindings.find? fun binding => binding.source = symbol with
    | some binding => binding.target
    | none => symbol

private def mapAtom (resolve : SourceSignature.PredicateIndicator →
    SourceSignature.PredicateIndicator) (atom : SourceSignature.Atom) :
    SourceSignature.Atom :=
  let arguments := List.ofFn atom.args
  SourceSignature.predicate (resolve atom.symbol).name arguments

private def mapGoal (resolve : SourceSignature.PredicateIndicator →
    SourceSignature.PredicateIndicator) :
    SourceSignature.Goal → SourceSignature.Goal
  | .call atom => .call (mapAtom resolve atom)
  | .succeed => .succeed
  | .fail => .fail
  | .cut => .cut
  | .conj left right => .conj (mapGoal resolve left) (mapGoal resolve right)
  | .disj left right => .disj (mapGoal resolve left) (mapGoal resolve right)
  | .ifThenElse condition thenBranch elseBranch =>
      .ifThenElse (mapGoal resolve condition) (mapGoal resolve thenBranch)
        (mapGoal resolve elseBranch)
  | .softIfThenElse condition thenBranch elseBranch =>
      .softIfThenElse (mapGoal resolve condition) (mapGoal resolve thenBranch)
        (mapGoal resolve elseBranch)
  | .once goal => .once (mapGoal resolve goal)
  | .transaction goal => .transaction (mapGoal resolve goal)
  | .neg goal => .neg (mapGoal resolve goal)
  | .unify left right => .unify left right
  | .notUnify left right => .notUnify left right
  | .isVar term => .isVar term
  | .findall template generator bag =>
      .findall template (mapGoal resolve generator) bag
  | .catch guarded catcher recovery =>
      .catch (mapGoal resolve guarded) catcher (mapGoal resolve recovery)
  | .throw ball => .throw ball

private def mapClause (resolve : SourceSignature.PredicateIndicator →
    SourceSignature.PredicateIndicator) (clause : SourceSignature.Clause) :
    SourceSignature.Clause := {
  head := mapAtom resolve clause.head
  body := mapGoal resolve clause.body
  sourceTerm := none
}

/-- Canonical variables for one finite import forwarding clause.  Runtime
standardization-apart supplies the activation scope; these source identities
only preserve argument positions. -/
def moduleAliasVariables (arity : Nat) : List SourceSignature.Term :=
  (List.range arity).map fun occurrence =>
    SourceSignature.var "__module_import" occurrence

/-- Materialize one same-arity import as an ordinary canonical clause.  The
shared runtime therefore resolves a dynamically constructed unqualified call
by its normal clause-selection path, while the body uses the statically proven
qualified target. -/
def moduleAliasClause (source : SourceSignature.PredicateIndicator)
    (targetName : String) :
    SourceSignature.Clause :=
  let arguments := moduleAliasVariables source.arity
  {
    head := SourceSignature.predicate source.name arguments
    body := .call (SourceSignature.predicate targetName arguments)
    sourceTerm := none
  }

@[simp]
theorem moduleAliasClause_head_symbol
    (source : SourceSignature.PredicateIndicator) (targetName : String) :
    (moduleAliasClause source targetName).head.symbol = source := by
  simp [moduleAliasClause, moduleAliasVariables, SourceSignature.predicate]

@[simp]
theorem moduleAliasClause_sourceTerm
    (source : SourceSignature.PredicateIndicator) (targetName : String) :
    (moduleAliasClause source targetName).sourceTerm = none := rfl

@[simp]
theorem moduleAliasClause_body_symbol
    (source : SourceSignature.PredicateIndicator) (targetName : String) :
    (match (moduleAliasClause source targetName).body with
      | .call atom => some atom.symbol
      | _ => none) =
      some { name := targetName, arity := source.arity } := by
  simp [moduleAliasClause, moduleAliasVariables, SourceSignature.predicate]

private def sharedUserLocalSymbols (planned : List (Plan × List ImportBinding)) :
    List SourceSignature.PredicateIndicator :=
  (planned.flatMap fun entry =>
    let (plan, _) := entry
    if plan.moduleInfo.isNone then plan.localSymbols else []).eraseDups

/-- Module-less source files are loaded into one `user` context.  Collect
their imports once, discard aliases shadowed by a real user definition, merge
identical imports, and reject target disagreement. -/
private def sharedUserAliases (planned : List (Plan × List ImportBinding)) :
    Except Error (List ImportBinding) := do
  let locals := sharedUserLocalSymbols planned
  let candidates := planned.flatMap fun entry =>
    let (plan, bindings) := entry
    if plan.moduleInfo.isNone then bindings else []
  candidates.foldlM (fun aliases binding =>
    if binding.source ∈ locals then pure aliases
    else insertBinding "user" aliases binding) []

private def appendProgram (program : SourceSignature.Program)
    (next : SourceSignature.Program) : Except Error SourceSignature.Program :=
  match ReaderUnitClosure.firstOverlap
      (ReaderUnitClosure.definedSymbols program)
      (ReaderUnitClosure.definedSymbols next) with
  | some symbol => .error (.predicateCollision symbol)
  | none => pure (program ++ next)

/-- Link a finite closure using static module exports and imports.  The output
is still a `FlatLink` over the canonical program type; its retained units are
the original source/provenance objects, while `program` is the qualified
executable projection. -/
def link (sourceKey? : SourceSignature.Term → Option String)
    (closure : ReaderUnitClosure.Closure String) :
    Except Error (ReaderUnitClosure.FlatLink String) := do
  let plans ← closure.units.mapM planOf
  validateQualifiedNames plans
  let planned ← plans.mapM fun plan => do
    let bindings ← symbolBindings sourceKey? plans plan
    pure (plan, bindings)
  let qualifiedProgram ← planned.foldlM (fun program entry => do
    let (plan, bindings) := entry
    let resolve := resolveSymbol plan bindings
    appendProgram program (plan.unit.program.map (mapClause resolve))) []
  let aliases ← sharedUserAliases planned
  let aliasProgram := aliases.map fun binding =>
    moduleAliasClause binding.source binding.target.name
  let program ← appendProgram qualifiedProgram aliasProgram
  pure {
    program
    units := closure.units
    external := closure.external
    declarations := planned.flatMap fun entry =>
      let (plan, bindings) := entry
      let resolve := resolveSymbol plan bindings
      plan.unit.declarations.map fun goal =>
        (plan.key, mapGoal resolve goal)
    pendingGoals := planned.flatMap fun entry =>
      let (plan, bindings) := entry
      let resolve := resolveSymbol plan bindings
      plan.unit.pendingGoals.map fun goal =>
        (plan.key, mapGoal resolve goal)
  }

end Mettapedia.Logic.Prolog.ReaderModuleLink
