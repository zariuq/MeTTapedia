import Mettapedia.GSLT.LanguageDef.IndexedInductiveOperationSource
import Mettapedia.GSLT.LanguageDef.IndexedInductiveAppendElaboration
import Mettapedia.GSLT.LanguageDef.ModuleSource.Commands
import Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedNatVecSource
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorProgramChecking
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorComputationProfiles

/-!
# A textual Nat/Vec/append input to the existing checking target

The common module reader retains both the source declarations and four
operation clauses. A finite, untrusted producer resolves constructor patterns,
derives recursive-call plans from the source fields, compiles addition before
using it in append, and proposes the closed core function. The actual input
is compared with the independent admitted Nat/Vec inventory and checked core.

This qualifies the selected textual program. It is not correctness of this
producer for every module, general packed-parse completeness, dependent
function-signature syntax, full computation admission or native execution.
The requested dependent function type is supplied by the checking query.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductive.AppendSource

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
open Mettapedia.OSLF.MeTTaIL.Syntax
open ModuleSource.Commands CaseElaboration OperationSource Programs

#module_file "../../../../../metta/gslt/module/IndexedNatVecAppend.module"
#module_roundtrip IndexedNatVecAppend

def names : ModuleSource.IndexedNatVecSource.Names := {}
def addName : DeclName := `Authored.add
def appendName : DeclName := `Authored.append

def fieldTag (index : Nat) : String := "field." ++ toString index

def fieldSlots (ambient fields : Nat) : List (String × Fin (ambient + fields)) :=
  List.ofFn fun index : Fin fields =>
    (fieldTag index.val, ⟨fields - 1 - index.val, by omega⟩)

def fieldVariable (ambient fields : Nat) (index : Fin fields) : Tower.Tm (ambient + fields) :=
  .var ⟨fields - 1 - index.val, by omega⟩

def constructorPattern (constructor : ModuleSource.InductiveSyntax.Constructor)
    (parameterPatterns : List Pattern) : Pattern :=
  .apply constructor.name (parameterPatterns ++
    List.ofFn (fun index : Fin constructor.fields.length => .fvar (fieldTag index.val)))

/-- Source declaration names resolve before the operation's source binders.
The selected fixture has fresh field names and one explicit payload parameter. -/
def declarationEnvironment (constructor : ModuleSource.InductiveSyntax.Constructor) :
    String → Option Pattern :=
  fun sourceName => match findName (constructor.fields.map (·.name)) sourceName with
    | some index => some (.fvar (fieldTag index.val))
    | none => if sourceName = "A" then some (.fvar "ambient.A") else none

def quoteDeclaration (environment : String → Option Pattern) :
    ModuleSource.InductiveSyntax.Term → Option Pattern
  | .name sourceName => some ((environment sourceName).getD (.apply sourceName []))
  | .app function argument => do
      let function ← quoteDeclaration environment function
      let argument ← quoteDeclaration environment argument
      match function with
      | .apply sourceName arguments => some (.apply sourceName (arguments ++ [argument]))
      | _ => none
  | .arrow _ _ => none
  | .pi _ _ _ => none
  | .project _ _ _ => none

theorem quoteDeclaration_constructor_application :
    quoteDeclaration (fun _ => none) (.app (.name "Vec") (.name "Nat")) =
      some (.apply "Vec" [.apply "Nat" []]) := rfl

theorem quoteDeclaration_refuses_dependent_product
    (environment : String → Option Pattern) (binder : String)
    (domain codomain : ModuleSource.InductiveSyntax.Term) :
    quoteDeclaration environment (.pi binder domain codomain) = none := rfl

theorem quoteDeclaration_refuses_projection
    (environment : String → Option Pattern) (owner : String) (field : Nat)
    (record : ModuleSource.InductiveSyntax.Term) :
    quoteDeclaration environment (.project owner field record) = none := rfl

def naturalHeader (constructor : ModuleSource.InductiveSyntax.Constructor) : Header 2 :=
  let fields := constructor.fields.length
  ⟨constructor.name, fields,
    .apply "Add" [constructorPattern constructor [], .fvar "ambient.m"],
    ("ambient.m", ⟨fields, by omega⟩) :: fieldSlots 2 fields⟩

def vectorSlots (fields : Nat) : List (String × Fin (5 + fields)) :=
  [("ambient.A", ⟨4 + fields, by omega⟩), ("ambient.m", ⟨2 + fields, by omega⟩),
    ("ambient.ys", ⟨fields, by omega⟩)] ++ fieldSlots 5 fields

def vectorHeader (constructor : ModuleSource.InductiveSyntax.Constructor) : Option (Header 5) := do
  if !(decide (constructor.fields.map (·.name)).Nodup) then none else do
    let result ← quoteDeclaration (declarationEnvironment constructor) constructor.result
    match result with
    | .apply "Vec" [parameter, index] =>
        if parameter = .fvar "ambient.A" then
          let fields := constructor.fields.length
          some ⟨constructor.name, fields,
            .apply "Append" [.fvar "ambient.A", index, .fvar "ambient.m",
              constructorPattern constructor [.fvar "ambient.A"], .fvar "ambient.ys"],
            vectorSlots fields⟩
        else none
    | _ => none

def naturalPlan (constructor : ModuleSource.InductiveSyntax.Constructor) : BranchPlan Tower.Head 2 :=
  let fields := constructor.fields.length
  ⟨constructor.name, fields, List.ofFn fun index : Fin fields =>
    Declaration.IndexedFamily.applyArgs (.const addName)
      [fieldVariable 2 fields index, .var ⟨fields, by omega⟩]⟩

def constructorSymbols : List (Symbol Tower.Head) :=
  [⟨"Zero", 0, zeroTm⟩, ⟨"Succ", 1, succApp (.var 0)⟩,
    ⟨"Nil", 1, vnilApp (.var 0)⟩,
    ⟨"Cons", 4, vconsApp (.var 3) (.var 2) (.var 1) (.var 0)⟩]

def addSelf : Symbol Tower.Head :=
  ⟨"Add", 2, Declaration.IndexedFamily.applyArgs (.const addName) [.var 1, .var 0]⟩

def appendSelf : Symbol Tower.Head :=
  ⟨"Append", 5, Declaration.IndexedFamily.applyArgs (.const appendName)
    [.var 4, .var 3, .var 2, .var 1, .var 0]⟩

def vectorPlan (symbols : List (Symbol Tower.Head))
    (constructor : ModuleSource.InductiveSyntax.Constructor) : Option (BranchPlan Tower.Head 5) := do
  let _ ← vectorHeader constructor
  let fields := constructor.fields.length
  let children ← (List.finRange fields).mapM fun index => do
    let field := constructor.fields.get index
    if field.type = .name "Nat" ∨ field.type = .name "A" then some none else do
      let quoted ← quoteDeclaration (declarationEnvironment constructor) field.type
      match quoted with
      | .apply "Vec" [parameter, indexPattern] =>
          if parameter = .fvar "ambient.A" then do
            let childIndex ← lower symbols (variableEnvironment (vectorSlots fields)) 32 indexPattern
            some (some (Declaration.IndexedFamily.applyArgs (.const appendName)
              [.var ⟨4 + fields, by omega⟩, childIndex, .var ⟨2 + fields, by omega⟩,
                fieldVariable 5 fields index, .var ⟨fields, by omega⟩]))
          else none
      | _ => none
  return ⟨constructor.name, fields, children.filterMap id⟩

def readClauses {n : Nat} (symbols : List (Symbol Tower.Head)) (headers : List (Header n))
    (rows : List RewriteRule) : Option (List (Clause Tower.Head n)) := do
  if headers.length = rows.length then
    (headers.zip rows).mapM fun (header, row) =>
      (readRule symbols 64 header row).map (·.toClause)
  else none

structure Proposed where
  addition : Tower.Tm 2
  appendFunction : Tower.Tm 0
  naturalClauses : List (Clause Tower.Head 2)
  vectorClauses : List (Clause Tower.Head 5)

/-- The producer preserves a complete direct declaration/operation source.
Its correctness claims below concern the actual named input, not all modules
for which this untrusted procedure might return a proposal. -/
def propose (policy : NamePolicy) (source : ModuleSource.Module) : Option Proposed := do
  let selected ← selectModule source
  let (natural, vector) ← ModuleSource.IndexedNatVecSource.select selected.declarations
  if !(ModuleSource.IndexedNatVecSource.check names selected.declarations) then none else do
    if selected.rules.length ≠ natural.constructors.length + vector.constructors.length then none else do
      let sourceRows := selected.rules.map (resolveRule constructorSymbols policy)
      let naturalClauses ← readClauses (constructorSymbols ++ [addSelf])
        (natural.constructors.map naturalHeader) (sourceRows.take natural.constructors.length)
      let naturalMethods ← compilePlans (natural.constructors.map naturalPlan) addName naturalClauses
      match naturalMethods with
      | [zeroMethod, succMethod] =>
          let addition := natEliminateApp (.lam natTm) zeroMethod succMethod (.var 1)
          let symbols := constructorSymbols ++ [⟨"Add", 2, addition⟩, appendSelf]
          let vectorHeaders ← vector.constructors.mapM vectorHeader
          let vectorClauses ← readClauses symbols vectorHeaders
            (sourceRows.drop natural.constructors.length)
          let vectorPlans ← vector.constructors.mapM (vectorPlan symbols)
          let vectorMethods ← compilePlans vectorPlans appendName vectorClauses
          match vectorMethods with
          | [nilMethod, consMethod] =>
              return ⟨addition,
                TelescopeAbstraction.closeTerm appendContext
                  (vecEliminateApp (.var 4) (appendMotive (.var 4) (.var 2))
                    nilMethod consMethod (.var 3) (.var 1)), naturalClauses, vectorClauses⟩
          | _ => none
      | _ => none

def proposedAddition : Option (Tower.Tm 2) :=
  (propose .declaredNullary IndexedNatVecAppend.module).map (·.addition)
def proposedAppend : Option (Tower.Tm 0) :=
  (propose .declaredNullary IndexedNatVecAppend.module).map (·.appendFunction)

def sourceVectorPlans : Option (List (BranchPlan Tower.Head 5)) := do
  let selected ← selectModule IndexedNatVecAppend.module
  let (_, vector) ← ModuleSource.IndexedNatVecSource.select selected.declarations
  vector.constructors.mapM (vectorPlan constructorSymbols)

theorem source_vector_plans_match (A : Type) : sourceVectorPlans = some
    ((AppendElaboration.admitted A).constructors.map fun constructor =>
      plan (AppendElaboration.indices A) constructor AppendElaboration.callTemplate) := by
  change sourceVectorPlans = some
    ((AppendElaboration.admitted Unit).constructors.map fun constructor =>
      plan (AppendElaboration.indices Unit) constructor AppendElaboration.callTemplate)
  decide +kernel

theorem source_reconstructed :
    (selectModule IndexedNatVecAppend.module).map (·.assemble) = some IndexedNatVecAppend.module := rfl

theorem text_admitted (A : Type) :
    ((selectModule IndexedNatVecAppend.module).bind fun selected =>
      ModuleSource.IndexedNatVecSource.admitModule A names selected.declarations) =
      some (IndexedInductiveNatVec.Vectors.admitted A) := rfl

theorem addition_matches_reference : proposedAddition = some (add (.var 1) (.var 0)) := by decide +kernel
theorem append_matches_reference : proposedAppend = some appendTerm := by decide +kernel

theorem append_typed (term : Tower.Tm 0) (compiled : proposedAppend = some term) :
    FormationSensitive.Judgment Programs.rules .nil term appendType := by
  rw [append_matches_reference] at compiled
  cases Option.some.inj compiled
  exact Programs.append_typed

theorem append_typed_naturalOnly (term : Tower.Tm 0) (compiled : proposedAppend = some term) :
    FormationSensitive.Judgment (ComputationProfiles.rules ComputationProfiles.naturalOnly)
      .nil term appendType := by
  rw [append_matches_reference] at compiled
  cases Option.some.inj compiled
  exact ComputationProfiles.append_typed_naturalOnly

local instance : DecidableRel Programs.rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred Programs.rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (Programs.rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel Programs.rules.cumulative :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.cumulative h u))
local instance : DecidableRel Programs.rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

/-- Replay is independent of the textual producer. It validates the actual
proposed term at the requested dependent type with the retained submission. -/
def checkProposal (policy : NamePolicy) (source : ModuleSource.Module) : Bool :=
  match propose policy source with
  | none => false
  | some proposed => FormationSensitiveElaboration.replay Programs.rules Programs.decoder
      .nil proposed.appendFunction appendType appendEvidence

theorem checkProposal_sound (policy : NamePolicy) (source : ModuleSource.Module)
    (accepted : checkProposal policy source = true) :
    ∃ proposed, propose policy source = some proposed ∧
      FormationSensitive.Judgment Programs.rules .nil proposed.appendFunction appendType := by
  cases found : propose policy source with
  | none => simp [checkProposal, found] at accepted
  | some proposed =>
      refine ⟨proposed, rfl, ?_⟩
      exact FormationSensitiveElaboration.replay_sound _ _ (by
        simpa [checkProposal, found] using accepted)

def changedRules (change : List RewriteRule → List RewriteRule) : Option ModuleSource.Module :=
  (selectModule IndexedNatVecAppend.module).map fun selected => { selected with rules := change selected.rules }.assemble

def changedProposal (change : List RewriteRule → List RewriteRule) : Bool :=
  match changedRules change with
  | none => false
  | some source => checkProposal .declaredNullary source

def literalZeroProposal : Bool :=
  match changedRules (fun rows => rows.mapIdx fun index row =>
      if index = 0 then { row with left := .apply "Add" [.fvar "Zero", .fvar "m"] } else row) with
  | none => false
  | some source => checkProposal .literalVariables source

def replaceLastBody (body : Pattern) (rows : List RewriteRule) : List RewriteRule :=
  rows.mapIdx fun index row => if index + 1 = rows.length then { row with right := body } else row

def omittedRecursion : Pattern :=
  .apply "Cons" [.fvar "A", .apply "Add" [.fvar "k", .fvar "m"], .fvar "x", .fvar "tail"]

def wrongChild : Pattern :=
  .apply "Cons" [.fvar "A", .apply "Add" [.fvar "k", .fvar "m"], .fvar "x",
    .apply "Append" [.fvar "A", .fvar "k", .fvar "m", .fvar "x", .fvar "ys"]]

def verdicts : List (String × Bool) := [
  ("textual append compiles to the checked function", proposedAppend == some appendTerm),
  ("textual addition comes from its source clauses", proposedAddition == some (add (.var 1) (.var 0))),
  ("textual append passes independent dependent replay", checkProposal .declaredNullary IndexedNatVecAppend.module),
  ("literal nullary-name variable retains its distinct refusal", !literalZeroProposal),
  ("textual program refuses missing clauses", !(changedProposal (·.drop 1))),
  ("textual program refuses extra clauses", !(changedProposal (fun rows => rows ++ rows.take 1))),
  ("textual program refuses reordered clauses", !(changedProposal List.reverse)),
  ("omitted recursion fails the submitted dependent evidence", !(changedProposal (replaceLastBody omittedRecursion))),
  ("call on the wrong recursive child refuses", !(changedProposal (replaceLastBody wrongChild))),
  ("unbound source result refuses", !(changedProposal (replaceLastBody (.fvar "unknown")))),
  ("unsupported extra source block refuses", !(checkProposal .declaredNullary
    { IndexedNatVecAppend.module with theories :=
      [⟨"Data", [], .extend none [.types ["Ignored"]]⟩] })),
  ("unresolved source import refuses", !(checkProposal .declaredNullary
    { IndexedNatVecAppend.module with imports := [⟨"Other.module", "other"⟩] }))]

theorem all_verdicts : verdicts.all (·.2) = true := by decide +kernel

end Mettapedia.GSLT.LanguageDef.IndexedInductive.AppendSource
