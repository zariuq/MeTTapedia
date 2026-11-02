import Mettapedia.Logic.Prolog.ReaderLoader

/-!
# Read-time directive effects

SWI executes directives between `read_term` calls. Only effects that change
the reader environment belong here: local `op/3`, operators exported by a
`module/2` declaration, and operators imported by `use_module`/`autoload`/
`ensure_loaded`. All other directive behavior remains the runtime loader's
responsibility.
-/

namespace Mettapedia.Logic.Prolog.ReaderDirective

open ReaderOperator SourceSignature

structure Update where
  priority : Nat
  specifier : ReaderOperator.Specifier
  names : List String
deriving DecidableEq, Repr

/-- Resolve one canonical source-sink term to the operators exported by that
source. A fail-closed profile reports unknown imports instead of silently
assuming that they export no operators. -/
abbrev ImportProfile (rho : Type) :=
  SourceSignature.Term -> Except rho (List Update)

inductive Error (rho : Type) where
  | malformedOperatorDirective
  | operator (error : ReaderOperator.Error)
  | import (error : rho)

private def application? : SourceSignature.Term ->
    Option (String × List SourceSignature.Term)
  | .const (.atom name) => some (name, [])
  | .app indicator arguments => some (indicator.name, List.ofFn arguments)
  | _ => none

private def atomName? : SourceSignature.Term -> Option String
  | .const (.atom name) => some name
  | _ => none

private def properListAux (lists : SourceSignature.ListEncoding) : Nat -> SourceSignature.Term ->
    Option (List SourceSignature.Term)
  | 0, _ => none
  | _ + 1, .const c => if c = lists.nilConstant then some [] else none
  | fuel + 1, term =>
      match application? term with
      | some (name, [head, tail]) => do
          if name != lists.consName then none else do
            let rest <- properListAux lists fuel tail
            pure (head :: rest)
      | _ => none

private def properList? (lists : SourceSignature.ListEncoding) (term : SourceSignature.Term) :
    Option (List SourceSignature.Term) :=
  properListAux lists (term.size + 1) term

private def specifier? : String -> Option ReaderOperator.Specifier
  | "fx" => some .fx
  | "fy" => some .fy
  | "xf" => some .xf
  | "yf" => some .yf
  | "xfx" => some .xfx
  | "xfy" => some .xfy
  | "yfx" => some .yfx
  | _ => none

private def operatorNames? (lists : SourceSignature.ListEncoding) (term : SourceSignature.Term) : Option (List String) :=
  if let .const c := term then
    if c = lists.nilConstant then some [] else atomName? term |>.map (fun name => [name])
  else
  match atomName? term with
  | some name => some [name]
  | none => do
      let terms <- properList? lists term
      terms.mapM atomName?

private def decodeUpdateArguments (lists : SourceSignature.ListEncoding)
    (arguments : List SourceSignature.Term) : Option Update := do
  let [priorityTerm, specifierTerm, namesTerm] := arguments | none
  let priority <- match priorityTerm with
    | .const (.integer (.ofNat value)) => some value
    | _ => none
  let specifierName <- atomName? specifierTerm
  let specifier <- specifier? specifierName
  let names <- operatorNames? lists namesTerm
  pure { priority, specifier, names }

private def decodeUpdate? (lists : SourceSignature.ListEncoding) (term : SourceSignature.Term) : Option Update := do
  let (name, arguments) <- application? term
  if name = "op" then decodeUpdateArguments lists arguments else none

private def applyUpdate (update : Update) (operators : ReaderOperator.Table) :
    Except (Error rho) ReaderOperator.Table :=
  update.names.foldlM (fun table name =>
    (ReaderOperator.declare update.priority update.specifier name table).mapError
      .operator) operators

private def applyUpdates (updates : List Update)
    (operators : ReaderOperator.Table) :
    Except (Error rho) ReaderOperator.Table :=
  updates.foldlM (fun table update => applyUpdate update table) operators

private def importSources (lists : SourceSignature.ListEncoding) (term : SourceSignature.Term) :
    List SourceSignature.Term :=
  match properList? lists term with
  | some sources => sources
  | none => [term]

private def applyImports (lists : SourceSignature.ListEncoding) (profile : ImportProfile rho)
    (sourceTerm : SourceSignature.Term) (operators : ReaderOperator.Table) :
    Except (Error rho) ReaderOperator.Table :=
  (importSources lists sourceTerm).foldlM (fun table source => do
    let updates <- (profile source).mapError .import
    applyUpdates updates table) operators

private def applyExportList (lists : SourceSignature.ListEncoding) (exports : SourceSignature.Term)
    (operators : ReaderOperator.Table) :
    Except (Error rho) ReaderOperator.Table := do
  let entries <- match properList? lists exports with
    | some entries => pure entries
    | none => .error .malformedOperatorDirective
  entries.foldlM (fun table entry =>
    match application? entry with
    | some ("op", arguments) =>
        match decodeUpdateArguments lists arguments with
        | some update => applyUpdate update table
        | none => .error .malformedOperatorDirective
    | _ => .ok table) operators

private def applyCall (lists : SourceSignature.ListEncoding) (profile : ImportProfile rho)
    (atom : SourceSignature.Atom) (operators : ReaderOperator.Table) :
    Except (Error rho) ReaderOperator.Table :=
  let arguments := List.ofFn atom.args
  match atom.symbol.name, arguments with
  | "op", arguments =>
      match decodeUpdateArguments lists arguments with
      | some update => applyUpdate update operators
      | none => .error .malformedOperatorDirective
  | "module", [_moduleName, exports] => applyExportList lists exports operators
  | "use_module", source :: _ => applyImports lists profile source operators
  | "autoload", source :: _ => applyImports lists profile source operators
  | "ensure_loaded", [source] => applyImports lists profile source operators
  | _, _ => .ok operators

private def applyGoal (lists : SourceSignature.ListEncoding) (profile : ImportProfile rho) :
    SourceSignature.Goal -> ReaderOperator.Table ->
      Except (Error rho) ReaderOperator.Table
  | .call atom, operators => applyCall lists profile atom operators
  | .conj left right, operators => do
      let afterLeft <- applyGoal lists profile left operators
      applyGoal lists profile right afterLeft
  | _, operators => .ok operators

/-- Reader effect that applies only read-time operator consequences. The
directive itself remains in the returned source-form list for ordinary runtime
execution. -/
def effectWithLists (lists : SourceSignature.ListEncoding) (profile : ImportProfile rho) :
    ReaderLoader.Effect (Error rho) :=
  fun form operators =>
    match form with
    | .directive goal => applyGoal lists profile goal operators
    | _ => .ok operators

/-- Existing runtime loading uses the SWI source list representation. -/
def effectWith (profile : ImportProfile rho) : ReaderLoader.Effect (Error rho) :=
  effectWithLists SourceSignature.swiLists profile

end Mettapedia.Logic.Prolog.ReaderDirective
