import Mettapedia.Logic.Prolog.ReaderSource
import Mettapedia.Languages.Datalog.ProgramStatic

/-! The explicit Datalog interpretation of positive function-free Prolog
source clauses. It uses the existing Datalog IR and static checker. This is
an admission boundary, not an identification of Prolog search with closure.
Declarations are supplied separately, as in the ordinary Datalog pipeline. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.PrologDatalog

open Mettapedia.Logic.Prolog
open Mettapedia.Languages

def value? : SourceSignature.Constant → Option Datalog.Value
  | .atom name => some (.symbol name)
  | .integer n => if Datalog.Value.fits64 (.number n) then some (.number n) else none
  | _ => none

def argument? : SourceSignature.Term → Option Datalog.Argument
  | .var v => some (if v.spelling == "_" then .anonymous else .var v.spelling)
  | .const c => Datalog.Argument.literal <$> value? c
  | .app _ _ => none

def atom? (source : SourceSignature.Atom) : Option Datalog.Atom := do
  pure ⟨[source.symbol.name], ← (List.ofFn source.args).mapM argument?⟩

/-- Named variables must denote one source identity within a clause. The
anonymous spelling may have several identities and remains anonymous in IR. -/
def sourceVariables (source : SourceSignature.Atom) : List SourceSignature.Variable :=
  (List.ofFn source.args).filterMap fun | .var v => some v | _ => none

def coherent (atoms : List SourceSignature.Atom) : Bool :=
  let vs := atoms.flatMap sourceVariables
  vs.all fun v => if v.spelling == "_" then vs.count v == 1 else
    vs.all fun w => v.spelling != w.spelling || decide (v = w)

def clause? (source : SourceSignature.Clause) : Option Datalog.Statement := do
  let .ordinary := source.neck | none
  let body ← source.body.toAtoms?
  if !coherent (source.head :: body) then none else do
    let head ← atom? source.head
    let premises ← body.mapM atom?
    if premises.isEmpty then
      match head.arguments.mapM (fun | .literal v => some v | _ => none) with
      | some values => pure (.fact ⟨head.relation,values⟩)
      | none => pure (.rule ⟨head,[]⟩)
    else pure (.rule ⟨head,premises.map .atom⟩)

def form? : ReaderSource.Form → Option Datalog.Statement
  | .clause source => clause? source
  | _ => none

def program? (declarations : List Datalog.RelationDeclaration) (forms : List ReaderSource.Form) :
    Option Datalog.Program := do
  let statements ← forms.mapM form?
  let program : Datalog.Program := ⟨declarations.map .declaration ++ statements⟩
  if Datalog.ProgramStatic.checkProgram program then some program else none

theorem program?_typed {declarations : List Datalog.RelationDeclaration} {forms : List ReaderSource.Form}
    {program : Datalog.Program} (accepted : program? declarations forms = some program) :
    Datalog.ProgramStatic.ProgramTyped program := by
  unfold program? at accepted
  cases decoded : forms.mapM form? with
  | none => simp [decoded] at accepted
  | some statements =>
      simp only [decoded, bind, Option.bind] at accepted
      split at accepted
      next checked =>
        cases Option.some.inj accepted
        exact (Datalog.ProgramStatic.checkProgram_iff _).mp checked
      next => cases accepted

theorem compound_argument_refused (f : SourceSignature.CompoundIndicator)
    (args : Fin f.arity → SourceSignature.Term) : argument? (.app f args) = none := rfl

theorem directive_refused (goal : SourceSignature.Goal) : form? (.directive goal) = none := rfl

theorem swi_nil_refused : value? .nil = none := rfl
theorem quoted_nil_is_symbol : value? (.atom "[]") = some (.symbol "[]") := rfl

theorem cut_clause_refused (head : SourceSignature.Atom) :
    clause? { head, body := .cut } = none := rfl

end Mettapedia.GSLT.LanguageDef.ModuleFormat.PrologDatalog
