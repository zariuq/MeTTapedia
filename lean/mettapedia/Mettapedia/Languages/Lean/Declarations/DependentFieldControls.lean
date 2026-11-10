import Mettapedia.Languages.Lean.Declarations.Profile
import Mettapedia.GSLT.LanguageDef.ModuleSource.InductiveMeTTaData

/-!
# Dependent law fields retain their binding and erasure information

An algebraic structure's universally quantified law must remain a proposition
about its operation. Its admission inventory keeps the law as a scoped guard;
this does not by itself provide a target interpretation of that guard.
-/

namespace Mettapedia.Languages.Lean.Declarations.DependentFieldControls

open _root_.Lean Meta
open Mettapedia.GSLT.LanguageDef.ModuleSource
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

structure AssociativeOperation (α : Type) where
  operation : α → α → α
  associative : ∀ a b c, operation (operation a b) c = operation a (operation b c)

structure UnitalOperation (α : Type) extends AssociativeOperation α where
  unit : α
  leftIdentity : ∀ a, operation unit a = a

structure ReflexiveLaw (α : Type) where
  reflexive : ∀ a : α, a = a

run_meta do
  let .ok reading ← read ``AssociativeOperation
    | throwError "dependent law field was not read"
  let [constructor] := reading.family.constructors
    | throwError "expected one structure constructor"
  let [_, ⟨_, .pi _ _ (.pi _ _ (.pi _ _ _))⟩] := constructor.fields
    | throwError "the universally quantified law lost a binder"
  unless reading.keptFields == [[true, false]] do
    throwError "the operation must be retained and its proof erased"
  match Profile.admit Profile.Model.syntactic reading.family reading.proofFields reading.keptFields with
  | .ok _ => pure ()
  | .error reason => throwError "quantified constructor guard was refused: {repr reason}"

run_meta do
  let .ok reading ← read ``UnitalOperation
    | throwError "inherited operation and law were not read"
  unless reading.keptFields == [[true, true, false]] do
    throwError "the parent and unit must be retained and the law erased"
  match Profile.guards Profile.Model.syntactic reading.family reading.proofFields with
  | .ok [[_]] => pure ()
  | _ => throwError "the inherited-operation law was not retained as a guard"

run_meta do
  let .ok reading ← read ``ReflexiveLaw
    | throwError "closed quantified law was not read"
  match Profile.guards Profile.Model.syntactic reading.family reading.proofFields with
  | .ok [[guard]] =>
      unless guard.depth == 0 do throwError "the closed law invented a free constructor field"
  | _ => throwError "a quantified law without data fields must remain a guard"

def lawSyntax : InductiveSyntax.Term :=
  .pi "x" (.name "A") (.app (.name "P") (.name "x"))

example : InductiveMeTTaData.readTerm (InductiveMeTTaData.termData lawSyntax) = some lawSyntax :=
  InductiveMeTTaData.readTerm_termData lawSyntax

/-- A binder name must be an identifier, not an expression. -/
example : InductiveMeTTaData.readTerm
    (.expression [.symbol "Pi", .expression [], .symbol "A", .symbol "P"]) = none := by
  simp [InductiveMeTTaData.readTerm]

/-- The binder scopes over the body, not its own domain. -/
example : Profile.mentions "x" (.pi "x" (.name "A") (.name "x")) = false := by decide
example : Profile.mentions "x" (.pi "x" (.name "x") (.name "x")) = true := by decide

/-- Projection positions are natural numbers; a negative field is malformed. -/
example : InductiveMeTTaData.readTerm (.expression [.symbol "Projection", .symbol "Parent",
    .grounded (.int (-1)), .symbol "record"]) = none := by
  simp [InductiveMeTTaData.readTerm]

end Mettapedia.Languages.Lean.Declarations.DependentFieldControls
