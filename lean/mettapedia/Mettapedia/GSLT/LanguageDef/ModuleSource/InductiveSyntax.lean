/-!
# Authored inductive declarations

Unresolved dependent declaration syntax shared by the grammar-driven and Lean
readers. Parameters, indices and constructor fields are separate ordered
telescopes. Arrows remain syntax even when a selected admission fragment refuses
them. Reading a declaration grants neither positivity nor computation authority.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.InductiveSyntax

inductive Term where
  | name (identifier : String)
  | app (function argument : Term)
  | arrow (domain codomain : Term)
  /-- A dependent product; the name binds only in the codomain. -/
  | pi (binder : String) (domain codomain : Term)
  /-- A kernel structure projection, retaining the owner and field position. -/
  | project (owner : String) (field : Nat) (record : Term)
  deriving DecidableEq, Repr

structure Binder where
  name : String
  type : Term
  deriving DecidableEq, Repr

structure Constructor where
  name : String
  fields : List Binder
  result : Term
  deriving DecidableEq, Repr

structure Family where
  name : String
  parameters : List Binder
  indices : List Binder
  sort : Term
  constructors : List Constructor
  deriving DecidableEq, Repr

/-- Parenthesized printing preserves application and arrow grouping. -/
def Term.print : Term → String
  | .name identifier => identifier
  | .app function argument => "(" ++ function.print ++ " " ++ argument.print ++ ")"
  | .arrow domain codomain => "(" ++ domain.print ++ " -> " ++ codomain.print ++ ")"
  | .pi binder domain codomain =>
      "((" ++ binder ++ " : " ++ domain.print ++ ") -> " ++ codomain.print ++ ")"
  | .project owner field record =>
      "(field " ++ owner ++ " " ++ toString field ++ " " ++ record.print ++ ")"

def Binder.print (binder : Binder) : String := binder.name ++ " : " ++ binder.type.print

def telescope (binders : List Binder) : String :=
  "(" ++ ", ".intercalate (binders.map Binder.print) ++ ")"

def Constructor.print (constructor : Constructor) : String :=
  constructor.name ++ " " ++ telescope constructor.fields ++ " : " ++ constructor.result.print ++ ";"

def Family.print (family : Family) : String :=
  family.name ++ " parameters " ++ telescope family.parameters ++ " indices " ++
    telescope family.indices ++ " : " ++ family.sort.print ++ " { " ++
    " ".intercalate (family.constructors.map Constructor.print) ++ " }"

end Mettapedia.GSLT.LanguageDef.ModuleSource.InductiveSyntax
