import Mettapedia.Logic.Prolog.ReaderNumber

/-!
# Prolog operator declarations

The source reader carries an explicit operator table. Priorities and
specifier meanings follow SWI-Prolog V10.1.9 `src/pl-op.c` and the ISO
`op/3` contract: live declarations have priority `1..1200`, while priority
zero removes a declaration. Prefix, postfix, and infix lookup remain separate
because one atom may legally have several fixities.
-/

namespace Mettapedia.Logic.Prolog.ReaderOperator

inductive Specifier where
  | fx | fy | xf | yf | xfx | xfy | yfx
deriving DecidableEq, Repr

namespace Specifier

def isPrefix : Specifier -> Bool
  | .fx | .fy => true
  | _ => false

def isPostfix : Specifier -> Bool
  | .xf | .yf => true
  | _ => false

def isInfix : Specifier -> Bool
  | .xfx | .xfy | .yfx => true
  | _ => false

/-- Maximum precedence accepted by the left argument. -/
def leftMaximum (priority : Nat) : Specifier -> Option Nat
  | .xf | .xfx | .xfy => some (priority - 1)
  | .yf | .yfx => some priority
  | _ => none

/-- Maximum precedence accepted by the right argument. -/
def rightMaximum (priority : Nat) : Specifier -> Option Nat
  | .fx | .xfx | .yfx => some (priority - 1)
  | .fy | .xfy => some priority
  | _ => none

end Specifier

structure Priority where
  value : Nat
  positive : 0 < value
  bounded : value <= 1200

@[ext]
theorem Priority.ext {first second : Priority}
    (value : first.value = second.value) : first = second := by
  cases first
  cases second
  simp_all

instance : DecidableEq Priority := fun first second =>
  if equal : first.value = second.value then
    isTrue (Priority.ext equal)
  else
    isFalse fun same => equal (congrArg Priority.value same)

structure Declaration where
  name : String
  priority : Priority
  specifier : Specifier
deriving DecidableEq

abbrev Table := List Declaration

inductive Error where
  | priorityOutOfRange (priority : Nat)
deriving DecidableEq, Repr

private def checkedPriority (value : Nat) : Except Error Priority :=
  if positive : 0 < value then
    if bounded : value <= 1200 then
      .ok { value, positive, bounded }
    else .error (.priorityOutOfRange value)
  else .error (.priorityOutOfRange value)

private def replaces (name : String) (specifier : Specifier)
    (declaration : Declaration) : Bool :=
  declaration.name = name &&
    ((declaration.specifier.isPrefix && specifier.isPrefix) ||
      (declaration.specifier.isPostfix && specifier.isPostfix) ||
      (declaration.specifier.isInfix && specifier.isInfix))

/-- Apply one `op/3` declaration. Priority zero removes the selected
name/fixity class; a positive priority replaces that class without disturbing
prefix, postfix, or infix declarations in the other classes. -/
def declare (priority : Nat) (specifier : Specifier) (name : String)
    (table : Table) : Except Error Table :=
  let remaining := table.filter (fun declaration =>
    !replaces name specifier declaration)
  if priority = 0 then
    .ok remaining
  else do
    let checked <- checkedPriority priority
    pure ({ name, priority := checked, specifier } :: remaining)

def prefixes (table : Table) (name : String) : List Declaration :=
  table.filter (fun declaration =>
    declaration.name = name && declaration.specifier.isPrefix)

def postfixes (table : Table) (name : String) : List Declaration :=
  table.filter (fun declaration =>
    declaration.name = name && declaration.specifier.isPostfix)

def infixes (table : Table) (name : String) : List Declaration :=
  table.filter (fun declaration =>
    declaration.name = name && declaration.specifier.isInfix)

private def declaration (priority : Nat) (specifier : Specifier)
    (name : String) (positive : 0 < priority := by omega)
    (bounded : priority <= 1200 := by omega) : Declaration := {
  name
  priority := { value := priority, positive, bounded }
  specifier
}

/-- The pinned SWI operator inventory before source directives run.
`ReaderProfile.isoOperators` supplies the separate ISO inventory. -/
def defaults : Table := [
  declaration 1 .fx "$",
  declaration 100 .yfx ".",
  declaration 200 .fy "+",
  declaration 200 .fy "-",
  declaration 200 .fy "\\",
  declaration 200 .xfx "**",
  declaration 200 .xfy "^",
  declaration 400 .yfx "*",
  declaration 400 .yfx "/",
  declaration 400 .yfx "//",
  declaration 400 .yfx "<<",
  declaration 400 .yfx ">>",
  declaration 400 .yfx "div",
  declaration 400 .yfx "mod",
  declaration 400 .yfx "rdiv",
  declaration 400 .yfx "rem",
  declaration 400 .yfx "xor",
  declaration 500 .yfx "+",
  declaration 500 .yfx "-",
  declaration 500 .yfx "/\\",
  declaration 500 .yfx "\\/",
  declaration 600 .xfy ":",
  declaration 700 .xfx ":<",
  declaration 700 .xfx "<",
  declaration 700 .xfx "=",
  declaration 700 .xfx "=..",
  declaration 700 .xfx "=:=",
  declaration 700 .xfx "=<",
  declaration 700 .xfx "==",
  declaration 700 .xfx "=@=",
  declaration 700 .xfx "=\\=",
  declaration 700 .xfx ">",
  declaration 700 .xfx ">:<",
  declaration 700 .xfx ">=",
  declaration 700 .xfx "@<",
  declaration 700 .xfx "@=<",
  declaration 700 .xfx "@>",
  declaration 700 .xfx "@>=",
  declaration 700 .xfx "\\=",
  declaration 700 .xfx "\\==",
  declaration 700 .xfx "\\=@=",
  declaration 700 .xfx "as",
  declaration 700 .xfx "is",
  declaration 800 .xfx ":=",
  declaration 900 .fy "\\+",
  declaration 1000 .xfy ",",
  declaration 1050 .xfy "*->",
  declaration 1050 .xfy "->",
  declaration 1100 .xfy ";",
  declaration 1105 .xfy "|",
  declaration 1150 .fx "discontiguous",
  declaration 1150 .fx "dynamic",
  declaration 1150 .fx "initialization",
  declaration 1150 .fx "meta_predicate",
  declaration 1150 .fx "module_transparent",
  declaration 1150 .fx "multifile",
  declaration 1150 .fx "public",
  declaration 1150 .fx "table",
  declaration 1150 .fx "thread_initialization",
  declaration 1150 .fx "thread_local",
  declaration 1150 .fx "volatile",
  declaration 1200 .fx ":-",
  declaration 1200 .fx "?-",
  declaration 1200 .xfx "-->",
  declaration 1200 .xfx ":-",
  declaration 1200 .xfx "==>",
  declaration 1200 .xfx "=>"
]

end Mettapedia.Logic.Prolog.ReaderOperator
