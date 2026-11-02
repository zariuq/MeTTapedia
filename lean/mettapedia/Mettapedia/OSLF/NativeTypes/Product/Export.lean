import Mettapedia.GSLT.LanguageDef.ModuleSource.Printer
import Mettapedia.OSLF.MeTTaIL.CoreLanguageDef
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.LanguageEquality

/-!
# Languages as `.module` files

A language becomes a module with one theory: its sorts, constructors, equations and rewrites (`moduleOf`), printed
in the `.module` format (`moduleText`), which the format's reader reads back.

Rows are written as they are: anonymous binders as `^.p`, the substitution for an open body's bound variable as
`[a/#0]b`. A rule or equation may also declare its binding: the bound names each metavariable may use, and its
arguments at each occurrence. The core reduction computes such a declaration from binder names
(`CoreReduction.reduceRule`): a metavariable depends on the binders around its first occurrence on the left, and takes
their names as its arguments wherever it occurs. So a declared row is written with binder names whose reduction is its
declaration (`namedRow`), as the exchange of restrictions is written `ν x. ν y. P = ν y. ν x. P`:

    "PiNu"(^x0."PiNu"(^x1.P)) = "PiNu"(^x1."PiNu"(^x0.P))

and the reader's direct reading (`Product.directReading`) reduces the rows with named binders and keeps the others.
-/

namespace Mettapedia.OSLF.NativeTypes.Product

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.ModuleSource

/-! ## Declared rows as named rows -/

/-- The paths of the binders above a position in a pattern, innermost first. A position below a substitution's body,
whose bound variable has no name to write, or below a binder of several names, has none. -/
partial def bindersAbove (here : List Nat) : Pattern → List Nat → Option (List (List Nat))
  | _, [] => some []
  | .lambda _ body, 0 :: rest => (bindersAbove (here ++ [0]) body rest).map (· ++ [here])
  | .apply _ arguments, index :: rest => do
      let child ← arguments[index]?
      bindersAbove (here ++ [index]) child rest
  | .collection _ elements tail, index :: rest =>
      match elements[index]? with
      | some child => bindersAbove (here ++ [index]) child rest
      | none => if index = elements.length ∧ tail.isSome ∧ rest = [] then some [] else none
  | .subst _ replacement, 1 :: rest => bindersAbove (here ++ [1]) replacement rest
  | _, _ => none

/-- The binders at the given paths, named. -/
partial def nameBinders (names : List (List Nat × String)) (here : List Nat) : Pattern → Pattern
  | .lambda binder body =>
      .lambda (((names.find? (·.1 == here)).map (·.2)).orElse fun _ => binder) (nameBinders names (here ++ [0]) body)
  | .apply label arguments =>
      .apply label (arguments.zipIdx.map fun (argument, index) => nameBinders names (here ++ [index]) argument)
  | .collection kind elements tail =>
      .collection kind (elements.zipIdx.map fun (element, index) => nameBinders names (here ++ [index]) element) tail
  | .subst body replacement => .subst (nameBinders names (here ++ [0]) body) (nameBinders names (here ++ [1]) replacement)
  | .multiLambda arity binders body => .multiLambda arity binders (nameBinders names (here ++ [0]) body)
  | pattern => pattern

/-- The paths of a pattern's binders, in order. -/
partial def binderPaths (here : List Nat) : Pattern → List (List Nat)
  | .lambda _ body => here :: binderPaths (here ++ [0]) body
  | .apply _ arguments => (arguments.zipIdx.map fun (argument, index) => binderPaths (here ++ [index]) argument).flatten
  | .collection _ elements _ =>
      (elements.zipIdx.map fun (element, index) => binderPaths (here ++ [index]) element).flatten
  | .subst body replacement => binderPaths (here ++ [0]) body ++ binderPaths (here ++ [1]) replacement
  | .multiLambda _ _ body => binderPaths (here ++ [0]) body
  | _ => []

/-- A binder: its side and its path there. -/
abbrev BinderAt := RulePatternSite × List Nat

/-- **Binder names for a declaration**, when there are some whose reduction gives it back: the left's binders are
named in order; a metavariable's dependencies are the binders around its first occurrence on the left, all of them;
and wherever it occurs, the binder its argument points to takes the name of that dependency. A binder that no argument
points to keeps a name of its own. -/
def declaredNames (spec : RuleBindingSpec) (left right : Pattern) (taken : List String) :
    Option (List (List Nat × String) × List (List Nat × String)) := do
  let sideOf : RulePatternSite → Option Pattern
    | .left => some left
    | .right => some right
    | .premise .. => none
  let fresh (prefix_ : String) (count : Nat) : String := s!"{prefix_}{count}"
  -- each occurrence's binders, innermost first, and the indices its arguments point to
  let occurrences ← spec.occurrences.mapM fun occurrence => do
    let side ← sideOf occurrence.site
    let binders ← bindersAbove [] side occurrence.path
    let indices ← occurrence.arguments.mapM fun
      | .bvar index => some index
      | _ => none
    pure (occurrence, binders, indices)
  let leftNames : List (BinderAt × String) :=
    (binderPaths [] left).zipIdx.map fun (path, index) => ((.left, path), fresh "x" index)
  -- the dependencies of a metavariable: the binders around its first occurrence on the left, all of them
  let dependencies ← spec.dependencies.mapM fun (name, sorts) => do
    match occurrences.find? fun (occurrence, _, _) => occurrence.name == name && occurrence.site == .left with
    | some (_, binders, indices) =>
        guard (indices = List.range binders.length ∧ sorts.length = binders.length)
        pure (name, ← binders.mapM fun path => (leftNames.find? (·.1 == (.left, path))).map (·.2))
    | none => none
  -- the binders the arguments point to take their dependencies' names
  let mut assigned : List (BinderAt × String) := leftNames
  for (occurrence, binders, indices) in occurrences do
    let some (_, names) := dependencies.find? (·.1 == occurrence.name) | none
    guard (names.length = indices.length)
    for (dependency, index) in names.zip indices do
      let path ← binders[index]?
      match assigned.find? (·.1 == (occurrence.site, path)) with
      | some (_, existing) => guard (existing = dependency)
      | none => assigned := assigned ++ [((occurrence.site, path), dependency)]
  let rightNames := (binderPaths [] right).zipIdx.map fun (path, index) =>
    (path, ((assigned.find? (·.1 == (.right, path))).map (·.2)).getD (fresh "y" index))
  let chosen : List String := leftNames.map (·.2) ++ rightNames.map (·.2)
  guard (chosen.all fun name => !taken.contains name)
  pure (leftNames.map fun ((_, path), name) => (path, name), rightNames)

/-- The free names of a pattern. -/
partial def freeNames : Pattern → List String
  | .fvar name => [name]
  | .apply _ arguments => arguments.flatMap freeNames
  | .lambda _ body | .multiLambda _ _ body => freeNames body
  | .subst body replacement => freeNames body ++ freeNames replacement
  | .collection _ elements tail => elements.flatMap freeNames ++ tail.toList
  | .bvar _ => []

/-- **An equation with a declared binding, written with named binders** whose reduction is the equation, when there
are such names; the equation as it is otherwise. -/
def namedEquation (language : LanguageDef) (row : Equation) : Equation :=
  match row.bindings with
  | none => row
  | some spec =>
    let taken := freeNames row.left ++ freeNames row.right ++ row.typeContext.map (·.1)
    match declaredNames spec row.left row.right taken with
    | none => row
    | some (leftNames, rightNames) =>
      let named : Equation := ⟨row.name, row.typeContext, row.premises, nameBinders leftNames [] row.left,
        nameBinders rightNames [] row.right, none⟩
      match Mettapedia.OSLF.MeTTaIL.CoreReduction.reduceEquation
          (Mettapedia.OSLF.MeTTaIL.CoreReduction.canonicalGrammar language) named with
      | .ok reduced => if reduced = row then named else row
      | .error _ => row

/-- **A rewrite with a declared binding, written with named binders** whose reduction is the rewrite, when there are
such names; the rewrite as it is otherwise. -/
def namedRewrite (language : LanguageDef) (row : RewriteRule) : RewriteRule :=
  match row.bindings with
  | none => row
  | some spec =>
    let taken := freeNames row.left ++ freeNames row.right ++ row.typeContext.map (·.1)
    match declaredNames spec row.left row.right taken with
    | none => row
    | some (leftNames, rightNames) =>
      let named : RewriteRule := ⟨row.name, row.typeContext, row.premises, nameBinders leftNames [] row.left,
        nameBinders rightNames [] row.right, none⟩
      match Mettapedia.OSLF.MeTTaIL.CoreReduction.reduceRewrite
          (Mettapedia.OSLF.MeTTaIL.CoreReduction.canonicalGrammar language) named with
      | .ok reduced => if reduced = row then named else row
      | .error _ => row

/-! ## Modules -/

/-- **The bare constructors to declare bare**: those whose collection kind another constructor shares, which the
module's shared-carrier protection would otherwise wrap (`ModuleSource.retainSharedCollectionLabels`). -/
def declaredBareOf (language : LanguageDef) : List String :=
  ((language.terms.zip (retainSharedCollectionLabels language).terms).filter fun (written, protected_) =>
    written.collectionRepresentation == .bare && protected_.collectionRepresentation == .wrapped).map (·.1.label)

/-- The theory of a language: its sorts, constructors (those the protection would wrap declared bare), equations and
rewrites, declared rows with named binders. -/
def theoryOf (language : LanguageDef) : Theory where
  «name» := language.«name»
  params := []
  body := .extend none [.types language.«types», .terms language.«terms» (declaredBareOf language),
    .equations (language.equations.map (namedEquation language)),
    .rewrites (language.rewrites.map (namedRewrite language))]

/-- **A language as a module** with one theory, which the module elaborates to. -/
def moduleOf (language : LanguageDef) : Module where
  imports := []
  «name» := language.«name»
  theories := [theoryOf language]
  entry := some ([language.«name»], [])

/-- A language as `.module` text. -/
def moduleText (language : LanguageDef) : String := Printer.print (moduleOf language)

end Mettapedia.OSLF.NativeTypes.Product
