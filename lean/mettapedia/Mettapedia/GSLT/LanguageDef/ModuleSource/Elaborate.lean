import Mettapedia.GSLT.LanguageDef.ModuleSource.Syntax
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.Presentation
import Mettapedia.OSLF.MeTTaIL.Substitution
import Mettapedia.OSLF.MeTTaIL.CollectionLaws
import Mettapedia.GSLT.LanguageDef.WellSortedChecker

/-!
# Elaborating `.module` into `LanguageDef`

A theory value is an ordered fragment of `ModuleAlgebra.Presentation` entries. Each declaration
carries its origin: the instance that introduced it and its name there. Applying a theory makes
a fresh instance, so two applications are two independent structures, while one `let`-bound
value used twice is one structure. A join is `Presentation.orderedJoin?`: entries with one origin
are identified when they agree, and a join is refused exactly when one origin is declared two
ways or one label names two origins.

A name written `(One)` in an equation or a rewrite is the nullary constructor `One` when the
theory declares one at that point, its own or its base's; otherwise it is a variable. Names are
resolved where they are written, so a later replacement of `One` reaches them.

Equations are anonymous in the format: each instance's equations are its own declarations, so
an equation's label and name carry its instance.

`Replacements` replace a constructor and `Exports` may rename a sort; both keep the origin, so a
replaced constructor stays the same declaration for every later join. References follow: a
replaced constructor is rewritten in every equation and rewrite, with its arguments matched by
parameter name, and a binary operation replaced by a bag constructor of its sort collects its
arguments into the bag.

A replacement re-spells an operation and never adds laws: a binary operation becomes a bag only
when it commutes, and a set only when it is also idempotent (`checkFaithful`). The equations that
state a collection constructor's algebra, those of the operation it replaced or its own, become its
declaration, flattening with a unit when one holds (`declareAlgebras`).

Facts:
- `joinValues_isSome_iff`: a join succeeds exactly when the two fragments are compatible;
- `joinEntries_presentation`: a computed join is `Presentation.join`, a pushout over the shared
  entries; `evalExpr_join`: elaborating a join joins the elaborations;
- `joinEntries_self`: a fragment joined with itself is itself, so sharing never duplicates;
- `replace_origins`, `renameSort_origins`: replacing and renaming keep every origin;
- `fresh_lt`: every application gets an instance id larger than every earlier one.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.ModuleAlgebra (Entry)

instance : DecidableEq Equation := fun first second => by
  cases first
  cases second
  exact decidable_of_iff' _ (Iff.of_eq (Equation.mk.injEq _ _ _ _ _ _ _ _ _ _ _ _))

instance : DecidableEq RewriteRule := fun first second => by
  cases first
  cases second
  exact decidable_of_iff' _ (Iff.of_eq (RewriteRule.mk.injEq _ _ _ _ _ _ _ _ _ _ _ _))

/-! ## Builders, for the readers -/

def mkExport (sort : String) (renamed : Option String) : Export := ⟨sort, renamed⟩
def mkReplacement (old : String) (rule : GrammarRule) : Replacement := ⟨old, rule⟩
def mkParam (param : String) (target : Path) : Param := ⟨param, target⟩
def mkTheory (theoryName : String) (params : List Param) (body : Expr) : Theory := ⟨theoryName, params, body⟩
def mkImport (file qualifier : String) : Import := ⟨file, qualifier⟩
def mkModule (imports : List Import) (moduleName : String) (theories : List Theory)
    (entry : Option (Path × List Expr)) : Module := ⟨imports, moduleName, theories, entry⟩
abbrev ModuleData := Module

/-- The one rule of a single-row fragment. -/
def singleRule : List GrammarRule → GrammarRule
  | [rule] => rule
  | _ => { label := "", category := "", params := [], syntaxPattern := [] }

/-! ## Declarations and values -/

/-- The instance that introduced a declaration, and the declaration's name there. -/
structure Origin where
  inst : Nat
  name : String
  deriving DecidableEq, Repr

/-- Sorts, constructors, equations and rewrites have separate name spaces. -/
inductive Kind where
  | sort | term | equation | rewrite
  deriving DecidableEq, Repr

abbrev Label := Kind × String

inductive Decl where
  | sort (declaration : TypeDecl)
  | term (rule : GrammarRule)
  | equation (row : Equation)
  | rewrite (row : RewriteRule)
  deriving DecidableEq

abbrev Item := Entry Origin Label Decl

/-- A theory value: its declarations in order, its exported sorts, and the theories it is an
instance of. -/
structure Value where
  entries : List Item
  exports : List String := []
  instanceOf : List String := []
  /-- Origins that were introduced as binary operations and subsequently
  presented by a collection constructor. Variadic declarations do not acquire
  this authority merely by satisfying their binary associativity instance. -/
  binaryCollections : List Origin := []
  /-- The constructors declared bare (`![bare]`). -/
  declaredBare : List String := []

/-- Why a module does not elaborate. -/
inductive Error where
  | unknownName (name : String)
  | unknownTheory (path : Path)
  | arity (theory : String) (expected given : Nat)
  | notInstance (theory param : String) (expected : String)
  | collision (witness : Option (Item × Item))
  | replaceMissing (label : String)
  | replaceShape (old new : String)
  | replaceTyping (old new : String)
  | renameMissing (sort : String)
  | importMissing (file : String)
  | noEntry
  | replaceAddsLaws (old new law : String)
  | replaceCollectionBasis (old new : String)
  | requiresIndexedAdmission

instance : Repr Error where
  reprPrec
    | .unknownName name, _ => s!"unknown name {name}"
    | .unknownTheory path, _ => s!"unknown theory {".".intercalate path}"
    | .arity theory expected given, _ => s!"{theory} takes {expected} arguments, given {given}"
    | .notInstance theory param expected, _ => s!"{theory}: argument {param} is not an instance of {expected}"
    | .collision (some (left, right)), _ =>
        s!"join collision: {repr left.label} from instance {left.origin.inst} ({left.origin.name}) " ++
          s!"against {repr right.label} from instance {right.origin.inst} ({right.origin.name})"
    | .collision none, _ => "join collision"
    | .replaceMissing label, _ => s!"no constructor {label} to replace"
    | .replaceShape old new, _ => s!"cannot map the arguments of {old} onto {new}"
    | .replaceTyping old new, _ =>
        s!"replacing {old} by {new} changes its result sort or argument typing profile"
    | .renameMissing sort, _ => s!"no sort {sort} to export"
    | .importMissing file, _ => s!"import {file} is not available"
    | .noEntry, _ => "the module has no entry theory"
    | .replaceAddsLaws old new law, _ => s!"replacing {old} by {new} would add {law}, which {old} does not have"
    | .replaceCollectionBasis old new, _ =>
        s!"replacing {old} by {new} requires a binary associative operation and a declared unit"
    | .requiresIndexedAdmission, _ => "inductive declarations require the indexed admission route"

/-- Elaboration threads the next instance id. -/
abbrev M := StateT Nat (Except Error)

def fresh : M Nat := modifyGet fun next => (next, next + 1)

theorem fresh_lt (next : Nat) : ∀ result, fresh.run next = .ok result → result.1 = next ∧ result.2 = next + 1 := by
  intro result ran
  simp only [fresh, StateT.run, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure, Except.pure,
    Except.ok.injEq] at ran
  subst ran
  exact ⟨rfl, rfl⟩

/-! ## Joins -/

/-- The first incompatible pair, for the diagnostic. -/
def firstCollision (items : List Item) : Option (Item × Item) :=
  items.findSome? fun first =>
    (items.find? fun second => !ModuleAlgebra.entryCompatible first second).map (first, ·)

/-- Add entries to a fragment, refusing collisions. -/
def joinEntries (first second : List Item) : Except Error (List Item) :=
  match ModuleAlgebra.orderedJoin? first second with
  | some joined => .ok joined
  | none => .error (.collision (firstCollision (first ++ second)))

def joinValues (left right : Value) : Except Error Value := do
  let entries ← joinEntries left.entries right.entries
  pure { entries, exports := (left.exports ++ right.exports).eraseDups,
         instanceOf := (left.instanceOf ++ right.instanceOf).eraseDups,
         binaryCollections := (left.binaryCollections ++ right.binaryCollections).eraseDups,
         declaredBare := (left.declaredBare ++ right.declaredBare).eraseDups }

theorem joinEntries_isSome_iff (first second : List Item) :
    (∃ joined, joinEntries first second = .ok joined) ↔
      ModuleAlgebra.Valid (first.toFinset ∪ second.toFinset) := by
  rw [← ModuleAlgebra.orderedJoin_isSome_iff]
  unfold joinEntries
  cases joined : ModuleAlgebra.orderedJoin? first second with
  | some result => simp
  | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, iff_false, not_exists]
      intro result refused
      cases refused

/-- **A join succeeds exactly when the two fragments are compatible.** -/
theorem joinValues_isSome_iff (left right : Value) :
    (∃ joined, joinValues left right = .ok joined) ↔
      ModuleAlgebra.Valid (left.entries.toFinset ∪ right.entries.toFinset) := by
  rw [← joinEntries_isSome_iff]
  unfold joinValues
  cases joined : joinEntries left.entries right.entries with
  | ok entries => simp [bind, Except.bind, pure, Except.pure]
  | error failure => simp [bind, Except.bind]

/-- **A computed join is the presentation join**, whose square is a pushout over the shared
entries (`ModuleAlgebra.join_isPushout`). -/
theorem joinEntries_presentation (first second joined : List Item)
    (validFirst : ModuleAlgebra.Valid first.toFinset) (validSecond : ModuleAlgebra.Valid second.toFinset)
    (computed : joinEntries first second = .ok joined) :
    ∃ result, ModuleAlgebra.join ⟨first.toFinset, validFirst⟩ ⟨second.toFinset, validSecond⟩ = some result ∧
      result.val = joined.toFinset := by
  have ordered : ModuleAlgebra.orderedJoin? first second = some joined := by
    unfold joinEntries at computed
    cases found : ModuleAlgebra.orderedJoin? first second with
    | some result => rw [found] at computed; cases computed; rfl
    | none => rw [found] at computed; cases computed
  have agrees := ModuleAlgebra.orderedJoin_agrees first second
  rw [ordered, Option.bind_some] at agrees
  have union : joined.toFinset = first.toFinset ∪ second.toFinset := by
    simpa only [ModuleAlgebra.orderedJoin?, List.toFinset_append] using
      ModuleAlgebra.orderedCheck_toFinset (first ++ second) joined ordered
  have valid : ModuleAlgebra.Valid joined.toFinset := by
    have isSome := (ModuleAlgebra.orderedJoin_isSome_iff first second).mp (by simp [ordered])
    rwa [union]
  refine ⟨⟨joined.toFinset, valid⟩, ?_, rfl⟩
  show ModuleAlgebra.check (first.toFinset ∪ second.toFinset) = _
  rw [← union]
  simp [ModuleAlgebra.check, valid]

/-- Inserting an entry already present in a compatible fragment changes nothing. -/
theorem insert_member (kept : List Item) (accepted : List.AllCompatible ModuleAlgebra.entryCompatible kept)
    (entry : Item) (member : entry ∈ kept) :
    List.insertCompatible? ModuleAlgebra.entryCompatible entry kept = some kept := by
  induction kept with
  | nil => cases member
  | cons first rest ih =>
    by_cases same : entry = first
    · simp [List.insertCompatible?, same]
    · have inRest : entry ∈ rest := by
        rcases List.mem_cons.mp member with equal | inside
        · exact absurd equal same
        · exact inside
      have compatible : ModuleAlgebra.entryCompatible first entry = true :=
        accepted first (by simp) entry (by simp [inRest])
      have later := ih (accepted.mono (fun item inside => by simp [inside])) inRest
      simp [List.insertCompatible?, same, compatible, later]

/-- Adding entries that are all present changes nothing. -/
theorem union_members (kept : List Item) (accepted : List.AllCompatible ModuleAlgebra.entryCompatible kept) :
    ∀ incoming : List Item, (∀ entry ∈ incoming, entry ∈ kept) →
      List.unionCompatible? ModuleAlgebra.entryCompatible kept incoming = some kept
  | [], _ => rfl
  | entry :: rest, inside => by
    simp only [List.unionCompatible?, insert_member kept accepted entry (inside entry (by simp)),
      Option.bind_eq_bind, Option.bind_some]
    exact union_members kept accepted rest (fun other member => inside other (by simp [member]))

/-- A checked fragment is compatible. -/
theorem checked_allCompatible (items : List Item) (checked : ModuleAlgebra.orderedCheck? items = some items) :
    List.AllCompatible ModuleAlgebra.entryCompatible items :=
  List.unionCompatible?_allCompatible _ ModuleAlgebra.entryCompatible_self ModuleAlgebra.entryCompatible_symm
    [] items items (by simp) checked

/-- **Sharing never duplicates**: a checked fragment joined with itself is itself. -/
theorem joinEntries_self (items : List Item) (checked : ModuleAlgebra.orderedCheck? items = some items) :
    joinEntries items items = .ok items := by
  have joined : ModuleAlgebra.orderedJoin? items items = some items := by
    unfold ModuleAlgebra.orderedJoin? ModuleAlgebra.orderedCheck? at *
    rw [List.unionCompatible?_append, checked, Option.bind_some]
    exact union_members items (checked_allCompatible items checked) items (fun _ member => member)
  simp [joinEntries, joined]

/-! ## Renaming a sort -/

section Rename

variable (old new : String)

def renameName (name : String) : String := if name = old then new else name

def renameType : TypeExpr → TypeExpr
  | .base name => .base (renameName old new name)
  | .arrow domain codomain => .arrow (renameType domain) (renameType codomain)
  | .multiBinder body => .multiBinder (renameType body)
  | .collection kind element => .collection kind (renameType element)

def renameParam : TermParam → TermParam
  | .simple name type => .simple name (renameType old new type)
  | .abstractionNamed binder name type => .abstractionNamed binder name (renameType old new type)
  | .multiAbstractionNamed binders name type => .multiAbstractionNamed binders name (renameType old new type)

def renamePremise : Premise → Premise
  | .freshness condition => .freshness condition
  | .congruence source target => .congruence source target
  | .scopedStep step => .scopedStep { step with binders := step.binders.map (renameType old new),
                                                resultType := renameType old new step.resultType }
  | .relationQuery relation arguments => .relationQuery relation arguments
  | .forAll index element body => .forAll index element (renamePremise body)

def renameSpec (spec : RuleBindingSpec) : RuleBindingSpec :=
  { spec with dependencies := spec.dependencies.map fun entry => (entry.1, entry.2.map (renameType old new)) }

def renameContext (context : List (String × TypeExpr)) : List (String × TypeExpr) :=
  context.map fun entry => (entry.1, renameType old new entry.2)

def renameDecl : Decl → Decl
  | .sort declaration => .sort { declaration with name := renameName old new declaration.name }
  | .term rule => .term { rule with category := renameName old new rule.category,
                                    params := rule.params.map (renameParam old new) }
  | .equation row => .equation { row with typeContext := renameContext old new row.typeContext,
                                          premises := row.premises.map (renamePremise old new),
                                          bindings := row.bindings.map (renameSpec old new) }
  | .rewrite row => .rewrite { row with typeContext := renameContext old new row.typeContext,
                                        premises := row.premises.map (renamePremise old new),
                                        bindings := row.bindings.map (renameSpec old new) }

def renameItem (item : Item) : Item :=
  { item with label := if item.label = (.sort, old) then (.sort, new) else item.label,
              body := renameDecl old new item.body }

/-- **Renaming a sort keeps every origin.** -/
theorem renameSort_origins (items : List Item) :
    (items.map (renameItem old new)).map (·.origin) = items.map (·.origin) := by
  simp [renameItem, Function.comp_def]

end Rename

/-! ## Replacing a constructor -/

def paramName : TermParam → String
  | .simple name _ => name
  | .abstractionNamed _ name _ => name
  | .multiAbstractionNamed _ name _ => name

/-- Parameter names select an argument permutation; they grant no authority
to change the selected argument's type or binding representation. -/
def namedArguments? (old new : GrammarRule) : Bool :=
  let oldNames := old.params.map paramName
  let newNames := new.params.map paramName
  newNames.length = oldNames.length && newNames.all oldNames.contains && newNames.Nodup

/-- The declaration-derived parameter type and its required term form.
Binder display names do not alter either component. -/
def compatibleParameter? (old new : TermParam) : Bool :=
  let sameForm := match old, new with
    | .simple _ _, .simple _ _ => true
    | .abstractionNamed _ _ _, .abstractionNamed _ _ _ => true
    | .multiAbstractionNamed _ _ _, .multiAbstractionNamed _ _ _ => true
    | _, _ => false
  sameForm && (WellSorted.parameterType? old).isSome &&
    WellSorted.parameterType? old == WellSorted.parameterType? new

/-- Constructor replacement keeps its result sort. Named arguments keep
their types and binding forms; binary collection packing has a homogeneous
carrier. Sort renaming is the separate `Exports` operation. -/
def checkReplacementTyping (old new : GrammarRule) : Bool :=
  old.category == new.category &&
    if namedArguments? old new then
      WellSorted.usesBareCollection? old == WellSorted.usesBareCollection? new &&
        new.params.all fun parameter =>
          (old.params[(old.params.map paramName).idxOf (paramName parameter)]?).any
            (fun previous => compatibleParameter? previous parameter)
    else match new.params with
      | [.simple _ (.collection _ (.base element))] =>
          old.params.length == 2 && old.category == element &&
            old.params.all (fun parameter => match parameter with
              | .simple _ (.base sort) => sort == element
              | _ => false)
      | _ => false

/-- How the old constructor's arguments become the new one's: by parameter name, or, for a bag
constructor of the old parameters' sort, collected into the bag. -/
def argumentMap (old new : GrammarRule) : Option (List Pattern → List Pattern) :=
  let oldNames := old.params.map paramName
  let newNames := new.params.map paramName
  if namedArguments? old new then
    some fun arguments => newNames.map fun name => (arguments[oldNames.idxOf name]?).getD (.fvar name)
  else
    match new.params with
    | [.simple _ (.collection kind (.base element))] =>
        if old.params.all (fun param => match param with
            | .simple _ (.base sort) => sort = element
            | _ => false) then
          some fun arguments => [.collection kind arguments none]
        else none
    | _ => none

/-- `(op x y) == (op y x)`: the binary constructor `op` commutes. -/
def statesCommutative (op : String) (left right : Pattern) : Bool :=
  match left, right with
  | .apply first [.fvar x, .fvar y], .apply second [.fvar y', .fvar x'] =>
      first == op && second == op && x != y && x == x' && y == y'
  | _, _ => false

/-- `(op x x) == x`: the binary constructor `op` is idempotent. -/
def statesIdempotent (op : String) (left right : Pattern) : Bool :=
  match left, right with
  | .apply head [.fvar x, .fvar x'], .fvar x'' => head == op && x == x' && x == x''
  | _, _ => false

/-- Whether some premise-free equation of a value states `law` of `op`, either way round. -/
def holdsOf (value : Value) (law : String → Pattern → Pattern → Bool) (op : String) : Bool :=
  value.entries.any fun item => match item.body with
    | .equation row => row.premises.isEmpty && (law op row.left row.right || law op row.right row.left)
    | _ => false

/-- Binary associativity in the source operation, before collection lowering. -/
def statesBinaryAssociative (op : String) (left right : Pattern) : Bool :=
  match left, right with
  | .apply a [.apply b [.fvar x, .fvar y], .fvar z],
      .apply c [.fvar x', .apply d [.fvar y', .fvar z']] =>
      a == op && b == op && c == op && d == op &&
        x == x' && y == y' && z == z' && decide [x, y, z].Nodup
  | _, _ => false

/-- A named left or right unit of the source binary operation. -/
def binaryUnit (op : String) (left right : Pattern) : Option (String × Bool) :=
  match left, right with
  | .apply head [.fvar x, .apply unit []], .fvar x' =>
      if head == op && x == x' then some (unit, false) else none
  | .apply head [.apply unit [], .fvar x], .fvar x' =>
      if head == op && x == x' then some (unit, true) else none
  | _, _ => none

def binaryUnits (value : Value) (op : String) : List (String × Bool) :=
  value.entries.flatMap fun item => match item.body with
    | .equation row =>
        if row.premises.isEmpty then
          (binaryUnit op row.left row.right).toList ++
            (binaryUnit op row.right row.left).toList
        else []
    | _ => []

/-- An unrestricted finite collection needs an empty value as well as a
binary operation. A source semigroup alone cannot authorize that extension. -/
def binaryFoldReady (value : Value) (op : String) : Bool :=
  let units := binaryUnits value op
  holdsOf value statesBinaryAssociative op && units.any fun candidate =>
    units.any fun other => candidate.1 == other.1 && candidate.2 != other.2 ||
      holdsOf value statesCommutative op

/-- The parameter carrier, independently of whether its constructor label
is retained in the target representation. -/
def collectionParameterKind (rule : GrammarRule) : Option CollType :=
  match rule.params with
  | [.simple _ (.collection kind _)] => some kind
  | _ => none

/-- **A replacement re-spells an operation; it never adds laws.** A binary operation becomes a bag
constructor only when it commutes, and a set constructor only when it is also idempotent, because
those collections quotient out exactly that. -/
def checkFaithful (value : Value) (old : GrammarRule) (new : GrammarRule) : Except Error Unit := do
  match collectionParameterKind old,
      collectionParameterKind new with
  | some first, some second =>
      unless first == second do throw (.replaceShape old.label new.label)
  | _, _ => pure ()
  match new.params with
  | [.simple _ (.collection kind _)] =>
      if 2 ≤ old.params.length then
        if (kind == .hashBag || kind == .hashSet) && !holdsOf value statesCommutative old.label then
          .error (.replaceAddsLaws old.label new.label "commutativity")
        else if kind == .hashSet && !holdsOf value statesIdempotent old.label then
          .error (.replaceAddsLaws old.label new.label "idempotence")
        else .ok ()
      else .ok ()
  | _ => .ok ()
  if (collectionParameterKind new).isSome &&
      (collectionParameterKind old).isNone then
    unless old.params.length == 2 && binaryFoldReady value old.label do
      throw (.replaceCollectionBasis old.label new.label)

section Constructor

variable (old new : String) (map : List Pattern → List Pattern)

/-- Algebra units are constructor references. They follow the same symbol
action as term occurrences, while the declaration's other fields remain. -/
def renameUnitReferences (rule : GrammarRule) : GrammarRule :=
  { rule with algebra? := rule.algebra?.map (StructuralMorphism.mapCollectionAlgebra (renameName old new)) }

def renameConstructor : Pattern → Pattern
  | .bvar index => .bvar index
  | .fvar name => .fvar name
  | .apply label arguments =>
      let inner := arguments.map renameConstructor
      if label = old then .apply new (map inner) else .apply label inner
  | .lambda binder body => .lambda binder (renameConstructor body)
  | .multiLambda arity binders body => .multiLambda arity binders (renameConstructor body)
  | .subst body replacement => .subst (renameConstructor body) (renameConstructor replacement)
  | .collection kind elements rest => .collection kind (elements.map renameConstructor) rest
decreasing_by all_goals sizeOf_pattern_dec

def replacePremise : Premise → Premise
  | .freshness condition => .freshness { condition with term := renameConstructor old new map condition.term }
  | .congruence source target =>
      .congruence (renameConstructor old new map source) (renameConstructor old new map target)
  | .scopedStep step => .scopedStep { step with source := renameConstructor old new map step.source,
                                                target := renameConstructor old new map step.target }
  | .relationQuery relation arguments => .relationQuery relation (arguments.map (renameConstructor old new map))
  | .forAll index element body => .forAll index element (replacePremise body)

def replaceDecl : Decl → Decl
  | .term rule => .term (renameUnitReferences old new rule)
  | .equation row => .equation { row with premises := row.premises.map (replacePremise old new map),
                                          left := renameConstructor old new map row.left,
                                          right := renameConstructor old new map row.right }
  | .rewrite row => .rewrite { row with premises := row.premises.map (replacePremise old new map),
                                        left := renameConstructor old new map row.left,
                                        right := renameConstructor old new map row.right }
  | other => other

end Constructor

/-- The constructor `old` becomes `rule`, keeping its origin; every reference follows. -/
def replaceItems (items : List Item) (row : Replacement) (map : List Pattern → List Pattern) : List Item :=
  items.map fun item =>
    if item.label = (.term, row.old) then
      { item with
        label := (.term, row.rule.label)
        body := .term (renameUnitReferences row.old row.rule.label row.rule) }
    else { item with body := replaceDecl row.old row.rule.label map item.body }

/-- **Replacing a constructor keeps every origin.** -/
theorem replace_origins (items : List Item) (row : Replacement) (map : List Pattern → List Pattern) :
    (replaceItems items row map).map (·.origin) = items.map (·.origin) := by
  simp only [replaceItems, List.map_map]
  apply List.map_congr_left
  intro item _
  simp only [Function.comp_apply]
  split <;> rfl

/-! ## Blocks -/

/-- Re-admit a fragment after renaming or replacing. -/
def recheck (items : List Item) : Except Error (List Item) :=
  match ModuleAlgebra.orderedCheck? items with
  | some checked => .ok checked
  | none => .error (.collision (firstCollision items))

def newItem (inst : Nat) (kind : Kind) (name : String) (body : Decl) : Item := ⟨⟨inst, name⟩, (kind, name), body⟩

/-- An export row. A theory's exports are the sorts of the language it exports: a sort it has not declared is declared
by its export, as the module algebra's `Exports` builder declares the exported categories. Renaming on export needs
the sort to rename. -/
def exportRow (inst : Nat) (value : Value) (row : Export) : Except Error Value := do
  match row.renamed with
  | none =>
      if value.entries.any (·.label == (.sort, row.sort)) then
        pure { value with exports := value.exports ++ [row.sort] }
      else
        let entries ← joinEntries value.entries [newItem inst .sort row.sort (.sort (TypeDecl.plain row.sort))]
        pure { value with entries, exports := value.exports ++ [row.sort] }
  | some target =>
      unless value.entries.any (·.label == (.sort, row.sort)) do throw (.renameMissing row.sort)
      let entries ← recheck (value.entries.map (renameItem row.sort target))
      pure { value with entries, exports := value.exports.map (renameName row.sort target) ++ [target] }

def replaceRow (value : Value) (row : Replacement) : Except Error Value := do
  let some found := value.entries.find? (·.label == (.term, row.old)) | throw (.replaceMissing row.old)
  let .term oldRule := found.body | throw (.replaceMissing row.old)
  let some map := argumentMap oldRule row.rule | throw (.replaceShape row.old row.rule.label)
  unless checkReplacementTyping oldRule row.rule do throw (.replaceTyping row.old row.rule.label)
  checkFaithful value oldRule row.rule
  let entries ← recheck (replaceItems value.entries row map)
  let binaryCollections :=
    if oldRule.params.length == 2 &&
        (collectionParameterKind row.rule).isSome then
      found.origin :: value.binaryCollections
    else value.binaryCollections
  pure { value with entries, binaryCollections }

/-- The nullary constructors a value declares. -/
def nullaries (value : Value) : List String :=
  value.entries.filterMap fun item => match item.body with
    | .term rule => if rule.params.isEmpty then some rule.label else none
    | _ => none

def applyBlock (inst : Nat) (value : Value) : Block → Except Error Value
  | .types declarations =>
    add (declarations.map fun declaration => newItem inst .sort declaration.name (.sort declaration))
  | .terms rules bare => do
      let value ← add (rules.map fun rule => newItem inst .term rule.label (.term rule))
      pure { value with declaredBare := value.declaredBare ++ bare }
  | .equations rows => add (rows.map fun row =>
      let label := s!"{row.name}@{inst}"
      ⟨⟨inst, row.name⟩, (.equation, label), .equation (Equation.resolveNullary (nullaries value) { row with name := label })⟩)
  | .rewrites rows => add (rows.map fun row =>
      newItem inst .rewrite row.name (.rewrite (RewriteRule.resolveNullary (nullaries value) row)))
  | .exports rows => rows.foldlM (exportRow inst) value
  | .replacements rows => rows.foldlM replaceRow value
  | .inductives _ => .error .requiresIndexedAdmission
where
  add (fresh : List Item) : Except Error Value := do
    let entries ← joinEntries value.entries fresh
    pure { value with entries }

/-! ## Theories and modules -/

/-- A theory ready to apply: its canonical name, its parameters' theories, and its body. -/
structure Closure where
  name : String
  params : List (String × String)
  run : List Value → M Value

/-- What names mean while a theory body is elaborated. -/
structure Scope where
  theories : List (Path × Closure)
  values : List (String × Value) := []

def lookupTheory (scope : Scope) (path : Path) : Except Error Closure :=
  match scope.theories.find? (·.1 == path) with
  | some entry => .ok entry.2
  | none => .error (.unknownTheory path)

def liftExcept {α : Type} (result : Except Error α) : M α := StateT.lift result

mutual

def evalExpr (scope : Scope) (inst : Nat) : Expr → M Value
  | .ref name =>
      match scope.values.find? (·.1 == name) with
      | some entry => pure entry.2
      | none => throw (.unknownName name)
  | .apply path args => do
      let closure ← liftExcept (lookupTheory scope path)
      let values ← evalList scope inst args
      closure.run values
  | .join left right => do
      let first ← evalExpr scope inst left
      let second ← evalExpr scope inst right
      liftExcept (joinValues first second)
  | .extend base blocks => do
      let start ← match base with
        | some expr => evalExpr scope inst expr
        | none => pure { entries := [] }
      liftExcept (blocks.foldlM (applyBlock inst) start)
  | .letIn name value body => do
      let bound ← evalExpr scope inst value
      evalExpr { scope with values := (name, bound) :: scope.values } inst body

def evalList (scope : Scope) (inst : Nat) : List Expr → M (List Value)
  | [] => pure []
  | expr :: rest => do
      let head ← evalExpr scope inst expr
      let tail ← evalList scope inst rest
      pure (head :: tail)

end

/-- **Elaborating a join joins the elaborations**, in order, threading instance ids. -/
theorem evalExpr_join (scope : Scope) (inst : Nat) (left right : Expr) (next : Nat) :
    (evalExpr scope inst (.join left right)).run next =
      ((evalExpr scope inst left).run next).bind fun (first, afterLeft) =>
        ((evalExpr scope inst right).run afterLeft).bind fun (second, afterRight) =>
          (joinValues first second).map (·, afterRight) := by
  simp only [evalExpr, liftExcept, StateT.run, bind, StateT.bind, StateT.lift]
  cases (evalExpr scope inst left next) with
  | error failure => rfl
  | ok pair =>
    cases (evalExpr scope inst right pair.2) with
    | error failure => rfl
    | ok second =>
      simp only [Except.bind]
      cases (joinValues pair.1 second.1) <;> rfl

/-- The closure of a theory: applying it makes a fresh instance. -/
def closure (theories : List (Path × Closure)) (canonical : String) (theory : Theory) : Except Error Closure := do
  let params ← theory.params.mapM fun param => do
    let target ← lookupTheory { theories } param.theory
    pure (param.name, target.name)
  pure { name := canonical, params, run := fun args => do
    if args.length ≠ params.length then throw (.arity canonical params.length args.length)
    for (param, arg) in params.zip args do
      unless arg.instanceOf.contains param.2 do throw (.notInstance canonical param.1 param.2)
    let inst ← fresh
    let value ← evalExpr { theories, values := (params.map (·.1)).zip args } inst theory.body
    pure { value with instanceOf := (canonical :: value.instanceOf).eraseDups } }

/-- The theories a module defines, with those of its imports under their qualifiers. A module is
found in `library` by its file name; `fuel` bounds the import depth. -/
def theoriesOf (library : List (String × Module)) : Nat → Module → Except Error (List (Path × Closure))
  | 0, _ => .error (.importMissing "(import depth)")
  | fuel + 1, module => do
      let mut scope : List (Path × Closure) := []
      for imported in module.imports do
        let some dependency := library.find? (·.1 == imported.file) | throw (.importMissing imported.file)
        let theirs ← theoriesOf library fuel dependency.2
        scope := scope ++ (theirs.filter (·.1.length == 1)).map fun entry => (imported.qualifier :: entry.1, entry.2)
      for theory in module.theories do
        let made ← closure scope (module.name ++ "." ++ theory.name) theory
        scope := scope ++ [([theory.name], made)]
      pure scope

/-! ## Collection algebras

A constructor whose single parameter is a collection of its own sort carries its algebra as a
declaration (`GrammarRule.algebra?`): flattening, with the singleton law, and optionally a unit. A
module states that algebra as equations, those of the operation a bag replaced or those written for
the collection constructor itself. Those equations become the declaration and leave the equations;
an unordered collection's own laws already permute its elements. -/

/-- The elements of a collection written as the argument of the constructor `label`. -/
def elementsUnder (label : String) : Pattern → Option (List Pattern)
  | .apply head [.collection _ elements none] => if head == label then some elements else none
  | _ => none

/-- The names of a list of variables. -/
def variableNames : List Pattern → Option (List String)
  | [] => some []
  | .fvar name :: rest => (variableNames rest).map (name :: ·)
  | _ => none

/-- `{{x, y}, z}`, `{x, {y, z}}` or `{x, y, z}` under `label`, as the names `[x, y, z]` and which
of the three it is. -/
def threeShape (label : String) (pattern : Pattern) : Option (Nat × List String) :=
  match elementsUnder label pattern with
  | some [inner, .fvar z] =>
      match (elementsUnder label inner).bind variableNames with
      | some [x, y] => some (0, [x, y, z])
      | _ => none
  | some [.fvar x, inner] =>
      match (elementsUnder label inner).bind variableNames with
      | some [y, z] => some (1, [x, y, z])
      | _ => none
  | some elements =>
      match variableNames elements with
      | some [x, y, z] => some (2, [x, y, z])
      | _ => none
  | none => none

/-- Two different shapes of three distinct variables in one order: associativity, or flattening. -/
def statesFlatten (label : String) (left right : Pattern) : Bool :=
  match threeShape label left, threeShape label right with
  | some (first, names), some (second, names') => first != second && names == names' && names.Nodup
  | _, _ => false

/-- `{x, u} == x` (`some (u, false)`) or `{u, x} == x` (`some (u, true)`) under `label`. -/
def statesUnit (label : String) (left right : Pattern) : Option (String × Bool) :=
  match elementsUnder label left, right with
  | some [.fvar x, .apply unit []], .fvar x' => if x == x' then some (unit, false) else none
  | some [.apply unit [], .fvar x], .fvar x' => if x == x' then some (unit, true) else none
  | _, _ => none

/-- `{x} == x` under `label`. -/
def statesSingleton (label : String) (left right : Pattern) : Bool :=
  match elementsUnder label left, right with
  | some [.fvar x], .fvar x' => x == x'
  | _, _ => false

/-- `{x, y} == {y, x}` under `label`. -/
def statesCommuting (label : String) (left right : Pattern) : Bool :=
  match elementsUnder label left, elementsUnder label right with
  | some [.fvar x, .fvar y], some [.fvar y', .fvar x'] => x != y && x == x' && y == y'
  | _, _ => false

/-- A law either way round. -/
def eitherWay (law : Pattern → Pattern → Bool) (row : Equation) : Bool :=
  law row.left row.right || law row.right row.left

/-- The units an equation states, either way round. -/
def unitsOf (label : String) (row : Equation) : List (String × Bool) :=
  (statesUnit label row.left row.right).toList ++ (statesUnit label row.right row.left).toList

/-- The kind of a bare collection constructor of its own sort. -/
def ownKind (rule : GrammarRule) : Option CollType :=
  match rule.bareParams with
  | [.simple _ (.collection kind (.base element))] => if element == rule.category then some kind else none
  | _ => none

/-- A candidate fold algebra read from the translated binary equations.
This recognizer alone does not authorize interpreting an arbitrary variadic
constructor as a fold: extraction also requires its binary source origin.
Unit and singleton equations remain explicit because the standard collection
normalizer does not itself remove their outer wrappers. -/
def statedAlgebra (equations : List Equation) (rule : GrammarRule) : Option (CollectionAlgebra × (Equation → Bool)) := do
  let kind ← ownKind rule
  let free := equations.filter (·.premises.isEmpty)
  guard (free.any (eitherWay (statesFlatten rule.label)))
  let unordered := kind == .hashBag || kind == .hashSet
  let stated := free.flatMap (unitsOf rule.label)
  let unit? : Option String :=
    match stated.head? with
    | some (unit, _) =>
        if stated.all (·.1 == unit) && (unordered || (stated.any (·.2) && stated.any (!·.2))) then some unit
        else none
    | none => none
  let replaced (row : Equation) : Bool :=
    row.premises.isEmpty &&
      (eitherWay (statesFlatten rule.label) row ||
        (unordered && eitherWay (statesCommuting rule.label) row))
  return (⟨true, unit?⟩, replaced)

/-- The normalizer selects collection laws by kind only when the language
has one constructor of that kind. Extraction must use the same boundary:
otherwise deleting a source equation would leave no law implementing it. -/
def uniqueCollectionKind (language : LanguageDef) (rule : GrammarRule) : Bool :=
  match Mettapedia.OSLF.MeTTaIL.CollectionLaws.bareKind rule with
  | none => false
  | some kind =>
      (language.terms.filter fun other =>
        Mettapedia.OSLF.MeTTaIL.CollectionLaws.bareKind other == some kind).length == 1

/-- An inferred collection algebra requires a binary replacement origin,
a unit for the empty fold, and one constructor of its kind. Other source
equations remain explicit. Existing algebra declarations are retained. -/
def extractAlgebra (language : LanguageDef) (binaryLabels : List String)
    (current : LanguageDef) (rule : GrammarRule) : LanguageDef :=
    if rule.algebra?.isSome || !uniqueCollectionKind language rule ||
        !binaryLabels.contains rule.label then current
    else match statedAlgebra current.equations rule with
      | some (algebra, replaced) =>
          if algebra.unit.isSome then
            { current with
              terms := current.terms.map fun other =>
                if other.label == rule.label then { other with algebra? := some algebra } else other
              equations := current.equations.filter (!replaced ·) }
          else current
      | none => current

def declareAlgebras (language : LanguageDef) (binaryLabels : List String := []) : LanguageDef :=
  language.terms.foldl (extractAlgebra language binaryLabels) language

/-- A value's declarations in order, before nullary names are resolved. -/
def flattenRaw (name : String) (value : Value) : LanguageDef where
  name := name
  types := value.entries.filterMap fun item => match item.body with
    | .sort declaration => some declaration | _ => none
  terms := value.entries.filterMap fun item => match item.body with
    | .term rule => some rule | _ => none
  equations := value.entries.filterMap fun item => match item.body with
    | .equation row => some row | _ => none
  rewrites := value.entries.filterMap fun item => match item.body with
    | .rewrite row => some row | _ => none

/-- New representation protection applies to pending extraction from an
actual binary source origin. Existing algebra metadata retains its current
representation until a representation-aware law certificate is supplied. -/
def collectionAlgebraCandidate (rule : GrammarRule) (binaryLabels : List String) : Bool :=
  binaryLabels.contains rule.label && rule.algebra?.isNone

/-- A collection kind used in another constructor parameter also has a data
role. The recursive type traversal includes nested collections and binder
and arrow slots, independently of the other constructor's arity. -/
def otherCollectionParameter (language : LanguageDef) (rule : GrammarRule)
    (kind : CollType) : Bool :=
  language.terms.any fun other =>
    other.label != rule.label &&
      other.params.any (fun parameter => parameter.typeExpr.mentionsCollection kind)

/-- Sharing a carrier does not identify declared operations or turn data
collections into algebra occurrences. Retain a pending binary algebra's label when another constructor exposes that
carrier as data. Existing declared profiles retain the prior shared-operation
protection. The equations of pending extraction remain
available to the ordinary equation machinery. This finite guard does not
certify reflection for arbitrary root values or free-variable types. -/
def retainSharedCollectionLabels (language : LanguageDef) (binaryLabels : List String := []) : LanguageDef :=
  { language with terms := language.terms.map fun rule =>
      match collectionParameterKind rule with
      | none => rule
      | some kind =>
          if language.terms.any (fun other =>
              other.label != rule.label && collectionParameterKind other == some kind) ||
              (collectionAlgebraCandidate rule binaryLabels &&
                otherCollectionParameter language rule kind) then
            { rule with collectionRepresentation := .wrapped }
          else rule }

/-- The replaced binary origins represented by collection declarations. -/
def binaryCollectionLabels (value : Value) : List String :=
  value.entries.filterMap fun item =>
    if value.binaryCollections.contains item.origin then
      match item.body with
      | .term rule => some rule.label
      | _ => none
    else none

/-- The categories of labelled BNF whose terms are tokens. -/
def tokenCategories : List String := ["Ident", "Integer", "Double", "String", "Char"]

/-- The base sorts a type mentions. -/
def baseSorts : TypeExpr → List String
  | .base name => [name]
  | .arrow domain codomain => baseSorts domain ++ baseSorts codomain
  | .multiBinder body => baseSorts body
  | .collection _ element => baseSorts element

/-- **The sorts a language's constructors use and nothing declares**, in order of first use: each constructor's
category, then the sorts of its parameters. They are declared as the runtime's module reader declares them: with the
abstract syntax, and the token categories of labelled BNF with raw token carriers. -/
def implicitSorts (language : LanguageDef) : List TypeDecl :=
  let used := language.terms.flatMap fun rule => rule.category :: rule.params.flatMap (baseSorts ·.typeExpr)
  (used.eraseDups.filter fun sort => !language.types.any (·.name == sort)).map fun sort =>
    ⟨sort, if tokenCategories.contains sort then .tokenRaw else .ast⟩

/-- **Declared representations are kept**: a constructor declared bare (`![bare]`) keeps its bare collections, where
the shared-carrier protection would keep its label. The protection is for constructors whose representation a module
does not state. -/
def keepDeclaredBare (declared : List String) (language : LanguageDef) : LanguageDef :=
  { language with terms := language.terms.map fun rule =>
      if declared.contains rule.label then { rule with collectionRepresentation := .bare } else rule }

/-- A value as a `LanguageDef`, its declarations in order, with collection
algebras declared only after carrier representations have been protected, and the sorts its constructors use and
nothing declares declared after the declared ones. -/
def flatten (name : String) (value : Value) : LanguageDef :=
  let binaryLabels := binaryCollectionLabels value
  let language := declareAlgebras
    (keepDeclaredBare value.declaredBare (retainSharedCollectionLabels (flattenRaw name value) binaryLabels))
    binaryLabels
  { language with «types» := language.types ++ implicitSorts language }

/-- The value of applying a theory to arguments, within a module. -/
def applyTheory (library : List (String × Module)) (module : Module) (path : Path) (args : List Expr) :
    Except Error (String × Value) := do
  let theories ← theoriesOf library (library.length + 1) module
  let made ← lookupTheory { theories } path
  let value ← (evalExpr { theories } 0 (.apply path args)).run' 0
  pure (made.name, value)

/-- **A module's `LanguageDef`**: its entry theory, elaborated. -/
def elaborate (library : List (String × Module)) (module : Module) : Except Error LanguageDef := do
  let some (path, args) := module.entry | throw .noEntry
  let (name, value) ← applyTheory library module path args
  pure (flatten name value)

/-- **The language of one theory of a module**, applied to no arguments: how a module that declares theories and no
entry is read, as CeTTa's core modules are. -/
def elaborateTheory (library : List (String × Module)) (module : Module) (path : Path) : Except Error LanguageDef := do
  let (name, value) ← applyTheory library module path []
  pure (flatten name value)

/-! ## Authored names

An elaborated language names itself by its theory's canonical name, `Module.Theory`, and each equation by its label,
which carries the instance that introduced it (`Assoc@2`): a join of two instances of one theory keeps their
equations apart by it. A module that writes one language reads back under the names it was written with: the entry's
name as the module writes it, and each equation under its own name. -/

/-- A value with each equation under the name it was written with. -/
def authoredNames (value : Value) : Value :=
  { value with entries := value.entries.map fun item =>
      match item.body with
      | .equation row => { item with body := .equation { row with name := item.origin.name } }
      | _ => item }

/-- **A module's `LanguageDef` under its authored names**: `elaborate`, named as the module writes it. -/
def elaborateAuthored (library : List (String × Module)) (module : Module) : Except Error LanguageDef := do
  let some (path, args) := module.entry | throw .noEntry
  let (_, value) ← applyTheory library module path args
  pure (flatten (path.foldl (fun name part => if name.isEmpty then part else name ++ "." ++ part) "")
    (authoredNames value))

/-- **The language of one theory of a module under its authored names**: `elaborateTheory`, named as written. -/
def elaborateTheoryAuthored (library : List (String × Module)) (module : Module) (path : Path) :
    Except Error LanguageDef := do
  let (_, value) ← applyTheory library module path []
  pure (flatten (path.foldl (fun name part => if name.isEmpty then part else name ++ "." ++ part) "")
    (authoredNames value))

end Mettapedia.GSLT.LanguageDef.ModuleSource
