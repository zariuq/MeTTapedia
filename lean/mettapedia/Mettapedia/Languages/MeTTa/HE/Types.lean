import Mettapedia.Languages.MeTTa.OSLFCore.Bindings
import Mettapedia.Machines.ReadOnlyQuery
import Mathlib.Data.Finset.Card
import Mettapedia.Languages.MeTTa.SubstitutionAlgebra
import Mettapedia.Algorithms.WellFoundedServices.DependencyAnalysis

/-!
# HE MeTTa Types

Foundation types for the Hyperon Experimental MeTTa interpreter formalization.

## Source Precedence
1. `hyperon-experimental/lib/src/metta/interpreter.rs` (ground truth)
2. `hyperon-experimental/docs/metta.md` (spec prose)

## Main Definitions
* `ErrorCode` - Structured error codes from the HE spec
* `Bindings` - Variable bindings with assignments AND equalities
* `ResultPair` / `ResultSet` - Interpreter output types
* `ResultEqBag` / `ResultEqOrdered` - Result equivalence relations
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## Error Codes

The published specification describes these structured diagnostic shapes.
Malformed minimal instructions can also return message symbols containing
rendered source syntax. Although message wording is not fixed by this code
catalogue, a program can inspect those symbols with `case` or equality.
Comparison theorems must therefore state their diagnostic policy and observer;
ignoring message text alone does not establish contextual equivalence. -/

/-- Structured error codes from the HE interpreter.
    Ref: `metta.md` lines 125-148, `interpreter.rs` error branches. -/
inductive ErrorCode where
  | stackOverflow
  | noReturn
  | incorrectNumberOfArguments
  | badArgType (pos : Nat) (expected actual : Atom)
  | badType (expected actual : Atom)
  deriving Repr, DecidableEq, Inhabited

/-- Convert an error code to its atom representation.
    Ref: `metta.md` line 253 `(Error $atom ...)` shape. -/
def ErrorCode.toAtom : ErrorCode → Atom
  | .stackOverflow => .symbol "StackOverflow"
  | .noReturn => .symbol "NoReturn"
  | .incorrectNumberOfArguments => .symbol "IncorrectNumberOfArguments"
  | .badArgType pos expected actual =>
    .expression [.symbol "BadArgType", .grounded (.int pos), expected, actual]
  | .badType expected actual =>
    .expression [.symbol "BadType", expected, actual]

/-- Construct an `(Error source errorCode)` atom.
    Ref: `metta.md` line 253. -/
def mkError (source : Atom) (code : ErrorCode) : Atom :=
  Atom.error source code.toAtom

/-- Construct an `(Error source message)` atom with a textual message payload.
    Hyperon Experimental uses this interface for malformed minimal-instruction
    parser errors such as bad-arity `unify`. -/
def mkErrorMessage (source : Atom) (message : String) : Atom :=
  Atom.error source (.symbol message)

/-- Reference malformed-`unify` message from hyperon-experimental's
    minimal-instruction parser. -/
def unifyBadArityMessage : Atom → String
  | .expression [.symbol "unify", .symbol a, .symbol p, .symbol t] =>
      "expected: (unify <atom> <pattern> <then> <else>), found: " ++
        "(unify " ++ a ++ " " ++ p ++ " " ++ t ++ ")"
  | source =>
      "expected: (unify <atom> <pattern> <then> <else>), found: " ++
        toString source

/-- Reference HE error for malformed primitive `unify` interfaces. -/
def mkUnifyBadArityError (source : Atom) : Atom :=
  mkErrorMessage source (unifyBadArityMessage source)

/-! ## Bindings

The HE spec (metta.md lines 562-576) defines bindings as a set of two kinds
of relations:
1. Assignment: `$x <- value`
2. Equality: `$a = $b`

We use sorted lists for canonical representation and `DecidableEq`. -/

/-- Variable bindings for HE MeTTa.

    `assignments` maps variable names to values (`$x <- val`).
    `equalities` records variable-variable equalities (`$a = $b`).

    Invariant: no duplicate variable names in assignments (maintained by operations).
    Ref: metta.md lines 562-576. -/
structure Bindings where
  assignments : List (String × Atom)
  equalities : List (String × String)
  deriving Repr, Inhabited, DecidableEq

namespace Bindings

/-- Empty bindings. -/
def empty : Bindings := ⟨[], []⟩

instance : EmptyCollection Bindings := ⟨empty⟩

/-- Look up a variable's assigned value. -/
def lookup (b : Bindings) (v : String) : Option Atom :=
  b.assignments.lookup v

/-- Check if a variable has an assignment. -/
def isBound (b : Bindings) (v : String) : Bool :=
  (b.lookup v).isSome

/-- Structural depth sufficient for total variable scans. -/
def atomScanFuel : Atom → Nat
  | .expression es => atomListScanFuel es + 1
  | _ => 1
where
  atomListScanFuel : List Atom → Nat
    | [] => 0
    | a :: as => max (atomScanFuel a) (atomListScanFuel as)

/-- Fuelled scan for a variable with a direct assignment in `b`. -/
def hasAssignedVarAux (b : Bindings) : Nat → Atom → Bool
  | 0, _ => false
  | Nat.succ _, .var v => b.isBound v
  | n + 1, .expression es => es.any (b.hasAssignedVarAux n)
  | Nat.succ _, _ => false

/-- Whether an atom contains a variable with a direct assignment in `b`. -/
def hasAssignedVar (b : Bindings) (a : Atom) : Bool :=
  b.hasAssignedVarAux (atomScanFuel a) a

private theorem hasAssignedVar_var_of_lookup_some {b : Bindings}
    {v : String} {a : Atom} (h : b.lookup v = some a) :
    b.hasAssignedVar (.var v) = true := by
  simp [hasAssignedVar, atomScanFuel, hasAssignedVarAux, isBound, h]

/-- Add or update a variable assignment. Replaces existing if present. -/
def assign (b : Bindings) (v : String) (val : Atom) : Bindings :=
  let assignments' := if b.isBound v then
    b.assignments.map fun (k, a) => if k == v then (k, val) else (k, a)
  else
    b.assignments ++ [(v, val)]
  { b with assignments := assignments' }

/-- Add a variable equality. -/
def addEquality (b : Bindings) (a c : String) : Bindings :=
  { b with equalities := b.equalities ++ [(a, c)] }

/-- Remove a variable assignment. -/
def removeAssignment (b : Bindings) (v : String) : Bindings :=
  { b with assignments := b.assignments.filter fun (k, _) => k != v }

/-- Recursively resolve an atom through assignments. Unknown variables remain
    variables inside compound values; revisiting a variable reports a cycle. -/
def resolveAtomAux (b : Bindings) : Nat → List String → Atom → Option Atom
  | 0, _, _ => none
  | n + 1, visited, atom =>
    match atom with
    | .var v =>
      if visited.contains v then none
      else
        match b.lookup v with
        | none => some (.var v)
        | some value =>
          if b.hasAssignedVar value then b.resolveAtomAux n (v :: visited) value
          else some value
    | .expression es =>
      match es.mapM (b.resolveAtomAux n visited) with
      | some resolved => some (.expression resolved)
      | none => none
    | other => some other

/-- Resolve a variable to its recursively instantiated assignment. `none`
    means the variable is unbound, fuel was exhausted, or a cycle was found. -/
def resolve (b : Bindings) (v : String) (fuel : Nat) : Option Atom :=
  match b.lookup v with
  | none => none
  | some _ => b.resolveAtomAux fuel [] (.var v)

/-- Get all variable names that are bound (have assignments). -/
def boundVars (b : Bindings) : List String :=
  b.assignments.map Prod.fst

/-- Maximum syntax depth of an assignment value. -/
def resolutionValueDepth (b : Bindings) : Nat :=
  b.assignments.foldr (fun entry bound => max (atomScanFuel entry.2) bound) 0

/-- Sufficient depth for binding application, including compound values and
class-aware resolution. Each assignment dependency marks a fresh finite key. -/
def resolutionFuel (b : Bindings) (atom : Atom) : Nat :=
  b.boundVars.toFinset.card * (b.resolutionValueDepth + 1) + atomScanFuel atom + 3

/-- Resolve a variable using the proved structural depth. -/
def resolveDefault (b : Bindings) (v : String) : Option Atom :=
  b.resolve v (b.resolutionFuel (.var v))

/-- Apply bindings to an atom, substituting variables with their values.
    Uses explicit fuel in the trusted path. -/
def apply (b : Bindings) (a : Atom) (fuel : Nat) : Atom :=
  match fuel with
  | 0 => a
  | n + 1 =>
    match a with
    | .var v =>
      match b.resolve v n with
      | some val => val
      | none => a
    | .expression es => .expression (es.map (b.apply · n))
    | other => other

/-- Apply bindings using the proved structural depth. -/
def applyDefault (b : Bindings) (a : Atom) : Atom :=
  b.apply a (b.resolutionFuel a)

/-! ### Equality-aware resolution (G3b)

The English spec treats a binding set as ORDER-FREE relations where `$x = $y`
means the variables have equal-or-matchable values (metta.md line 393), and
extracts query answers as "the value of the `$X` variable" from the full
binding set.  Upstream (`hyperon-atom/src/matcher.rs`, `resolve_internal`)
resolves a variable through its binding GROUP: a group carrying no value
resolves to the group's representative variable.  `resolve`/`apply` above
consult assignments only — the functions below add the equality-class layer.
On equality-free bindings they agree with `resolve`/`apply`
(`resolveFull_no_equalities`, `applyFull_no_equalities`). -/

/-- One saturation pass of the symmetric equality closure: extend `acc` by
    every variable one equality hop away from a member. -/
def eqStep (eqs : List (String × String)) (acc : List String) : List String :=
  eqs.foldl (fun acc p =>
    let acc := if acc.contains p.1 && !acc.contains p.2 then acc ++ [p.2] else acc
    if acc.contains p.2 && !acc.contains p.1 then acc ++ [p.1] else acc) acc

/-- Iterated saturation for the equality closure. -/
def eqClassAux (eqs : List (String × String)) : Nat → List String → List String
  | 0, acc => acc
  | n + 1, acc => eqClassAux eqs n (eqStep eqs acc)

/-- Equality class of `v`: the symmetric-transitive closure of `equalities`
    reachable from `v` (always contains `v`).  `2·|equalities| + 1` passes
    saturate, since each productive pass adds a member and a class has at most
    `2·|equalities| + 1` members. -/
def eqClass (b : Bindings) (v : String) : List String :=
  eqClassAux b.equalities (2 * b.equalities.length + 1) [v]

/-- Every variable occurring in `equalities`, in first-appearance order.  This
    is the insertion order upstream uses to pick a binding group's
    representative (match orientation inserts the query-side variable first). -/
def eqVarsInOrder (b : Bindings) : List String :=
  b.equalities.foldl (fun acc p =>
    let acc := if acc.contains p.1 then acc else acc ++ [p.1]
    if acc.contains p.2 then acc else acc ++ [p.2]) []

/-- Members of `v`'s equality class in insertion order (`[v]` when the class is
    trivial).  Canonical: any two members of one class get the same list. -/
def eqClassOrdered (b : Bindings) (v : String) : List String :=
  match (b.eqVarsInOrder).filter (fun w => (b.eqClass v).contains w) with
  | [] => [v]
  | ordered => ordered

/-- Direct values carried by members of `v`'s whole equality class, in the
    stable representative order used by `resolveFull`. -/
def classValues (b : Bindings) (v : String) : List Atom :=
  (b.eqClassOrdered v).filterMap b.lookup

/-- Whether a nonempty list of class values is structurally constant. Empty
    and singleton lists are consistent by construction. Unequal but unifiable
    values are reconciled by the matcher rather than accepted here. -/
def valuesConsistent : List Atom → Bool
  | [] => true
  | first :: rest => rest.all (fun value => value == first)

/-- Upstream-style class representative: the earliest-inserted member of `v`'s
    equality class (`v` itself when the class is trivial). -/
def eqRepresentative (b : Bindings) (v : String) : String :=
  (b.eqClassOrdered v).headD v

/-- Fuelled scan for a variable whose equality class has a value or a
    nontrivial representative. -/
def hasResolvableVarAux (b : Bindings) : Nat → Atom → Bool
  | 0, _ => false
  | Nat.succ _, .var v => if b.eqClassOrdered v = [v] then b.isBound v else true
  | n + 1, .expression es => es.any (b.hasResolvableVarAux n)
  | Nat.succ _, _ => false

/-- Whether an atom contains a variable whose equality class has a value or a
    nontrivial representative. -/
def hasResolvableVar (b : Bindings) (a : Atom) : Bool :=
  b.hasResolvableVarAux (atomScanFuel a) a

/-- Recursively resolve an atom through equality classes and class values.
    Unknown variables remain variables inside compound values. Visiting any
    member of a class already on the dependency path reports a cycle. -/
def resolveAtomFullAux (b : Bindings) : Nat → List String → Atom → Option Atom
  | 0, _, _ => none
  | n + 1, visited, atom =>
    match atom with
    | .var v =>
      let cls := b.eqClassOrdered v
      if cls.any visited.contains then none
      else
        match cls.findSome? b.lookup with
        | none =>
          if cls = [v] then some (.var v)
          else some (.var (b.eqRepresentative v))
        | some (.var w) =>
          if cls.contains w then
            if cls.length = 1 then none
            else some (.var (b.eqRepresentative v))
          else if b.hasResolvableVar (.var w) then
            b.resolveAtomFullAux n (cls ++ visited) (.var w)
          else some (.var w)
        | some value =>
          if b.hasResolvableVar value then
            b.resolveAtomFullAux n (cls ++ visited) value
          else some value
    | .expression es =>
      match es.mapM (b.resolveAtomFullAux n visited) with
      | some resolved => some (.expression resolved)
      | none => none
    | other => some other

/-- Equality-aware resolution: value lookup consults `v`'s whole equality
    class, recursively resolves compound values, and sends a valueless
    nontrivial class to its representative variable. -/
def resolveFull (b : Bindings) (v : String) (fuel : Nat) : Option Atom :=
  let cls := b.eqClassOrdered v
  if cls = [v] && (cls.findSome? b.lookup).isNone then none
  else b.resolveAtomFullAux fuel [] (.var v)

/-- Equality-aware `apply`: substitutes via `resolveFull`. -/
def applyFull (b : Bindings) (a : Atom) (fuel : Nat) : Atom :=
  match fuel with
  | 0 => a
  | n + 1 =>
    match a with
    | .var v =>
      match b.resolveFull v n with
      | some val => val
      | none => a
    | .expression es => .expression (es.map (b.applyFull · n))
    | other => other

/-- Equality-free bindings have trivial classes. -/
theorem eqClassOrdered_no_equalities {b : Bindings} (h : b.equalities = [])
    (v : String) : b.eqClassOrdered v = [v] := by
  simp [eqClassOrdered, eqVarsInOrder, h]

/-- Equality-free class-value lookup is exactly direct assignment lookup. -/
theorem classValues_no_equalities {b : Bindings} (h : b.equalities = [])
    (v : String) : b.classValues v = (b.lookup v).toList := by
  rw [classValues, eqClassOrdered_no_equalities h]
  cases hlookup : b.lookup v <;> simp [hlookup]

private theorem hasResolvableVar_no_equalities {b : Bindings}
    (h : b.equalities = []) :
    ∀ a : Atom, b.hasResolvableVar a = b.hasAssignedVar a := by
  have haux : ∀ fuel a,
      b.hasResolvableVarAux fuel a = b.hasAssignedVarAux fuel a := by
    intro fuel
    induction fuel with
    | zero => intro a; rfl
    | succ n ih =>
        intro a
        cases a with
        | var v => simp [hasResolvableVarAux, hasAssignedVarAux,
            eqClassOrdered_no_equalities h]
        | expression es =>
            simp only [hasResolvableVarAux, hasAssignedVarAux]
            induction es with
            | nil => rfl
            | cons a as ihEs => simp [ih a, ihEs]
        | symbol s => rfl
        | grounded g => rfl
  intro a
  exact haux (atomScanFuel a) a

private theorem resolveAtomAux_var_mem (b : Bindings) :
    ∀ (fuel : Nat) (visited : List String) (v : String),
      v ∈ visited → b.resolveAtomAux fuel visited (.var v) = none := by
  intro fuel visited v hv
  cases fuel with
  | zero => rfl
  | succ n => simp [resolveAtomAux, hv]

private theorem resolveAtomFullAux_no_equalities {b : Bindings}
    (h : b.equalities = []) :
    ∀ (fuel : Nat) (visited : List String) (a : Atom),
      b.resolveAtomFullAux fuel visited a = b.resolveAtomAux fuel visited a := by
  intro fuel
  induction fuel with
  | zero => intro visited a; rfl
  | succ n ih =>
      intro visited a
      cases a with
      | var v =>
          by_cases hv : v ∈ visited
          · simp [resolveAtomFullAux, resolveAtomAux,
              eqClassOrdered_no_equalities h, hv]
          · cases hl : b.lookup v with
            | none =>
                simp [resolveAtomFullAux, resolveAtomAux,
                  eqClassOrdered_no_equalities h, hv, hl]
            | some value =>
                cases value with
                | var w =>
                    by_cases hw : w = v
                    · subst w
                      simp [resolveAtomFullAux, resolveAtomAux,
                        eqClassOrdered_no_equalities h, hv, hl,
                        hasAssignedVar_var_of_lookup_some hl,
                        resolveAtomAux_var_mem]
                    · simp [resolveAtomFullAux, resolveAtomAux,
                        eqClassOrdered_no_equalities h, hv, hl, hw, ih,
                        hasResolvableVar_no_equalities h]
                | symbol s =>
                    simp [resolveAtomFullAux, resolveAtomAux,
                      eqClassOrdered_no_equalities h, hv, hl, ih,
                      hasResolvableVar_no_equalities h]
                | grounded g =>
                    simp [resolveAtomFullAux, resolveAtomAux,
                      eqClassOrdered_no_equalities h, hv, hl, ih,
                      hasResolvableVar_no_equalities h]
                | expression es =>
                    simp [resolveAtomFullAux, resolveAtomAux,
                      eqClassOrdered_no_equalities h, hv, hl, ih,
                      hasResolvableVar_no_equalities h]
      | expression es =>
          simp only [resolveAtomFullAux, resolveAtomAux]
          have hfun : b.resolveAtomFullAux n visited =
              b.resolveAtomAux n visited := funext (ih visited)
          rw [hfun]
      | symbol s => rfl
      | grounded g => rfl

/-- On equality-free bindings, `resolveFull` is `resolve`. -/
theorem resolveFull_no_equalities {b : Bindings} (h : b.equalities = []) :
    ∀ (fuel : Nat) (v : String), b.resolveFull v fuel = b.resolve v fuel := by
  intro fuel v
  unfold resolveFull resolve
  rw [eqClassOrdered_no_equalities h]
  simp [resolveAtomFullAux_no_equalities h]
  cases b.lookup v <;> rfl

/-- On equality-free bindings, `applyFull` is `apply`. -/
theorem applyFull_no_equalities {b : Bindings} (h : b.equalities = []) :
    ∀ (fuel : Nat) (a : Atom), b.applyFull a fuel = b.apply a fuel := by
  intro fuel
  induction fuel with
  | zero => intro a; rfl
  | succ n ih =>
    intro a
    cases a with
    | var v =>
        rw [applyFull, apply, resolveFull_no_equalities h]
    | expression es =>
        rw [applyFull, apply]
        exact congrArg Atom.expression (List.map_congr_left fun a _ => ih a)
    | symbol s => rfl
    | grounded g => rfl

/-- POSITIVE: a valueless equality class resolves every member to the shared
    representative — the nonlinear-query case where assignment-only `apply`
    diverges from upstream.  Here `{q = p, q = p2}` sends `(f $p $p2)` to
    `(f $q $q)`. -/
example :
    ((Bindings.empty.addEquality "q" "p").addEquality "q" "p2").applyFull
      (.expression [.symbol "f", .var "p", .var "p2"]) 10 =
    .expression [.symbol "f", .var "q", .var "q"] := by decide

/-- NEGATIVE (conservativity witness): on assignment-only bindings `applyFull`
    changes nothing relative to `apply`. -/
example :
    (Bindings.empty.assign "x" (.symbol "a")).applyFull
      (.expression [.symbol "f", .var "x", .var "y"]) 10 =
    (Bindings.empty.assign "x" (.symbol "a")).apply
      (.expression [.symbol "f", .var "x", .var "y"]) 10 := by decide

/-- POSITIVE: resolution descends through variables nested in compound values. -/
example :
    ((Bindings.empty.assign "x" (.expression [.symbol "f", .var "y"])).assign
      "y" (.symbol "A")).applyFull (.var "x") 10 =
    .expression [.symbol "f", .symbol "A"] := by decide

/-- NEGATIVE: a cycle through a compound value fails resolution. -/
example :
    ((Bindings.empty.assign "x" (.expression [.symbol "f", .var "y"])).assign
      "y" (.var "x")).resolveFull "x" 10 = none := by decide

/-- Assigned names not yet visited by an alias walk. -/
def loopRemaining (b : Bindings) (visited : List String) : Finset String :=
  b.boundVars.toFinset \ visited.toFinset

theorem loopRemaining_cons (b : Bindings) (visited : List String) (name : String) :
    b.loopRemaining (name :: visited) = (b.loopRemaining visited).erase name := by
  ext key
  simp [loopRemaining, and_assoc, and_comm]


/-- Sources which carry an assignment, expanded through their equality classes. -/
def dependencySources (b : Bindings) : List String :=
  (b.assignments.flatMap fun entry => b.eqClass entry.1).eraseDups

/-- Assignment dependencies between equality classes. Variables underneath
compound values remain dependencies. A bare alias to a distinct member of its
own class is redundant; a direct self-assignment is still a dependency. -/
def dependencyTargets (b : Bindings) (source : String) : List String :=
  (b.assignments.flatMap fun (key, value) =>
    if source ∈ b.eqClass key then
      (Mettapedia.Languages.MeTTa.SubstitutionAlgebra.vars value).flatMap fun dependency =>
        if value = .var dependency ∧ key ≠ dependency ∧ dependency ∈ b.eqClass key then []
        else b.eqClass dependency
    else []).eraseDups

/-- Finite presentation of the binding dependency graph. All stored assignment
relations participate, including entries in a malformed duplicate-key record. -/
def dependencyCatalogue (b : Bindings) :
    Mettapedia.Algorithms.WellFoundedServices.Catalogue String :=
  ⟨b.dependencySources, b.dependencyTargets⟩

/-- An explicit cycle, found by the shared finite dependency service. Its
measured elimination and witness walk are total and need no caller fuel. -/
def dependencyCycle? (b : Bindings) : Option (List String) :=
  b.dependencyCatalogue.cycle?

/-- Check for a directed cycle through assignment values and equality classes.
Ref: `matcher.rs::binding_has_loops`, `metta.md`'s variable-loop filter. -/
def hasLoop (b : Bindings) : Bool := b.dependencyCycle?.isSome

theorem hasLoop_eq_true_iff_dependency_cycle (b : Bindings) :
    b.hasLoop = true ↔ ∃ name, Relation.TransGen b.dependencyCatalogue.Uses name name :=
  b.dependencyCatalogue.cycle?_isSome_iff

theorem hasLoop_false_of_no_dependency (b : Bindings)
    (noDependency : ∀ source target, target ∉ b.dependencyTargets source) :
    b.hasLoop = false := by
  rw [← Bool.not_eq_true, hasLoop_eq_true_iff_dependency_cycle]
  rintro ⟨name, cycle⟩
  have impossible : ∀ {source target},
      Relation.TransGen b.dependencyCatalogue.Uses source target → False := by
    intro source target path
    induction path with
    | single edge => exact noDependency _ _ edge.2
    | tail _ edge _ => exact noDependency _ _ edge.2
  exact impossible cycle

/-- Ground values cannot create a dependency, regardless of the equality list. -/
theorem hasLoop_false_of_assignment_vars_nil (b : Bindings)
    (ground : ∀ entry ∈ b.assignments,
      Mettapedia.Languages.MeTTa.SubstitutionAlgebra.vars entry.2 = []) :
    b.hasLoop = false := by
  apply b.hasLoop_false_of_no_dependency
  intro source target member
  simp only [dependencyTargets, List.mem_eraseDups, List.mem_flatMap] at member
  obtain ⟨⟨key, value⟩, stored, member⟩ := member
  rw [ground (key, value) stored] at member
  split at member <;> simp at member

theorem hasLoop_false_of_assignments_nil (b : Bindings) (empty : b.assignments = []) :
    b.hasLoop = false :=
  b.hasLoop_false_of_assignment_vars_nil (by simp [empty])

theorem hasLoop_empty : Bindings.empty.hasLoop = false :=
  hasLoop_false_of_assignments_nil _ rfl

/-! ### Coverage of binding-resolution depth

The existing resolver returns `none` both for a detected cycle and for a depth
cutoff; applying bindings consequently leaves the original variable in either
case. These read certificates distinguish those outcomes without changing the
resolver. A covered answer is stable at every greater depth, including a
covered negative answer. The class-and-compound cycle detector uses total finite dependency analysis;
it has no cutoff outcome requiring a depth-coverage certificate.
-/

namespace Depth

open Mettapedia.Machines.ReadOnlyQuery

/-- A recursive call made by one of the two existing binding resolvers or
binding applications. `full` selects the equality-aware operation. -/
inductive Request where
  | resolve (full : Bool) (visited : List String) (atom : Atom)
  | apply (full : Bool) (atom : Atom)

abbrev Query := Program Request (Option Atom)

def eval (b : Bindings) (depth : Nat) : Request → Option Atom
  | .resolve false visited atom => b.resolveAtomAux depth visited atom
  | .resolve true visited atom => b.resolveAtomFullAux depth visited atom
  | .apply false atom => some (b.apply atom depth)
  | .apply true atom => some (b.applyFull atom depth)

/-- The list traversal short-circuits at precisely the first failed child,
as the resolver's actual `mapM` does. -/
def resolveList (full : Bool) (visited : List String) : List Atom → Query (Option (List Atom))
  | [] => .pure (some [])
  | first :: rest => .read (.resolve full visited first) fun answer =>
      match answer with
      | none => .pure none
      | some value => map (Option.map (value :: ·)) (resolveList full visited rest)

def applyList (full : Bool) : List Atom → Query (List Atom)
  | [] => .pure []
  | first :: rest => .read (.apply full first) fun answer =>
      map (answer.getD first :: ·) (applyList full rest)

/-- Expose one layer of the actual algorithms. Recursive evaluator calls are
reads; lookup, class selection and cycle decisions remain the existing ones. -/
def body (b : Bindings) : Request → Query (Option Atom)
  | .resolve false visited (.var v) =>
      if visited.contains v then .pure none
      else match b.lookup v with
        | none => .pure (some (.var v))
        | some value =>
            if b.hasAssignedVar value then .read (.resolve false (v :: visited) value) .pure
            else .pure (some value)
  | .resolve true visited (.var v) =>
      let cls := b.eqClassOrdered v
      if cls.any visited.contains then .pure none
      else match cls.findSome? b.lookup with
        | none => .pure (some (.var (if cls = [v] then v else b.eqRepresentative v)))
        | some (.var w) =>
            if cls.contains w then
              if cls.length = 1 then .pure none else .pure (some (.var (b.eqRepresentative v)))
            else if b.hasResolvableVar (.var w) then
              .read (.resolve true (cls ++ visited) (.var w)) .pure
            else .pure (some (.var w))
        | some value =>
            if b.hasResolvableVar value then
              .read (.resolve true (cls ++ visited) value) .pure
            else .pure (some value)
  | .resolve full visited (.expression atoms) =>
      map (Option.map Atom.expression) (resolveList full visited atoms)
  | .resolve _ _ other => .pure (some other)
  | .apply false (.var v) =>
      match b.lookup v with
      | none => .pure (some (.var v))
      | some _ => .read (.resolve false [] (.var v)) fun answer =>
          .pure (some (answer.getD (.var v)))
  | .apply true (.var v) =>
      let cls := b.eqClassOrdered v
      if cls = [v] && (cls.findSome? b.lookup).isNone then .pure (some (.var v))
      else .read (.resolve true [] (.var v)) fun answer =>
          .pure (some (answer.getD (.var v)))
  | .apply full (.expression atoms) =>
      map (fun values => some (.expression values)) (applyList full atoms)
  | .apply _ other => .pure (some other)

theorem run_resolveList (b : Bindings) (depth : Nat) (full : Bool)
    (visited : List String) (atoms : List Atom) :
    (run (eval b depth) (resolveList full visited atoms)).answer =
      atoms.mapM (fun atom => eval b depth (.resolve full visited atom)) := by
  induction atoms with
  | nil => rfl
  | cons first rest ih =>
      simp only [resolveList, run, List.mapM_cons]
      cases eval b depth (.resolve full visited first) with
      | none => rfl
      | some value =>
          rw [run_map, ih]
          cases rest.mapM (fun atom => eval b depth (.resolve full visited atom)) <;> rfl

theorem run_applyList (b : Bindings) (depth : Nat) (full : Bool) (atoms : List Atom) :
    (run (eval b depth) (applyList full atoms)).answer =
      atoms.map (fun atom => if full then b.applyFull atom depth else b.apply atom depth) := by
  induction atoms with
  | nil => rfl
  | cons first rest ih =>
      cases full <;> simp [applyList, run, eval, run_map, ih]

theorem unfold_eval (b : Bindings) (depth : Nat) (request : Request) :
    eval b (depth + 1) request = (run (eval b depth) (body b request)).answer := by
  cases request with
  | resolve full visited atom =>
      cases full <;> cases atom with
      | symbol _ => rfl
      | grounded _ => rfl
      | var v =>
          simp only [eval, resolveAtomAux, resolveAtomFullAux, body]
          repeat first | split | rfl
      | expression atoms =>
          simp only [eval, resolveAtomAux, resolveAtomFullAux, body, run_map,
            run_resolveList]
          all_goals split <;> simp_all
  | apply full atom =>
      cases full with
      | false =>
          cases atom with
          | symbol _ => rfl
          | grounded _ => rfl
          | expression atoms => simp [eval, Bindings.apply, body, run_map, run_applyList]
          | var v =>
              cases found : b.lookup v with
              | none => simp [eval, Bindings.apply, body, resolve, found, run]
              | some value =>
                  simp only [eval, Bindings.apply, body, resolve, found, run]
                  cases b.resolveAtomAux depth [] (.var v) <;> rfl
      | true =>
          cases atom with
          | symbol _ => rfl
          | grounded _ => rfl
          | expression atoms => simp [eval, applyFull, body, run_map, run_applyList]
          | var v =>
              by_cases missing :
                  (b.eqClassOrdered v = [v] && ((b.eqClassOrdered v).findSome? b.lookup).isNone) = true
              · simp [eval, applyFull, body, resolveFull, missing, run]
              · cases result : b.resolveAtomFullAux depth [] (.var v) <;>
                  simp [eval, applyFull, body, resolveFull, missing, run, result]

def covered (b : Bindings) (depth : Nat) (request : Request) : Bool :=
  depthCovered (body b) (eval b) depth request

theorem stable (b : Bindings) (depth extra : Nat) (request : Request)
    (complete : covered b depth request = true) :
    eval b (depth + extra) request = eval b depth request :=
  depthCovered_stable (body b) (eval b) (unfold_eval b) depth extra request complete

end Depth

def resolveAtomCovered (b : Bindings) (visited : List String) (atom : Atom) (depth : Nat) : Bool :=
  Depth.covered b depth (.resolve false visited atom)

def resolveAtomFullCovered (b : Bindings) (visited : List String) (atom : Atom) (depth : Nat) : Bool :=
  Depth.covered b depth (.resolve true visited atom)

def applyCovered (b : Bindings) (atom : Atom) (depth : Nat) : Bool :=
  Depth.covered b depth (.apply false atom)

def applyFullCovered (b : Bindings) (atom : Atom) (depth : Nat) : Bool :=
  Depth.covered b depth (.apply true atom)

theorem resolveAtomCovered_stable (b : Bindings) (visited : List String) (atom : Atom)
    (depth extra : Nat) (complete : b.resolveAtomCovered visited atom depth = true) :
    b.resolveAtomAux (depth + extra) visited atom = b.resolveAtomAux depth visited atom :=
  Depth.stable b depth extra (.resolve false visited atom) complete

theorem resolveAtomFullCovered_stable (b : Bindings) (visited : List String) (atom : Atom)
    (depth extra : Nat) (complete : b.resolveAtomFullCovered visited atom depth = true) :
    b.resolveAtomFullAux (depth + extra) visited atom = b.resolveAtomFullAux depth visited atom :=
  Depth.stable b depth extra (.resolve true visited atom) complete

theorem applyCovered_stable (b : Bindings) (atom : Atom) (depth extra : Nat)
    (complete : b.applyCovered atom depth = true) :
    b.apply atom (depth + extra) = b.apply atom depth :=
  Option.some.inj (Depth.stable b depth extra (.apply false atom) complete)

theorem applyFullCovered_stable (b : Bindings) (atom : Atom) (depth extra : Nat)
    (complete : b.applyFullCovered atom depth = true) :
    b.applyFull atom (depth + extra) = b.applyFull atom depth :=
  Option.some.inj (Depth.stable b depth extra (.apply true atom) complete)

open Mettapedia.Machines.ReadOnlyQuery

theorem resolutionValueDepth_of_mem (b : Bindings) (name : String) (value : Atom)
    (member : (name,value) ∈ b.assignments) : atomScanFuel value ≤ b.resolutionValueDepth := by
  have bound : ∀ (entries : List (String × Atom)) (entry : String × Atom),
      entry ∈ entries → atomScanFuel entry.2 ≤
        entries.foldr (fun entry bound => max (atomScanFuel entry.2) bound) 0 := by
    intro entries
    induction entries with
    | nil => intro entry member; simp at member
    | cons first rest ih =>
        intro entry member
        rcases List.mem_cons.mp member with here | later
        · subst entry; exact Nat.le_max_left _ _
        · exact (ih entry later).trans (Nat.le_max_right _ _)
  exact bound b.assignments (name,value) member

theorem resolutionValueDepth_of_lookup (b : Bindings) (name : String) (value : Atom)
    (found : b.lookup name = some value) : atomScanFuel value ≤ b.resolutionValueDepth := by
  apply b.resolutionValueDepth_of_mem name value
  obtain ⟨first,rest,same,_⟩ := List.lookup_eq_some_iff.mp found
  rw [same]
  simp

def resolutionRank (b : Bindings) (visited : List String) (atom : Atom) : Nat :=
  (b.loopRemaining visited).card * (b.resolutionValueDepth + 1) + atomScanFuel atom

theorem resolutionRank_value (b : Bindings) (visited added : List String)
    (key name : String) (value : Atom) (assigned : key ∈ b.boundVars)
    (fresh : key ∉ visited) (marked : key ∈ added)
    (bounded : atomScanFuel value ≤ b.resolutionValueDepth) :
    b.resolutionRank (added ++ visited) value < b.resolutionRank visited (.var name) := by
  have included : b.loopRemaining (added ++ visited) ⊆
      (b.loopRemaining visited).erase key := by
    intro member present
    simp only [loopRemaining, List.toFinset_append, Finset.mem_sdiff, List.mem_toFinset,
      Finset.mem_union, not_or] at present
    simp only [Finset.mem_erase, loopRemaining, Finset.mem_sdiff, List.mem_toFinset]
    refine ⟨?_,present.1,present.2.2⟩
    intro same; subst member; exact present.2.1 marked
  have member : key ∈ b.loopRemaining visited := by
    simp [loopRemaining, assigned, fresh]
  have smaller : (b.loopRemaining (added ++ visited)).card + 1 ≤
      (b.loopRemaining visited).card := by
    have bound := Finset.card_le_card included
    have erased := Finset.card_erase_of_mem member
    have positive := Finset.card_pos.mpr ⟨key,member⟩
    omega
  have multiplied := Nat.mul_le_mul_right (b.resolutionValueDepth + 1) smaller
  simp only [Nat.add_mul, Nat.one_mul] at multiplied
  simp only [resolutionRank, atomScanFuel]
  omega

theorem resolveList_reads (store : Depth.Request → Option Atom) (full : Bool)
    (visited : List String) (atoms : List Atom) (read : Depth.Request × Option Atom)
    (member : read ∈ (run store (Depth.resolveList full visited atoms)).reads) :
    ∃ atom ∈ atoms, read.1 = .resolve full visited atom := by
  induction atoms with
  | nil => simp [Depth.resolveList, run] at member
  | cons first rest ih =>
      cases found : store (.resolve full visited first) with
      | none =>
          simp [Depth.resolveList, run, found] at member
          exact ⟨first,by simp,congrArg Prod.fst member⟩
      | some value =>
          simp only [Depth.resolveList, run, found, run_map, List.mem_cons] at member
          rcases member with same | later
          · exact ⟨first,by simp,congrArg Prod.fst same⟩
          · obtain ⟨atom,inside,same⟩ := ih later
            exact ⟨atom,by simp [inside],same⟩

theorem atomScanFuel_mem (atoms : List Atom) (atom : Atom) (member : atom ∈ atoms) :
    atomScanFuel atom < atomScanFuel (.expression atoms) := by
  have bound : ∀ atoms : List Atom, ∀ atom ∈ atoms,
      atomScanFuel atom ≤ atomScanFuel.atomListScanFuel atoms := by
    intro atoms
    induction atoms with
    | nil => intro atom member; simp at member
    | cons first rest ih =>
        intro atom member
        rcases List.mem_cons.mp member with same | later
        · subst atom; exact Nat.le_max_left _ _
        · exact (ih atom later).trans (Nat.le_max_right _ _)
  have enough := bound atoms atom member
  simp only [atomScanFuel]
  omega

theorem applyList_reads (store : Depth.Request → Option Atom) (full : Bool)
    (atoms : List Atom) (read : Depth.Request × Option Atom)
    (member : read ∈ (run store (Depth.applyList full atoms)).reads) :
    ∃ atom ∈ atoms, read.1 = .apply full atom := by
  induction atoms with
  | nil => simp [Depth.applyList, run] at member
  | cons first rest ih =>
      simp only [Depth.applyList, run, run_map, List.mem_cons] at member
      rcases member with same | later
      · exact ⟨first,by simp,congrArg Prod.fst same⟩
      · obtain ⟨atom,inside,same⟩ := ih later
        exact ⟨atom,by simp [inside],same⟩

def queryRank (b : Bindings) : Depth.Request → Nat
  | .resolve _ visited atom => b.resolutionRank visited atom
  | .apply _ atom => b.boundVars.toFinset.card * (b.resolutionValueDepth + 1) +
      atomScanFuel atom + 2

theorem lookup_key_mem (b : Bindings) (key : String) (value : Atom)
    (found : b.lookup key = some value) : key ∈ b.boundVars := by
  obtain ⟨first,rest,same,_⟩ := List.lookup_eq_some_iff.mp found
  simp [boundVars, same]

theorem class_value_rank (b : Bindings) (visited cls : List String) (name : String)
    (value : Atom) (selected : cls.findSome? b.lookup = some value)
    (fresh : cls.any visited.contains = false) :
    b.resolutionRank (cls ++ visited) value < b.resolutionRank visited (.var name) := by
  obtain ⟨key,inside,found⟩ := List.exists_of_findSome?_eq_some selected
  exact b.resolutionRank_value visited cls key name value
    (b.lookup_key_mem key value found)
    (by simpa using List.any_eq_false.mp fresh key inside) inside
    (b.resolutionValueDepth_of_lookup key value found)

theorem body_reads_decrease (b : Bindings) (store : Depth.Request → Option Atom)
    (request : Depth.Request) (read : Depth.Request × Option Atom)
    (member : read ∈ (run store (Depth.body b request)).reads) :
    b.queryRank read.1 < b.queryRank request := by
  cases request with
  | resolve full visited atom =>
      cases atom with
      | symbol name => simp [Depth.body, run] at member
      | grounded value => simp [Depth.body, run] at member
      | expression atoms =>
          simp only [Depth.body, run_map] at member
          obtain ⟨atom,inside,same⟩ := resolveList_reads store full visited atoms read member
          rw [same]
          simp only [queryRank, resolutionRank]
          have smaller := atomScanFuel_mem atoms atom inside
          omega
      | var name =>
          cases full with
          | false =>
              simp only [Depth.body] at member
              split at member
              · simp [run] at member
              · rename_i fresh
                cases found : b.lookup name with
                | none => simp [found,run] at member
                | some value =>
                    simp only [found] at member
                    split at member
                    · simp only [run, List.mem_singleton] at member
                      rw [congrArg Prod.fst member]
                      simpa only [queryRank, List.singleton_append] using
                        b.resolutionRank_value visited [name] name name value
                          (b.lookup_key_mem name value found) (by simpa using fresh)
                          (by simp) (b.resolutionValueDepth_of_lookup name value found)
                    · simp [run] at member
          | true =>
              simp only [Depth.body] at member
              split at member
              · simp [run] at member
              · rename_i fresh
                cases selected : (b.eqClassOrdered name).findSome? b.lookup with
                | none => simp [selected, run] at member
                | some value =>
                    cases value with
                    | var next =>
                        simp only [selected] at member
                        split at member
                        · split at member <;> simp [run] at member
                        · split at member
                          · simp only [run, List.mem_singleton] at member
                            rw [congrArg Prod.fst member]
                            exact b.class_value_rank visited (b.eqClassOrdered name)
                              name (.var next) selected (Bool.eq_false_iff.mpr fresh)
                          · simp [run] at member
                    | _ =>
                        simp only [selected] at member
                        split at member
                        · simp only [run, List.mem_singleton] at member
                          rw [congrArg Prod.fst member]
                          exact b.class_value_rank visited (b.eqClassOrdered name)
                            name _ selected (Bool.eq_false_iff.mpr fresh)
                        · simp [run] at member
  | apply full atom =>
      cases atom with
      | symbol name => simp [Depth.body, run] at member
      | grounded value => simp [Depth.body, run] at member
      | expression atoms =>
          simp only [Depth.body, run_map] at member
          obtain ⟨atom,inside,same⟩ := applyList_reads store full atoms read member
          rw [same]
          simp only [queryRank]
          have smaller := atomScanFuel_mem atoms atom inside
          omega
      | var name =>
          have smaller : b.queryRank (.resolve full [] (.var name)) < b.queryRank (.apply full (.var name)) := by
            simp [queryRank,resolutionRank,loopRemaining,atomScanFuel]
          cases full with
          | false =>
              cases found : b.lookup name with
              | none => simp [Depth.body,found,run] at member
              | some value =>
                  simp [Depth.body,found,run] at member
                  exact (congrArg (fun key => b.queryRank key) (congrArg Prod.fst member)) ▸ smaller
          | true =>
              simp only [Depth.body] at member
              split at member
              · simp [run] at member
              · simp [run] at member
                exact (congrArg (fun key => b.queryRank key) (congrArg Prod.fst member)) ▸ smaller



/-- Every operation requested by either binding resolver is covered above its
concrete decreasing read rank. No acyclicity assumption is required. -/
theorem queryRank_covers (b : Bindings) (depth : Nat) (request : Depth.Request)
    (enough : b.queryRank request < depth) : Depth.covered b depth request = true :=
  Mettapedia.Machines.ReadOnlyQuery.depthCovered_of_rank (Depth.body b) (Depth.eval b)
    b.queryRank (fun _ key read member => b.body_reads_decrease _ key read member)
    depth request enough

theorem applyCovered_resolutionFuel (b : Bindings) (atom : Atom) :
    b.applyCovered atom (b.resolutionFuel atom) = true := by
  apply b.queryRank_covers
  simp [queryRank, resolutionFuel]

theorem applyFullCovered_resolutionFuel (b : Bindings) (atom : Atom) :
    b.applyFullCovered atom (b.resolutionFuel atom) = true := by
  apply b.queryRank_covers
  simp [queryRank, resolutionFuel]

/-- Any independently covered depth gives the same complete application as
the structural wrapper, even if it is smaller than the structural bound. -/
theorem applyDefault_eq_of_covered (b : Bindings) (atom : Atom) (depth : Nat)
    (covered : b.applyCovered atom depth = true) : b.applyDefault atom = b.apply atom depth := by
  have first := b.applyCovered_stable atom depth (b.resolutionFuel atom) covered
  have second := b.applyCovered_stable atom (b.resolutionFuel atom) depth
    (b.applyCovered_resolutionFuel atom)
  rw [Nat.add_comm depth] at first
  exact second.symm.trans first


/-- Structural application fixes literal symbols. -/
@[simp] theorem applyDefault_symbol (b : Bindings) (name : String) :
    b.applyDefault (.symbol name) = .symbol name := by
  simp [applyDefault,resolutionFuel,Bindings.apply]

@[simp] theorem applyDefault_grounded (b : Bindings) (value : Mettapedia.Languages.MeTTa.OSLFCore.GroundedValue) :
    b.applyDefault (.grounded value) = .grounded value := by
  simp [applyDefault,resolutionFuel,Bindings.apply]

/-- Complete binding application respects the expression constructor. -/
theorem applyDefault_expression (b : Bindings) (atoms : List Atom) :
    b.applyDefault (.expression atoms) = .expression (atoms.map b.applyDefault) := by
  let rest := b.boundVars.toFinset.card * (b.resolutionValueDepth + 1) +
    atomScanFuel.atomListScanFuel atoms + 3
  have depth : b.resolutionFuel (.expression atoms) = rest + 1 := by
    simp only [resolutionFuel,atomScanFuel,rest]
    omega
  unfold applyDefault
  rw [depth,Bindings.apply]
  congr 1
  apply List.map_congr_left
  intro atom member
  apply (b.applyDefault_eq_of_covered atom rest ?_).symm
  apply b.queryRank_covers
  have smaller := atomScanFuel_mem atoms atom member
  simp only [atomScanFuel] at smaller
  simp only [queryRank,rest]
  omega


/-- Binding readout traverses a quotation expression. Evaluation of quotation
is a separate operation and does not change this structural law. -/
theorem applyDefault_quote (b : Bindings) (code : Atom) :
    b.applyDefault (.expression [.symbol "quote", code]) =
      .expression [.symbol "quote", b.applyDefault code] := by
  rw [applyDefault_expression]
  simp only [List.map_cons, List.map_nil, applyDefault_symbol]

/-- Structural depth covers ordinary resolution from every retained path. -/
theorem resolveAtomCovered_resolutionFuel (b : Bindings) (visited : List String) (atom : Atom) :
    b.resolveAtomCovered visited atom (b.resolutionFuel atom) = true := by
  apply b.queryRank_covers
  have smaller := Finset.card_le_card (Finset.sdiff_subset :
    b.boundVars.toFinset \ visited.toFinset ⊆ b.boundVars.toFinset)
  have multiplied := Nat.mul_le_mul_right (b.resolutionValueDepth + 1) smaller
  simp only [queryRank,resolutionRank,loopRemaining,resolutionFuel]
  omega

/-- The same bound covers equality-aware class resolution. -/
theorem resolveAtomFullCovered_resolutionFuel (b : Bindings) (visited : List String) (atom : Atom) :
    b.resolveAtomFullCovered visited atom (b.resolutionFuel atom) = true := by
  apply b.queryRank_covers
  have smaller := Finset.card_le_card (Finset.sdiff_subset :
    b.boundVars.toFinset \ visited.toFinset ⊆ b.boundVars.toFinset)
  have multiplied := Nat.mul_le_mul_right (b.resolutionValueDepth + 1) smaller
  simp only [queryRank,resolutionRank,loopRemaining,resolutionFuel]
  omega

/-- Increasing the structural depth preserves the complete variable answer. -/
theorem resolveDefault_stable (b : Bindings) (name : String) (extra : Nat) :
    b.resolve name (b.resolutionFuel (.var name) + extra) = b.resolveDefault name := by
  unfold resolveDefault resolve
  cases found : b.lookup name with
  | none => rfl
  | some value =>
      exact b.resolveAtomCovered_stable [] (.var name) _ extra
        (b.resolveAtomCovered_resolutionFuel [] (.var name))

namespace Depth.Controls

private def direct := Bindings.empty.assign "x" (.symbol "value")

#guard direct.applyCovered (.var "x") 2
#guard !direct.applyCovered (.var "x") 1
#guard direct.applyFullCovered (.var "x") 2
#guard !direct.applyFullCovered (.var "x") 1

private def nested :=
  ((Bindings.empty.assign "x" (.expression [.symbol "f", .var "y"])).assign
    "y" (.symbol "value"))

#guard nested.applyFullCovered (.var "x") 4
#guard !nested.applyFullCovered (.var "x") 3

private def cyclic := Bindings.empty.assign "x" (.var "x")

/-- A detected cycle is a covered negative result; exhaustion is not. -/
theorem cycle_is_complete :
    cyclic.resolveAtomAux 2 [] (.var "x") = none ∧
      cyclic.resolveAtomCovered [] (.var "x") 2 = true := by decide

theorem zero_depth_is_incomplete :
    cyclic.resolveAtomAux 0 [] (.var "x") = none ∧
      cyclic.resolveAtomCovered [] (.var "x") 0 = false := by decide

/-- An acyclic alias chain exceeds the historical loop-check cap. -/
private def longAliases : Bindings := {
  assignments := (List.range 106).map fun index =>
    (s!"v{index}", if index < 105 then .var s!"v{index + 1}" else .symbol "value")
  equalities := [] }

#guard !longAliases.hasLoop
#guard !longAliases.applyCovered (.var "v0") 100
#guard !longAliases.applyFullCovered (.var "v0") 100
#guard longAliases.applyDefault (.var "v0") == .symbol "value"
#guard longAliases.applyFullCovered (.var "v0") (longAliases.resolutionFuel (.var "v0"))

/-- A cycle remains rejected when followed by a long independent acyclic chain. -/
private def earlyCycle : Bindings :=
  { longAliases with assignments := ("self", .var "self") :: longAliases.assignments }

#guard earlyCycle.hasLoop

end Depth.Controls

/-- Convert to MeTTaCore.Bindings (only when equalities are empty/discharged).
    Returns `none` if equalities are present. -/
def toCore? (b : Bindings) : Option Mettapedia.Languages.MeTTa.OSLFCore.Bindings :=
  if b.equalities.isEmpty then
    some ⟨fun v => b.lookup v⟩
  else
    none

/-- Convert from MeTTaCore.Bindings (given a finite list of known variables). -/
def fromCore (cb : Mettapedia.Languages.MeTTa.OSLFCore.Bindings) (vars : List String) : Bindings :=
  let assignments := vars.filterMap fun v =>
    match cb.map v with
    | some a => some (v, a)
    | none => none
  ⟨assignments, []⟩

/-! ### Legacy structural binding serialization

The published minimal semantics requires the second component of a collapsed
pair to be an opaque grounded binding object.  The expression serialization
below predates that exact carrier and is retained only for validation artifacts
that inspect binding records structurally.  The active evaluator specification
uses `Spec.Eval.Minimal.Services.bindingPayload`; it does not use this encoding.

Hypercube connection (Stay–Meredith–Wells, Section 5.12): this is the reflection
operator — bindings become first-class citizens in the term language. The
collapse-bind/superpose-bind pair is a modal operator (□/◇) acting on the full
(term, context) pair. -/

private def encodeAssignment : String × Atom → Atom
  | (v, a) => .expression [.symbol v, a]

private def decodeAssignment? : Atom → Option (String × Atom)
  | .expression [.symbol v, a] => some (v, a)
  | _ => none

private def encodeEquality : String × String → Atom
  | (a, c) => .expression [.symbol a, .symbol c]

private def decodeEquality? : Atom → Option (String × String)
  | .expression [.symbol a, .symbol c] => some (a, c)
  | _ => none

/-- Serialize bindings as an ordinary expression for legacy validation tools. -/
def toLegacyStructuralAtom (b : Bindings) : Atom :=
  .expression [.symbol "Bindings",
    .expression (b.assignments.map encodeAssignment),
    .expression (b.equalities.map encodeEquality)]

/-- Decode the legacy structural serialization. -/
def ofLegacyStructuralAtom? : Atom → Option Bindings
  | .expression [.symbol "Bindings", .expression assigns, .expression eqs] =>
    let assignments := assigns.filterMap decodeAssignment?
    let equalities := eqs.filterMap decodeEquality?
    if assignments.length = assigns.length && equalities.length = eqs.length then
      some ⟨assignments, equalities⟩
    else none
  | _ => none

private theorem filterMap_decode_encode_assignments (xs : List (String × Atom)) :
    (xs.map encodeAssignment).filterMap decodeAssignment? = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases x
      simp only [List.map_cons, List.filterMap_cons, encodeAssignment, decodeAssignment?]
      exact congrArg (_ :: ·) ih

private theorem filterMap_decode_encode_equalities (xs : List (String × String)) :
    (xs.map encodeEquality).filterMap decodeEquality? = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      cases x
      simp only [List.map_cons, List.filterMap_cons, encodeEquality, decodeEquality?]
      exact congrArg (_ :: ·) ih

theorem ofLegacyStructuralAtom_toLegacyStructuralAtom (b : Bindings) :
    ofLegacyStructuralAtom? (toLegacyStructuralAtom b) = some b := by
  simp only [toLegacyStructuralAtom, ofLegacyStructuralAtom?]
  rw [filterMap_decode_encode_assignments, filterMap_decode_encode_equalities]
  simp [List.length_map]

end Bindings

/-! ## Result Types -/

/-- A single result from the HE interpreter: an atom paired with bindings.
    Ref: metta.md line 250 "[(Atom, Bindings)]". -/
abbrev ResultPair := Atom × Bindings

/-- The result set from the HE interpreter.
    Ref: metta.md line 250. -/
abbrev ResultSet := List ResultPair

/-! ## Result Equivalence

The HE spec is partially ambiguous about result ordering.
`interpret_expression` explicitly returns `$tuples + $errors` (ordered).
But within each group, order depends on type-list iteration (unspecified).

We define two equivalences:
- `ResultEqOrdered`: exact list equality (where spec mandates order)
- `ResultEqBag`: multiset equivalence (where spec is silent on order)
-/

/-- Ordered result equivalence (list equality). -/
def ResultEqOrdered (r1 r2 : ResultSet) : Prop := r1 = r2

/-- Multiset (bag) result equivalence, ignoring order.
    Two result sets are bag-equivalent when they are permutations. -/
def ResultEqBag (r1 r2 : ResultSet) : Prop :=
  r1.Perm r2

/-! ## Function Type Utilities

Ref: metta.md lines 98-104 `(-> arg1_type ... argN_type ret_type)`. -/

/-- Check if an atom is a function type `(-> ...)`. -/
def isFunctionType : Atom → Bool
  | .expression (.symbol "->" :: _ :: _) => true
  | _ => false

/-- Extract argument types from a function type `(-> t1 t2 ... tN ret)`.
    Returns all types except the last (which is the return type). -/
def getFunctionArgTypes : Atom → Option (List Atom)
  | .expression (.symbol "->" :: rest) =>
    if rest.length ≥ 1 then some (rest.dropLast)
    else none
  | _ => none

/-- Extract the return type from a function type `(-> ... ret)`. -/
def getFunctionRetType : Atom → Option Atom
  | .expression (.symbol "->" :: rest) =>
    if rest.length ≥ 1 then rest.getLast?
    else none
  | _ => none

/-- Get the number of arguments a function type expects. -/
def getFunctionArity : Atom → Option Nat :=
  fun a => (getFunctionArgTypes a).map List.length

/-! ## Atom Predicates (HE-specific) -/

/-- Check if atom is Empty.
    Ref: metta.md line 253. -/
def isEmptyAtom (a : Atom) : Bool := a == Atom.empty

/-- Check if atom is an Error expression.
    Ref: metta.md line 253. -/
def isErrorAtom : Atom → Bool
  | .expression (.symbol "Error" :: _) => true
  | _ => false

/-- Check if atom is Empty or Error.
    Used in short-circuit conditions throughout the interpreter. -/
def isEmptyOrError (a : Atom) : Bool :=
  isEmptyAtom a || isErrorAtom a

/-- A successful singleton tuple retains its expression wrapper. Failures
propagate without becoming successful tuple values; bindings are unchanged. -/
def tupleSingleton (r : ResultPair) : ResultPair :=
  if isEmptyOrError r.1 then r else (.expression [r.1], r.2)

@[simp] theorem tupleSingleton_bindings (r : ResultPair) :
    (tupleSingleton r).2 = r.2 := by
  unfold tupleSingleton
  split <;> rfl

@[simp] theorem tupleSingleton_success (r : ResultPair)
    (h : isEmptyOrError r.1 = false) :
    tupleSingleton r = (.expression [r.1], r.2) := by
  simp [tupleSingleton, h]

@[simp] theorem tupleSingleton_failure (r : ResultPair)
    (h : isEmptyOrError r.1 = true) : tupleSingleton r = r := by
  simp [tupleSingleton, h]

/-! ## Convenience Constructors (for tests) -/

/-- Shorthand for symbol atom. -/
abbrev sym := Atom.symbol

/-- Shorthand for variable atom. -/
abbrev vr := Atom.var

/-- Shorthand for expression atom. -/
abbrev expr := Atom.expression

/-! ## Meta-type of an atom

Returns the meta-type as a symbol atom.
Ref: metta.md line 252 `<meta-type of the $atom>`. -/

/-- Get the meta-type of an atom as a symbol.
    Ref: metta.md implicit in interpreter, explicit in `types.rs:get_meta_type`. -/
def getMetaType : Atom → Atom
  | .symbol _ => Atom.symbolType
  | .var _ => Atom.variableType
  | .grounded _ => Atom.groundedType
  | .expression _ => Atom.expressionType

/-! ## Unit Tests -/

section Tests

-- Error code construction
example : (ErrorCode.stackOverflow).toAtom = .symbol "StackOverflow" := rfl
example : (ErrorCode.badType (.symbol "Int") (.symbol "Bool")).toAtom =
    .expression [.symbol "BadType", .symbol "Int", .symbol "Bool"] := rfl

-- mkError
example : mkError (.symbol "x") .stackOverflow =
    .expression [.symbol "Error", .symbol "x", .symbol "StackOverflow"] := rfl

-- Bindings
example : Bindings.empty.assignments = [] := rfl
example : Bindings.empty.equalities = [] := rfl
example : (Bindings.empty.assign "x" (.symbol "a")).lookup "x" = some (.symbol "a") := rfl
example : (Bindings.empty.assign "x" (.symbol "a")).lookup "y" = none := rfl

-- Function type utilities
example : isFunctionType (.expression [.symbol "->", .symbol "Int", .symbol "Bool"]) = true := rfl
example : isFunctionType (.symbol "Int") = false := rfl
example : getFunctionArgTypes (.expression [.symbol "->", .symbol "Int", .symbol "Bool"]) =
    some [.symbol "Int"] := rfl
example : getFunctionRetType (.expression [.symbol "->", .symbol "Int", .symbol "Bool"]) =
    some (.symbol "Bool") := rfl

-- Meta-type
example : getMetaType (.symbol "x") = Atom.symbolType := rfl
example : getMetaType (.var "x") = Atom.variableType := rfl
example : getMetaType (.expression []) = Atom.expressionType := rfl
example : getMetaType (.grounded (.int 42)) = Atom.groundedType := rfl

-- Predicates
example : isEmptyAtom Atom.empty = true := rfl
example : isErrorAtom (Atom.error (.symbol "x") (.symbol "msg")) = true := rfl
example : isEmptyOrError Atom.empty = true := rfl
example : isEmptyOrError (Atom.error (.symbol "x") (.symbol "msg")) = true := rfl
example : isEmptyOrError (.symbol "foo") = false := rfl

-- ResultEqBag reflexivity
example : ResultEqBag ([] : ResultSet) [] := List.Perm.nil

end Tests

end Mettapedia.Languages.MeTTa.HE
