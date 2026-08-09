import Mettapedia.Languages.MeTTa.OSLFCore.Bindings

/-!
# HE MeTTa Types

Foundation types for the Hyperon Experimental MeTTa interpreter formalization.

## Source Precedence
1. `hyperon-experimental/lib/src/metta/interpreter.rs` (ground truth)
2. `hyperon-experimental/docs/metta.md` (spec prose)

## Main Definitions
* `ErrorCode` - Structured error codes (normative from HE spec)
* `Bindings` - Variable bindings with assignments AND equalities
* `ResultPair` / `ResultSet` - Interpreter output types
* `ResultEqBag` / `ResultEqOrdered` - Result equivalence relations
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## Error Codes

Normative from HE spec. Error *text* is non-normative; only these
constructors/shapes are normative. -/

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
private def atomScanFuel : Atom → Nat
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

/-- Convenience wrapper for callers outside the trusted theorem boundary. -/
def resolveDefault (b : Bindings) (v : String) : Option Atom :=
  b.resolve v 100

/-- Get all variable names that are bound (have assignments). -/
def boundVars (b : Bindings) : List String :=
  b.assignments.map Prod.fst

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

/-- Convenience wrapper for callers outside the trusted theorem boundary. -/
def applyDefault (b : Bindings) (a : Atom) : Atom :=
  b.apply a 100

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

/-- Check if bindings contain a variable loop.
    Ref: metta.md line 616 "filter(lambda $b: <$b doesn't have variable loops>)". -/
def hasLoop (b : Bindings) : Bool :=
  b.assignments.any fun (v, _) => hasLoopFrom b v [v] 100
where
  hasLoopFrom (b : Bindings) (v : String) (visited : List String) (fuel : Nat) : Bool :=
    match fuel with
    | 0 => true  -- conservative: assume loop on fuel exhaustion
    | n + 1 =>
      match b.lookup v with
      | none => false
      | some (.var w) =>
        if visited.contains w then true
        else hasLoopFrom b w (w :: visited) n
      | some _ => false

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
  | cons x xs ih => cases x; simp [encodeAssignment, decodeAssignment?]

private theorem filterMap_decode_encode_equalities (xs : List (String × String)) :
    (xs.map encodeEquality).filterMap decodeEquality? = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x; simp [encodeEquality, decodeEquality?]

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
