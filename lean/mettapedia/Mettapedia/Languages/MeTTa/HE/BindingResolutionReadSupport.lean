import Mettapedia.Languages.MeTTa.HE.Types
import Mettapedia.Languages.MeTTa.SubstitutionAlgebra
import Mettapedia.Machines.ReadOnlyQuery

/-!
# Assignment read support for equality-aware HE resolution

The public HE resolver follows assignments through ordered equality classes.
Its finite support includes the class lookups, the variables inspected by its
resolvability guard, and the recursively inspected assignment values. Absent
lookups are dependencies too. The support conservatively records every member
of an inspected equality class, even if its first value stops the search.

Equality authority is retained separately: reusing an assignment certificate
requires the ordered equality relations to remain unchanged. The result theorem
preserves the actual `resolveFull`, including fuel exhaustion and cycle rejection.
The same holds of `applyFull`, the application of bindings to an atom that the
HE evaluator performs: its support is the support of each variable occurrence.
It makes no claim about an interpreter, mutable C storage, or pointer lifetime.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.BindingResolutionReadSupport

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.SubstitutionAlgebra (vars)

open Mettapedia.Machines

/-- The assignment lookups that govern the resolvability scan of a value.
The scan tests the assignment of each variable itself, and only when that
variable's equality class is trivial; it never reads another class member. -/
def guardSupport (atom : Atom) : List String := vars atom

/-- Finite transitive support for the actual equality-aware recursive resolver.
Fuel bounds recursive discovery and visited classes stop dependency cycles.
The support may also inspect a value that the resolver's guard leaves unchanged. -/
def atomSupport (bindings : Bindings) : Nat → List String → Atom → List String
  | 0, _, _ => []
  | remaining + 1, visited, .var key =>
      let cls := bindings.eqClassOrdered key
      if cls.any visited.contains then []
      else cls ++ match cls.findSome? bindings.lookup with
        | none => []
        | some value =>
            guardSupport value ++
              atomSupport bindings remaining (cls ++ visited) value
  | remaining + 1, visited, .expression atoms =>
      atoms.flatMap (atomSupport bindings remaining visited)
  | _ + 1, _, _ => []

/-- The public entry checks class assignments even when recursive fuel is zero. -/
def support (bindings : Bindings) (key : String) (fuel : Nat) : List String :=
  bindings.eqClassOrdered key ++ atomSupport bindings fuel [] (.var key)

/-- Complete assignment values sampled at every supporting coordinate. -/
def reads (bindings : Bindings) (key : String) (fuel : Nat) :
    ReadOnlyQuery.Reads String (Option Atom) :=
  ReadOnlyQuery.samples bindings.lookup (support bindings key fuel)

private theorem classes_eq {first second : Bindings}
    (equalities : second.equalities = first.equalities) (key : String) :
    second.eqClassOrdered key = first.eqClassOrdered key := by
  simp only [Bindings.eqClassOrdered, Bindings.eqVarsInOrder, Bindings.eqClass,
    equalities]

private theorem representative_eq {first second : Bindings}
    (equalities : second.equalities = first.equalities) (key : String) :
    second.eqRepresentative key = first.eqRepresentative key := by
  simp only [Bindings.eqRepresentative, classes_eq equalities]

private theorem findSome_eq (first second : Bindings) (keys : List String)
    (agree : ∀ key ∈ keys, second.lookup key = first.lookup key) :
    keys.findSome? second.lookup = keys.findSome? first.lookup := by
  induction keys with
  | nil => rfl
  | cons key rest ih =>
      simp only [List.findSome?_cons, agree key (by simp)]
      cases first.lookup key with
      | none => exact ih (fun key member => agree key (by simp [member]))
      | some value => rfl

private theorem vars_expression (atoms : List Atom) :
    vars (.expression atoms) = atoms.flatMap vars := by
  simp only [vars]
  induction atoms with
  | nil => rfl
  | cons atom rest ih => simp [vars.varsList, ih]

private theorem guardAux_eq {first second : Bindings}
    (equalities : second.equalities = first.equalities) :
    ∀ fuel atom,
      (∀ key ∈ vars atom, second.lookup key = first.lookup key) →
      second.hasResolvableVarAux fuel atom = first.hasResolvableVarAux fuel atom := by
  intro fuel
  induction fuel with
  | zero => intro atom agree; rfl
  | succ remaining ih =>
      intro atom agree
      cases atom with
      | symbol name => rfl
      | grounded value => rfl
      | var key =>
          simp only [Bindings.hasResolvableVarAux, classes_eq equalities,
            Bindings.isBound, agree key (by simp [vars])]
      | expression atoms =>
          simp only [Bindings.hasResolvableVarAux]
          induction atoms with
          | nil => rfl
          | cons atom rest tail =>
              have headAgree : ∀ key ∈ vars atom,
                  second.lookup key = first.lookup key := by
                intro key member
                apply agree key
                simp only [vars_expression, List.mem_flatMap]
                exact ⟨atom, by simp, member⟩
              have tailAgree : ∀ key ∈ vars (.expression rest),
                  second.lookup key = first.lookup key := by
                intro key member
                apply agree key
                simp only [vars_expression, List.mem_flatMap] at member ⊢
                rcases member with ⟨child, contained, read⟩
                exact ⟨child, List.mem_cons_of_mem atom contained, read⟩
              simp only [List.any_cons, ih atom headAgree, tail tailAgree]

private theorem guard_eq {first second : Bindings}
    (equalities : second.equalities = first.equalities) (atom : Atom)
    (agree : ∀ key ∈ vars atom, second.lookup key = first.lookup key) :
    second.hasResolvableVar atom = first.hasResolvableVar atom := by
  unfold Bindings.hasResolvableVar
  exact guardAux_eq equalities _ atom agree

/-- Agreement on transitive assignment reads preserves the actual recursive
resolution, including the original fuel and visited-path rejection. -/
theorem resolveAtomFullAux_eq_of_support {first second : Bindings}
    (equalities : second.equalities = first.equalities) :
    ∀ fuel visited atom,
      (∀ key ∈ atomSupport first fuel visited atom,
        second.lookup key = first.lookup key) →
      second.resolveAtomFullAux fuel visited atom =
        first.resolveAtomFullAux fuel visited atom := by
  intro fuel
  induction fuel with
  | zero => intro visited atom agree; rfl
  | succ remaining ih =>
      intro visited atom agree
      cases atom with
      | symbol name => rfl
      | grounded value => rfl
      | expression atoms =>
          simp only [Bindings.resolveAtomFullAux]
          have children : ∀ atom ∈ atoms,
              second.resolveAtomFullAux remaining visited atom =
                first.resolveAtomFullAux remaining visited atom := by
            intro atom member
            exact ih visited atom (fun key contained =>
              agree key (by
                simp only [atomSupport, List.mem_flatMap]
                exact ⟨atom, member, contained⟩))
          have mapped : atoms.mapM (second.resolveAtomFullAux remaining visited) =
              atoms.mapM (first.resolveAtomFullAux remaining visited) := by
            clear agree
            induction atoms with
            | nil => rfl
            | cons atom rest tail =>
                simp only [List.mapM_cons, children atom (by simp)]
                rw [tail (fun atom member => children atom (by simp [member]))]
          rw [mapped]
      | var root =>
          simp only [Bindings.resolveAtomFullAux, classes_eq equalities]
          by_cases visitedClass : (first.eqClassOrdered root).any visited.contains = true
          · simp only [visitedClass, ↓reduceIte]
          · have classAgree : ∀ key ∈ (first.eqClassOrdered root), second.lookup key = first.lookup key := by
              intro key member
              apply agree key
              simp only [atomSupport, visitedClass, Bool.false_eq_true, ↓reduceIte, List.mem_append]
              exact Or.inl member
            have found := findSome_eq first second (first.eqClassOrdered root) classAgree
            rw [found]
            cases valueFound : (first.eqClassOrdered root).findSome? first.lookup with
            | none => simp only [representative_eq equalities]
            | some value =>
                have nextAgree : ∀ key ∈
                    atomSupport first remaining ((first.eqClassOrdered root) ++ visited) value,
                    second.lookup key = first.lookup key := by
                  intro key member
                  apply agree key
                  simp only [atomSupport, visitedClass, Bool.false_eq_true, ↓reduceIte, valueFound,
                    List.mem_append]
                  exact Or.inr (Or.inr member)
                have guardAgree : ∀ key ∈ guardSupport value,
                    second.lookup key = first.lookup key := by
                  intro key member
                  apply agree key
                  simp only [atomSupport, visitedClass, Bool.false_eq_true, ↓reduceIte, valueFound,
                    List.mem_append]
                  exact Or.inr (Or.inl member)
                have scanned := guard_eq equalities value guardAgree
                have continued := ih ((first.eqClassOrdered root) ++ visited) value nextAgree
                cases value <;> simp only [scanned, continued,
                  representative_eq equalities]

/-- A valid read certificate licenses reuse of the public HE resolution.
The equality relations remain a separate governing authority. -/
theorem resolveFull_eq_of_reads {first second : Bindings}
    (equalities : second.equalities = first.equalities)
    (key : String) (fuel : Nat)
    (agree : ReadOnlyQuery.Agrees second.lookup (reads first key fuel)) :
    second.resolveFull key fuel = first.resolveFull key fuel := by
  have lookups := (ReadOnlyQuery.agrees_samples_iff first.lookup second.lookup
    (support first key fuel)).mp agree
  have classAgree : ∀ observed ∈ first.eqClassOrdered key,
      second.lookup observed = first.lookup observed :=
    fun observed member => lookups observed (List.mem_append_left _ member)
  have atomAgree : ∀ observed ∈ atomSupport first fuel [] (.var key),
      second.lookup observed = first.lookup observed :=
    fun observed member => lookups observed (List.mem_append_right _ member)
  simp only [Bindings.resolveFull, classes_eq equalities,
    findSome_eq first second _ classAgree,
    resolveAtomFullAux_eq_of_support equalities fuel [] (.var key) atomAgree]

theorem resolveFull_eq_of_checkReads {first second : Bindings}
    (equalities : second.equalities = first.equalities)
    (key : String) (fuel : Nat)
    (valid : ReadOnlyQuery.checkReads second.lookup (reads first key fuel) = true) :
    second.resolveFull key fuel = first.resolveFull key fuel :=
  resolveFull_eq_of_reads equalities key fuel ((ReadOnlyQuery.checkReads_iff _ _).mp valid)

/-- Assignment lookups read when bindings are applied to an atom: the support
of each variable occurrence, at the fuel the application gives it. -/
def applySupport (bindings : Bindings) : Nat → Atom → List String
  | 0, _ => []
  | remaining + 1, .var key => support bindings key remaining
  | remaining + 1, .expression atoms => atoms.flatMap (applySupport bindings remaining)
  | _ + 1, _ => []

/-- Complete assignment values sampled at every coordinate an application
reads. -/
def applyReads (bindings : Bindings) (atom : Atom) (fuel : Nat) :
    ReadOnlyQuery.Reads String (Option Atom) :=
  ReadOnlyQuery.samples bindings.lookup (applySupport bindings fuel atom)

/-- Agreement on the support of an application preserves the application,
including every variable left in place by an exhausted or rejected
resolution. -/
theorem applyFull_eq_of_support {first second : Bindings}
    (equalities : second.equalities = first.equalities) :
    ∀ fuel atom,
      (∀ key ∈ applySupport first fuel atom, second.lookup key = first.lookup key) →
      second.applyFull atom fuel = first.applyFull atom fuel := by
  intro fuel
  induction fuel with
  | zero => intro atom agree; rfl
  | succ remaining ih =>
      intro atom agree
      cases atom with
      | symbol name => rfl
      | grounded value => rfl
      | var key =>
          have resolved := resolveFull_eq_of_reads equalities key remaining
            ((ReadOnlyQuery.agrees_samples_iff _ _ _).mpr agree)
          simp only [Bindings.applyFull, resolved]
      | expression atoms =>
          simp only [Bindings.applyFull]
          congr 1
          apply List.map_congr_left
          intro child member
          exact ih child (fun key contained => agree key (by
            simp only [applySupport, List.mem_flatMap]
            exact ⟨child, member, contained⟩))

/-- A valid read certificate licenses reuse of an application of bindings. -/
theorem applyFull_eq_of_reads {first second : Bindings}
    (equalities : second.equalities = first.equalities)
    (atom : Atom) (fuel : Nat)
    (agree : ReadOnlyQuery.Agrees second.lookup (applyReads first atom fuel)) :
    second.applyFull atom fuel = first.applyFull atom fuel :=
  applyFull_eq_of_support equalities fuel atom
    ((ReadOnlyQuery.agrees_samples_iff _ _ _).mp agree)

private theorem lookup_map_of_key_preserved (transform : String × Atom → String × Atom)
    (changed key : String) (different : key ≠ changed)
    (keys : ∀ entry, (transform entry).1 = entry.1)
    (values : ∀ entry, entry.1 ≠ changed → (transform entry).2 = entry.2) :
    ∀ assignments : List (String × Atom),
      (assignments.map transform).lookup key = assignments.lookup key
  | [] => rfl
  | (name, old) :: rest => by
      have tail := lookup_map_of_key_preserved transform changed key different keys values rest
      have shape : transform (name, old) = (name, (transform (name, old)).2) :=
        Prod.ext (keys _) rfl
      rw [List.map_cons, shape, List.lookup_cons, List.lookup_cons, tail]
      cases hit : key == name with
      | false => rfl
      | true =>
          have equal : key = name := by simpa using hit
          simp only [values (name, old) (equal ▸ different)]

/-- An assignment changes the lookup of its own variable only, whether that
variable was unassigned or already assigned. -/
theorem lookup_assign_of_ne (bindings : Bindings) (changed : String) (value : Atom)
    (key : String) (different : key ≠ changed) :
    (bindings.assign changed value).lookup key = bindings.lookup key := by
  by_cases bound : bindings.isBound changed = true
  · simp only [Bindings.assign, Bindings.lookup, bound, if_true]
    refine lookup_map_of_key_preserved _ changed key different ?_ ?_ bindings.assignments
    · rintro ⟨name, old⟩
      by_cases same : (name == changed) = true <;> simp [same]
    · rintro ⟨name, old⟩ other
      have distinct : (name == changed) = false := by simpa using other
      simp [distinct]
  · simp only [Bindings.assign, Bindings.lookup, bound, Bool.false_eq_true, if_false,
      List.lookup_append]
    cases bindings.assignments.lookup key with
    | some found => rfl
    | none => simp [different]

/-- An assignment outside the transitive support preserves the public
resolution, whether it binds a fresh variable or rebinds an assigned one. -/
theorem resolveFull_assign_unrelated (bindings : Bindings)
    (root changed : String) (value : Atom) (fuel : Nat)
    (outside : changed ∉ support bindings root fuel) :
    (bindings.assign changed value).resolveFull root fuel =
      bindings.resolveFull root fuel := by
  apply resolveFull_eq_of_reads (first := bindings)
    (second := bindings.assign changed value) rfl root fuel
  apply (ReadOnlyQuery.agrees_samples_iff _ _ _).mpr
  intro key member
  exact lookup_assign_of_ne bindings changed value key fun same => outside (same ▸ member)

/-- An assignment outside the support of an application preserves the
application. -/
theorem applyFull_assign_unrelated (bindings : Bindings)
    (atom : Atom) (changed : String) (value : Atom) (fuel : Nat)
    (outside : changed ∉ applySupport bindings fuel atom) :
    (bindings.assign changed value).applyFull atom fuel = bindings.applyFull atom fuel :=
  applyFull_eq_of_support (first := bindings) (second := bindings.assign changed value) rfl
    fuel atom fun key member =>
      lookup_assign_of_ne bindings changed value key fun same => outside (same ▸ member)

/-- Array-trace stability transports the certificate into the real HE
resolver when the two assignment lookup maps realize the trace endpoints.
Equality relations are a separate retained authority. -/
theorem resolveFull_eq_of_untouched_trace {first second : Bindings}
    (equalities : second.equalities = first.equalities)
    (initial : String → Option Atom)
    (writes : Nat → Option
      (Mettapedia.Logic.ArrayInvariants.UpdateTrace.Write String (Option Atom)))
    (start finish : Nat)
    (firstLookup : first.lookup =
      Mettapedia.Logic.ArrayInvariants.UpdateTrace.trace initial writes start)
    (secondLookup : second.lookup =
      Mettapedia.Logic.ArrayInvariants.UpdateTrace.trace initial writes finish)
    (root : String) (fuel : Nat) (ordered : start ≤ finish)
    (untouched : ∀ key ∈ support first root fuel, ∀ i,
      start ≤ i → i < finish →
        ¬ Mettapedia.Logic.ArrayInvariants.UpdateTrace.Updates writes i key) :
    second.resolveFull root fuel = first.resolveFull root fuel := by
  apply resolveFull_eq_of_reads equalities
  have valid : ReadOnlyQuery.Agrees
      (Mettapedia.Logic.ArrayInvariants.UpdateTrace.trace initial writes start)
      (reads first root fuel) := by
    rw [← firstLookup]
    exact (ReadOnlyQuery.agrees_samples_iff _ _ _).mpr (fun _ _ => rfl)
  have retained := ReadOnlyQuery.trace_preserves_reads initial writes start finish
    (reads first root fuel) valid ordered (by
      intro observed member
      simp only [reads, ReadOnlyQuery.samples, List.mem_map] at member
      rcases member with ⟨key, contained, rfl⟩
      exact untouched key contained)
  rw [secondLookup]
  exact retained

namespace Controls

def openAlias : Bindings :=
  { assignments := [("x", .var "y")], equalities := [] }

def firstBranch : Bindings := openAlias.assign "y" (.symbol "A")

/-- Restoring the open checkpoint and writing the other branch's value. -/
def secondBranch : Bindings := openAlias.assign "y" (.symbol "B")

theorem transitive_read_resolves :
    firstBranch.resolveFull "x" 6 = some (.symbol "A") ∧
      "y" ∈ support firstBranch "x" 6 := by
  decide

theorem unrelated_assignment_preserves :
    (firstBranch.assign "z" (.symbol "Other")).resolveFull "x" 6 =
      firstBranch.resolveFull "x" 6 := by
  exact resolveFull_assign_unrelated firstBranch "x" "z" (.symbol "Other") 6 (by decide)

/-- Rebinding an unrelated variable that already has a value preserves the
resolution too. -/
theorem unrelated_rebinding_preserves :
    ((firstBranch.assign "z" (.symbol "Other")).assign "z" (.symbol "Again")).resolveFull "x" 6 =
      firstBranch.resolveFull "x" 6 := by
  rw [resolveFull_assign_unrelated _ "x" "z" (.symbol "Again") 6 (by decide)]
  exact unrelated_assignment_preserves

/-- Root-cell agreement misses the assignment actually followed by the resolver. -/
theorem root_only_certificate_is_insufficient :
    ReadOnlyQuery.checkReads secondBranch.lookup
        (ReadOnlyQuery.samples firstBranch.lookup ["x"]) = true ∧
      secondBranch.resolveFull "x" 6 ≠ firstBranch.resolveFull "x" 6 := by
  decide

/-- The unbound target is observed even when the guard skips recursion. -/
theorem formerly_absent_assignment_invalidates :
    openAlias.lookup "y" = none ∧
      "y" ∈ support openAlias "x" 6 ∧
      ReadOnlyQuery.checkReads firstBranch.lookup (reads openAlias "x" 6) = false ∧
      firstBranch.resolveFull "x" 6 ≠ openAlias.resolveFull "x" 6 := by
  decide

theorem restored_alias_rebinding_invalidates :
    firstBranch.lookup "x" = secondBranch.lookup "x" ∧
      ReadOnlyQuery.checkReads secondBranch.lookup (reads firstBranch "x" 6) = false ∧
      firstBranch.resolveFull "x" 6 = some (.symbol "A") ∧
      secondBranch.resolveFull "x" 6 = some (.symbol "B") := by
  decide

def equalitySource : Bindings :=
  { assignments := [("z", .symbol "B")], equalities := [] }

/-- Assignment reads alone do not protect a changed equality-class authority. -/
theorem equality_authority_must_be_retained :
    ReadOnlyQuery.checkReads (equalitySource.addEquality "z" "x").lookup
        (reads equalitySource "x" 6) = true ∧
      (equalitySource.addEquality "z" "x").resolveFull "x" 6 = some (.symbol "B") ∧
      equalitySource.resolveFull "x" 6 = none := by
  decide

def equalityAlias : Bindings := firstBranch.addEquality "z" "x"

/-- Reusing the class reads preserves resolution through the equality alias. -/
theorem equality_aware_resolution_preserves :
    equalityAlias.resolveFull "z" 6 = some (.symbol "A") ∧
      (equalityAlias.assign "other" (.symbol "Other")).resolveFull "z" 6 =
        equalityAlias.resolveFull "z" 6 := by
  constructor
  · decide
  · exact resolveFull_assign_unrelated equalityAlias "z" "other" (.symbol "Other") 6
      (by decide)

def compound : Bindings :=
  { assignments := [("x", .expression [.symbol "Pair", .var "y", .var "y"]),
      ("y", .symbol "A")], equalities := [] }

theorem correlated_compound_resolution :
    compound.resolveFull "x" 6 =
      some (.expression [.symbol "Pair", .symbol "A", .symbol "A"]) ∧
      (compound.assign "z" (.symbol "Other")).resolveFull "x" 6 =
        compound.resolveFull "x" 6 := by
  constructor
  · decide
  · exact resolveFull_assign_unrelated compound "x" "z" (.symbol "Other") 6
      (by decide)

def cyclic : Bindings :=
  { assignments := [("x", .var "y"), ("y", .var "x")], equalities := [] }

theorem rejection_is_preserved :
    cyclic.resolveFull "x" 6 = none ∧
      (cyclic.assign "z" (.symbol "Other")).resolveFull "x" 6 = none ∧
      firstBranch.resolveFull "x" 0 = none := by
  decide

def pairOfAlias : Atom := .expression [.symbol "Pair", .var "x", .var "w"]

/-- An application reads the support of each of its variables, including a
variable with no assignment. -/
theorem application_reads_each_variable :
    firstBranch.applyFull pairOfAlias 7 =
        .expression [.symbol "Pair", .symbol "A", .var "w"] ∧
      "y" ∈ applySupport firstBranch 7 pairOfAlias ∧
      "w" ∈ applySupport firstBranch 7 pairOfAlias := by
  decide

theorem unrelated_assignment_preserves_application :
    (firstBranch.assign "z" (.symbol "Other")).applyFull pairOfAlias 7 =
      firstBranch.applyFull pairOfAlias 7 :=
  applyFull_assign_unrelated firstBranch pairOfAlias "z" (.symbol "Other") 7 (by decide)

/-- Binding a variable the application left in place invalidates its
certificate, and so does rebinding the target of an alias. -/
theorem changed_dependency_invalidates_application :
    ReadOnlyQuery.checkReads (firstBranch.assign "w" (.symbol "C")).lookup
        (applyReads firstBranch pairOfAlias 7) = false ∧
      (firstBranch.assign "w" (.symbol "C")).applyFull pairOfAlias 7 ≠
        firstBranch.applyFull pairOfAlias 7 ∧
      ReadOnlyQuery.checkReads secondBranch.lookup
        (applyReads firstBranch pairOfAlias 7) = false ∧
      secondBranch.applyFull pairOfAlias 7 ≠ firstBranch.applyFull pairOfAlias 7 := by
  decide

end Controls

end Mettapedia.Languages.MeTTa.HE.BindingResolutionReadSupport
