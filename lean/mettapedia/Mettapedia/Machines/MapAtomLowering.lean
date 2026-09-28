import Mettapedia.Machines.SuperposeFusion
import Mettapedia.Languages.MeTTa.PeTTa.ValueOccurrences

/-!
# Reusable callbacks for finite relational list mapping

`SuperposeFusion.mapAtom` independently specifies the ordered Cartesian
product. `enumerate` instead accumulates results backwards and invokes its
continuation at complete leaves. Its correctness theorem preserves order,
multiplicity and failure, without a single-result assumption.

The callback compiler stores the source plan once and snapshots only the
source's free variable occurrences. Its arguments and captures remain values,
including values which spell executable calls. Correctness follows from the
existing value-occurrence substitution theorem, plus a proved lookup property
of the actual capture table. Fresh opening is a separate corollary with its
explicit freshness condition.

This is finite, pure answer semantics. Mutation, exceptions, divergence and
scoped commitment are not inferred from list equality. A runtime lowering
must preserve their continuation boundaries or leave those bodies on the
original execution route.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.MapAtomLowering

open Mettapedia.Languages.MeTTa
open OSLFCore (Atom)
open SubstitutionAlgebra (Subst subst vars)
open PeTTa.ValueOccurrences

universe u v w

variable {α : Type u} {β : Type v} {γ : Type w}

/-- An explicit mapper traversal. The partial output is a reversed prefix;
the continuation receives complete output lists, one per search branch. -/
def enumerate (callback : α → List β) :
    List α → List β → (List β → List γ) → List γ
  | [], reversed, next => next reversed.reverse
  | first :: rest, reversed, next =>
      (callback first).flatMap fun value => enumerate callback rest (value :: reversed) next

/-- General continuation correctness, including an existing output prefix. -/
theorem enumerate_correct (callback : α → List β) (items : List α)
    (reversed : List β) (next : List β → List γ) :
    enumerate callback items reversed next =
      (SuperposeFusion.mapAtom callback items).flatMap
        (fun suffix => next (reversed.reverse ++ suffix)) := by
  induction items generalizing reversed with
  | nil => simp [enumerate, SuperposeFusion.mapAtom]
  | cons first rest ih =>
      simp only [enumerate, SuperposeFusion.mapAtom, List.flatMap_assoc,
        List.flatMap_map, ih]
      congr 1
      funext value
      simp [List.reverse_cons, List.append_assoc]

/-- The reusable callback machine returns every combination in source order. -/
theorem enumerate_answers (callback : α → List β) (items : List α) :
    enumerate callback items [] (fun values => [values]) =
      SuperposeFusion.mapAtom callback items := by
  rw [enumerate_correct]
  simp

/-- A consumer may request any prefix of the complete finite trace. This is
an equality of traces, not yet a cost or early-cancellation theorem. -/
theorem enumerate_prefix (callback : α → List β) (items : List α) (count : Nat) :
    (enumerate callback items [] (fun values => [values])).take count =
      (SuperposeFusion.mapAtom callback items).take count := by
  rw [enumerate_answers]

/-- Snapshot table, including `none` for unbound source variables. -/
abbrev Captures := List (String × Option Atom)

def lookup : Captures → Subst
  | [], _ => none
  | (name, value) :: rest, query => if query = name then value else lookup rest query

def capture (environment : Subst) (names : List String) : Captures :=
  names.map fun name => (name, environment name)

theorem lookup_capture (environment : Subst) (names : List String) (name : String)
    (present : name ∈ names) :
    lookup (capture environment names) name = environment name := by
  induction names with
  | nil => simp at present
  | cons first rest ih =>
      by_cases same : name = first
      · simp [capture, lookup, same]
      · simp only [List.mem_cons] at present
        have inRest : name ∈ rest := present.resolve_left same
        simpa [capture, lookup, same] using ih inRest

/-- Source syntax and its compiled occurrence plan are retained once. The
table records captured values; it contains no per-element substituted body. -/
structure Callback where
  parameter : String
  body : Atom
  plan : Plan
  captures : Captures

def compile (environment : Subst) (parameter : String) (body : Atom) : Callback :=
  ⟨parameter, body, planOf body, capture environment (vars body)⟩

/-- The source evaluator reads a lexical argument in its environment. -/
def sourceCallback (program : Program) (environment : Subst)
    (parameter : String) (body argument : Atom) : List Atom :=
  evalIn program (bindAt environment parameter argument) body

/-- A compiled callback substitutes values under its retained source plan. -/
def invoke (program : Program) (callback : Callback) (argument : Atom) : List Atom :=
  evalPlanned program callback.plan
    (subst (bindAt (lookup callback.captures) callback.parameter argument) callback.body)

theorem invoke_compile (program : Program) (environment : Subst)
    (parameter : String) (body argument : Atom) :
    invoke program (compile environment parameter body) argument =
      sourceCallback program environment parameter body argument := by
  unfold invoke compile
  rw [evalPlanned_planOf_subst]
  apply evalIn_congr_on_vars
  intro name member
  by_cases same : name = parameter
  · simp [bindAt, same]
  · simp [bindAt, same, lookup_capture environment (vars body) name member]

/-- Store one compiled body and reuse it throughout the independent
continuation traversal. Capture lookup and variable occurrence preservation
are proved above, rather than postulated as callback equivalence. -/
theorem compiled_map_correct (program : Program) (environment : Subst)
    (parameter : String) (body : Atom) (items : List Atom) :
    enumerate (invoke program (compile environment parameter body)) items []
        (fun values => [values]) =
      SuperposeFusion.mapAtom (sourceCallback program environment parameter body) items := by
  rw [enumerate_answers]
  congr 1
  funext argument
  exact invoke_compile program environment parameter body argument

/-- A fresh local parameter is interchangeable with the original lexical
parameter. The callback's captured variables retain their old identities. -/
theorem invoke_open_fresh (program : Program) (environment : Subst)
    (parameter fresh : String) (body argument : Atom)
    (unused : fresh ∉ vars body) :
    invoke program (compile environment fresh (subst (renameTo parameter fresh) body))
        argument = sourceCallback program environment parameter body argument := by
  rw [invoke_compile]
  exact evalIn_open_fresh program environment parameter fresh argument body unused

namespace Controls

theorem ordered_product_with_duplicates :
    enumerate (fun n : Nat => [n, n, n + 10]) [1, 2] [] (fun values => [values]) =
      [[1, 2], [1, 2], [1, 12], [1, 2], [1, 2], [1, 12],
       [11, 2], [11, 2], [11, 12]] := by decide

theorem failure_discards_partial_output :
    enumerate (fun n : Nat => if n = 2 then [] else [n]) [1, 2] []
      (fun values => [values]) = [] := by decide

theorem truncating_each_mapper_is_wrong :
    enumerate (fun n : Nat => ([n, n + 10] : List Nat).take 1) [1, 2] []
        (fun values => [values]) ≠
      enumerate (fun n : Nat => [n, n + 10]) [1, 2] [] (fun values => [values]) := by
  decide

theorem callback_result_is_not_reexecuted :
    invoke Examples.callsSymbols
        (compile SubstitutionAlgebra.empty "x" Examples.wrapVariable)
        (.expression [.symbol "foo"]) =
      [.expression [.expression [.symbol "foo"]]] := by
  rw [invoke_compile]
  rfl

theorem captured_name_must_not_be_reused_as_parameter :
    sourceCallback Examples.callsSymbols
        (fun name => if name = "y" then some (.symbol "captured") else none)
        "x" (.expression [.var "x", .var "y"]) (.symbol "argument") ≠
      sourceCallback Examples.callsSymbols
        (fun name => if name = "y" then some (.symbol "captured") else none)
        "y" (.expression [.var "y", .var "y"]) (.symbol "argument") := by
  decide

end Controls

end Mettapedia.Machines.MapAtomLowering
