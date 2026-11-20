import Mettapedia.GSLT.Parsing.GeneratedPeTTaDataPatternMeaning
import Mettapedia.GSLT.Parsing.GeneratedPeTTaDataPatternLaws

/-!
# Exact meaning of the compiler's native constructor graph

Reading and instantiating the original template characterizes the entire
constructor graph, in both directions. The result uses the original Atom
carrier, arbitrary finite source trees, and the actual standard primitive.
It does not assert that the passive-pattern evaluator implements a computed
binding pattern, nor decide which open substitutions a runtime enumerates.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.GeneratedPeTTaDataPattern

open Algorithms.MeTTa.Simple.Parser (SExpr)
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.PeTTa.Effects (State)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)

theorem ConstructorGraph.leaf_iff (bindings : Subst) (before after : State)
    (token : String) (value : Atom) :
    ConstructorGraph bindings before (.atom token) after value ↔
      ∃ atom, SpaceSemantics.readToken token = .ok atom ∧
        after = before ∧ value = applySubst bindings atom := by
  constructor
  · intro graph
    cases graph with
    | leaf read => exact ⟨_, read, rfl, rfl⟩
  · rintro ⟨atom, read, rfl, rfl⟩
    exact .leaf read

theorem ConstructorGraph.empty_iff (bindings : Subst) (before after : State) (value : Atom) :
    ConstructorGraph bindings before (.list []) after value ↔
      after = before ∧ value = .expression [] := by
  constructor
  · intro graph
    cases graph
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact .empty _

theorem ConstructorGraph.cons_iff (bindings : Subst) (before after : State)
    (first rest : SExpr) (value : Atom) :
    ConstructorGraph bindings before (.list [.atom "cons-atom", first, rest]) after value ↔
      ∃ middle reached head tail,
        ConstructorGraph bindings before first middle head ∧
        ConstructorGraph bindings middle rest reached (.expression tail) ∧
        StdLib.apply reached "cons-atom" [head, .expression tail] = .ok (after, [value]) := by
  constructor
  · intro graph
    cases graph with
    | cons firstGraph restGraph primitive => exact ⟨_, _, _, _, firstGraph, restGraph, primitive⟩
  · rintro ⟨middle, reached, head, tail, firstGraph, restGraph, primitive⟩
    exact .cons firstGraph restGraph primitive

mutual
  theorem graph_encode_iff (bindings : Subst) (before after : State)
      (template : SExpr) (value : Atom) :
      ConstructorGraph bindings before (encode template) after value ↔
        ∃ atom, SpaceSemantics.readRawExpression template = .ok atom ∧
          after = before ∧ value = applySubst bindings atom := by
    cases template with
    | atom token =>
        simpa only [encode, SpaceSemantics.readRawExpression] using
          ConstructorGraph.leaf_iff bindings before after token value
    | list templates =>
        rw [encode, graph_encodeList_iff]
        cases read : SpaceSemantics.readRawExpressions templates with
        | error reason => simp [SpaceSemantics.readRawExpression, read]
        | ok atoms => simp [SpaceSemantics.readRawExpression, read, applySubst]
  termination_by sizeOf template

  theorem graph_encodeList_iff (bindings : Subst) (before after : State)
      (templates : List SExpr) (value : Atom) :
      ConstructorGraph bindings before (encodeList templates) after value ↔
        ∃ atoms, SpaceSemantics.readRawExpressions templates = .ok atoms ∧
          after = before ∧ value = .expression (applySubst.applySubstList bindings atoms) := by
    cases templates with
    | nil => simp [encodeList, ConstructorGraph.empty_iff, SpaceSemantics.readRawExpressions,
        applySubst.applySubstList]
    | cons first rest =>
        rw [encodeList, ConstructorGraph.cons_iff]
        simp only [graph_encode_iff (template := first),
          graph_encodeList_iff (templates := rest), StdLib.native_cons,
          Except.ok.injEq, Prod.mk.injEq, List.cons.injEq, and_true]
        cases firstRead : SpaceSemantics.readRawExpression first with
        | error reason => simp [SpaceSemantics.readRawExpressions, firstRead, bind, Except.bind]
        | ok atom =>
            cases restRead : SpaceSemantics.readRawExpressions rest with
            | error reason => simp [SpaceSemantics.readRawExpressions, firstRead, restRead, bind, Except.bind]
            | ok atoms =>
                simp [SpaceSemantics.readRawExpressions, firstRead, restRead,
                  bind, Except.bind, pure, Except.pure, applySubst.applySubstList, eq_comm]
  termination_by sizeOf templates
end

/-- A successful whole-tree syntax check gives exactly the standard native
constructor graph, not merely equality of operation names. -/
theorem checked_graph_iff (bindings : Subst) (before after : State)
    (template emitted : SExpr) (value : Atom) (checked : check template emitted = true) :
    ConstructorGraph bindings before emitted after value ↔
      ∃ atom, SpaceSemantics.readRawExpression template = .ok atom ∧
        after = before ∧ value = applySubst bindings atom := by
  rw [(check_iff template emitted).1 checked]
  exact graph_encode_iff bindings before after template value

theorem checked_graph_preserves_world {bindings : Subst} {before after : State}
    {template emitted : SExpr} {value : Atom} (checked : check template emitted = true)
    (graph : ConstructorGraph bindings before emitted after value) : after = before := by
  obtain ⟨_, _, pure, _⟩ := (checked_graph_iff bindings before after template emitted value checked).1 graph
  exact pure

theorem checked_graph_deterministic {bindings : Subst} {before firstAfter secondAfter : State}
    {template emitted : SExpr} {first second : Atom} (checked : check template emitted = true)
    (firstGraph : ConstructorGraph bindings before emitted firstAfter first)
    (secondGraph : ConstructorGraph bindings before emitted secondAfter second) :
    firstAfter = secondAfter ∧ first = second := by
  obtain ⟨firstAtom, firstRead, firstPure, firstValue⟩ :=
    (checked_graph_iff bindings before firstAfter template emitted first checked).1 firstGraph
  obtain ⟨secondAtom, secondRead, secondPure, secondValue⟩ :=
    (checked_graph_iff bindings before secondAfter template emitted second checked).1 secondGraph
  have same : firstAtom = secondAtom := Except.ok.inj (firstRead.symm.trans secondRead)
  exact ⟨firstPure.trans secondPure.symm, firstValue.trans (same ▸ secondValue.symm)⟩

#print axioms graph_encode_iff
#print axioms checked_graph_iff
#print axioms checked_graph_preserves_world
#print axioms checked_graph_deterministic

end Mettapedia.GSLT.Parsing.GeneratedPeTTaDataPattern
