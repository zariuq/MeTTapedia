import Mettapedia.Languages.MeTTa.HE.SmallStep
import Mettapedia.Languages.MeTTa.HE.EvalSpec

/-!
# Context Transport Lemmas for the Master Absorption Theorem

Machinery for Theorem M's congruence case (see the design note
`docs/plans/2026-06-10_correspondence_master_theorem_design.txt` in the
CeTTa repository): transporting official derivations across the
replacement of a single element.

The hypothesis shape is exactly M's induction hypothesis: a
*result-preserving substitution* — every official evaluation of the
new element is an official evaluation of the old one, with the same
result pair.  Because the transported derivation keeps its exact result,
the T6 shape subtleties (singleton unwrap, tail splice) do not arise:
nothing here claims anything about the result's shape.

* `interpretTuple_swap` — tuple-path transport at any element position
  (including the head: in the tuple path the head is evaluated at
  `%Undefined%` like every other element).
* `interpretArgs_swap` — typed argument-list transport at any position
  (the hypothesis is type-generic, matching `InterpretArgs`' per-position
  expected types).

The remaining (genuinely hard) part of M's congruence case is the
*function-path head swap*, where path selection itself depends on the
head's declared types — analyzed but not provable by transport alone;
see the design note.  We state only what we prove.
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-- Tuple-path transport: if every official evaluation of `x'` (under
`%Undefined%`) is an official evaluation of `x` with the same result, then
any official tuple derivation of `(pre ++ x' :: post)` transports to
`(pre ++ x :: post)` with the identical result. -/
theorem interpretTuple_swap {space : Space} {d : GroundedDispatch}
    {x x' : Atom}
    (h_sub : ∀ (b' : Bindings) (r' : ResultPair),
      EvalAtom space d x' Atom.undefinedType b' r' →
      EvalAtom space d x Atom.undefinedType b' r') :
    ∀ (pre : List Atom) {post : List Atom} {b : Bindings} {r : ResultPair}
      {l : List Atom}, l = pre ++ x' :: post →
      InterpretTuple space d (.expression l) b r →
      InterpretTuple space d (.expression (pre ++ x :: post)) b r
  | [], post, b, r, l, h_eq, h => by
      cases h with
      | singleton a _ _ h_eval =>
          injection h_eq.symm with h1 h2
          cases h1; cases h2
          exact InterpretTuple.singleton x b r (h_sub b r h_eval)
      | head_error =>
          -- probed: h_ne : tl ≠ [], h_isErr : isEmptyOrError r.1 = true,
          --         h_ev : EvalAtom hd ⊤ b r
          rename_i hd tl h_ne h_isErr h_ev
          injection h_eq.symm with h1 h2
          cases h1; cases h2
          exact InterpretTuple.head_error x post b r h_ne
            (h_sub b r h_ev) h_isErr
      | tail_error =>
          -- probed: hr; h_ne : tl ≠ []; h_hok : isEmptyOrError hr.1 = false;
          --         h_ev : EvalAtom hd ⊤ b hr; h_tail : InterpretTuple tl hr.2 r;
          --         h_terr : isEmptyOrError r.1 = true
          rename_i hd tl hr h_ne h_hok h_ev h_tail h_terr
          injection h_eq.symm with h1 h2
          cases h1; cases h2
          exact InterpretTuple.tail_error x post b hr r h_ne
            (h_sub b hr h_ev) h_hok h_tail h_terr
      | success =>
          -- probed: hr tr; h_ne : tl ≠ []; h_hok : isEmptyOrError hr.1 = false;
          --         h_tl : InterpretTuple tl hr.2 tr; h_tok : isEmptyOrError tr.1 = false;
          --         h_ev : EvalAtom hd ⊤ b hr
          rename_i hd tl hr tr h_ne h_hok h_tl h_tok h_ev
          injection h_eq.symm with h1 h2
          cases h1; cases h2
          exact InterpretTuple.success x post b hr tr h_ne
            (h_sub b hr h_ev) h_hok h_tl h_tok
  | p :: ps, post, b, r, l, h_eq, h => by
      cases h with
      | singleton a _ _ h_eval =>
          exfalso
          injection h_eq.symm with h1 h2
          exact absurd h2.symm (by simp)
      | head_error =>
          rename_i hd tl h_ne h_isErr h_ev
          injection h_eq.symm with h1 h2
          cases h1; cases h2
          exact InterpretTuple.head_error p (ps ++ x :: post) b r
            (by simp) h_ev h_isErr
      | tail_error =>
          rename_i hd tl hr h_ne h_hok h_ev h_tail h_terr
          injection h_eq.symm with h1 h2
          cases h1; cases h2
          exact InterpretTuple.tail_error p (ps ++ x :: post) b hr r
            (by simp) h_ev h_hok
            (interpretTuple_swap h_sub ps rfl h_tail) h_terr
      | success =>
          rename_i hd tl hr tr h_ne h_hok h_tl h_tok h_ev
          injection h_eq.symm with h1 h2
          cases h1; cases h2
          exact InterpretTuple.success p (ps ++ x :: post) b hr tr
            (by simp) h_ev h_hok
            (interpretTuple_swap h_sub ps rfl h_tl) h_tok

/-- Typed argument-list transport: with a type-generic result-preserving
substitution for one argument position, any official `InterpretArgs`
derivation transports across the replacement with the identical result.
The expected-type lists are arbitrary and untouched: each position keeps
its own expected type, exactly as `InterpretArgs` threads them.

Side conditions: both atoms must be non-Empty/Error-shaped — without
them transport genuinely fails (an unchanged-error argument officially
*continues* to the tail, while the same result against a different
argument would *stop* as a changed error; discovered designing this
lemma — recorded as trap T8). -/
theorem interpretArgs_swap {space : Space} {d : GroundedDispatch}
    {x x' : Atom}
    (h_x : isEmptyOrError x = false)
    (h_x' : isEmptyOrError x' = false)
    (h_sub : ∀ (t : Atom) (b' : Bindings) (r' : ResultPair),
      EvalAtom space d x' t b' r' → EvalAtom space d x t b' r') :
    ∀ (pre : List Atom) {post : List Atom} {types : List Atom}
      {b : Bindings} {r : ResultPair},
      InterpretArgs space d (pre ++ x' :: post) types b r →
      InterpretArgs space d (pre ++ x :: post) types b r
  | [], post, types, b, r, h => by
      cases h with
      | head_changed_error _ _ t ts _ _ h_head h_err h_changed =>
          refine InterpretArgs.head_changed_error x post t ts b _
            (h_sub t b _ h_head) h_err ?_
          -- result is Empty/Error-shaped; x is not, so they differ
          intro hcontra
          rw [hcontra] at h_err
          rw [h_err] at h_x
          cases h_x
      | cons_tail_error _ _ t ts _ _ _ h_head h_head_ok h_tail h_terr =>
          refine InterpretArgs.cons_tail_error x post t ts b _ _
            (h_sub t b _ h_head) (Or.inl ?_) h_tail h_terr
          rcases h_head_ok with h | h
          · exact h
          · rw [h]; exact h_x'
      | cons_ok _ _ t ts _ _ _ h_head h_head_ok h_tail h_tok =>
          refine InterpretArgs.cons_ok x post t ts b _ _
            (h_sub t b _ h_head) (Or.inl ?_) h_tail h_tok
          rcases h_head_ok with h | h
          · exact h
          · rw [h]; exact h_x'
  | p :: ps, post, types, b, r, h => by
      cases h with
      | head_changed_error _ _ t ts _ _ h_head h_err h_changed =>
          exact InterpretArgs.head_changed_error p (ps ++ x :: post) t ts b _
            h_head h_err h_changed
      | cons_tail_error _ _ t ts _ _ _ h_head h_head_ok h_tail h_terr =>
          exact InterpretArgs.cons_tail_error p (ps ++ x :: post) t ts b _ _
            h_head h_head_ok (interpretArgs_swap h_x h_x' h_sub ps h_tail) h_terr
      | cons_ok _ _ t ts _ _ _ h_head h_head_ok h_tail h_tok =>
          exact InterpretArgs.cons_ok p (ps ++ x :: post) t ts b _ _
            h_head h_head_ok (interpretArgs_swap h_x h_x' h_sub ps h_tail) h_tok

/-- Tuple-path `InterpretExpression` transport at non-head positions: with
the head untouched, the tuple-path side conditions (the head's non-function
type witness) transfer verbatim, the tuple derivation transports by
`interpretTuple_swap`, and the final `MettaCall` is reused as-is (it runs
on the evaluated tuple result, which transport keeps identical). -/
theorem interpretExpression_swap_tuple_path
    {space : Space} {d : GroundedDispatch} {x x' : Atom}
    (h_sub : ∀ (b' : Bindings) (r' : ResultPair),
      EvalAtom space d x' Atom.undefinedType b' r' →
      EvalAtom space d x Atom.undefinedType b' r')
    (p : Atom) (ps : List Atom) {post : List Atom}
    {type_ : Atom} {b : Bindings} {tupleResult callResult : ResultPair}
    (h_has : ∃ t ∈ getAtomTypes space p,
      isFunctionType t = false ∨ t = Atom.undefinedType)
    (h_tuple : InterpretTuple space d
      (.expression (p :: ps ++ x' :: post)) b tupleResult)
    (h_call : MettaCall space d tupleResult.1 type_ tupleResult.2 callResult) :
    InterpretExpression space d (.expression (p :: ps ++ x :: post))
      type_ b callResult :=
  InterpretExpression.tuple_path _ _ _ tupleResult callResult
    (by simpa using h_has)
    (interpretTuple_swap h_sub (p :: ps) rfl h_tuple)
    h_call

/-- `EvalAtom` transport for tuple-path `interpret_success` derivations at
non-head positions.  All `interpret_success` side conditions about the
source transfer from the successor's (same head, same expected type, both
proper expressions); the interpretation transports; the success-filter
condition is about the (identical) result. -/
theorem evalAtom_swap_tuple_path
    {space : Space} {d : GroundedDispatch} {x x' : Atom}
    (h_sub : ∀ (b' : Bindings) (r' : ResultPair),
      EvalAtom space d x' Atom.undefinedType b' r' →
      EvalAtom space d x Atom.undefinedType b' r')
    (p : Atom) (ps : List Atom) {post : List Atom}
    {type_ : Atom} {b : Bindings} {tupleResult r : ResultPair}
    (h_not_err : isEmptyOrError (.expression (p :: ps ++ x :: post)) = false)
    (h_not_pass : ¬(type_ = Atom.atomType
      ∨ type_ = getMetaType (Atom.expression (p :: ps ++ x :: post))
      ∨ getMetaType (Atom.expression (p :: ps ++ x :: post))
          = Atom.variableType))
    (h_has : ∃ t ∈ getAtomTypes space p,
      isFunctionType t = false ∨ t = Atom.undefinedType)
    (h_tuple : InterpretTuple space d
      (.expression (p :: ps ++ x' :: post)) b tupleResult)
    (h_call : MettaCall space d tupleResult.1 type_ tupleResult.2 r)
    (h_not_error : isErrorAtom r.1 = false) :
    EvalAtom space d (.expression (p :: ps ++ x :: post)) type_ b r :=
  EvalAtom.interpret_success _ _ _ _
    h_not_err
    h_not_pass
    rfl
    (by intro h_unit; simp [Atom.unit] at h_unit)
    (interpretExpression_swap_tuple_path h_sub p ps h_has h_tuple h_call)
    h_not_error

/-- Ground atoms: no variables anywhere.  The substrate for the
bindings-irrelevance induction (design-note T10): on ground atoms,
official result *atoms* are independent of the incoming bindings
thread, which is what lets the master absorption theorem be stated on
result atoms across equation steps in element position. -/
inductive GroundAtom : Atom → Prop where
  | symbol (s : String) : GroundAtom (.symbol s)
  | grounded (g : GroundedValue) : GroundAtom (.grounded g)
  | expression {es : List Atom} (h : ∀ e ∈ es, GroundAtom e) :
      GroundAtom (.expression es)

theorem GroundAtom.not_var {v : String} : ¬ GroundAtom (.var v) := by
  rintro ⟨⟩

theorem GroundAtom.elem {es : List Atom} {e : Atom}
    (h : GroundAtom (.expression es)) (h_mem : e ∈ es) : GroundAtom e := by
  cases h with
  | expression h_elems => exact h_elems e h_mem

/-- Positive and negative examples. -/
example : GroundAtom (.expression [.symbol "f", .grounded (.int 5)]) :=
  .expression (by
    intro e he
    rcases List.mem_cons.mp he with rfl | he'
    · exact .symbol _
    rcases List.mem_cons.mp he' with rfl | he''
    · exact .grounded _
    · cases he'')

example : ¬ GroundAtom (.expression [.symbol "f", .var "x"]) := by
  intro h
  exact GroundAtom.not_var (v := "x") (h.elem (by simp))

end Mettapedia.Languages.MeTTa.HE
