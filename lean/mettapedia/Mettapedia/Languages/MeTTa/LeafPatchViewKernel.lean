import Mathlib.Data.List.Basic

/-!
# The leaf-patch view kernel

Semantic license for compiled equation views: for a LINEAR pattern (each
variable occurring exactly once), instantiating the pattern with an
assignment and then matching recovers exactly that assignment on the
pattern's variables — so a compiled view that reads argument leaves by
position and substitutes them into the body computes precisely what
match-then-substitute computes, and the matcher may be bypassed.

Contents, all proved:

* `matchP_complete_linear` / `view_eq_match`: matching an instantiated
  linear pattern succeeds and returns the induced environment — **the
  view-correctness core**.
* `nonlinear_counterexample`: a repeated-variable pattern where naive
  positional leaf reading accepts a term the matcher rejects — the
  linearity guard is load-bearing, not defensive.

Scope honesty: terms are binary-constructor first-order trees — enough
to carry the theorem shape; the engine's differential gates check the
implementation against richer syntax.  General matcher soundness (any
successful match is a substitution witness) is deliberately out of this
module's scope — it belongs with a functional-environment matcher
kernel.  Revision-correctness (a view is valid only at the equation set
it was compiled from) is a keying discipline outside this kernel: the
equation is a parameter here, which is exactly what revision-keying
provides.
-/

namespace Mettapedia.Languages.MeTTa.LeafPatchViewKernel

variable {σ : Type} [DecidableEq σ]

/-- First-order patterns: variables, symbols, binary nodes. -/
inductive Pat (σ : Type) where
  | var (n : Nat)
  | sym (s : σ)
  | node (l r : Pat σ)
deriving DecidableEq

/-- Ground terms: symbols and binary nodes. -/
inductive Tm (σ : Type) where
  | sym (s : σ)
  | node (l r : Tm σ)
deriving DecidableEq

/-- Total substitution of an assignment into a pattern. -/
def subst (ρ : Nat → Tm σ) : Pat σ → Tm σ
  | .var n => ρ n
  | .sym s => .sym s
  | .node l r => .node (subst ρ l) (subst ρ r)

/-- The variables of a pattern, in traversal order, with multiplicity. -/
def vars : Pat σ → List Nat
  | .var n => [n]
  | .sym _ => []
  | .node l r => vars l ++ vars r

/-- Linearity: no variable occurs twice. -/
def Linear (p : Pat σ) : Prop := (vars p).Nodup

/-- Environment lookup. -/
def lookup (e : List (Nat × Tm σ)) (n : Nat) : Option (Tm σ) :=
  (e.find? fun q => q.1 = n).map Prod.snd

/-- First-order matching with a consistency check on repeated variables:
extends the environment, refusing conflicting bindings. -/
def matchP : Pat σ → Tm σ → List (Nat × Tm σ) → Option (List (Nat × Tm σ))
  | .var n, t, e =>
    match lookup e n with
    | none => some ((n, t) :: e)
    | some t' => if t = t' then some e else none
  | .sym s, .sym s', e => if s = s' then some e else none
  | .sym _, .node _ _, _ => none
  | .node _ _, .sym _, _ => none
  | .node l r, .node tl tr, e =>
    match matchP l tl e with
    | none => none
    | some e' => matchP r tr e'

/-- The canonical environment an instantiation induces on a pattern's
variables (traversal order). -/
def envOf (ρ : Nat → Tm σ) (p : Pat σ) : List (Nat × Tm σ) :=
  (vars p).map fun n => (n, ρ n)

omit [DecidableEq σ] in
/-- A lookup misses an appended prefix whose keys all differ from `n`. -/
theorem lookup_append_none {pre e : List (Nat × Tm σ)} {n : Nat}
    (hpre : ∀ q ∈ pre, q.1 ≠ n) (he : lookup e n = none) :
    lookup (pre ++ e) n = none := by
  simp only [lookup, List.find?_append]
  cases hf : (pre.find? fun q => q.1 = n) with
  | some q =>
    exfalso
    have hkey : q.1 = n := by simpa using List.find?_some hf
    exact hpre q (List.mem_of_find?_eq_some hf) hkey
  | none =>
    simp only [Option.none_or]
    simpa [lookup] using he

/-- **Completeness on linear patterns**: matching an instantiated linear
pattern succeeds and yields exactly the induced environment (reversed,
prepended to the base).  This is the compiled view's license: the leaves
the view reads by position ARE the matcher's answer. -/
theorem matchP_complete_linear :
    ∀ (p : Pat σ) (ρ : Nat → Tm σ) (e : List (Nat × Tm σ)),
      Linear p → (∀ n ∈ vars p, lookup e n = none) →
      matchP p (subst ρ p) e = some ((envOf ρ p).reverse ++ e) := by
  intro p
  induction p with
  | var n =>
    intro ρ e _ hfresh
    simp [matchP, subst, envOf, vars, hfresh n (by simp [vars])]
  | sym s =>
    intro ρ e _ _
    simp [matchP, subst, envOf, vars]
  | node l r ihl ihr =>
    intro ρ e hlin hfresh
    have hsplit := List.nodup_append.mp (by simpa [Linear, vars] using hlin)
    have hlinl : Linear l := hsplit.1
    have hlinr : Linear r := hsplit.2.1
    have hdisj : ∀ n ∈ vars l, n ∉ vars r :=
      fun n hn hnr => hsplit.2.2 n hn n hnr rfl
    simp only [matchP, subst]
    rw [ihl ρ e hlinl fun n hn => hfresh n (by simp [vars, hn])]
    dsimp only
    rw [ihr ρ ((envOf ρ l).reverse ++ e) hlinr ?fresh]
    case fresh =>
      intro n hn
      refine lookup_append_none ?_ (hfresh n (by simp [vars, hn]))
      intro q hq
      simp only [envOf, List.mem_reverse, List.mem_map] at hq
      obtain ⟨m, hm, rfl⟩ := hq
      intro hqn
      have hmn : m = n := by simpa using hqn
      exact hdisj m hm (by rw [hmn]; exact hn)
    simp [envOf, vars, List.map_append, List.reverse_append,
          List.append_assoc]

/-- Equation views: for a linear pattern, matching the instantiated call
from an empty environment returns exactly the induced environment — the
compiled route (leaf reading + body substitution) and the matcher route
coincide. -/
theorem view_eq_match (p : Pat σ) (ρ : Nat → Tm σ) (hlin : Linear p) :
    matchP p (subst ρ p) [] = some ((envOf ρ p).reverse) := by
  simpa using matchP_complete_linear p ρ [] hlin (by simp [lookup])

/-- **Negative instance**: the non-linear pattern `(node (var 0) (var 0))`
rejects `(node a b)` for distinct symbols `a ≠ b` — while naive
positional leaf reading would accept it.  The linearity guard is
load-bearing. -/
theorem nonlinear_counterexample {a b : σ} (hab : a ≠ b) :
    matchP (Pat.node (.var 0) (.var 0))
      (Tm.node (.sym a) (.sym b)) [] = none := by
  simp [matchP, lookup]
  exact fun h => hab h.symm

end Mettapedia.Languages.MeTTa.LeafPatchViewKernel
