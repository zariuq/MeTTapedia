import Mettapedia.GSLT.Core.GSLT
import Mettapedia.GSLT.Core.NonFactorization
import Mathlib.Data.List.Perm.Basic

/-!
# Multi-argument rewrite theories (ordered / pre-net rung)

Kernel `GSLT` remains a triple `(T, E, R)` with `R : Term → Term → Prop`.
That is the credo: one state, one successor.

A *multi-rewrite theory* is the authored enrichment: a relation on **lists**
of terms.  That is the ordered rung (pre-nets: Bruni–Meseguer–Montanari–Sassone).
Windows see argument order.  `[out, inp]` is not `[inp, out]`.

Unary GSLT rewrites embed as singleton lists.  Compilation is document
closure: one kernel step replaces a consecutive window.

Proof relevance lives on `WindowWitness` (which rule-window fired).
`GSLT.Step` is still a `Prop`; it is `Nonempty` of that witness.  Cost,
rates, and OSLF rely need the witness, not the erased step.

The symmetric property and the commutative collapse (Petri / rho soups)
live in `MultiRewrite.Comm`.  They are not a second kernel GSLT.

This module does not change `GSLT` and does not import LanguageDef.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.MultiRewrite

open Mettapedia.GSLT
open Mettapedia.GSLT.Core.NonFactorization

universe u

/-- Pointwise lifting of a relation to lists of equal length. -/
inductive Pointwise {α : Type u} (r : α → α → Prop) :
    List α → List α → Prop where
  | nil : Pointwise r [] []
  | cons {a b : α} {as bs : List α} :
      r a b → Pointwise r as bs → Pointwise r (a :: as) (b :: bs)

namespace Pointwise

variable {α : Type u} {r : α → α → Prop}

theorem refl (hrefl : ∀ a, r a a) : ∀ xs, Pointwise r xs xs
  | [] => .nil
  | x :: xs => .cons (hrefl x) (refl hrefl xs)

theorem symm (hsymm : ∀ {a b}, r a b → r b a)
    {xs ys : List α} (h : Pointwise r xs ys) : Pointwise r ys xs := by
  induction h with
  | nil => exact .nil
  | cons head tail ih => exact .cons (hsymm head) ih

theorem trans (htrans : ∀ {a b c}, r a b → r b c → r a c)
    {xs ys zs : List α} (hxy : Pointwise r xs ys) (hyz : Pointwise r ys zs) :
    Pointwise r xs zs := by
  induction hxy generalizing zs with
  | nil =>
      cases hyz
      exact .nil
  | cons head tail ih =>
      cases hyz with
      | cons head' tail' => exact .cons (htrans head head') (ih tail')

theorem length {xs ys : List α} (h : Pointwise r xs ys) :
    xs.length = ys.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem append {xs xs' ys ys' : List α}
    (hx : Pointwise r xs xs') (hy : Pointwise r ys ys') :
    Pointwise r (xs ++ ys) (xs' ++ ys') := by
  induction hx with
  | nil => exact hy
  | cons head _ ih => exact .cons head ih

theorem split_append {xs ys zs : List α} (h : Pointwise r (xs ++ ys) zs) :
    ∃ zs₁ zs₂, zs = zs₁ ++ zs₂ ∧ Pointwise r xs zs₁ ∧ Pointwise r ys zs₂ := by
  induction xs generalizing zs with
  | nil => exact ⟨[], zs, rfl, .nil, h⟩
  | cons x xs ih =>
      cases h with
      | cons head tail =>
          obtain ⟨zs₁, zs₂, hzs, hxs, hys⟩ := ih tail
          exact ⟨_ :: zs₁, zs₂, by simp [hzs], .cons head hxs, hys⟩

theorem eq_of_eq {xs ys : List α} (h : Pointwise (@Eq α) xs ys) : xs = ys := by
  induction h with
  | nil => rfl
  | cons head _ ih => exact congrArg₂ List.cons head ih

theorem of_eq {xs ys : List α} (h : xs = ys) : Pointwise (@Eq α) xs ys := by
  subst h
  exact Pointwise.refl (fun _ => rfl) xs

end Pointwise

/-- An authored rewrite theory whose rules may consume and produce any
finite number of terms.  Not a `GSLT`. -/
structure MultiRewriteTheory where
  Term : Type u
  equations : Setoid Term
  rewrites : List Term → List Term → Prop
  rewrites_resp_left :
    ∀ {sources sources' targets},
      Pointwise equations.r sources sources' →
        rewrites sources targets →
          ∃ targets', rewrites sources' targets' ∧
            Pointwise equations.r targets targets'
  rewrites_resp_right :
    ∀ {sources targets targets'},
      rewrites sources targets →
        Pointwise equations.r targets targets' →
          rewrites sources targets'

namespace MultiRewriteTheory

/-- Witness of one document-window rewrite. -/
structure WindowWitness (M : MultiRewriteTheory)
    (source target : List M.Term) where
  pre : List M.Term
  sources : List M.Term
  targets : List M.Term
  suf : List M.Term
  source_eq : Pointwise M.equations.r source (pre ++ sources ++ suf)
  target_eq : Pointwise M.equations.r (pre ++ targets ++ suf) target
  rule : M.rewrites sources targets
  real : sources ≠ [] ∨ targets ≠ []

/-- A kernel step is the existence of a window witness. -/
def WindowStep (M : MultiRewriteTheory) (source target : List M.Term) : Prop :=
  Nonempty (WindowWitness M source target)

private theorem pointwise_trans {α : Type u} (s : Setoid α)
    {xs ys zs : List α}
    (hxy : Pointwise s.r xs ys) (hyz : Pointwise s.r ys zs) :
    Pointwise s.r xs zs :=
  Pointwise.trans (r := s.r)
    (fun {a b c} (hab : s.r a b) (hbc : s.r b c) => s.trans hab hbc) hxy hyz

private theorem pointwise_symm {α : Type u} (s : Setoid α)
    {xs ys : List α} (h : Pointwise s.r xs ys) : Pointwise s.r ys xs :=
  Pointwise.symm (r := s.r) (fun {a b} (h' : s.r a b) => s.symm h') h

/-- Document closure: the GSLT a multi-rewrite theory denotes. -/
def toGSLT (M : MultiRewriteTheory) : GSLT where
  Term := List M.Term
  equations :=
    { r := Pointwise M.equations.r
      iseqv :=
        { refl := Pointwise.refl M.equations.refl
          symm := fun h => pointwise_symm M.equations h
          trans := fun h₁ h₂ => pointwise_trans M.equations h₁ h₂ } }
  rewrites := WindowStep M
  rewrites_resp_left := by
    intro source source' target sourceEq ⟨w⟩
    refine ⟨target, ?_, Pointwise.refl M.equations.refl target⟩
    exact Nonempty.intro
      (WindowWitness.mk w.pre w.sources w.targets w.suf
        (pointwise_trans M.equations (pointwise_symm M.equations sourceEq)
          w.source_eq)
        w.target_eq w.rule w.real)
  rewrites_resp_right := by
    intro source target target' ⟨w⟩ targetEq
    exact Nonempty.intro
      (WindowWitness.mk w.pre w.sources w.targets w.suf w.source_eq
        (pointwise_trans M.equations w.target_eq targetEq) w.rule w.real)

theorem step_of_unary (M : MultiRewriteTheory) {x y : M.Term}
    (h : M.rewrites [x] [y]) :
    GSLT.Step (toGSLT M) [x] [y] :=
  Nonempty.intro
    { pre := []
      sources := [x]
      targets := [y]
      suf := []
      source_eq := Pointwise.refl M.equations.refl [x]
      target_eq := Pointwise.refl M.equations.refl [y]
      rule := h
      real := Or.inl (List.cons_ne_nil _ _) }

theorem step_of_binary (M : MultiRewriteTheory) {a b c : M.Term}
    (h : M.rewrites [a, b] [c]) :
    GSLT.Step (toGSLT M) [a, b] [c] :=
  Nonempty.intro
    { pre := []
      sources := [a, b]
      targets := [c]
      suf := []
      source_eq := Pointwise.refl M.equations.refl [a, b]
      target_eq := Pointwise.refl M.equations.refl [c]
      rule := h
      real := Or.inl (List.cons_ne_nil _ _) }

theorem step_of_binary_in_context (M : MultiRewriteTheory) {a b c : M.Term}
    (pre suf : List M.Term) (h : M.rewrites [a, b] [c]) :
    GSLT.Step (toGSLT M) (pre ++ [a, b] ++ suf) (pre ++ [c] ++ suf) :=
  Nonempty.intro
    { pre := pre
      sources := [a, b]
      targets := [c]
      suf := suf
      source_eq := Pointwise.refl M.equations.refl (pre ++ [a, b] ++ suf)
      target_eq := Pointwise.refl M.equations.refl (pre ++ [c] ++ suf)
      rule := h
      real := Or.inl (List.cons_ne_nil _ _) }

/-- A rule whose window is the whole document. Persistent kernels (keep
every previously derived term) are this shape. -/
def wholeWindow (M : MultiRewriteTheory)
    {sources targets : List M.Term} (h : M.rewrites sources targets)
    (real : sources ≠ [] ∨ targets ≠ []) :
    WindowWitness M sources targets where
  pre := []
  sources := sources
  targets := targets
  suf := []
  source_eq := by
    simpa [List.nil_append, List.append_nil] using
      Pointwise.refl M.equations.refl sources
  target_eq := by
    simpa [List.nil_append, List.append_nil] using
      Pointwise.refl M.equations.refl targets
  rule := h
  real := real

theorem step_of_whole (M : MultiRewriteTheory)
    {sources targets : List M.Term} (h : M.rewrites sources targets)
    (real : sources ≠ [] ∨ targets ≠ []) :
    GSLT.Step (toGSLT M) sources targets :=
  Nonempty.intro (wholeWindow M h real)

end MultiRewriteTheory

/-- Embed a kernel GSLT as the unary fragment of a multi-rewrite theory. -/
def ofUnary (S : GSLT) : MultiRewriteTheory where
  Term := S.Term
  equations := S.equations
  rewrites := fun sources targets =>
    ∃ x y, sources = [x] ∧ targets = [y] ∧ S.Step x y
  rewrites_resp_left := by
    intro sources sources' targets equiv ⟨x, y, hs, ht, step⟩
    subst hs
    subst ht
    cases equiv with
    | cons head tail =>
        cases tail
        obtain ⟨y', step', yEq⟩ := S.rewrites_resp_left head step
        exact ⟨[y'], ⟨_, y', rfl, rfl, step'⟩, .cons yEq .nil⟩
  rewrites_resp_right := by
    intro sources targets targets' ⟨x, y, hs, ht, step⟩ equiv
    subst hs
    subst ht
    cases equiv with
    | cons head tail =>
        cases tail
        exact ⟨x, _, rfl, rfl, S.rewrites_resp_right step head⟩

theorem ofUnary_only_singletons {S : GSLT} {xs ys : List S.Term}
    (h : (ofUnary S).rewrites xs ys) : xs.length = 1 ∧ ys.length = 1 := by
  obtain ⟨_, _, hs, ht, _⟩ := h
  subst hs
  subst ht
  exact ⟨rfl, rfl⟩

theorem ofUnary_step {S : GSLT} {x y : S.Term} :
    (ofUnary S).rewrites [x] [y] ↔ S.Step x y := by
  constructor
  · rintro ⟨x', y', hx, hy, step⟩
    cases hx
    cases hy
    exact step
  · intro step
    exact ⟨x, y, rfl, rfl, step⟩

theorem ofUnary_toGSLT_step {S : GSLT} {x y : S.Term}
    (h : S.Step x y) :
    GSLT.Step (MultiRewriteTheory.toGSLT (ofUnary S)) [x] [y] :=
  MultiRewriteTheory.step_of_unary (ofUnary S) (ofUnary_step.mpr h)

/-! ## Canary: binary interaction is extra data -/

def silent : MultiRewriteTheory where
  Term := Bool
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun _ _ => False
  rewrites_resp_left := by
    intro _ _ _ _ h
    exact h.elim
  rewrites_resp_right := by
    intro _ _ _ h _
    exact h.elim

def meet : MultiRewriteTheory where
  Term := Bool
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := fun sources targets =>
    sources = [false, true] ∧ targets = [true]
  rewrites_resp_left := by
    intro sources sources' targets equiv ⟨hs, ht⟩
    subst hs
    subst ht
    have : sources' = [false, true] := (Pointwise.eq_of_eq equiv).symm
    exact ⟨[true], ⟨this, rfl⟩, Pointwise.of_eq rfl⟩
  rewrites_resp_right := by
    intro sources targets targets' ⟨hs, ht⟩ equiv
    subst hs
    subst ht
    exact ⟨rfl, (Pointwise.eq_of_eq equiv).symm⟩

theorem meet_fires : meet.rewrites [false, true] [true] :=
  ⟨rfl, rfl⟩

theorem meet_not_unary (x y : Bool) : ¬ meet.rewrites [x] [y] := by
  intro h
  obtain ⟨hs, _⟩ := h
  cases hs

/-- A binary rule is never in the image of `ofUnary`. -/
theorem ofUnary_misses_binary {S : GSLT} {a b c : S.Term} :
    ¬ (ofUnary S).rewrites [a, b] [c] := by
  intro h
  have : (2 : Nat) = 1 := (ofUnary_only_singletons h).1
  omega

theorem meet_compiles :
    GSLT.Step (MultiRewriteTheory.toGSLT meet) [false, true] [true] :=
  MultiRewriteTheory.step_of_binary meet meet_fires

/-- Restricting a multi-rewrite to unary windows forgets interaction.
Two relations can agree on every 1→1 window and disagree on a 2→1 window. -/
def unaryRestrictionMissesMeet :
    NonTrivialFiber
      (fun r : List Bool → List Bool → Prop => fun x y : Bool => r [x] [y])
      (fun r => r [false, true] [true]) where
  left := fun _ _ => False
  right := fun xs ys => xs = [false, true] ∧ ys = [true]
  sameShadow := by
    funext x y
    simp
  differentValue := fun h =>
    (eq_iff_iff.mp h).mpr ⟨rfl, rfl⟩

theorem unary_restriction_does_not_factor :
    ¬ Factors
      (fun r : List Bool → List Bool → Prop => fun x y : Bool => r [x] [y])
      (fun r => r [false, true] [true]) :=
  unaryRestrictionMissesMeet.not_factors

/-! ## Symmetry is a property of the ordered theory

A theory is symmetric when permuting the source window still yields a
(possibly permuted) target.  That is the Σ-net / individual-token reading:
tokens keep identity, order of the window does not matter.  It is not a
new carrier. -/

/-- Rules cannot see the order of their arguments. -/
def Symmetric (M : MultiRewriteTheory) : Prop :=
  ∀ {sources sources' targets : List M.Term},
    sources.Perm sources' → M.rewrites sources targets →
      ∃ targets', targets.Perm targets' ∧ M.rewrites sources' targets'

/-- The ordered `meet` window is not symmetric: `[false, true]` fires and
`[true, false]` does not. -/
theorem meet_not_symmetric : ¬ Symmetric meet := by
  intro h
  obtain ⟨targets', hperm, hrule⟩ :=
    h (List.Perm.swap true false []) meet_fires
  have ht : targets' = [true] := List.perm_singleton.mp hperm.symm
  subst ht
  cases hrule.1

/-- Term equations that are discrete equality.  Needed to close rewrites
under permutation without mixing Setoid transport with `List.Perm`. -/
def DiscreteEq (M : MultiRewriteTheory) : Prop :=
  ∀ a b : M.Term, M.equations.r a b ↔ a = b

theorem meet_discrete : DiscreteEq meet := fun _ _ => Iff.rfl

theorem Pointwise.eq_iff_of_discrete {M : MultiRewriteTheory}
    (hE : DiscreteEq M) {xs ys : List M.Term} :
    Pointwise M.equations.r xs ys ↔ xs = ys := by
  constructor
  · intro h
    induction h with
    | nil => rfl
    | cons head tail ih =>
        have : _ = _ := (hE _ _).mp head
        exact congrArg₂ List.cons this ih
  · intro h
    subst h
    exact Pointwise.refl (fun a => (hE a a).mpr rfl) xs

/-- Least symmetric extension: close the rewrite relation under permuting
sources and targets.  Discrete equations keep response laws on the nose. -/
def symmetrize (M : MultiRewriteTheory) (hE : DiscreteEq M) :
    MultiRewriteTheory where
  Term := M.Term
  equations := M.equations
  rewrites := fun sources targets =>
    ∃ sources' targets',
      sources.Perm sources' ∧ targets.Perm targets' ∧
        M.rewrites sources' targets'
  rewrites_resp_left := by
    intro sources sources' targets heq ⟨s0, t0, hp, hq, hr⟩
    have hs : sources = sources' :=
      ((Pointwise.eq_iff_of_discrete hE).mp heq)
    subst hs
    exact ⟨targets, ⟨s0, t0, hp, hq, hr⟩,
      (Pointwise.eq_iff_of_discrete hE).mpr rfl⟩
  rewrites_resp_right := by
    intro sources targets targets' ⟨s0, t0, hp, hq, hr⟩ heq
    have ht : targets = targets' :=
      ((Pointwise.eq_iff_of_discrete hE).mp heq)
    subst ht
    exact ⟨s0, t0, hp, hq, hr⟩

theorem symmetrize_symmetric (M : MultiRewriteTheory) (hE : DiscreteEq M) :
    Symmetric (symmetrize M hE) := by
  intro sources sources' targets hperm ⟨s0, t0, hp, hq, hr⟩
  refine ⟨targets, List.Perm.refl _, ?_⟩
  exact ⟨s0, t0, hperm.symm.trans hp, hq, hr⟩

theorem symmetrize_meet_fires_swapped :
    (symmetrize meet meet_discrete).rewrites [true, false] [true] :=
  ⟨[false, true], [true],
    List.Perm.swap false true [], List.Perm.refl _, meet_fires⟩

/-- A rewrite that consumes at least one source.  Creation from nothing
(`[] → [t]`) is a different kind; the net literature treats it separately. -/
def Consuming (M : MultiRewriteTheory) : Prop :=
  ∀ {sources targets}, M.rewrites sources targets → sources ≠ []

def Creates (M : MultiRewriteTheory) : Prop :=
  ∃ targets, targets ≠ [] ∧ M.rewrites [] targets

theorem meet_consuming : Consuming meet := by
  intro sources targets h hempty
  subst hempty
  cases h.1

theorem meet_does_not_create : ¬ Creates meet := by
  rintro ⟨targets, hne, h⟩
  exact List.cons_ne_nil false [true] h.1.symm

#print axioms ofUnary_only_singletons
#print axioms ofUnary_toGSLT_step
#print axioms meet_compiles
#print axioms ofUnary_misses_binary
#print axioms unary_restriction_does_not_factor
#print axioms meet_not_symmetric
#print axioms symmetrize_symmetric
#print axioms symmetrize_meet_fires_swapped
#print axioms meet_consuming
#print axioms meet_does_not_create

end Mettapedia.GSLT.MultiRewrite
