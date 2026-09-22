import Mettapedia.GSLT.Core.MultiRewrite

/-!
# Commutative collapse of multi-rewrite theories

The ordered theory is a pre-net: windows are lists.  Symmetry is a
*property* of that theory (individual tokens, order irrelevant).  The
commutative rung is not a third unrelated carrier.  It is the collapse
that identifies states up to `List.Perm` (Mathlib's `Multiset` is that
quotient).  That is Meseguer–Montanari's "Petri nets are monoids" at the
level of one GSLT.

At reachability this is the bag-plus-rest idiom already in
`PetriNetInstance` and rho `PPar`.  What the collapse adds is the theorem
that the soup is the quotient of the ordered window, and the negative:
order-sensitive readouts do not survive it.

Kernel `GSLT` remains 1→1, now with permutation as the equations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.MultiRewrite.Comm

open Mettapedia.GSLT
open Mettapedia.GSLT.MultiRewrite
open Mettapedia.GSLT.Core.NonFactorization

universe u

/-- Collective-token multi-rewrites: argument order is not observable. -/
structure CommRewriteTheory where
  Term : Type u
  rewrites : List Term → List Term → Prop
  resp_perm :
    ∀ {sources sources' targets targets' : List Term},
      sources.Perm sources' → targets.Perm targets' →
        rewrites sources targets → rewrites sources' targets'

namespace CommRewriteTheory

/-- One reaction in a soup: consume a nonempty window, produce a window,
leave a context; the whole state is identified up to permutation. -/
def WindowStep (M : CommRewriteTheory) (source target : List M.Term) : Prop :=
  ∃ (w w' ctx : List M.Term),
    M.rewrites w w' ∧ source.Perm (w ++ ctx) ∧ target.Perm (w' ++ ctx) ∧
      w ≠ []

def toGSLT (M : CommRewriteTheory) : GSLT where
  Term := List M.Term
  equations :=
    ⟨List.Perm, ⟨List.Perm.refl, List.Perm.symm, List.Perm.trans⟩⟩
  rewrites := WindowStep M
  rewrites_resp_left := by
    intro source source' target hEq ⟨w, w', ctx, hr, hs, ht, hne⟩
    refine ⟨target, ?_, List.Perm.refl _⟩
    exact ⟨w, w', ctx, hr, hEq.symm.trans hs, ht, hne⟩
  rewrites_resp_right := by
    intro source target target' ⟨w, w', ctx, hr, hs, ht, hne⟩ hEq
    exact ⟨w, w', ctx, hr, hs, hEq.symm.trans ht, hne⟩

theorem step_of_reaction (M : CommRewriteTheory)
    {w w' : List M.Term} (h : M.rewrites w w') (hne : w ≠ []) :
    GSLT.Step (toGSLT M) w w' :=
  ⟨w, w', [], h, by simp [List.append_nil], by simp [List.append_nil], hne⟩

end CommRewriteTheory

/-- Collapse an ordered theory: a bag-window fires iff some linearization
of that bag fires in the ordered theory. -/
def toComm (M : MultiRewriteTheory) : CommRewriteTheory where
  Term := M.Term
  rewrites := fun sources targets =>
    ∃ sources' targets',
      sources.Perm sources' ∧ targets.Perm targets' ∧
        sources' ≠ [] ∧ M.rewrites sources' targets'
  resp_perm := by
    intro s s' t t' hs ht ⟨s0, t0, hp, hq, hne, hr⟩
    exact ⟨s0, t0, hs.symm.trans hp, ht.symm.trans hq, hne, hr⟩

/-- `meet` refuses the swapped *list*, but the collapsed soup still fires. -/
theorem toComm_meet_ignores_order :
    (toComm meet).rewrites [true, false] [true] :=
  ⟨[false, true], [true], List.Perm.swap false true [], List.Perm.refl _,
    List.cons_ne_nil _ _, meet_fires⟩

theorem toComm_meet_step :
    GSLT.Step (CommRewriteTheory.toGSLT (toComm meet))
      [true, false] [true] :=
  CommRewriteTheory.step_of_reaction (toComm meet)
    toComm_meet_ignores_order (List.cons_ne_nil _ _)

/-- The ordered theory still refuses the swapped window. -/
theorem ordered_meet_refuses_swap :
    ¬ meet.rewrites [true, false] [true] := by
  intro h
  cases h.1

/-- The collapse canary: permutation of a firing window is not an
ordered rewrite, and is a commutative rewrite. -/
theorem collapse_is_strict :
    ¬ meet.rewrites [true, false] [true] ∧
      (toComm meet).rewrites [true, false] [true] :=
  ⟨ordered_meet_refuses_swap, toComm_meet_ignores_order⟩

theorem symmetrize_collapses_to_same_bag :
    (toComm (symmetrize meet meet_discrete)).rewrites [true, false] [true] :=
  ⟨[true, false], [true], List.Perm.refl _, List.Perm.refl _,
    List.cons_ne_nil _ _, symmetrize_meet_fires_swapped⟩

#print axioms toComm_meet_ignores_order
#print axioms toComm_meet_step
#print axioms ordered_meet_refuses_swap
#print axioms collapse_is_strict
#print axioms symmetrize_collapses_to_same_bag

end Mettapedia.GSLT.MultiRewrite.Comm
