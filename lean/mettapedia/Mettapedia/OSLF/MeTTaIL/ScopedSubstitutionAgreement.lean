import Mettapedia.OSLF.MeTTaIL.ContextSubstitution
import Mettapedia.OSLF.MeTTaIL.ScopedPattern

/-!
# Finite-context agreement for raw pattern substitution

A scoped pattern can only inspect substitution entries that correspond to
variables in its declared context. Agreement on those entries survives under
all binders, explicit substitutions and collection elements. This law connects
finite typed environments to the total raw assignment used by the executor.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.ContextSubstitution

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ScopedPattern

/-- Agreement on the variables of a context survives extension by binders. -/
private theorem lift_agree_on_scope
    (first second : Assignment) (depth arity : Nat)
    (agree : ∀ index, index < depth → first index = second index) :
    ∀ index, index < depth + arity →
      lift arity first index = lift arity second index := by
  intro index inside
  unfold lift
  split_ifs with smaller
  · rfl
  · have older : index - arity < depth := by omega
    rw [agree (index - arity) older]

/-- Simultaneous substitution only reads the entries corresponding to actual
free variables of a scoped pattern, including below arbitrary binders. -/
theorem substitute_eq_of_agree_on_scope
    (first second : Assignment) (p : Pattern) (depth : Nat)
    (hscope : p.isWellScopedAt depth = true)
    (agree : ∀ index, index < depth → first index = second index) :
    substitute first p = substitute second p := by
  induction p using Pattern.inductionOn generalizing first second depth with
  | hbvar index =>
      have inside : index < depth := by
        simpa only [Pattern.isWellScopedAt, decide_eq_true_eq] using hscope
      simpa only [substitute] using agree index inside
  | hfvar name => rfl
  | happly constructor arguments ih =>
      have each :=
        (isWellScopedListAt_eq_true_iff depth arguments).mp hscope
      simp only [substitute, substituteList_eq_map]
      congr 1
      exact List.map_congr_left fun p member =>
        ih p member first second depth (each p member) agree

  | hlambda name body ih =>
      simp only [Pattern.isWellScopedAt] at hscope
      simp only [substitute]
      exact congrArg (Pattern.lambda name)
        (ih (lift 1 first) (lift 1 second) (depth + 1) hscope
          (by simpa [Nat.add_comm] using
            lift_agree_on_scope first second depth 1 agree))
  | hmultiLambda arity names body ih =>
      simp only [Pattern.isWellScopedAt] at hscope
      simp only [substitute]
      exact congrArg (Pattern.multiLambda arity names)
        (ih (lift arity first) (lift arity second) (depth + arity)
          hscope (lift_agree_on_scope first second depth arity agree))
  | hsubst body replacement ihBody ihReplacement =>
      simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at hscope
      simp only [substitute]
      exact congrArg₂ Pattern.subst
        (ihBody (lift 1 first) (lift 1 second) (depth + 1)
          hscope.1 (by simpa [Nat.add_comm] using
            lift_agree_on_scope first second depth 1 agree))
        (ihReplacement first second depth hscope.2 agree)
  | hcollection kind elements rest ih =>
      have each :=
        (isWellScopedListAt_eq_true_iff depth elements).mp hscope
      simp only [substitute, substituteList_eq_map]
      congr 1
      exact List.map_congr_left fun p member =>
        ih p member first second depth (each p member) agree

/-- A pattern closed to the surrounding de Bruijn context is unchanged by
every context-variable assignment. It may still contain free names and its
own internal binders. -/
theorem substitute_closed_eq_self (assignment : Assignment) (p : Pattern)
    (closed : p.isWellScopedAt 0 = true) :
    substitute assignment p = p := by
  calc
    substitute assignment p = substitute Pattern.bvar p :=
      substitute_eq_of_agree_on_scope assignment Pattern.bvar p 0 closed
        (by intro index inside; omega)
    _ = p := substitute_id p

#print axioms substitute_eq_of_agree_on_scope

end Mettapedia.OSLF.MeTTaIL.ContextSubstitution
