import Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
import Mettapedia.OSLF.MeTTaIL.ContextClosing

/-!
# Structural congruence under contexts and under binding

Structural congruence of rho terms is preserved by plugging into a one-hole
context, and by closing a free name into a bound variable.  Both are needed
to move a congruence beneath an input, whose body is closed over the name it
binds.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution (closeFVar)
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

namespace StructuralCongruence

/-- Two lists that differ at one position by congruent patterns are
congruent position by position. -/
theorem get_append_cons {left right : Pattern} (related : StructuralCongruence left right)
    (after : List Pattern) :
    ∀ (before : List Pattern) (index : Nat)
      (first : index < (before ++ left :: after).length)
      (second : index < (before ++ right :: after).length),
      StructuralCongruence ((before ++ left :: after).get ⟨index, first⟩)
        ((before ++ right :: after).get ⟨index, second⟩)
  | [], 0, _, _ => related
  | [], _ + 1, _, _ => .refl _
  | _ :: _, 0, _, _ => .refl _
  | _ :: before, index + 1, first, second =>
      get_append_cons related after before index (Nat.lt_of_succ_lt_succ first)
        (Nat.lt_of_succ_lt_succ second)

/-- **Plugging congruent patterns gives congruent patterns.** -/
theorem fill : ∀ (context : OneHoleContext) {left right : Pattern},
    StructuralCongruence left right →
      StructuralCongruence (context.fill left) (context.fill right)
  | .hole, _, _, related => related
  | .apply constructor before inner after, _, _, related =>
      .apply_cong constructor _ _ (by simp)
        (get_append_cons (fill inner related) after before)
  | .lambda binderName inner, _, _, related => .lambda_cong binderName _ _ (fill inner related)
  | .multiLambda arity binderNames inner, _, _, related =>
      .multiLambda_cong arity binderNames _ _ (fill inner related)
  | .substBody inner replacement, _, _, related =>
      .subst_cong _ _ _ _ (fill inner related) (.refl replacement)
  | .substReplacement body inner, _, _, related =>
      .subst_cong _ _ _ _ (.refl body) (fill inner related)
  | .collection collectionType before inner after rest, _, _, related =>
      .collection_general_cong collectionType _ _ rest (by simp)
        (get_append_cons (fill inner related) after before)

/-- **Closing a free name preserves structural congruence.** -/
theorem closeName (name : String) {left right : Pattern}
    (related : StructuralCongruence left right) :
    ∀ depth : Nat,
      StructuralCongruence (closeFVar depth name left) (closeFVar depth name right) := by
  induction related with
  | alpha _ _ same => intro depth; subst same; exact .refl _
  | refl _ => intro depth; exact .refl _
  | symm _ _ _ recurse => intro depth; exact .symm _ _ (recurse depth)
  | trans _ _ _ _ _ first second => intro depth; exact .trans _ _ _ (first depth) (second depth)
  | par_singleton pattern =>
      intro depth
      simpa [closeFVar] using StructuralCongruence.par_singleton (closeFVar depth name pattern)
  | par_nil_left pattern =>
      intro depth
      simpa [closeFVar] using StructuralCongruence.par_nil_left (closeFVar depth name pattern)
  | par_nil_right pattern =>
      intro depth
      simpa [closeFVar] using StructuralCongruence.par_nil_right (closeFVar depth name pattern)
  | par_comm first second =>
      intro depth
      simpa [closeFVar] using
        StructuralCongruence.par_comm (closeFVar depth name first) (closeFVar depth name second)
  | par_assoc first second third =>
      intro depth
      simpa [closeFVar] using
        StructuralCongruence.par_assoc (closeFVar depth name first)
          (closeFVar depth name second) (closeFVar depth name third)
  | par_cong first second sameLength _ recurse =>
      intro depth
      rw [closeFVar, closeFVar]
      refine .par_cong _ _ (by simp [sameLength]) fun index firstBound secondBound => ?_
      simp only [List.get_eq_getElem, List.getElem_map]
      exact recurse index (by simpa using firstBound) (by simpa using secondBound) depth
  | par_flatten outer inner =>
      intro depth
      simpa [closeFVar] using
        StructuralCongruence.par_flatten (outer.map (closeFVar depth name))
          (inner.map (closeFVar depth name))
  | par_perm first second permutation =>
      intro depth
      rw [closeFVar, closeFVar]
      exact .par_perm _ _ (permutation.map _)
  | set_perm first second permutation =>
      intro depth
      rw [closeFVar, closeFVar]
      exact .set_perm _ _ (permutation.map _)
  | set_cong first second sameLength _ recurse =>
      intro depth
      rw [closeFVar, closeFVar]
      refine .set_cong _ _ (by simp [sameLength]) fun index firstBound secondBound => ?_
      simp only [List.get_eq_getElem, List.getElem_map]
      exact recurse index (by simpa using firstBound) (by simpa using secondBound) depth
  | lambda_cong binderName _ _ _ recurse =>
      intro depth
      rw [closeFVar, closeFVar]
      exact .lambda_cong binderName _ _ (recurse (depth + 1))
  | apply_cong constructor first second sameLength _ recurse =>
      intro depth
      rw [closeFVar, closeFVar]
      refine .apply_cong constructor _ _ (by simp [sameLength])
        fun index firstBound secondBound => ?_
      simp only [List.get_eq_getElem, List.getElem_map]
      exact recurse index (by simpa using firstBound) (by simpa using secondBound) depth
  | collection_general_cong collectionType first second rest sameLength _ recurse =>
      intro depth
      rw [closeFVar, closeFVar]
      refine .collection_general_cong collectionType _ _ rest (by simp [sameLength])
        fun index firstBound secondBound => ?_
      simp only [List.get_eq_getElem, List.getElem_map]
      exact recurse index (by simpa using firstBound) (by simpa using secondBound) depth
  | multiLambda_cong arity binderNames _ _ _ recurse =>
      intro depth
      rw [closeFVar, closeFVar]
      exact .multiLambda_cong arity binderNames _ _ (recurse (depth + arity))
  | subst_cong _ _ _ _ _ _ body replacement =>
      intro depth
      rw [closeFVar, closeFVar]
      exact .subst_cong _ _ _ _ (body (depth + 1)) (replacement depth)
  | quote_drop pattern =>
      intro depth
      simpa [closeFVar] using StructuralCongruence.quote_drop (closeFVar depth name pattern)
  | par_empty =>
      intro depth
      simpa [closeFVar] using StructuralCongruence.par_empty

end StructuralCongruence

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
