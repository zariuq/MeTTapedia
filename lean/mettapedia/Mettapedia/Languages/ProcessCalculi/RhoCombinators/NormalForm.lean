import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Seeds

/-!
# The normal form for structural congruence

Structural congruence is the monoid laws for parallel composition, so a term
is determined up to congruence by the multiset of its parallel components.
`Seeds.lean` proves the soundness direction: congruence preserves components.
This file proves the completeness direction, which is what makes the normal
form usable.

* `componentList` — the components as a list;
* `ofList` — right-nested composition of a list;
* `cong_ofList` — every term is congruent to the composition of its own
  components, so the normal form is reachable;
* `ofList_perm` — permuting components preserves congruence;
* `cong_of_perm` — **terms whose components agree up to permutation are
  congruent.**

`cong_of_components` converts that into component *arithmetic*: since the
components form a multiset under addition, a rearrangement is discharged by
commutativity and associativity, so each one is `ac_rfl` rather than a
hand-written chain.

The last two are the working tools.  Rearranging a parallel composition to bring a
redex together is otherwise a chain of associativity and commutativity steps
written by hand, one chain per rearrangement; with `cong_of_perm` it is a
single application together with a permutation of lists.

## References

- L. G. Meredith and M. Radestock, *A reflective higher-order calculus*,
  ENTCS 141(5):49–67, 2005, for the congruence.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Comb

/-- Parallel components as a list. -/
def componentList : Comb → List Comb
  | nil => []
  | par p q => componentList p ++ componentList q
  | mm a b => [mm a b]
  | dd a b c => [dd a b c]
  | kk a => [kk a]
  | fw a b => [fw a b]
  | bl a b => [bl a b]
  | br a b => [br a b]
  | sy a b c => [sy a b c]
  | ev a => [ev a]
  | qq a p => [qq a p]
  | consPar a b c => [consPar a b c]
  | consMsg a b c => [consMsg a b c]
  | consDup a b c e => [consDup a b c e]
  | consSyn a b c e => [consSyn a b c e]

/-- Right-nested parallel composition of a list. -/
def ofList : List Comb → Comb
  | [] => nil
  | x :: rest => par x (ofList rest)

theorem ofList_append (l₁ l₂ : List Comb) :
    Cong (ofList (l₁ ++ l₂)) (par (ofList l₁) (ofList l₂)) := by
  induction l₁ with
  | nil =>
      simp only [List.nil_append, ofList]
      exact Cong.symm (Cong.trans (Cong.parComm _ _) (Cong.parNil _))
  | cons x rest ih =>
      simp only [List.cons_append, ofList]
      exact Cong.trans (Cong.parRight x ih) (Cong.symm (Cong.parAssoc _ _ _))

/-- Every term is congruent to the right-nested composition of its
components: the normal form is reachable. -/
theorem cong_ofList (t : Comb) : Cong t (ofList (componentList t)) := by
  induction t with
  | nil => exact Cong.refl _
  | par p q ihp ihq =>
      refine Cong.trans (Cong.trans (Cong.parLeft _ ihp) (Cong.parRight _ ihq)) ?_
      exact Cong.symm (ofList_append _ _)
  | mm a b => exact Cong.symm (Cong.parNil _)
  | dd a b c => exact Cong.symm (Cong.parNil _)
  | kk a => exact Cong.symm (Cong.parNil _)
  | fw a b => exact Cong.symm (Cong.parNil _)
  | bl a b => exact Cong.symm (Cong.parNil _)
  | br a b => exact Cong.symm (Cong.parNil _)
  | sy a b c => exact Cong.symm (Cong.parNil _)
  | ev a => exact Cong.symm (Cong.parNil _)
  | qq a p => exact Cong.symm (Cong.parNil _)
  | consPar a b c => exact Cong.symm (Cong.parNil _)
  | consMsg a b c => exact Cong.symm (Cong.parNil _)
  | consDup a b c e => exact Cong.symm (Cong.parNil _)
  | consSyn a b c e => exact Cong.symm (Cong.parNil _)

/-- Permuting the components preserves congruence. -/
theorem ofList_perm {l₁ l₂ : List Comb} (h : l₁.Perm l₂) :
    Cong (ofList l₁) (ofList l₂) := by
  induction h with
  | nil => exact Cong.refl _
  | cons x _ ih => exact Cong.parRight x ih
  | swap x y l =>
      simp only [ofList]
      exact Cong.trans (Cong.symm (Cong.parAssoc _ _ _))
        (Cong.trans (Cong.parLeft _ (Cong.parComm _ _)) (Cong.parAssoc _ _ _))
  | trans _ _ ih₁ ih₂ => exact Cong.trans ih₁ ih₂

/-- **Completeness of the normal form.**  Terms whose components agree up to
permutation are structurally congruent.  Every rearrangement of a parallel
composition is therefore a single application of this lemma. -/
theorem cong_of_perm {p q : Comb} (h : (componentList p).Perm (componentList q)) :
    Cong p q :=
  Cong.trans (cong_ofList p) (Cong.trans (ofList_perm h) (Cong.symm (cong_ofList q)))

/-! ## Rearrangement by component arithmetic -/

theorem components_eq_coe (t : Comb) :
    components t = (componentList t : Multiset Comb) := by
  induction t with
  | nil => rfl
  | par p q ihp ihq =>
      simp only [components, componentList, ihp, ihq]
      exact (Multiset.coe_add _ _).symm
  | mm a b => rfl
  | dd a b c => rfl
  | kk a => rfl
  | fw a b => rfl
  | bl a b => rfl
  | br a b => rfl
  | sy a b c => rfl
  | ev a => rfl
  | qq a p => rfl
  | consPar a b c => rfl
  | consMsg a b c => rfl
  | consDup a b c e => rfl
  | consSyn a b c e => rfl

theorem cong_of_components {p q : Comb} (h : components p = components q) :
    Cong p q := by
  refine cong_of_perm ?_
  rw [components_eq_coe, components_eq_coe] at h
  exact Multiset.coe_eq_coe.mp h

/-! ## Every bag is realized by a term

The reactive-systems reading of this calculus quantifies over *contexts as
bags*.  For that reading to be about terms rather than about bookkeeping, every
bag that can appear as a context must be the component bag of an actual term.
It is, and the witness is `ofList`.
-/

/-- Components are atoms: a component of a term is its own only component. -/
theorem atomic_of_mem_components {t : Comb} :
    ∀ {x : Comb}, x ∈ components t → components x = {x} := by
  induction t with
  | nil => intro x hx; simp [components] at hx
  | par p q ihp ihq =>
      intro x hx
      simp only [components, Multiset.mem_add] at hx
      rcases hx with h | h
      · exact ihp h
      · exact ihq h
  | _ =>
      intro x hx
      simp only [components, Multiset.mem_singleton] at hx
      subst hx; rfl

/-- On a list of atoms, `ofList` realizes the list as a component bag. -/
theorem components_ofList_of_atomic :
    ∀ {l : List Comb}, (∀ x ∈ l, components x = {x}) → components (ofList l) = (l : Multiset Comb)
  | [], _ => rfl
  | x :: rest, h => by
      have tail := components_ofList_of_atomic (fun y hy => h y (List.Mem.tail _ hy))
      simp only [ofList, components, h x (List.Mem.head _), tail]
      rfl

/-- **Every sub-bag of a term's components is itself a term's components.**  So
a reaction context in the bag category is always a process, and the bag reading
loses nothing. -/
theorem exists_components_eq {t : Comb} {ctx : Multiset Comb} (h : ctx ≤ components t) :
    ∃ c : Comb, components c = ctx := by
  refine ⟨ofList ctx.toList, ?_⟩
  rw [components_ofList_of_atomic (fun x hx =>
    atomic_of_mem_components (Multiset.mem_of_le h (Multiset.mem_toList.mp hx)))]
  exact Multiset.coe_toList ctx

end Mettapedia.Languages.ProcessCalculi.RhoCombinators

#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.ofList_append
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.cong_ofList
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.ofList_perm
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.cong_of_perm
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.components_eq_coe
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.cong_of_components
