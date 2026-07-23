/-
Boundary lemmas for the repaired LeaTTa matcher: a single failing child
collapses the whole pointwise match, for EVERY accumulator — so downstream
proofs never unfold `matchAll`'s recursion (which, post-repair, keeps
computing child subs/filters even on an empty accumulator).

Candidates for adoption into `MettaHyperonFull/Proofs/Indexing.lean`
next to `matchAll_nil` (re-proved privately here so this file depends only
on the settled Core, not on Proofs files currently being rebuilt).
-/
import MettaHyperonFull.Core.Matching

namespace Metta

private theorem matchAllNil (custom : Option GroundMatcher)
    (xs : List Atom) : ∀ ys, matchAll custom [] xs ys = [] := by
  induction xs with
  | nil => intro ys; cases ys <;> rfl
  | cons x xs ih =>
    intro ys
    cases ys with
    | nil => rfl
    | cons y ys =>
      show matchAll custom (([] : List Bindings).flatMap _) xs ys = []
      exact ih ys

private theorem nilFlatMap {α β : Type _} (f : α → List β) :
    ([] : List α).flatMap f = [] := rfl

private theorem flatMapConstNil {α β : Type _} (l : List α) :
    (l.flatMap fun _ => ([] : List β)) = [] := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

private theorem matchAllCons (custom : Option GroundMatcher)
    (acc : List Bindings) (x y : Atom) (xs ys : List Atom) :
    matchAll custom acc (x :: xs) (y :: ys) =
      matchAll custom
        (acc.flatMap fun a =>
          ((matchAtomsWith custom x y).filter fun b => !b.hasLoop).flatMap
            fun b => Bindings.merge a b) xs ys := rfl

/-- If any aligned child pair fails to match (after the per-child loop
filter), the pointwise matcher returns nothing — for every accumulator. -/
theorem matchAll_eq_nil_of_child_nil (custom : Option GroundMatcher)
    {x y : Atom}
    (hchild : (matchAtomsWith custom x y).filter (fun b => !b.hasLoop) = []) :
    ∀ (acc : List Bindings) (xs ys : List Atom),
      (x, y) ∈ xs.zip ys → matchAll custom acc xs ys = []
  | _, [], _, h => by simp at h
  | _, _ :: _, [], h => by simp at h
  | acc, x' :: xs, y' :: ys, h => by
    rw [List.zip_cons_cons] at h
    cases List.mem_cons.mp h with
    | inl heq =>
      have h1 : x = x' := congrArg Prod.fst heq
      have h2 : y = y' := congrArg Prod.snd heq
      subst h1
      subst h2
      rw [matchAllCons, hchild]
      simp only [nilFlatMap]
      rw [flatMapConstNil]
      exact matchAllNil custom xs ys
    | inr htail =>
      rw [matchAllCons]
      exact matchAll_eq_nil_of_child_nil custom hchild _ xs ys htail

/-- Raw-child variant: an unfiltered child failure already collapses
everything. -/
theorem matchAll_eq_nil_of_child_raw_nil (custom : Option GroundMatcher)
    {x y : Atom} (hchild : matchAtomsWith custom x y = [])
    (acc : List Bindings) (xs ys : List Atom)
    (hmem : (x, y) ∈ xs.zip ys) : matchAll custom acc xs ys = [] :=
  matchAll_eq_nil_of_child_nil custom (by rw [hchild]; rfl) acc xs ys hmem

/-- Public-boundary corollary: one failing child kills the whole
expression-vs-expression match. -/
theorem matchAtoms_expr_eq_nil_of_child_nil {x y : Atom} {xs ys : List Atom}
    (hmem : (x, y) ∈ xs.zip ys)
    (hchild : (matchAtomsWith none x y).filter (fun b => !b.hasLoop) = []) :
    matchAtoms (.expr xs) (.expr ys) = [] := by
  show ((matchAtomsWith none (.expr xs) (.expr ys)).filter
    fun b => !b.hasLoop) = []
  rw [show matchAtomsWith none (.expr xs) (.expr ys) =
      matchAll none [[]] xs ys from rfl,
    matchAll_eq_nil_of_child_nil none hchild [[]] xs ys hmem]
  rfl

/-- Public-boundary corollary, raw-child form. -/
theorem matchAtoms_expr_eq_nil_of_child_raw_nil {x y : Atom}
    {xs ys : List Atom}
    (hmem : (x, y) ∈ xs.zip ys) (hchild : matchAtomsWith none x y = []) :
    matchAtoms (.expr xs) (.expr ys) = [] :=
  matchAtoms_expr_eq_nil_of_child_nil hmem (by rw [hchild]; rfl)

end Metta
