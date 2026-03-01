import Mettapedia.OSLF.MeTTaCore.Types

/-!
# MeTTa's Type System Does Not Satisfy Subject Reduction

This file proves a fundamental limitation of MeTTa's type system:
it does **not** satisfy **subject reduction** (also called *type preservation*),
the property that if `t : T` and `T` reduces to `T'`, then `t : T'`.

## The Problem

MeTTa's `HasType` judgment is *purely lookup-based*:
`HasType space a T` holds when `(: a T)` is literally present in the atomspace.
It does not propagate through type reduction.

Meanwhile, MeTTa's rewrite rules `(= lhs rhs)` can reduce types. After such
a reduction, the typing annotation is *not* automatically updated.

## The Counterexample

We exhibit a concrete atomspace with:
- A term `t` with annotation `(: t (Vec n))` — so `t` has type `(Vec n)`
- A rewrite rule `(= (Vec n) (Vec 0))` — so the type `(Vec n)` reduces to `(Vec 0)`

But `t` does NOT have type `(Vec 0)` in this space, because there is no
annotation `(: t (Vec 0))` present.

## Contrast with MLTT

In Martin-Löf Type Theory (and Calculus of Constructions), subject reduction
is a theorem proved by induction on the typing derivation. The key mechanism
is that typing rules carry proof terms that are preserved under β-reduction.
MeTTa has no such mechanism: types are atoms, typed by lookup, not inference.

## References

* Hyperon Experimental Spec: https://trueagi-io.github.io/hyperon-experimental/metta/
* Martin-Löf à la Coq (arXiv:2310.06376): `literature/HoTT/martin_lof_a_la_coq_2310.06376.pdf`
-/

namespace Mettapedia.OSLF.MeTTaCore

/-! ## Subject Reduction Property -/

/-- **Subject reduction** (type preservation under reduction): if `a` has type `T`
    and `T` reduces to `T'`, then `a` also has type `T'`.

    This is a foundational property of well-behaved dependent type theories
    (MLTT, CoC, Lean itself). MeTTa's type system does NOT satisfy this property. -/
def SubjectReduction
    (HasTy : Atomspace → Atom → Atom → Prop)
    (Reduces : Atomspace → Atom → Atom → Prop) : Prop :=
  ∀ (space : Atomspace) (a T T' : Atom),
    HasTy space a T → Reduces space T T' → HasTy space a T'

/-! ## Reduction via Rewrite Rules -/

/-- One-step syntactic rewrite reduction: atom `a` reduces to `b` when
    the atomspace contains the equation `(= a b)`.

    This is the simplest case of MeTTa reduction (exact syntactic match,
    no unification variables). The MeTTa interpreter can also reduce via
    pattern-matching equations with variables, but this ground case suffices
    for our counterexample. -/
def AtomReduces (space : Atomspace) (a b : Atom) : Prop :=
  .expression [.symbol "=", a, b] ∈ space.atoms

/-! ## The Counterexample -/

private def t_atom   : Atom := .symbol "t"
private def Vec_atom : Atom := .symbol "Vec"
private def n_atom   : Atom := .symbol "n"

/-- The type `(Vec n)` — a type indexed by the free symbol `n`. -/
private def VecN : Atom := .expression [Vec_atom, n_atom]

/-- The type `(Vec 0)` — the type after `n` is "evaluated" to `0`. -/
private def Vec0 : Atom := .expression [Vec_atom, .grounded (.int 0)]

/-- The rewrite rule `(= (Vec n) (Vec 0))` — reduces the type `VecN` to `Vec0`. -/
private def vecRewriteRule : Atom := .expression [.symbol "=", VecN, Vec0]

/-- The counterexample atomspace containing:
    - `(: t (Vec n))` — type annotation making `t : (Vec n)` hold
    - `(= (Vec n) (Vec 0))` — rewrite rule that reduces the type

    Note: there is NO annotation `(: t (Vec 0))` in this space. -/
private def counterSpace : Atomspace :=
  Atomspace.empty.add (typeAnnotation t_atom VecN) |>.add vecRewriteRule

/-! ## The Three Key Lemmas -/

/-- **Lemma 1**: `t` has type `(Vec n)` in `counterSpace`. -/
lemma t_has_type_VecN : HasType counterSpace t_atom VecN :=
  HasType.annotated t_atom VecN (by decide)

/-- **Lemma 2**: `(Vec n)` reduces to `(Vec 0)` in `counterSpace`
    via the rewrite rule `(= (Vec n) (Vec 0))`. -/
lemma VecN_reduces_to_Vec0 : AtomReduces counterSpace VecN Vec0 := by
  unfold AtomReduces counterSpace vecRewriteRule VecN Vec0
  decide

/-- **Lemma 3**: `t` does NOT have type `(Vec 0)` in `counterSpace`.
    There is no annotation `(: t (Vec 0))` in the space,
    and `t` is a symbol so it has no other path to type `(Vec 0)`. -/
lemma t_not_hasType_Vec0 : ¬ HasType counterSpace t_atom Vec0 := by
  intro h
  -- Lean 4 automatically discharges all constructor cases where the type indices
  -- (t_atom, Vec0) cannot match the constructor's index pattern (e.g. intrinsicSymbol
  -- would need Vec0 = .symbol "Symbol", which is impossible). Only the `annotated`
  -- case survives: it requires typeAnnotation t_atom Vec0 ∈ counterSpace.atoms.
  cases h with
  | annotated a ty hmem =>
    -- counterSpace.atoms = {(: t (Vec n)), (= (Vec n) (Vec 0))}
    -- Neither element equals (: t (Vec 0)) — verified by kernel reduction.
    exact absurd hmem (by decide)

/-! ## The Main Theorem -/

/-- **Main Theorem**: MeTTa's type system does not satisfy subject reduction.

    Concretely: in `counterSpace`,
    - `t : (Vec n)` holds (by annotation), and
    - `(Vec n)` reduces to `(Vec 0)` (by the rewrite rule), but
    - `t : (Vec 0)` does NOT hold (no such annotation exists).

    This shows that `HasType` (a pure atomspace-lookup judgment) cannot
    be preserved by `AtomReduces` (rewrite-rule evaluation). -/
theorem metta_not_subject_reduction : ¬ SubjectReduction HasType AtomReduces := by
  intro h
  -- h : ∀ space a T T', HasType space a T → AtomReduces space T T' → HasType space a T'
  -- Apply h to our counterexample
  have hconclusion : HasType counterSpace t_atom Vec0 :=
    h counterSpace t_atom VecN Vec0 t_has_type_VecN VecN_reduces_to_Vec0
  exact t_not_hasType_Vec0 hconclusion

/-! ## Companion Theorems: What MeTTa CAN Do -/

/-- MeTTa trivially satisfies "subject reduction" when the reduction is the
    identity (no change). -/
theorem metta_sr_refl (space : Atomspace) (a T : Atom)
    (h : HasType space a T) : HasType space a T := h

/-- If we *explicitly* add `(: t (Vec 0))` to the atomspace,
    then `t` does obtain that type. This requires intentional augmentation —
    MeTTa does not propagate types through reductions automatically. -/
theorem metta_explicit_augmentation :
    HasType (counterSpace.add (typeAnnotation t_atom Vec0)) t_atom Vec0 :=
  HasType.annotated t_atom Vec0 (by decide)

/-! ## Eval-Closed Atomspaces -/

/-- **Definition**: An atomspace is *eval-closed* (with respect to subject reduction)
    if it contains explicit type annotations for all reduction results:
    whenever `a : T` and `T` reduces to `T'`, the space also contains `(: a T')`.

    This is the property MeTTa atomspaces would need to satisfy subject reduction. -/
def EvalClosed (space : Atomspace) : Prop :=
  ∀ (a T T' : Atom),
    HasType space a T → AtomReduces space T T' →
    typeAnnotation a T' ∈ space.atoms

/-- The counterexample atomspace is NOT eval-closed: it has `t : (Vec n)` and
    `(Vec n) ↪ (Vec 0)`, but does not contain the annotation `(: t (Vec 0))`. -/
theorem counterSpace_not_eval_closed : ¬ EvalClosed counterSpace := by
  intro h
  have hmem := h t_atom VecN Vec0 t_has_type_VecN VecN_reduces_to_Vec0
  exact absurd hmem (by decide)

end Mettapedia.OSLF.MeTTaCore
