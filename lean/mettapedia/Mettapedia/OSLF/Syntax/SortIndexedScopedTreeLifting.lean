import Mettapedia.OSLF.Syntax.SortIndexedScopedOperationalPresentation

/-!
# Lifting depth-indexed scoped derivations to a chosen sort context

The old operational polynomial remembers scoped binders in its constructor
shapes but stores only their number in child judgments. Once a root sort
context is supplied, each child context is uniquely obtained by adjoining
the binder list retained by its constructor. Cartesian premise-position
transport gives a recursive lift of complete proof-relevant derivations.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.SortIndexedScopedTreeLifting

open Mettapedia.TypeTheory
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.Binding.SortIndexedScopedOperationalPresentation
open Mettapedia.OSLF.Binding.IndexedRulePolynomialMorphisms
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists

private abbrev oldPresentation (relEnv : RelationEnv) (lang : LanguageDef) :=
  Mettapedia.OSLF.Binding.ScopedOperationalPresentation.presentation relEnv lang

/-- Every old tree has a sort-indexed lift above a supplied root context
whose length matches its old depth. The actual constructor and premise
position at each node are retained. -/
noncomputable def liftTree (relEnv : RelationEnv) (lang : LanguageDef) :
    ∀ (old : Mettapedia.OSLF.Binding.ScopedOperationalPresentation.Judgment),
      (oldPresentation relEnv lang).Derivation () old →
      ∀ (sorted : Judgment), sorted.depth = old →
        (presentation relEnv lang).Derivation () sorted :=
  fun old tree => IndexedPolynomial.Fix.eliminate
    (oldPresentation relEnv lang).polynomial
    (fun _ old _ => ∀ (sorted : Judgment), sorted.depth = old →
      (presentation relEnv lang).Derivation () sorted)
    (fun _ old shape _children ih sorted indexEq => by
      cases indexEq
      let mapping := depthPolynomialMap relEnv lang
      refine .roll shape ?_
      intro position
      let oldPosition :=
        ((mapping.onPosition () sorted shape).symm position)
      have nextEq := mapping.onNext () sorted shape oldPosition
      rw [(mapping.onPosition () sorted shape).apply_symm_apply position]
        at nextEq
      exact ih oldPosition
        ((presentation relEnv lang).polynomial.next shape position)
        nextEq.symm) () old tree

/-- At a fixed sorted root judgment, lifting is an ordinary map of the
complete old derivation carrier into the new one. -/
noncomputable def liftTreeAt (relEnv : RelationEnv) (lang : LanguageDef)
    (judgment : Judgment) :
    (oldPresentation relEnv lang).Derivation () judgment.depth →
      (presentation relEnv lang).Derivation () judgment :=
  fun tree => liftTree relEnv lang judgment.depth tree judgment rfl

private theorem cast_comp {A : Type} {F : A → Type}
    {a b c : A} (first : a = b) (second : b = c) (value : F a) :
    second ▸ (first ▸ value) = first.trans second ▸ value := by
  cases first
  cases second
  rfl

private theorem cast_dependent_congr {A B : Type} {F : B → Type}
    (index : A → B) (value : (x : A) → F (index x))
    {first second : A} (equal : first = second) :
    congrArg index equal ▸ value first = value second := by
  cases equal
  rfl

/-- Erasing the sort-indexed lift gives the original proof tree, not merely
another tree with the same endpoints. The proof uses the equivalence of
individual premise positions and composes its dependent child transports. -/
theorem erase_liftTree (relEnv : RelationEnv) (lang : LanguageDef)
    (old : Mettapedia.OSLF.Binding.ScopedOperationalPresentation.Judgment)
    (tree : (oldPresentation relEnv lang).Derivation () old) :
    ∀ (sorted : Judgment) (same : sorted.depth = old),
      eraseTree relEnv lang sorted (liftTree relEnv lang old tree sorted same) =
        same.symm ▸ tree := by
  refine IndexedPolynomial.Fix.eliminate
    (oldPresentation relEnv lang).polynomial
    (fun _ old tree => ∀ (sorted : Judgment) (same : sorted.depth = old),
      eraseTree relEnv lang sorted (liftTree relEnv lang old tree sorted same) =
        same.symm ▸ tree) ?_ () old tree
  intro _ old shape children ih sorted same
  cases same
  change IndexedPolynomial.Fix.roll shape _ =
    IndexedPolynomial.Fix.roll shape children
  apply congrArg (IndexedPolynomial.Fix.roll shape)
  funext position
  let mapping := depthPolynomialMap relEnv lang
  let sortedPosition := mapping.onPosition () sorted shape position
  let oldPosition := (mapping.onPosition () sorted shape).symm sortedPosition
  have hpos : oldPosition = position := by
    exact (mapping.onPosition () sorted shape).symm_apply_apply position
  have nextEq := mapping.onNext () sorted shape position
  change
    (Mettapedia.OSLF.Binding.ScopedOperationalPresentation.presentation
      relEnv lang).polynomial.next shape position =
      ((presentation relEnv lang).polynomial.next shape sortedPosition).depth
    at nextEq
  have nextEqOld :
      (oldPresentation relEnv lang).polynomial.next shape oldPosition =
        ((presentation relEnv lang).polynomial.next shape sortedPosition).depth := by
    simpa only [hpos, sortedPosition] using nextEq
  change nextEq.symm ▸ eraseTree relEnv lang
      ((presentation relEnv lang).polynomial.next shape sortedPosition)
      (liftTree relEnv lang
        ((oldPresentation relEnv lang).polynomial.next shape oldPosition)
        (children oldPosition)
        ((presentation relEnv lang).polynomial.next shape sortedPosition)
        nextEqOld.symm) = children position
  rw [ih oldPosition _ nextEqOld.symm]
  rw [cast_comp nextEqOld nextEq.symm]
  have sameTransport : nextEqOld.trans nextEq.symm =
      congrArg (fun p => (oldPresentation relEnv lang).polynomial.next shape p)
        hpos :=
    Subsingleton.elim _ _
  rw [sameTransport]
  exact cast_dependent_congr
    (fun p => (oldPresentation relEnv lang).polynomial.next shape p)
    children hpos

/-- Every old firing history survives sort annotation and erasure exactly
at a chosen root context. -/
theorem erase_liftTreeAt (relEnv : RelationEnv) (lang : LanguageDef)
    (judgment : Judgment)
    (tree : (oldPresentation relEnv lang).Derivation () judgment.depth) :
    eraseTree relEnv lang judgment
      (liftTreeAt relEnv lang judgment tree) = tree := by
  simpa only [liftTreeAt] using
    erase_liftTree relEnv lang judgment.depth tree judgment rfl

/-- Distinct depth-indexed firing histories stay distinct after lifting to
the same chosen root sort context. -/
theorem liftTreeAt_injective (relEnv : RelationEnv) (lang : LanguageDef)
    (judgment : Judgment) :
    Function.Injective (liftTreeAt relEnv lang judgment) := by
  intro first second equal
  have erased := congrArg (eraseTree relEnv lang judgment) equal
  simpa only [erase_liftTreeAt] using erased

private theorem liftTree_cast (relEnv : RelationEnv) (lang : LanguageDef)
    {old newOld : Mettapedia.OSLF.Binding.ScopedOperationalPresentation.Judgment}
    (equal : old = newOld)
    (tree : (oldPresentation relEnv lang).Derivation () old)
    (sorted : Judgment) (same : sorted.depth = newOld) :
    liftTree relEnv lang newOld (equal ▸ tree) sorted same =
      liftTree relEnv lang old tree sorted (same.trans equal.symm) := by
  cases equal
  rfl

/-- Sorting a sorted free firing history after depth erasure returns the
original history at every constructor and recursive premise position. This
uses the exact child-context transport, not just equality of endpoints. -/
theorem lift_eraseTree (relEnv : RelationEnv) (lang : LanguageDef)
    (judgment : Judgment)
    (tree : (presentation relEnv lang).Derivation () judgment) :
    liftTreeAt relEnv lang judgment
      (eraseTree relEnv lang judgment tree) = tree := by
  refine IndexedPolynomial.Fix.eliminate
    (presentation relEnv lang).polynomial
    (fun _ judgment tree =>
      liftTreeAt relEnv lang judgment
        (eraseTree relEnv lang judgment tree) = tree) ?_ () judgment tree
  intro base judgment shape children ih
  cases base
  change IndexedPolynomial.Fix.roll shape _ =
    IndexedPolynomial.Fix.roll shape children
  apply congrArg (IndexedPolynomial.Fix.roll shape)
  funext position
  change (presentation relEnv lang).polynomial.Position shape at position
  let mapping := depthPolynomialMap relEnv lang
  let oldShape := mapping.onShape () judgment shape
  let oldPosition := (mapping.onPosition () judgment shape).symm position
  let mappedPosition := (mapping.onPosition () judgment shape) oldPosition
  have hpos : (mapping.onPosition () judgment shape) oldPosition = position := by
    exact (mapping.onPosition () judgment shape).apply_symm_apply position
  have nextEq := mapping.onNext () judgment shape oldPosition
  have nextEqSorted :
      (oldPresentation relEnv lang).polynomial.next oldShape oldPosition =
      ((presentation relEnv lang).polynomial.next shape position).depth := by
    simpa only [hpos] using nextEq
  change liftTree relEnv lang
      ((oldPresentation relEnv lang).polynomial.next oldShape oldPosition)
      (nextEq.symm ▸ eraseTree relEnv lang
        ((presentation relEnv lang).polynomial.next shape mappedPosition)
        (children mappedPosition))
      ((presentation relEnv lang).polynomial.next shape position)
      nextEqSorted.symm = children position
  have mappedIndexEq := congrArg
    (fun p => ((presentation relEnv lang).polynomial.next shape p).depth)
    hpos
  have erasedHpos :
      mappedIndexEq ▸ eraseTree relEnv lang
        ((presentation relEnv lang).polynomial.next shape mappedPosition)
        (children mappedPosition) =
      eraseTree relEnv lang
        ((presentation relEnv lang).polynomial.next shape position)
        (children position) :=
    cast_dependent_congr
      (fun p => ((presentation relEnv lang).polynomial.next shape p).depth)
      (fun p => eraseTree relEnv lang
        ((presentation relEnv lang).polynomial.next shape p) (children p))
      hpos
  have oldTreeEq :
      nextEq.symm ▸ eraseTree relEnv lang
        ((presentation relEnv lang).polynomial.next shape mappedPosition)
        (children mappedPosition) =
      nextEqSorted.symm ▸ eraseTree relEnv lang
        ((presentation relEnv lang).polynomial.next shape position)
        (children position) := by
    have proofs : nextEq.symm = mappedIndexEq.trans nextEqSorted.symm :=
      Subsingleton.elim _ _
    rw [proofs]
    rw [← cast_comp mappedIndexEq nextEqSorted.symm]
    exact congrArg (fun value => nextEqSorted.symm ▸ value) erasedHpos
  calc
    liftTree relEnv lang _
        (nextEq.symm ▸ eraseTree relEnv lang
          ((presentation relEnv lang).polynomial.next shape mappedPosition)
          (children mappedPosition))
        ((presentation relEnv lang).polynomial.next shape position)
        nextEqSorted.symm =
      liftTree relEnv lang _
        (nextEqSorted.symm ▸ eraseTree relEnv lang
          ((presentation relEnv lang).polynomial.next shape position)
          (children position))
        ((presentation relEnv lang).polynomial.next shape position)
        nextEqSorted.symm :=
          congrArg (fun value => liftTree relEnv lang _ value
            ((presentation relEnv lang).polynomial.next shape position)
            nextEqSorted.symm) oldTreeEq
    _ = liftTreeAt relEnv lang
          ((presentation relEnv lang).polynomial.next shape position)
          (eraseTree relEnv lang
            ((presentation relEnv lang).polynomial.next shape position)
            (children position)) := by
        rw [liftTree_cast relEnv lang nextEqSorted.symm]
        rfl
    _ = children position := ih position

/-- At a fixed sorted judgment, raw sort-indexed and depth-indexed free
firing trees are canonically equivalent. The equivalence retains complete
constructor histories; it does not certify the authors' result sorts. -/
noncomputable def derivationEquiv (relEnv : RelationEnv) (lang : LanguageDef)
    (judgment : Judgment) :
    (presentation relEnv lang).Derivation () judgment ≃
      (oldPresentation relEnv lang).Derivation () judgment.depth where
  toFun := eraseTree relEnv lang judgment
  invFun := liftTreeAt relEnv lang judgment
  left_inv := lift_eraseTree relEnv lang judgment
  right_inv := erase_liftTreeAt relEnv lang judgment

theorem depth_derivation_has_sorted_lift
    (relEnv : RelationEnv) (lang : LanguageDef)
    (judgment : Judgment)
    (available : Nonempty
      ((oldPresentation relEnv lang).Derivation () judgment.depth)) :
    Nonempty ((presentation relEnv lang).Derivation () judgment) :=
  available.map (liftTreeAt relEnv lang judgment)

/-- At a chosen sorted root context, the two raw free presentations inhabit
exactly the same endpoint judgments, as witnessed more strongly by
`derivationEquiv` on complete firing trees. -/
theorem derivation_nonempty_iff
    (relEnv : RelationEnv) (lang : LanguageDef)
    (judgment : Judgment) :
    Nonempty ((presentation relEnv lang).Derivation () judgment) ↔
      Nonempty ((oldPresentation relEnv lang).Derivation ()
        judgment.depth) :=
  ⟨sorted_derivation_has_depth_derivation relEnv lang judgment,
    depth_derivation_has_sorted_lift relEnv lang judgment⟩

/-- Raw constructor-tree existence still depends only on context *length*.
The sorted indices record binder sorts but do not validate the authored
typing of a constructor. A sort-sensitive classifier must refine which
constructor shapes are admitted. -/
theorem derivation_nonempty_congr_depth
    (relEnv : RelationEnv) (lang : LanguageDef)
    (first second : Judgment)
    (same : first.depth = second.depth) :
    Nonempty ((presentation relEnv lang).Derivation () first) ↔
      Nonempty ((presentation relEnv lang).Derivation () second) := by
  rw [derivation_nonempty_iff relEnv lang first,
    derivation_nonempty_iff relEnv lang second, same]

#print axioms liftTree
#print axioms erase_liftTree
#print axioms erase_liftTreeAt
#print axioms liftTreeAt_injective
#print axioms lift_eraseTree
#print axioms derivationEquiv
#print axioms depth_derivation_has_sorted_lift
#print axioms derivation_nonempty_iff
#print axioms derivation_nonempty_congr_depth

end Mettapedia.OSLF.Binding.SortIndexedScopedTreeLifting
