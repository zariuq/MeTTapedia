import Mettapedia.OSLF.Syntax.IndexedRuleFreeTransport
import Mettapedia.OSLF.Syntax.IndexedRuleAlgebraPullback

/-!
# Transport of event-variable substitution across rule presentations

A cartesian rule translation sends a tree with typed event variables to a
tree with translated variables. Filling those variables commutes with that
translation whenever the two interpretations of each variable agree. This
is the composition law needed by contextual free operational syntax when
the program interpretation changes.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IndexedRuleFreeSubstitutionNaturality

open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding.IndexedRulePolynomialMorphisms
open Mettapedia.OSLF.Binding.IndexedRuleFreeTransport

universe uBase uIndex uOtherIndex uShape uPosition uOtherShape uOtherPosition
  uHole uOtherHole uNext uOtherNext uCarrier

variable {Base : Type uBase}
variable {I : Base → Type uIndex} {J : Base → Type uOtherIndex}
variable {P : IndexedPolynomial.{uBase, uIndex, uShape, uPosition} Base I}
variable {Q : IndexedPolynomial.{uBase, uOtherIndex, uOtherShape, uOtherPosition} Base J}
variable {f : ∀ b, I b → J b}
variable {H : (b : Base) → I b → Type uHole}
variable {K : (b : Base) → J b → Type uOtherHole}
variable {H' : (b : Base) → I b → Type uNext}
variable {K' : (b : Base) → J b → Type uOtherNext}

private theorem fold_cast
    {carrier : (b : Base) → J b → Type uCarrier}
    (decode : ∀ b j, K b j → carrier b j)
    (algebra : Q.Algebra carrier)
    {b : Base} {j j' : J b} (equal : j = j')
    (tree : Q.Free K b j) :
    IndexedPolynomial.Free.fold Q decode algebra b j' (equal ▸ tree) =
      equal ▸ IndexedPolynomial.Free.fold Q decode algebra b j tree := by
  cases equal
  rfl

/-- Interpreting a transported tree in an arbitrary target rule algebra
agrees with interpreting the source tree in the pulled-back algebra. This
retains typed leaves, constructor positions, and binder-local premises. -/
theorem fold_mapFree
    {carrier : (b : Base) → J b → Type uCarrier}
    (h : Hom P Q f) (algebra : Q.Algebra carrier)
    (leaf : ∀ b i, H b i → K b (f b i))
    (decode : ∀ b j, K b j → carrier b j)
    (b : Base) (i : I b) (tree : P.Free H b i) :
    IndexedPolynomial.Free.fold Q decode algebra b (f b i)
        (mapFree h leaf b i tree) =
      IndexedPolynomial.Free.fold P
        (fun b i seed => decode b (f b i) (leaf b i seed))
        (IndexedRuleAlgebraPullback.pullback h algebra) b i tree := by
  refine IndexedPolynomial.Fix.eliminate (P.withHoles H)
    (fun b i tree =>
      IndexedPolynomial.Free.fold Q decode algebra b (f b i)
          (mapFree h leaf b i tree) =
        IndexedPolynomial.Free.fold P
          (fun b i seed => decode b (f b i) (leaf b i seed))
          (IndexedRuleAlgebraPullback.pullback h algebra) b i tree)
    ?_ b i tree
  intro b i shape children ih
  cases shape with
  | inl seed =>
      have empty : children = fun position => position.elim := by
        funext position
        exact position.elim
      subst children
      change IndexedPolynomial.Free.fold Q decode algebra b (f b i)
          (mapFree h leaf b i (IndexedPolynomial.Free.pure P seed)) =
        IndexedPolynomial.Free.fold P
          (fun b i seed => decode b (f b i) (leaf b i seed))
          (IndexedRuleAlgebraPullback.pullback h algebra) b i
          (IndexedPolynomial.Free.pure P seed)
      rw [mapFree_pure, IndexedPolynomial.Free.fold_pure,
        IndexedPolynomial.Free.fold_pure]
  | inr shape =>
      change (position : P.Position shape) →
        P.Free H b (P.next shape position) at children
      change ∀ position : P.Position shape,
        IndexedPolynomial.Free.fold Q decode algebra b
            (f b (P.next shape position))
            (mapFree h leaf b _ (children position)) =
          IndexedPolynomial.Free.fold P
            (fun b i seed => decode b (f b i) (leaf b i seed))
            (IndexedRuleAlgebraPullback.pullback h algebra) b _
            (children position) at ih
      change IndexedPolynomial.Free.fold Q decode algebra b (f b i)
          (mapFree h leaf b i (IndexedPolynomial.Free.node P shape children)) =
        IndexedPolynomial.Free.fold P
          (fun b i seed => decode b (f b i) (leaf b i seed))
          (IndexedRuleAlgebraPullback.pullback h algebra) b i
          (IndexedPolynomial.Free.node P shape children)
      rw [mapFree_node, IndexedPolynomial.Free.fold_node,
        IndexedPolynomial.Free.fold_node]
      change algebra.act b (f b i)
          ⟨h.onShape b i shape,
            fun position => IndexedPolynomial.Free.fold Q decode algebra b _
              ((h.onNext b i shape position).symm ▸
                mapFree h leaf b _
                  (children ((h.onPosition b i shape) position)))⟩ =
        algebra.act b (f b i)
          ⟨h.onShape b i shape,
            fun position => (h.onNext b i shape position).symm ▸
              IndexedPolynomial.Free.fold P
                (fun b i seed => decode b (f b i) (leaf b i seed))
                (IndexedRuleAlgebraPullback.pullback h algebra) b _
                (children ((h.onPosition b i shape) position))⟩
      congr 1
      congr 1
      funext position
      rw [fold_cast decode algebra (h.onNext b i shape position).symm]
      exact congrArg
        (fun value => (h.onNext b i shape position).symm ▸ value)
        (ih ((h.onPosition b i shape) position))

/-- Filling is stable under transport of a judgment index. -/
private theorem bind_cast
    (fill : ∀ b j, K b j → Q.Free K' b j)
    {b : Base} {j k : J b} (equal : j = k)
    (tree : Q.Free K b j) :
    IndexedPolynomial.Free.bind Q fill b k (equal ▸ tree) =
      equal ▸ IndexedPolynomial.Free.bind Q fill b j tree := by
  cases equal
  rfl

/-- Mapping a free tree through a cartesian rule translation commutes with
filling its event leaves. The premise is precisely the compatibility of the
two fillings on each original event variable; constructors and their ordered
recursive positions require no further assumptions. -/
theorem mapFree_bind (h : Hom P Q f)
    (leaf : ∀ b i, H b i → K b (f b i))
    (nextLeaf : ∀ b i, H' b i → K' b (f b i))
    (sourceFill : ∀ b i, H b i → P.Free H' b i)
    (targetFill : ∀ b j, K b j → Q.Free K' b j)
    (commutes : ∀ b i (seed : H b i),
      mapFree h nextLeaf b i (sourceFill b i seed) =
        targetFill b (f b i) (leaf b i seed))
    (b : Base) (i : I b) (tree : P.Free H b i) :
    mapFree h nextLeaf b i
        (IndexedPolynomial.Free.bind P sourceFill b i tree) =
      IndexedPolynomial.Free.bind Q targetFill b (f b i)
        (mapFree h leaf b i tree) := by
  refine IndexedPolynomial.Fix.eliminate (P.withHoles H)
    (fun b i tree =>
      mapFree h nextLeaf b i
          (IndexedPolynomial.Free.bind P sourceFill b i tree) =
        IndexedPolynomial.Free.bind Q targetFill b (f b i)
          (mapFree h leaf b i tree)) ?_ b i tree
  intro b i shape children ih
  cases shape with
  | inl seed =>
      have empty : children = fun position => position.elim := by
        funext position
        exact position.elim
      subst children
      change mapFree h nextLeaf b i
          (IndexedPolynomial.Free.bind P sourceFill b i
            (IndexedPolynomial.Free.pure P seed)) =
        IndexedPolynomial.Free.bind Q targetFill b (f b i)
          (mapFree h leaf b i (IndexedPolynomial.Free.pure P seed))
      rw [IndexedPolynomial.Free.bind_pure, mapFree_pure,
        IndexedPolynomial.Free.bind_pure]
      exact commutes b i seed
  | inr shape =>
      change (position : P.Position shape) →
        P.Free H b (P.next shape position) at children
      change ∀ position : P.Position shape,
        mapFree h nextLeaf b _
            (IndexedPolynomial.Free.bind P sourceFill b _ (children position)) =
          IndexedPolynomial.Free.bind Q targetFill b _
            (mapFree h leaf b _ (children position)) at ih
      change mapFree h nextLeaf b i
          (IndexedPolynomial.Free.bind P sourceFill b i
            (IndexedPolynomial.Free.node P shape children)) =
        IndexedPolynomial.Free.bind Q targetFill b (f b i)
          (mapFree h leaf b i
            (IndexedPolynomial.Free.node P shape children))
      rw [IndexedPolynomial.Free.bind_node, mapFree_node,
        mapFree_node, IndexedPolynomial.Free.bind_node]
      congr 1
      funext position
      let equal : f b (P.next shape ((h.onPosition b i shape) position)) =
          Q.next (h.onShape b i shape) position :=
        (h.onNext b i shape position).symm
      change (equal ▸ mapFree h nextLeaf b _
          (IndexedPolynomial.Free.bind P sourceFill b _
            (children ((h.onPosition b i shape) position)))) =
        IndexedPolynomial.Free.bind Q targetFill b _
          (equal ▸ mapFree h leaf b _
            (children ((h.onPosition b i shape) position)))
      rw [bind_cast targetFill equal]
      exact congrArg (fun value => equal ▸ value)
        (ih ((h.onPosition b i shape) position))

end Mettapedia.OSLF.Binding.IndexedRuleFreeSubstitutionNaturality
