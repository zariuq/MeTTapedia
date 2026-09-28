import Mettapedia.OSLF.Syntax.IndexedRulePolynomialMorphisms
import Mettapedia.OSLF.Syntax.IndexedRuleAlgebraMorphisms

/-!
# Rule algebras along a cartesian presentation map

A cartesian map of indexed rule polynomials allows a target rule algebra to
be read over the source judgment indices. The resulting source algebra has
one action for each authored source constructor and retains every recursive
premise. Its unique fold is the relative interpretation of source firing
histories. This construction is a component of, rather than a replacement
for, the category combining authored syntax, equations, and rule actions.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IndexedRuleAlgebraPullback

open Mettapedia.TypeTheory
open Mettapedia.OSLF.Binding.IndexedRulePolynomialMorphisms

universe uBase uIndex uOtherIndex uFinalIndex uShape uPosition
  uOtherShape uOtherPosition uFinalShape uFinalPosition
  uCarrier uOtherCarrier uFinalCarrier

variable {Base : Type uBase}
variable {I : Base → Type uIndex} {J : Base → Type uOtherIndex}
variable {P : IndexedPolynomial.{uBase, uIndex, uShape, uPosition} Base I}
variable {Q : IndexedPolynomial.{uBase, uOtherIndex, uOtherShape, uOtherPosition} Base J}
variable {f : ∀ b, I b → J b}
variable (h : Hom P Q f)
variable {target : (b : Base) → J b → Type uCarrier}

/-- Reindex a target rule algebra along a cartesian rule presentation map.
The premise-position equivalence supplies each input exactly once. -/
noncomputable def pullback (A : Q.Algebra target) :
    P.Algebra (fun b i => target b (f b i)) where
  act := fun b i layer =>
    A.act b (f b i)
      ⟨h.onShape b i layer.1,
        fun p => (h.onNext b i layer.1 p).symm ▸
          layer.2 ((h.onPosition b i layer.1) p)⟩

/-- Interpret a source firing history in a target algebra across the rule
presentation map. -/
noncomputable def relativeFold (A : Q.Algebra target) :
    ∀ b i, P.Fix b i → target b (f b i) :=
  IndexedPolynomial.Fix.fold P (pullback h A).act

/-- The relative interpretation satisfies the authored constructor action,
with all recursively interpreted premises at their exact indices. -/
theorem relativeFold_roll (A : Q.Algebra target)
    {b : Base} {i : I b} (shape : P.Shape b i)
    (children : (p : P.Position shape) → P.Fix b (P.next shape p)) :
    relativeFold h A b i (.roll shape children) =
      A.act b (f b i)
        ⟨h.onShape b i shape,
          fun p => (h.onNext b i shape p).symm ▸
            relativeFold h A b _
              (children ((h.onPosition b i shape) p))⟩ := by
  rfl

/-- The relative fold is the unique interpretation preserving every
constructor and its individual recursive premise. -/
theorem relativeFold_unique (A : Q.Algebra target)
    (candidate : ∀ b i, P.Fix b i → target b (f b i))
    (preserves : ∀ b i (shape : P.Shape b i)
      (children : (p : P.Position shape) → P.Fix b (P.next shape p)),
      candidate b i (.roll shape children) =
        A.act b (f b i)
          ⟨h.onShape b i shape,
            fun p => (h.onNext b i shape p).symm ▸
              candidate b _ (children ((h.onPosition b i shape) p))⟩)
    (b : Base) (i : I b) (tree : P.Fix b i) :
    candidate b i tree = relativeFold h A b i tree := by
  refine IndexedPolynomial.Fix.eliminate P
    (fun b i tree => candidate b i tree = relativeFold h A b i tree)
    ?_ b i tree
  intro b i shape children ih
  rw [preserves b i shape children, relativeFold_roll]
  congr 1
  congr 1
  funext p
  exact congrArg
    (fun value => (h.onNext b i shape p).symm ▸ value)
    (ih ((h.onPosition b i shape) p))

private theorem fold_cast (A : Q.Algebra target)
    {b : Base} {j j' : J b} (equal : j = j')
    (tree : Q.Fix b j) :
    IndexedPolynomial.Fix.fold Q A.act b j' (equal ▸ tree) =
      equal ▸ IndexedPolynomial.Fix.fold Q A.act b j tree := by
  cases equal
  rfl

private theorem cast_fun_trans {X : Type*} {Y : Type*}
    {mapping : X → Y} {Family : Y → Type*}
    {x y : X} {z : Y} (first : x = y)
    (second : mapping y = z) (value : Family (mapping x)) :
    ((congrArg mapping first).trans second) ▸ value =
      second ▸ (first ▸ value) := by
  cases first
  cases second
  rfl

/-- Pulling back the target algebra and folding source trees agrees with
first transporting the full firing tree and then folding it in the target.
This is the comparison required when a semantic interpretation changes both
the judgment indices and the rule algebra. -/
theorem relativeFold_eq_mapFix_fold (A : Q.Algebra target)
    (b : Base) (i : I b) (tree : P.Fix b i) :
    relativeFold h A b i tree =
      IndexedPolynomial.Fix.fold Q A.act b (f b i)
        (h.mapFix b i tree) := by
  symm
  apply relativeFold_unique h A
    (fun b i tree =>
      IndexedPolynomial.Fix.fold Q A.act b (f b i)
        (h.mapFix b i tree))
    (by
      intro b i shape children
      change A.act b (f b i)
          ⟨h.onShape b i shape, fun p =>
            IndexedPolynomial.Fix.fold Q A.act b _
              ((h.onNext b i shape p).symm ▸
                h.mapFix b _ (children ((h.onPosition b i shape) p)))⟩ = _
      congr 1
      congr 1
      funext p
      exact fold_cast A (h.onNext b i shape p).symm _) b i tree

/-- Folding into the constructor algebra retains the complete tree. -/
theorem fold_initial_id
    (Q' : IndexedPolynomial.{uBase, uOtherIndex, uOtherShape, uOtherPosition}
      Base J) (b : Base) (j : J b) (tree : Q'.Fix b j) :
    IndexedPolynomial.Fix.fold Q'
      (IndexedPolynomial.Algebra.initial Q').act b j tree = tree := by
  refine IndexedPolynomial.Fix.eliminate Q'
    (fun b j tree =>
      IndexedPolynomial.Fix.fold Q'
        (IndexedPolynomial.Algebra.initial Q').act b j tree = tree)
    ?_ b j tree
  intro b j shape children ih
  change IndexedPolynomial.Fix.roll shape
      (fun p => IndexedPolynomial.Fix.fold Q'
        (IndexedPolynomial.Algebra.initial Q').act b _ (children p)) =
    IndexedPolynomial.Fix.roll shape children
  congr 1
  funext p
  exact ih p

/-- The relative fold into free target firing histories is exactly the
cartesian presentation map's tree action. -/
theorem relativeFold_initial_eq_mapFix
    (b : Base) (i : I b) (tree : P.Fix b i) :
    relativeFold h (IndexedPolynomial.Algebra.initial Q) b i tree =
      h.mapFix b i tree := by
  rw [relativeFold_eq_mapFix_fold]
  exact fold_initial_id Q b (f b i) (h.mapFix b i tree)

/-- Pulling an algebra back along the identity presentation map is the
original algebra, including the action on every premise position. -/
theorem pullback_id
    {source : (b : Base) → I b → Type uCarrier}
    (A : P.Algebra source) :
    pullback (Hom.id P) A = A := by
  cases A
  rfl

/-- Algebra reindexing respects composition of cartesian rule maps. -/
theorem pullback_comp
    {K : Base → Type uFinalIndex}
    {R : IndexedPolynomial.{uBase, uFinalIndex, uFinalShape, uFinalPosition}
      Base K}
    {g : ∀ b, J b → K b}
    {final : (b : Base) → K b → Type uCarrier}
    (k : Hom Q R g) (A : R.Algebra final) :
    pullback (h.comp k) A = pullback h (pullback k A) := by
  have hact : (pullback (h.comp k) A).act =
      (pullback h (pullback k A)).act := by
    funext b i layer
    cases layer with
    | mk shape children =>
        simp only [pullback, Hom.comp]
        congr 1
        congr 1
        funext p
        exact cast_fun_trans
          (h.onNext b i shape
            ((k.onPosition b (f b i) (h.onShape b i shape)) p)).symm
          (k.onNext b (f b i) (h.onShape b i shape) p).symm
          (children ((h.onPosition b i shape)
            ((k.onPosition b (f b i) (h.onShape b i shape)) p)))
  cases ha : pullback (h.comp k) A with
  | mk left =>
      cases hb : pullback h (pullback k A) with
      | mk right =>
          have equal : left = right := by simpa only [ha, hb] using hact
          cases equal
          rfl

private theorem algebraMap_cast
    {source : (b : Base) → J b → Type uCarrier}
    {other : (b : Base) → J b → Type uOtherCarrier}
    {A : Q.Algebra source} {B : Q.Algebra other}
    (mapping : IndexedPolynomial.Algebra.Hom A B)
    {b : Base} {j j' : J b} (equal : j = j')
    (value : source b j) :
    mapping.toFun b j' (equal ▸ value) =
      equal ▸ mapping.toFun b j value := by
  cases equal
  rfl

/-- A cartesian presentation map reindexes rule-algebra morphisms as well
as algebras. This retains the action of a semantic map on every individual
premise value. -/
noncomputable def pullbackHom
    {source : (b : Base) → J b → Type uCarrier}
    {other : (b : Base) → J b → Type uOtherCarrier}
    {A : Q.Algebra source} {B : Q.Algebra other}
    (mapping : IndexedPolynomial.Algebra.Hom A B) :
    IndexedPolynomial.Algebra.Hom (pullback h A) (pullback h B) where
  toFun := fun b i value => mapping.toFun b (f b i) value
  commutes := by
    intro b i layer
    let targetLayer : Q.Extension source b (f b i) :=
      ⟨h.onShape b i layer.1, fun p =>
        (h.onNext b i layer.1 p).symm ▸
          layer.2 ((h.onPosition b i layer.1) p)⟩
    change mapping.toFun b (f b i) (A.act b (f b i) targetLayer) = _
    rw [mapping.commutes b (f b i) targetLayer]
    change B.act b (f b i)
      ⟨h.onShape b i layer.1,
        fun p => mapping.toFun b _
          ((h.onNext b i layer.1 p).symm ▸
            layer.2 ((h.onPosition b i layer.1) p))⟩ = _
    congr 1
    congr 1
    funext p
    exact algebraMap_cast mapping (h.onNext b i layer.1 p).symm
      (layer.2 ((h.onPosition b i layer.1) p))

/-- Reindexing the identity algebra map gives the identity on the
reindexed algebra. -/
theorem pullbackHom_id
    {source : (b : Base) → J b → Type uCarrier}
    (A : Q.Algebra source) :
    pullbackHom h (IndexedPolynomial.Algebra.Hom.id A) =
      IndexedPolynomial.Algebra.Hom.id (pullback h A) := by
  apply IndexedPolynomial.Algebra.Hom.ext
  intro b i value
  rfl

/-- Reindexing preserves composition of rule-algebra interpretations. -/
theorem pullbackHom_comp
    {source : (b : Base) → J b → Type uCarrier}
    {middle : (b : Base) → J b → Type uOtherCarrier}
    {final : (b : Base) → J b → Type uFinalCarrier}
    {A : Q.Algebra source} {B : Q.Algebra middle}
    {C : Q.Algebra final}
    (first : IndexedPolynomial.Algebra.Hom A B)
    (second : IndexedPolynomial.Algebra.Hom B C) :
    pullbackHom h (IndexedPolynomial.Algebra.Hom.comp first second) =
      IndexedPolynomial.Algebra.Hom.comp
        (pullbackHom h first) (pullbackHom h second) := by
  apply IndexedPolynomial.Algebra.Hom.ext
  intro b i value
  rfl

/-- Relative interpretation is natural in a target rule-algebra map.
Individual premise witnesses are transported before the target algebra map
acts, so this law also applies to history-sensitive interpretations. -/
theorem relativeFold_natural
    {source : (b : Base) → J b → Type uCarrier}
    {other : (b : Base) → J b → Type uOtherCarrier}
    {A : Q.Algebra source} {B : Q.Algebra other}
    (mapping : IndexedPolynomial.Algebra.Hom A B)
    (b : Base) (i : I b) (tree : P.Fix b i) :
    mapping.toFun b (f b i) (relativeFold h A b i tree) =
      relativeFold h B b i tree := by
  refine IndexedPolynomial.Fix.eliminate P
    (fun b i tree =>
      mapping.toFun b (f b i) (relativeFold h A b i tree) =
        relativeFold h B b i tree)
    ?_ b i tree
  intro b i shape children ih
  rw [relativeFold_roll h A, relativeFold_roll h B]
  let layer : Q.Extension source b (f b i) :=
    ⟨h.onShape b i shape, fun p => (h.onNext b i shape p).symm ▸
      relativeFold h A b _ (children ((h.onPosition b i shape) p))⟩
  change mapping.toFun b (f b i) (A.act b (f b i) layer) = _
  rw [mapping.commutes b (f b i) layer]
  change B.act b (f b i)
      ⟨h.onShape b i shape,
        fun p => mapping.toFun b _
          ((h.onNext b i shape p).symm ▸
            relativeFold h A b _
              (children ((h.onPosition b i shape) p)))⟩ = _
  congr 1
  congr 1
  funext p
  rw [algebraMap_cast mapping (h.onNext b i shape p).symm]
  exact congrArg
    (fun value => (h.onNext b i shape p).symm ▸ value)
    (ih ((h.onPosition b i shape) p))

/-- Relative interpretation composes with a second rule-presentation map.
The intermediate full firing tree, including all premises, is retained. -/
theorem relativeFold_comp
    {K : Base → Type uFinalIndex}
    {R : IndexedPolynomial.{uBase, uFinalIndex, uFinalShape, uFinalPosition}
      Base K}
    {g : ∀ b, J b → K b}
    {final : (b : Base) → K b → Type uCarrier}
    (k : Hom Q R g) (A : R.Algebra final)
    (b : Base) (i : I b) (tree : P.Fix b i) :
    relativeFold (h.comp k) A b i tree =
      relativeFold k A b (f b i) (h.mapFix b i tree) := by
  rw [relativeFold_eq_mapFix_fold, Hom.mapFix_comp]
  exact (relativeFold_eq_mapFix_fold k A b (f b i)
    (h.mapFix b i tree)).symm

#print axioms relativeFold_unique
#print axioms relativeFold_eq_mapFix_fold
#print axioms relativeFold_initial_eq_mapFix
#print axioms pullback_id
#print axioms pullback_comp
#print axioms pullbackHom
#print axioms relativeFold_natural
#print axioms relativeFold_comp

end Mettapedia.OSLF.Binding.IndexedRuleAlgebraPullback
