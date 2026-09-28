import Mettapedia.TypeTheory.IndexedPolynomial

/-!
# Maps of indexed rule presentations

A map of rule presentations sends an output judgment to an output judgment,
each rule constructor to a rule constructor, and each recursive premise to
exactly one recursive premise with the corresponding judgment.  The
equivalence on premise positions retains individual firing histories.  It is
stronger than a map of endpoint reduction predicates.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IndexedRulePolynomialMorphisms

open Mettapedia.TypeTheory

universe uBase uIndex uOtherIndex uShape uPosition uOtherShape uOtherPosition

variable {Base : Type uBase}
variable {I : Base → Type uIndex} {J : Base → Type uOtherIndex}

/-- A cartesian map between indexed rule polynomials over the same context
base. The premise equivalence prevents deletion, duplication, or invention of
recursive evidence. -/
structure Hom
    (P : IndexedPolynomial.{uBase, uIndex, uShape, uPosition} Base I)
    (Q : IndexedPolynomial.{uBase, uOtherIndex, uOtherShape, uOtherPosition} Base J)
    (onIndex : ∀ b, I b → J b) where
  onShape : ∀ b i, P.Shape b i → Q.Shape b (onIndex b i)
  onPosition : ∀ b i (s : P.Shape b i),
    Q.Position (onShape b i s) ≃ P.Position s
  onNext : ∀ b i (s : P.Shape b i)
    (p : Q.Position (onShape b i s)),
    Q.next (onShape b i s) p =
      onIndex b (P.next s ((onPosition b i s) p))

namespace Hom

variable
    {P : IndexedPolynomial.{uBase, uIndex, uShape, uPosition} Base I}
    {Q : IndexedPolynomial.{uBase, uOtherIndex, uOtherShape, uOtherPosition} Base J}

/-- A cartesian rule map is determined by its constructor and premise-address
actions; endpoint-index equations are propositions. -/
theorem ext {f : ∀ b, I b → J b} (first second : Hom P Q f)
    (shapeEq : first.onShape = second.onShape)
    (positionEq : HEq first.onPosition second.onPosition) :
    first = second := by
  cases first with
  | mk firstShape firstPosition firstNext =>
      cases second with
      | mk secondShape secondPosition secondNext =>
          cases shapeEq
          cases positionEq
          rfl

/-- If each source constructor has at most one recursive premise address,
equality of constructor actions determines the whole cartesian rule map. -/
theorem ext_of_subsingleton_positions {f : ∀ b, I b → J b}
    (first second : Hom P Q f)
    (shapeEq : first.onShape = second.onShape)
    (positionSubsingleton : ∀ b i (s : P.Shape b i),
      Subsingleton (P.Position s)) :
    first = second := by
  cases first with
  | mk firstShape firstPosition firstNext =>
      cases second with
      | mk secondShape secondPosition secondNext =>
          cases shapeEq
          have positionEq : firstPosition = secondPosition := by
            funext b i shape
            apply Equiv.ext
            intro position
            exact (positionSubsingleton b i shape).elim _ _
          cases positionEq
          rfl

/-- The identity map of a rule presentation retains every constructor and
every recursive premise. -/
def id (P : IndexedPolynomial.{uBase, uIndex, uShape, uPosition} Base I) :
    Hom P P (fun _ i => i) where
  onShape := fun _ _ s => s
  onPosition := fun _ _ s => Equiv.refl (P.Position s)
  onNext := by intros; rfl

/-- Composition of rule-presentation maps transports each premise through
both position equivalences. -/
def comp
    {K : Base → Type*}
    {R : IndexedPolynomial Base K}
    {f : ∀ b, I b → J b} {g : ∀ b, J b → K b}
    (earlier : Hom P Q f) (later : Hom Q R g) :
    Hom P R (fun b i => g b (f b i)) where
  onShape := fun b i s => later.onShape b (f b i) (earlier.onShape b i s)
  onPosition := fun b i s =>
    (later.onPosition b (f b i) (earlier.onShape b i s)).trans
      (earlier.onPosition b i s)
  onNext := by
    intro b i s p
    calc
      R.next (later.onShape b (f b i) (earlier.onShape b i s)) p =
          g b (Q.next (earlier.onShape b i s)
            ((later.onPosition b (f b i) (earlier.onShape b i s)) p)) :=
        later.onNext b (f b i) (earlier.onShape b i s) p
      _ = g b (f b (P.next s
            ((earlier.onPosition b i s)
              ((later.onPosition b (f b i) (earlier.onShape b i s)) p)))) :=
        congrArg (g b) (earlier.onNext b i s _)

/-- Identity followed by a rule map is that same map, including its
premise-position equivalences. -/
theorem id_comp {f : ∀ b, I b → J b} (h : Hom P Q f) :
    comp (id P) h = h := by
  cases h
  rfl

/-- A rule map followed by the identity retains its exact premise map. -/
theorem comp_id {f : ∀ b, I b → J b} (h : Hom P Q f) :
    comp h (id Q) = h := by
  cases h
  rfl

/-- Rule-map composition is associative on constructors and premise
addresses, not just on the induced endpoint predicates. -/
theorem comp_assoc
    {K L : Base → Type*}
    {R : IndexedPolynomial Base K} {S : IndexedPolynomial Base L}
    {f : ∀ b, I b → J b} {g : ∀ b, J b → K b}
    {k : ∀ b, K b → L b}
    (first : Hom P Q f) (middle : Hom Q R g) (last : Hom R S k) :
    comp (comp first middle) last = comp first (comp middle last) := by
  cases first
  cases middle
  cases last
  rfl

/-- Interpret a firing derivation, recursively transporting each premise at
its exact judgment index. -/
noncomputable def mapFix {f : ∀ b, I b → J b} (h : Hom P Q f) :
    ∀ b i, P.Fix b i → Q.Fix b (f b i) :=
  IndexedPolynomial.Fix.eliminate P
    (fun b i _ => Q.Fix b (f b i))
    (fun b i s _children ih =>
      .roll (h.onShape b i s) (fun p =>
        (h.onNext b i s p).symm ▸
          ih ((h.onPosition b i s) p)))

/-- The identity presentation map acts identically on complete firing
histories, not merely on their endpoints. -/
theorem mapFix_id
    (P : IndexedPolynomial.{uBase, uIndex, uShape, uPosition} Base I)
    (b : Base) (i : I b) (tree : P.Fix b i) :
    (id P).mapFix b i tree = tree := by
  refine IndexedPolynomial.Fix.eliminate P
    (fun b i tree => (id P).mapFix b i tree = tree) ?_ b i tree
  intro b i s children ih
  change IndexedPolynomial.Fix.roll s
      (fun p => (id P).mapFix b _ (children p)) =
    IndexedPolynomial.Fix.roll s children
  congr 1
  funext p
  exact ih p

private theorem mapFix_cast
    {f : ∀ b, I b → J b} (h : Hom P Q f)
    {b : Base} {i i' : I b} (equal : i = i') (tree : P.Fix b i) :
    h.mapFix b i' (equal ▸ tree) =
      congrArg (f b) equal ▸ h.mapFix b i tree := by
  cases equal
  rfl

private theorem cast_trans {X : Type*} {Family : X → Type*}
    {x y z : X} (first : x = y) (second : y = z) (value : Family x) :
    (first.trans second) ▸ value = second ▸ (first ▸ value) := by
  cases first
  cases second
  rfl

/-- Composing presentation maps composes their action on complete firing
histories, retaining every constructor occurrence and premise address. -/
theorem mapFix_comp
    {K : Base → Type*}
    {R : IndexedPolynomial Base K}
    {f : ∀ b, I b → J b} {g : ∀ b, J b → K b}
    (earlier : Hom P Q f) (later : Hom Q R g)
    (b : Base) (i : I b) (tree : P.Fix b i) :
    (comp earlier later).mapFix b i tree =
      later.mapFix b (f b i) (earlier.mapFix b i tree) := by
  refine IndexedPolynomial.Fix.eliminate P
    (fun b i tree =>
      (comp earlier later).mapFix b i tree =
        later.mapFix b (f b i) (earlier.mapFix b i tree)) ?_ b i tree
  intro b i s children ih
  change IndexedPolynomial.Fix.roll
      (later.onShape b (f b i) (earlier.onShape b i s))
      (fun p => (comp earlier later).onNext b i s p |>.symm ▸
        (comp earlier later).mapFix b _
          (children ((earlier.onPosition b i s)
            ((later.onPosition b (f b i) (earlier.onShape b i s)) p)))) =
    IndexedPolynomial.Fix.roll
      (later.onShape b (f b i) (earlier.onShape b i s))
      (fun p => (later.onNext b (f b i) (earlier.onShape b i s) p).symm ▸
        later.mapFix b _
          ((earlier.onNext b i s
            ((later.onPosition b (f b i) (earlier.onShape b i s)) p)).symm ▸
              earlier.mapFix b _
                (children ((earlier.onPosition b i s)
                  ((later.onPosition b (f b i) (earlier.onShape b i s)) p)))))
  congr 1
  funext p
  let q' := (later.onPosition b (f b i) (earlier.onShape b i s)) p
  let q := (earlier.onPosition b i s) q'
  have hp : (comp earlier later).onPosition b i s p = q := rfl
  change ((comp earlier later).onNext b i s p).symm ▸
      (comp earlier later).mapFix b (P.next s q) (children q) =
    (later.onNext b (f b i) (earlier.onShape b i s) p).symm ▸
      later.mapFix b (Q.next (earlier.onShape b i s) q')
        ((earlier.onNext b i s q').symm ▸
          earlier.mapFix b (P.next s q) (children q))
  rw [ih q]
  rw [mapFix_cast later (earlier.onNext b i s q').symm
    (earlier.mapFix b (P.next s q) (children q))]
  exact cast_trans (congrArg (g b) (earlier.onNext b i s q').symm)
    (later.onNext b (f b i) (earlier.onShape b i s) p).symm
    (later.mapFix b (f b (P.next s q))
      (earlier.mapFix b (P.next s q) (children q)))

/-- Constructor preservation characterizes the interpretation of every
firing history. This is the relative initiality law for a cartesian rule-map
over a fixed map of judgment indices. -/
theorem mapFix_unique {f : ∀ b, I b → J b} (h : Hom P Q f)
    (candidate : ∀ b i, P.Fix b i → Q.Fix b (f b i))
    (preserves : ∀ b i (s : P.Shape b i)
      (children : (p : P.Position s) → P.Fix b (P.next s p)),
      candidate b i (.roll s children) =
        .roll (h.onShape b i s)
          (fun p => (h.onNext b i s p).symm ▸
            candidate b _ (children ((h.onPosition b i s) p))))
    (b : Base) (i : I b) (tree : P.Fix b i) :
    candidate b i tree = h.mapFix b i tree := by
  refine IndexedPolynomial.Fix.eliminate P
    (fun b i tree => candidate b i tree = h.mapFix b i tree)
    ?_ b i tree
  intro b i s children ih
  calc
    candidate b i (.roll s children) =
        .roll (h.onShape b i s)
          (fun p => (h.onNext b i s p).symm ▸
            candidate b _ (children ((h.onPosition b i s) p))) :=
      preserves b i s children
    _ = .roll (h.onShape b i s)
          (fun p => (h.onNext b i s p).symm ▸
            h.mapFix b _ (children ((h.onPosition b i s) p))) := by
      congr 1
      funext p
      exact congrArg
        (fun value => (h.onNext b i s p).symm ▸ value)
        (ih ((h.onPosition b i s) p))
    _ = h.mapFix b i (.roll s children) := rfl

end Hom

end Mettapedia.OSLF.Binding.IndexedRulePolynomialMorphisms
