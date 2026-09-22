import Mettapedia.Languages.ProcessCalculi.RhoCombinators.Basic

/-!
# Occupancy: deciding which sub-calculus a term belongs to

A sub-calculus of the combinators is named by a set of atom shapes, and the
expressiveness lattice is the family of those sub-calculi ordered by inclusion.
This module makes membership of a lattice point a *predicate on terms* and
decides it.

Three things are proved.

* `Occ` is the least predicate closed under the term formers whose shape is
  admitted, and `occ_iff_atomsStar_subset` identifies it with hereditary
  containment of the shapes actually occurring.  So satisfying the predicate is
  literally *being a term of* the sub-calculus, quotations included.
* `occ_par` makes the predicate homomorphic for parallel composition, which is
  what keeps the decision one traversal rather than an enumeration of splits:
  no choice of how to divide the components is ever made.
* `occ_step` transports occupancy along reduction, under the closure condition
  `RuleClosed` on the admitted set — and `occupancy_not_invariant_of_consDup`
  shows the condition is necessary, by exhibiting a term that leaves its own
  sub-calculus in one step.

The last of these is a statement about the calculus rather than about the
predicate: a sub-calculus that can *build* the quotation of a node it has no
shape for is not closed under its own reduction, because its names are
quotations of its own processes.

The reduction-closure argument descends into name positions, which is where a
set of shapes and a set of names part company: `Basic.noNameCreation` bounds the
names a constructor-free step can produce, while a constructor step provably
escapes that bound (`Basic.constructor_creates_name`).  Occupancy is coarser and
survives the constructors exactly when `RuleClosed` holds.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCombinators

open Comb

/-! ## Shapes -/

/-- The thirteen atom shapes.  Parallel composition and the empty process are
not atoms, which is why no sub-calculus can omit them. -/
inductive Shape where
  | mm | dd | kk | fw | bl | br | sy | ev | qq
  | consPar | consMsg | consDup | consSyn
  deriving Repr, DecidableEq

/-- The shapes occurring in a term at any quote depth.  Name positions are
descended into: a name of the combinators is a quotation, so the shapes inside
it are shapes the term hereditarily contains. -/
def atomsStar : Comb → Finset Shape
  | nil => ∅
  | par p q => atomsStar p ∪ atomsStar q
  | mm a b => insert Shape.mm (atomsStar a ∪ atomsStar b)
  | dd a b c => insert Shape.dd (atomsStar a ∪ atomsStar b ∪ atomsStar c)
  | kk a => insert Shape.kk (atomsStar a)
  | fw a b => insert Shape.fw (atomsStar a ∪ atomsStar b)
  | bl a b => insert Shape.bl (atomsStar a ∪ atomsStar b)
  | br a b => insert Shape.br (atomsStar a ∪ atomsStar b)
  | sy a b c => insert Shape.sy (atomsStar a ∪ atomsStar b ∪ atomsStar c)
  | ev a => insert Shape.ev (atomsStar a)
  | qq a p => insert Shape.qq (atomsStar a ∪ atomsStar p)
  | consPar a b c => insert Shape.consPar (atomsStar a ∪ atomsStar b ∪ atomsStar c)
  | consMsg a b c => insert Shape.consMsg (atomsStar a ∪ atomsStar b ∪ atomsStar c)
  | consDup a b c e =>
      insert Shape.consDup (atomsStar a ∪ atomsStar b ∪ atomsStar c ∪ atomsStar e)
  | consSyn a b c e =>
      insert Shape.consSyn (atomsStar a ∪ atomsStar b ∪ atomsStar c ∪ atomsStar e)

/-- Structural congruence neither adds nor removes a shape. -/
theorem atomsStar_cong {p q : Comb} (h : Cong p q) : atomsStar p = atomsStar q := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | parNil p => simp [atomsStar]
  | parComm p q => simp [atomsStar, Finset.union_comm]
  | parAssoc p q r => simp [atomsStar, Finset.union_assoc]
  | parLeft q _ ih => simp [atomsStar, ih]
  | parRight p _ ih => simp [atomsStar, ih]

/-- Weakens a containment statement from a term to any of its hereditary
subterms.  The reduction rules put subterms of their premises on the right of
the arrow, so this is the step every case of the transport proofs below takes
before supplying whatever shape the rule itself introduces. -/
local macro "descend" : term =>
  `(fun containment => Finset.Subset.trans
      (by intro shape occurring
          simp only [atomsStar, Finset.mem_insert, Finset.mem_union]
          tauto)
      containment)

/-! ## The occupancy predicate -/

/-- **Occupancy.**  The least predicate containing the empty process, closed
under parallel composition, and admitting an atom exactly when its shape is in
`admitted` and its arguments are themselves occupied.  Being inductive is what
makes it the least such predicate; the recursor is the induction principle the
transport proof below uses. -/
inductive Occ (admitted : Finset Shape) : Comb → Prop where
  | nil : Occ admitted nil
  | par {p q : Comb} : Occ admitted p → Occ admitted q → Occ admitted (par p q)
  | mm {a b : Comb} : Shape.mm ∈ admitted →
      Occ admitted a → Occ admitted b → Occ admitted (mm a b)
  | dd {a b c : Comb} : Shape.dd ∈ admitted →
      Occ admitted a → Occ admitted b → Occ admitted c → Occ admitted (dd a b c)
  | kk {a : Comb} : Shape.kk ∈ admitted → Occ admitted a → Occ admitted (kk a)
  | fw {a b : Comb} : Shape.fw ∈ admitted →
      Occ admitted a → Occ admitted b → Occ admitted (fw a b)
  | bl {a b : Comb} : Shape.bl ∈ admitted →
      Occ admitted a → Occ admitted b → Occ admitted (bl a b)
  | br {a b : Comb} : Shape.br ∈ admitted →
      Occ admitted a → Occ admitted b → Occ admitted (br a b)
  | sy {a b c : Comb} : Shape.sy ∈ admitted →
      Occ admitted a → Occ admitted b → Occ admitted c → Occ admitted (sy a b c)
  | ev {a : Comb} : Shape.ev ∈ admitted → Occ admitted a → Occ admitted (ev a)
  | qq {a p : Comb} : Shape.qq ∈ admitted →
      Occ admitted a → Occ admitted p → Occ admitted (qq a p)
  | consPar {a b c : Comb} : Shape.consPar ∈ admitted →
      Occ admitted a → Occ admitted b → Occ admitted c → Occ admitted (consPar a b c)
  | consMsg {a b c : Comb} : Shape.consMsg ∈ admitted →
      Occ admitted a → Occ admitted b → Occ admitted c → Occ admitted (consMsg a b c)
  | consDup {a b c e : Comb} : Shape.consDup ∈ admitted →
      Occ admitted a → Occ admitted b → Occ admitted c → Occ admitted e →
      Occ admitted (consDup a b c e)
  | consSyn {a b c e : Comb} : Shape.consSyn ∈ admitted →
      Occ admitted a → Occ admitted b → Occ admitted c → Occ admitted e →
      Occ admitted (consSyn a b c e)

/-- **Occupancy is hereditary containment.**  So the predicate holds of exactly
the terms of the sub-calculus whose atoms are `admitted` — the unfolding of the
fixpoint descends the subterm order, and on a finite term it terminates with
every shape encountered matched against the admitted set. -/
theorem occ_iff_atomsStar_subset (admitted : Finset Shape) (t : Comb) :
    Occ admitted t ↔ atomsStar t ⊆ admitted := by
  constructor
  · intro occupied
    induction occupied with
    | nil => simp [atomsStar]
    | par _ _ ih₁ ih₂ =>
        simp only [atomsStar, Finset.union_subset_iff]
        exact ⟨ih₁, ih₂⟩
    | mm shape _ _ ih₁ ih₂ =>
        simp only [atomsStar, Finset.insert_subset_iff, Finset.union_subset_iff]
        exact ⟨shape, ih₁, ih₂⟩
    | dd shape _ _ _ ih₁ ih₂ ih₃ =>
        simp only [atomsStar, Finset.insert_subset_iff, Finset.union_subset_iff]
        exact ⟨shape, ⟨ih₁, ih₂⟩, ih₃⟩
    | kk shape _ ih =>
        simp only [atomsStar, Finset.insert_subset_iff]
        exact ⟨shape, ih⟩
    | fw shape _ _ ih₁ ih₂ =>
        simp only [atomsStar, Finset.insert_subset_iff, Finset.union_subset_iff]
        exact ⟨shape, ih₁, ih₂⟩
    | bl shape _ _ ih₁ ih₂ =>
        simp only [atomsStar, Finset.insert_subset_iff, Finset.union_subset_iff]
        exact ⟨shape, ih₁, ih₂⟩
    | br shape _ _ ih₁ ih₂ =>
        simp only [atomsStar, Finset.insert_subset_iff, Finset.union_subset_iff]
        exact ⟨shape, ih₁, ih₂⟩
    | sy shape _ _ _ ih₁ ih₂ ih₃ =>
        simp only [atomsStar, Finset.insert_subset_iff, Finset.union_subset_iff]
        exact ⟨shape, ⟨ih₁, ih₂⟩, ih₃⟩
    | ev shape _ ih =>
        simp only [atomsStar, Finset.insert_subset_iff]
        exact ⟨shape, ih⟩
    | qq shape _ _ ih₁ ih₂ =>
        simp only [atomsStar, Finset.insert_subset_iff, Finset.union_subset_iff]
        exact ⟨shape, ih₁, ih₂⟩
    | consPar shape _ _ _ ih₁ ih₂ ih₃ =>
        simp only [atomsStar, Finset.insert_subset_iff, Finset.union_subset_iff]
        exact ⟨shape, ⟨ih₁, ih₂⟩, ih₃⟩
    | consMsg shape _ _ _ ih₁ ih₂ ih₃ =>
        simp only [atomsStar, Finset.insert_subset_iff, Finset.union_subset_iff]
        exact ⟨shape, ⟨ih₁, ih₂⟩, ih₃⟩
    | consDup shape _ _ _ _ ih₁ ih₂ ih₃ ih₄ =>
        simp only [atomsStar, Finset.insert_subset_iff, Finset.union_subset_iff]
        exact ⟨shape, ⟨⟨ih₁, ih₂⟩, ih₃⟩, ih₄⟩
    | consSyn shape _ _ _ _ ih₁ ih₂ ih₃ ih₄ =>
        simp only [atomsStar, Finset.insert_subset_iff, Finset.union_subset_iff]
        exact ⟨shape, ⟨⟨ih₁, ih₂⟩, ih₃⟩, ih₄⟩
  · intro contained
    induction t with
    | nil => exact Occ.nil
    | par p q ih₁ ih₂ =>
        simp only [atomsStar, Finset.union_subset_iff] at contained
        exact Occ.par (ih₁ contained.1) (ih₂ contained.2)
    | mm a b ih₁ ih₂ =>
        simp only [atomsStar, Finset.insert_subset_iff, Finset.union_subset_iff] at contained
        exact Occ.mm contained.1 (ih₁ contained.2.1) (ih₂ contained.2.2)
    | dd a b c ih₁ ih₂ ih₃ =>
        simp only [atomsStar, Finset.insert_subset_iff, Finset.union_subset_iff] at contained
        exact Occ.dd contained.1 (ih₁ contained.2.1.1) (ih₂ contained.2.1.2)
          (ih₃ contained.2.2)
    | kk a ih =>
        simp only [atomsStar, Finset.insert_subset_iff] at contained
        exact Occ.kk contained.1 (ih contained.2)
    | fw a b ih₁ ih₂ =>
        simp only [atomsStar, Finset.insert_subset_iff, Finset.union_subset_iff] at contained
        exact Occ.fw contained.1 (ih₁ contained.2.1) (ih₂ contained.2.2)
    | bl a b ih₁ ih₂ =>
        simp only [atomsStar, Finset.insert_subset_iff, Finset.union_subset_iff] at contained
        exact Occ.bl contained.1 (ih₁ contained.2.1) (ih₂ contained.2.2)
    | br a b ih₁ ih₂ =>
        simp only [atomsStar, Finset.insert_subset_iff, Finset.union_subset_iff] at contained
        exact Occ.br contained.1 (ih₁ contained.2.1) (ih₂ contained.2.2)
    | sy a b c ih₁ ih₂ ih₃ =>
        simp only [atomsStar, Finset.insert_subset_iff, Finset.union_subset_iff] at contained
        exact Occ.sy contained.1 (ih₁ contained.2.1.1) (ih₂ contained.2.1.2)
          (ih₃ contained.2.2)
    | ev a ih =>
        simp only [atomsStar, Finset.insert_subset_iff] at contained
        exact Occ.ev contained.1 (ih contained.2)
    | qq a p ih₁ ih₂ =>
        simp only [atomsStar, Finset.insert_subset_iff, Finset.union_subset_iff] at contained
        exact Occ.qq contained.1 (ih₁ contained.2.1) (ih₂ contained.2.2)
    | consPar a b c ih₁ ih₂ ih₃ =>
        simp only [atomsStar, Finset.insert_subset_iff, Finset.union_subset_iff] at contained
        exact Occ.consPar contained.1 (ih₁ contained.2.1.1) (ih₂ contained.2.1.2)
          (ih₃ contained.2.2)
    | consMsg a b c ih₁ ih₂ ih₃ =>
        simp only [atomsStar, Finset.insert_subset_iff, Finset.union_subset_iff] at contained
        exact Occ.consMsg contained.1 (ih₁ contained.2.1.1) (ih₂ contained.2.1.2)
          (ih₃ contained.2.2)
    | consDup a b c e ih₁ ih₂ ih₃ ih₄ =>
        simp only [atomsStar, Finset.insert_subset_iff, Finset.union_subset_iff] at contained
        exact Occ.consDup contained.1 (ih₁ contained.2.1.1.1) (ih₂ contained.2.1.1.2)
          (ih₃ contained.2.1.2) (ih₄ contained.2.2)
    | consSyn a b c e ih₁ ih₂ ih₃ ih₄ =>
        simp only [atomsStar, Finset.insert_subset_iff, Finset.union_subset_iff] at contained
        exact Occ.consSyn contained.1 (ih₁ contained.2.1.1.1) (ih₂ contained.2.1.1.2)
          (ih₃ contained.2.1.2) (ih₄ contained.2.2)

/-- **The predicate is homomorphic for parallel composition.**  This is what
makes the decision one traversal: no division of the components into two parts
is ever chosen, so the exponential that a spatial composition connective
normally costs is not spent here. -/
theorem occ_par (admitted : Finset Shape) (p q : Comb) :
    Occ admitted (par p q) ↔ Occ admitted p ∧ Occ admitted q := by
  simp only [occ_iff_atomsStar_subset, atomsStar, Finset.union_subset_iff]

/-- Occupancy is invariant under structural congruence. -/
theorem occ_cong {admitted : Finset Shape} {p q : Comb} (h : Cong p q)
    (occupied : Occ admitted p) : Occ admitted q := by
  rw [occ_iff_atomsStar_subset] at occupied ⊢
  rwa [← atomsStar_cong h]

/-- Occupancy is decidable, by one traversal computing `atomsStar`. -/
instance (admitted : Finset Shape) (t : Comb) : Decidable (Occ admitted t) :=
  decidable_of_iff _ (occ_iff_atomsStar_subset admitted t).symm

/-! ## Reduction closure -/

/-- **Rule-closed.**  The admitted set must contain every shape a rule can put
on the right of an arrow given only admitted shapes on the left: the medium,
the forwarder that the three re-addressing routers produce, and — for each
constructor — the shape whose quotation that constructor assembles. -/
structure RuleClosed (admitted : Finset Shape) : Prop where
  medium : Shape.mm ∈ admitted
  forwarder : Shape.bl ∈ admitted ∨ Shape.br ∈ admitted ∨ Shape.sy ∈ admitted →
      Shape.fw ∈ admitted
  builtMsg : Shape.consMsg ∈ admitted → Shape.mm ∈ admitted
  builtDup : Shape.consDup ∈ admitted → Shape.dd ∈ admitted
  builtSyn : Shape.consSyn ∈ admitted → Shape.sy ∈ admitted

/-- **Occupancy is preserved by reduction of the constructor-free calculus.**
Only the medium and the forwarder are needed, since no rule here assembles a
quotation. -/
theorem atomsStar_stepMinus {admitted : Finset Shape} (closed : RuleClosed admitted)
    {p q : Comb} (step : StepMinus Cong p q) (contained : atomsStar p ⊆ admitted) :
    atomsStar q ⊆ admitted := by
  induction step with
  | duplicate b c v _ =>
      exact Finset.union_subset
        (Finset.insert_subset closed.medium
          (Finset.union_subset (descend contained) (descend contained)))
        (Finset.insert_subset closed.medium
          (Finset.union_subset (descend contained) (descend contained)))
  | discard v _ => simp [atomsStar]
  | forward b v _ =>
      exact Finset.insert_subset closed.medium
        (Finset.union_subset (descend contained) (descend contained))
  | bindOut b v _ =>
      exact Finset.insert_subset
        (closed.forwarder (Or.inr (Or.inl (contained (by simp [atomsStar])))))
        (Finset.union_subset (descend contained) (descend contained))
  | bindIn b v _ =>
      exact Finset.insert_subset
        (closed.forwarder (Or.inl (contained (by simp [atomsStar]))))
        (Finset.union_subset (descend contained) (descend contained))
  | synchronise b c v _ =>
      exact Finset.insert_subset
        (closed.forwarder (Or.inr (Or.inr (contained (by simp [atomsStar])))))
        (Finset.union_subset (descend contained) (descend contained))
  | opening p _ => exact descend contained
  | release b p _ =>
      exact Finset.insert_subset closed.medium
        (Finset.union_subset (descend contained) (descend contained))
  | parLeft r _ ih =>
      simp only [atomsStar, Finset.union_subset_iff] at contained ⊢
      exact ⟨ih contained.1, contained.2⟩
  | congruent hc₁ _ hc₂ ih =>
      rw [← atomsStar_cong hc₂]
      exact ih (by rwa [← atomsStar_cong hc₁])

/-- **Occupancy is preserved by reduction of the full calculus.**  The four
constructor rules are where the closure conditions on `RuleClosed` are spent:
each emits a message carrying the quotation of a node, and that node's shape
must already be admitted. -/
theorem atomsStar_step {admitted : Finset Shape} (closed : RuleClosed admitted)
    {p q : Comb} (step : Step Cong p q) (contained : atomsStar p ⊆ admitted) :
    atomsStar q ⊆ admitted := by
  induction step with
  | ofMinus minus => exact atomsStar_stepMinus closed minus contained
  | buildPar c p q _ _ =>
      exact Finset.insert_subset closed.medium
        (Finset.union_subset (descend contained)
          (Finset.union_subset (descend contained) (descend contained)))
  | buildMsg c u v _ _ =>
      exact Finset.insert_subset closed.medium
        (Finset.union_subset (descend contained)
          (Finset.insert_subset (closed.builtMsg (contained (by simp [atomsStar])))
            (Finset.union_subset (descend contained) (descend contained))))
  | buildDup e p q r _ _ _ =>
      exact Finset.insert_subset closed.medium
        (Finset.union_subset (descend contained)
          (Finset.insert_subset (closed.builtDup (contained (by simp [atomsStar])))
            (Finset.union_subset
              (Finset.union_subset (descend contained) (descend contained))
              (descend contained))))
  | buildSyn e p q r _ _ _ =>
      exact Finset.insert_subset closed.medium
        (Finset.union_subset (descend contained)
          (Finset.insert_subset (closed.builtSyn (contained (by simp [atomsStar])))
            (Finset.union_subset
              (Finset.union_subset (descend contained) (descend contained))
              (descend contained))))
  | parLeft r _ ih =>
      simp only [atomsStar, Finset.union_subset_iff] at contained ⊢
      exact ⟨ih contained.1, contained.2⟩
  | congruent hc₁ _ hc₂ ih =>
      rw [← atomsStar_cong hc₂]
      exact ih (by rwa [← atomsStar_cong hc₁])

/-- **Invariance of occupancy.**  A rule-closed sub-calculus is closed under its
own reduction, so its occupancy predicate is a reduction invariant. -/
theorem occ_step {admitted : Finset Shape} (closed : RuleClosed admitted)
    {p q : Comb} (occupied : Occ admitted p) (step : Step Cong p q) :
    Occ admitted q := by
  rw [occ_iff_atomsStar_subset] at occupied ⊢
  exact atomsStar_step closed step occupied

/-! ## The closure condition is necessary -/

/-- The witness: a duplicator is assembled from three messages, and the message
that carries it away mentions a shape the sub-calculus does not admit. -/
def escapingTerm : Comb :=
  par (consDup nil nil nil nil) (par (mm nil nil) (par (mm nil nil) (mm nil nil)))

/-- **A sub-calculus carrying the duplicator constructor but not the duplicator
does not contain its own reducts.**  So occupancy is not invariant there, and a
lattice drawn as a product of a computation axis omitting `dd` with a
constructor axis including `consDup` is not a product for this predicate: the
points carrying `consDup` without `dd` fail invariance.

A sub-calculus that can build the name `dd p q r` but has no `dd` atom is not
closed under its own reduction, because its names are quotations of its own
processes. -/
theorem occupancy_not_invariant_of_consDup
    (admitted : Finset Shape)
    (hasConsDup : Shape.consDup ∈ admitted) (hasMedium : Shape.mm ∈ admitted)
    (noDup : Shape.dd ∉ admitted) :
    ∃ p q : Comb, Occ admitted p ∧ Step Cong p q ∧ ¬ Occ admitted q := by
  refine ⟨escapingTerm, mm nil (dd nil nil nil), ?_, ?_, ?_⟩
  · rw [occ_iff_atomsStar_subset]
    simp only [escapingTerm, atomsStar, Finset.insert_subset_iff, Finset.union_subset_iff,
      Finset.empty_subset, and_true]
    exact ⟨hasConsDup, hasMedium, hasMedium, hasMedium⟩
  · exact Step.buildDup nil nil nil nil (Cong.refl nil) (Cong.refl nil) (Cong.refl nil)
  · rw [occ_iff_atomsStar_subset]
    intro contained
    exact noDup (contained (by simp [atomsStar]))

/-- The witness is not vacuous: an admitted set of the described kind exists. -/
theorem escaping_admitted_set_exists :
    ∃ admitted : Finset Shape,
      Shape.consDup ∈ admitted ∧ Shape.mm ∈ admitted ∧ Shape.dd ∉ admitted := by
  refine ⟨{Shape.consDup, Shape.mm}, by simp, by simp, by simp⟩

/-- And therefore the closure condition is exactly what invariance needs: it
fails on the very sets `RuleClosed` excludes. -/
theorem not_ruleClosed_of_consDup_without_dd
    {admitted : Finset Shape}
    (hasConsDup : Shape.consDup ∈ admitted) (noDup : Shape.dd ∉ admitted) :
    ¬ RuleClosed admitted :=
  fun closed => noDup (closed.builtDup hasConsDup)

/-! ## The lattice, decided

Reduction closure is a property of an admitted set alone, so which points of a
drawn lattice are closed under their own reduction is a finite computation.  The
base is the medium, the store, and the five routers that are not the
duplicator; a point adds a subset of the computation shapes and a subset of the
constructors. -/

/-- The shapes every point of the lattice carries. -/
def baseShapes : Finset Shape :=
  {Shape.mm, Shape.kk, Shape.fw, Shape.bl, Shape.br, Shape.sy, Shape.qq}

/-- A point of the lattice: the base, plus computation shapes, plus
constructors. -/
def latticePoint (computation constructors : Finset Shape) : Finset Shape :=
  baseShapes ∪ computation ∪ constructors

instance (admitted : Finset Shape) : Decidable (RuleClosed admitted) := by
  refine decidable_of_iff
    (Shape.mm ∈ admitted ∧
      ((Shape.bl ∈ admitted ∨ Shape.br ∈ admitted ∨ Shape.sy ∈ admitted) →
        Shape.fw ∈ admitted) ∧
      (Shape.consMsg ∈ admitted → Shape.mm ∈ admitted) ∧
      (Shape.consDup ∈ admitted → Shape.dd ∈ admitted) ∧
      (Shape.consSyn ∈ admitted → Shape.sy ∈ admitted)) ?_
  constructor
  · intro h; exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩
  · intro h; exact ⟨h.medium, h.forwarder, h.builtMsg, h.builtDup, h.builtSyn⟩

/-- **The two axes are not independent.**  Every point of the lattice that
carries the duplicator constructor without the duplicator itself fails reduction
closure, whatever else it carries.  So a lattice drawn as a product of a
computation axis over the duplicator and the opener with a constructor axis over
the four constructors is not a product for occupancy: the points omitting the
duplicator while admitting its constructor are exactly the failures. -/
theorem latticePoint_not_ruleClosed
    (computation constructors : Finset Shape)
    (constructorAxis :
      constructors ⊆ {Shape.consPar, Shape.consMsg, Shape.consDup, Shape.consSyn})
    (hasConsDup : Shape.consDup ∈ constructors)
    (noDup : Shape.dd ∉ computation) :
    ¬ RuleClosed (latticePoint computation constructors) := by
  refine not_ruleClosed_of_consDup_without_dd ?_ ?_
  · simp only [latticePoint, Finset.mem_union]
    exact Or.inr hasConsDup
  · simp only [latticePoint, Finset.mem_union]
    rintro ((inBase | inComputation) | inConstructors)
    · revert inBase; decide
    · exact noDup inComputation
    · have bound := constructorAxis inConstructors
      revert bound
      decide

/-! ## Controls

The decision runs.  Each of these is settled by the kernel from the definitions,
so the occupancy predicate is a check on a term rather than a statement about
one. -/

namespace Controls

/-- The base point together with the opener and the parallel constructor. -/
def openerPoint : Finset Shape :=
  latticePoint {Shape.ev} {Shape.consPar}

/-- The same point with the duplicator constructor added and the duplicator
still absent — one of the points that fails closure. -/
def brokenPoint : Finset Shape :=
  latticePoint {Shape.ev} {Shape.consPar, Shape.consDup}

/-- A forwarder relaying a stored process: a term of the base calculus. -/
def relay : Comb := par (fw nil nil) (qq nil (kk nil))

theorem relay_occupies : Occ openerPoint relay := by decide

/-- The same term does not occupy a point that drops the store. -/
theorem relay_needs_store :
    ¬ Occ (latticePoint {Shape.ev} {Shape.consPar} \ {Shape.qq}) relay := by decide

/-- A term carrying a duplicator does not occupy a point without one. -/
theorem duplicator_excluded :
    ¬ Occ openerPoint (dd nil nil nil) := by decide

/-- Occupancy ignores how the components are arranged. -/
theorem occupancy_blind_to_arrangement :
    Occ openerPoint (par relay nil) ∧ Occ openerPoint (par nil relay) := by
  exact ⟨by decide, by decide⟩

/-- The point carrying the opener and the parallel constructor is closed under
its own reduction. -/
theorem openerPoint_ruleClosed : RuleClosed openerPoint := by decide

/-- Adding the duplicator constructor without the duplicator breaks closure —
computed, not argued. -/
theorem brokenPoint_not_ruleClosed : ¬ RuleClosed brokenPoint := by decide

/-- And the general statement covers it: the failure is the missing duplicator,
for every point of the drawn lattice that omits it. -/
theorem brokenPoint_not_ruleClosed_by_axis : ¬ RuleClosed brokenPoint :=
  latticePoint_not_ruleClosed {Shape.ev} {Shape.consPar, Shape.consDup}
    (by decide) (by decide) (by decide)

end Controls

end Mettapedia.Languages.ProcessCalculi.RhoCombinators

#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.atomsStar_cong
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.occ_iff_atomsStar_subset
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.occ_par
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.occ_step
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.occupancy_not_invariant_of_consDup
#print axioms Mettapedia.Languages.ProcessCalculi.RhoCombinators.not_ruleClosed_of_consDup_without_dd
