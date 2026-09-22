import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Relative pushouts, and least contexts as a universal property

A labelled transition system built from contexts has to say which context is
*the* label of a step, and "smallest that makes the rule fire" is not yet an
answer: smallest among what, and measured how?  Answering it by a choice of
grammar makes the labels an artefact of the presentation.  The answer that is
not an artefact is a universal property, and the one this file formalises is
the relative pushout.

Fix a span `f : W ⟶ X`, `g : W ⟶ Y` — read `f` as the term being observed and
`g` as the redex a rule wants — and a commuting square closing it, `h : X ⟶ Z`
and `i : Y ⟶ Z`.  The square says that the term, placed in the context `h`,
*is* the redex placed in the reaction context `i`.  Call such a square a bound.

A bound can be wasteful: the context may carry material the redex never needed.
A **candidate** is a way of cutting the waste away — a smaller apex the square
already factors through — and a **relative pushout** is a candidate through
which every candidate factors, uniquely.  A bound that is its own relative
pushout wastes nothing, and is called an **idem pushout**.

## Why relative, and not just a pushout

An ordinary pushout is initial among *all* cocones on the span.  A candidate is
a cocone that additionally comes with a map down to `Z`, so candidates are
fewer, and being initial among them is weaker.  `isIdemPushout_of_isPushout`
records the easy half — a pushout is an idem pushout — and the converse fails
in general, which is the entire reason the notion exists: operational theories
have idem pushouts where they have no pushouts at all.

The precise sense of "relative" is made exact by
`isPushout_over_iff_isIdemPushout`: a bound is an idem pushout exactly when the
corresponding square is a pushout **in the slice category over `Z`**.  So the
notion is not a new invention sitting beside the categorical one; it is the
categorical one, taken in the slice where the bound lives.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.RelativePushout

open CategoryTheory CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]
variable {W X Y Z : C}

/-! ## Candidates -/

/-- A **candidate** reduction of the bound `(h, i)` on the span `(f, g)`: a
smaller apex closing the same span, together with the map back down to `Z`
through which the bound factors.  The two factorisation laws are what "smaller"
means — nothing is asserted about size, only that the bound is recovered. -/
structure Candidate (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (i : Y ⟶ Z) where
  /-- The candidate's own apex. -/
  apex : C
  /-- Where the observed term's interface goes. -/
  inl : X ⟶ apex
  /-- Where the redex's interface goes. -/
  inr : Y ⟶ apex
  /-- The map recovering the original bound. -/
  down : apex ⟶ Z
  /-- The candidate closes the span. -/
  comm : f ≫ inl = g ≫ inr
  /-- It recovers the context. -/
  fac_left : inl ≫ down = h
  /-- And the reaction context. -/
  fac_right : inr ≫ down = i

namespace Candidate

variable {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

/-- The bound is a candidate for itself: nothing has been cut away. -/
@[simps]
def self (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (i : Y ⟶ Z) (w : f ≫ h = g ≫ i) :
    Candidate f g h i where
  apex := Z
  inl := h
  inr := i
  down := 𝟙 Z
  comm := w
  fac_left := by simp
  fac_right := by simp

/-- An arrow **mediates** between candidates when it carries one apex to the
other compatibly with both interfaces and with the descent to `Z`. -/
def Mediates (c d : Candidate f g h i) (j : c.apex ⟶ d.apex) : Prop :=
  c.inl ≫ j = d.inl ∧ c.inr ≫ j = d.inr ∧ j ≫ d.down = c.down

/-- One candidate **refines** another when some arrow mediates.  This is the
preorder in which a relative pushout is least. -/
def Refines (c d : Candidate f g h i) : Prop := ∃ j, Mediates c d j

theorem mediates_id (c : Candidate f g h i) : Mediates c c (𝟙 c.apex) := by
  refine ⟨by simp, by simp, by simp⟩

theorem refines_refl (c : Candidate f g h i) : Refines c c :=
  ⟨𝟙 c.apex, mediates_id c⟩

theorem mediates_comp {c d e : Candidate f g h i} {j : c.apex ⟶ d.apex}
    {k : d.apex ⟶ e.apex} (first : Mediates c d j) (second : Mediates d e k) :
    Mediates c e (j ≫ k) := by
  obtain ⟨jl, jr, jd⟩ := first
  obtain ⟨kl, kr, kd⟩ := second
  refine ⟨?_, ?_, ?_⟩
  · rw [← Category.assoc, jl, kl]
  · rw [← Category.assoc, jr, kr]
  · rw [Category.assoc, kd, jd]

theorem refines_trans {c d e : Candidate f g h i}
    (first : Refines c d) (second : Refines d e) : Refines c e := by
  obtain ⟨j, hj⟩ := first
  obtain ⟨k, hk⟩ := second
  exact ⟨j ≫ k, mediates_comp hj hk⟩

end Candidate

/-! ## The universal property -/

variable {f : W ⟶ X} {g : W ⟶ Y} {h : X ⟶ Z} {i : Y ⟶ Z}

/-- **A relative pushout**: a candidate through which every candidate factors,
by exactly one arrow.  It is the least way of closing the span that still
recovers the given bound — least relative to that bound, which is what the word
"relative" carries. -/
def IsRelativePushout (c : Candidate f g h i) : Prop :=
  ∀ d : Candidate f g h i, ∃! j : c.apex ⟶ d.apex, Candidate.Mediates c d j

/-- **An idem pushout**: a bound that is its own relative pushout.  Nothing can
be cut away from it, so it is the label a context-based transition system can
take without choosing one. -/
def IsIdemPushout (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (i : Y ⟶ Z)
    (w : f ≫ h = g ≫ i) : Prop :=
  IsRelativePushout (Candidate.self f g h i w)

/-- A relative pushout refines every candidate, which is the property in the
preorder that the universal property strengthens. -/
theorem IsRelativePushout.refines {c : Candidate f g h i}
    (rpo : IsRelativePushout c) (d : Candidate f g h i) : Candidate.Refines c d :=
  ⟨(rpo d).exists.choose, (rpo d).exists.choose_spec⟩

/-- **Nothing is cut away from an idem pushout.**  Every candidate's descent to
the bound is a split epimorphism: whatever a candidate removes is put straight
back.  This is the content of minimality in a form that does not mention
candidates twice. -/
theorem IsIdemPushout.down_splits {w : f ≫ h = g ≫ i} (ipo : IsIdemPushout f g h i w)
    (d : Candidate f g h i) : ∃ section_ : Z ⟶ d.apex, section_ ≫ d.down = 𝟙 Z := by
  obtain ⟨j, ⟨-, -, descent⟩, -⟩ := ipo d
  exact ⟨j, descent⟩

/-- Two relative pushouts of one bound have isomorphic apices, and the
isomorphism is the mediating arrow.  Leastness therefore determines the label
up to the only ambiguity a universal property ever leaves. -/
theorem IsRelativePushout.unique {c d : Candidate f g h i}
    (first : IsRelativePushout c) (second : IsRelativePushout d) :
    ∃ j : c.apex ⟶ d.apex, ∃ k : d.apex ⟶ c.apex,
      j ≫ k = 𝟙 c.apex ∧ k ≫ j = 𝟙 d.apex := by
  obtain ⟨j, mediatesJ, -⟩ := first d
  obtain ⟨k, mediatesK, -⟩ := second c
  obtain ⟨witnessC, -, uniqueC⟩ := first c
  obtain ⟨witnessD, -, uniqueD⟩ := second d
  refine ⟨j, k, ?_, ?_⟩
  · exact (uniqueC _ (Candidate.mediates_comp mediatesJ mediatesK)).trans
      (uniqueC _ (Candidate.mediates_id c)).symm
  · exact (uniqueD _ (Candidate.mediates_comp mediatesK mediatesJ)).trans
      (uniqueD _ (Candidate.mediates_id d)).symm

/-! ## A pushout is an idem pushout -/

/-- **The easy half of the comparison.**  A pushout is initial among all
cocones, so in particular among the cocones that carry a map down to the bound.
The converse fails, and that failure is the reason the relative notion is
worth having: operational theories routinely have idem pushouts for every
bound while having no pushouts at all. -/
theorem isIdemPushout_of_isPushout (po : IsPushout f g h i) :
    IsIdemPushout f g h i po.w := by
  intro d
  refine ⟨po.desc d.inl d.inr d.comm,
    ⟨po.inl_desc _ _ _, po.inr_desc _ _ _, ?_⟩, ?_⟩
  · refine po.hom_ext ?_ ?_
    · simp [Candidate.self, po.inl_desc_assoc, d.fac_left]
    · simp [Candidate.self, po.inr_desc_assoc, d.fac_right]
  · rintro k ⟨left, right, -⟩
    refine po.hom_ext ?_ ?_
    · rw [po.inl_desc]; exact left
    · rw [po.inr_desc]; exact right

/-! ## A relative pushout's own bound is an idem pushout

This is the step that makes the notion usable: taking the relative pushout of a
bound produces a bound that wastes nothing, so a theory with relative pushouts
has a least label for every reaction it can perform, and the label is determined
up to isomorphism by `IsRelativePushout.unique`. -/

/-- **The bound of a relative pushout is an idem pushout.**  Nothing more can be
cut away from what a relative pushout already cut down to. -/
theorem isIdemPushout_of_isRelativePushout {c : Candidate f g h i}
    (rpo : IsRelativePushout c) : IsIdemPushout f g c.inl c.inr c.comm := by
  intro d
  -- A candidate for `c`'s own bound is a candidate for the original bound,
  -- by composing the two descents.
  let lowered : Candidate f g h i :=
    { apex := d.apex
      inl := d.inl
      inr := d.inr
      down := d.down ≫ c.down
      comm := d.comm
      fac_left := by rw [← Category.assoc, d.fac_left, c.fac_left]
      fac_right := by rw [← Category.assoc, d.fac_right, c.fac_right] }
  obtain ⟨j, ⟨mediatesLeft, mediatesRight, mediatesDown⟩, uniqueJ⟩ := rpo lowered
  refine ⟨j, ⟨mediatesLeft, mediatesRight, ?_⟩, ?_⟩
  · -- `j ≫ d.down` mediates `c` to itself, and so does the identity.
    have mediatesSelf : Candidate.Mediates c c (j ≫ d.down) := by
      refine ⟨?_, ?_, ?_⟩
      · rw [← Category.assoc, mediatesLeft, d.fac_left]
      · rw [← Category.assoc, mediatesRight, d.fac_right]
      · rw [Category.assoc]
        exact mediatesDown
    exact (rpo c).unique mediatesSelf (Candidate.mediates_id c)
  · rintro k ⟨left, right, descent⟩
    refine uniqueJ k ⟨left, right, ?_⟩
    show k ≫ (d.down ≫ c.down) = c.down
    rw [← Category.assoc, descent]
    exact Category.id_comp c.down

/-- **Relative pushouts exist for a span** when every bound on it has one. -/
def HasRelativePushouts (f : W ⟶ X) (g : W ⟶ Y) : Prop :=
  ∀ (apex : C) (h : X ⟶ apex) (i : Y ⟶ apex), f ≫ h = g ≫ i →
    ∃ c : Candidate f g h i, IsRelativePushout c

/-- An ordinary pushout supplies a relative pushout for every bound of its
span. The descent is the pushout's map into the bound, and both the mediator
and compatibility of its descent follow from the same universal property. -/
theorem hasRelativePushouts_of_isPushout {P : C} {inl : X ⟶ P} {inr : Y ⟶ P}
    (po : IsPushout f g inl inr) : HasRelativePushouts f g := by
  intro apex h i square
  let candidate : Candidate f g h i :=
    { apex := P
      inl := inl
      inr := inr
      down := po.desc h i square
      comm := po.w
      fac_left := po.inl_desc h i square
      fac_right := po.inr_desc h i square }
  refine ⟨candidate, ?_⟩
  intro other
  refine ⟨po.desc other.inl other.inr other.comm,
    ⟨po.inl_desc _ _ _, po.inr_desc _ _ _, ?_⟩, ?_⟩
  · change po.desc other.inl other.inr other.comm ≫ other.down = po.desc h i square
    apply po.hom_ext
    · rw [po.inl_desc_assoc, other.fac_left, po.inl_desc]
    · rw [po.inr_desc_assoc, other.fac_right, po.inr_desc]
  · rintro mediator ⟨left, right, -⟩
    apply po.hom_ext
    · exact left.trans (po.inl_desc _ _ _).symm
    · exact right.trans (po.inr_desc _ _ _).symm

/-- A category's chosen ordinary pushout discharges the reactive-system RPO
hypothesis. No restriction to one-object context categories is required. -/
theorem hasRelativePushouts_of_hasPushout [HasPushout f g] :
    HasRelativePushouts f g :=
  hasRelativePushouts_of_isPushout (IsPushout.of_hasPushout f g)

/-- **So every bound reduces to an idem pushout.**  A theory with relative
pushouts has a least label for every reaction it can perform: the bound the
reaction presents factors through one that wastes nothing.  This is the property
a context-labelled transition system needs before it can choose its labels at
all. -/
theorem exists_idemPushout_below (hasRPO : HasRelativePushouts f g)
    (w : f ≫ h = g ≫ i) :
    ∃ c : Candidate f g h i, IsIdemPushout f g c.inl c.inr c.comm :=
  let ⟨c, rpo⟩ := hasRPO Z h i w
  ⟨c, isIdemPushout_of_isRelativePushout rpo⟩

/-- And the reduction is a genuine factorisation: the original bound is the
least one composed with the residual. -/
theorem idemPushout_below_factors (hasRPO : HasRelativePushouts f g)
    (w : f ≫ h = g ≫ i) :
    ∃ c : Candidate f g h i, IsIdemPushout f g c.inl c.inr c.comm ∧
      c.inl ≫ c.down = h ∧ c.inr ≫ c.down = i :=
  let ⟨c, rpo⟩ := hasRPO Z h i w
  ⟨c, isIdemPushout_of_isRelativePushout rpo, c.fac_left, c.fac_right⟩

/-- A bound that is already an idem pushout is its own reduction, so the two
notions agree where they overlap. -/
theorem isRelativePushout_self_of_isIdemPushout (w : f ≫ h = g ≫ i)
    (ipo : IsIdemPushout f g h i w) :
    IsRelativePushout (Candidate.self f g h i w) := ipo

/-! ## An idem pushout survives post-composition

The step the pasting argument turns on.  An idem pushout is least for its own
bound; post-composing both legs with a further context gives a bigger bound, and
the question is whether it is still least for *that*.  It is — when relative
pushouts exist — and the proof is the standard retract argument: the relative
pushout of the bigger bound and the idem pushout are mutually mediating, hence
isomorphic. -/

/-- **An idem pushout, post-composed, is a relative pushout of the larger
bound.**  So nothing is gained by looking at a reaction through a bigger
context: the label stays the one the redex determined. -/
theorem isRelativePushout_postcompose {Z' : C} (e : Z ⟶ Z')
    (hasRPO : HasRelativePushouts f g) (w : f ≫ h = g ≫ i)
    (ipo : IsIdemPushout f g h i w) :
    IsRelativePushout
      ({ apex := Z, inl := h, inr := i, down := e, comm := w
         fac_left := rfl, fac_right := rfl } : Candidate f g (h ≫ e) (i ≫ e)) := by
  obtain ⟨big, bigRPO⟩ := hasRPO Z' (h ≫ e) (i ≫ e) (by rw [← Category.assoc, w, Category.assoc])
  -- The idem pushout is a candidate for the larger bound, so the larger
  -- relative pushout mediates into it.
  obtain ⟨down, ⟨downLeft, downRight, downFac⟩, -⟩ :=
    bigRPO { apex := Z, inl := h, inr := i, down := e, comm := w
             fac_left := rfl, fac_right := rfl }
  -- And the larger relative pushout is a candidate for the idem pushout's own
  -- bound, so the idem pushout mediates back.
  obtain ⟨up, ⟨upLeft, upRight, upFac⟩, -⟩ :=
    ipo { apex := big.apex, inl := big.inl, inr := big.inr, down := down
          comm := big.comm, fac_left := downLeft, fac_right := downRight }
  let downZ : big.apex ⟶ Z := down
  let upZ : Z ⟶ big.apex := up
  have downLeft' : big.inl ≫ downZ = h := downLeft
  have downRight' : big.inr ≫ downZ = i := downRight
  have downFac' : downZ ≫ e = big.down := downFac
  have upLeft' : h ≫ upZ = big.inl := upLeft
  have upRight' : i ≫ upZ = big.inr := upRight
  have upFac' : upZ ≫ downZ = 𝟙 Z := upFac
  intro d
  obtain ⟨mediator, ⟨mediatorLeft, mediatorRight, mediatorFac⟩, mediatorUnique⟩ := bigRPO d
  refine ⟨upZ ≫ mediator, ⟨?_, ?_, ?_⟩, ?_⟩
  · show h ≫ (upZ ≫ mediator) = d.inl
    rw [← Category.assoc, upLeft', mediatorLeft]
  · show i ≫ (upZ ≫ mediator) = d.inr
    rw [← Category.assoc, upRight', mediatorRight]
  · show (upZ ≫ mediator) ≫ d.down = e
    rw [Category.assoc, mediatorFac, ← downFac', ← Category.assoc, upFac',
      Category.id_comp]
  · rintro other ⟨otherLeft, otherRight, otherFac⟩
    have otherLeft' : h ≫ other = d.inl := otherLeft
    have otherRight' : i ≫ other = d.inr := otherRight
    have otherFac' : other ≫ d.down = e := otherFac
    have factored : downZ ≫ other = mediator := by
      refine mediatorUnique (downZ ≫ other) ⟨?_, ?_, ?_⟩
      · rw [← Category.assoc, downLeft']; exact otherLeft'
      · rw [← Category.assoc, downRight']; exact otherRight'
      · rw [Category.assoc, otherFac']; exact downFac'
    show other = upZ ≫ mediator
    rw [← factored, ← Category.assoc, upFac', Category.id_comp]

/-! ## Pasting

Two squares side by side: a reaction least for its redex at a term, and a
context placed around it that is least for that label.  Pasting says the
composite is least for the same redex at the term in the enlarged context —
which is the property a context-labelled transition relation needs in place of
the composition law that cannot hold. -/

/-- **Idem pushouts paste.**  If the inner square is least for its redex and the
outer square is least for the inner label, the composite is least for that redex
at the composed term.  Relative pushouts for the inner span are what make the
two squares talk to each other. -/
theorem isIdemPushout_paste {interface source redexSort mid outerSort top : C}
    (term : interface ⟶ source) (redex : interface ⟶ redexSort)
    (innerLabel : source ⟶ mid) (reaction : redexSort ⟶ mid)
    (context : source ⟶ outerSort) (outerLabel : outerSort ⟶ top)
    (residual : mid ⟶ top)
    (wInner : term ≫ innerLabel = redex ≫ reaction)
    (wOuter : context ≫ outerLabel = innerLabel ≫ residual)
    (hasRPO : HasRelativePushouts term redex)
    (innerIPO : IsIdemPushout term redex innerLabel reaction wInner)
    (outerIPO : IsIdemPushout context innerLabel outerLabel residual wOuter) :
    IsIdemPushout (term ≫ context) redex outerLabel (reaction ≫ residual)
      (by rw [Category.assoc, wOuter, ← Category.assoc, wInner, Category.assoc]) := by
  have postcomposed := isRelativePushout_postcompose residual hasRPO wInner innerIPO
  intro d
  have dComm : (term ≫ context) ≫ d.inl = redex ≫ d.inr := d.comm
  have dLeft : d.inl ≫ d.down = outerLabel := d.fac_left
  have dRight : d.inr ≫ d.down = reaction ≫ residual := d.fac_right
  -- The composite candidate, read as a candidate for the inner span's enlarged
  -- bound.
  let innerCandidate : Candidate term redex (innerLabel ≫ residual) (reaction ≫ residual) :=
    { apex := d.apex
      inl := context ≫ d.inl
      inr := d.inr
      down := d.down
      comm := by rw [← Category.assoc]; exact dComm
      fac_left := by rw [Category.assoc, dLeft]; exact wOuter
      fac_right := dRight }
  obtain ⟨residualMediator, ⟨innerLeft, innerRight, innerDown⟩, innerUnique⟩ :=
    postcomposed innerCandidate
  let residualMid : mid ⟶ d.apex := residualMediator
  have innerLeft' : innerLabel ≫ residualMid = context ≫ d.inl := innerLeft
  have innerRight' : reaction ≫ residualMid = d.inr := innerRight
  have innerDown' : residualMid ≫ d.down = residual := innerDown
  -- Which makes the composite candidate a candidate for the outer square.
  let outerCandidate : Candidate context innerLabel outerLabel residual :=
    { apex := d.apex
      inl := d.inl
      inr := residualMid
      down := d.down
      comm := innerLeft'.symm
      fac_left := dLeft
      fac_right := innerDown' }
  obtain ⟨mediator, ⟨outerLeft, outerRight, outerDown⟩, outerUnique⟩ := outerIPO outerCandidate
  let mediatorTop : top ⟶ d.apex := mediator
  have outerLeft' : outerLabel ≫ mediatorTop = d.inl := outerLeft
  have outerRight' : residual ≫ mediatorTop = residualMid := outerRight
  have outerDown' : mediatorTop ≫ d.down = 𝟙 top := outerDown
  refine ⟨mediatorTop, ⟨outerLeft', ?_, outerDown'⟩, ?_⟩
  · show (reaction ≫ residual) ≫ mediatorTop = d.inr
    rw [Category.assoc, outerRight']
    exact innerRight'
  · rintro other ⟨otherLeft, otherRight, otherDown⟩
    let otherTop : top ⟶ d.apex := other
    have otherLeft' : outerLabel ≫ otherTop = d.inl := otherLeft
    have otherRight' : (reaction ≫ residual) ≫ otherTop = d.inr := otherRight
    have otherDown' : otherTop ≫ d.down = 𝟙 top := otherDown
    -- `residual ≫ other` mediates the enlarged inner bound, so it is the one
    -- the inner square already named.
    have residualFactored : residual ≫ otherTop = residualMid := by
      refine innerUnique (residual ≫ otherTop) ⟨?_, ?_, ?_⟩
      · show innerLabel ≫ (residual ≫ otherTop) = context ≫ d.inl
        rw [← Category.assoc, ← wOuter, Category.assoc, otherLeft']
      · show reaction ≫ (residual ≫ otherTop) = d.inr
        rw [← Category.assoc]; exact otherRight'
      · show (residual ≫ otherTop) ≫ d.down = residual
        rw [Category.assoc, otherDown', Category.comp_id]
    show otherTop = mediatorTop
    exact outerUnique otherTop ⟨otherLeft', residualFactored, otherDown'⟩

/-- **The residual square of a relative pushout is an idem pushout.**  Reducing
a bound produces two squares: the reduced one, and the residual that puts the
context back.  If the original was least, so is the residual — which is the
second half of what pasting needs, and the half that lets a step out of a filled
context be read as a step out of its filling. -/
theorem isIdemPushout_residual {interface source redexSort outerSort top : C}
    (term : interface ⟶ source) (redex : interface ⟶ redexSort)
    (context : source ⟶ outerSort) (outerLabel : outerSort ⟶ top)
    (reaction : redexSort ⟶ top)
    (wComposite : (term ≫ context) ≫ outerLabel = redex ≫ reaction)
    (compositeIPO : IsIdemPushout (term ≫ context) redex outerLabel reaction wComposite)
    (c : Candidate term redex (context ≫ outerLabel) reaction)
    (rpo : IsRelativePushout c) :
    IsIdemPushout context c.inl outerLabel c.down c.fac_left.symm := by
  intro d
  have dComm : context ≫ d.inl = c.inl ≫ d.inr := d.comm
  have dLeft : d.inl ≫ d.down = outerLabel := d.fac_left
  have dRight : d.inr ≫ d.down = c.down := d.fac_right
  -- The candidate, read for the composite bound.
  let compositeCandidate :
      Candidate (term ≫ context) redex outerLabel reaction :=
    { apex := d.apex
      inl := d.inl
      inr := c.inr ≫ d.inr
      down := d.down
      comm := by
        rw [Category.assoc, dComm, ← Category.assoc, ← Category.assoc]
        exact congrArg (· ≫ d.inr) c.comm
      fac_left := dLeft
      fac_right := by rw [Category.assoc, dRight]; exact c.fac_right }
  obtain ⟨mediator, ⟨mediatorLeft, mediatorRight, mediatorDown⟩, mediatorUnique⟩ :=
    compositeIPO compositeCandidate
  let mediatorTop : top ⟶ d.apex := mediator
  have mediatorLeft' : outerLabel ≫ mediatorTop = d.inl := mediatorLeft
  have mediatorRight' : reaction ≫ mediatorTop = c.inr ≫ d.inr := mediatorRight
  have mediatorDown' : mediatorTop ≫ d.down = 𝟙 top := mediatorDown
  -- The residual composed with it mediates the reduced bound, and so does the
  -- candidate's own right leg, so the two agree.
  let reduced : Candidate term redex (context ≫ outerLabel) reaction :=
    { apex := d.apex
      inl := context ≫ d.inl
      inr := c.inr ≫ d.inr
      down := d.down
      comm := by
        rw [← Category.assoc]
        exact compositeCandidate.comm
      fac_left := by rw [Category.assoc, dLeft]
      fac_right := by rw [Category.assoc, dRight]; exact c.fac_right }
  have residualAgrees : c.down ≫ mediatorTop = d.inr := by
    obtain ⟨reducedMediator, -, reducedUnique⟩ := rpo reduced
    have viaResidual : Candidate.Mediates c reduced (c.down ≫ mediatorTop) := by
      refine ⟨?_, ?_, ?_⟩
      · show c.inl ≫ (c.down ≫ mediatorTop) = context ≫ d.inl
        rw [← Category.assoc, c.fac_left, Category.assoc, mediatorLeft']
      · show c.inr ≫ (c.down ≫ mediatorTop) = c.inr ≫ d.inr
        rw [← Category.assoc, c.fac_right, mediatorRight']
      · show (c.down ≫ mediatorTop) ≫ d.down = c.down
        rw [Category.assoc, mediatorDown', Category.comp_id]
    have viaCandidate : Candidate.Mediates c reduced d.inr := by
      refine ⟨dComm.symm, rfl, dRight⟩
    exact (reducedUnique _ viaResidual).trans (reducedUnique _ viaCandidate).symm
  refine ⟨mediatorTop, ⟨mediatorLeft', residualAgrees, mediatorDown'⟩, ?_⟩
  rintro other ⟨otherLeft, otherRight, otherDown⟩
  let otherTop : top ⟶ d.apex := other
  have otherLeft' : outerLabel ≫ otherTop = d.inl := otherLeft
  have otherRight' : c.down ≫ otherTop = d.inr := otherRight
  have otherDown' : otherTop ≫ d.down = 𝟙 top := otherDown
  show otherTop = mediatorTop
  refine mediatorUnique otherTop ⟨otherLeft', ?_, otherDown'⟩
  show reaction ≫ otherTop = c.inr ≫ d.inr
  calc reaction ≫ otherTop
      = (c.inr ≫ c.down) ≫ otherTop := by rw [c.fac_right]
    _ = c.inr ≫ (c.down ≫ otherTop) := Category.assoc _ _ _
    _ = c.inr ≫ d.inr := by rw [otherRight']

/-! ## The slice presentation

The relative notion is the absolute one, taken where the bound lives.  Below,
the bound's square is transported into the slice category over `Z`, and being
an idem pushout is proved to be exactly being a pushout there. -/

/-- The observed term's leg, in the slice over `Z`. -/
def overSpanLeft (f : W ⟶ X) (h : X ⟶ Z) : Over.mk (f ≫ h) ⟶ Over.mk h :=
  Over.homMk f rfl

/-- The redex's leg, in the slice over `Z`. -/
def overSpanRight (f : W ⟶ X) (g : W ⟶ Y) (h : X ⟶ Z) (i : Y ⟶ Z)
    (w : f ≫ h = g ≫ i) : Over.mk (f ≫ h) ⟶ Over.mk i :=
  Over.homMk g w.symm

/-- The context, in the slice over `Z`. -/
def overInl (h : X ⟶ Z) : Over.mk h ⟶ Over.mk (𝟙 Z) :=
  Over.homMk h (by simp)

/-- The reaction context, in the slice over `Z`. -/
def overInr (i : Y ⟶ Z) : Over.mk i ⟶ Over.mk (𝟙 Z) :=
  Over.homMk i (by simp)

/-- A cocone of the slice square is a candidate: its apex carries a map down to
`Z` by being an object over `Z`, and that map is the descent. -/
def sliceCandidate (w : f ≫ h = g ≫ i)
    (s : PushoutCocone (overSpanLeft f h) (overSpanRight f g h i w)) :
    Candidate f g h i where
  apex := s.pt.left
  inl := s.inl.left
  inr := s.inr.left
  down := s.pt.hom
  comm := by
    have underlying := congrArg CommaMorphism.left s.condition
    simpa [overSpanLeft, overSpanRight] using underlying
  fac_left := Over.w s.inl
  fac_right := Over.w s.inr

/-- The slice square commutes, which is the bound restated over `Z`. -/
theorem overSq (w : f ≫ h = g ≫ i) :
    overSpanLeft f h ≫ overInl h = overSpanRight f g h i w ≫ overInr i := by
  ext
  exact w

/-- A candidate gives a cocone of the slice square. -/
def overCocone (d : Candidate f g h i) :
    (Over.mk h ⟶ Over.mk d.down) × (Over.mk i ⟶ Over.mk d.down) :=
  (Over.homMk d.inl d.fac_left, Over.homMk d.inr d.fac_right)

/-- **The relative notion is the absolute one in the slice.**  A bound is an
idem pushout exactly when its square is a pushout over `Z`.  Nothing here is a
new definition: it is the ordinary universal property, read in the category
where a bound is an object rather than a diagram. -/
theorem isPushout_over_iff_isIdemPushout (w : f ≫ h = g ≫ i) :
    IsPushout (overSpanLeft f h) (overSpanRight f g h i w) (overInl h) (overInr i) ↔
      IsIdemPushout f g h i w := by
  constructor
  · intro po d
    have cocondition :
        overSpanLeft f h ≫ (overCocone d).1 =
          overSpanRight f g h i w ≫ (overCocone d).2 := by
      ext
      exact d.comm
    have leftFac := po.inl_desc (overCocone d).1 (overCocone d).2 cocondition
    have rightFac := po.inr_desc (overCocone d).1 (overCocone d).2 cocondition
    refine ⟨(po.desc (overCocone d).1 (overCocone d).2 cocondition).left,
      ⟨congrArg CommaMorphism.left leftFac, congrArg CommaMorphism.left rightFac,
        Over.w _⟩, ?_⟩
    rintro k ⟨left, right, descent⟩
    have mediating : (Over.homMk k descent : Over.mk (𝟙 Z) ⟶ Over.mk d.down) =
        po.desc (overCocone d).1 (overCocone d).2 cocondition := by
      refine po.hom_ext ?_ ?_
      · ext; exact left.trans (congrArg CommaMorphism.left leftFac).symm
      · ext; exact right.trans (congrArg CommaMorphism.left rightFac).symm
    exact congrArg CommaMorphism.left mediating
  · intro ipo
    refine IsPushout.of_isColimit
      (PushoutCocone.IsColimit.mk (overSq w) ?_ ?_ ?_ ?_)
    · intro s
      exact Over.homMk (ipo (sliceCandidate w s)).exists.choose
        (ipo (sliceCandidate w s)).exists.choose_spec.2.2
    · intro s
      ext
      exact (ipo (sliceCandidate w s)).exists.choose_spec.1
    · intro s
      ext
      exact (ipo (sliceCandidate w s)).exists.choose_spec.2.1
    · intro s m left right
      ext
      refine (ipo (sliceCandidate w s)).unique ?_
        (ipo (sliceCandidate w s)).exists.choose_spec
      exact ⟨congrArg CommaMorphism.left left, congrArg CommaMorphism.left right,
        Over.w m⟩

end Mettapedia.GSLT.RelativePushout
