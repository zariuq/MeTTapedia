import Mettapedia.OSLF.Framework.GeneratedModality
import Mettapedia.OSLF.Framework.DerivedModalities
import Mettapedia.OSLF.Syntax.BindingSignature
import Mettapedia.GSLT.Meredith.Modal.RewriteModality

/-!
# One rely-possibly modality, three carriers

The rely-possibly modality of the generated type system is defined three times
in this development, on three different carriers, by three groups of
declarations that share their names:

* `Mettapedia/GSLT/Meredith/Modal/RewriteModality.lean` — over a lambda theory,
  as an existential over reducts of the filled context;
* `Mettapedia/OSLF/Syntax/BindingSignature.lean` — over intrinsically scoped
  closed terms, as a universal over rely environments yielding a rule instance;
* `Mettapedia/OSLF/Framework/GeneratedModality.lean` — over untyped patterns, as
  a universal over bindings guarded by rule firing.

They are not re-exports of one another, and the first does not even have the
same quantifier shape as the other two.  This module supplies the missing
agreement: **all three are the same construction at three choices of index,**
and the construction is a familiar one.

## The abstraction

Write `Fit w e t` for "the witness `w` fits the environment `e` with `t` at the
chosen position", and `out w` for what the witness produces.  Then each of the
three modalities is

  `modality rely B t  =  ∀ e, rely e → ∃ w, Fit w e t ∧ B (out w)`.

Reading the existential as a relational direct image, this is

  `modality rely B t  ↔  ∀ e, rely e → ⟨step e⟩ B t`,

a **meet, over the admissible environments, of relational diamonds** — where
`step e` is the relation "placing `t` here, under `e`, produces this output".
`modality_iff_diamond` proves the equivalence.

That identification is what carries the laws.  The diamond `⟨R⟩` is change of
base along the span of `R`'s steps, `∃_source ∘ target*`, so it is the left
adjoint of `∀_target ∘ source*` by composing the change-of-base adjunctions
(`diamond_galois`); on a single type it is literally the derived step-future
modality (`diamond_eq_derivedDiamond`).  Being a left adjoint it is monotone and
preserves arbitrary joins (`diamond_mono`, `diamond_exists`).  The
modality inherits monotonicity in its target, antitonicity in its rely
assumptions, and the conversion of a disjunction of rely conditions into a
conjunction of modalities — proved once here, and then instantiated at each of
the three carriers.

## What the three carriers differ in, exactly

Only in the index.  The lambda-theory presentation takes `Env := Unit`: it is
the **rely-free** instance, and that is why it looks existential where the other
two look universal.  The distinction is not cosmetic, and it is not a defect of
either side:

* at a rely-free (or otherwise subsingleton) index the modality *is* a single
  diamond, hence a left adjoint, hence preserves joins of targets
  (`modality_iff_diamond_of_subsingleton`);
* at a genuine index it does not — `join_not_preserved` exhibits a frame, a term
  and two targets where the modality holds of their disjunction and of neither
  disjunct.

So the rely-free carrier satisfies a law the rely-indexed carriers provably fail.
Reading a result about one as a result about another is unsound in that precise
direction, and sound in the direction the instance theorems record.

A second difference of the same kind concerns vacuity.  With no admissible
environment the modality holds of everything, target predicate notwithstanding
(`modality_of_no_admissible`); the rely-free instance can never be in that
situation, because its index is inhabited and its rely condition is `True`.  The
scoped presentation's choice to index by rely environments rather than by
arbitrary closing substitutions is exactly a defence against this, and
`target_need_not_be_load_bearing` is the failure it defends against.

## Transport between carriers

`FrameMorphism` is a map of frames: covariant in carriers, outputs and witnesses,
and **contravariant in the index**, because the modality quantifies universally
over environments.  `FrameMorphism.modality_map` transports the modality along
one.  `transport_is_directed` exhibits a map along which the target satisfies a
modality the source refutes, so transport is a one-way street and identifying the
three presentations as instances is not the same as identifying the modalities.

The agreement still missing is a concrete map between the two rely-indexed
frames.  What it needs is now exactly stated by the structure: a function on
patterns, a function from binding lists back to rely environments, and a function
from rule instances to decomposition-and-step pairs, such that fitting and
production are preserved.

## Status of the identification

`categorical_is_instance`, `pattern_is_instance` and `scoped_is_instance` are
the three bridges, each an `Iff` against the existing definition; none holds by
`rfl`, since the three differ from the scheme by currying, by associativity of
conjunction, and by the collapse of a quantifier over `Unit`.  The `example`
blocks that follow each bridge re-derive that carrier's own published laws from
the scheme's, with the statements copied unchanged, so the claim that the
abstraction suffices is checked by the compiler rather than asserted.
-/

namespace Mettapedia.OSLF.Framework.RelyPossiblyScheme

universe u v w x

/-! ## The relational diamond -/

open Mettapedia.OSLF.Framework.DerivedModalities (pb di ui di_pb_adj pb_ui_adj derivedDiamond
  derivedBox derived_galois)

/-- The steps of a relation: its related pairs.  Their two projections form the
span along which the relation's modalities are change of base. -/
def RelationStep {X : Type u} {Y : Type w} (R : X → Y → Prop) : Type (max u w) :=
  {pair : X × Y // R pair.1 pair.2}

/-- Existential quantification along a relation, `∃_source ∘ target*` over the
span of its steps: `diamond R B` holds of `t` when some `R`-output of `t`
satisfies `B`.  Every modality below is built from it. -/
def diamond {X : Type u} {Y : Type w} (R : X → Y → Prop) (B : Y → Prop) : X → Prop :=
  di (fun step : RelationStep R => step.1.1) (pb (fun step : RelationStep R => step.1.2) B)

/-- The right adjoint of `diamond R`, `∀_target ∘ source*`: `boxInv R C` holds of
an output when every input producing it satisfies `C`. -/
def boxInv {X : Type u} {Y : Type w} (R : X → Y → Prop) (C : X → Prop) : Y → Prop :=
  ui (fun step : RelationStep R => step.1.2) (pb (fun step : RelationStep R => step.1.1) C)

theorem diamond_iff {X : Type u} {Y : Type w} (R : X → Y → Prop) (B : Y → Prop) (t : X) :
    diamond R B t ↔ ∃ o, R t o ∧ B o := by
  constructor
  · rintro ⟨⟨⟨_, o⟩, related⟩, rfl, holds⟩
    exact ⟨o, related, holds⟩
  · rintro ⟨o, related, holds⟩
    exact ⟨⟨(t, o), related⟩, rfl, holds⟩

theorem boxInv_iff {X : Type u} {Y : Type w} (R : X → Y → Prop) (C : X → Prop) (o : Y) :
    boxInv R C o ↔ ∀ t, R t o → C t := by
  constructor
  · intro holds t related
    exact holds ⟨(t, o), related⟩ rfl
  · rintro holds ⟨⟨t, _⟩, related⟩ rfl
    exact holds t related

/-- **The diamond is a left adjoint**, by composing the change-of-base
adjunctions `∃_source ⊣ source*` and `target* ⊣ ∀_target`. -/
theorem diamond_galois {X : Type u} {Y : Type w} (R : X → Y → Prop) :
    GaloisConnection (diamond R) (boxInv R) := fun _ _ =>
  (di_pb_adj _ _ _).trans (pb_ui_adj _ _ _)

/-- On a single type, the diamond is the derived step-future modality of the span
of the relation's steps, and its adjoint the derived step-past modality. -/
theorem diamond_eq_derivedDiamond {X : Type u} (R : X → X → Prop) :
    diamond R = derivedDiamond ⟨RelationStep R, fun step => step.1.1, fun step => step.1.2⟩ :=
  rfl

theorem boxInv_eq_derivedBox {X : Type u} (R : X → X → Prop) :
    boxInv R = derivedBox ⟨RelationStep R, fun step => step.1.1, fun step => step.1.2⟩ :=
  rfl

/-- The adjunction, spelled out on predicates. -/
theorem diamond_adjunction {X : Type u} {Y : Type w} (R : X → Y → Prop)
    (B : Y → Prop) (C : X → Prop) :
    (∀ t, diamond R B t → C t) ↔ (∀ o, B o → boxInv R C o) :=
  diamond_galois R B C

/-- Monotone in the target, as a left adjoint must be. -/
theorem diamond_mono {X : Type u} {Y : Type w} {R : X → Y → Prop}
    {B C : Y → Prop} (hBC : ∀ o, B o → C o) {t : X}
    (h : diamond R B t) : diamond R C t :=
  (diamond_galois R).monotone_l hBC t h

/-- And it preserves arbitrary joins, which is the part a mere monotone map does
not give.  Used below to separate the rely-free carrier from the others. -/
theorem diamond_exists {X : Type u} {Y : Type w} {ι : Type v} {R : X → Y → Prop}
    (Bs : ι → Y → Prop) (t : X) :
    diamond R (fun o => ∃ i, Bs i o) t ↔ ∃ i, diamond R (Bs i) t := by
  have joins := congrFun ((diamond_galois R).l_iSup (f := Bs)) t
  simp only [iSup_apply, iSup_Prop_eq] at joins
  exact (iff_of_eq (congrArg (fun B => diamond R B t) (funext fun o => by simp))).trans
    (iff_of_eq joins)

/-- The empty target is not reachable: nothing has an `R`-output satisfying a
predicate nothing satisfies. -/
theorem not_diamond_of_target_empty {X : Type u} {Y : Type w} (R : X → Y → Prop)
    {B : Y → Prop} (hB : ∀ o, ¬ B o) (t : X) : ¬ diamond R B t := by
  have empty : B = ⊥ := funext fun o => eq_false (hB o)
  rw [empty, (diamond_galois R).l_bot]
  exact id

/-! ## The scheme -/

set_option linter.checkUnivs false in
/-- The data a rely-possibly modality needs, stripped of any carrier: what the
modality is a predicate on, what it is indexed by, what its existential ranges
over, how a witness fits an index, and what a witness produces.

Nothing here mentions terms, patterns, bindings, rewriting or binding structure.
Each of the three carriers supplies these five components and nothing else.

The four component types are independently universe-polymorphic because the
three carriers place them differently: the pattern presentation puts all four at
the bottom, while the lambda-theory presentation puts two of them at the
category's hom universe.  That is why they occur only inside one `max`. -/
structure RelyFrame where
  /-- What the modality is a predicate on: the carrier of the chosen hole. -/
  Carrier : Type u
  /-- What the modality is indexed by: the rely environments. -/
  Env : Type v
  /-- Where the target predicate lives. -/
  Out : Type w
  /-- What the existential ranges over. -/
  Wit : Type x
  /-- When a witness fits an environment, with the given term at the hole. -/
  Fit : Wit → Env → Carrier → Prop
  /-- What a witness produces. -/
  out : Wit → Out

namespace RelyFrame

/-- The relation a frame induces at a fixed environment: "placing `t` at the
hole under `e` produces `o`".  The modality is assembled from these. -/
def step (F : RelyFrame) (e : F.Env) (t : F.Carrier) (o : F.Out) : Prop :=
  ∃ wit : F.Wit, F.Fit wit e t ∧ F.out wit = o

/-- **The rely-possibly modality.**  Under every admissible environment, some
witness fits and produces an output the target accepts. -/
def modality (F : RelyFrame) (rely : F.Env → Prop) (B : F.Out → Prop)
    (t : F.Carrier) : Prop :=
  ∀ e : F.Env, rely e → ∃ wit : F.Wit, F.Fit wit e t ∧ B (F.out wit)

/-- **The identification.**  The modality is the meet, over admissible
environments, of the diamonds of the induced relations. -/
theorem modality_iff_diamond (F : RelyFrame) (rely : F.Env → Prop)
    (B : F.Out → Prop) (t : F.Carrier) :
    F.modality rely B t ↔ ∀ e : F.Env, rely e → diamond (F.step e) B t := by
  simp only [diamond_iff]
  constructor
  · intro h e he
    obtain ⟨wit, hfit, hB⟩ := h e he
    exact ⟨F.out wit, ⟨wit, hfit, rfl⟩, hB⟩
  · intro h e he
    obtain ⟨o, ⟨wit, hfit, hout⟩, hB⟩ := h e he
    subst hout
    exact ⟨wit, hfit, hB⟩

/-- Monotone in the target, inherited from the diamond. -/
theorem modality_mono_target (F : RelyFrame) {rely : F.Env → Prop}
    {B C : F.Out → Prop} (hBC : ∀ o, B o → C o) {t : F.Carrier}
    (h : F.modality rely B t) : F.modality rely C t := by
  rw [modality_iff_diamond] at h ⊢
  exact fun e he => diamond_mono hBC (h e he)

/-- Antitone in the rely assumptions: a meet over a smaller index set is
weaker, so strengthening what one relies on makes the specification easier. -/
theorem modality_antitone_rely (F : RelyFrame) {rely rely' : F.Env → Prop}
    (hr : ∀ e, rely' e → rely e) {B : F.Out → Prop} {t : F.Carrier}
    (h : F.modality rely B t) : F.modality rely' B t :=
  fun e he => h e (hr e he)

/-- Rely conditions with the same extension give the same modality. -/
theorem modality_congr_rely (F : RelyFrame) {rely rely' : F.Env → Prop}
    (hr : ∀ e, rely e ↔ rely' e) {B : F.Out → Prop} {t : F.Carrier} :
    F.modality rely B t ↔ F.modality rely' B t :=
  ⟨modality_antitone_rely F (fun e he => (hr e).mpr he),
    modality_antitone_rely F (fun e he => (hr e).mp he)⟩

/-- A meet over a union of index sets splits, which is the indexed-meet law the
identification above predicts. -/
theorem modality_or_rely (F : RelyFrame) {rely₁ rely₂ : F.Env → Prop}
    {B : F.Out → Prop} {t : F.Carrier} :
    F.modality (fun e => rely₁ e ∨ rely₂ e) B t ↔
      F.modality rely₁ B t ∧ F.modality rely₂ B t := by
  constructor
  · intro h
    exact ⟨fun e he => h e (Or.inl he), fun e he => h e (Or.inr he)⟩
  · rintro ⟨h₁, h₂⟩ e (he | he)
    · exact h₁ e he
    · exact h₂ e he

/-- **Vacuity.**  With no admissible environment the modality holds of
everything, whatever the target.  This is the failure mode an over-large
environment type invites. -/
theorem modality_of_no_admissible (F : RelyFrame) {rely : F.Env → Prop}
    (hempty : ∀ e, ¬ rely e) (B : F.Out → Prop) (t : F.Carrier) :
    F.modality rely B t :=
  fun e he => absurd he (hempty e)

/-- **And the target is load-bearing as soon as one environment is
admissible.**  The converse guard to the previous result. -/
theorem not_modality_of_target_empty (F : RelyFrame) {rely : F.Env → Prop}
    (e : F.Env) (he : rely e) {B : F.Out → Prop} (hB : ∀ o, ¬ B o)
    (t : F.Carrier) : ¬ F.modality rely B t := by
  intro h
  obtain ⟨wit, -, hBo⟩ := h e he
  exact hB _ hBo

/-- At a subsingleton index with one admissible environment the modality *is* a
single diamond.  This is where the rely-free carrier sits, and it is why that
carrier enjoys the join law the others do not. -/
theorem modality_iff_diamond_of_subsingleton (F : RelyFrame)
    {rely : F.Env → Prop} (e₀ : F.Env) (he₀ : rely e₀)
    (hsub : ∀ e, rely e → e = e₀) (B : F.Out → Prop) (t : F.Carrier) :
    F.modality rely B t ↔ diamond (F.step e₀) B t := by
  rw [modality_iff_diamond]
  constructor
  · intro h
    exact h e₀ he₀
  · intro h e he
    have : e = e₀ := hsub e he
    subst this
    exact h

/-- Joins of targets always pass **into** the modality. -/
theorem modality_of_exists (F : RelyFrame) {rely : F.Env → Prop} {ι : Type v}
    {Bs : ι → F.Out → Prop} {t : F.Carrier} (h : ∃ i, F.modality rely (Bs i) t) :
    F.modality rely (fun o => ∃ i, Bs i o) t := by
  obtain ⟨i, hi⟩ := h
  exact modality_mono_target F (fun o hB => ⟨i, hB⟩) hi

end RelyFrame

/-! ## Maps of frames, and what transport along one requires

A result proved at one carrier reaches another along a map of frames, and only
along one.  The maps are covariant in what a frame produces and **contravariant
in what it is indexed by**, because the modality quantifies universally over the
index: to conclude something under every environment of the target, one needs
every target environment to come from a source environment. -/

/-- A map of frames.  Note the direction of `onEnv`. -/
structure FrameMorphism (F G : RelyFrame) where
  /-- Where the inhabitants go. -/
  onCarrier : F.Carrier → G.Carrier
  /-- Where the target's environments come from. -/
  onEnv : G.Env → F.Env
  /-- Where the outputs go. -/
  onOut : F.Out → G.Out
  /-- Where the witnesses go. -/
  onWit : F.Wit → G.Wit
  /-- Fitting is preserved. -/
  fit : ∀ (wit : F.Wit) (e : G.Env) (t : F.Carrier),
    F.Fit wit (onEnv e) t → G.Fit (onWit wit) e (onCarrier t)
  /-- And so is what a witness produces. -/
  out : ∀ wit : F.Wit, G.out (onWit wit) = onOut (F.out wit)

namespace FrameMorphism

/-- The identity map of frames. -/
def id (F : RelyFrame) : FrameMorphism F F where
  onCarrier := _root_.id
  onEnv := _root_.id
  onOut := _root_.id
  onWit := _root_.id
  fit := fun _ _ _ h => h
  out := fun _ => rfl

/-- Maps of frames compose, with the index map composing the other way. -/
def comp {F G H : RelyFrame} (f : FrameMorphism F G) (g : FrameMorphism G H) :
    FrameMorphism F H where
  onCarrier := g.onCarrier ∘ f.onCarrier
  onEnv := f.onEnv ∘ g.onEnv
  onOut := g.onOut ∘ f.onOut
  onWit := g.onWit ∘ f.onWit
  fit := fun wit e t h => g.fit _ e _ (f.fit wit (g.onEnv e) t h)
  out := fun wit => by
    simp only [Function.comp_apply, g.out, f.out]

/-- **Transport.**  A map of frames carries the modality forward, provided the
target's rely condition implies the source's along the index map and the
target's predicate is implied by the source's along the output map. -/
theorem modality_map {F G : RelyFrame} (f : FrameMorphism F G)
    {relyF : F.Env → Prop} {relyG : G.Env → Prop}
    (hrely : ∀ e : G.Env, relyG e → relyF (f.onEnv e))
    {BF : F.Out → Prop} {BG : G.Out → Prop}
    (hB : ∀ o, BF o → BG (f.onOut o))
    {t : F.Carrier} (h : F.modality relyF BF t) :
    G.modality relyG BG (f.onCarrier t) := by
  intro e he
  obtain ⟨wit, hfit, hBF⟩ := h (f.onEnv e) (hrely e he)
  refine ⟨f.onWit wit, f.fit wit e t hfit, ?_⟩
  rw [f.out wit]
  exact hB _ hBF

end FrameMorphism

/-! ## The join law separates the rely-free index from the others

`diamond_exists` says the diamond preserves joins.  The modality does not, and
the obstruction is exactly the universal quantifier over environments: different
environments may be served by witnesses landing in different disjuncts. -/

/-- A frame with two environments, whose witnesses are forced to track them. -/
def joinFailureFrame : RelyFrame where
  Carrier := Unit
  Env := Bool
  Out := Bool
  Wit := Bool
  Fit := fun wit e _ => wit = e
  out := id

/-- **Joins of targets are not preserved at a genuine index.**  The modality
holds of a disjunction and of neither disjunct. -/
theorem join_not_preserved :
    joinFailureFrame.modality (fun _ => True)
        (fun o => (o = true) ∨ (o = false)) ()
      ∧ ¬ joinFailureFrame.modality (fun _ => True) (fun o => o = true) ()
      ∧ ¬ joinFailureFrame.modality (fun _ => True) (fun o => o = false) () := by
  refine ⟨?_, ?_, ?_⟩
  · intro e _
    refine ⟨e, rfl, ?_⟩
    cases e
    · exact Or.inr rfl
    · exact Or.inl rfl
  · intro h
    obtain ⟨wit, hfit, hB⟩ := h false trivial
    cases hfit
    exact Bool.noConfusion hB
  · intro h
    obtain ⟨wit, hfit, hB⟩ := h true trivial
    cases hfit
    exact Bool.noConfusion hB

/-- **Vacuity is reachable with an inhabited environment type.**  The rely
condition, not the index, is what can empty out. -/
theorem target_need_not_be_load_bearing :
    joinFailureFrame.modality (fun _ => False) (fun _ => False) () :=
  RelyFrame.modality_of_no_admissible _ (fun _ h => h) _ _

/-- A frame with the same witnesses as `joinFailureFrame` but a trivial index,
so that a witness need not track anything. -/
def trivialIndexFrame : RelyFrame where
  Carrier := Unit
  Env := Unit
  Out := Bool
  Wit := Bool
  Fit := fun wit _ _ => wit = true
  out := id

/-- There is a map of frames from the indexed one to the trivial one. -/
def forgetIndex : FrameMorphism joinFailureFrame trivialIndexFrame where
  onCarrier := _root_.id
  onEnv := fun _ => true
  onOut := _root_.id
  onWit := _root_.id
  fit := fun _ _ _ h => h
  out := fun _ => rfl

/-- **Transport runs one way only.**  Along `forgetIndex` the trivial frame
satisfies a modality the indexed frame refutes, so a result established at the
target carrier is not a result at the source carrier.  This is the precise sense
in which the three presentations below, once identified as instances of one
scheme, are still three different modalities. -/
theorem transport_is_directed :
    trivialIndexFrame.modality (fun _ => True) (fun o => o = true) ()
      ∧ ¬ joinFailureFrame.modality (fun _ => True) (fun o => o = true) () := by
  refine ⟨?_, (join_not_preserved).2.1⟩
  intro _ _
  exact ⟨true, rfl, rfl⟩

/-! ## Instance one: the lambda-theory carrier, at the trivial index

This is the presentation whose shape looked incompatible with the other two.  It
is not: it is the frame whose environment type is `Unit`, so its universal
quantifier collapses and only the existential is visible. -/

section Categorical

open _root_.CategoryTheory
open Mettapedia.GSLT.Meredith

/-- The frame the lambda-theory presentation supplies.  A witness is a reduct of
the filled context; there is nothing to index by. -/
def categoricalFrame {T : LambdaTheory} {br : BaseRewrite T}
    (pos : Modal.RedexPosition T br) : RelyFrame where
  Carrier := br.ctx ⟶ pos.subtermCarrier
  Env := Unit
  Out := br.ctx ⟶ T.Pr
  Wit := br.ctx ⟶ T.Pr
  Fit := fun reduct _ t => T.rewriteRel (pos.fillContext t) reduct
  out := id

/-- **The bridge.**  Not `rfl`: the scheme's quantifier over `Unit` has to be
collapsed. -/
theorem categorical_is_instance {T : LambdaTheory} {br : BaseRewrite T}
    (pos : Modal.RedexPosition T br) (post : (br.ctx ⟶ T.Pr) → Prop)
    (t : br.ctx ⟶ pos.subtermCarrier) :
    Modal.RelyPossibly pos post t ↔
      (categoricalFrame pos).modality (fun _ => True) post t := by
  constructor
  · rintro ⟨reduct, steps, accepted⟩ _ _
    exact ⟨reduct, steps, accepted⟩
  · intro h
    obtain ⟨reduct, steps, accepted⟩ := h () trivial
    exact ⟨reduct, steps, accepted⟩

/-- The published monotonicity law of this carrier, statement unchanged,
re-derived from the scheme. -/
example {T : LambdaTheory} {br : BaseRewrite T}
    {pos : Modal.RedexPosition T br} {post post' : (br.ctx ⟶ T.Pr) → Prop}
    (weaker : ∀ q, post q → post' q) {t : br.ctx ⟶ pos.subtermCarrier}
    (inhabits : Modal.RelyPossibly pos post t) : Modal.RelyPossibly pos post' t :=
  (categorical_is_instance pos post' t).mpr
    (RelyFrame.modality_mono_target _ weaker
      ((categorical_is_instance pos post t).mp inhabits))

/-- The published load-bearing-target law of this carrier, likewise. -/
example {T : LambdaTheory} {br : BaseRewrite T}
    (pos : Modal.RedexPosition T br) {post : (br.ctx ⟶ T.Pr) → Prop}
    (empty : ∀ q, ¬ post q) (t : br.ctx ⟶ pos.subtermCarrier) :
    ¬ Modal.RelyPossibly pos post t := fun h =>
  RelyFrame.not_modality_of_target_empty (categoricalFrame pos) () trivial empty t
    ((categorical_is_instance pos post t).mp h)

/-- **The law this carrier has and the others do not.**  At the trivial index the
modality is a single diamond, so it preserves joins of targets.  Compare
`join_not_preserved`, which refutes the same statement at a genuine index. -/
theorem categorical_preserves_joins {T : LambdaTheory} {br : BaseRewrite T}
    (pos : Modal.RedexPosition T br) {ι : Type _}
    (posts : ι → (br.ctx ⟶ T.Pr) → Prop) (t : br.ctx ⟶ pos.subtermCarrier) :
    Modal.RelyPossibly pos (fun q => ∃ i, posts i q) t ↔
      ∃ i, Modal.RelyPossibly pos (posts i) t := by
  have collapse : ∀ post : (br.ctx ⟶ T.Pr) → Prop,
      Modal.RelyPossibly pos post t ↔ diamond ((categoricalFrame pos).step ()) post t := by
    intro post
    exact (categorical_is_instance pos post t).trans
      (RelyFrame.modality_iff_diamond_of_subsingleton (categoricalFrame pos) ()
        trivial (fun _ _ => rfl) post t)
  exact (collapse _).trans
    ((diamond_exists posts t).trans (exists_congr fun i => (collapse (posts i)).symm))

end Categorical

/-! ## Instance two: the pattern carrier

Here the index is the binding list, and the rely condition carries the firing
guard alongside the declared assumptions. -/

section PatternCarrier

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.RedexPosition
open Mettapedia.OSLF.Framework.GeneratedModality

/-- The frame the pattern presentation supplies.  A witness is a decomposition
together with the step it licenses; what it produces is the step's target. -/
def patternFrame (base : BasePremiseEvaluator) (lang : LanguageDef)
    (rule : RewriteRule) (pos : Position) : RelyFrame where
  Carrier := Pattern
  Env := Bindings
  Out := Pattern
  Wit := Pattern × Pattern
  Fit := fun wit bindings t =>
    plug (applyBindings bindings rule.left) pos (applyBindings bindings t)
        = some wit.1 ∧ Step base lang wit.1 wit.2
  out := Prod.snd

/-- The rely condition this carrier uses.  The firing guard is part of the
index's admissibility, not part of the witness. -/
def patternRely (base : BasePremiseEvaluator) (lang : LanguageDef)
    (rule : RewriteRule) (pos : Position) (A : String → Pattern → Prop)
    (bindings : Bindings) : Prop :=
  RelySatisfied rule pos A bindings ∧ RuleFires base lang rule bindings

/-- **The bridge.**  Not `rfl`: the scheme's single hypothesis has to be split
into the two the carrier curries, and its single existential into two. -/
theorem pattern_is_instance (base : BasePremiseEvaluator) (lang : LanguageDef)
    (rule : RewriteRule) (pos : Position) (A : String → Pattern → Prop)
    (B : Pattern → Prop) (t : Pattern) :
    GeneratedModality.RelyPossibly base lang rule pos A B t ↔
      (patternFrame base lang rule pos).modality (patternRely base lang rule pos A) B t := by
  constructor
  · intro h bindings hb
    obtain ⟨source, target, hplug, hstep, hB⟩ := h bindings hb.1 hb.2
    exact ⟨(source, target), ⟨hplug, hstep⟩, hB⟩
  · intro h bindings hrely hfires
    obtain ⟨wit, ⟨hplug, hstep⟩, hB⟩ := h bindings ⟨hrely, hfires⟩
    exact ⟨wit.1, wit.2, hplug, hstep, hB⟩

/-- The published monotonicity law of this carrier, statement unchanged,
re-derived from the scheme. -/
example {base : BasePremiseEvaluator} {lang : LanguageDef} {rule : RewriteRule}
    {pos : Position} {A : String → Pattern → Prop} {B B' : Pattern → Prop}
    {t : Pattern} (weaker : ∀ q, B q → B' q)
    (ht : GeneratedModality.RelyPossibly base lang rule pos A B t) :
    GeneratedModality.RelyPossibly base lang rule pos A B' t :=
  (pattern_is_instance base lang rule pos A B' t).mpr
    (RelyFrame.modality_mono_target _ weaker
      ((pattern_is_instance base lang rule pos A B t).mp ht))

/-- The published load-bearing-target law of this carrier, likewise. -/
example {base : BasePremiseEvaluator} {lang : LanguageDef} {rule : RewriteRule}
    {pos : Position} {A : String → Pattern → Prop} {B : Pattern → Prop}
    {t : Pattern} {bindings : Bindings} (empty : ∀ q, ¬ B q)
    (hrely : RelySatisfied rule pos A bindings)
    (hfires : RuleFires base lang rule bindings) :
    ¬ GeneratedModality.RelyPossibly base lang rule pos A B t := fun ht =>
  RelyFrame.not_modality_of_target_empty (patternFrame base lang rule pos) bindings
    ⟨hrely, hfires⟩ empty t
    ((pattern_is_instance base lang rule pos A B t).mp ht)

/-- The published rely-congruence law of this carrier, likewise: all that is
carrier-specific is that agreement on the rely variables preserves the rely
condition, and the scheme supplies the rest. -/
example {base : BasePremiseEvaluator} {lang : LanguageDef} {rule : RewriteRule}
    {pos : Position} {A A' : String → Pattern → Prop} {B : Pattern → Prop}
    {t : Pattern} (hA : ∀ x ∈ relyVars rule.left pos, A x = A' x) :
    GeneratedModality.RelyPossibly base lang rule pos A B t ↔
      GeneratedModality.RelyPossibly base lang rule pos A' B t := by
  rw [pattern_is_instance, pattern_is_instance]
  refine RelyFrame.modality_congr_rely _ ?_
  intro bindings
  constructor
  · rintro ⟨hrely, hfires⟩
    refine ⟨fun x hx v hv => ?_, hfires⟩
    have hv' := hrely x hx v hv
    rwa [hA x hx] at hv'
  · rintro ⟨hrely, hfires⟩
    refine ⟨fun x hx v hv => ?_, hfires⟩
    have hv' := hrely x hx v hv
    rwa [← hA x hx] at hv'

end PatternCarrier

/-! ## Instance three: the intrinsically scoped carrier

Here the index is the rely environment and a witness is a closed rule instance;
there is no separate firing guard, because exhibiting the instance is the
firing. -/

section ScopedCarrier

open Mettapedia.OSLF.Binding

/-- The frame the scoped presentation supplies. -/
def scopedFrame {S : Signature} {M : List (MetaArity S)}
    (P : PositionedRewrite (withMetas S M)) : RelyFrame where
  Carrier := Term S [] P.position.carrier
  Env := RelyEnv P
  Out := Term S [] P.sort
  Wit := RuleInstance M P
  Fit := fun I env t =>
    Realises P I.close env ∧ bind I.close (instantiate I.body P.position.redex) = t
  out := fun I => bind I.close (instantiate I.body P.rhs)

/-- The rely condition this carrier uses: the declared typing holds of every
value the environment supplies. -/
def scopedRely {S : Signature} {M : List (MetaArity S)}
    {P : PositionedRewrite (withMetas S M)} (A : RelyTyping P) (env : RelyEnv P) :
    Prop :=
  ∀ (s : S.Srt) (x : Var P.ctx s) (hx : P.RelyParameter x), A s x (env s x hx)

/-- **The bridge.**  Not `rfl`: the carrier's three-way conjunction has to be
re-associated into the scheme's two-way one. -/
theorem scoped_is_instance {S : Signature} {M : List (MetaArity S)}
    (P : PositionedRewrite (withMetas S M)) (A : RelyTyping P)
    (B : Term S [] P.sort → Prop) (t : Term S [] P.position.carrier) :
    Mettapedia.OSLF.Binding.RelyPossibly P A B t ↔
      (scopedFrame P).modality (scopedRely A) B t := by
  constructor
  · intro h env henv
    obtain ⟨I, hreal, ht, hB⟩ := h env henv
    exact ⟨I, ⟨hreal, ht⟩, hB⟩
  · intro h env henv
    obtain ⟨I, ⟨hreal, ht⟩, hB⟩ := h env henv
    exact ⟨I, hreal, ht, hB⟩

/-- The published target-monotonicity law of this carrier, statement unchanged,
re-derived from the scheme. -/
example {S : Signature} {M : List (MetaArity S)}
    {P : PositionedRewrite (withMetas S M)} {A : RelyTyping P}
    {B C : Term S [] P.sort → Prop} (hBC : ∀ x, B x → C x)
    {t : Term S [] P.position.carrier}
    (h : Mettapedia.OSLF.Binding.RelyPossibly P A B t) :
    Mettapedia.OSLF.Binding.RelyPossibly P A C t :=
  (scoped_is_instance P A C t).mpr
    (RelyFrame.modality_mono_target _ hBC ((scoped_is_instance P A B t).mp h))

/-- The published rely-antitonicity law of this carrier, likewise. -/
example {S : Signature} {M : List (MetaArity S)}
    {P : PositionedRewrite (withMetas S M)} {A A' : RelyTyping P}
    (hAA : ∀ s x u, A' s x u → A s x u)
    {B : Term S [] P.sort → Prop} {t : Term S [] P.position.carrier}
    (h : Mettapedia.OSLF.Binding.RelyPossibly P A B t) :
    Mettapedia.OSLF.Binding.RelyPossibly P A' B t :=
  (scoped_is_instance P A' B t).mpr
    (RelyFrame.modality_antitone_rely (scopedFrame P)
      (fun env he s x hx => hAA s x (env s x hx) (he s x hx))
      ((scoped_is_instance P A B t).mp h))

end ScopedCarrier


end Mettapedia.OSLF.Framework.RelyPossiblyScheme
