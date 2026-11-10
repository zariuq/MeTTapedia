import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullTelescopes
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFullRace
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceGenericWeak

/-!
# Firings that make helpers, placed in the generic races layer

R93 placed the firings without helpers in `Race.Generic` by a strict transport. Firings that make
telescopes of helpers cannot move strictly: moving a telescope along the identity reindexes each of
its types along `𝟙`, which is the old type only up to `TypeOver.reindex_id`. This file places them
with **alikeness up to an isomorphism of telescopes over the frame**, which absorbs `reindex_id`.

**Lifts** (`IsLift`). A telescope `K` over `Δ` with a leg `ℓ : K.frame ⟶ H.frame` is a lift of `H`
along `σ : Δ ⟶ Γ` when the square commutes and is a pullback. The reindexed telescope is a lift
(`isLift_reindex`), and so is `H` itself along the identity (`isLift_id`); lifts paste
(`IsLift.paste`), turn along isomorphisms over the frame (`IsLift.twist`), and any two lifts along one
morphism are isomorphic over it (`IsLift.compare`). Along an isomorphism, the lift is an isomorphism
(`liftIso`).

**The step** (`helperStep`): the dependent full step on firings that make a telescope and carry
natural queries (`HelperFiring`).

**Transport** (`helperTransport`). Isomorphisms of states are R93's `PlainIso`. A firing moves by
reindexing its telescope and carrying its data along the lift; it is alike to another when an
isomorphism of their telescope frames over the state's frame carries the one's data to the other's
(`AlikeData`). Moving along the identity gives an alike firing, not the same one
(`helper_move_refl`); this is the place where `reindex_id` lives.

**The races layer applies** (`helper_bisimilar_of_same`, `helper_weakBisimilar_of_same`,
`helper_branchingBisimilar_of_same`): for every program whose labels are invariant under transport,
transport-equivalent states are strongly, weakly and branching bisimilar.

**Diamonds close** (`helper_closes`), so independence is the admission of both orders
(`helper_independent_iff`); the two composites are related by the block exchange.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
namespace DependentFull

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire mem_fire)

variable {Head L : Type} [UniverseLevel.LevelOrder L] {rules : Rules Head} {levels : LevelModel rules L}
  {O : Type}

/-! ## Lifts of telescopes -/

section Lifts

/-- **`K` with the leg `ℓ` is a lift of `H` along `σ`**: the square commutes and is a pullback. -/
structure IsLift {Γ Δ : Context rules} (σ : Δ ⟶ Γ) (H : Helpers Γ) (K : Helpers Δ) (ℓ : K.frame ⟶ H.frame) :
    Prop where
  covers : ℓ ≫ H.weaken = K.weaken ≫ σ
  factors : ∀ {X : Context rules} (a : X ⟶ Δ) (b : X ⟶ H.frame), a ≫ σ = b ≫ H.weaken →
    ∃ m : X ⟶ K.frame, m ≫ K.weaken = a ∧ m ≫ ℓ = b
  unique : ∀ {X : Context rules} (m m' : X ⟶ K.frame), m ≫ K.weaken = m' ≫ K.weaken → m ≫ ℓ = m' ≫ ℓ →
    m = m'

variable {Γ Δ Δ' : Context rules}

/-- **The reindexed telescope is a lift.** -/
theorem isLift_reindex (σ : Δ ⟶ Γ) (H : Helpers Γ) : IsLift σ H (H.reindex σ) (Helpers.lift σ H) where
  covers := Helpers.lift_weaken σ H
  factors a b agree := ⟨Helpers.into σ H a b agree, Helpers.into_weaken σ H a b agree, Helpers.into_lift σ H a b agree⟩
  unique m m' weakened lifted := by
    have agree : (m ≫ (H.reindex σ).weaken) ≫ σ = (m ≫ Helpers.lift σ H) ≫ H.weaken := by
      rw [Category.assoc, Category.assoc, Helpers.lift_weaken]
    exact (Helpers.into_unique σ H _ _ agree m rfl rfl).trans
      (Helpers.into_unique σ H _ _ agree m' weakened.symm lifted.symm).symm

/-- **A telescope is its own lift along the identity.** -/
theorem isLift_id (H : Helpers Γ) : IsLift (𝟙 Γ) H H (𝟙 H.frame) where
  covers := (Category.id_comp _).trans (Category.comp_id _).symm
  factors a b agree := ⟨b, agree.symm.trans (Category.comp_id a), Category.comp_id b⟩
  unique m m' _ lifted := by simpa only [Category.comp_id] using lifted

/-- **Lifts paste.** -/
theorem IsLift.paste {σ : Δ ⟶ Γ} {τ : Δ' ⟶ Δ} {H : Helpers Γ} {K : Helpers Δ} {K' : Helpers Δ'}
    {ℓ : K.frame ⟶ H.frame} {ℓ' : K'.frame ⟶ K.frame} (first : IsLift σ H K ℓ) (second : IsLift τ K K' ℓ') :
    IsLift (τ ≫ σ) H K' (ℓ' ≫ ℓ) where
  covers := by rw [Category.assoc, first.covers, ← Category.assoc, second.covers, Category.assoc]
  factors a b agree := by
    obtain ⟨m, mWeaken, mLift⟩ := first.factors (a ≫ τ) b (by rw [Category.assoc]; exact agree)
    obtain ⟨m', m'Weaken, m'Lift⟩ := second.factors a m mWeaken.symm
    exact ⟨m', m'Weaken, by rw [← Category.assoc, m'Lift, mLift]⟩
  unique m m' weakened lifted := by
    apply second.unique m m' weakened
    apply first.unique
    · rw [Category.assoc, second.covers, ← Category.assoc, weakened, Category.assoc, ← second.covers,
        ← Category.assoc]
    · simpa only [Category.assoc] using lifted

/-- **A lift turns along an isomorphism of telescopes over the frame.** -/
theorem IsLift.twist {σ : Δ ⟶ Γ} {H H' : Helpers Γ} {K : Helpers Δ} {ℓ : K.frame ⟶ H.frame}
    (lift : IsLift σ H K ℓ) (e : H.frame ≅ H'.frame) (commutes : e.hom ≫ H'.weaken = H.weaken) :
    IsLift σ H' K (ℓ ≫ e.hom) where
  covers := by rw [Category.assoc, commutes, lift.covers]
  factors a b agree := by
    have back : e.inv ≫ H.weaken = H'.weaken := by
      rw [← commutes, ← Category.assoc, e.inv_hom_id, Category.id_comp]
    obtain ⟨m, mWeaken, mLift⟩ := lift.factors a (b ≫ e.inv) (by rw [Category.assoc, back]; exact agree)
    exact ⟨m, mWeaken, by rw [← Category.assoc, mLift, Category.assoc, e.inv_hom_id, Category.comp_id]⟩
  unique m m' weakened lifted := by
    apply lift.unique m m' weakened
    have cancelled := congrArg (· ≫ e.inv) lifted
    simpa only [Category.assoc, e.hom_inv_id, Category.comp_id] using cancelled

/-- **Two lifts along one morphism are isomorphic over it.** -/
theorem IsLift.compare {σ : Δ ⟶ Γ} {H : Helpers Γ} {K K' : Helpers Δ} {ℓ : K.frame ⟶ H.frame}
    {ℓ' : K'.frame ⟶ H.frame} (one : IsLift σ H K ℓ) (two : IsLift σ H K' ℓ') :
    ∃ e : K.frame ≅ K'.frame, e.hom ≫ K'.weaken = K.weaken ∧ e.hom ≫ ℓ' = ℓ := by
  obtain ⟨m, mWeaken, mLift⟩ := two.factors K.weaken ℓ one.covers.symm
  obtain ⟨m', m'Weaken, m'Lift⟩ := one.factors K'.weaken ℓ' two.covers.symm
  have left : m ≫ m' = 𝟙 _ := one.unique _ _ (by rw [Category.assoc, m'Weaken, mWeaken, Category.id_comp])
    (by rw [Category.assoc, m'Lift, mLift, Category.id_comp])
  have right : m' ≫ m = 𝟙 _ := two.unique _ _ (by rw [Category.assoc, mWeaken, m'Weaken, Category.id_comp])
    (by rw [Category.assoc, mLift, m'Lift, Category.id_comp])
  exact ⟨⟨m, m', left, right⟩, mWeaken, mLift⟩

/-- **Along an isomorphism, the lift is an isomorphism.** -/
def liftIso (e : Δ ≅ Γ) (H : Helpers Γ) : (H.reindex e.hom).frame ≅ H.frame where
  hom := Helpers.lift e.hom H
  inv := Helpers.into e.hom H (H.weaken ≫ e.inv) (𝟙 H.frame)
    (by rw [Category.assoc, e.inv_hom_id, Category.comp_id, Category.id_comp])
  hom_inv_id := by
    have agree : (H.reindex e.hom).weaken ≫ e.hom = Helpers.lift e.hom H ≫ H.weaken :=
      (Helpers.lift_weaken e.hom H).symm
    refine (isLift_reindex e.hom H).unique _ _ ?_ ?_
    · rw [Category.assoc, Helpers.into_weaken, ← Category.assoc, ← agree, Category.assoc, e.hom_inv_id,
        Category.comp_id, Category.id_comp]
    · rw [Category.assoc, Helpers.into_lift, Category.comp_id, Category.id_comp]
  inv_hom_id := Helpers.into_lift _ _ _ _ _

theorem liftIso_hom (e : Δ ≅ Γ) (H : Helpers Γ) : (liftIso e H).hom = Helpers.lift e.hom H := rfl

end Lifts

/-! ## The step of firings that make telescopes -/

variable (levels O) in
/-- **A firing that makes a telescope of helpers**, with natural queries. -/
structure HelperFiring (s : State rules O) where
  helpers : Helpers s.frame
  data : Natural levels O helpers.frame

namespace HelperFiring

variable {s : State rules O} (f : HelperFiring levels O s)

/-- The firing of the dependent full step it is. -/
abbrev toFiring : Firing levels s := Natural.withHelpers f.helpers f.data

/-- The state read at the firing's frame. -/
abbrev reading : Local rules O f.helpers.frame := s.toLocal.move f.helpers.weaken

end HelperFiring

variable [DecidableEq O]

variable (levels O) in
/-- **The dependent full step on firings that make telescopes.** -/
abbrev helperStep : Interface.Step.Standard (frames levels) O (State rules O) (HelperFiring levels O) where
  frame s := s.frame
  knowledge s := s.knowledge
  present s := s.present
  selection f := f.toFiring.selection
  target f := f.helpers.frame
  extension f := f.helpers.weaken
  information f := f.toFiring.information
  transported f e member := (step levels O).transported f.toFiring e member
  Shapes f := f.toFiring.Shapes
  Holds f _ τ := f.toFiring.Holds τ
  Admits f := f.toFiring.Admits
  admits_iff _ := Iff.rfl
  preparedResult f p := (step levels O).preparedResult f.toFiring p
  present_preparedResult _ _ := rfl
  preparedSettle f _ := 𝟙 f.helpers.frame
  knowledge_preparedResult _ _ := (Frames.applyStore_id (X := frames levels) _).symm

/-- **It is the dependent full step on these firings.** -/
theorem helperStep_admits_iff {s : State rules O} (f : HelperFiring levels O s) :
    (helperStep levels O).Admits f ↔ (step levels O).Admits f.toFiring :=
  Iff.rfl

/-! ## Readings that agree along a morphism -/

omit [DecidableEq O] in
/-- Moving along an isomorphism of states and then along a morphism into the new frame agrees with
moving the old state along the composite. -/
theorem agree_of_iso {s t : State rules O} (i : PlainIso levels s t) {Δ : Context rules} (W : Δ ⟶ t.frame) :
    Local.AgreeAlong (levels := levels) (𝟙 Δ) (t.toLocal.move W) (s.toLocal.move (W ≫ i.frame.hom)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Local.move_comp, Category.id_comp]
    show (frames levels).Equivalent ((frames levels).applyStore W t.knowledge)
      ((frames levels).applyStore (W ≫ i.frame.hom) s.knowledge)
    rw [← applyStore_applyStore]
    exact (Frames.Equivalent.applyStore (X := frames levels) W i.knowledge).symm
  · rw [Local.move_comp, Category.id_comp]
    exact i.present.symm
  · rw [Local.move_comp, Category.id_comp]
    funext o
    show (frames levels).act W (t.label o) = (frames levels).act (W ≫ i.frame.hom) (s.label o)
    rw [i.label, act_act]

omit [DecidableEq O] in
theorem agree_congr {Δ Δ' : Context rules} {σ σ' : Δ' ⟶ Δ} {c : Local rules O Δ} {c' : Local rules O Δ'}
    (same : σ = σ') (agree : Local.AgreeAlong (levels := levels) σ c' c) :
    Local.AgreeAlong (levels := levels) σ' c' c := by
  subst same
  exact agree

omit [DecidableEq O] in
/-- Agreement along the identity, then along a morphism. -/
theorem agree_move {Δ Δ' : Context rules} (σ : Δ' ⟶ Δ) {c : Local rules O Δ} {c' : Local rules O Δ'}
    (agree : Local.AgreeAlong (levels := levels) (𝟙 Δ') c' (c.move σ)) :
    Local.AgreeAlong (levels := levels) σ c' c := by
  obtain ⟨knowledge, present, label⟩ := agree
  rw [Local.move_comp, Category.id_comp] at knowledge present label
  exact ⟨knowledge, present, label⟩

/-- **Admission moves along agreeing readings.** -/
theorem admits_agree {Δ Δ' : Context rules} (d : Natural levels O Δ) (e : Δ' ≅ Δ) {c : Local rules O Δ}
    {c' : Local rules O Δ'} (agree : Local.AgreeAlong (levels := levels) e.hom c' c) :
    (d.move e.hom).toPlain.Admits c' ↔ d.toPlain.Admits c := by
  cases c' with
  | mk K' P' L' =>
      obtain ⟨knowledge, present, label⟩ := agree
      refine ((d.move e.hom).toPlain.admits_equivalent P' L' knowledge).trans ?_
      have same : (⟨(c.move e.hom).knowledge, P', L'⟩ : Local rules O Δ') = c.move e.hom :=
        Local.mk_congr rfl present label
      rw [same]
      exact Natural.admits_move_iff d e c

/-- **Results agree along agreeing readings.** -/
theorem after_agree {Δ Δ' : Context rules} (d : Natural levels O Δ) (σ : Δ' ⟶ Δ) {c : Local rules O Δ}
    {c' : Local rules O Δ'} (agree : Local.AgreeAlong (levels := levels) σ c' c)
    (typed : ∀ m ∈ d.makes, m.2.WellTyped) (typed' : ∀ m ∈ (d.move σ).makes, m.2.WellTyped) :
    Local.AgreeAlong (levels := levels) σ ((d.move σ).toPlain.after c' typed') (d.toPlain.after c typed) := by
  obtain ⟨knowledge, present, label⟩ := agree
  unfold Local.AgreeAlong
  rw [← Natural.after_move σ d c typed typed']
  refine ⟨?_, ?_, ?_⟩
  · show (frames levels).Equivalent (c'.knowledge ++ (d.move σ).toPlain.own c'.label)
      ((c.move σ).knowledge ++ (d.move σ).toPlain.own (c.move σ).label)
    rw [label]
    intro b τ
    rw [Frames.models_append, Frames.models_append, knowledge b τ]
  · show fire c'.present _ = fire (c.move σ).present _
    rw [present]
  · show relabel c'.label (d.move σ).makes typed' = relabel (c.move σ).label (d.move σ).makes typed'
    rw [label]

omit [DecidableEq O] in
/-- **An isomorphism of states from agreeing states.** -/
def PlainIso.ofAgree {s t : State rules O} (e : t.frame ≅ s.frame)
    (agree : Local.AgreeAlong (levels := levels) e.hom t.toLocal s.toLocal) : PlainIso levels s t where
  frame := e
  knowledge := agree.1.symm
  present := agree.2.1.symm
  label o := congrFun agree.2.2 o

/-! ## Alikeness up to an isomorphism of telescopes -/

omit [DecidableEq O] in
variable (levels O) in
/-- **Alikeness data**: an isomorphism of the telescope frames over the state's frame that carries
the second firing's data to the first's. -/
structure AlikeData {s : State rules O} (f f' : HelperFiring levels O s) : Type where
  frame : f.helpers.frame ≅ f'.helpers.frame
  commutes : frame.hom ≫ f'.helpers.weaken = f.helpers.weaken
  data : f.data = f'.data.move frame.hom

omit [DecidableEq O] in
variable (levels O) in
/-- **Alike firings**: alikeness data exists. -/
def HelperAlike {s : State rules O} (f f' : HelperFiring levels O s) : Prop := Nonempty (AlikeData levels O f f')

omit [DecidableEq O] in
theorem helperAlike_equivalence (s : State rules O) : Equivalence (HelperAlike levels O (s := s)) where
  refl f := ⟨⟨Iso.refl _, Category.id_comp _, (Natural.move_id f.data).symm⟩⟩
  symm := by
    rintro f f' ⟨a⟩
    refine ⟨⟨a.frame.symm, ?_, ?_⟩⟩
    · show a.frame.inv ≫ f.helpers.weaken = f'.helpers.weaken
      rw [← a.commutes, ← Category.assoc, a.frame.inv_hom_id, Category.id_comp]
    · show f'.data = f.data.move a.frame.inv
      rw [a.data, Natural.move_comp, a.frame.inv_hom_id, Natural.move_id]
  trans := by
    rintro f f' f'' ⟨a⟩ ⟨b⟩
    refine ⟨⟨a.frame ≪≫ b.frame, ?_, ?_⟩⟩
    · show (a.frame.hom ≫ b.frame.hom) ≫ f''.helpers.weaken = f.helpers.weaken
      rw [Category.assoc, b.commutes, a.commutes]
    · show f.data = f''.data.move (a.frame.hom ≫ b.frame.hom)
      rw [a.data, b.data, Natural.move_comp]

omit [DecidableEq O] in
/-- Alikeness from two lifts of one telescope along one morphism, whose data are the old data along
the legs. -/
theorem alike_of_lifts {s : State rules O} {Γ : Context rules} {σ : s.frame ⟶ Γ} {H : Helpers Γ}
    {d : Natural levels O H.frame} {f f' : HelperFiring levels O s} {ℓ : f.helpers.frame ⟶ H.frame}
    {ℓ' : f'.helpers.frame ⟶ H.frame} (one : IsLift σ H f.helpers ℓ) (two : IsLift σ H f'.helpers ℓ')
    (first : f.data = d.move ℓ) (second : f'.data = d.move ℓ') : HelperAlike levels O f f' := by
  obtain ⟨e, commutes, legs⟩ := one.compare two
  refine ⟨⟨e, commutes, ?_⟩⟩
  rw [first, second, Natural.move_comp, legs]

/-! ## The transport -/

/-- **A firing carried along an isomorphism of states**: its telescope reindexed, its data along the
lift. -/
def HelperFiring.move {s t : State rules O} (i : PlainIso levels s t) (f : HelperFiring levels O s) :
    HelperFiring levels O t :=
  ⟨f.helpers.reindex i.frame.hom, f.data.move (Helpers.lift i.frame.hom f.helpers)⟩

omit [DecidableEq O] in
/-- The reading of a moved firing agrees with the old reading along the lift. -/
theorem reading_move {s t : State rules O} (i : PlainIso levels s t) (f : HelperFiring levels O s) :
    Local.AgreeAlong (levels := levels) (Helpers.lift i.frame.hom f.helpers) (f.move i).reading f.reading := by
  apply agree_move
  have agree := agree_of_iso i (f.helpers.reindex i.frame.hom).weaken
  rw [← Helpers.lift_weaken] at agree
  rw [Local.move_comp]
  exact agree

theorem helper_admits_move {s t : State rules O} (i : PlainIso levels s t) (f : HelperFiring levels O s) :
    (helperStep levels O).Admits (f.move i) ↔ (helperStep levels O).Admits f :=
  (Natural.admits_withHelpers _ _).trans ((admits_agree f.data (liftIso i.frame f.helpers) (reading_move i f)).trans
    (Natural.admits_withHelpers _ _).symm)

/-- The result of a moved firing agrees with the old result along the lift. -/
def helperResultMove {s t : State rules O} (i : PlainIso levels s t) (f : HelperFiring levels O s)
    (admitted : (helperStep levels O).Admits f) :
    PlainIso levels ((helperStep levels O).result f admitted)
      ((helperStep levels O).result (f.move i) ((helper_admits_move i f).mpr admitted)) :=
  PlainIso.ofAgree (liftIso i.frame f.helpers) (by
    show Local.AgreeAlong (Helpers.lift i.frame.hom f.helpers)
      ((f.move i).toFiring.after ((helper_admits_move i f).mpr admitted)).toLocal
      (f.toFiring.after admitted).toLocal
    rw [Natural.toLocal_after_withHelpers, Natural.toLocal_after_withHelpers]
    exact after_agree f.data _ (reading_move i f) _ _)

/-- Alike firings have isomorphic results. -/
noncomputable def helperResultAlike {s : State rules O} {f f' : HelperFiring levels O s}
    (alike : HelperAlike levels O f f') (admitted : (helperStep levels O).Admits f)
    (admitted' : (helperStep levels O).Admits f') :
    PlainIso levels ((helperStep levels O).result f admitted) ((helperStep levels O).result f' admitted') :=
  PlainIso.symm (PlainIso.ofAgree alike.some.frame (by
    show Local.AgreeAlong alike.some.frame.hom (f.toFiring.after admitted).toLocal
      (f'.toFiring.after admitted').toLocal
    rw [Natural.toLocal_after_withHelpers, Natural.toLocal_after_withHelpers]
    have reading : f.reading = f'.reading.move alike.some.frame.hom := by
      show s.toLocal.move f.helpers.weaken = (s.toLocal.move f'.helpers.weaken).move alike.some.frame.hom
      rw [Local.move_comp, alike.some.commutes]
    have agree : Local.AgreeAlong (levels := levels) alike.some.frame.hom f.reading f'.reading :=
      ⟨by rw [reading]; exact fun _ _ => Iff.rfl, by rw [reading], by rw [reading]⟩
    have moved := after_agree f'.data alike.some.frame.hom agree admitted'.1.2.2.2.2
      (by rw [← alike.some.data]; exact admitted.1.2.2.2.2)
    exact (Plain.after_congr (congrArg Natural.toPlain alike.some.data) rfl _ _) ▸ moved))

theorem helper_admits_alike {s : State rules O} {f f' : HelperFiring levels O s}
    (alike : HelperAlike levels O f f') :
    (helperStep levels O).Admits f ↔ (helperStep levels O).Admits f' := by
  obtain ⟨a⟩ := alike
  have reading : f.reading = f'.reading.move a.frame.hom := by
    show s.toLocal.move f.helpers.weaken = (s.toLocal.move f'.helpers.weaken).move a.frame.hom
    rw [Local.move_comp, a.commutes]
  have agree : Local.AgreeAlong (levels := levels) a.frame.hom f.reading f'.reading :=
    ⟨by rw [reading]; exact fun _ _ => Iff.rfl, by rw [reading], by rw [reading]⟩
  refine (Natural.admits_withHelpers _ _).trans ?_
  rw [a.data]
  exact (admits_agree f'.data a.frame agree).trans (Natural.admits_withHelpers _ _).symm

theorem helper_selection_alike {s : State rules O} {f f' : HelperFiring levels O s}
    (alike : HelperAlike levels O f f') : (helperStep levels O).selection f = (helperStep levels O).selection f' := by
  obtain ⟨a⟩ := alike
  show f.data.toPlain.selection = f'.data.toPlain.selection
  rw [a.data, Natural.selection_move]

omit [DecidableEq O] in
theorem helper_move_alike {s t : State rules O} (i : PlainIso levels s t) {f f' : HelperFiring levels O s}
    (alike : HelperAlike levels O f f') : HelperAlike levels O (f.move i) (f'.move i) := by
  obtain ⟨a⟩ := alike
  refine alike_of_lifts (σ := i.frame.hom) (H := f'.helpers) (d := f'.data)
    ((isLift_reindex i.frame.hom f.helpers).twist a.frame a.commutes) (isLift_reindex i.frame.hom f'.helpers)
    ?_ rfl
  show f.data.move (Helpers.lift i.frame.hom f.helpers) =
    f'.data.move (Helpers.lift i.frame.hom f.helpers ≫ a.frame.hom)
  rw [a.data, Natural.move_comp]

omit [DecidableEq O] in
/-- **Moving along the identity gives an alike firing**: its telescope is reindexed along `𝟙`, which
is the old telescope up to the comparison of two lifts. -/
theorem helper_move_refl {s : State rules O} (f : HelperFiring levels O s) :
    HelperAlike levels O (f.move (PlainIso.refl s)) f :=
  alike_of_lifts (σ := 𝟙 s.frame) (H := f.helpers) (d := f.data) (isLift_reindex (𝟙 s.frame) f.helpers)
    (isLift_id f.helpers) rfl (Natural.move_id f.data).symm

omit [DecidableEq O] in
theorem helper_move_trans {s t u : State rules O} (i : PlainIso levels s t) (j : PlainIso levels t u)
    (f : HelperFiring levels O s) : HelperAlike levels O (f.move (i.trans j)) ((f.move i).move j) := by
  refine alike_of_lifts (σ := j.frame.hom ≫ i.frame.hom) (H := f.helpers) (d := f.data)
    (isLift_reindex _ f.helpers)
    ((isLift_reindex i.frame.hom f.helpers).paste (isLift_reindex j.frame.hom (f.helpers.reindex i.frame.hom)))
    rfl ?_
  show (f.data.move (Helpers.lift i.frame.hom f.helpers)).move
      (Helpers.lift j.frame.hom (f.helpers.reindex i.frame.hom)) =
    f.data.move (Helpers.lift j.frame.hom (f.helpers.reindex i.frame.hom) ≫ Helpers.lift i.frame.hom f.helpers)
  rw [Natural.move_comp]

omit [DecidableEq O] in
theorem helper_move_symm {s t : State rules O} (i : PlainIso levels s t) (f : HelperFiring levels O s) :
    HelperAlike levels O ((f.move i).move i.symm) f := by
  have pasted := (isLift_reindex i.frame.hom f.helpers).paste
    (isLift_reindex i.frame.inv (f.helpers.reindex i.frame.hom))
  rw [i.frame.inv_hom_id] at pasted
  refine alike_of_lifts (d := f.data) pasted (isLift_id f.helpers) ?_ (Natural.move_id f.data).symm
  show (f.data.move (Helpers.lift i.frame.hom f.helpers)).move
      (Helpers.lift i.frame.inv (f.helpers.reindex i.frame.hom)) =
    f.data.move (Helpers.lift i.frame.inv (f.helpers.reindex i.frame.hom) ≫ Helpers.lift i.frame.hom f.helpers)
  rw [Natural.move_comp]

/-- **The residual of a firing after another**: its telescope reindexed along the other's weakening,
its data along the lift. -/
def helperResidual {s : State rules O} (g : HelperFiring levels O s) (admitted : (helperStep levels O).Admits g)
    (f : HelperFiring levels O s) : HelperFiring levels O ((helperStep levels O).result g admitted) :=
  ⟨f.helpers.reindex g.helpers.weaken, f.data.move (Helpers.lift g.helpers.weaken f.helpers)⟩

theorem helper_move_residual {s t : State rules O} (i : PlainIso levels s t) (g : HelperFiring levels O s)
    (admitted : (helperStep levels O).Admits g) (f : HelperFiring levels O s) :
    HelperAlike levels O ((helperResidual g admitted f).move (helperResultMove i g admitted))
      (helperResidual (g.move i) ((helper_admits_move i g).mpr admitted) (f.move i)) := by
  have left := (isLift_reindex g.helpers.weaken f.helpers).paste
    (isLift_reindex (Helpers.lift i.frame.hom g.helpers) (f.helpers.reindex g.helpers.weaken))
  rw [Helpers.lift_weaken] at left
  refine alike_of_lifts (d := f.data) left
    ((isLift_reindex i.frame.hom f.helpers).paste
      (isLift_reindex (g.helpers.reindex i.frame.hom).weaken (f.helpers.reindex i.frame.hom))) ?_ ?_
  · show (f.data.move (Helpers.lift g.helpers.weaken f.helpers)).move
        (Helpers.lift (Helpers.lift i.frame.hom g.helpers) (f.helpers.reindex g.helpers.weaken)) =
      f.data.move (Helpers.lift (Helpers.lift i.frame.hom g.helpers) (f.helpers.reindex g.helpers.weaken) ≫
        Helpers.lift g.helpers.weaken f.helpers)
    rw [Natural.move_comp]
  · show (f.data.move (Helpers.lift i.frame.hom f.helpers)).move
        (Helpers.lift (g.helpers.reindex i.frame.hom).weaken (f.helpers.reindex i.frame.hom)) =
      f.data.move (Helpers.lift (g.helpers.reindex i.frame.hom).weaken (f.helpers.reindex i.frame.hom) ≫
        Helpers.lift i.frame.hom f.helpers)
    rw [Natural.move_comp]

variable (levels O) in
/-- **The transport of firings that make telescopes**, with alikeness up to an isomorphism of
telescopes over the frame. -/
noncomputable def helperTransport : Transport (helperStep levels O).toStep where
  Iso s t := PlainIso levels s t
  toStateIso {s t} i := ⟨framesIso i.frame, i.knowledge, Equiv.refl O, by
    show s.present.map (Equiv.refl O).toEmbedding = t.present
    rw [Equiv.refl_toEmbedding, Finset.map_refl, i.present]⟩
  refl := PlainIso.refl
  symm := PlainIso.symm
  trans := PlainIso.trans
  Alike f f' := HelperAlike levels O f f'
  alike_equivalence s := helperAlike_equivalence s
  selection_alike := helper_selection_alike
  admits_alike := helper_admits_alike
  result_alike alike admitted admitted' := helperResultAlike alike admitted admitted'
  move i f := f.move i
  move_alike := helper_move_alike
  move_refl := helper_move_refl
  move_trans := helper_move_trans
  move_symm := helper_move_symm
  selection_move i f := (Natural.selection_move _ f.data).trans (renameSelection_refl _).symm
  admits_move := helper_admits_move
  result_move := helperResultMove
  residual := helperResidual
  selection_residual _ _ f := Natural.selection_move _ f.data
  move_residual := helper_move_residual

/-! ## Diamonds close up to the block exchange -/

/-- **The diamond of two telescope firings closes whenever both orders are admitted**: the two
composites are isomorphic along the block exchange. -/
theorem helper_closes : (helperTransport levels O).Closes := by
  intro s f g first second afterFirst afterSecond
  obtain ⟨H₁, d₁⟩ := f
  obtain ⟨H₂, d₂⟩ := g
  have localFirst := (Natural.admits_withHelpers H₁ d₁).mp first
  have localSecond := (Natural.admits_withHelpers H₂ d₂).mp second
  have typedF := (Natural.shapes_move (H₂.reindex H₁.weaken).weaken d₁ localFirst.1).2.2.2.2
  have typedG := (Natural.shapes_move (Helpers.lift H₁.weaken H₂) d₂ localSecond.1).2.2.2.2
  -- the state after each firing, read at the common frame
  have stateOne : ((Natural.withHelpers H₁ d₁).after first).toLocal.move (H₂.reindex H₁.weaken).weaken =
      (d₁.move (H₂.reindex H₁.weaken).weaken).toPlain.after (jointState H₁ H₂) typedF :=
    (congrArg (Local.move (H₂.reindex H₁.weaken).weaken) (Natural.toLocal_after_withHelpers H₁ d₁ first)).trans
      ((Natural.after_move (H₂.reindex H₁.weaken).weaken d₁ (s.toLocal.move H₁.weaken) localFirst.1.2.2.2.2
        typedF).symm.trans (Plain.after_congr rfl (telescope_state_first H₁ H₂) _ _))
  have stateTwo : ((Natural.withHelpers H₂ d₂).after second).toLocal.move (Helpers.lift H₁.weaken H₂) =
      (d₂.move (Helpers.lift H₁.weaken H₂)).toPlain.after (jointState H₁ H₂) typedG :=
    (congrArg (Local.move (Helpers.lift H₁.weaken H₂)) (Natural.toLocal_after_withHelpers H₂ d₂ second)).trans
      ((Natural.after_move (Helpers.lift H₁.weaken H₂) d₂ (s.toLocal.move H₂.weaken) localSecond.1.2.2.2.2
        typedG).symm.trans (Plain.after_congr rfl (telescope_state_second H₁ H₂) _ _))
  have backFirst : (d₁.move (Helpers.lift H₂.weaken H₁)).move (exchange H₁ H₂) =
      d₁.move (H₂.reindex H₁.weaken).weaken := by
    rw [Natural.move_comp, exchange_lift]
  have backState : (((Natural.withHelpers H₂ d₂).after second).toLocal.move
        (H₁.reindex H₂.weaken).weaken).move (exchange H₁ H₂) =
      (d₂.move (Helpers.lift H₁.weaken H₂)).toPlain.after (jointState H₁ H₂) typedG :=
    (Local.move_comp (H₁.reindex H₂.weaken).weaken (exchange H₁ H₂)
      ((Natural.withHelpers H₂ d₂).after second).toLocal).trans
      ((congrArg (fun σ => Local.move σ ((Natural.withHelpers H₂ d₂).after second).toLocal)
        (exchange_weaken H₁ H₂)).trans stateTwo)
  -- each order is admitted at the common frame
  have gAfterF : (d₂.move (Helpers.lift H₁.weaken H₂)).toPlain.Admits
      ((d₁.move (H₂.reindex H₁.weaken).weaken).toPlain.after (jointState H₁ H₂) typedF) :=
    (Plain.admits_congr rfl stateOne).mp
      ((Natural.admits_withHelpers (s := (Natural.withHelpers H₁ d₁).after first) (H₂.reindex H₁.weaken)
        (d₂.move (Helpers.lift H₁.weaken H₂))).mp afterFirst)
  have fAfterG : (d₁.move (H₂.reindex H₁.weaken).weaken).toPlain.Admits
      ((d₂.move (Helpers.lift H₁.weaken H₂)).toPlain.after (jointState H₁ H₂) typedG) :=
    (Plain.admits_congr (congrArg Natural.toPlain backFirst) backState).mp
      ((Natural.admits_move_iff (d₁.move (Helpers.lift H₂.weaken H₁)) (exchangeIso H₁ H₂) _).mpr
        ((Natural.admits_withHelpers (s := (Natural.withHelpers H₂ d₂).after second) (H₁.reindex H₂.weaken)
          (d₁.move (Helpers.lift H₂.weaken H₁))).mp afterSecond))
  have admitF : (d₁.move (H₂.reindex H₁.weaken).weaken).toPlain.Admits (jointState H₁ H₂) := by
    have moved := Natural.admits_move (H₂.reindex H₁.weaken).weaken d₁ localFirst (by
      rw [← Natural.information_move, telescope_state_first]
      exact Frames.solvable_of_subset (fun e member => List.mem_append_left _ member) gAfterF.2.2.1)
    exact (Plain.admits_congr rfl (telescope_state_first H₁ H₂)).mp moved
  have admitG : (d₂.move (Helpers.lift H₁.weaken H₂)).toPlain.Admits (jointState H₁ H₂) := by
    have moved := Natural.admits_move (Helpers.lift H₁.weaken H₂) d₂ localSecond (by
      rw [← Natural.information_move, telescope_state_second]
      exact Frames.solvable_of_subset (fun e member => List.mem_append_left _ member) fAfterG.2.2.1)
    exact (Plain.admits_congr rfl (telescope_state_second H₁ H₂)).mp moved
  obtain ⟨knowledge, present, label⟩ := agree_of_residuals admitF admitG gAfterF fAfterG
  -- the two composites, read at the common frame
  have one : ((Natural.residualHelpers d₁ d₂ first).after afterFirst).toLocal =
      (d₂.move (Helpers.lift H₁.weaken H₂)).toPlain.after
        ((d₁.move (H₂.reindex H₁.weaken).weaken).toPlain.after (jointState H₁ H₂) typedF) typedG :=
    (Natural.toLocal_after_withHelpers (s := (Natural.withHelpers H₁ d₁).after first) (H₂.reindex H₁.weaken)
      (d₂.move (Helpers.lift H₁.weaken H₂)) afterFirst).trans (Plain.after_congr rfl stateOne _ _)
  have two : ((Natural.residualHelpers d₂ d₁ second).after afterSecond).toLocal.move (exchange H₁ H₂) =
      (d₁.move (H₂.reindex H₁.weaken).weaken).toPlain.after
        ((d₂.move (Helpers.lift H₁.weaken H₂)).toPlain.after (jointState H₁ H₂) typedG) typedF :=
    (congrArg (Local.move (exchange H₁ H₂))
      (Natural.toLocal_after_withHelpers (s := (Natural.withHelpers H₂ d₂).after second) (H₁.reindex H₂.weaken)
        (d₁.move (Helpers.lift H₂.weaken H₁)) afterSecond)).trans
      ((Natural.after_move (exchange H₁ H₂) (d₁.move (Helpers.lift H₂.weaken H₁)) _ afterSecond.1.2.2.2.2
        (Natural.shapes_move (exchange H₁ H₂) (d₁.move (Helpers.lift H₂.weaken H₁)) afterSecond.1).2.2.2.2).symm.trans
        (Plain.after_congr (congrArg Natural.toPlain backFirst) backState _ _))
  have agree : Local.AgreeAlong (levels := levels) (exchange H₁ H₂)
      ((Natural.residualHelpers d₁ d₂ first).after afterFirst).toLocal
      ((Natural.residualHelpers d₂ d₁ second).after afterSecond).toLocal := by
    unfold Local.AgreeAlong
    rw [one, two]
    exact ⟨knowledge, present, label⟩
  exact ⟨(PlainIso.ofAgree (exchangeIso H₁ H₂) agree).symm⟩

/-- **The interface's independence is the admission of both orders.** -/
theorem helper_independent_iff {s : State rules O} {f g : HelperFiring levels O s} :
    (helperTransport levels O).Independent s f g ↔
      ∃ (first : (helperStep levels O).Admits f) (second : (helperStep levels O).Admits g),
        (helperStep levels O).Admits ((helperTransport levels O).residual f first g) ∧
          (helperStep levels O).Admits ((helperTransport levels O).residual g second f) :=
  Transport.independent_iff_admits helper_closes

/-! ## The races layer -/

/-- **Transport-equivalent states are bisimilar**, for every program with invariant labels. -/
theorem helper_bisimilar_of_same {Lab : Type}
    (offers : Lab → (s : State rules O) → HelperFiring levels O s → Prop)
    (invariant : Race.Generic.Invariant (helperStep levels O).toStep offers (helperTransport levels O))
    {s t : State rules O} (same : (helperTransport levels O).Same s t) :
    Race.Generic.Bisimilar (helperStep levels O).toStep offers s t :=
  Race.Generic.bisimilar_of_same (helperTransport levels O) invariant same

/-- **Transport-equivalent states are weakly bisimilar.** -/
theorem helper_weakBisimilar_of_same {Lab : Type}
    (offers : Lab → (s : State rules O) → HelperFiring levels O s → Prop) (internal : Lab → Prop)
    (invariant : Race.Generic.Invariant (helperStep levels O).toStep offers (helperTransport levels O))
    {s t : State rules O} (same : (helperTransport levels O).Same s t) :
    Race.Generic.WeakBisimilar (helperStep levels O).toStep offers internal s t :=
  Race.Generic.weakBisimilar_of_same (helperTransport levels O) invariant same

/-- **Transport-equivalent states are branching bisimilar.** -/
theorem helper_branchingBisimilar_of_same {Lab : Type}
    (offers : Lab → (s : State rules O) → HelperFiring levels O s → Prop) (internal : Lab → Prop)
    (invariant : Race.Generic.Invariant (helperStep levels O).toStep offers (helperTransport levels O))
    {s t : State rules O} (same : (helperTransport levels O).Same s t) :
    Race.Generic.BranchingBisimilar (helperStep levels O).toStep offers internal s t :=
  Race.Generic.branchingBisimilar_of_same (helperTransport levels O) invariant same

end DependentFull

#print axioms DependentFull.isLift_reindex
#print axioms DependentFull.isLift_id
#print axioms DependentFull.IsLift.paste
#print axioms DependentFull.IsLift.twist
#print axioms DependentFull.IsLift.compare
#print axioms DependentFull.liftIso
#print axioms DependentFull.helperStep
#print axioms DependentFull.admits_agree
#print axioms DependentFull.after_agree
#print axioms DependentFull.helperAlike_equivalence
#print axioms DependentFull.helper_admits_move
#print axioms DependentFull.helperResultMove
#print axioms DependentFull.helperResultAlike
#print axioms DependentFull.helper_admits_alike
#print axioms DependentFull.helper_move_refl
#print axioms DependentFull.helper_move_trans
#print axioms DependentFull.helper_move_symm
#print axioms DependentFull.helper_move_residual
#print axioms DependentFull.helperTransport
#print axioms DependentFull.helper_closes
#print axioms DependentFull.helper_independent_iff
#print axioms DependentFull.helper_bisimilar_of_same
#print axioms DependentFull.helper_weakBisimilar_of_same
#print axioms DependentFull.helper_branchingBisimilar_of_same

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
