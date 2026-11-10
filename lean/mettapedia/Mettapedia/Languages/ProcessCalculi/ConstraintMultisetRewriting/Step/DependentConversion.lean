import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentPacking

/-!
# Transport of dependent helper firings up to conversion

The isomorphisms of dependent frames (`Frames.Iso` over `frames`) hold only up to conversion: their
composites act as the identity up to convertibility, not on the nose. `helperTransport` therefore
uses strict isomorphisms of telescopes. This module transports dependent helper firings along every
isomorphism of states of the interface, with the functor laws up to conversion.

* **Lifting under a convertible type** (`liftConv`): a substitution lifts under one more variable
  whose type converts to the reindexed type; the newest variable is read at the target type through
  the conversion rule. An isomorphism of frames lifts to the extended frames whenever the new types
  convert (`extendIso`).
* **Alike firings** (`FiringAlike`): the same occurrence, convertible helper types and values, and
  guards that agree equation by equation up to conversion. Alike firings are admitted together and
  have isomorphic results.
* **The transport** (`conversionTransport`): isomorphisms are the interface's isomorphisms of states;
  a firing moves by reindexing; its result moves along the isomorphism lifted under the new variable.
  Moving along an isomorphism and back gives an alike firing (`move_symm`), which need not be equal.

## Controls (`Consumer`)

At the frame `x : g → g`, the frame isomorphism `x ↦ (λy.y) x`, with the identity as inverse, holds
only up to β (`castFrame`). Moving the firing that makes `y : Id (g → g) x x` along it and back gives
a firing of type `Id (g → g) ((λy.y) x) ((λy.y) x)`: different from the original
(`moved_back_ne`) and alike to it (`moved_back_alike`). Firings whose helper types do not convert,
`g → g` against `(g → g) → (g → g)`, are not alike (`not_alike`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

namespace Dependent

open _root_.CategoryTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitiveContextual
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire)

variable {Head : Type} {rules : Rules Head}

/-! ## Lifting under a convertible type -/

/-- **A substitution lifted under one more variable whose type converts to the reindexed type.** -/
def liftConv {Γ Δ : Context rules} (σ : Δ ⟶ Γ) {A : TypeOver Γ} {B : TypeOver Δ}
    (conv : Conv rules.headEq B.code (A.reindex σ).code rules.computation) :
    extend Δ B ⟶ extend Γ A :=
  pair (projectionHom Δ B ≫ σ) (convertTerm (newest Δ B) _ (by
    show Conv rules.headEq (subst projection B.code)
      (subst (subComp projection σ.substitution) A.code) rules.computation
    rw [← subst_subComp]
    exact Conv.substitute _ conv))

theorem liftConv_projection {Γ Δ : Context rules} (σ : Δ ⟶ Γ) {A : TypeOver Γ} {B : TypeOver Δ}
    (conv : Conv rules.headEq B.code (A.reindex σ).code rules.computation) :
    liftConv σ conv ≫ projectionHom Γ A = projectionHom Δ B ≫ σ :=
  pair_projection _ _

theorem liftConv_zero {Γ Δ : Context rules} (σ : Δ ⟶ Γ) {A : TypeOver Γ} {B : TypeOver Δ}
    (conv : Conv rules.headEq B.code (A.reindex σ).code rules.computation) :
    (liftConv σ conv).substitution 0 = .var 0 :=
  rfl

/-- Under the reindexed type itself, lifting through conversion is the strict lift. -/
theorem liftConv_eq_lift {Γ Δ : Context rules} (σ : Δ ⟶ Γ) {A : TypeOver Γ}
    (conv : Conv rules.headEq (A.reindex σ).code (A.reindex σ).code rules.computation) :
    liftConv σ conv = lift σ rfl :=
  hom_ext_extend (by rw [liftConv_projection, lift_projection])
    ((liftConv_zero σ conv).trans (lift_zero σ rfl).symm)

/-- Morphisms into an extended frame are pointwise convertible when their projections and their
newest components are. -/
theorem pointwise_extend {Ξ Γ : Context rules} {A : TypeOver Γ} {f g : Ξ ⟶ extend Γ A}
    (base : ∀ i, Conv rules.headEq ((f ≫ projectionHom Γ A).substitution i)
      ((g ≫ projectionHom Γ A).substitution i) rules.computation)
    (newestConv : Conv rules.headEq (f.substitution 0) (g.substitution 0) rules.computation) :
    ∀ i, Conv rules.headEq (f.substitution i) (g.substitution i) rules.computation := by
  intro i
  refine Fin.cases newestConv (fun j => ?_) i
  exact base j

/-- The two composites of an isomorphism of frames are pointwise convertible to identities. -/
theorem pointwise_inv_hom {Γ Δ : Context rules} (φ : (frames rules).Iso Γ Δ) :
    ∀ i, Conv rules.headEq ((φ.inv ≫ φ.hom).substitution i) (ids i)
      rules.computation :=
  pointwise_of_convertible_reindex (σ := φ.inv ≫ φ.hom) (τ := 𝟙 Γ) fun t => by
    rw [Entry.reindex_comp, Entry.reindex_id]
    exact φ.inv_hom t

theorem pointwise_hom_inv {Γ Δ : Context rules} (φ : (frames rules).Iso Γ Δ) :
    ∀ i, Conv rules.headEq ((φ.hom ≫ φ.inv).substitution i) (ids i)
      rules.computation :=
  pointwise_of_convertible_reindex (σ := φ.hom ≫ φ.inv) (τ := 𝟙 Δ) fun t => by
    rw [Entry.reindex_comp, Entry.reindex_id]
    exact φ.hom_inv t

/-- Pointwise convertible morphisms precomposed with a common morphism stay pointwise convertible. -/
theorem pointwise_comp_left {Ξ Δ Γ : Context rules} (ρ : Ξ ⟶ Δ) {σ τ : Δ ⟶ Γ}
    (pointwise : ∀ i, Conv rules.headEq (σ.substitution i) (τ.substitution i) rules.computation) :
    ∀ i, Conv rules.headEq ((ρ ≫ σ).substitution i) ((ρ ≫ τ).substitution i) rules.computation :=
  fun i => Conv.substitute ρ.substitution (pointwise i)

/-- The type of the inverse lift converts. -/
theorem extendIso_back {Γ Δ : Context rules} (φ : (frames rules).Iso Γ Δ) (A : TypeOver Γ)
    (B : TypeOver Δ) (conv : Conv rules.headEq B.code (A.reindex φ.hom).code rules.computation) :
    Conv rules.headEq A.code (B.reindex φ.inv).code rules.computation := by
  have composite : Conv rules.headEq (subst (φ.inv ≫ φ.hom).substitution A.code)
      (subst ids A.code) rules.computation :=
    Conv.substitutePointwise (pointwise_inv_hom φ) A.code
  have identity : subst ids A.code = A.code := subst_ids A.code
  rw [identity] at composite
  have carried : Conv rules.headEq (subst φ.inv.substitution B.code)
      (subst φ.inv.substitution (subst φ.hom.substitution A.code)) rules.computation :=
    Conv.substitute _ conv
  rw [subst_subComp] at carried
  exact .symm _ _ (.trans _ _ _ carried composite)

/-- The composite of the two lifts, after projection, is the projection followed by the composite
of the frame isomorphism. -/
theorem lift_composite {Γ Δ : Context rules} {A : TypeOver Γ} {B : TypeOver Δ} (σ : Δ ⟶ Γ)
    (τ : Γ ⟶ Δ) (conv : Conv rules.headEq B.code (A.reindex σ).code rules.computation)
    (conv' : Conv rules.headEq A.code (B.reindex τ).code rules.computation) :
    (liftConv τ conv' ≫ liftConv σ conv) ≫ projectionHom Γ A =
      projectionHom Γ A ≫ (τ ≫ σ) := by
  rw [Category.assoc, liftConv_projection, ← Category.assoc, liftConv_projection, Category.assoc]

/-- The composite of the two lifts is pointwise convertible to the identity. -/
theorem lift_composite_pointwise {Γ Δ : Context rules} {A : TypeOver Γ} {B : TypeOver Δ}
    (σ : Δ ⟶ Γ) (τ : Γ ⟶ Δ) (conv : Conv rules.headEq B.code (A.reindex σ).code rules.computation)
    (conv' : Conv rules.headEq A.code (B.reindex τ).code rules.computation)
    (pointwise : ∀ i, Conv rules.headEq ((τ ≫ σ).substitution i) (ids i)
      rules.computation) :
    ∀ i, Conv rules.headEq ((liftConv τ conv' ≫ liftConv σ conv).substitution i)
      (ids i) rules.computation := by
  refine pointwise_extend (g := 𝟙 (extend Γ A)) (fun i => ?_) (.refl _)
  rw [lift_composite, Category.id_comp]
  exact pointwise_comp_left (τ := 𝟙 Γ) (projectionHom Γ A) pointwise i

/-- Convertible reindexing along pointwise convertible composites gives back the entry. -/
theorem convertible_of_pointwise_id {Γ : Context rules} {σ : Γ ⟶ Γ}
    (pointwise : ∀ i, Conv rules.headEq (σ.substitution i) (ids i) rules.computation)
    (t : Entry Γ) : Entry.Convertible (t.reindex σ) t := by
  have converted := convertible_reindex_of_pointwise (τ := 𝟙 Γ) pointwise t
  rwa [Entry.reindex_id] at converted

/-- **An isomorphism of frames lifts under convertible types.** -/
def extendIso {Γ Δ : Context rules} (φ : (frames rules).Iso Γ Δ) (A : TypeOver Γ) (B : TypeOver Δ)
    (conv : Conv rules.headEq B.code (A.reindex φ.hom).code rules.computation) :
    (frames rules).Iso (extend Γ A) (extend Δ B) where
  hom := liftConv φ.hom conv
  inv := liftConv φ.inv (extendIso_back φ A B conv)
  inv_hom t := by
    show Entry.Convertible ((t.reindex (liftConv φ.hom conv)).reindex
      (liftConv φ.inv (extendIso_back φ A B conv))) t
    rw [← Entry.reindex_comp]
    exact convertible_of_pointwise_id
      (lift_composite_pointwise _ _ _ _ (pointwise_inv_hom φ)) t
  hom_inv t := by
    show Entry.Convertible ((t.reindex (liftConv φ.inv (extendIso_back φ A B conv))).reindex
      (liftConv φ.hom conv)) t
    rw [← Entry.reindex_comp]
    exact convertible_of_pointwise_id
      (lift_composite_pointwise _ _ _ _ (pointwise_hom_inv φ)) t

/-! ## Alike firings -/

variable {O : Type}

/-- Stores carried along pointwise convertible morphisms agree equation by equation. -/
theorem forall₂_applyStore {Γ Δ : Context rules} {σ τ : Δ ⟶ Γ}
    (pointwise : ∀ i, Conv rules.headEq (σ.substitution i) (τ.substitution i) rules.computation) :
    ∀ store : EquationStore (Entry Γ),
      List.Forall₂ (fun e e' => (frames rules).E e.1 e'.1 ∧ (frames rules).E e.2 e'.2)
        ((frames rules).applyStore σ store) ((frames rules).applyStore τ store)
  | [] => .nil
  | e :: rest => .cons ⟨convertible_reindex_of_pointwise pointwise e.1,
      convertible_reindex_of_pointwise pointwise e.2⟩ (forall₂_applyStore pointwise rest)

/-- Stores that agree equation by equation still do after a common morphism. -/
theorem forall₂_applyStore_congr {Γ Δ : Context rules} (σ : Δ ⟶ Γ) :
    ∀ {one two : EquationStore (Entry Γ)},
      List.Forall₂ (fun e e' => (frames rules).E e.1 e'.1 ∧ (frames rules).E e.2 e'.2) one two →
      List.Forall₂ (fun e e' => (frames rules).E e.1 e'.1 ∧ (frames rules).E e.2 e'.2)
        ((frames rules).applyStore σ one) ((frames rules).applyStore σ two)
  | _, _, .nil => .nil
  | _, _, .cons head rest => .cons ⟨(frames rules).preserves σ head.1, (frames rules).preserves σ head.2⟩
      (forall₂_applyStore_congr σ rest)

/-- **Alike dependent helper firings**: the same occurrence, convertible helper types and values, and
guards that agree equation by equation up to conversion. -/
def FiringAlike {s : State rules O} (f f' : Firing s) : Prop :=
  f.made = f'.made ∧ Conv rules.headEq f.helper.code f'.helper.code rules.computation ∧
    Conv rules.headEq f.value.code f'.value.code rules.computation ∧
    List.Forall₂ (fun e e' => (frames rules).E e.1 e'.1 ∧ (frames rules).E e.2 e'.2) f.guards f'.guards

namespace FiringAlike

variable {s : State rules O}

theorem refl (f : Firing s) : FiringAlike f f :=
  ⟨rfl, .refl _, .refl _, List.forall₂_same.mpr fun _ _ => ⟨Entry.Convertible.refl _, Entry.Convertible.refl _⟩⟩

theorem symm {f f' : Firing s} (alike : FiringAlike f f') : FiringAlike f' f :=
  ⟨alike.1.symm, .symm _ _ alike.2.1, .symm _ _ alike.2.2.1,
    forall₂_swap (fun _ _ same => ⟨same.1.symm, same.2.symm⟩) alike.2.2.2⟩

theorem trans {f f' f'' : Firing s} (first : FiringAlike f f') (second : FiringAlike f' f'') :
    FiringAlike f f'' :=
  ⟨first.1.trans second.1, .trans _ _ _ first.2.1 second.2.1, .trans _ _ _ first.2.2.1 second.2.2.1,
    forall₂_comp (fun _ _ _ one two => ⟨one.1.trans two.1, one.2.trans two.2⟩) first.2.2.2 second.2.2.2⟩

theorem of_eq {f f' : Firing s} (same : f = f') : FiringAlike f f' := same ▸ refl f

/-- Carrying along a substitution and a renaming keeps alikeness. -/
theorem carry {t : State rules O} (π : O ≃ O) (σ : t.frame ⟶ s.frame) {f f' : Firing s}
    (alike : FiringAlike f f') : FiringAlike (f.carry (t := t) π σ) (f'.carry (t := t) π σ) :=
  ⟨congrArg π alike.1, Conv.substitute _ alike.2.1, Conv.substitute _ alike.2.2.1,
    forall₂_applyStore_congr σ alike.2.2.2⟩

/-- A firing moved along a morphism pointwise convertible to the identity is alike to itself. -/
theorem of_pointwise (f : Firing s) {σ : s.frame ⟶ s.frame}
    (pointwise : ∀ i, Conv rules.headEq (σ.substitution i) (ids i)
      rules.computation) : FiringAlike (f.move (t := s) σ) f := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · have converted := Conv.substitutePointwise pointwise f.helper.code
    rwa [subst_ids] at converted
  · have converted := Conv.substitutePointwise pointwise f.value.code
    rwa [subst_ids] at converted
  · have related := forall₂_applyStore (τ := 𝟙 s.frame) pointwise f.guards
    rwa [show (frames rules).applyStore (𝟙 s.frame) f.guards = f.guards from
      Frames.applyStore_id (X := frames rules) f.guards] at related

end FiringAlike

variable [DecidableEq O]

/-- **Alike firings are admitted together.** -/
theorem admits_alike {s : State rules O} {f f' : Firing s} (alike : FiringAlike f f') :
    (helperStep (rules := rules)).Admits f ↔ (helperStep (rules := rules)).Admits f' := by
  rw [admits_iff, admits_iff, alike.1]
  refine and_congr Iff.rfl (and_congr Iff.rfl ⟨fun asked Δ σ solved => ?_, fun asked Δ σ solved => ?_⟩)
  · exact (Frames.equivalent_of_forall₂ (X := frames rules) alike.2.2.2 Δ σ).mp (asked Δ σ solved)
  · exact (Frames.equivalent_of_forall₂ (X := frames rules) alike.2.2.2 Δ σ).mpr (asked Δ σ solved)

omit [DecidableEq O] in
/-- The helper types of alike firings convert along the identity of the old frame. -/
theorem alikeConv {s : State rules O} {f f' : Firing s} (alike : FiringAlike f f') :
    Conv rules.headEq f'.helper.code
      (f.helper.reindex (Frames.Iso.refl (X := frames rules) s.frame).hom).code rules.computation := by
  have identity : f.helper.reindex (Frames.Iso.refl (X := frames rules) s.frame).hom = f.helper :=
    f.helper.reindex_id
  rw [identity]
  exact .symm _ _ alike.2.1

/-- The isomorphism of the results of alike firings: the identity of the old frame, lifted under the
two convertible helper types. -/
def alikeFrame {s : State rules O} {f f' : Firing s} (alike : FiringAlike f f') :
    (frames rules).Iso (extend s.frame f.helper) (extend s.frame f'.helper) :=
  extendIso (Frames.Iso.refl s.frame) f.helper f'.helper (alikeConv alike)

omit [DecidableEq O] in
/-- **Alike firings have results with the same solutions** along the lifted identity. -/
theorem information_alike {s : State rules O} {f f' : Firing s} (alike : FiringAlike f f') :
    (frames rules).Equivalent
      ((frames rules).applyStore (alikeFrame alike).hom f.information) f'.information := by
  apply Frames.equivalent_of_forall₂
  have base : (alikeFrame alike).hom ≫ projectionHom s.frame f.helper =
      projectionHom s.frame f'.helper :=
    (liftConv_projection (Frames.Iso.refl (X := frames rules) s.frame).hom (alikeConv alike)).trans
      (Category.comp_id _)
  unfold Firing.information Firing.tell
  rw [Frames.applyStore_append, Frames.applyStore_applyStore]
  refine forall₂_append ?_ (.cons ⟨⟨?_, .refl _⟩, ⟨?_, ?_⟩⟩ .nil)
  · show List.Forall₂ _ ((frames rules).applyStore ((alikeFrame alike).hom ≫ projectionHom s.frame f.helper)
      s.knowledge) ((frames rules).applyStore (projectionHom s.frame f'.helper) s.knowledge)
    rw [base]
    exact List.forall₂_same.mpr fun _ _ => ⟨Entry.Convertible.refl _, Entry.Convertible.refl _⟩
  · show Conv rules.headEq (subst (alikeFrame alike).hom.substitution (subst projection f.helper.code))
      (subst projection f'.helper.code) rules.computation
    rw [subst_subComp]
    show Conv rules.headEq (subst ((alikeFrame alike).hom ≫ projectionHom s.frame f.helper).substitution
      f.helper.code) _ rules.computation
    rw [base]
    exact Conv.substitute _ alike.2.1
  · show Conv rules.headEq (subst (alikeFrame alike).hom.substitution (subst projection f.helper.code))
      (subst projection f'.helper.code) rules.computation
    rw [subst_subComp]
    show Conv rules.headEq (subst ((alikeFrame alike).hom ≫ projectionHom s.frame f.helper).substitution
      f.helper.code) _ rules.computation
    rw [base]
    exact Conv.substitute _ alike.2.1
  · show Conv rules.headEq (subst (alikeFrame alike).hom.substitution (subst projection f.value.code))
      (subst projection f'.value.code) rules.computation
    rw [subst_subComp]
    show Conv rules.headEq (subst ((alikeFrame alike).hom ≫ projectionHom s.frame f.helper).substitution
      f.value.code) _ rules.computation
    rw [base]
    exact Conv.substitute _ alike.2.2.1

/-! ## Transport up to conversion -/

/-- A firing carried along an isomorphism of states is admitted exactly when it is. -/
theorem admits_move_iff {s t : State rules O} (i : (helperStep (rules := rules) (O := O)).StateIso s t)
    (f : Firing s) :
    (helperStep (rules := rules)).Admits (f.carry (t := t) i.rename i.frame.hom) ↔
      (helperStep (rules := rules)).Admits f := by
  rw [admits_iff, admits_iff]
  exact and_congr i.solvable_iff.symm (and_congr (not_congr (i.mem_present_iff f.made))
    ((Frames.Equivalent.entails_iff i.knowledge _).symm.trans
      (Frames.Iso.entails_applyStore_iff i.frame s.knowledge f.guards)))

/-- **Transport of dependent helper firings up to conversion**: along every isomorphism of states of
the interface, with alikeness up to conversion. -/
def conversionTransport : Transport (helperStep (rules := rules) (O := O)).toStep where
  Iso s t := (helperStep (rules := rules) (O := O)).StateIso s t
  toStateIso i := i
  refl s := Step.StateIso.refl s
  symm i := i.symm
  trans i j := i.trans j
  Alike f f' := FiringAlike f f'
  alike_equivalence _ := ⟨FiringAlike.refl, FiringAlike.symm, FiringAlike.trans⟩
  selection_alike alike := by
    show Firing.selection _ = Firing.selection _
    rw [Firing.selection, Firing.selection, alike.1]
  admits_alike alike := admits_alike alike
  result_alike {s} {f f'} alike _ _ :=
    ⟨alikeFrame alike, information_alike alike, Equiv.refl O, by
      show (fire s.present (f.selection.commit (T := Unit))).map (Equiv.refl O).toEmbedding =
        fire s.present (f'.selection.commit (T := Unit))
      rw [Equiv.refl_toEmbedding, Finset.map_refl, Firing.selection, Firing.selection, alike.1]⟩
  move i f := f.carry i.rename i.frame.hom
  move_alike i _ _ alike := FiringAlike.carry i.rename i.frame.hom alike
  move_refl f := FiringAlike.of_eq (Firing.move_id f)
  move_trans i j f := by
    have composite := (Firing.move_move f i.frame.hom j.frame.hom).symm
    have helper := congrArg Firing.helper composite
    have value := congrArg (fun g : Firing _ => g.value.code) composite
    have guards := congrArg Firing.guards composite
    exact FiringAlike.of_eq (Firing.ext rfl helper value guards)
  move_symm i f := by
    have back := FiringAlike.of_pointwise f (pointwise_inv_hom i.frame)
    rw [← Firing.move_move] at back
    exact ⟨i.rename.symm_apply_apply f.made, back.2⟩
  selection_move _ _ := rfl
  admits_move i f := admits_move_iff i f
  result_move {s t} i f _ :=
    ⟨extendIso i.frame f.helper (f.helper.reindex i.frame.hom)
      (Relation.EqvGen.refl (f.helper.reindex i.frame.hom).code), by
      have lifted := liftConv_eq_lift i.frame.hom (A := f.helper)
        (Relation.EqvGen.refl (f.helper.reindex i.frame.hom).code)
      have carried := information_move_along i.frame.hom i.knowledge f
      rw [← lifted] at carried
      exact carried, i.rename, by
      show (fire s.present (f.selection.commit (T := Unit))).map i.rename.toEmbedding =
        fire t.present ((AnnotatedRuns.renameSelection i.rename f.selection).commit (T := Unit))
      have present : s.present.map i.rename.toEmbedding = t.present := i.present
      rw [← present]
      exact (AnnotatedRuns.fire_rename s.present f.selection).symm⟩
  residual g admitted f := f.move ((helperStep (rules := rules)).along g admitted)
  selection_residual _ _ _ := rfl
  move_residual {s t} i g admitted f := FiringAlike.of_eq (by
    have lifted := liftConv_eq_lift i.frame.hom (A := g.helper)
      (Relation.EqvGen.refl (g.helper.reindex i.frame.hom).code)
    have natural := move_along_lift (t := t) i.rename i.frame.hom g admitted f
      ((admits_move_iff i g).mpr admitted)
    rw [← lifted] at natural
    exact natural)

/-- **Strict transport is the case where the isomorphisms are strict**: every strict isomorphism is
an isomorphism of this transport, and moving along it is the same move. -/
theorem conversion_move_strict {s t : State rules O} (i : Strict s t) (f : Firing s) :
    (conversionTransport (rules := rules) (O := O)).move i.toStateIso f =
      (helperTransport (rules := rules) (O := O)).move i f :=
  rfl

/-! ## Controls -/

namespace Consumer

/-- The frame `x : g → g`. -/
abbrev arrowFrame : Context tiny := extend (empty tiny) arrowType

/-- `(λy.y) x : g → g` at the frame `x : g → g`. -/
def castValue : Term arrowFrame (arrowType.reindex (projectionHom (empty tiny) arrowType)) :=
  ⟨.app (.lam (.var 0)) (.var 0),
    .appElim (.lamIntro (.piForm (arrow_formed _) rfl (arrow_formed _) rfl ⟨rfl, rfl, rfl⟩) rfl (.var 0))
      (.var 0)⟩

/-- The substitution `x ↦ (λy.y) x`. -/
def castHom : arrowFrame ⟶ arrowFrame := pair (projectionHom (empty tiny) arrowType) castValue

theorem castHom_pointwise :
    ∀ i, Conv tiny.headEq (castHom.substitution i) (ids i) tiny.computation := by
  intro i
  refine Fin.cases ?_ (fun j => j.elim0) i
  exact .rel _ _ (.betaPi _ _)

theorem castHom_convertible (t : Entry arrowFrame) : Entry.Convertible (t.reindex castHom) t :=
  convertible_of_pointwise_id castHom_pointwise t

/-- **The frame isomorphism `x ↦ (λy.y) x`, with the identity as inverse**: its inverse laws hold
only up to β. -/
def castFrame : (frames tiny).Iso arrowFrame arrowFrame where
  hom := castHom
  inv := 𝟙 arrowFrame
  inv_hom t := by
    show Entry.Convertible ((t.reindex castHom).reindex (𝟙 arrowFrame)) t
    rw [Entry.reindex_id]
    exact castHom_convertible t
  hom_inv t := by
    show Entry.Convertible ((t.reindex (𝟙 arrowFrame)).reindex castHom) t
    rw [Entry.reindex_id]
    exact castHom_convertible t

/-- The isomorphism of the state the first firing made, along `castFrame`. -/
def castIso : (helperStep (rules := tiny) (O := Nat)).StateIso first.after first.after where
  frame := castFrame
  knowledge := by
    apply Frames.equivalent_of_forall₂
    have related := forall₂_applyStore (τ := 𝟙 arrowFrame) castHom_pointwise first.information
    rwa [show (frames tiny).applyStore (𝟙 arrowFrame) first.information = first.information from
      Frames.applyStore_id (X := frames tiny) _] at related
  rename := Equiv.refl Nat
  present := by rw [Equiv.refl_toEmbedding, Finset.map_refl]

/-- `dependent` moved along `castIso`, and back. -/
abbrev movedBack : Firing first.after :=
  conversionTransport.move (conversionTransport.symm castIso) (conversionTransport.move castIso dependent)

/-- **Moving along the isomorphism and back changes the firing**: its helper type becomes
`Id (g → g) ((λy.y) x) ((λy.y) x)`. -/
theorem moved_back_ne : movedBack ≠ dependent := by
  intro same
  have codes := congrArg (fun f : Firing first.after => f.helper.code) same
  change (Tm.id _ _ _ : Tm TinyHead 1) = .id _ (.var 0) (.var 0) at codes
  injection codes with _ _ left _
  change subst ids (Tm.app (Tm.lam (Tm.var 0)) (Tm.var 0)) = Tm.var 0 at left
  rw [subst_ids] at left
  cases left

/-- **The transport moves it back up to conversion**: the moved-back firing is alike to it. -/
theorem moved_back_alike : conversionTransport.Alike movedBack dependent :=
  conversionTransport.move_symm castIso dependent

/-- The firing that makes a helper `z : g → g` valued `x`. -/
def copyArrow : Firing first.after :=
  ⟨5, ⟨arrow, .universe, rfl, arrow_formed _⟩, ⟨.var 0, .var 0⟩, []⟩

/-- `(g → g) → (g → g)` over a telescope. -/
def higher {n : Nat} : Tm TinyHead n := .pi arrow arrow

theorem higher_formed {n : Nat} (Γ : Ctx TinyHead n) :
    FormationSensitive.Typing tiny Γ higher (.head .universe) :=
  .piForm (arrow_formed Γ) rfl (arrow_formed _) rfl ⟨rfl, rfl, rfl⟩

/-- The firing that makes a helper `z : (g → g) → (g → g)` valued `λf.f`. -/
def copyHigher : Firing first.after :=
  ⟨5, ⟨higher, .universe, rfl, higher_formed _⟩, ⟨.lam (.var 0), .lamIntro (higher_formed _) rfl (.var 0)⟩,
    []⟩

/-- **Firings whose helper types do not convert are not alike.** -/
theorem not_alike : ¬ conversionTransport.Alike copyArrow copyHigher := by
  intro alike
  obtain ⟨-, types, -⟩ := (alike : FiringAlike copyArrow copyHigher)
  change Conv tiny.headEq (.pi (.head .ground) (.head .ground)) (.pi arrow arrow) tiny.computation at types
  have domains := ((EmptyRootConversion.piConversionBoundary tiny rfl tiny_symm).components types).1
  exact (EmptyRootConversion.piConversionBoundary tiny rfl tiny_symm).headDisjoint (.symm _ _ domains)

end Consumer

end Dependent

#print axioms Dependent.liftConv
#print axioms Dependent.liftConv_eq_lift
#print axioms Dependent.extendIso
#print axioms Dependent.admits_alike
#print axioms Dependent.information_alike
#print axioms Dependent.conversionTransport
#print axioms Dependent.conversion_move_strict
#print axioms Dependent.Consumer.castFrame
#print axioms Dependent.Consumer.castIso
#print axioms Dependent.Consumer.moved_back_ne
#print axioms Dependent.Consumer.moved_back_alike
#print axioms Dependent.Consumer.not_alike

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
