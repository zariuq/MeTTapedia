import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Conversion.Interp

/-!
# The realizers of the conversion model

The value side states only equalities of realizers. Which terms realize a value,
and how realizers are included in one another, is the conversion model's own:

* **Identity types.** An identity type whose endpoints are related, a point and
  itself among them, is realized by the identity candidate of a true
  proposition: the reflexivity proofs that `E` relates, and the terms reaching
  neutral terms (`DenN.id_real_true`, `DenN.id_diag`). A realizer of an
  identity type that reaches, by typed reduction, a reflexivity proof witnesses
  that its endpoints are related (`DenN.id_endpoints`); one reaching a neutral
  term witnesses nothing.
* **Inclusion.** One candidate is included in another when it relates, at every
  realizer type, only what the other relates there (`ECand.Le`). Meets and the
  constructions are monotone in what they range over.
* **Realizers along world morphisms.** A renamed valid value has every realizer
  of the value (`SInterp.real_rename`, `NInterp.real_rename`,
  `DenN.rename_real`). A function type quantifies over the worlds reached from
  its world, among them those reached from the new world, so its Girard clause
  after the renaming ranges over part of what it ranged over before. A pair has
  realizers growing with those of its projections. At an inductive type, the
  shapes of a renamed value are the renamed shapes of the value, the constructor
  candidates grow with the candidates of their fields, and the closed fields
  carry their realizers along. An identity type realizes by the relation of its
  endpoints, which the renaming keeps. Every other clause realizes all of its
  values alike.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace Conversion

open Normalization
open UniverseLevel (LevelOrder)
open Consistency (World Morph)
open ValueSide (Pack IPack SInterp IndRel IndShape IndShapes HasIndShape HasIndShapes
  closedFields indPack)

variable {Head L : Type} [LevelOrder L]

/-! ## Inclusion of candidates -/

namespace ECand

variable {T : RealizerSide Head L}

/-- Inclusion of candidates: everything the first relates at a realizer type,
the second relates there. -/
def Le (X Y : ECand T) : Prop :=
  ∀ {k : Nat} {Θ : Ctx Head k} {B s s' : Tm Head k}, X.rel Θ B s s' → Y.rel Θ B s s'

theorem Le.refl (X : ECand T) : X.Le X := fun h => h

theorem Le.trans {X Y Z : ECand T} (first : X.Le Y) (second : Y.Le Z) : X.Le Z :=
  fun h => second (first h)

/-- A meet is included in a meet whose members each include a member of the
first family. -/
theorem inter_le_inter {ι κ : Type} {F : ι → ECand T} {G : κ → ECand T}
    (cover : ∀ j, ∃ i, (F i).Le (G j)) : (inter F).Le (inter G) := fun h =>
  ⟨h.1, fun j => by
    obtain ⟨i, le⟩ := cover j
    exact le (h.2 i)⟩

end ECand

variable {M : NModel Head L}

/-! ## Identity types -/

section Identity

variable (laws : M.Laws) {n : Nat} {ξ : World M.reading n} {A a b : Tm Head n} {P : NPack M n}
include laws

/-- **An identity type whose endpoints are related is realized by the identity
candidate of a true proposition.** -/
theorem DenN.id_real_true (den : DenN M ξ (.id A a b) P) {R : NPack M n} (denA : DenN M ξ A R)
    (related : R.rel a b) (t : Tm Head n) : P.real t = ECand.ident M.side True := by
  rw [ValueSide.DenS.id_real laws.value den denA t]
  exact (ecandAlgebra M.side).ident_congr (iff_true_intro related)

/-- **A realizer of an identity type that reaches reflexivity witnesses that
its endpoints are related.** -/
theorem DenN.id_endpoints (den : DenN M ξ (.id A a b) P) {R : NPack M n} (denA : DenN M ξ A R)
    {t : Tm Head n} {m : Nat} {Δ : Ctx Head m} {B x x' u : Tm Head m}
    (real : (P.real t).rel Δ B x x') (red : RedTm M.side.R M.side.roles Δ x (.refl u) B) :
    R.rel a b := by
  rw [ValueSide.DenS.id_real laws.value den denA t] at real
  rcases real with ne | ⟨-, -, -, -, related⟩
  · exact ((ne.left_whnf red (refl_whnf M.side.shape u)).ne_refl rfl).elim
  · exact related

/-- An identity type between a point and itself is realized by the identity
candidate of a true proposition. -/
theorem DenN.id_diag (den : DenN M ξ (.id A a a) P) (t : Tm Head n) :
    P.real t = ECand.ident M.side True := by
  obtain ⟨R, rfl, -, ha, -⟩ := ValueSide.DenS.id_inv laws.value den
  exact (ecandAlgebra M.side).ident_congr (iff_true_intro ha)

end Identity

/-! ## Realizers along world morphisms -/

/-- Along a renaming, `P'` has every realizer of each valid value of `P` at the
renamed value. -/
def RealsRenamed {n m : Nat} (P : NPack M n) (ρ : Ren n m) (P' : NPack M m) : Prop :=
  ∀ {a : Tm Head n}, P.Val a → (P.real a).Le (P'.real (Presentation.rename ρ a))

section Inductive

variable {n m : Nat} {cs : List (DeclName × List (Field Head))} {ρ : Ren n m}
  {field : Tm Head 0 → NPack M n} {field' : Tm Head 0 → NPack M m}

/-- Every shape of a renamed value of an inductive type is matched by a shape of
the value with fewer realizers, when the packs of the closed field types carry
their realizers along the renaming. -/
theorem IndRel.shape_rename (laws : M.Laws) {T : DeclName} (role : M.roles T = .inductive cs)
    (fieldReal : ∀ {F : Tm Head 0}, F ∈ closedFields cs →
      RealsRenamed (field F) ρ (field' F))
    {t : Tm Head n} (valid : IndRel M.value cs field t t) {s' : IndShape Head m}
    (shape' : HasIndShape M.value cs (Presentation.rename ρ t) s') :
    ∃ s, HasIndShape M.value cs t s ∧
      (s.real M.value T field).Le (s'.real M.value T field') := by
  have vlaws := laws.value
  have key : ∀ {t t' : Tm Head n}, IndRel M.value cs field t t' → t = t' →
      ∀ {s' : IndShape Head m}, HasIndShape M.value cs (Presentation.rename ρ t) s' →
        ∃ s, HasIndShape M.value cs t s ∧
          (s.real M.value T field).Le (s'.real M.value T field') := by
    intro t t' related
    refine IndRel.rec
      (motive_1 := fun t t' _ => t = t' →
        ∀ {s' : IndShape Head m}, HasIndShape M.value cs (Presentation.rename ρ t) s' →
          ∃ s, HasIndShape M.value cs t s ∧
            (s.real M.value T field).Le (s'.real M.value T field'))
      (motive_2 := fun fs as as' _ => as = as' →
        (∀ {F : Tm Head 0}, Field.closed F ∈ fs → F ∈ closedFields cs) →
          ∀ {fields' : IndShapes Head m},
            HasIndShapes M.value cs fs (as.map (Presentation.rename ρ)) fields' →
            ∃ fields, HasIndShapes M.value cs fs as fields ∧
              List.Forall₂ ECand.Le (IndShapes.reals M.value T field fields)
                (IndShapes.reals M.value T field' fields'))
      ?_ ?_ ?_ ?_ ?_ related
    · intro k fs t t' as as' mem red red' _ ih same s' shape'
      subst same
      obtain ⟨-, -, rfl⟩ := vlaws.ctorSpine_unique role mem mem red red'
      have redρ := red.rename ρ
      rw [rename_appSpine] at redρ
      cases shape' with
      | ctor mem₁ red₁ shapes₁ =>
          obtain ⟨rfl, rfl, rfl⟩ := vlaws.ctorSpine_unique role mem₁ mem red₁ redρ
          obtain ⟨fields, shapes, incl⟩ :=
            ih rfl (fun hF => ValueSide.mem_closedFields mem hF) shapes₁
          exact ⟨.ctor _ fields, .ctor mem red shapes, fun h => ECand.ctorReal_mono incl h⟩
      | star red₁ daimonic₁ =>
          exact (vlaws.ctorSpine_not_daimonic role mem redρ red₁ daimonic₁).elim
    · intro t t' u u' red daimonic _ _ _ s' shape'
      cases shape' with
      | ctor mem₁ red₁ _ =>
          exact (vlaws.ctorSpine_not_daimonic role mem₁ red₁ (red.rename ρ)
            (daimonic.rename ρ)).elim
      | star _ _ => exact ⟨.star, .star red daimonic, ECand.Le.refl _⟩
    · intro _ _ fields' shapes'
      cases shapes'
      exact ⟨.nil, .nil, .nil⟩
    · intro fs t t' as as' _ _ ihHead ihRest same closed fields' shapes'
      obtain ⟨rfl, rfl⟩ := List.cons.inj same
      cases shapes' with
      | recursive shape rest =>
          obtain ⟨s, hs, incl⟩ := ihHead rfl shape
          obtain ⟨fields, hfields, incls⟩ :=
            ihRest rfl (fun hF => closed (List.mem_cons_of_mem _ hF)) rest
          exact ⟨.recursive s fields, .recursive hs hfields, .cons incl incls⟩
    · intro F fs t t' as as' hF _ ihRest same closed fields' shapes'
      obtain ⟨rfl, rfl⟩ := List.cons.inj same
      cases shapes' with
      | closed rest =>
          obtain ⟨fields, hfields, incls⟩ :=
            ihRest rfl (fun hF' => closed (List.mem_cons_of_mem _ hF')) rest
          exact ⟨.closed F t fields, .closed hfields,
            .cons (fieldReal (closed List.mem_cons_self) hF) incls⟩
  exact key valid rfl shape'

/-- **A renamed valid value of an inductive type has every realizer of the
value**, when the packs of the closed field types carry their realizers along
the renaming. -/
theorem indPack_real_rename (laws : M.Laws) {T : DeclName} (role : M.roles T = .inductive cs)
    (fieldReal : ∀ {F : Tm Head 0}, F ∈ closedFields cs →
      RealsRenamed (field F) ρ (field' F)) :
    RealsRenamed (indPack M.value T cs field) ρ (indPack M.value T cs field') := by
  intro a valid
  refine ECand.inter_le_inter fun s' => ?_
  obtain ⟨s, hs, incl⟩ := IndRel.shape_rename laws role fieldReal valid s'.2
  exact ⟨⟨s, hs⟩, incl⟩

end Inductive

section Rename

variable {l : L} {below : L → IPack M.value}

/-- **Along a world morphism, a renamed valid value has every realizer of the
value**, in every interpretation of the renamed type at the same level. -/
theorem SInterp.real_rename (laws : M.Laws) {n : Nat} {ξ : World M.reading n} {A : Tm Head n}
    {P : NPack M n} (interp : SInterp M.value l below ξ A P) :
    ∀ {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m}, Morph ξ ξ' ρ →
      ∀ {P' : NPack M m}, SInterp M.value l below ξ' (Presentation.rename ρ A) P' →
        RealsRenamed P ρ P' := by
  have vlaws := laws.value
  induction interp with
  | sort isUniverse _ red =>
      intro m ξ' ρ w P' interp' a _ k Θ B s s' h
      obtain ⟨-, rfl⟩ := interp'.univ_inv vlaws (red.rename ρ) isUniverse
      exact h
  | ground notUniverse red =>
      intro m ξ' ρ w P' interp' a _ k Θ B s s' h
      rw [interp'.deterministic vlaws (.ground notUniverse (red.rename ρ))]
      exact h
  | pi red Q domInterp codInterp _ _ _ =>
      intro m ξ' ρ w P' interp' f _
      obtain ⟨Q', rfl, interprets'⟩ := interp'.pi_inv vlaws (red.rename ρ)
      -- The renamed family reads the family at the composite morphisms.
      have dom : ∀ {k : Nat} {ξ'' : World M.reading k} {ρ' : Ren m k} (w' : Morph ξ' ξ'' ρ'),
          Q'.dom w' = Q.dom (w.comp' w') := by
        intro k ξ'' ρ' w'
        have h' := interprets'.dom w'
        rw [rename_comp] at h'
        exact h'.deterministic vlaws (domInterp (w.comp' w'))
      have cod : ∀ {k : Nat} {ξ'' : World M.reading k} {ρ' : Ren m k} (w' : Morph ξ' ξ'' ρ')
          {a : Tm Head k} (ha : (Q'.dom w').Val a) (ha' : (Q.dom (w.comp' w')).Val a),
          Q'.cod w' ha = Q.cod (w.comp' w') ha' := by
        intro k ξ'' ρ' w' a ha ha'
        have h' := interprets'.cod w' ha
        rw [rename_rename_lift] at h'
        exact h'.deterministic vlaws (codInterp (w.comp' w') ha')
      intro k Θ B s s' h
      change (Q.real f).rel Θ B s s' at h
      change (Q'.real (Presentation.rename ρ f)).rel Θ B s s'
      rw [PiPack.real_eq] at h ⊢
      refine ECand.piOver_mono (fun j => ?_) h
      have ha' : (Q.dom (w.comp' j.morph)).Val j.arg := dom j.morph ▸ j.valid
      refine ⟨⟨j.m, j.world, _, w.comp' j.morph, j.arg, ha'⟩, ?_, ?_⟩
      · exact congrArg (fun R : NPack M j.m => R.real j.arg) (dom j.morph).symm
      · change (Q.cod (w.comp' j.morph) ha').real
            (.app (Presentation.rename (fun i => j.ren (ρ i)) f) j.arg) =
          (Q'.cod j.morph j.valid).real
            (.app (Presentation.rename j.ren (Presentation.rename ρ f)) j.arg)
        rw [cod j.morph j.valid ha', rename_rename]
  | @sigma n ξ A dom cod red Q domInterp codInterp codRespect domIH codIH =>
      intro m ξ' ρ w P' interp' p valid
      obtain ⟨Q', rfl, interprets'⟩ := interp'.sigma_inv vlaws (red.rename ρ)
      obtain ⟨hp, _, hc⟩ := valid
      have domI' : SInterp M.value l below ξ' (Presentation.rename ρ
          (Presentation.rename idRen dom)) (Q'.dom (Morph.id ξ')) := by
        have h' := interprets'.dom (Morph.id ξ')
        rw [rename_id] at h'
        rwa [rename_id]
      have domR : RealsRenamed (Q.dom (Morph.id ξ)) ρ (Q'.dom (Morph.id ξ')) :=
        fun {_} valid' => domIH (Morph.id ξ) w domI' valid'
      intro k Θ B s s' h
      change (Q.pairReal p).rel Θ B s s' at h
      change (Q'.pairReal (Presentation.rename ρ p)).rel Θ B s s'
      rw [PiPack.pairReal_eq] at h ⊢
      refine ECand.inter_le_inter (fun hp' => ⟨⟨hp⟩, fun h' => ?_⟩) h
      have codI' : SInterp M.value l below ξ' (Presentation.rename ρ
          (inst0 (.fst p) (Presentation.rename (liftRen idRen) cod)))
          (Q'.cod (Morph.id ξ') hp'.down) := by
        have h'' := interprets'.cod (Morph.id ξ') hp'.down
        rw [liftRen_id, rename_id] at h''
        rw [liftRen_id, rename_id, rename_inst0]
        exact h''
      exact ECand.sigmaOver_mono (domR hp) (codIH (Morph.id ξ) hp w codI' hc) h'
  | ident red R tyInterp _ _ _ =>
      intro m ξ' ρ w P' interp' a _ k Θ B s s' h
      obtain ⟨R', rfl, tyInterp', -, -⟩ := interp'.id_inv vlaws (red.rename ρ)
      obtain ⟨R'', tyInterp'', renamed⟩ := tyInterp.rename vlaws w
      obtain rfl := tyInterp'.deterministic vlaws tyInterp''
      exact ECand.ident_mono renamed.rel h
  | ind red role field fieldInterp fieldIH =>
      intro m ξ' ρ w P' interp' a valid
      obtain ⟨field', rfl, fieldInterp'⟩ := interp'.ind_inv vlaws (red.rename ρ) role
      refine indPack_real_rename laws role (fun {F} hF => ?_) valid
      have h' := fieldInterp' hF
      rw [← rename_liftClosed ρ F] at h'
      exact fun {_} valid' => fieldIH hF w h' valid'
  | prop red =>
      intro m ξ' ρ w P' interp' a _ k Θ B s s' h
      rw [interp'.deterministic vlaws (.prop (red.rename ρ))]
      exact h
  | holds red truth =>
      intro m ξ' ρ w P' interp' a _ k Θ B s s' h
      rw [interp'.deterministic vlaws (.holds (red.rename ρ) (truth.rename w))]
      exact h
  | rigid red role notProp notHolds =>
      intro m ξ' ρ w P' interp' a _ k Θ B s s' h
      have red' := red.rename ρ
      rw [rename_appSpine] at red'
      rw [interp'.deterministic vlaws (.rigid red' role notProp notHolds)]
      exact h
  | daimon red daimonic =>
      intro m ξ' ρ w P' interp' a _ k Θ B s s' h
      rw [interp'.deterministic vlaws (.daimon (red.rename ρ) (daimonic.rename ρ))]
      exact h

end Rename

/-- **Along a world morphism, a renamed valid value has every realizer of the
value**, in the interpretation of the renamed type at the same level. -/
theorem NInterp.real_rename (laws : M.Laws) {l : L} {n : Nat} {ξ : World M.reading n}
    {A : Tm Head n} {P : NPack M n} (interp : NInterp M l ξ A P) {m : Nat}
    {ξ' : World M.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ) :
    ∃ P', NInterp M l ξ' (Presentation.rename ρ A) P' ∧ P.Renamed ρ P' ∧
      RealsRenamed P ρ P' := by
  obtain ⟨P', interp', renamed⟩ := ValueSide.InterpAt.rename laws.value interp w
  exact ⟨P', interp', renamed, SInterp.real_rename laws interp w interp'⟩

/-- **Along a world morphism, a denoted type has a renamed denotation that
relates the renamed values and in which a renamed valid value has every realizer
of the value.** -/
theorem DenN.rename_real (laws : M.Laws) {n : Nat} {ξ : World M.reading n} {A : Tm Head n}
    {P : NPack M n} (den : DenN M ξ A P) {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m}
    (w : Morph ξ ξ' ρ) :
    ∃ P', DenN M ξ' (Presentation.rename ρ A) P' ∧ P.Renamed ρ P' ∧
      RealsRenamed P ρ P' := by
  obtain ⟨l, interp⟩ := den
  obtain ⟨P', interp', renamed, reals⟩ := NInterp.real_rename laws interp w
  exact ⟨P', ⟨l, interp'⟩, renamed, reals⟩

end Conversion
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
