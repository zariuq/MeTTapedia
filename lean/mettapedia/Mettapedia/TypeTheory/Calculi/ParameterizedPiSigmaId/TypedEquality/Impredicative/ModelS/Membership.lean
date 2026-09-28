import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ValueSide.Denotation
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.ModelS.KCandAlgebra

/-!
# Model S and the membership of its realizers

Model S reads a rule package with the value side's reduction, levels in a level
order, a daimon, and a realizer side whose Kripke candidates realize its values
(`kcandAlgebra`). Its laws are those of the value side without the laws of the
realizer algebra, which the Kripke candidates satisfy (`kcandAlgebra_laws`).

The value side states only equalities of realizers. Membership is model S's own:

* a function is realized by the strongly normalizing terms that send, after any
  renaming, every realizer of every valid argument, at every world reached by a
  morphism, to a realizer of the result (`PiPack.mem_real`); a pair by the
  strongly normalizing terms whose projections realize the projections of the
  pair, when its first projection is valid (`PiPack.mem_pairReal`);
* an identity type whose endpoints are related, a point and itself among them,
  is realized by the strongly normalizing terms (`DenS.id_real_sn`,
  `DenS.id_diag`), and a realizer of it that reduces to reflexivity witnesses
  that its endpoints are related (`DenS.id_endpoints`);
* along a world morphism, a renamed valid value has every realizer of the value
  (`SInterp.real_rename`, `DenS.rename_real`). A function type quantifies over
  the worlds reached from its world, among them those reached from the new
  world. At an inductive type, the shapes of a renamed value are the renamed
  shapes of the value, the constructor candidates grow with the candidates of
  their fields (`ctorCand_mono`), and the closed fields carry their realizers
  along. Every other clause realizes all of its values alike, or reads a
  proposition that the renaming keeps.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace TypedEquality
namespace Impredicative
namespace ModelS

open Normalization
open UniverseLevel (LevelOrder)
open Consistency (Reading World Morph Truth)
open Realizability (Realizers Daimonic)
open StrongNormalization
open ValueSide

variable {Head L : Type} [LevelOrder L]

/-! ## The model -/

/-- Model S: the consistency model's reading of a package, universe levels in a
level order `L`, a daimon, and a realizer side. -/
structure SModel (Head L : Type) [LevelOrder L] extends Consistency.Model Head L where
  star : DeclName
  realizers : Realizers Head

namespace SModel

variable (M : SModel Head L)

/-- The value model of model S: its values are realized by the Kripke candidates
of the realizer side. -/
def value : ValueSide.Model Head L where
  toModel := M.toModel
  star := M.star
  alg := kcandAlgebra M.realizers

/-- The reading of codes of model S. -/
abbrev reading : Reading Head := M.value.reading

/-- The Kripke candidates of the realizer side. -/
abbrev Cand : Type := M.realizers.Cand

/-- The laws of model S: those of the consistency model, the daimon rigid and
distinct from the type of codes and from the decoder, and the listed
constructors of inductive types declared as constructors. -/
structure Laws : Prop where
  values : M.toModel.Laws
  star : M.roles M.star = .rigid
  starNotProp : M.star ≠ M.prop
  starNotHolds : M.star ≠ M.holds
  declared : ConstructorsDeclared M.roles

variable {M}

/-- The laws of the value model of model S. -/
theorem Laws.value (laws : M.Laws) : M.value.Laws :=
  ⟨laws.values, laws.star, laws.starNotProp, laws.starNotHolds, kcandAlgebra_laws M.realizers,
    laws.declared⟩

end SModel

variable {M : SModel Head L}

/-! ## Functions and pairs -/

namespace PiPack

variable {n : Nat} {ξ : World M.reading n} (P : ValueSide.PiPack M.value ξ)

/-- **The realizers of a function**: the strongly normalizing terms that send,
after any renaming, every realizer of every valid argument at every world
reached by a morphism to a realizer of the result. -/
theorem mem_real {f : Tm Head n} {r : Nat} {t : Tm Head r} :
    (P.real f).mem t ↔ SN M.realizers.rules t ∧
      ∀ {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m} (w : Morph ξ ξ' ρ) {a : Tm Head m}
        (ha : (P.dom w).Val a) {r' : Nat} (ρr : Ren r r') (u : Tm Head r'),
          ((P.dom w).real a).mem u →
            ((P.cod w ha).real (.app (Presentation.rename ρ f) a)).mem
              (.app (Presentation.rename ρr t) u) :=
  ⟨fun h => ⟨h.1, fun w a ha _ ρr u hu => h.2 ⟨_, _, _, w, a, ha⟩ ρr u hu⟩,
    fun h => ⟨h.1, fun a {_} ρr u hu => h.2 a.morph a.valid ρr u hu⟩⟩

/-- **The realizers of a pair**: the strongly normalizing terms whose projections
realize the projections of the pair, when its first projection is valid. -/
theorem mem_pairReal {p : Tm Head n} {r : Nat} {t : Tm Head r} :
    (P.pairReal p).mem t ↔ SN M.realizers.rules t ∧
      ∀ hp : (P.dom (Morph.id ξ)).Val (.fst p),
        ((P.dom (Morph.id ξ)).real (.fst p)).mem (.fst t) ∧
          ((P.cod (Morph.id ξ) hp).real (.snd p)).mem (.snd t) :=
  ⟨fun h => ⟨h.1, fun hp => h.2 ⟨hp⟩⟩, fun h => ⟨h.1, fun hp => h.2 hp.down⟩⟩

end PiPack

/-! ## Identity types -/

/-- An identity type is realized by the strongly normalizing terms that reduce to
reflexivity only when its endpoints are related. -/
theorem identPack_real {n : Nat} (R : Pack M.value n) (lhs rhs t : Tm Head n) :
    (identPack R lhs rhs).real t = IdCand M.realizers.reflects (R.rel lhs rhs) :=
  rfl

/-- **An identity type whose endpoints are related is realized by the strongly
normalizing terms.** -/
theorem DenS.id_real_sn (laws : M.Laws) {n : Nat} {ξ : World M.reading n} {A a b : Tm Head n}
    {P : Pack M.value n} (den : DenS M.value ξ (.id A a b) P) {R : Pack M.value n}
    (denA : DenS M.value ξ A R) (related : R.rel a b) (t : Tm Head n) :
    P.real t = M.realizers.sn := by
  rw [ValueSide.DenS.id_real laws.value den denA t]
  exact IdCand.of_holds M.realizers.reflects related

/-- A realizer of an identity type that reduces to reflexivity witnesses that
its endpoints are related. -/
theorem DenS.id_endpoints (laws : M.Laws) {n : Nat} {ξ : World M.reading n} {A a b : Tm Head n}
    {P : Pack M.value n} (den : DenS M.value ξ (.id A a b) P) {R : Pack M.value n}
    (denA : DenS M.value ξ A R) {t : Tm Head n} {r : Nat} {x u : Tm Head r}
    (real : (P.real t).mem x) (steps : ReducesStar M.realizers.rules x (.refl u)) :
    R.rel a b := by
  rw [ValueSide.DenS.id_real laws.value den denA t] at real
  exact real.2 u steps

/-- An identity type between a point and itself is realized by the strongly
normalizing terms. -/
theorem DenS.id_diag (laws : M.Laws) {n : Nat} {ξ : World M.reading n} {A a : Tm Head n}
    {P : Pack M.value n} (den : DenS M.value ξ (.id A a a) P) (t : Tm Head n) :
    P.real t = M.realizers.sn := by
  obtain ⟨R, rfl, -, ha, -⟩ := ValueSide.DenS.id_inv laws.value den
  exact IdCand.of_holds M.realizers.reflects ha

/-! ## Constructor candidates -/

/-- Inclusion of Kripke candidates. -/
def Incl (X Y : M.Cand) : Prop :=
  ∀ {r : Nat} {t : Tm Head r}, X.mem t → Y.mem t

/-- A list of candidates included pointwise in another sends members of the
first, pointwise, to members of the second. -/
theorem forall₂_incl {Xs Ys : List M.Cand} (incl : List.Forall₂ Incl Xs Ys) {r : Nat}
    {us : List (Tm Head r)} (mem : List.Forall₂ (fun (X : M.Cand) u => X.mem u) Xs us) :
    List.Forall₂ (fun (Y : M.Cand) u => Y.mem u) Ys us := by
  induction incl generalizing us with
  | nil =>
      cases mem
      exact .nil
  | cons head _ ih =>
      cases mem with
      | cons hu rest => exact .cons (head hu) (ih rest)

/-- **The constructor candidates grow with the candidates of their fields.** -/
theorem ctorCand_mono (tyName k : DeclName) {Xs Ys : List M.Cand} (incl : List.Forall₂ Incl Xs Ys) :
    Incl (ctorCand M.realizers tyName k Xs) (ctorCand M.realizers tyName k Ys) := by
  intro r t h
  refine ⟨h.1, h.2.1, fun us reach => ?_⟩
  rw [← incl.length_eq] at reach
  exact forall₂_incl incl (h.2.2 us reach)

/-! ## Realizers along world morphisms -/

/-- Along a renaming, `P'` has every realizer of each valid value of `P` at the
renamed value. -/
def RealsRenamed {n m : Nat} (P : Pack M.value n) (ρ : Ren n m) (P' : Pack M.value m) : Prop :=
  ∀ {a : Tm Head n}, P.Val a → Incl (P.real a) (P'.real (Presentation.rename ρ a))

section Inductive

variable {n m : Nat} {cs : List (DeclName × List (Field Head))} {ρ : Ren n m}
  {field : Tm Head 0 → Pack M.value n} {field' : Tm Head 0 → Pack M.value m}

/-- Every shape of a renamed value of an inductive type is matched by a shape of
the value with fewer realizers, when the packs of the closed field types carry
their realizers along the renaming. -/
theorem IndRel.shape_rename (laws : M.Laws) {T : DeclName} (role : M.roles T = .inductive cs)
    (fieldReal : ∀ {F : Tm Head 0}, F ∈ closedFields cs → RealsRenamed (field F) ρ (field' F))
    {t : Tm Head n} (valid : IndRel M.value cs field t t) {s' : IndShape Head m}
    (shape' : HasIndShape M.value cs (Presentation.rename ρ t) s') :
    ∃ s, HasIndShape M.value cs t s ∧ Incl (s.real M.value T field) (s'.real M.value T field') := by
  have vlaws := laws.value
  have key : ∀ {t t' : Tm Head n}, IndRel M.value cs field t t' → t = t' →
      ∀ {s' : IndShape Head m}, HasIndShape M.value cs (Presentation.rename ρ t) s' →
        ∃ s, HasIndShape M.value cs t s ∧
          Incl (s.real M.value T field) (s'.real M.value T field') := by
    intro t t' related
    refine IndRel.rec
      (motive_1 := fun t t' _ => t = t' →
        ∀ {s' : IndShape Head m}, HasIndShape M.value cs (Presentation.rename ρ t) s' →
          ∃ s, HasIndShape M.value cs t s ∧
            Incl (s.real M.value T field) (s'.real M.value T field'))
      (motive_2 := fun fs as as' _ => as = as' →
        (∀ {F : Tm Head 0}, Field.closed F ∈ fs → F ∈ closedFields cs) →
          ∀ {fields' : IndShapes Head m},
            HasIndShapes M.value cs fs (as.map (Presentation.rename ρ)) fields' →
            ∃ fields, HasIndShapes M.value cs fs as fields ∧
              List.Forall₂ Incl (IndShapes.reals M.value T field fields)
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
          obtain ⟨fields, shapes, incl⟩ := ih rfl (fun hF => mem_closedFields mem hF) shapes₁
          exact ⟨.ctor _ fields, .ctor mem red shapes, ctorCand_mono T _ incl⟩
      | star red₁ daimonic₁ =>
          exact (vlaws.ctorSpine_not_daimonic role mem redρ red₁ daimonic₁).elim
    · intro t t' u u' red daimonic _ _ _ s' shape'
      cases shape' with
      | ctor mem₁ red₁ _ =>
          exact (vlaws.ctorSpine_not_daimonic role mem₁ red₁ (red.rename ρ)
            (daimonic.rename ρ)).elim
      | star _ _ => exact ⟨.star, .star red daimonic, fun h => h⟩
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
    (fieldReal : ∀ {F : Tm Head 0}, F ∈ closedFields cs → RealsRenamed (field F) ρ (field' F)) :
    RealsRenamed (indPack M.value T cs field) ρ (indPack M.value T cs field') := by
  intro a valid r t h
  refine ⟨h.1, fun s' => ?_⟩
  obtain ⟨s, hs, incl⟩ := IndRel.shape_rename laws role fieldReal valid s'.2
  exact incl (h.2 ⟨s, hs⟩)

end Inductive

section Rename

variable {l : L} {below : L → IPack M.value}

/-- **Along a world morphism, a renamed valid value has every realizer of the
value**, in every interpretation of the renamed type at the same level. -/
theorem SInterp.real_rename (laws : M.Laws) {n : Nat} {ξ : World M.reading n} {A : Tm Head n}
    {P : Pack M.value n} (interp : SInterp M.value l below ξ A P) :
    ∀ {m : Nat} {ξ' : World M.reading m} {ρ : Ren n m}, Morph ξ ξ' ρ →
      ∀ {P' : Pack M.value m}, SInterp M.value l below ξ' (Presentation.rename ρ A) P' →
        RealsRenamed P ρ P' := by
  have vlaws := laws.value
  induction interp with
  | sort isUniverse _ red =>
      intro m ξ' ρ w P' interp' a _ r t h
      obtain ⟨-, rfl⟩ := interp'.univ_inv vlaws (red.rename ρ) isUniverse
      exact h
  | ground notUniverse red =>
      intro m ξ' ρ w P' interp' a _ r t h
      rw [interp'.deterministic vlaws (.ground notUniverse (red.rename ρ))]
      exact h
  | pi red Q domInterp codInterp _ _ _ =>
      intro m ξ' ρ w P' interp' f _ r t h
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
      have h' := (PiPack.mem_real Q).mp h
      refine (PiPack.mem_real Q').mpr ⟨h'.1, fun {k ξ'' ρ'} w' {a} ha {r'} ρr u hu => ?_⟩
      have ha' : (Q.dom (w.comp' w')).Val a := dom w' ▸ ha
      rw [cod w' ha ha', rename_comp]
      exact h'.2 (w.comp' w') ha' ρr u (dom w' ▸ hu)
  | @sigma n ξ A dom cod red Q domInterp codInterp codRespect domIH codIH =>
      intro m ξ' ρ w P' interp' p valid r t h
      obtain ⟨Q', rfl, interprets'⟩ := interp'.sigma_inv vlaws (red.rename ρ)
      obtain ⟨hp, _, hc⟩ := valid
      have domI' : SInterp M.value l below ξ' (Presentation.rename ρ
          (Presentation.rename idRen dom)) (Q'.dom (Morph.id ξ')) := by
        have h' := interprets'.dom (Morph.id ξ')
        rw [rename_id] at h'
        rwa [rename_id]
      have domR : RealsRenamed (Q.dom (Morph.id ξ)) ρ (Q'.dom (Morph.id ξ')) :=
        fun {_} valid' => domIH (Morph.id ξ) w domI' valid'
      have h' := (PiPack.mem_pairReal Q).mp h
      refine (PiPack.mem_pairReal Q').mpr ⟨h'.1, fun hp' => ⟨domR hp (h'.2 hp).1, ?_⟩⟩
      have codI' : SInterp M.value l below ξ' (Presentation.rename ρ
          (inst0 (.fst p) (Presentation.rename (liftRen idRen) cod)))
          (Q'.cod (Morph.id ξ') hp') := by
        have h'' := interprets'.cod (Morph.id ξ') hp'
        rw [liftRen_id, rename_id] at h''
        rw [liftRen_id, rename_id, rename_inst0]
        exact h''
      exact codIH (Morph.id ξ) hp w codI' hc (h'.2 hp).2
  | ident red R tyInterp _ _ _ =>
      intro m ξ' ρ w P' interp' a _ r t h
      obtain ⟨R', rfl, tyInterp', -, -⟩ := interp'.id_inv vlaws (red.rename ρ)
      obtain ⟨R'', tyInterp'', renamed⟩ := tyInterp.rename vlaws w
      obtain rfl := tyInterp'.deterministic vlaws tyInterp''
      exact ⟨h.1, fun u steps => renamed.rel (h.2 u steps)⟩
  | ind red role field fieldInterp fieldIH =>
      intro m ξ' ρ w P' interp' a valid r t h
      obtain ⟨field', rfl, fieldInterp'⟩ := interp'.ind_inv vlaws (red.rename ρ) role
      refine indPack_real_rename laws role (fun {F} hF => ?_) valid h
      have h' := fieldInterp' hF
      rw [← rename_liftClosed ρ F] at h'
      exact fun {_} valid' => fieldIH hF w h' valid'
  | prop red =>
      intro m ξ' ρ w P' interp' a _ r t h
      rw [interp'.deterministic vlaws (.prop (red.rename ρ))]
      exact h
  | holds red truth =>
      intro m ξ' ρ w P' interp' a _ r t h
      rw [interp'.deterministic vlaws (.holds (red.rename ρ) (truth.rename w))]
      exact h
  | rigid red role notProp notHolds =>
      intro m ξ' ρ w P' interp' a _ r t h
      have red' := red.rename ρ
      rw [rename_appSpine] at red'
      rw [interp'.deterministic vlaws (.rigid red' role notProp notHolds)]
      exact h
  | daimon red daimonic =>
      intro m ξ' ρ w P' interp' a _ r t h
      rw [interp'.deterministic vlaws (.daimon (red.rename ρ) (daimonic.rename ρ))]
      exact h

end Rename

/-- **Along a world morphism, a denoted type has a renamed denotation that relates
the renamed values and in which a renamed valid value has every realizer of the
value.** -/
theorem DenS.rename_real (laws : M.Laws) {n : Nat} {ξ : World M.reading n} {A : Tm Head n}
    {P : Pack M.value n} (den : DenS M.value ξ A P) {m : Nat} {ξ' : World M.reading m}
    {ρ : Ren n m} (w : Morph ξ ξ' ρ) :
    ∃ P', DenS M.value ξ' (Presentation.rename ρ A) P' ∧ P.Renamed ρ P' ∧ RealsRenamed P ρ P' := by
  obtain ⟨l, interp⟩ := den
  obtain ⟨P', interp', renamed⟩ := InterpAt.rename laws.value interp w
  exact ⟨P', ⟨l, interp'⟩, renamed, SInterp.real_rename laws interp w interp'⟩

end ModelS
end Impredicative
end TypedEquality
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
