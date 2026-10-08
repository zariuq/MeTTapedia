import Mettapedia.TypeTheory.ContextualTypeOperations
import Mettapedia.TypeTheory.CwfYoneda
import Mettapedia.GSLT.Core.ContextualTypeReindexingCoherence

/-!
# Dependent sums and context comprehension

Local sum operations, their beta/eta equations and strict substitution laws
determine the comparison between a two-variable context and a context with
one dependent-pair variable. The full-motive eliminator is obtained by
substitution along that comparison, rather than supplied as a model field.

This construction concerns the supplied strict representatives. It neither
postulates an arbitrary-model interpreter nor a classifying property.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualSumComprehension

open CategoryTheory
open Mettapedia.GSLT.Core.ContextualLadder
open ContextualProductComparison (selfExtend)
open ContextualTypeOperations

universe u v w w'

variable {C : Cwf.{u, v, w, w'}}

/-- Surjective pairing is a separate local sum equation. -/
def SigmaEta (sums : SigmaOperations C) : Prop :=
  ∀ {Γ : C.Ctx} {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (p : C.Tm Γ (sums.sigma A B)), sums.pair (sums.fst p) (sums.snd p) = p

/-- Local sum laws; no context comparison or elimination theorem is a field. -/
structure StableSums (C : Cwf.{u, v, w, w'}) where
  operations : SigmaOperations C
  beta : SigmaBeta operations
  eta : SigmaEta operations
  substitution : StrictSigmaSubstitution operations

/-- The local beta/eta equations classify the two term components. -/
def termEquiv (sums : StableSums C) {Γ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    C.Tm Γ (sums.operations.sigma A B) ≃
      Σ a : C.Tm Γ A, C.Tm Γ (C.tySub B (selfExtend C a)) where
  toFun p := ⟨sums.operations.fst p, sums.operations.snd p⟩
  invFun p := sums.operations.pair p.1 p.2
  left_inv := sums.eta
  right_inv p := Sigma.ext (sums.beta.1 p.1 p.2) (sums.beta.2 p.1 p.2)

/-- Extending a substituted type and supplying its variable has precisely
the original context-pairing substitution. -/
theorem lift_selfExtend {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ) (A : C.Ty Γ)
    (a : C.Tm Δ (C.tySub A σ)) :
    C.compS (TypeOver.extensionSubstitution σ A) (selfExtend C a) =
      C.pair σ A a := by
  apply TypeOver.substitution_ext
  · rw [← C.comp_assoc, TypeOver.wk_extensionSubstitution, C.comp_assoc,
      wk_selfExtend, C.comp_id, C.wk_pair]
  · have types :
        C.tySub (C.tySub A (C.wk A)) (TypeOver.extensionSubstitution σ A) =
          C.tySub (C.tySub A σ) (C.wk (C.tySub A σ)) := by
      rw [← C.tySub_comp, TypeOver.wk_extensionSubstitution, C.tySub_comp]
    exact (TypeOver.tmSub_comp_heq (C.vz A) _ _).trans
      ((TypeOver.tmSub_heq types (TypeOver.vz_extensionSubstitution σ A) _).trans
        ((vz_selfExtend a).trans
          ((cast_heq _ _).symm.trans (heq_of_eq (C.vz_pair σ A a)).symm)))

/-- Components of a dependent pair above an arbitrary base substitution. -/
def Components {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ)
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :=
  Σ a : C.Tm Δ (C.tySub A σ), C.Tm Δ (C.tySub B (C.pair σ A a))

/-- The second-component transport is determined by comprehension. -/
def secondEquiv {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ)
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A))
    (a : C.Tm Δ (C.tySub A σ)) :
    C.Tm Δ (C.tySub (C.tySub B (TypeOver.extensionSubstitution σ A))
      (selfExtend C a)) ≃ C.Tm Δ (C.tySub B (C.pair σ A a)) :=
  Equiv.cast (by rw [← C.tySub_comp, lift_selfExtend])

/-- A substituted sum term is equivalent to its actual dependent components.
The only type casts are the supplied formation law and the earned lift square. -/
def componentsEquiv (sums : StableSums C) {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ)
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    C.Tm Δ (C.tySub (sums.operations.sigma A B) σ) ≃ Components σ A B :=
  (Equiv.cast (congrArg (C.Tm Δ) (sums.substitution.1 σ A B))).trans
    ((termEquiv sums (C.tySub A σ)
      (C.tySub B (TypeOver.extensionSubstitution σ A))).trans
        (Equiv.sigmaCongrRight (secondEquiv σ A B)))

/-- Pairing at a supplied base substitution, rather than only at identity. -/
def pairAt (sums : StableSums C) {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ)
    {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (a : C.Tm Δ (C.tySub A σ)) (b : C.Tm Δ (C.tySub B (C.pair σ A a))) :
    C.Tm Δ (C.tySub (sums.operations.sigma A B) σ) :=
  (componentsEquiv sums σ A B).symm ⟨a, b⟩

theorem pairAt_components (sums : StableSums C) {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ)
    {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (a : C.Tm Δ (C.tySub A σ)) (b : C.Tm Δ (C.tySub B (C.pair σ A a))) :
    componentsEquiv sums σ A B (pairAt sums σ a b) = ⟨a, b⟩ :=
  (componentsEquiv sums σ A B).apply_symm_apply ⟨a, b⟩

theorem components_pairAt (sums : StableSums C) {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ)
    {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (p : C.Tm Δ (C.tySub (sums.operations.sigma A B) σ)) :
    pairAt sums σ (componentsEquiv sums σ A B p).1
      (componentsEquiv sums σ A B p).2 = p :=
  (componentsEquiv sums σ A B).symm_apply_apply p

/-- The identity comparison is actual transport of a display context. -/
theorem compose_isoOfValEq_heq {Γ Δ : C.Ctx} {A B : C.Ty Γ}
    (same : A = B) (σ : C.Sub (C.ext Γ B) Δ) :
    HEq (C.compS σ (TypeOver.isoOfValEq
      (C := C) (A := ⟨A⟩) (B := ⟨B⟩) same).hom.substitution) σ := by
  cases same
  exact heq_of_eq (C.comp_id σ)

/-- The one-step and two-step lifts agree after the CwF's actual
type-composition transport. -/
theorem lift_comp_heq {Γ Δ Θ : C.Ctx} (σ : C.Sub Δ Γ) (τ : C.Sub Θ Δ)
    (A : C.Ty Γ) :
    HEq (TypeOver.extensionSubstitution (C.compS σ τ) A)
      (C.compS (TypeOver.extensionSubstitution σ A)
        (TypeOver.extensionSubstitution τ (C.tySub A σ))) :=
  (heq_of_eq (TypeOver.compositionObjectIso_hom_lift σ τ
    (⟨A⟩ : TypeOver C Γ)).symm).trans
      (compose_isoOfValEq_heq (C.tySub_comp A σ τ) _)

/-- Reindexing respects transport of its source context and actual arrow. -/
theorem tySub_source_heq {Γ Δ Θ : C.Ctx} (same : Δ = Θ)
    {σ : C.Sub Δ Γ} {τ : C.Sub Θ Γ} (arrows : HEq σ τ) (A : C.Ty Γ) :
    HEq (C.tySub A σ) (C.tySub A τ) := by
  cases same
  cases eq_of_heq arrows
  rfl

theorem codomain_comp_heq {Γ Δ Θ : C.Ctx}
    (σ : C.Sub Δ Γ) (τ : C.Sub Θ Δ)
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    HEq (C.tySub B (TypeOver.extensionSubstitution (C.compS σ τ) A))
      (C.tySub (C.tySub B (TypeOver.extensionSubstitution σ A))
        (TypeOver.extensionSubstitution τ (C.tySub A σ))) :=
  (tySub_source_heq (congrArg (C.ext Θ) (C.tySub_comp A σ τ))
    (lift_comp_heq σ τ A) B).trans (heq_of_eq (C.tySub_comp B _ _))

/-- The supplied sum's dependent arguments, not just its formed type,
control the meaning of its projections. -/
theorem fst_heq (operations : SigmaOperations C) {Γ : C.Ctx}
    {A A' : C.Ty Γ} {B : C.Ty (C.ext Γ A)} {B' : C.Ty (C.ext Γ A')}
    (domains : A = A') (codomains : HEq B B')
    {p : C.Tm Γ (operations.sigma A B)}
    {p' : C.Tm Γ (operations.sigma A' B')} (values : HEq p p') :
    HEq (operations.fst p) (operations.fst p') := by
  cases domains
  cases eq_of_heq codomains
  cases eq_of_heq values
  rfl

theorem snd_heq (operations : SigmaOperations C) {Γ : C.Ctx}
    {A A' : C.Ty Γ} {B : C.Ty (C.ext Γ A)} {B' : C.Ty (C.ext Γ A')}
    (domains : A = A') (codomains : HEq B B')
    {p : C.Tm Γ (operations.sigma A B)}
    {p' : C.Tm Γ (operations.sigma A' B')} (values : HEq p p') :
    HEq (operations.snd p) (operations.snd p') := by
  cases domains
  cases eq_of_heq codomains
  cases eq_of_heq values
  rfl

def normalize (sums : StableSums C) {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ)
    {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (p : C.Tm Δ (C.tySub (sums.operations.sigma A B) σ)) :
    C.Tm Δ (sums.operations.sigma (C.tySub A σ)
      (C.tySub B (TypeOver.extensionSubstitution σ A))) :=
  cast (congrArg (C.Tm Δ) (sums.substitution.1 σ A B)) p

theorem normalize_heq (sums : StableSums C) {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ)
    {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (p : C.Tm Δ (C.tySub (sums.operations.sigma A B) σ)) :
    HEq (normalize sums σ p) p := cast_heq _ _

def reindexValue {Γ Δ Θ : C.Ctx} (σ : C.Sub Δ Γ) (τ : C.Sub Θ Δ)
    {S : C.Ty Γ} (p : C.Tm Δ (C.tySub S σ)) :
    C.Tm Θ (C.tySub S (C.compS σ τ)) :=
  cast (congrArg (C.Tm Θ) (C.tySub_comp S σ τ).symm) (C.tmSub p τ)

theorem reindexValue_heq {Γ Δ Θ : C.Ctx} (σ : C.Sub Δ Γ) (τ : C.Sub Θ Δ)
    {S : C.Ty Γ} (p : C.Tm Δ (C.tySub S σ)) :
    HEq (reindexValue σ τ p) (C.tmSub p τ) := cast_heq _ _

theorem normalize_comp_heq (sums : StableSums C) {Γ Δ Θ : C.Ctx}
    (σ : C.Sub Δ Γ) (τ : C.Sub Θ Δ)
    {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (p : C.Tm Δ (C.tySub (sums.operations.sigma A B) σ)) :
    HEq (normalize sums (C.compS σ τ) (reindexValue σ τ p))
      (normalize sums τ (C.tmSub (normalize sums σ p) τ)) :=
  (normalize_heq sums _ _).trans ((cast_heq _ _).trans
    ((TypeOver.tmSub_heq (sums.substitution.1 σ A B)
      (normalize_heq sums σ p).symm τ).trans
        (normalize_heq sums τ _).symm))

/-- Extracting either component commutes with actual term substitution.
The changing codomain is compared using the earned composition of lifts. -/
theorem components_substitution_heq (sums : StableSums C) {Γ Δ Θ : C.Ctx}
    (σ : C.Sub Δ Γ) (τ : C.Sub Θ Δ)
    {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    (p : C.Tm Δ (C.tySub (sums.operations.sigma A B) σ)) :
    HEq (componentsEquiv sums (C.compS σ τ) A B (reindexValue σ τ p)).1
        (C.tmSub (componentsEquiv sums σ A B p).1 τ) ∧
      HEq (componentsEquiv sums (C.compS σ τ) A B (reindexValue σ τ p)).2
        (C.tmSub (componentsEquiv sums σ A B p).2 τ) := by
  have stable := sums.substitution.2.2 τ (normalize sums σ p)
    (normalize sums τ (C.tmSub (normalize sums σ p) τ))
    (normalize_heq sums τ _).symm
  refine ⟨?_, ?_⟩
  · exact (fst_heq sums.operations (C.tySub_comp A σ τ)
      (codomain_comp_heq σ τ A B) (normalize_comp_heq sums σ τ p)).trans
        stable.1.symm
  · have first := (snd_heq sums.operations (C.tySub_comp A σ τ)
      (codomain_comp_heq σ τ A B) (normalize_comp_heq sums σ τ p)).trans
        stable.2.symm
    change HEq ((secondEquiv (C.compS σ τ) A B _)
      (sums.operations.snd _)) (C.tmSub ((secondEquiv σ A B _)
        (sums.operations.snd _)) τ)
    have secondTypes :
        C.tySub (C.tySub B (TypeOver.extensionSubstitution σ A))
          (selfExtend C (sums.operations.fst (normalize sums σ p))) =
        C.tySub B (C.pair σ A (sums.operations.fst (normalize sums σ p))) := by
      rw [← C.tySub_comp, lift_selfExtend]
    exact (cast_heq _ _).trans (first.trans
      (TypeOver.tmSub_heq secondTypes (cast_heq _ _).symm τ))

/-- Reading the actual newest variable, with its base-composition cast. -/
def read {Γ Δ : C.Ctx} (A : C.Ty Γ) (δ : C.Sub Δ (C.ext Γ A)) :
    C.Tm Δ (C.tySub A (C.compS (C.wk A) δ)) :=
  cast (congrArg (C.Tm Δ) (C.tySub_comp A (C.wk A) δ).symm)
    (C.tmSub (C.vz A) δ)

theorem read_heq {Γ Δ : C.Ctx} (A : C.Ty Γ) (δ : C.Sub Δ (C.ext Γ A)) :
    HEq (read A δ) (C.tmSub (C.vz A) δ) := cast_heq _ _

theorem read_pair {Γ Δ : C.Ctx} (A : C.Ty Γ)
    (σ : C.Sub Δ Γ) (a : C.Tm Δ (C.tySub A σ)) :
    HEq (read A (C.pair σ A a)) a :=
  (read_heq A _).trans ((heq_of_eq (C.vz_pair σ A a)).trans (cast_heq _ _))

theorem pair_read {Γ Δ : C.Ctx} (A : C.Ty Γ) (δ : C.Sub Δ (C.ext Γ A)) :
    C.pair (C.compS (C.wk A) δ) A (read A δ) = δ := C.pair_eta A δ

theorem read_comp_heq {Γ Δ Θ : C.Ctx} (A : C.Ty Γ)
    (δ : C.Sub Δ (C.ext Γ A)) (τ : C.Sub Θ Δ) :
    HEq (read A (C.compS δ τ)) (C.tmSub (read A δ) τ) :=
  (read_heq A _).trans ((TypeOver.tmSub_comp_heq (C.vz A) δ τ).trans
    (TypeOver.tmSub_heq (C.tySub_comp A (C.wk A) δ).symm
      (read_heq A δ).symm τ))

/-- Context comprehension classifies an arbitrary actual arrow by its base
projection and its supplied variable reading. -/
def arrowEquiv {Γ Δ : C.Ctx} (A : C.Ty Γ) :
    C.Sub Δ (C.ext Γ A) ≃
      Σ σ : C.Sub Δ Γ, C.Tm Δ (C.tySub A σ) where
  toFun δ := ⟨C.compS (C.wk A) δ, read A δ⟩
  invFun p := C.pair p.1 A p.2
  left_inv := pair_read A
  right_inv p := Sigma.ext (C.wk_pair p.1 A p.2) (read_pair A p.1 p.2)

abbrev tupleContext {Γ : C.Ctx} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) : C.Ctx :=
  C.ext (C.ext Γ A) B

abbrev sumContext (sums : StableSums C) {Γ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) : C.Ctx :=
  C.ext Γ (sums.operations.sigma A B)

/-- The two-variable context retains both components over their original base. -/
def tupleArrowEquiv {Γ Δ : C.Ctx} (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    C.Sub Δ (tupleContext A B) ≃ Σ σ : C.Sub Δ Γ, Components σ A B :=
  (arrowEquiv B).trans
    ((Equiv.sigmaCongr (arrowEquiv A) (fun δ =>
      Equiv.cast (congrArg (fun arrow => C.Tm Δ (C.tySub B arrow))
        (pair_read A δ).symm))).trans
          (Equiv.sigmaAssoc (fun σ a => C.Tm Δ (C.tySub B (C.pair σ A a)))))

/-- The single sum variable retains the same dependent component data. -/
def sumArrowEquiv (sums : StableSums C) {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    C.Sub Δ (sumContext sums A B) ≃ Σ σ : C.Sub Δ Γ, Components σ A B :=
  (arrowEquiv (sums.operations.sigma A B)).trans
    (Equiv.sigmaCongrRight (fun σ => componentsEquiv sums σ A B))

def unpackArrow (sums : StableSums C) {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A))
    (δ : C.Sub Δ (sumContext sums A B)) : C.Sub Δ (tupleContext A B) :=
  (tupleArrowEquiv A B).symm (sumArrowEquiv sums A B δ)

def packArrow (sums : StableSums C) {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A))
    (δ : C.Sub Δ (tupleContext A B)) : C.Sub Δ (sumContext sums A B) :=
  (sumArrowEquiv sums A B).symm (tupleArrowEquiv A B δ)

theorem unpack_packArrow (sums : StableSums C) {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (δ : C.Sub Δ (tupleContext A B)) :
    unpackArrow sums A B (packArrow sums A B δ) = δ := by
  unfold unpackArrow packArrow
  rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]

theorem pack_unpackArrow (sums : StableSums C) {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (δ : C.Sub Δ (sumContext sums A B)) :
    packArrow sums A B (unpackArrow sums A B δ) = δ := by
  unfold unpackArrow packArrow
  rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]

theorem unpackArrow_data (sums : StableSums C) {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (δ : C.Sub Δ (sumContext sums A B)) :
    tupleArrowEquiv A B (unpackArrow sums A B δ) = sumArrowEquiv sums A B δ :=
  Equiv.apply_symm_apply _ _

theorem unpackArrow_base (sums : StableSums C) {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (δ : C.Sub Δ (sumContext sums A B)) :
    C.compS (C.wk A) (C.compS (C.wk B) (unpackArrow sums A B δ)) =
      C.compS (C.wk (sums.operations.sigma A B)) δ :=
  congrArg Sigma.fst (unpackArrow_data sums A B δ)

theorem Components.first_heq {Γ Δ : C.Ctx} {σ τ : C.Sub Δ Γ}
    {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)} (bases : σ = τ)
    {left : Components σ A B} {right : Components τ A B} (data : HEq left right) :
    HEq left.1 right.1 := by
  cases bases
  cases eq_of_heq data
  rfl

theorem Components.second_heq {Γ Δ : C.Ctx} {σ τ : C.Sub Δ Γ}
    {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)} (bases : σ = τ)
    {left : Components σ A B} {right : Components τ A B} (data : HEq left right) :
    HEq left.2 right.2 := by
  cases bases
  cases eq_of_heq data
  rfl

theorem sigma_second_heq {α : Type v} {β : α → Type w'}
    {left right : Sigma β} (same : left = right) : HEq left.2 right.2 := by
  cases same
  rfl

theorem unpackArrow_first (sums : StableSums C) {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (δ : C.Sub Δ (sumContext sums A B)) :
    HEq (read A (C.compS (C.wk B) (unpackArrow sums A B δ)))
      (sumArrowEquiv sums A B δ).2.1 := by
  have data := unpackArrow_data sums A B δ
  exact Components.first_heq (congrArg Sigma.fst data) (sigma_second_heq data)

theorem unpackArrow_second (sums : StableSums C) {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (δ : C.Sub Δ (sumContext sums A B)) :
    HEq (read B (unpackArrow sums A B δ)) (sumArrowEquiv sums A B δ).2.2 := by
  have data := unpackArrow_data sums A B δ
  have reading : HEq (tupleArrowEquiv A B (unpackArrow sums A B δ)).2.2
      (read B (unpackArrow sums A B δ)) := cast_heq _ _
  exact reading.symm.trans
    (Components.second_heq (congrArg Sigma.fst data) (sigma_second_heq data))

theorem unpackArrow_first_raw (sums : StableSums C) {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (δ : C.Sub Δ (sumContext sums A B)) :
    HEq (C.tmSub (C.vz A) (C.compS (C.wk B) (unpackArrow sums A B δ)))
      (sumArrowEquiv sums A B δ).2.1 :=
  (read_heq A _).symm.trans (unpackArrow_first sums A B δ)

theorem unpackArrow_mid (sums : StableSums C) {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (δ : C.Sub Δ (sumContext sums A B)) :
    C.compS (C.wk B) (unpackArrow sums A B δ) =
      C.pair (C.compS (C.wk (sums.operations.sigma A B)) δ) A
        (sumArrowEquiv sums A B δ).2.1 := by
  apply TypeOver.substitution_ext
  · exact (unpackArrow_base sums A B δ).trans (C.wk_pair _ A _).symm
  · exact (unpackArrow_first_raw sums A B δ).trans
      ((cast_heq _ _).symm.trans (heq_of_eq (C.vz_pair _ _ _)).symm)

theorem unpackArrow_second_raw (sums : StableSums C) {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (δ : C.Sub Δ (sumContext sums A B)) :
    HEq (C.tmSub (C.vz B) (unpackArrow sums A B δ))
      (sumArrowEquiv sums A B δ).2.2 :=
  (read_heq B _).symm.trans (unpackArrow_second sums A B δ)

theorem components_first_congr (sums : StableSums C) {Γ Δ : C.Ctx}
    {σ τ : C.Sub Δ Γ} (bases : σ = τ)
    {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    {p : C.Tm Δ (C.tySub (sums.operations.sigma A B) σ)}
    {q : C.Tm Δ (C.tySub (sums.operations.sigma A B) τ)} (values : HEq p q) :
    HEq (componentsEquiv sums σ A B p).1 (componentsEquiv sums τ A B q).1 := by
  cases bases
  cases eq_of_heq values
  rfl

theorem components_second_congr (sums : StableSums C) {Γ Δ : C.Ctx}
    {σ τ : C.Sub Δ Γ} (bases : σ = τ)
    {A : C.Ty Γ} {B : C.Ty (C.ext Γ A)}
    {p : C.Tm Δ (C.tySub (sums.operations.sigma A B) σ)}
    {q : C.Tm Δ (C.tySub (sums.operations.sigma A B) τ)} (values : HEq p q) :
    HEq (componentsEquiv sums σ A B p).2 (componentsEquiv sums τ A B q).2 := by
  cases bases
  cases eq_of_heq values
  rfl

theorem sumArrow_components_substitution (sums : StableSums C) {Γ Δ Θ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A))
    (δ : C.Sub Δ (sumContext sums A B)) (τ : C.Sub Θ Δ) :
    HEq (sumArrowEquiv sums A B (C.compS δ τ)).2.1
        (C.tmSub (sumArrowEquiv sums A B δ).2.1 τ) ∧
      HEq (sumArrowEquiv sums A B (C.compS δ τ)).2.2
        (C.tmSub (sumArrowEquiv sums A B δ).2.2 τ) := by
  have bases := (C.comp_assoc (C.wk (sums.operations.sigma A B)) δ τ).symm
  have values := (read_comp_heq (sums.operations.sigma A B) δ τ).trans
    (reindexValue_heq (C.compS (C.wk (sums.operations.sigma A B)) δ) τ
      (read (sums.operations.sigma A B) δ)).symm
  have components := components_substitution_heq sums
    (C.compS (C.wk (sums.operations.sigma A B)) δ) τ
      (read (sums.operations.sigma A B) δ)
  exact ⟨(components_first_congr sums bases values).trans components.1,
    (components_second_congr sums bases values).trans components.2⟩

/-- Unpacking commutes with all actual source-context substitutions. -/
theorem unpackArrow_comp (sums : StableSums C) {Γ Δ Θ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A))
    (δ : C.Sub Δ (sumContext sums A B)) (τ : C.Sub Θ Δ) :
    unpackArrow sums A B (C.compS δ τ) =
      C.compS (unpackArrow sums A B δ) τ := by
  have stable := sumArrow_components_substitution sums A B δ τ
  apply TypeOver.substitution_ext
  · apply TypeOver.substitution_ext
    · exact (unpackArrow_base sums A B (C.compS δ τ)).trans
        ((C.comp_assoc (C.wk (sums.operations.sigma A B)) δ τ).symm.trans
          ((congrArg (fun base => C.compS base τ)
            (unpackArrow_base sums A B δ).symm).trans
              ((C.comp_assoc (C.wk A)
                (C.compS (C.wk B) (unpackArrow sums A B δ)) τ).trans
                  (congrArg (C.compS (C.wk A))
                    (C.comp_assoc (C.wk B) (unpackArrow sums A B δ) τ)))))
    · have types :
          C.tySub (C.tySub A (C.wk A))
            (C.compS (C.wk B) (unpackArrow sums A B δ)) =
          C.tySub A (C.compS (C.wk (sums.operations.sigma A B)) δ) := by
        rw [← C.tySub_comp, unpackArrow_base]
      have right := (TypeOver.tmSub_comp_heq (C.vz A)
        (C.compS (C.wk B) (unpackArrow sums A B δ)) τ).trans
          (TypeOver.tmSub_heq types (unpackArrow_first_raw sums A B δ) τ)
      rw [C.comp_assoc] at right
      exact (unpackArrow_first_raw sums A B (C.compS δ τ)).trans
        (stable.1.trans right.symm)
  · have types :
        C.tySub (C.tySub B (C.wk B)) (unpackArrow sums A B δ) =
          C.tySub B (C.pair (C.compS (C.wk (sums.operations.sigma A B)) δ) A
            (sumArrowEquiv sums A B δ).2.1) := by
      rw [← C.tySub_comp, unpackArrow_mid]
    exact (unpackArrow_second_raw sums A B (C.compS δ τ)).trans
      (stable.2.trans ((TypeOver.tmSub_comp_heq (C.vz B) _ _).trans
        (TypeOver.tmSub_heq types (unpackArrow_second_raw sums A B δ) τ)).symm)

theorem unpackArrow_injective (sums : StableSums C) {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    Function.Injective (unpackArrow sums (Δ := Δ) A B) :=
  Function.LeftInverse.injective (pack_unpackArrow sums A B)

theorem packArrow_comp (sums : StableSums C) {Γ Δ Θ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A))
    (δ : C.Sub Δ (tupleContext A B)) (τ : C.Sub Θ Δ) :
    packArrow sums A B (C.compS δ τ) =
      C.compS (packArrow sums A B δ) τ := by
  apply unpackArrow_injective sums A B
  rw [unpack_packArrow, unpackArrow_comp, unpack_packArrow]

/-- The actual pairing map between the two context presentations. -/
def pack (sums : StableSums C) {Γ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    C.Sub (tupleContext A B) (sumContext sums A B) :=
  packArrow sums A B (C.idS (tupleContext A B))

/-- The actual projection map, retaining both dependent witnesses. -/
def unpack (sums : StableSums C) {Γ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    C.Sub (sumContext sums A B) (tupleContext A B) :=
  unpackArrow sums A B (C.idS (sumContext sums A B))

theorem packArrow_eq_comp (sums : StableSums C) {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (δ : C.Sub Δ (tupleContext A B)) :
    packArrow sums A B δ = C.compS (pack sums A B) δ := by
  have natural := packArrow_comp sums A B (C.idS (tupleContext A B)) δ
  rw [C.id_comp] at natural
  exact natural

theorem unpackArrow_eq_comp (sums : StableSums C) {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (δ : C.Sub Δ (sumContext sums A B)) :
    unpackArrow sums A B δ = C.compS (unpack sums A B) δ := by
  have natural := unpackArrow_comp sums A B (C.idS (sumContext sums A B)) δ
  rw [C.id_comp] at natural
  exact natural

theorem unpack_pack (sums : StableSums C) {Γ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    C.compS (unpack sums A B) (pack sums A B) = C.idS (tupleContext A B) :=
  (unpackArrow_eq_comp sums A B _).symm.trans
    (unpack_packArrow sums A B (C.idS (tupleContext A B)))

theorem pack_unpack (sums : StableSums C) {Γ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    C.compS (pack sums A B) (unpack sums A B) = C.idS (sumContext sums A B) :=
  (packArrow_eq_comp sums A B _).symm.trans
    (pack_unpackArrow sums A B (C.idS (sumContext sums A B)))

/-- The context comparison is an isomorphism in the actual CwF base category. -/
def contextIso (sums : StableSums C) {Γ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    CwfYoneda.context C (tupleContext A B) ≅ CwfYoneda.context C (sumContext sums A B) where
  hom := pack sums A B
  inv := unpack sums A B
  hom_inv_id := unpack_pack sums A B
  inv_hom_id := pack_unpack sums A B

theorem packArrow_base (sums : StableSums C) {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (δ : C.Sub Δ (tupleContext A B)) :
    C.compS (C.wk (sums.operations.sigma A B)) (packArrow sums A B δ) =
      C.compS (C.wk A) (C.compS (C.wk B) δ) :=
  congrArg Sigma.fst ((sumArrowEquiv sums A B).apply_symm_apply
    (tupleArrowEquiv A B δ))

/-- The comparison preserves the original base context. -/
theorem pack_over (sums : StableSums C) {Γ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    C.compS (C.wk (sums.operations.sigma A B)) (pack sums A B) =
      C.compS (C.wk A) (C.wk B) := by
  have over := packArrow_base sums A B (C.idS (tupleContext A B))
  rw [C.comp_id] at over
  exact over

theorem unpack_over (sums : StableSums C) {Γ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    C.compS (C.compS (C.wk A) (C.wk B)) (unpack sums A B) =
      C.wk (sums.operations.sigma A B) := by
  have over := unpackArrow_base sums A B (C.idS (sumContext sums A B))
  rw [C.comp_id] at over
  exact (C.comp_assoc _ _ _).trans over

/-- The body motive becomes the complete sum-context motive after unpacking. -/
theorem motive_roundtrip (sums : StableSums C) {Γ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (M : C.Ty (sumContext sums A B)) :
    C.tySub (C.tySub M (pack sums A B)) (unpack sums A B) = M := by
  rw [← C.tySub_comp, pack_unpack, C.tySub_id]

/-- Full-motive sum elimination derived from the actual context comparison. -/
def eliminate (sums : StableSums C) {Γ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (M : C.Ty (sumContext sums A B))
    (body : C.Tm (tupleContext A B) (C.tySub M (pack sums A B))) :
    C.Tm (sumContext sums A B) M :=
  cast (congrArg (C.Tm (sumContext sums A B)) (motive_roundtrip sums A B M))
    (C.tmSub body (unpack sums A B))

theorem eliminate_heq (sums : StableSums C) {Γ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (M : C.Ty (sumContext sums A B))
    (body : C.Tm (tupleContext A B) (C.tySub M (pack sums A B))) :
    HEq (eliminate sums A B M body) (C.tmSub body (unpack sums A B)) := cast_heq _ _

/-- Pair elimination computes the exact supplied body, including both witnesses. -/
theorem eliminate_beta (sums : StableSums C) {Γ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (M : C.Ty (sumContext sums A B))
    (body : C.Tm (tupleContext A B) (C.tySub M (pack sums A B))) :
    C.tmSub (eliminate sums A B M body) (pack sums A B) = body := by
  apply eq_of_heq
  have transported := TypeOver.tmSub_heq (motive_roundtrip sums A B M).symm
    (eliminate_heq sums A B M body) (pack sums A B)
  have compose := (TypeOver.tmSub_comp_heq body (unpack sums A B) (pack sums A B)).symm
  rw [unpack_pack] at compose
  exact transported.trans (compose.trans
    ((heq_of_eq (C.tmSub_id body)).trans (cast_heq _ _)))

/-- Eliminating the restriction of a section recovers that section. -/
theorem eliminate_eta (sums : StableSums C) {Γ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (M : C.Ty (sumContext sums A B))
    (term : C.Tm (sumContext sums A B) M) :
    eliminate sums A B M (C.tmSub term (pack sums A B)) = term := by
  apply eq_of_heq
  have compose := (TypeOver.tmSub_comp_heq term (pack sums A B) (unpack sums A B)).symm
  rw [pack_unpack] at compose
  exact (eliminate_heq sums A B M _).trans
    (compose.trans ((heq_of_eq (C.tmSub_id term)).trans (cast_heq _ _)))

def sectionEquiv (sums : StableSums C) {Γ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (M : C.Ty (sumContext sums A B)) :
    C.Tm (tupleContext A B) (C.tySub M (pack sums A B)) ≃ C.Tm (sumContext sums A B) M where
  toFun := eliminate sums A B M
  invFun term := C.tmSub term (pack sums A B)
  left_inv := eliminate_beta sums A B M
  right_inv := eliminate_eta sums A B M

/-- The actual canonical lift of the formed sum along a base substitution.
The supplied strict formation equality fixes its source presentation. -/
def sumReindex (sums : StableSums C) {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ)
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    C.Sub (sumContext sums (C.tySub A σ)
      (C.tySub B (TypeOver.extensionSubstitution σ A))) (sumContext sums A B) :=
  C.compS (TypeOver.extensionSubstitution σ (sums.operations.sigma A B))
    (TypeOver.isoOfValEq (C := C)
      (A := ⟨sums.operations.sigma (C.tySub A σ)
        (C.tySub B (TypeOver.extensionSubstitution σ A))⟩)
      (B := ⟨C.tySub (sums.operations.sigma A B) σ⟩)
      (sums.substitution.1 σ A B).symm).hom.substitution

/-- Both actual context-extension lifts, without using the sum comparison. -/
def tupleReindex {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ)
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    C.Sub (tupleContext (C.tySub A σ)
      (C.tySub B (TypeOver.extensionSubstitution σ A))) (tupleContext A B) :=
  TypeOver.extensionSubstitution (TypeOver.extensionSubstitution σ A) B

theorem sumReindex_base (sums : StableSums C) {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ)
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    C.compS (C.wk (sums.operations.sigma A B)) (sumReindex sums σ A B) =
      C.compS σ (C.wk (sums.operations.sigma (C.tySub A σ)
        (C.tySub B (TypeOver.extensionSubstitution σ A)))) := by
  unfold sumReindex
  rw [← C.comp_assoc, TypeOver.wk_extensionSubstitution, C.comp_assoc]
  exact congrArg (C.compS σ) (TypeOver.isoOfValEq
    (C := C) (A := ⟨sums.operations.sigma (C.tySub A σ)
      (C.tySub B (TypeOver.extensionSubstitution σ A))⟩)
    (B := ⟨C.tySub (sums.operations.sigma A B) σ⟩)
    (sums.substitution.1 σ A B).symm).hom.over

theorem sumReindex_variable (sums : StableSums C) {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ)
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    HEq (C.tmSub (C.vz (sums.operations.sigma A B)) (sumReindex sums σ A B))
      (C.vz (sums.operations.sigma (C.tySub A σ)
        (C.tySub B (TypeOver.extensionSubstitution σ A)))) := by
  have types :
      C.tySub (C.tySub (sums.operations.sigma A B) (C.wk (sums.operations.sigma A B)))
        (TypeOver.extensionSubstitution σ (sums.operations.sigma A B)) =
      C.tySub (C.tySub (sums.operations.sigma A B) σ)
        (C.wk (C.tySub (sums.operations.sigma A B) σ)) := by
    rw [← C.tySub_comp, TypeOver.wk_extensionSubstitution, C.tySub_comp]
  exact (TypeOver.tmSub_comp_heq (C.vz (sums.operations.sigma A B)) _ _).trans
    ((TypeOver.tmSub_heq types (TypeOver.vz_extensionSubstitution σ
      (sums.operations.sigma A B)) _).trans
        (TypeOver.isoOfValEq_hom_reads_vz (sums.substitution.1 σ A B).symm))

/-- The original and substituted sum presentations read the same two
components along the actual canonical sum lift. -/
theorem sumReindex_components (sums : StableSums C) {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ)
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    HEq (sumArrowEquiv sums A B (sumReindex sums σ A B)).2.1
        (sumArrowEquiv sums (C.tySub A σ)
          (C.tySub B (TypeOver.extensionSubstitution σ A))
          (C.idS (sumContext sums (C.tySub A σ)
            (C.tySub B (TypeOver.extensionSubstitution σ A))))).2.1 ∧
      HEq (sumArrowEquiv sums A B (sumReindex sums σ A B)).2.2
        (sumArrowEquiv sums (C.tySub A σ)
          (C.tySub B (TypeOver.extensionSubstitution σ A))
          (C.idS (sumContext sums (C.tySub A σ)
            (C.tySub B (TypeOver.extensionSubstitution σ A))))).2.2 := by
  let newSum := sums.operations.sigma (C.tySub A σ)
    (C.tySub B (TypeOver.extensionSubstitution σ A))
  let newBase := C.compS (C.wk newSum) (C.idS (C.ext Δ newSum))
  have bases : C.compS (C.wk (sums.operations.sigma A B)) (sumReindex sums σ A B) =
      C.compS σ newBase := by
    exact (sumReindex_base sums σ A B).trans
      (congrArg (C.compS σ) (C.comp_id (C.wk newSum)).symm)
  have domains :
      C.tySub A (C.compS (C.wk (sums.operations.sigma A B)) (sumReindex sums σ A B)) =
      C.tySub (C.tySub A σ) newBase := by rw [bases, C.tySub_comp]
  have codomains :
      HEq (C.tySub B (TypeOver.extensionSubstitution
        (C.compS (C.wk (sums.operations.sigma A B)) (sumReindex sums σ A B)) A))
        (C.tySub (C.tySub B (TypeOver.extensionSubstitution σ A))
          (TypeOver.extensionSubstitution newBase (C.tySub A σ))) := by
    rw [bases]
    exact codomain_comp_heq σ newBase A B
  have value :
      HEq (normalize sums _ (read (sums.operations.sigma A B) (sumReindex sums σ A B)))
        (normalize sums newBase (read newSum (C.idS (C.ext Δ newSum)))) :=
    (normalize_heq sums _ _).trans ((read_heq _ _).trans
      ((sumReindex_variable sums σ A B).trans
        ((cast_heq _ _).symm.trans ((heq_of_eq (C.tmSub_id (C.vz newSum))).symm.trans
          ((read_heq _ _).symm.trans (normalize_heq sums _ _).symm)))))
  refine ⟨fst_heq sums.operations domains codomains value, ?_⟩
  exact (cast_heq _ _).trans ((snd_heq sums.operations domains codomains value).trans
    (cast_heq _ _).symm)

theorem tupleReindex_over {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ)
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    C.compS (C.compS (C.wk A) (C.wk B)) (tupleReindex σ A B) =
      C.compS σ (C.compS (C.wk (C.tySub A σ))
        (C.wk (C.tySub B (TypeOver.extensionSubstitution σ A)))) := by
  unfold tupleReindex
  rw [C.comp_assoc, TypeOver.wk_extensionSubstitution, ← C.comp_assoc,
    TypeOver.wk_extensionSubstitution, C.comp_assoc]

/-- The comparison square uses the two independently defined canonical
reindex maps. It is not a definition of the sum reindex map by conjugation. -/
theorem unpack_reindex (sums : StableSums C) {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ)
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    C.compS (unpack sums A B) (sumReindex sums σ A B) =
      C.compS (tupleReindex σ A B) (unpack sums (C.tySub A σ)
        (C.tySub B (TypeOver.extensionSubstitution σ A))) := by
  let A' := C.tySub A σ
  let B' := C.tySub B (TypeOver.extensionSubstitution σ A)
  let S' := sums.operations.sigma A' B'
  let U' := unpack sums A' B'
  let k := sumReindex sums σ A B
  have components := sumReindex_components sums σ A B
  rw [← unpackArrow_eq_comp]
  apply TypeOver.substitution_ext
  · apply TypeOver.substitution_ext
    · have left := (unpackArrow_base sums A B k).trans (sumReindex_base sums σ A B)
      have right :
          C.compS (C.wk A) (C.compS (C.wk B) (C.compS (tupleReindex σ A B) U')) =
            C.compS σ (C.wk S') := by
        exact (C.comp_assoc (C.wk A) (C.wk B) _).symm.trans
          ((C.comp_assoc (C.compS (C.wk A) (C.wk B)) (tupleReindex σ A B) U').symm.trans
            ((congrArg (fun base => C.compS base U') (tupleReindex_over σ A B)).trans
              ((C.comp_assoc σ (C.compS (C.wk A') (C.wk B')) U').trans
                (congrArg (C.compS σ) (unpack_over sums A' B')))))
      exact left.trans right.symm
    · have rightBase : C.compS (C.wk B) (C.compS (tupleReindex σ A B) U') =
          C.compS (TypeOver.extensionSubstitution σ A) (C.compS (C.wk B') U') := by
        unfold tupleReindex
        rw [← C.comp_assoc, TypeOver.wk_extensionSubstitution, C.comp_assoc]
      have types :
          C.tySub (C.tySub A (C.wk A)) (TypeOver.extensionSubstitution σ A) =
            C.tySub A' (C.wk A') := by
        rw [← C.tySub_comp, TypeOver.wk_extensionSubstitution, C.tySub_comp]
      have reading := (TypeOver.tmSub_comp_heq (C.vz A)
        (TypeOver.extensionSubstitution σ A) (C.compS (C.wk B') U')).trans
          ((TypeOver.tmSub_heq types (TypeOver.vz_extensionSubstitution σ A) _).trans
            (unpackArrow_first_raw sums A' B' (C.idS (sumContext sums A' B'))))
      rw [← rightBase] at reading
      exact (unpackArrow_first_raw sums A B k).trans (components.1.trans reading.symm)
  · have types :
        C.tySub (C.tySub B (C.wk B)) (tupleReindex σ A B) =
          C.tySub B' (C.wk B') := by
      unfold tupleReindex
      rw [← C.tySub_comp, TypeOver.wk_extensionSubstitution, C.tySub_comp]
    have reading := (TypeOver.tmSub_comp_heq (C.vz B) (tupleReindex σ A B) U').trans
      ((TypeOver.tmSub_heq types
        (TypeOver.vz_extensionSubstitution (TypeOver.extensionSubstitution σ A) B) U').trans
          (unpackArrow_second_raw sums A' B' (C.idS (sumContext sums A' B'))))
    exact (unpackArrow_second_raw sums A B k).trans (components.2.trans reading.symm)

/-- Packing obeys the same independently earned canonical context square. -/
theorem pack_reindex (sums : StableSums C) {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ)
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) :
    C.compS (sumReindex sums σ A B) (pack sums (C.tySub A σ)
        (C.tySub B (TypeOver.extensionSubstitution σ A))) =
      C.compS (pack sums A B) (tupleReindex σ A B) := by
  apply unpackArrow_injective sums A B
  rw [unpackArrow_comp, unpackArrow_eq_comp, unpack_reindex, C.comp_assoc,
    unpack_pack, C.comp_id, unpackArrow_comp]
  have pair := unpack_packArrow sums A B (C.idS (tupleContext A B))
  exact (C.id_comp (tupleReindex σ A B)).symm.trans
    (congrArg (fun base => C.compS base (tupleReindex σ A B)) pair.symm)

/-- Elimination at any supplied context arrow computes by the actual
unpacking arrow and retains the original dependent body. -/
theorem eliminate_atArrow (sums : StableSums C) {Γ Δ : C.Ctx}
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (M : C.Ty (sumContext sums A B))
    (body : C.Tm (tupleContext A B) (C.tySub M (pack sums A B)))
    (δ : C.Sub Δ (sumContext sums A B)) :
    HEq (C.tmSub (eliminate sums A B M body) δ)
      (C.tmSub body (unpackArrow sums A B δ)) := by
  have compose := (TypeOver.tmSub_comp_heq body (unpack sums A B) δ).symm
  rw [← unpackArrow_eq_comp] at compose
  exact (TypeOver.tmSub_heq (motive_roundtrip sums A B M).symm
    (eliminate_heq sums A B M body) δ).trans compose

theorem reindexBody_type (sums : StableSums C) {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ)
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (M : C.Ty (sumContext sums A B)) :
    C.tySub (C.tySub M (pack sums A B)) (tupleReindex σ A B) =
      C.tySub (C.tySub M (sumReindex sums σ A B))
        (pack sums (C.tySub A σ) (C.tySub B (TypeOver.extensionSubstitution σ A))) := by
  rw [← C.tySub_comp, ← pack_reindex, C.tySub_comp]

/-- A body with a motive depending on the complete pair has the reindexed
branch type by the earned canonical context square. -/
def reindexBody (sums : StableSums C) {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ)
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (M : C.Ty (sumContext sums A B))
    (body : C.Tm (tupleContext A B) (C.tySub M (pack sums A B))) :
    C.Tm (tupleContext (C.tySub A σ) (C.tySub B (TypeOver.extensionSubstitution σ A)))
      (C.tySub (C.tySub M (sumReindex sums σ A B))
        (pack sums (C.tySub A σ) (C.tySub B (TypeOver.extensionSubstitution σ A)))) :=
  cast (congrArg (C.Tm _) (reindexBody_type sums σ A B M))
    (C.tmSub body (tupleReindex σ A B))

theorem reindexBody_heq (sums : StableSums C) {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ)
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (M : C.Ty (sumContext sums A B))
    (body : C.Tm (tupleContext A B) (C.tySub M (pack sums A B))) :
    HEq (reindexBody sums σ A B M body) (C.tmSub body (tupleReindex σ A B)) := cast_heq _ _

/-- Full-motive elimination commutes with the independently defined canonical
sum and tuple context substitutions. No elimination-stability field is used. -/
theorem eliminate_substitution (sums : StableSums C) {Γ Δ : C.Ctx} (σ : C.Sub Δ Γ)
    (A : C.Ty Γ) (B : C.Ty (C.ext Γ A)) (M : C.Ty (sumContext sums A B))
    (body : C.Tm (tupleContext A B) (C.tySub M (pack sums A B))) :
    C.tmSub (eliminate sums A B M body) (sumReindex sums σ A B) =
      eliminate sums (C.tySub A σ) (C.tySub B (TypeOver.extensionSubstitution σ A))
        (C.tySub M (sumReindex sums σ A B)) (reindexBody sums σ A B M body) := by
  apply eq_of_heq
  have evaluated := eliminate_atArrow sums A B M body (sumReindex sums σ A B)
  rw [unpackArrow_eq_comp, unpack_reindex] at evaluated
  exact evaluated.trans ((TypeOver.tmSub_comp_heq body (tupleReindex σ A B) _).trans
    ((TypeOver.tmSub_heq (reindexBody_type sums σ A B M)
      (reindexBody_heq sums σ A B M body).symm _).trans
        (eliminate_heq sums (C.tySub A σ) (C.tySub B (TypeOver.extensionSubstitution σ A))
          (C.tySub M (sumReindex sums σ A B)) (reindexBody sums σ A B M body)).symm))

end Mettapedia.TypeTheory.ContextualSumComprehension
