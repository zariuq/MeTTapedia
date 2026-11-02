import Mettapedia.Logic.HOL.PredicateSigmaProjection
import Mettapedia.Logic.HOL.ConstantSubstitutionSemantics
import Mettapedia.TypeTheory.MaterialSets.PredicatePairing

/-!
# Interpreting guarded Sigma codes in a Henkin model

The general denotation law retains admitted existential witnesses and the
model's equality relation. At a base evidence carrier, admissibility and
equality are already exact in a Henkin model. Actual closed projection laws
then construct the existing material Pairing and its guarded fibre equivalence.
No full function-domain or global surjective-pairing assumption is needed.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.PredicateSigma

universe u v w
variable {Base : Type u} {Const : Ty Base → Type v}
    (model : HenkinModel.{u,v,w} Base Const) {Γ : Ctx Base} {space : Ty Base}

def emptyValues : model.Valuation [] := fun index => nomatch index

def pairValue (ops : Operations Const space) : Ty.denote model.Carrier space →
    Ty.denote model.Carrier space → Ty.denote model.Carrier space := model.denote ops.pair (emptyValues model)

def firstValue (ops : Operations Const space) : Ty.denote model.Carrier space → Ty.denote model.Carrier space :=
  model.denote ops.first (emptyValues model)

def secondValue (ops : Operations Const space) : Ty.denote model.Carrier space → Ty.denote model.Carrier space :=
  model.denote ops.second (emptyValues model)

theorem closed_denote {type : Ty Base} (term : ClosedTerm Const type) (values : model.Valuation Γ) :
    model.denote (weakenCtx Γ term) values = model.denote term (emptyValues model) :=
  (model.denote_weakenCtx Γ term values).trans (model.denote_closed_valuation_eq term _ _)

theorem pair_denote (ops : Operations Const space) (head tail : Term Const Γ space) (values : model.Valuation Γ) :
    model.denote (pair ops head tail) values = pairValue model ops (model.denote head values) (model.denote tail values) := by
  change model.denote (weakenCtx Γ ops.pair) values (model.denote head values) (model.denote tail values) = _
  rw [closed_denote]
  rfl

theorem first_denote (ops : Operations Const space) (point : Term Const Γ space) (values : model.Valuation Γ) :
    model.denote (first ops point) values = firstValue model ops (model.denote point values) := by
  change model.denote (weakenCtx Γ ops.first) values (model.denote point values) = _
  rw [closed_denote]
  rfl

theorem second_denote (ops : Operations Const space) (point : Term Const Γ space) (values : model.Valuation Γ) :
    model.denote (second ops point) values = secondValue model ops (model.denote point values) := by
  change model.denote (weakenCtx Γ ops.second) values (model.denote point values) = _
  rw [closed_denote]
  rfl

theorem membership_denote (ops : Operations Const space) (domain : Term Const Γ (space ⇒ .prop))
    (family : Term Const Γ (space ⇒ space ⇒ .prop)) (point : Term Const Γ space) (values : model.Valuation Γ) :
    (model.denote (membership ops domain family point) values).down ↔
      ∃ head, model.adm space head ∧ ∃ tail, model.adm space tail ∧
        model.Eqv space (pairValue model ops head tail) (model.denote point values) ∧
        (model.denote domain values head).down ∧ (model.denote family values head tail).down := by
  have packed (head tail : Ty.denote model.Carrier space) :
      model.denote (pair ops (.var (.vs .vz)) (.var .vz)) (model.extend (model.extend values head) tail) =
        pairValue model ops head tail := by rw [pair_denote]; rfl
  have shifted {type : Ty Base} (term : Term Const Γ type) (head tail : Ty.denote model.Carrier space) :
      model.denote (weaken (weaken term)) (model.extend (model.extend values head) tail) = model.denote term values := by
    rw [Soundness.denote_weaken, Soundness.denote_weaken]
  simp only [membership, familyAt, HenkinModel.denote, PreModel.denote, packed, shifted, PreModel.extend]

theorem sigma_apply_denote (ops : Operations Const space) (domain : Term Const Γ (space ⇒ .prop))
    (family : Term Const Γ (space ⇒ space ⇒ .prop)) (point : Ty.denote model.Carrier space) (values : model.Valuation Γ) :
    (model.denote (sigma ops domain family) values point).down ↔
      ∃ head, model.adm space head ∧ ∃ tail, model.adm space tail ∧
        model.Eqv space (pairValue model ops head tail) point ∧
        (model.denote domain values head).down ∧ (model.denote family values head tail).down := by
  change (model.denote (membership ops (weaken domain) (weaken family) (.var .vz))
    (model.extend values point)).down ↔ _
  rw [membership_denote]
  simp only [Soundness.denote_weaken, HenkinModel.denote, PreModel.denote, PreModel.extend]

theorem sigma_denote (ops : Operations Const space) (domain : Term Const Γ (space ⇒ .prop))
    (family : Term Const Γ (space ⇒ space ⇒ .prop)) (point : Term Const Γ space) (values : model.Valuation Γ) :
    (model.denote (.app (sigma ops domain family) point) values).down ↔
      ∃ head, model.adm space head ∧ ∃ tail, model.adm space tail ∧
        model.Eqv space (pairValue model ops head tail) (model.denote point values) ∧
        (model.denote domain values head).down ∧ (model.denote family values head tail).down :=
  sigma_apply_denote model ops domain family (model.denote point values) values

theorem firstLaw_denote (ops : Operations Const space) : model.models (firstLaw ops) ↔
    ∀ head, model.adm space head → ∀ tail, model.adm space tail →
      model.Eqv space (firstValue model ops (pairValue model ops head tail)) head := by
  have projected (head tail : Ty.denote model.Carrier space) :
      model.denote (first ops (pair ops (.var (.vs .vz)) (.var .vz)))
        (model.extend (model.extend (emptyValues model) head) tail) =
          firstValue model ops (pairValue model ops head tail) := by rw [first_denote, pair_denote]; rfl
  change (model.denote (firstLaw ops) (emptyValues model)).down ↔ _
  simp only [firstLaw, HenkinModel.denote, PreModel.denote, projected, PreModel.extend]

theorem secondLaw_denote (ops : Operations Const space) : model.models (secondLaw ops) ↔
    ∀ head, model.adm space head → ∀ tail, model.adm space tail →
      model.Eqv space (secondValue model ops (pairValue model ops head tail)) tail := by
  have projected (head tail : Ty.denote model.Carrier space) :
      model.denote (second ops (pair ops (.var (.vs .vz)) (.var .vz)))
        (model.extend (model.extend (emptyValues model) head) tail) =
          secondValue model ops (pairValue model ops head tail) := by rw [second_denote, pair_denote]; rfl
  change (model.denote (secondLaw ops) (emptyValues model)).down ↔ _
  simp only [secondLaw, HenkinModel.denote, PreModel.denote, projected, PreModel.extend]

def interpretedPairing {base : Base} (ops : Operations Const (.base base))
    (firstValid : model.models (firstLaw ops)) (secondValid : model.models (secondLaw ops)) :
    TypeTheory.MaterialSets.Pairing (model.Carrier base) where
  pair := pairValue model ops
  fst := firstValue model ops
  snd := secondValue model ops
  fst_pair head tail := (firstLaw_denote model ops).mp firstValid head (model.base_mem base head) tail (model.base_mem base tail)
  snd_pair head tail := (secondLaw_denote model ops).mp secondValid head (model.base_mem base head) tail (model.base_mem base tail)

theorem sigma_apply_denote_base {base : Base} (ops : Operations Const (.base base))
    (firstValid : model.models (firstLaw ops)) (secondValid : model.models (secondLaw ops))
    (domain : Term Const Γ (.base base ⇒ .prop)) (family : Term Const Γ (.base base ⇒ .base base ⇒ .prop))
    (point : model.Carrier base) (values : model.Valuation Γ) :
    (model.denote (sigma ops domain family) values point).down ↔
      (interpretedPairing model ops firstValid secondValid).SigmaGuard
        (fun head => (model.denote domain values head).down)
        (fun head tail => (model.denote family values head tail).down) point := by
  have interpreted := sigma_apply_denote model ops domain family point values
  constructor
  · intro member
    obtain ⟨head, _, tail, _, same, firstMember, secondMember⟩ := interpreted.mp member
    exact ⟨head, tail, same, firstMember, secondMember⟩
  · rintro ⟨head, tail, same, firstMember, secondMember⟩
    exact interpreted.mpr ⟨head, model.base_mem base head, tail, model.base_mem base tail, same, firstMember, secondMember⟩

theorem sigma_denote_base {base : Base} (ops : Operations Const (.base base))
    (firstValid : model.models (firstLaw ops)) (secondValid : model.models (secondLaw ops))
    (domain : Term Const Γ (.base base ⇒ .prop)) (family : Term Const Γ (.base base ⇒ .base base ⇒ .prop))
    (point : Term Const Γ (.base base)) (values : model.Valuation Γ) :
    (model.denote (.app (sigma ops domain family) point) values).down ↔
      (interpretedPairing model ops firstValid secondValid).SigmaGuard
        (fun head => (model.denote domain values head).down)
        (fun head tail => (model.denote family values head tail).down) (model.denote point values) :=
  sigma_apply_denote_base model ops firstValid secondValid domain family (model.denote point values) values

def fibreEquiv {base : Base} (ops : Operations Const (.base base))
    (firstValid : model.models (firstLaw ops)) (secondValid : model.models (secondLaw ops))
    (domain : Term Const Γ (.base base ⇒ .prop)) (family : Term Const Γ (.base base ⇒ .base base ⇒ .prop))
    (values : model.Valuation Γ) :
    {code : model.Carrier base // (model.denote (sigma ops domain family) values code).down} ≃
      TypeTheory.MaterialSets.Pairing.GuardedSigma (fun head => (model.denote domain values head).down)
        (fun head tail => (model.denote family values head tail).down) :=
  let guardEquiv :
      {code : model.Carrier base // (model.denote (sigma ops domain family) values code).down} ≃
        {code : model.Carrier base // (interpretedPairing model ops firstValid secondValid).SigmaGuard
          (fun head => (model.denote domain values head).down) (fun head tail => (model.denote family values head tail).down) code} :=
    { toFun := fun code => ⟨code.val, (sigma_apply_denote_base model ops firstValid secondValid domain family code.val values).mp code.property⟩
      invFun := fun code => ⟨code.val, (sigma_apply_denote_base model ops firstValid secondValid domain family code.val values).mpr code.property⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }
  guardEquiv.trans ((interpretedPairing model ops firstValid secondValid).sigmaEquiv _ _)

#print axioms membership_denote
#print axioms sigma_denote_base
#print axioms fibreEquiv

end Mettapedia.Logic.HOL.PredicateSigma
