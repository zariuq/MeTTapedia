import Mettapedia.Logic.HOL.IndexedConstructorEdgeGuards

/-!
# Curried programs for indexed constructor guards

The programs bind their queried values and preserve the inventory's parameter
context. Typed substitutions place the original index programs and field
predicates under these binders. Root and edge programs use the supplied
constructor operation of the same payload type.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.IndexedConstructorGuards
open FiniteConstructorEncoding
universe u v w
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}

namespace ConstructorPrograms
def beneathTwo {first second : Ty Base} : Subst Const Γ (second :: first :: Γ) :=
  fun index => .var (.vs (.vs index))

def beneathThree {first second third : Ty Base} : Subst Const Γ (third :: second :: first :: Γ) :=
  fun index => .var (.vs (.vs (.vs index)))

variable (inventory : ConstructorPrograms Const Γ)

def shapeProgram : Term Const Γ (inventory.number ⇒ payloadType inventory.fields ⇒ .prop) :=
  .lam (.lam ((inventory.subst beneathTwo).shapeGuard (.var (.vs .vz)) (.var .vz)))

def resultProgram : Term Const Γ (payloadType inventory.fields ⇒ inventory.index ⇒ .prop) :=
  .lam (.lam ((inventory.subst beneathTwo).resultGuard (.var (.vs .vz)) (.var .vz)))

variable {space : Ty Base}
  (construct : Term Const Γ (inventory.number ⇒ payloadType inventory.fields ⇒ (inventory.number ⇒ space) ⇒ space))

def rootProgram : Term Const Γ (space ⇒ inventory.index ⇒ .prop) :=
  .lam (.lam ((inventory.subst beneathTwo).rootIndex
    (HOL.subst beneathTwo construct) (.var (.vs .vz)) (.var .vz)))

variable (model : HenkinModel.{u,v,w} Base Const) (full : model.FullDomains)
include full

theorem shapeProgram_denote (values : model.Valuation Γ)
    (tag : Ty.denote model.Carrier inventory.number)
    (payload : Ty.denote model.Carrier (payloadType inventory.fields)) :
    (model.denote inventory.shapeProgram values tag payload).down ↔
      ∃ data : inventory.Data model, (inventory.dataAllowed model values data ∧
        tag = model.denote (inventory.numeral data.1.val) values) ∧
        payloadEquivalence model inventory.fields payload =
          TypeTheory.FiniteConstructorEncoding.encode (Ty.denote model.Carrier) inventory.fields data := by
  change (model.denote ((inventory.subst beneathTwo).shapeGuard (.var (.vs .vz)) (.var .vz))
    (model.extend (model.extend values tag) payload)).down ↔ _
  rw [(inventory.subst beneathTwo).shapeGuard_denote model full]
  simp only [dataAllowed, payloadMatches, ConstructorPrograms.subst, CurriedPredicates.holds,
    Soundness.denote_subst, HenkinModel.denote, PreModel.denote, HenkinModel.extend, PreModel.extend]
  rfl

theorem resultProgram_denote (values : model.Valuation Γ)
    (payload : Ty.denote model.Carrier (payloadType inventory.fields))
    (index : Ty.denote model.Carrier inventory.index) :
    (model.denote inventory.resultProgram values payload index).down ↔
      ∃ data : inventory.Data model, (inventory.dataAllowed model values data ∧
        inventory.resultValue model values data = index) ∧
        payloadEquivalence model inventory.fields payload =
          TypeTheory.FiniteConstructorEncoding.encode (Ty.denote model.Carrier) inventory.fields data := by
  change (model.denote ((inventory.subst beneathTwo).resultGuard (.var (.vs .vz)) (.var .vz))
    (model.extend (model.extend values payload) index)).down ↔ _
  rw [(inventory.subst beneathTwo).resultGuard_denote model full]
  simp only [dataAllowed, resultValue, payloadMatches, ConstructorPrograms.subst, CurriedPredicates.holds,
    Soundness.denote_subst, HenkinModel.denote, PreModel.denote, HenkinModel.extend, PreModel.extend]
  rfl

theorem rootProgram_denote (values : model.Valuation Γ)
    (value : Ty.denote model.Carrier space) (index : Ty.denote model.Carrier inventory.index) :
    (model.denote (inventory.rootProgram construct) values value index).down ↔
      inventory.rootMeaning construct model values value index := by
  change (model.denote ((inventory.subst beneathTwo).rootIndex
    (HOL.subst beneathTwo construct) (.var (.vs .vz)) (.var .vz))
      (model.extend (model.extend values value) index)).down ↔ _
  rw [(inventory.subst beneathTwo).rootIndex_denote _ model full]
  simp only [rootMeaning, dataAllowed, resultValue, packedData, ConstructorPrograms.subst,
    CurriedPredicates.holds, Soundness.denote_subst,
    HenkinModel.denote, PreModel.denote, HenkinModel.extend, PreModel.extend]
  rfl

#print axioms rootProgram_denote
#print axioms shapeProgram_denote
#print axioms resultProgram_denote
end ConstructorPrograms

namespace Inventory
open ConstructorPrograms
variable (inventory : Inventory Const Γ)

def activeProgram : Term Const Γ (payloadType inventory.fields ⇒ inventory.number ⇒ .prop) :=
  .lam (.lam ((inventory.subst beneathTwo).activeGuard (.var (.vs .vz)) (.var .vz)))

def childProgram : Term Const Γ
    (payloadType inventory.fields ⇒ inventory.number ⇒ inventory.index ⇒ .prop) :=
  .lam (.lam (.lam ((inventory.subst beneathThree).childGuard
    (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))))

variable {space : Ty Base}
  (construct : Term Const Γ (inventory.number ⇒ payloadType inventory.fields ⇒ (inventory.number ⇒ space) ⇒ space))

def edgeProgram : Term Const Γ
    (payloadType inventory.fields ⇒ inventory.number ⇒ space ⇒ .prop) :=
  .lam (.lam (.lam ((inventory.subst beneathThree).edgeGuard
    (HOL.subst beneathThree construct) (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))))

variable (model : HenkinModel.{u,v,w} Base Const) (full : model.FullDomains)
include full

theorem edgeProgram_denote (values : model.Valuation Γ)
    (payload : Ty.denote model.Carrier (payloadType inventory.fields))
    (slot : Ty.denote model.Carrier inventory.number) (child : Ty.denote model.Carrier space) :
    (model.denote (inventory.edgeProgram construct) values payload slot child).down ↔
      inventory.edgeMeaning construct model values payload slot child := by
  change (model.denote ((inventory.subst beneathThree).edgeGuard
    (HOL.subst beneathThree construct) (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz))
      (model.extend (model.extend (model.extend values payload) slot) child)).down ↔ _
  rw [(inventory.subst beneathThree).edgeGuard_denote _ model full]
  simp only [edgeMeaning, ConstructorPrograms.rootMeaning, ConstructorPrograms.dataAllowed, childValue, ConstructorPrograms.resultValue, ConstructorPrograms.packedData, Inventory.subst, ConstructorPrograms.subst,
    CurriedPredicates.holds, Soundness.denote_subst,
    HenkinModel.denote, PreModel.denote, HenkinModel.extend, PreModel.extend]
  rfl

#print axioms edgeProgram_denote
end Inventory
end Mettapedia.Logic.HOL.IndexedConstructorGuards
