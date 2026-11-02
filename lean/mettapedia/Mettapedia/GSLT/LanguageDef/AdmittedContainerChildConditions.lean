import Mettapedia.GSLT.LanguageDef.AdmittedContainerPredicate
import Mettapedia.Logic.HOL.ContextualRecursiveSpaceProofs

/-!
# Source child arrays realize the generated child condition

Decoded source positions supply both the original child root and the
predicate at that same child. Canonical padding handles every inactive slot.
The argument reuses the admitted activity and edge correspondences and
does not assume the generated child condition itself.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.AdmittedContainerHOL

open Mettapedia.Logic Mettapedia.Logic.HOL Mettapedia.TypeTheory
open IndexedContainerPositionTerms IndexedPolynomial.Description

universe u v w x
variable {I : Interface.{u}} {source : PositiveInductiveBlock.Registry} {parameterCount : Nat}
  {context : List I.SortCode} {Base : Type v} {Const : Ty Base → Type w} {Γ : Ctx Base}
  (block : PositiveInductiveBlock.Admitted source I parameterCount context) (registered : block.WellRegistered)
  (sourceOrder : ∀ name container, source.lookup name = some container → IndexedContainer.OrderedFinitary container)
  {reading : Reading I (IndexedPositiveContainer.Unindexed.liftRegistry source I) Const}
  {model : HenkinModel.{v,w,x} Base Const}
  (realization : IndexedContainerPositionTerms.Realization reading
    (IndexedPositiveContainer.Unindexed.liftOrdered sourceOrder) model)
  {guards : FieldGuards reading} (images : FieldImages realization guards)
  (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
  (numeral : Nat → Term Const Γ reading.number)
  (values : model.Valuation Γ) (environment : Env I.Value context)
  (represented : realization.Represents environment rho values)
  (zero : ClosedTerm Const reading.number) (successor : ClosedTerm Const (reading.number ⇒ reading.number))
  (full : model.FullDomains) (arithmeticValues : model.Valuation [])
  (zero_meaning : model.denote zero arithmeticValues = realization.numbers 0)
  (successor_meaning : ∀ n, model.denote successor arithmeticValues (realization.numbers n) = realization.numbers (n+1))
  (index_injective : Function.Injective realization.index)
  (numeral_meaning : ∀ n, model.denote (numeral n) values = realization.numbers n)
  {space : Ty Base} (bottomCode : Term Const Γ space)
  (constructorCode : Term Const Γ (reading.number ⇒
    FiniteConstructorEncoding.payloadType ((codes block registered).map reading.fields) ⇒
      (reading.number ⇒ space) ⇒ space))

include images represented full arithmeticValues zero_meaning successor_meaning index_injective numeral_meaning

theorem childConditions_of_source
    (predicate : Term Const Γ (space ⇒ .prop))
    (payloadCode : Term Const Γ (FiniteConstructorEncoding.payloadType ((codes block registered).map reading.fields)))
    (childrenCode : Term Const Γ (reading.number ⇒ space))
    (point : ConstructorPoint reading (codes block registered) environment)
    (children : Nat → Ty.denote model.Carrier space)
    (payload_exact : model.denote payloadCode values =
      nativePayload block registered sourceOrder realization environment (sourcePoint block registered environment point))
    (children_exact : ∀ slot, model.denote childrenCode values (realization.numbers slot) = children slot)
    (conditions : ∀ slot position,
      ((IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered).coding
        (sourcePoint block registered environment point).2).decode slot = some position →
      IndexedPolynomial.RecursiveSpaceRepresentation.ConstructorRoot
        (IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered)
        (nativePayload block registered sourceOrder realization)
        (fun _ => nativeConstructor block registered sourceOrder realization constructorCode values) environment
        ((IndexedPositiveContainer.Unindexed.blockPolynomial block registered).next
          (sourcePoint block registered environment point).2 position) (children slot) ∧
        (model.denote predicate values (children slot)).down)
    (canonical : ((IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered).coding
      (sourcePoint block registered environment point).2).Canonical (model.denote bottomCode values) children) :
    (model.denote ((recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode).childConditions
      predicate payloadCode childrenCode) values).down := by
  have shifted {type : Ty Base} (term : Term Const Γ type) (slot : Ty.denote model.Carrier reading.number) :
      model.denote (weaken term) (model.extend values slot) = model.denote term values := by
    change model.denote (HOL.rename Rename.weaken term) (model.extend values slot) = model.denote term values
    rw [Soundness.denote_rename, Soundness.renameVal_weaken_extend]
  simp only [RecursiveSpacePredicate.Contextual.childConditions, HenkinModel.denote, PreModel.denote, shifted]
  intro nativeSlot _
  simp only [PreModel.extend, recursiveSignature,
    IndexedConstructorGuards.PositionPrograms.contextual]
  let slot := realization.numbers.symm nativeSlot
  have slot_exact : realization.numbers slot = nativeSlot := realization.numbers.apply_symm_apply nativeSlot
  have child_exact : model.denote childrenCode values nativeSlot = children slot := by
    rw [← slot_exact, children_exact]
  constructor
  · intro active
    have atSlot := (activeProgram_exact block registered sourceOrder realization images rho numeral values environment
      represented zero successor full arithmeticValues zero_meaning successor_meaning point slot).mp
      (by simpa only [slot_exact, payload_exact] using active)
    obtain ⟨position, decoded⟩ := atSlot
    obtain ⟨root, present⟩ := conditions slot position decoded
    refine ⟨?_, ?_⟩
    · have edge := (edgeProgram_exact block registered sourceOrder realization images rho numeral values environment
        represented zero successor full arithmeticValues zero_meaning successor_meaning index_injective numeral_meaning
        constructorCode point slot (children slot)).mpr ⟨position, decoded, root⟩
      simpa only [slot_exact, payload_exact, child_exact] using edge
    · simpa only [child_exact] using present
  · intro inactive
    have absent : ((IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered).coding
        (sourcePoint block registered environment point).2).decode slot = none := by
      cases decoded : ((IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered).coding
          (sourcePoint block registered environment point).2).decode slot with
      | none => rfl
      | some position =>
        apply False.elim
        apply inactive
        have active := (activeProgram_exact block registered sourceOrder realization images rho numeral values environment
          represented zero successor full arithmeticValues zero_meaning successor_meaning point slot).mpr ⟨position, decoded⟩
        simpa only [slot_exact, payload_exact] using active
    have padding := canonical slot absent
    apply (model.eqv_iff_eq_of_fullDomains full _ _).mpr
    simpa only [child_exact] using padding

#print axioms childConditions_of_source

end Mettapedia.GSLT.LanguageDef.AdmittedContainerHOL
