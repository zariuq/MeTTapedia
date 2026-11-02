import Mettapedia.GSLT.LanguageDef.CertificateGSLTContextMaps

/-! # Products and transport of actual premise-position maps -/

namespace Mettapedia.GSLT.LanguageDef.CertificateGSLT.ContextMap

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open _root_.CategoryTheory
open ClassifyingContext

variable {source first second : List Pattern}

def left (first second : List Pattern) : ContextMap (first ++ second) first where
  position index := ⟨index.val, OpenDerivationList.length_left index⟩
  judgment index := OpenDerivationList.get_left index

def right (first second : List Pattern) : ContextMap (first ++ second) second where
  position index := ⟨index.val + first.length, OpenDerivationList.length_right index⟩
  judgment index := OpenDerivationList.get_right index

def pair (toFirst : ContextMap source first) (toSecond : ContextMap source second) :
    ContextMap source (first ++ second) where
  position index := if inside : index.val < first.length then
    toFirst.position ⟨index.val, inside⟩
  else toSecond.position ⟨index.val - first.length, by
    have := index.isLt
    simp only [List.length_append] at this
    omega⟩
  judgment index := by
    split <;> rename_i inside
    · simpa only [List.get_eq_getElem, List.getElem_append_left inside] using
        toFirst.judgment ⟨index.val, inside⟩
    · simpa only [List.get_eq_getElem,
        List.getElem_append_right (Nat.le_of_not_lt inside)] using
        toSecond.judgment ⟨index.val - first.length, by
          have := index.isLt
          simp only [List.length_append] at this
          omega⟩

theorem pair_left (toFirst : ContextMap source first) (toSecond : ContextMap source second) :
    (pair toFirst toSecond).comp (left first second) = toFirst := by
  apply ContextMap.ext
  funext index
  simp only [comp, pair, left, dif_pos index.isLt]

theorem pair_right (toFirst : ContextMap source first) (toSecond : ContextMap source second) :
    (pair toFirst toSecond).comp (right first second) = toSecond := by
  apply ContextMap.ext
  funext index
  simp only [comp, pair, right, Nat.not_lt.mpr (Nat.le_add_left _ _),
    ↓reduceDIte, Nat.add_sub_cancel_right]

@[simp] theorem interpret_left (definition : ValidatedCalculusLanguageDef) (first second : List Pattern) :
    (left first second).interpret definition =
      fstProjection (⟨first⟩ : ClassifyingContext definition) ⟨second⟩ := rfl

@[simp] theorem interpret_right (definition : ValidatedCalculusLanguageDef) (first second : List Pattern) :
    (right first second).interpret definition =
      sndProjection (⟨first⟩ : ClassifyingContext definition) ⟨second⟩ := rfl

theorem interpret_pair (definition : ValidatedCalculusLanguageDef)
    (toFirst : ContextMap source first) (toSecond : ContextMap source second) :
    (pair toFirst toSecond).interpret definition =
      ClassifyingContext.pair (toFirst.interpret definition) (toSecond.interpret definition) := by
  apply ClassifyingContext.pair_unique
  · exact (interpret_comp definition (pair toFirst toSecond) (left first second)).symm.trans
      (congrArg (fun mapping : ContextMap source first => mapping.interpret definition)
        (pair_left toFirst toSecond))
  · exact (interpret_comp definition (pair toFirst toSecond) (right first second)).symm.trans
      (congrArg (fun mapping : ContextMap source second => mapping.interpret definition)
        (pair_right toFirst toSecond))

/-- Retain a newly appended judgment while reindexing the old context. -/
def extend (mapping : ContextMap source first) (goal : Pattern) :
    ContextMap (source ++ [goal]) (first ++ [goal]) :=
  pair ((left source [goal]).comp mapping) (right source [goal])

theorem extend_position_value (mapping : ContextMap source first) (goal : Pattern)
    (index : Fin (first ++ [goal]).length) :
    ((mapping.extend goal).position index).val =
      if inside : index.val < first.length then (mapping.position ⟨index.val, inside⟩).val
      else source.length := by
  unfold extend pair comp left right
  split <;> rename_i inside
  · simp only [dif_pos inside]
  · have last : index.val = first.length := by
      have := index.isLt
      simp only [List.length_append, List.length_cons, List.length_nil] at this
      omega
    simp only [last, Nat.lt_irrefl, ↓reduceDIte, Nat.sub_self, Nat.zero_add]

theorem interpret_extend (definition : ValidatedCalculusLanguageDef)
    (mapping : ContextMap source first) (goal : Pattern) :
    (mapping.extend goal).interpret definition =
      ClassifyingContext.pair
        (fstProjection (⟨source⟩ : ClassifyingContext definition) ⟨[goal]⟩ ≫ mapping.interpret definition)
        (sndProjection (⟨source⟩ : ClassifyingContext definition) ⟨[goal]⟩) := by
  rw [extend, interpret_pair, interpret_comp, interpret_left, interpret_right]
  rfl

def transport {source' first' : List Pattern} (sourceEq : source = source') (targetEq : first = first')
    (mapping : ContextMap source first) : ContextMap source' first' := by
  cases sourceEq
  cases targetEq
  exact mapping

theorem transport_position {source' first' : List Pattern}
    (sourceEq : source = source') (targetEq : first = first') (mapping : ContextMap source first)
    (index : Fin first'.length) :
    (mapping.transport sourceEq targetEq).position index =
      Fin.cast (congrArg List.length sourceEq)
        (mapping.position (Fin.cast (congrArg List.length targetEq).symm index)) := by
  cases sourceEq
  cases targetEq
  rfl

theorem interpret_transport (definition : ValidatedCalculusLanguageDef)
    {source' first' : List Pattern} (sourceEq : source = source') (targetEq : first = first')
    (mapping : ContextMap source first) :
    (mapping.transport sourceEq targetEq).interpret definition =
      eqToHom (congrArg (fun goals => (⟨goals⟩ : ClassifyingContext definition)) sourceEq.symm) ≫
        mapping.interpret definition ≫
        eqToHom (congrArg (fun goals => (⟨goals⟩ : ClassifyingContext definition)) targetEq) := by
  cases sourceEq
  cases targetEq
  simp only [transport, eqToHom_refl, Category.id_comp, Category.comp_id]

end Mettapedia.GSLT.LanguageDef.CertificateGSLT.ContextMap
