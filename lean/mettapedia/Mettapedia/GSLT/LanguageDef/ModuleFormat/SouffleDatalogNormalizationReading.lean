import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalogNormalizationMeaning

/-! The existing normalization function preserves and reflects the
independent literal/name interpretation of projected program data. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourceMeaning

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Languages.Datalog

mutual
theorem normalization_sound (source target : Pattern) (read : Frontend.normalize? source = some target) :
    Normalizes source target := by
  unfold Frontend.normalize? at read
  split at read
  · obtain ⟨value,meaning,same⟩ := literal_value_sound _ _ _ read
    rw [same]
    exact .literal meaning
  · obtain ⟨value,meaning,same⟩ := literal_value_sound _ _ _ read
    rw [same]
    exact .literal meaning
  · obtain ⟨value,meaning,same⟩ := literal_value_sound _ _ _ read
    rw [same]
    exact .literal meaning
  · cases read
  · rename_i input
    change ((Frontend.qualifiedName? input).bind fun name => some (IRCodec.relation name)) = some target at read
    obtain ⟨name,printed,same⟩ := Option.bind_eq_some_iff.mp read
    rw [← Option.some.inj same]
    exact .relation (qualifiedName_sound input name printed)
  · rename_i input
    change ((Frontend.sourceText? input).bind fun name => some (Pattern.apply "Variable" [IRCodec.atom name])) = some target at read
    obtain ⟨name,printed,same⟩ := Option.bind_eq_some_iff.mp read
    rw [← Option.some.inj same]
    exact .logical (spelling_sound input name printed)
  · rename_i input type
    change ((Frontend.sourceText? input).bind fun name => (Frontend.normalize? type).bind fun kind =>
      some (Pattern.apply "Attribute" [IRCodec.atom name,kind])) = some target at read
    simp only [Option.bind_eq_some_iff,Option.some.injEq] at read
    obtain ⟨name,printed,kind,typeRead,rfl⟩ := read
    exact .attributeData (spelling_sound input name printed) (normalization_sound type kind typeRead)
  · rename_i label children notSymbol notInteger notUnsigned notFloat notRelation notVariable notAttribute
    obtain ⟨outputs,childrenRead,rfl⟩ := Option.map_eq_some_iff.mp read
    have plain : PlainNode label children := by simp_all [PlainNode]
    exact .node label children outputs plain (normalization_children_sound children outputs childrenRead)
  · rename_i children
    change ((Frontend.normalizeChildren? children).bind fun outputs =>
      some (Pattern.collection .vec outputs none)) = some target at read
    obtain ⟨outputs,childrenRead,same⟩ := Option.bind_eq_some_iff.mp read
    rw [← Option.some.inj same]
    exact .vector children outputs (normalization_children_sound children outputs childrenRead)
  · cases read
termination_by sizeOf source
decreasing_by all_goals (subst_vars; simp_wf <;> omega)

theorem normalization_children_sound (sources targets : List Pattern)
    (read : Frontend.normalizeChildren? sources = some targets) : List.Forall₂ Normalizes sources targets := by
  cases sources with
  | nil => cases Option.some.inj read; exact .nil
  | cons head tail =>
    change ((Frontend.normalize? head).bind fun first => (Frontend.normalizeChildren? tail).bind fun rest =>
      some (first :: rest)) = some targets at read
    simp only [Option.bind_eq_some_iff,Option.some.injEq] at read
    obtain ⟨first,headRead,rest,tailRead,rfl⟩ := read
    exact .cons (normalization_sound head first headRead) (normalization_children_sound tail rest tailRead)
termination_by sizeOf sources
decreasing_by all_goals (subst_vars; simp_wf <;> omega)
end

theorem normalization_exact (source target : Pattern) :
    Frontend.normalize? source = some target ↔ Normalizes source target :=
  ⟨normalization_sound source target,normalization_complete⟩

theorem normalization_functional (source first second : Pattern)
    (left : Normalizes source first) (right : Normalizes source second) : first = second :=
  Option.some.inj ((normalization_complete left).symm.trans (normalization_complete right))

#print axioms normalization_sound
#print axioms normalization_exact
#print axioms normalization_functional

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.SourceMeaning
