import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRValueInjectivity
import Mathlib.Data.List.Forall2

/-! Source occurrences use the existing constraint and packed-ID encodings.
Their list relation retains positions through selection and erasure, so a
matched physical row has a particular source occurrence and source remainder.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.OccurrenceEncoding

open Mettapedia.Languages.CHR
open Mettapedia.OSLF.MeTTaIL Syntax

def encode? (vocabulary : Vocabulary) (source : Occurrence) : Option Pattern :=
  (constraint? vocabulary source.constraint).map (occurrence (occurrenceRef source.id))

def schema? (vocabulary : Vocabulary) (active : Nat) (entry : Head × Nat) : Option Pattern := do
  pure (occurrence (.fvar (idSlot entry.2 active)) (← head? vocabulary entry.1))

theorem schema_readout (vocabulary : Vocabulary) (active : Nat) (entry : Head × Nat) (schema : Pattern)
    (compiled : schema? vocabulary active entry = some schema) :
    ∃ head, head? vocabulary entry.1 = some head ∧
      schema = occurrence (.fvar (idSlot entry.2 active)) head := by
  change ((head? vocabulary entry.1).bind fun head =>
    some (occurrence (.fvar (idSlot entry.2 active)) head)) = some schema at compiled
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at compiled
  obtain ⟨head, read, same⟩ := compiled
  exact ⟨head, read, same.symm⟩

theorem readout (vocabulary : Vocabulary) (source : Occurrence) (target : Pattern)
    (encoded : encode? vocabulary source = some target) :
    ∃ constraint, constraint? vocabulary source.constraint = some constraint ∧
      target = occurrence (occurrenceRef source.id) constraint := by
  unfold encode? at encoded
  obtain ⟨constraint, read, same⟩ := Option.map_eq_some_iff.mp encoded
  exact ⟨constraint, read, same.symm⟩

theorem paired_of_mapM (vocabulary : Vocabulary) (sources : List Occurrence) (targets : List Pattern)
    (encoded : sources.mapM (encode? vocabulary) = some targets) :
    List.Forall₂ (fun source target => encode? vocabulary source = some target) sources targets := by
  induction sources generalizing targets with
  | nil =>
    have empty : targets = [] := by simpa using encoded.symm
    subst targets
    exact .nil
  | cons first rest ih =>
    obtain ⟨target, targets, firstRead, restRead, rfl⟩ :=
      ValueInjectivity.traverse_cons (encode? vocabulary) first rest targets encoded
    exact .cons firstRead (ih targets restRead)

theorem paired_to_mapM (vocabulary : Vocabulary) {sources : List Occurrence} {targets : List Pattern}
    (paired : List.Forall₂ (fun source target => encode? vocabulary source = some target) sources targets) :
    sources.mapM (encode? vocabulary) = some targets := by
  induction paired with
  | nil => rfl
  | cons first _ rest => simp [List.mapM_cons, first, rest]

theorem paired_eraseIdx {α β : Type} {relation : α → β → Prop} {sources : List α} {targets : List β}
    (paired : List.Forall₂ relation sources targets) (index : Nat) :
    List.Forall₂ relation (sources.eraseIdx index) (targets.eraseIdx index) := by
  induction paired generalizing index with
  | nil => simp
  | cons first tail ih =>
    cases index with
    | zero => simpa using tail
    | succ index => simpa only [List.eraseIdx_cons_succ] using List.Forall₂.cons first (ih index)

theorem selected (vocabulary : Vocabulary) {sources : List Occurrence} {targets : List Pattern}
    (paired : List.Forall₂ (fun source target => encode? vocabulary source = some target) sources targets)
    (index : Nat) (within : index < targets.length) :
    ∃ sourceWithin : index < sources.length,
      encode? vocabulary sources[index] = some targets[index] ∧
      List.Forall₂ (fun source target => encode? vocabulary source = some target)
        (sources.eraseIdx index) (targets.eraseIdx index) := by
  have sourceWithin : index < sources.length := by rw [paired.length_eq]; exact within
  exact ⟨sourceWithin, paired.get sourceWithin within, paired_eraseIdx paired index⟩

#print axioms selected

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.OccurrenceEncoding
