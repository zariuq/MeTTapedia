import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.State

/-!
# Instantiation and the captured source interface

Later instantiation preserves a reading, including a schema's local equations.
Conversely, changing a caller assignment without changing the datum's ambient
terms cannot change its readings. These laws separate parametric derivation
from the invalid generalization of an arbitrary shared hypothesis.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows

open Interface (Frames)

universe uO uT uH
variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}

theorem Closure.readsAt_source_congr (X : Frames Tm Hom) {a b : Obj} (row : Closure Tm a)
    (first second : Hom a b) (agrees : ∀ argument ∈ row.args,
      X.E (X.act first argument) (X.act second argument)) (value : Tm b) :
    row.ReadsAt X first value ↔ row.ReadsAt X second value := by
  have transport : ∀ (source target : Hom a b),
      (∀ argument ∈ row.args, X.E (X.act source argument) (X.act target argument)) →
      row.ReadsAt X source value → row.ReadsAt X target value := by
    intro source target same reading
    obtain ⟨locals, solved, captures, output⟩ := reading
    obtain ⟨lengths, pairs⟩ := List.forall₂_iff_zip.mp captures
    refine ⟨locals, solved, List.forall₂_iff_zip.mpr ⟨lengths, ?_⟩, output⟩
    intro parameter argument member
    have inArguments : argument ∈ row.args := by
      have inMap : argument ∈ (row.schema.params.zip row.args).map Prod.snd :=
        List.mem_map_of_mem (f := Prod.snd) member
      rwa [List.map_snd_zip lengths.ge] at inMap
    exact (X.equivalence b).trans (pairs member) (same argument inArguments)
  exact ⟨transport first second agrees,
    transport second first (fun argument member => (X.equivalence b).symm (agrees argument member))⟩

theorem Row.readsAt_source_congr (X : Frames Tm Hom) {a b : Obj} (row : Row Tm a)
    (first second : Hom a b) (agrees : ∀ term ∈ row.ambientTerms,
      X.E (X.act first term) (X.act second term)) (value : Tm b) :
    row.ReadsAt X first value ↔ row.ReadsAt X second value := by
  cases row with
  | shared term =>
    have same := agrees term (List.mem_singleton_self _)
    exact ⟨fun reading => (X.equivalence b).trans ((X.equivalence b).symm same) reading,
      fun reading => (X.equivalence b).trans same reading⟩
  | schematic row => exact row.readsAt_source_congr X first second agrees value

theorem Row.readsAt_postcompose (X : Frames Tm Hom) {a b c : Obj} (row : Row Tm a)
    (source : Hom a b) (later : Hom b c) (value : Tm b)
    (reading : row.ReadsAt X source value) :
    row.ReadsAt X (X.comp later source) (X.act later value) := by
  cases row with
  | shared term =>
    change X.E (X.act (X.comp later source) term) (X.act later value)
    rw [X.act_comp]
    exact X.preserves later reading
  | schematic row =>
    obtain ⟨locals, solved, captures, output⟩ := reading
    refine ⟨X.comp later locals, Frames.models_comp solved later, ?_, ?_⟩
    · have preserved := captures.imp (fun _ _ same => X.preserves later same)
      simpa only [X.act_comp] using preserved
    · rw [X.act_comp]
      exact X.preserves later output

#print axioms Closure.readsAt_source_congr
#print axioms Row.readsAt_source_congr
#print axioms Row.readsAt_postcompose

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows
