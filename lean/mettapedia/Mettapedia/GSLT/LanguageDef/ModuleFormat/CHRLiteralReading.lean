import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRRequestPools

/-! Substituting the actual matched literal pool into a compiled constant
produces its independent runtime value encoding. Tuples recurse through the
same pool; integer constants become closed radix terms, not opaque names. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.LiteralReading

open Mettapedia.Languages.CHR
open Mettapedia.OSLF.MeTTaIL Syntax Match
open GeneralFirstOrderProjection

private theorem index_reads {α : Type} [BEq α] [LawfulBEq α]
    (items : List α) (value : α) (index : Nat) (selected : items.idxOf? value = some index) :
    items[index]? = some value := by
  obtain ⟨within, same, _⟩ := List.idxOf?_eq_some_iff.mp selected
  simp [within, same]

private theorem traverse_image {α : Type} (compile encode : α → Option Pattern)
    (transform : Pattern → Pattern) (inputs : List α) (outputs : List Pattern)
    (step : ∀ input ∈ inputs, ∀ output, compile input = some output → encode input = some (transform output))
    (compiled : inputs.mapM compile = some outputs) :
    inputs.mapM encode = some (outputs.map transform) := by
  induction inputs generalizing outputs with
  | nil =>
    have empty : outputs = [] := by simpa using compiled.symm
    subst outputs
    rfl
  | cons input rest ih =>
    cases first : compile input with
    | none => simp [List.mapM_cons, first] at compiled
    | some output =>
      cases tail : rest.mapM compile with
      | none => simp [List.mapM_cons, first, tail] at compiled
      | some results =>
        have same : output :: results = outputs := by simpa [List.mapM_cons, first, tail] using compiled
        subst outputs
        have headImage := step input List.mem_cons_self output first
        have tailImage := ih results (fun child member => step child (List.mem_cons_of_mem input member)) tail
        simp only [List.mapM_cons, List.map_cons, headImage, tailImage]
        rfl

theorem literal_instantiation (vocabulary : Vocabulary) (bindings : Bindings)
    (read : RequestPools.Read vocabulary bindings) (source : Value) (code : Pattern)
    (compiled : literal? vocabulary source = some code) :
    value? vocabulary source = some (applyBindings bindings code) := by
  cases source with
  | integer number =>
    cases selected : vocabulary.scalars.idxOf? (.integer number) with
    | none => simp [literal?, selected] at compiled
    | some index =>
      have same : Pattern.fvar (scalarSlot index) = code := by simpa [literal?, selected] using compiled
      subst code
      have stored := read.scalars index (.integer number) (index_reads _ _ _ selected)
      rw [apply_variable, stored]
      simp only [value?, RequestPools.scalarDatum, Option.getD_some]
  | atom name =>
    cases selected : vocabulary.scalars.idxOf? (.atom name) with
    | none => simp [literal?, selected] at compiled
    | some index =>
      have same : Pattern.fvar (scalarSlot index) = code := by simpa [literal?, selected] using compiled
      subst code
      have stored := read.scalars index (.atom name) (index_reads _ _ _ selected)
      rw [apply_variable, stored]
      simp only [value?, selected, RequestPools.scalarDatum]
      rfl
  | tuple fields =>
    rw [literal?] at compiled
    change ((fields.mapM (literal? vocabulary)).bind fun values =>
      some (Pattern.apply "ChrTuple" [vector values])) = some code at compiled
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨values, fieldsCompiled, rfl⟩ := compiled
    have image := traverse_image (literal? vocabulary) (value? vocabulary) (applyBindings bindings)
      fields values (fun field _ result readField => literal_instantiation vocabulary bindings read field result readField)
      fieldsCompiled
    rw [value?]
    rw [image]
    change some (.apply "ChrTuple" [vector (values.map (applyBindings bindings))]) =
      some (applyBindings bindings (.apply "ChrTuple" [vector values]))
    simp only [applyBindings, vector, List.map_cons, List.map_nil, List.append_nil]
termination_by sizeOf source

#print axioms literal_instantiation

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.LiteralReading
