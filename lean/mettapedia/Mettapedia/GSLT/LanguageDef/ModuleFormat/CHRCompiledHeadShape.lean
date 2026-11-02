import Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRRuleCompilation
import Mettapedia.OSLF.MeTTaIL.GeneralVectorMatchReadout

/-! Every successfully compiled CHR head has the shared constructor/vector
shape. The bag-selection theorem can therefore read actual matched head
occurrences and the exact remainder from one retained assignment. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.HeadShape

open Mettapedia.Languages.CHR
open Mettapedia.OSLF.MeTTaIL Syntax
open GeneralFirstOrderProjection

private theorem traverse_property {α : Type} (compile : α → Option Pattern) (property : Pattern → Prop)
    (inputs : List α) (outputs : List Pattern)
    (step : ∀ input ∈ inputs, ∀ output, compile input = some output → property output)
    (compiled : inputs.mapM compile = some outputs) : ∀ output ∈ outputs, property output := by
  induction inputs generalizing outputs with
  | nil =>
    have empty : outputs = [] := by simpa using compiled.symm
    subst outputs
    simp
  | cons input rest ih =>
    cases first : compile input with
    | none => simp [List.mapM_cons, first] at compiled
    | some output =>
      cases tail : rest.mapM compile with
      | none => simp [List.mapM_cons, first, tail] at compiled
      | some results =>
        have same : output :: results = outputs := by simpa [List.mapM_cons, first, tail] using compiled
        subst outputs
        intro result member
        rcases List.mem_cons.mp member with rfl | member
        · exact step input List.mem_cons_self result first
        · exact ih results (fun child present => step child (List.mem_cons_of_mem input present)) tail result member

private theorem tuple_shape (values : List Pattern) (children : ∀ value ∈ values, VectorFirstOrder value) :
    VectorFirstOrder (.apply "ChrTuple" [vector values]) := by
  apply VectorFirstOrder.constructor
  intro argument member
  cases List.mem_singleton.mp member
  exact .vector values children

theorem literal_shape (vocabulary : Vocabulary) (source : Value) (code : Pattern)
    (compiled : literal? vocabulary source = some code) : VectorFirstOrder code := by
  cases source with
  | integer number =>
    cases slot : vocabulary.scalars.idxOf? (.integer number) with
    | none => simp [literal?, slot] at compiled
    | some index =>
      have same : Pattern.fvar (scalarSlot index) = code := by simpa [literal?, slot] using compiled
      subst code
      exact .metavariable _
  | atom name =>
    cases slot : vocabulary.scalars.idxOf? (.atom name) with
    | none => simp [literal?, slot] at compiled
    | some index =>
      have same : Pattern.fvar (scalarSlot index) = code := by simpa [literal?, slot] using compiled
      subst code
      exact .metavariable _
  | tuple fields =>
    rw [literal?] at compiled
    change ((fields.mapM (literal? vocabulary)).bind fun values =>
      some (Pattern.apply "ChrTuple" [vector values])) = some code at compiled
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨values, fieldsCompiled, rfl⟩ := compiled
    apply tuple_shape
    exact traverse_property _ _ fields values
      (fun field _ result read => literal_shape vocabulary field result read) fieldsCompiled
termination_by sizeOf source

theorem term_shape (vocabulary : Vocabulary) (source : Mettapedia.Languages.CHR.Term) (code : Pattern)
    (compiled : term? vocabulary source = some code) : VectorFirstOrder code := by
  cases source with
  | value datum => exact literal_shape vocabulary datum code (by simpa only [term?] using compiled)
  | var index =>
    have same : Pattern.fvar (variableSlot index) = code := by simpa only [term?, Option.some.injEq] using compiled
    subst code
    exact .metavariable _
  | tuple fields =>
    rw [term?] at compiled
    change ((fields.mapM (term? vocabulary)).bind fun values =>
      some (Pattern.apply "ChrTuple" [vector values])) = some code at compiled
    simp only [Option.bind_eq_some_iff, Option.some.injEq] at compiled
    obtain ⟨values, fieldsCompiled, rfl⟩ := compiled
    apply tuple_shape
    exact traverse_property _ _ fields values
      (fun field _ result read => term_shape vocabulary field result read) fieldsCompiled
termination_by sizeOf source

theorem head_shape (vocabulary : Vocabulary) (source : Head) (code : Pattern)
    (compiled : head? vocabulary source = some code) : VectorFirstOrder code := by
  change ((vocabulary.predicates.idxOf? source.name).bind fun index =>
    (source.arguments.mapM (term? vocabulary)).bind fun values =>
      some (Pattern.apply "ChrConstraint" [.fvar (predicateSlot index), vector values])) = some code at compiled
  simp only [Option.bind_eq_some_iff, Option.some.injEq] at compiled
  obtain ⟨index, _, values, fieldsCompiled, rfl⟩ := compiled
  apply VectorFirstOrder.constructor
  intro argument member
  rcases List.mem_cons.mp member with rfl | member
  · exact .metavariable _
  · cases List.mem_singleton.mp member
    apply VectorFirstOrder.vector
    exact traverse_property _ _ source.arguments values
      (fun field _ result read => term_shape vocabulary field result read) fieldsCompiled

theorem compiled_rule_heads (vocabulary : Vocabulary) (query active : Nat) (source : Rule)
    (rule : RewriteRule) (compiled : compileRule? vocabulary query active source = some rule) :
    ∃ selected,
      rule.left = .apply (queryLabel query) (poolPatterns vocabulary ++
        [.fvar "chr:active", .apply "ChrStore" [.collection .hashBag selected (some "chr:rest")]]) ∧
      (∀ head ∈ selected, VectorFirstOrder head) := by
  unfold compileRule? at compiled
  split at compiled
  · cases selectedRead : source.heads.zipIdx.mapM (fun (head, index) => do
        pure (occurrence (.fvar (idSlot index active)) (← head? vocabulary head))) with
    | none => rw [selectedRead] at compiled; cases compiled
    | some selected =>
      rw [selectedRead] at compiled
      let built : RewriteRule := {
        name := "chr-query:" ++ toString query
        typeContext := variableContext vocabulary source active
        premises := []
        left := Pattern.apply (queryLabel query) (poolPatterns vocabulary ++
          [.fvar "chr:active", .apply "ChrStore" [.collection .hashBag selected (some "chr:rest")]])
        right := Pattern.apply "ChrMatched"
          [vector (source.variables.eraseDups.map (fun index => .fvar (variableSlot index))),
           heads (selected.take source.kept.length), heads (selected.drop source.kept.length),
           .apply "ChrStore" [.fvar "chr:rest"]] }
      have same : built = rule := Option.some.inj compiled
      subst rule
      refine ⟨selected, rfl, ?_⟩
      refine traverse_property _ VectorFirstOrder _ selected ?_ selectedRead
      intro entry _ output read
      rcases entry with ⟨head, index⟩
      change ((head? vocabulary head).bind fun body =>
        some (occurrence (.fvar (idSlot index active)) body)) = some output at read
      simp only [Option.bind_eq_some_iff, Option.some.injEq] at read
      obtain ⟨body, headCompiled, rfl⟩ := read
      apply VectorFirstOrder.constructor
      intro argument member
      rcases List.mem_cons.mp member with rfl | member
      · exact .metavariable _
      · cases List.mem_singleton.mp member
        exact head_shape vocabulary head body headCompiled
  · cases compiled

#print axioms literal_shape
#print axioms term_shape
#print axioms compiled_rule_heads

end Mettapedia.GSLT.LanguageDef.ModuleFormat.CHRCompilation.HeadShape
