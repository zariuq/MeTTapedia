import Mettapedia.Languages.MeTTa.SpaceTheory.Presentation
import Mettapedia.Languages.MeTTa.OSLFCore.Bridge
import Mettapedia.Languages.MeTTa.SpaceTheory.NativeTyping
import Mettapedia.GSLT.LanguageDef.CarrierExtension

/-!
# The full Atom vocabulary of a presentation

The constructor reading is not a restriction on the source grammar.
This instance uses the lossless Atom carrier for *every* declared
operand: symbols, grounded values, variables, arbitrary expressions
and their ordered children. Variables in function definitions are
metavariables; a quoted atom (including a written equation's member)
retains the variable as data. This is the term vocabulary, not a new
dialect strategy or a declaration of which calls read modulo equations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.SpaceTheory.NativeVocabulary

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.OSLFCore.Bridge
open Mettapedia.OSLF.MeTTaIL.Syntax (Equation LanguageDef Pattern RewriteRule TypeExpr)
open Mettapedia.OSLF.MeTTaIL.Match (applyBindings binderFree binderFreeList matchPattern)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)
open Mettapedia.OSLF.MeTTaIL.NonrecursiveReduction
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.RootRewriting (root_instantiation_iff)
open Mettapedia.GSLT.LanguageDef.LiveModuleEdits (Order)
open Presentation
open Atoms (Content content)
open NativeTyping (schemaContext atomSort definition_sides_typed)
open Mettapedia.GSLT.LanguageDef.CarrierWellSorted (HasType)

def contribution (atom : Content) : Option Contribution :=
  contributionUsing (some ∘ GroundData.schema) (some ∘ GroundData.encode)
    (some ∘ GroundData.encodeList) schemaContext atom

def parts (atoms : List Atom) : Option (List Contribution) :=
  (atoms.map content).mapM contribution

def present (order : Order) (base : LanguageDef) (atoms : List Atom) : Option PresentedSpace :=
  (parts atoms).map fun found => ⟨atoms, assemble order base found⟩

theorem written_definition (l r : Atom) :
    let rule : RewriteRule :=
      { name := "space definition", typeContext := schemaContext l r, premises := []
        left := GroundData.schema l, right := GroundData.schema r }
    contribution (.definition l r) =
      some { rewrites := [rule] } :=
  rfl

mutual
theorem schema_binderFree (atom : Atom) : binderFree (GroundData.schema atom) = true := by
  cases atom with
  | var => rfl
  | symbol => simp [GroundData.schema, GroundData.encode]; rfl
  | grounded value =>
    cases value with
    | bool b => cases b <;> simp [GroundData.schema, GroundData.encode] <;> rfl
    | _ => simp [GroundData.schema, GroundData.encode]; rfl
  | expression children =>
    simp [GroundData.schema, binderFree, binderFreeList, schemaList_binderFree children]
termination_by sizeOf atom

theorem schemaList_binderFree (atoms : List Atom) : binderFreeList (GroundData.schemaList atoms) = true := by
  cases atoms with
  | nil => rfl
  | cons atom tail =>
    simp [GroundData.schemaList, binderFreeList, schema_binderFree atom, schemaList_binderFree tail]
termination_by sizeOf atoms
end

private theorem compiled_rule (atom : Content) {part : Contribution} (built : contribution atom = some part)
    {rule : RewriteRule} (member : rule ∈ part.rewrites) :
    ∃ left right, atom = .definition left right ∧ rule.left = GroundData.schema left ∧
      rule.right = GroundData.schema right ∧ rule.premises = [] ∧
      rule.typeContext = schemaContext left right := by
  obtain ⟨left, right, source, l, r, unconditional, types⟩ :=
    contribution_rule_origin (definitionTerm := some ∘ GroundData.schema) built member
  exact ⟨left, right, source, (Option.some.inj l).symm, (Option.some.inj r).symm, unconditional, types⟩

/-- Both sides are typed in the actual finite context carried by a
definition or equation, rather than by a global assignment to names. -/
def AtomSides (language : LanguageDef) (context : List (String × TypeExpr))
    (left right : Pattern) : Prop :=
  HasType language (fun name => context.lookup name) [] left atomSort ∧
    HasType language (fun name => context.lookup name) [] right atomSort

private theorem atomSides_extend {source target : LanguageDef}
    (types : source.types ⊆ target.types) (terms : source.terms ⊆ target.terms)
    {context : List (String × TypeExpr)} {left right : Pattern}
    (typed : AtomSides source context left right) : AtomSides target context left right :=
  ⟨typed.1.of_signature_inclusion types terms, typed.2.of_signature_inclusion types terms⟩

theorem contribution_definition_typed (atom : Content) {part : Contribution}
    (built : contribution atom = some part) {rule : RewriteRule} (member : rule ∈ part.rewrites) :
    AtomSides GroundData.dataLanguage rule.typeContext rule.left rule.right := by
  obtain ⟨l, r, _, lhs, rhs, _, types⟩ := compiled_rule atom built member
  rw [types, lhs, rhs]
  exact definition_sides_typed l r

private theorem encoded_member_typed {atoms : List Atom} {term : Pattern}
    (member : term ∈ GroundData.encodeList atoms)
    (context : List (String × TypeExpr)) :
    HasType GroundData.dataLanguage (fun name => context.lookup name) [] term atomSort := by
  induction atoms with
  | nil => simp [GroundData.encodeList] at member
  | cons a tail ih =>
    rw [GroundData.encodeList, List.mem_cons] at member
    rcases member with rfl | member
    · exact GroundData.encode_has_type a _ _
    · exact ih member

theorem contribution_equation_typed (atom : Content) {part : Contribution}
    (built : contribution atom = some part) {equation : Equation} (member : equation ∈ part.equations) :
    AtomSides GroundData.dataLanguage equation.typeContext equation.left equation.right := by
  cases atom
  case equation preference first next rest =>
    cases built
    obtain ⟨target, fromWritten, rfl⟩ := List.mem_map.mp member
    exact ⟨GroundData.encode_has_type first _ _, encoded_member_typed fromWritten []⟩
  all_goals cases built <;> cases member

/-- Typing of all of the snapshot's newly authored definitions and equations.
No restriction on spellings or right-only variables is required for typing.
The operational treatment of a right-only variable is a separate choice. -/
theorem snapshot_declarations_typed (order : Order) (base : LanguageDef) (atoms : List Atom)
    {space : PresentedSpace} (built : present order base atoms = some space)
    (types : GroundData.dataLanguage.types ⊆ base.types)
    (terms : GroundData.dataLanguage.terms ⊆ base.terms) :
    (∀ rule ∈ space.language.rewrites, rule ∉ base.rewrites →
      AtomSides space.language rule.typeContext rule.left rule.right) ∧
    (∀ eq ∈ space.language.equations, eq ∉ base.equations →
      AtomSides space.language eq.typeContext eq.left eq.right) := by
  obtain ⟨found, compiled, rfl⟩ := Option.map_eq_some_iff.mp built
  have origin {part : Contribution} (member : part ∈ found) :
      ∃ atom, contribution atom = some part := by
    obtain ⟨atom, _, result⟩ :=
      Mettapedia.Data.List.option_mapM_origin contribution (atoms.map content) _ compiled _ member
    exact ⟨atom, result⟩
  have newRule {rule : RewriteRule} (member : rule ∈ found.flatMap Contribution.rewrites) :
      AtomSides (assemble order base found) rule.typeContext rule.left rule.right := by
    obtain ⟨part, selected, contributed⟩ := List.mem_flatMap.mp member
    obtain ⟨atom, presented⟩ := origin selected
    exact atomSides_extend (target := assemble order base found) types terms
      (contribution_definition_typed atom presented contributed)
  constructor
  · intro rule required notInherited
    apply newRule
    cases order with
    | front => exact (List.mem_append.mp required).resolve_right notInherited
    | back => exact (List.mem_append.mp required).resolve_left notInherited
  · intro eq required notInherited
    obtain ⟨part, selected, contributed⟩ := List.mem_flatMap.mp
      ((List.mem_append.mp required).resolve_left notInherited)
    obtain ⟨atom, presented⟩ := origin selected
    exact atomSides_extend (target := assemble order base found) types terms
      (contribution_equation_typed atom presented contributed)

theorem native_data_snapshot_typed (order : Order) (atoms : List Atom)
    {space : PresentedSpace} (built : present order GroundData.dataLanguage atoms = some space) :
    (∀ rule ∈ space.language.rewrites,
      AtomSides space.language rule.typeContext rule.left rule.right) ∧
    (∀ eq ∈ space.language.equations,
      AtomSides space.language eq.typeContext eq.left eq.right) := by
  obtain ⟨rules, equations⟩ := snapshot_declarations_typed _ _ _ built
    (List.Subset.refl _) (List.Subset.refl _)
  exact ⟨fun r h => rules r h (by simp [GroundData.dataLanguage]),
    fun e h => equations e h (by simp [GroundData.dataLanguage])⟩

open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)

/-- The body of a selected definition decodes after instantiation to
the actual source substitution, including an unbound variable kept as
data. This does not execute a captured atom accidentally. -/
theorem instantiated_body (atom : Content) {part : Contribution}
    (built : contribution atom = some part) {rule : RewriteRule} (member : rule ∈ part.rewrites)
    (binding : Subst) :
    ∃ left right, atom = .definition left right ∧
      GroundData.decode (applyBindings (GroundData.bindingsFor binding right) rule.right) =
        some (applySubst binding right) := by
  obtain ⟨left, right, authored, _, body, _, _⟩ := compiled_rule atom built member
  refine ⟨left, right, authored, ?_⟩
  rw [body]
  exact GroundData.instantiated_schema_decodes binding right

theorem aligned (order : Order) (base : LanguageDef) (atoms : List Atom)
    (baseAligned : isUnconditionalAligned base = true)
    {space : PresentedSpace} (loaded : present order base atoms = some space) :
    isUnconditionalAligned space.language = true := by
  obtain ⟨found, indexed, rfl⟩ := Option.map_eq_some_iff.mp loaded
  exact assemble_aligned order base baseAligned (definitionTerm := some ∘ GroundData.schema)
    (fun a _ h => (Option.some.inj h) ▸ schema_binderFree a) atoms indexed

/-- This characterizes steps of the encoded Pattern presentation.
Native equation observations use `SpaceTheory.AtomEquations`:
the unrestricted Pattern context may enter a literal's representation. -/
theorem encoded_step_iff (order : Order) (base : LanguageDef) (atoms : List Atom)
    (baseAligned : isUnconditionalAligned base = true)
    {space : PresentedSpace} (loaded : present order base atoms = some space)
    (premises : BasePremiseEvaluator) (input output : Pattern) :
    (space.theory premises).Step input output ↔
      ∃ rule ∈ space.language.rewrites, ∃ representative σ,
        EquationEquiv premises space.language input representative ∧
        σ ∈ matchPattern rule.left representative ∧
        EquationEquiv premises space.language (applyBindings σ rule.right) output :=
  root_instantiation_iff premises space.language (aligned order base atoms baseAligned loaded) input output

section Controls

private def l : Atom := .expression [.var "head", .grounded (.int 3)]
private def r : Atom := .expression [.var "head"]

theorem variable_head_and_grounded_value_are_presentable :
    ∃ space, present .back GroundData.dataLanguage [(Content.definition l r).syntax] = some space ∧
      rootReducts space.language (GroundData.encode (.expression [.symbol "A", .grounded (.int 3)])) =
        [GroundData.encode (.expression [.symbol "A"])] := by
  refine ⟨_, rfl, ?_⟩
  decide +kernel

theorem a_symbol_does_not_fire_a_singleton_expression_definition :
    ∃ space, present .back GroundData.dataLanguage
        [(Content.definition (.expression [.symbol "A"]) (.symbol "B")).syntax] = some space ∧
      rootReducts space.language (GroundData.encode (.symbol "A")) = [] := by
  refine ⟨_, rfl, ?_⟩
  decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.SpaceTheory.NativeVocabulary
