import Mettapedia.Languages.MM0.Presentation.ConversionChildren
import Mettapedia.Languages.MM0.Presentation.UnfoldingTheory

/-!
# Complete authored MM0 conversion checking

Every finite submitted witness is checked by the authored equations. The exact
result agrees with the independent witness semantics, including refusals.
The completeness endpoint concerns the independent conversion judgment and
allows finite witnesses without prescribing the internal computation trace.
-/

set_option autoImplicit false
set_option maxRecDepth 2048

namespace Mettapedia.Languages.MM0.Presentation.ComputationalConversion

open Kernel ComputationalContext ComputationalTyping ComputationalArguments ComputationalDefinitions
open Mettapedia.GSLT.LanguageDef.DeterministicEquations

local notation "P" => conversionProgram
local notation "A" => conversionEquations
local notation "H" => dataEqualityHost

mutual

theorem conversion_computes (table : SignatureTable) (definitions : DefinitionTable) (context : Context)
    (witness : ConvWitness) :
    Applies P H "mm0:conversion"
      [encodeTable table, encodeDefinitions definitions, encodeContext context, encodeWitness witness]
      (encodeConversion (ConvWitness.conversion? (signatureOf table) (definitionsOf definitions) context witness)) := by
  cases witness with
  | refl expression =>
      rw [encodeWitness, ConvWitness.conversion?]
      refine conversion_equation (equation := A[3]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) .nil))
        (refl_type_computes (Preterm.infer (signatureOf table) context expression) expression)
      exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl))
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) (infer_reused table context expression)
  | symm child =>
      rw [encodeWitness, ConvWitness.conversion?]
      refine conversion_equation (equation := A[8]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call
        (values := [encodeConversion (ConvWitness.conversion? (signatureOf table) (definitionsOf definitions) context child)])
        (by simp [Special]) (.cons ?_ .nil) ?_
      · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))
          (conversion_computes table definitions context child)
      · simpa [Option.map_eq_bind] using
          swap_computes (ConvWitness.conversion? (signatureOf table) (definitionsOf definitions) context child)
  | trans first second =>
      rw [encodeWitness]
      refine conversion_equation (equation := A[11]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call
        (values := [encodeConversion (ConvWitness.conversion? (signatureOf table) (definitionsOf definitions) context first),
          encodeTable table, encodeDefinitions definitions, encodeContext context, encodeWitness second])
        (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))) ?_
      · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))
          (conversion_computes table definitions context first)
      · cases firstResult : ConvWitness.conversion? (signatureOf table) (definitionsOf definitions) context first with
        | none =>
            rw [ConvWitness.conversion?, firstResult]
            exact ⟨1, by rw [conversion_apply _ (by decide)]; rfl⟩
        | some converted =>
            rw [ConvWitness.conversion?, firstResult]
            refine conversion_equation (equation := A[13]) (by decide) (by rfl) (by rfl) ?_
            refine Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
              (.cons (.variable (by rfl)) (.cons ?_ .nil))))
              (join_computes converted.left converted.right converted.sort
                (ConvWitness.conversion? (signatureOf table) (definitionsOf definitions) context second))
            exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
              (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))
              (conversion_computes table definitions context second)
  | congruence symbol children =>
      rw [encodeWitness]
      refine conversion_equation (equation := A[18]) (by decide) (by rfl) (by rfl) ?_
      refine Evaluates.call (values := [encodeDeclarationResult (signatureOf table symbol), encodeTable table,
        encodeDefinitions definitions, encodeContext context, natural symbol, encodeWitnesses children])
        (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))) ?_
      · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))
          (unfolding_reused _ (by
            simp only [unfoldingProgram, ComputationalFreshDummies.freshEquations, encodeBinder,
              encodeDependencies, encodeNaturals, Finset.sort_empty]
            decide) _ _ (declaration_reused table symbol))
      · cases found : signatureOf table symbol with
        | none =>
            rw [ConvWitness.conversion?, found]
            exact ⟨1, by rw [conversion_apply _ (by decide)]; rfl⟩
        | some declaration =>
            rw [ConvWitness.conversion?, found]
            refine conversion_equation (equation := A[20]) (by decide) (by rfl) (by rfl) ?_
            refine Evaluates.call (values := [encodeArguments (ConvWitness.arguments? (signatureOf table)
              (definitionsOf definitions) context children declaration.arguments), natural symbol, natural declaration.resultSort])
              (by simp [Special]) (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) ?_
            · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
                (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)))))
                (conversion_arguments_computes table definitions context children declaration.arguments)
            · simpa [Option.map_eq_bind] using
                congruent_computes (ConvWitness.arguments? (signatureOf table) (definitionsOf definitions)
                  context children declaration.arguments) symbol declaration.resultSort
  | unfold symbol arguments images => exact unfold_witness_computes table definitions context symbol arguments images
termination_by sizeOf witness

theorem conversion_arguments_computes (table : SignatureTable) (definitions : DefinitionTable) (context : Context)
    (children : List ConvWitness) (binders : Context) :
    Applies P H "mm0:conversion-arguments"
      [encodeTable table, encodeDefinitions definitions, encodeContext context, encodeWitnesses children, encodeContext binders]
      (encodeArguments (ConvWitness.arguments? (signatureOf table) (definitionsOf definitions) context children binders)) := by
  refine conversion_equation (equation := A[30]) (by decide) (by rfl) (by rfl) ?_
  refine Evaluates.call (values := [listView (children.map encodeWitness), listView (binders.map encodeBinder),
    encodeTable table, encodeDefinitions definitions, encodeContext context])
    (by simp [Special]) (.cons ?_ (.cons ?_ (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) .nil))))) ?_
  · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (.primitive (by rfl) (by rfl))
  · exact Evaluates.call (by simp [Special]) (.cons (.variable (by rfl)) .nil) (.primitive (by rfl) (by rfl))
  · cases children with
    | nil =>
        cases binders <;> simp only [ConvWitness.arguments?] <;>
          exact ⟨3, by rw [conversion_apply _ (by decide)]; rfl⟩
    | cons child children =>
        cases binders with
        | nil =>
            simp only [ConvWitness.arguments?]
            exact ⟨1, by rw [conversion_apply _ (by decide)]; rfl⟩
        | cons binder binders =>
            rw [ConvWitness.arguments?]
            simpa [Option.map_eq_bind] using
              arguments_view_computes table definitions context child children binder binders
                (ConvWitness.conversion? (signatureOf table) (definitionsOf definitions) context child)
                (ConvWitness.arguments? (signatureOf table) (definitionsOf definitions) context children binders)
                (conversion_computes table definitions context child)
                (conversion_arguments_computes table definitions context children binders)
termination_by sizeOf children

end

theorem conversion_result_exact (table : SignatureTable) (definitions : DefinitionTable) (context : Context)
    (witness : ConvWitness) (result : Term) :
    Applies P H "mm0:conversion"
      [encodeTable table, encodeDefinitions definitions, encodeContext context, encodeWitness witness] result ↔
      result = encodeConversion (ConvWitness.conversion? (signatureOf table) (definitionsOf definitions) context witness) := by
  constructor
  · exact fun computed => computed.deterministic (conversion_computes table definitions context witness)
  · rintro rfl; exact conversion_computes table definitions context witness

theorem conversion_accepts_iff (table : SignatureTable) (definitions : DefinitionTable) (context : Context)
    (witness : ConvWitness) (left right : Preterm) (sort : Nat) :
    Applies P H "mm0:conversion"
      [encodeTable table, encodeDefinitions definitions, encodeContext context, encodeWitness witness]
      (encodeConversion (some ⟨left, right, sort⟩)) ↔
      ConvWitness.Checks (signatureOf table) (definitionsOf definitions) context witness left right sort := by
  rw [conversion_result_exact, ← ConvWitness.conversion_eq_some_iff]
  constructor
  · exact fun same => (encodeConversion_injective same).symm
  · exact fun same => congrArg encodeConversion same.symm

theorem conversion_refuses_iff (table : SignatureTable) (definitions : DefinitionTable) (context : Context)
    (witness : ConvWitness) :
    Applies P H "mm0:conversion"
      [encodeTable table, encodeDefinitions definitions, encodeContext context, encodeWitness witness] (.sym "None") ↔
      ¬ ∃ left right sort, ConvWitness.Checks (signatureOf table) (definitionsOf definitions) context witness left right sort := by
  rw [conversion_result_exact, ← ConvWitness.conversion_none_iff]
  constructor
  · exact fun same => (encodeConversion_injective (show encodeConversion none = _ from same)).symm
  · exact fun same => congrArg encodeConversion same.symm

theorem converts_iff_authored (table : SignatureTable) (definitions : DefinitionTable) (context : Context)
    (left right : Preterm) (sort : Nat) :
    Converts (signatureOf table) (definitionsOf definitions) context left right sort ↔
      ∃ witness, Applies P H "mm0:conversion"
        [encodeTable table, encodeDefinitions definitions, encodeContext context, encodeWitness witness]
        (encodeConversion (some ⟨left, right, sort⟩)) := by
  constructor
  · intro converted
    obtain ⟨witness, checked⟩ := converted.certificate_exists
    exact ⟨witness, (conversion_accepts_iff table definitions context witness left right sort).mpr checked⟩
  · rintro ⟨witness, accepted⟩
    exact ((conversion_accepts_iff table definitions context witness left right sort).mp accepted).derives

theorem conversion_arguments_result_exact (table : SignatureTable) (definitions : DefinitionTable) (context : Context)
    (children : List ConvWitness) (binders : Context) (result : Term) :
    Applies P H "mm0:conversion-arguments"
      [encodeTable table, encodeDefinitions definitions, encodeContext context, encodeWitnesses children, encodeContext binders] result ↔
      result = encodeArguments (ConvWitness.arguments? (signatureOf table) (definitionsOf definitions) context children binders) := by
  constructor
  · exact fun computed => computed.deterministic (conversion_arguments_computes table definitions context children binders)
  · rintro rfl; exact conversion_arguments_computes table definitions context children binders

theorem conversion_arguments_accepts_iff (table : SignatureTable) (definitions : DefinitionTable) (context : Context)
    (children : List ConvWitness) (left right : List Preterm) (binders : Context) :
    Applies P H "mm0:conversion-arguments"
      [encodeTable table, encodeDefinitions definitions, encodeContext context, encodeWitnesses children, encodeContext binders]
      (encodeArguments (some (left, right))) ↔
      ConvWitness.ChecksArgs (signatureOf table) (definitionsOf definitions) context children left right binders := by
  rw [conversion_arguments_result_exact, ← ConvWitness.arguments_eq_some_iff]
  constructor
  · exact fun same => (encodeArguments_injective same).symm
  · exact fun same => congrArg encodeArguments same.symm

theorem conversion_completed_result (table : SignatureTable) (definitions : DefinitionTable) (context : Context)
    (witness : ConvWitness) (fuel : Nat)
    (finished : apply P H fuel "mm0:conversion"
      [encodeTable table, encodeDefinitions definitions, encodeContext context, encodeWitness witness] ≠ .exhausted) :
    apply P H fuel "mm0:conversion"
      [encodeTable table, encodeDefinitions definitions, encodeContext context, encodeWitness witness] =
      .value (encodeConversion (ConvWitness.conversion? (signatureOf table) (definitionsOf definitions) context witness)) :=
  (conversion_computes table definitions context witness).completed fuel finished

theorem conversion_eventually_stable (table : SignatureTable) (definitions : DefinitionTable) (context : Context)
    (witness : ConvWitness) :
    ∃ needed, ∀ fuel, needed ≤ fuel → apply P H fuel "mm0:conversion"
      [encodeTable table, encodeDefinitions definitions, encodeContext context, encodeWitness witness] =
      .value (encodeConversion (ConvWitness.conversion? (signatureOf table) (definitionsOf definitions) context witness)) :=
  (conversion_computes table definitions context witness).at_least

theorem theory_conversion_computes (theory : Theory) (context : Context) (witness : ConvWitness) :
    Applies P H "mm0:conversion"
      [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeContext context, encodeWitness witness]
      (encodeConversion (ConvWitness.conversion? theory.termSignature theory.definitionSignature context witness)) := by
  simpa only [theory_signature, theory_definitions] using conversion_computes theory.terms theory.definitions context witness

theorem theory_conversion_accepts_iff (theory : Theory) (context : Context) (witness : ConvWitness)
    (left right : Preterm) (sort : Nat) :
    Applies P H "mm0:conversion"
      [encodeTable theory.terms, encodeDefinitions theory.definitions, encodeContext context, encodeWitness witness]
      (encodeConversion (some ⟨left, right, sort⟩)) ↔
      ConvWitness.Checks theory.termSignature theory.definitionSignature context witness left right sort := by
  simpa only [theory_signature, theory_definitions] using conversion_accepts_iff theory.terms theory.definitions context witness left right sort

end Mettapedia.Languages.MM0.Presentation.ComputationalConversion
