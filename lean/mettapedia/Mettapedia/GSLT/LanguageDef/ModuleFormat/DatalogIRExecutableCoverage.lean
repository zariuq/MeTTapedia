import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRPreparationCoverage
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRExecutable

/-! Every typed source program in the supported nonfloating scalar profile
is accepted by the executable preparation path. This supplies preparation
coverage rather than assuming a successful compiler result. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Executable

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax

def Nonfloating (program : Program) (known : List GroundFact) : Prop :=
  (∀ statement ∈ program.statements, ∀ value ∈ Join.Program.statementValues statement, value.type ≠ .floating) ∧
  (∀ fact ∈ known, ∀ value ∈ fact.values, value.type ≠ .floating) ∧
  (∀ declaration ∈ ProgramStatic.declarations program, ∀ column ∈ declaration.attributes, column.type ≠ .floating)

theorem no_scalar_diagnostic (program : Program) (known : List GroundFact)
    (supported : Nonfloating program known) : scalarDiagnostic? program (Join.Program.pools program known) = none := by
  have literals : (Join.Program.pools program known).literals.any
      (fun value => match value with | .floating _ => true | _ => false) = false := by
    apply List.any_eq_false.mpr
    intro value member
    have nonfloating : value.type ≠ .floating := by
      simp only [Join.Program.pools, List.mem_dedup, List.mem_append, List.mem_flatMap] at member
      rcases member with ⟨statement,present,used⟩ | ⟨fact,present,used⟩
      · exact supported.1 statement present value used
      · exact supported.2.1 fact present value used
    cases value <;> simp_all [Value.type]
  have declarations : (ProgramStatic.declarations program).any
      (fun declaration => declaration.attributes.any (·.type == .floating)) = false := by
    apply List.any_eq_false.mpr
    intro declaration present
    rw [Bool.not_eq_true]
    apply List.any_eq_false.mpr
    intro column used
    simpa only [beq_iff_eq] using supported.2.2 declaration present column used
  unfold scalarDiagnostic?
  change (if ((Join.Program.pools program known).literals.any
    (fun value => match value with | .floating _ => true | _ => false) ||
    (ProgramStatic.declarations program).any (fun declaration => declaration.attributes.any (·.type == .floating)))
    then some "floating scalars require a declared floating comparison profile" else none) = none
  rw [literals,declarations]
  rfl

theorem seed_fact_exists (program : Program) (known : List GroundFact) (fact : GroundFact)
    (present : fact ∈ known) : ∃ code, fact? (Join.Program.pools program known) fact = some code := by
  have relation : fact.relation ∈ (Join.Program.pools program known).relations := by
    simp only [Join.Program.pools, List.mem_dedup, List.mem_append]
    exact Or.inr (List.mem_map.mpr ⟨fact,present,rfl⟩)
  obtain ⟨index,relationRead⟩ := Option.isSome_iff_exists.mp (List.isSome_idxOf?.mpr relation)
  obtain ⟨values,valuesRead⟩ := Join.mapM_exists
    (fun value => ((Join.Program.pools program known).literals.idxOf? value).map valueRef) fact.values (by
      intro value used
      have member : value ∈ (Join.Program.pools program known).literals := by
        simp only [Join.Program.pools, List.mem_dedup, List.mem_append]
        exact Or.inr (List.mem_flatMap.mpr ⟨fact,present,used⟩)
      obtain ⟨slot,found⟩ := Option.isSome_iff_exists.mp (List.isSome_idxOf?.mpr member)
      exact ⟨valueRef slot,by simp [found]⟩)
  refine ⟨.apply "GroundFact" [relationRef index,.apply "GroundTuple" [Join.vector values]],?_⟩
  simp only [fact?,relationRead,Option.bind_eq_bind,Option.bind_some]
  change ((fact.values.mapM (fun value => ((Join.Program.pools program known).literals.idxOf? value).map valueRef)).bind
    fun values => some (Pattern.apply "GroundFact" [relationRef index,.apply "GroundTuple" [Join.vector values]])) = _
  rw [valuesRead]
  rfl

theorem prepare_complete (program : Program) (known : List GroundFact)
    (typed : ProgramStatic.ProgramTyped program)
    (inputs : ∀ fact ∈ known, StaticTyping.FactTyped (ProgramStatic.signature program) fact)
    (supported : Nonfloating program known) :
    ∃ prepared, prepare program known = .ok prepared := by
  obtain ⟨compiled,compiledRead⟩ := Join.Program.prepare_complete program known typed inputs
  have vocabulary := (Join.Program.prepare?_sound program known compiled compiledRead).2.2.1
  obtain ⟨encoded,encodedRead⟩ := Join.mapM_exists (fact? compiled.vocabulary) known (by
    intro fact member
    rw [vocabulary]
    exact seed_fact_exists program known fact member)
  have diagnostic : scalarDiagnostic? program compiled.vocabulary = none := by
    rw [vocabulary]
    exact no_scalar_diagnostic program known supported
  refine ⟨⟨program,compiled.vocabulary,Query.language (compiled.rules.map (Query.lowerRule compiled.vocabulary)),
    encoded.eraseDups,comparisonRows program compiled.vocabulary⟩,?_⟩
  simp only [prepare,compiledRead,diagnostic,encodedRead]
  rfl

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.Executable
