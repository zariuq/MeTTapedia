import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRQueryReading

/-! Actual comparison-provider rows justify source guards. Operand readback
uses the same final assignment as positive body atoms and the conclusion. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.GuardReading

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding GeneralScopedMatch Match
open GeneralFirstOrderProjection

theorem comparison_row_readout (program : Program) (pools : Join.Pools) (operator : ComparisonOperator)
    (left right : Pattern)
    (present : (⟨Join.comparisonName operator,[left,right]⟩ : GeneralPremise.ProviderRow) ∈ Executable.comparisonRows program pools) :
    ∃ leftIndex rightIndex leftValue rightValue,
      left = Executable.valueRef leftIndex ∧ right = Executable.valueRef rightIndex ∧
      pools.literals[leftIndex]? = some leftValue ∧ pools.literals[rightIndex]? = some rightValue ∧
      Executable.policy.Holds operator leftValue rightValue := by
  obtain ⟨actual,_,rows⟩ := List.mem_flatMap.mp present
  obtain ⟨⟨leftValue,leftIndex⟩,leftAt,rows⟩ := List.mem_flatMap.mp rows
  obtain ⟨⟨rightValue,rightIndex⟩,rightAt,formed⟩ := List.mem_filterMap.mp rows
  dsimp only at formed
  by_cases accepted : Executable.compare actual leftValue rightValue = true
  · rw [if_pos accepted] at formed
    have same := Option.some.inj formed
    have operators := Executable.comparisonName_injective (congrArg GeneralPremise.ProviderRow.relation same)
    subst actual
    have values := congrArg GeneralPremise.ProviderRow.values same
    have leftRef := (List.cons.inj values).1.symm
    have rightRef := (List.cons.inj (List.cons.inj values).2).1.symm
    exact ⟨leftIndex,rightIndex,leftValue,rightValue,leftRef,rightRef,
      List.mk_mem_zipIdx_iff_getElem?.mp leftAt,List.mk_mem_zipIdx_iff_getElem?.mp rightAt,
      (Executable.primitive_comparison_exact _ _ _).mp accepted⟩
  · rw [if_neg accepted] at formed
    cases formed

theorem source_guard_sound (program : Program) (pools : Join.Pools) (known : List Pattern)
    (position : Nat) (comparison : Comparison) (leftCode rightCode : Pattern)
    (leftCompiled : Join.argument? pools position 0 comparison.left = some leftCode)
    (rightCompiled : Join.argument? pools position 1 comparison.right = some rightCode)
    {environment : GeneralPremise.Environment} {context : GeneralPremise.Context}
    {initial final chosen : ScopedRuleMatching.Assignment} {rowIndex : Nat}
    {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (rows : environment.provider.rows = (Query.provider known).rows ++ Executable.comparisonRows program pools)
    (static : environment.provider.dynamicRelations = [])
    (signature : GeneralPremise.signature? environment.provider (Join.comparisonName comparison.operator) 2 =
      some ⟨Join.comparisonName comparison.operator,[.base "DlValue",.base "DlValue"],[.input,.input]⟩)
    (query : GeneralPremise.TracedQuery environment context (Join.comparisonName comparison.operator)
      [leftCode,rightCode] initial rowIndex final origins)
    (later : GeneralScopedMatch.Extends final chosen)
    (roots : GeneralPremise.RootValues context.bound.length chosen)
    (poolRead : ClauseReading.PoolsRead pools (ClauseDictionary.expand pools (ordinary chosen))) :
    Comparisons.Holds Executable.policy (FiringReading.sourceAssignment pools chosen) comparison := by
  obtain ⟨left,right,present,leftRead,rightRead⟩ := QueryReading.input_row_readout pools position comparison leftCode rightCode
    leftCompiled rightCompiled (.base "DlValue") static signature query later roots
  have member := List.mem_of_getElem? present
  rw [rows] at member
  have compared : (⟨Join.comparisonName comparison.operator,[left,right]⟩ : GeneralPremise.ProviderRow) ∈
      Executable.comparisonRows program pools := by
    rcases List.mem_append.mp member with fact | compared
    · obtain ⟨_,_,same⟩ := List.mem_map.mp fact
      have lengths := congrArg (fun row : GeneralPremise.ProviderRow => row.values.length) same
      simp at lengths
    · exact compared
  obtain ⟨leftIndex,rightIndex,leftValue,rightValue,leftRef,rightRef,leftAt,rightAt,holds⟩ :=
    comparison_row_readout program pools comparison.operator left right compared
  have leftDecoded : IRCodec.value? (applyBindings (ClauseDictionary.expand pools (ordinary chosen)) leftCode) = some leftValue := by
    rw [ClauseDictionary.argument_expands pools (ordinary chosen) position 0 comparison.left leftCode leftCompiled,
      leftRead,leftRef,Executable.value_dictionary_expands pools leftIndex leftValue leftAt,IRCodec.value_roundtrip]
  have rightDecoded : IRCodec.value? (applyBindings (ClauseDictionary.expand pools (ordinary chosen)) rightCode) = some rightValue := by
    rw [ClauseDictionary.argument_expands pools (ordinary chosen) position 1 comparison.right rightCode rightCompiled,
      rightRead,rightRef,Executable.value_dictionary_expands pools rightIndex rightValue rightAt,IRCodec.value_roundtrip]
  exact ⟨leftValue,rightValue,
    ClauseReading.argument_decoding_sound pools _ poolRead position 0 comparison.left leftCode leftCompiled leftValue leftDecoded,
    ClauseReading.argument_decoding_sound pools _ poolRead position 1 comparison.right rightCode rightCompiled rightValue rightDecoded,
    holds⟩

#print axioms comparison_row_readout
#print axioms source_guard_sound

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.GuardReading
