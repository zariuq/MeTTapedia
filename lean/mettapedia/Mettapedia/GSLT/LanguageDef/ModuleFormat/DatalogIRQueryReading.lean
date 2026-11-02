import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRAtomMatching
import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRFiringReading

/-! Retained positive query evidence names the exact immutable provider row
and reconstructs its fact in the final shared assignment. This is the body
counterpart of the compiled-head readback. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.QueryReading

open Mettapedia.Languages.Datalog
open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding GeneralScopedMatch Match
open GeneralFirstOrderProjection

theorem output_row_readout (pools : Join.Pools) (position : Nat) (source : Mettapedia.Languages.Datalog.Atom)
    (code : Pattern) (compiled : Join.atom? pools position source = some code)
    {environment : GeneralPremise.Environment} {context : GeneralPremise.Context} {relation : String}
    {initial final chosen : ScopedRuleMatching.Assignment} {rowIndex : Nat}
    {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)} (type : TypeExpr)
    (static : environment.provider.dynamicRelations = [])
    (signature : GeneralPremise.signature? environment.provider relation 1 = some ⟨relation,[type],[.output]⟩)
    (query : GeneralPremise.TracedQuery environment context relation [code] initial rowIndex final origins)
    (later : GeneralScopedMatch.Extends final chosen)
    (roots : GeneralPremise.RootValues context.bound.length chosen) :
    ∃ value, environment.provider.rows[rowIndex]? = some ⟨relation,[value]⟩ ∧
      applyBindings (ordinary chosen) code = value := by
  cases query with
  | @row _ row actualSignature _ _ present selected typed arguments _ =>
    have same : actualSignature = ⟨relation,[type],[.output]⟩ := Option.some.inj (selected.symm.trans signature)
    subst actualSignature
    rcases row with ⟨rowRelation,values⟩
    have sameRelation : rowRelation = relation := typed.1
    subst rowRelation
    cases arguments with
    | @output _ _ _ _ _ value _ _ _ _ _ matching tail =>
      cases tail
      exact ⟨value,present,AtomMatching.compiled_atom_readout pools position source code compiled matching.matching later roots⟩
  | dynamicRow dynamic _ _ _ _ _ _ _ => simp [static] at dynamic

theorem source_query_match (pools : Join.Pools) (position : Nat) (source : Mettapedia.Languages.Datalog.Atom)
    (code : Pattern) (compiled : Join.atom? pools position source = some code)
    {environment : GeneralPremise.Environment} {context : GeneralPremise.Context}
    {initial final chosen : ScopedRuleMatching.Assignment} {rowIndex : Nat}
    {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (static : environment.provider.dynamicRelations = [])
    (signature : GeneralPremise.signature? environment.provider Query.factRelation 1 =
      some ⟨Query.factRelation,[.base "DlStatement"],[.output]⟩)
    (query : GeneralPremise.TracedQuery environment context Query.factRelation [code] initial rowIndex final origins)
    (later : GeneralScopedMatch.Extends final chosen)
    (roots : GeneralPremise.RootValues context.bound.length chosen)
    (poolRead : ClauseReading.PoolsRead pools (ClauseDictionary.expand pools (ordinary chosen))) :
    ∃ value, environment.provider.rows[rowIndex]? = some ⟨Query.factRelation,[value]⟩ ∧
      ∀ fact, IRCodec.groundFact? (applyBindings (Executable.dictionary pools) value) = some fact →
        source.Matches (FiringReading.sourceAssignment pools chosen) fact := by
  obtain ⟨value,present,reconstructed⟩ := output_row_readout pools position source code compiled
    (.base "DlStatement") static signature query later roots
  refine ⟨value,present,?_⟩
  intro fact decoded
  rw [← reconstructed,← ClauseDictionary.atom_expands pools (ordinary chosen) position source code compiled] at decoded
  exact ClauseReading.atom_decoding_sound pools _ poolRead position source code compiled fact decoded

theorem input_argument_readout (pools : Join.Pools) (position index : Nat) (argument : Argument)
    (code : Pattern) (compiled : Join.argument? pools position index argument = some code)
    {context : GeneralPremise.Context} {initial chosen : ScopedRuleMatching.Assignment} {value : Pattern}
    (read : ScopedRuleMatching.instantiateAt? context.rule context.spec context.bound.length
      (context.site index) [] 0 initial code = some value)
    (later : GeneralScopedMatch.Extends initial chosen)
    (roots : GeneralPremise.RootValues context.bound.length chosen) :
    applyBindings (ordinary chosen) code = value := by
  obtain ⟨name,rfl⟩ := ClauseDictionary.argument_variable pools position index argument code compiled
  simp only [ScopedRuleMatching.instantiateAt?,ScopedRuleMatching.instantiateWith?,
    Option.bind_eq_bind,Option.bind_eq_some_iff] at read
  obtain ⟨stored,found,arguments,_,projected⟩ := read
  have retained := later _ _ found
  have empty := root_value_arguments_empty (roots name stored retained) projected
  subst arguments
  have same := Option.some.inj ((root_value_readout (roots name stored retained)).symm.trans projected)
  exact (ordinary_variable retained).trans same

theorem input_row_readout (pools : Join.Pools) (position : Nat) (comparison : Comparison)
    (leftCode rightCode : Pattern)
    (leftCompiled : Join.argument? pools position 0 comparison.left = some leftCode)
    (rightCompiled : Join.argument? pools position 1 comparison.right = some rightCode)
    {environment : GeneralPremise.Environment} {context : GeneralPremise.Context} {relation : String}
    {initial final chosen : ScopedRuleMatching.Assignment} {rowIndex : Nat}
    {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)} (type : TypeExpr)
    (static : environment.provider.dynamicRelations = [])
    (signature : GeneralPremise.signature? environment.provider relation 2 = some ⟨relation,[type,type],[.input,.input]⟩)
    (query : GeneralPremise.TracedQuery environment context relation [leftCode,rightCode] initial rowIndex final origins)
    (later : GeneralScopedMatch.Extends final chosen)
    (roots : GeneralPremise.RootValues context.bound.length chosen) :
    ∃ left right, environment.provider.rows[rowIndex]? = some ⟨relation,[left,right]⟩ ∧
      applyBindings (ordinary chosen) leftCode = left ∧ applyBindings (ordinary chosen) rightCode = right := by
  cases query with
  | @row _ row actualSignature _ _ present selected typed arguments _ =>
    have same : actualSignature = ⟨relation,[type,type],[.input,.input]⟩ := Option.some.inj (selected.symm.trans signature)
    subst actualSignature
    rcases row with ⟨rowRelation,values⟩
    have sameRelation : rowRelation = relation := typed.1
    subst rowRelation
    cases arguments with
    | @input _ _ _ _ left _ _ _ _ leftRead rest =>
      cases rest with
      | @input _ _ _ _ right _ _ _ _ rightRead tail =>
        cases tail
        exact ⟨left,right,present,
          input_argument_readout pools position 0 comparison.left leftCode leftCompiled leftRead later roots,
          input_argument_readout pools position 1 comparison.right rightCode rightCompiled rightRead later roots⟩
  | dynamicRow dynamic _ _ _ _ _ _ _ => simp [static] at dynamic

#print axioms output_row_readout
#print axioms source_query_match
#print axioms input_argument_readout
#print axioms input_row_readout

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.QueryReading
