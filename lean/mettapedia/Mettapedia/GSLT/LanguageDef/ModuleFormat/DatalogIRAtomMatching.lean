import Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIRRequestReading

/-! Scoped matching of a compiled atom reconstructs the matched physical
fact in the final shared assignment. This includes vector tuples and
repeated variables; it does not rely on a constructor-only profile. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.AtomMatching

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding GeneralScopedMatch Match
open GeneralFirstOrderProjection

private theorem variable_arguments {rule : RewriteRule} {spec : RuleBindingSpec} {ambient index : Nat}
    {site : RulePatternSite} {path : List Nat} {initial final chosen : ScopedRuleMatching.Assignment}
    (schemas values : List Pattern) (areVariables : ∀ schema ∈ schemas, ∃ name, schema = .fvar name)
    (matched : Arguments rule spec ambient site path 0 initial index schemas values final)
    (later : GeneralScopedMatch.Extends final chosen) (roots : GeneralPremise.RootValues ambient chosen) :
    schemas.map (applyBindings (ordinary chosen)) = values := by
  induction schemas generalizing values initial index with
  | nil => cases matched; rfl
  | cons schema schemas ih =>
    obtain ⟨name,rfl⟩ := areVariables schema List.mem_cons_self
    cases matched with
    | cons first rest =>
      cases first with
      | capture stored =>
        have lookup := capture_ordinary_compatible stored (rest.extends.trans later) roots
        have head := lookup _ List.mem_cons_self
        have scalar := GeneralFirstOrderProjection.apply_variable (ordinary chosen) name
        rw [head] at scalar
        have tail := ih _ (fun other member => areVariables other (List.mem_cons_of_mem _ member)) rest
        simp only [List.map_cons,scalar,tail,Option.getD_some]

theorem compiled_atom_readout (pools : Join.Pools) (position : Nat)
    (source : Mettapedia.Languages.Datalog.Atom) (code : Pattern)
    (compiled : Join.atom? pools position source = some code)
    {rule : RewriteRule} {spec : RuleBindingSpec} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {target : Pattern}
    {initial final chosen : ScopedRuleMatching.Assignment}
    (matched : Matches rule spec ambient site path 0 initial code target final)
    (later : GeneralScopedMatch.Extends final chosen) (roots : GeneralPremise.RootValues ambient chosen) :
    applyBindings (ordinary chosen) code = target := by
  change ((Join.relation? pools source.relation).bind fun name =>
    (source.arguments.zipIdx.mapM fun entry => Join.argument? pools position entry.2 entry.1).bind fun arguments =>
      some (Pattern.apply "GroundFact" [name,.apply "GroundTuple" [Join.vector arguments]])) = some code at compiled
  simp only [Option.bind_eq_some_iff,Option.some.injEq] at compiled
  obtain ⟨name,named,arguments,argsCompiled,rfl⟩ := compiled
  obtain ⟨relationName,rfl⟩ := ClauseDictionary.relation_variable pools source.relation name named
  have areVariables := ClauseDictionary.compiled_arguments_are_variables pools position source.arguments arguments argsCompiled
  cases matched with
  | constructor children =>
    cases children with
    | cons relationMatch remaining =>
      cases remaining with
      | cons tupleMatch last =>
        cases last
        cases relationMatch with
        | capture stored =>
          have lookup := capture_ordinary_compatible stored (tupleMatch.extends.trans later) roots
          have head := lookup _ List.mem_cons_self
          have scalar := GeneralFirstOrderProjection.apply_variable (ordinary chosen) relationName
          rw [head] at scalar
          cases tupleMatch with
          | constructor tupleArguments =>
            cases tupleArguments with
            | cons vectorMatch last =>
              cases last
              cases vectorMatch with
              | bag nonvector _ => exact (nonvector rfl).elim
              | vector values =>
                have read := variable_arguments arguments _ areVariables values later roots
                simp only [applyBindings,List.map_cons,List.map_nil,Join.vector,List.append_nil,scalar,read,Option.getD_some]

#print axioms compiled_atom_readout

end Mettapedia.GSLT.LanguageDef.ModuleFormat.DatalogIR.AtomMatching
