import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalGroundingRows
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalGroundingFixed

/-!
# The actual finite compiler supplies its source dependency licence

Fixed context/value clauses, substitution helpers and every generated native
row satisfy the arbitrary-target ground-output law. The complete licence is
derived from the compiled rule list, rather than accepted as a new caller
hypothesis. Directed source normalization remains an independent property.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalGroundingCompiled

open SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing

theorem grounded {dev : Definitions.Development} (built : Compiled dev) :
    ∀ rule ∈ built.rules, GroundRead.Grounding rule := by
  intro rule member
  change rule ∈ (ContextRules.fixed ++ RuntimeSubstitution.rules) ++ built.authored at member
  rcases List.mem_append.mp member with fixedOrHelper | authored
  · rcases List.mem_append.mp fixedOrHelper with fixed | helper
    · exact NormalGroundingFixed.fixed rule fixed
    · exact NormalGroundingFixed.helpers rule helper
  · exact NormalGroundingRows.compiled_grounding built.compiled rule authored

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalGroundingCompiled

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalGroundingCompiled.grounded
