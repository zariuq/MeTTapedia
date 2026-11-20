import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalProbeFreshness
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalProgramIsolation

/-!
# Root-probe admission at any reached scoped scanner call

The query may be the standalone scanner or an enclosing computation. The
existing hosting invariant supplies freshness along its actual run. Together
with literal-head isolation and determined native payloads, source apply
admission is exactly the presence of an allowed native root action.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalReachableProbes

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage SourceLanguage.Elaboration Hosting
open NativeTypesOnTheStep.Computing

variable {dev : Definitions.Development} (built : Compiled dev) (D : Discipline MSig [] ())

theorem disabled_refutes_read_redex (scope : Nat)
    (K : List (Constraint (BinderCore.keys built.rules) [] ()))
    (datum : Data (BinderCore.keys built.rules) [] ())
    (storeBelow : StoreBelow scope K) (callBelow : DependsBelow scope datum)
    (disabled : ¬ NormalRootMatching.Enabled built D scope K datum)
    {n : Nat} (term : Tower.Tm n) (continuation : MClosed)
    (read : Reads K datum (rootC (encodeTm term) continuation)) :
    ¬ NormalRootMatching.Redex built term := by
  intro redex
  exact disabled (NormalProbeFreshness.selected_enables_below built D scope K datum _ storeBelow callBelow
    read ((NormalRootMatching.selected_iff_redex built term continuation).mpr redex))

variable
  (supply : Nat → MClosed)
  (spaces : MClosed → Multiset (Row (BinderCore.keys built.rules) [] ()))
  (query : Comp (BinderCore.keys built.rules) [] () D.Ty)
  {querySite : (BinderCore.keys built.rules).Site}
  (queryScoped : query.Scoped [querySite])
  (queryDistinct : (querySite :: query.sites).Nodup) (queryArrows : ArrowComp query)

include queryScoped queryDistinct queryArrows

theorem call_below {configuration : Config (BinderCore.keys built.rules) [] () D.Ty}
    (executed : Runs D (NormalProgram.program built D) supply (Config.initial spaces query) configuration)
    {K : List (Constraint (BinderCore.keys built.rules) [] ())}
    {datum : Data (BinderCore.keys built.rules) [] ()}
    {frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty)}
    {pending : List (Data (BinderCore.keys built.rules) [] () × Comp (BinderCore.keys built.rules) [] () D.Ty)}
    (member : (⟨K, .eval (.apply datum), frames, pending⟩ :
      Branch (BinderCore.keys built.rules) [] () D.Ty) ∈ configuration.branches) :
    StoreBelow configuration.world.scope K ∧ DependsBelow configuration.world.scope datum := by
  apply NormalProbeFreshness.scoped_call_below built
  exact scoping_reachable spaces query (NormalProgramFormation.equations_formed built D)
    queryScoped queryDistinct queryArrows configuration executed _ member

theorem enabled_iff_redex {configuration : Config (BinderCore.keys built.rules) [] () D.Ty}
    (executed : Runs D (NormalProgram.program built D) supply (Config.initial spaces query) configuration)
    {K : List (Constraint (BinderCore.keys built.rules) [] ())}
    {datum : Data (BinderCore.keys built.rules) [] ()}
    {frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty)}
    {pending : List (Data (BinderCore.keys built.rules) [] () × Comp (BinderCore.keys built.rules) [] () D.Ty)}
    (member : (⟨K, .eval (.apply (NormalProbe.wrap datum)), frames, pending⟩ :
      Branch (BinderCore.keys built.rules) [] () D.Ty) ∈ configuration.branches)
    {n : Nat} (term : Tower.Tm n) (continuation : MClosed)
    (determined : Determines K datum (rootC (encodeTm term) continuation)) :
    NormalRootMatching.Enabled built D configuration.world.scope K datum ↔ NormalRootMatching.Redex built term := by
  obtain ⟨storeBelow, callBelow⟩ := call_below built D supply spaces query
    queryScoped queryDistinct queryArrows executed member
  exact NormalProbeFreshness.probe_iff_redex_below built D configuration.world.scope K datum term continuation
    storeBelow (NormalProbeFreshness.below_unwrapped built callBelow) determined

theorem apply_admission_iff_redex {configuration : Config (BinderCore.keys built.rules) [] () D.Ty}
    (executed : Runs D (NormalProgram.program built D) supply (Config.initial spaces query) configuration)
    {K : List (Constraint (BinderCore.keys built.rules) [] ())}
    {datum : Data (BinderCore.keys built.rules) [] ()}
    {frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty)}
    {pending : List (Data (BinderCore.keys built.rules) [] () × Comp (BinderCore.keys built.rules) [] () D.Ty)}
    (member : (⟨K, .eval (.apply (NormalProbe.wrap datum)), frames, pending⟩ :
      Branch (BinderCore.keys built.rules) [] () D.Ty) ∈ configuration.branches)
    {n : Nat} (term : Tower.Tm n) (continuation : MClosed)
    (determined : Determines K datum (rootC (encodeTm term) continuation)) :
    (∃ clause ∈ (NormalProgram.program built D).equations,
      Solvable (K ++ [(instantiate (copyAt (BinderCore.keys built.rules) configuration.world.scope) clause.lhs,
        NormalProbe.wrap datum)])) ↔ NormalRootMatching.Redex built term :=
  (NormalProgramIsolation.probe_admission_iff built D configuration.world.scope K datum).trans
    (enabled_iff_redex built D supply spaces query queryScoped queryDistinct queryArrows executed member
      term continuation determined)

theorem unmatched_reading_no_redex {configuration : Config (BinderCore.keys built.rules) [] () D.Ty}
    (executed : Runs D (NormalProgram.program built D) supply (Config.initial spaces query) configuration)
    {K : List (Constraint (BinderCore.keys built.rules) [] ())}
    {datum : Data (BinderCore.keys built.rules) [] ()}
    {frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty)}
    {pending : List (Data (BinderCore.keys built.rules) [] () × Comp (BinderCore.keys built.rules) [] () D.Ty)}
    (member : (⟨K, .eval (.apply (NormalProbe.wrap datum)), frames, pending⟩ :
      Branch (BinderCore.keys built.rules) [] () D.Ty) ∈ configuration.branches)
    (none : ∀ clause ∈ (NormalProgram.program built D).equations,
      ¬ Solvable (K ++ [(instantiate (copyAt (BinderCore.keys built.rules) configuration.world.scope) clause.lhs,
        NormalProbe.wrap datum)]))
    {n : Nat} (term : Tower.Tm n) (continuation : MClosed)
    (read : Reads K datum (rootC (encodeTm term) continuation)) : ¬ NormalRootMatching.Redex built term := by
  obtain ⟨storeBelow, callBelow⟩ := call_below built D supply spaces query
    queryScoped queryDistinct queryArrows executed member
  apply disabled_refutes_read_redex built D configuration.world.scope K datum storeBelow
    (NormalProbeFreshness.below_unwrapped built callBelow) _ term continuation read
  rintro ⟨clause, probe, matched⟩
  exact none clause ((NormalProgramFormation.equation_mem_iff built D clause).mpr (.inr (.inl probe))) matched

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalReachableProbes

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalReachableProbes.apply_admission_iff_redex
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalReachableProbes.unmatched_reading_no_redex
