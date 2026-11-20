import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalScannerCallMoves
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalScannerPhaseMoves
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalScannerExecution

/-!
# Every completed live scanner branch certifies its original native input

The invariant is pointwise on actual source alternatives. Every possible
selected equation and continuation move is covered. Unrelated alternatives
cannot supply its certificate. Source scoping earns fresh call admission;
the typed parent stack retains context at binders throughout the run.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerReflection

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage SourceLanguage.Elaboration Hosting
open NativeTypesOnTheStep.Computing
open NormalChildViews (Child)
open NormalScannerCertificates (Certificate)

variable {dev : Definitions.Development} (built : Compiled dev) (D : Discipline MSig [] ())
  (supply : Nat → MClosed)

def FreshCalls (scope : Nat) (before : Branch (BinderCore.keys built.rules) [] () D.Ty) : Prop :=
  ∀ datum, before.focus = .eval (.apply datum) →
    StoreBelow scope before.store ∧ DependsBelow scope datum

theorem fresh_of_scoping {scope : Nat} {before : Branch (BinderCore.keys built.rules) [] () D.Ty}
    (runtimeScope : Scoping scope before) : FreshCalls built D scope before := by
  intro datum focus
  rcases before with ⟨K, oldFocus, frames, pending⟩
  change oldFocus = .eval (.apply datum) at focus
  subst oldFocus
  exact NormalProbeFreshness.scoped_call_below built runtimeScope

theorem move {outer : Child} {world nextWorld : World (BinderCore.keys built.rules) [] ()}
    {before : Branch (BinderCore.keys built.rules) [] () D.Ty}
    {children : Multiset (Branch (BinderCore.keys built.rules) [] () D.Ty)}
    (known : Certificate built D outer before) (fresh : FreshCalls built D world.scope before)
    (moved : Move D (NormalProgram.program built D) supply world before nextWorld children) :
    ∀ child ∈ children, Solvable child.store → Certificate built D outer child := by
  cases known with
  | scan datum current frames input outside =>
      obtain ⟨storeBelow, callBelow⟩ := fresh _ rfl
      exact NormalScannerCallMoves.scan_move built D supply _ datum frames input outside storeBelow callBelow moved
  | start current scope frames fields outside =>
      exact NormalScannerPhaseMoves.start_move built D supply current scope frames fields outside moved
  | probing current scope frames fields outside =>
      obtain ⟨storeBelow, callBelow⟩ := fresh _ rfl
      exact NormalScannerCallMoves.probing_move built D supply _ scope frames fields outside storeBelow callBelow moved
  | probed current scope frames root fields outside =>
      exact NormalScannerPhaseMoves.probed_move built D supply current scope frames root fields outside moved
  | redexReturning K datum body frames =>
      exact NormalScannerPhaseMoves.redexReturning_move built D supply K datum body frames moved
  | redexValue K datum body frames =>
      exact NormalScannerPhaseMoves.redexValue_move built D supply K datum body frames moved
  | chain current scope checkedJobs jobs frames partition root checked fields outside =>
      exact NormalScannerPhaseMoves.chain_move built D supply current scope checkedJobs jobs frames partition
        root checked fields outside moved
  | normalValue current frames normal outside =>
      exact NormalScannerPhaseMoves.normalValue_move built D supply current frames normal outside moved

def Invariant (outer : Child) (configuration : Config (BinderCore.keys built.rules) [] () D.Ty) : Prop :=
  ∀ branch ∈ configuration.branches, Solvable branch.store → Certificate built D outer branch

section Reached

variable (spaces : MClosed → Multiset (Row (BinderCore.keys built.rules) [] ()))
  (query : Comp (BinderCore.keys built.rules) [] () D.Ty)
  {querySite : (BinderCore.keys built.rules).Site}
  (queryScoped : query.Scoped [querySite]) (queryDistinct : (querySite :: query.sites).Nodup)
  (queryArrows : ArrowComp query)

include queryScoped queryDistinct queryArrows

theorem step {outer : Child} {before after : Config (BinderCore.keys built.rules) [] () D.Ty}
    (reached : Runs D (NormalProgram.program built D) supply (Config.initial spaces query) before)
    (known : Invariant built D outer before)
    (edge : SourceLanguage.Step D (NormalProgram.program built D) supply before after) :
    Invariant built D outer after := by
  cases edge with
  | move world nextWorld current rest children live moved =>
      intro child member alive
      rcases Multiset.mem_add.mp member with made | kept
      · have runtimeScope := scoping_reachable spaces query
          (NormalProgramFormation.equations_formed built D) queryScoped queryDistinct queryArrows
          _ reached current (Multiset.mem_cons_self _ _)
        exact move built D supply (known current (Multiset.mem_cons_self _ _) live)
          (fresh_of_scoping built D runtimeScope) moved child made alive
      · exact known child (Multiset.mem_cons_of_mem kept) alive

end Reached

theorem runs {n : Nat} (term : Tower.Tm n)
    {after : Config (BinderCore.keys built.rules) [] () D.Ty}
    (executed : Runs D (NormalProgram.program built D) supply
      (Config.initial (fun _ => 0) (NormalScanner.query built (encodeTm term))) after) :
    Invariant built D ⟨n, term⟩ after := by
  induction executed with
  | refl =>
      intro branch member _
      rw [Multiset.mem_singleton.mp member]
      exact NormalScannerCertificates.initial built D term
  | tail earlier edge ih =>
      exact step built D supply (fun _ => 0) (NormalScanner.query built (encodeTm term))
        (NormalScanner.query_scoped built _) (NormalScanner.query_distinct built _)
        (NormalScanner.query_arrows built _) earlier ih edge

theorem finished_reflects {n : Nat} (term : Tower.Tm n)
    {after : Config (BinderCore.keys built.rules) [] () D.Ty}
    (executed : Runs D (NormalProgram.program built D) supply
      (Config.initial (fun _ => 0) (NormalScanner.query built (encodeTm term))) after)
    {branch : Branch (BinderCore.keys built.rules) [] () D.Ty}
    (member : branch ∈ after.branches) (finished : branch.Finished (D := D)) (live : Solvable branch.store) :
    NormalStructure.Normal built term :=
  NormalScannerCertificates.finished_normal built D (runs built D supply term executed branch member live) finished

theorem normal_scan_iff {n : Nat} (term : Tower.Tm n) :
    (∃ after branch,
      Runs D (NormalProgram.program built D) supply
        (Config.initial (fun _ => 0) (NormalScanner.query built (encodeTm term))) after ∧
      branch ∈ after.branches ∧ branch.Finished (D := D) ∧ Solvable branch.store ∧
      csym NormalScanner.markerTag ∈ branch.answer (D := D)) ↔ NormalStructure.Normal built term := by
  constructor
  · rintro ⟨after, branch, executed, member, finished, live, _⟩
    exact finished_reflects built D supply term executed member finished live
  · exact NormalScannerExecution.normal_executes built D supply term

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerReflection

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerReflection.move
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerReflection.normal_scan_iff
