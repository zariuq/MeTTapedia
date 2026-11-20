import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalChildViews
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.NormalScannerCoverage

/-!
# Typed parent continuations for scanner reflection

Each pending child bind retains its actual source suffix and the canonical
native child, including its ambient scope. Completed-prefix proofs and root
checks belong to the parent whose scan will resume. The definitions annotate
the existing source stack; they introduce no evaluator or normality test.
Source-move preservation is proved separately.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerStack

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open SourceLanguage SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing
open NormalChildViews (Child Job)

variable {dev : Definitions.Development} (built : Compiled dev)

def copiedField (scope : Nat) (index : Fin 3) : Data (BinderCore.keys built.rules) [] () :=
  instantiate (copyAt (BinderCore.keys built.rules) scope) (NormalScanner.datum built index)

def copiedPattern (scope : Nat) (term : Child) : Data (BinderCore.keys built.rules) [] () :=
  instantiate (copyAt (BinderCore.keys built.rules) scope)
    (NormalScanner.pattern built (NormalScannerGrounding.kind term.2))

def Fields (K : List (Constraint (BinderCore.keys built.rules) [] ())) (term : Child) (scope : Nat) : Prop :=
  ∀ index ∈ (NormalScannerGrounding.kind term.2).fields,
    Determines K (copiedField built scope index) (NormalScannerGrounding.values term.2 index)

theorem Fields.extend {K extra : List (Constraint (BinderCore.keys built.rules) [] ())}
    {term : Child} {scope : Nat} (known : Fields built K term scope) (live : Solvable (K ++ extra)) :
    Fields built (K ++ extra) term scope :=
  fun index inside => NormalScannerGrounding.determines_append built (known index inside) live

theorem Fields.pattern {K : List (Constraint (BinderCore.keys built.rules) [] ())}
    {term : Child} {scope : Nat} (known : Fields built K term scope) (live : Solvable K) :
    Determines K (copiedPattern built scope term) (encodeTm term.2) := by
  refine ⟨live, ?_⟩
  intro X target assignment solved
  simp only [copiedPattern, NormalScanner.instantiate_pattern, NormalScanner.instantiate_nodeAt,
    List.map_map, Function.comp_def]
  rw [NormalScannerGrounding.encode_instance, NormalScanner.include_nodeAt]
  simp only [List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro index inside
  exact (known index inside).2 target assignment solved

variable (D : Discipline MSig [] ())

def copiedChain (scope : Nat) (jobs : List Job) : Comp (BinderCore.keys built.rules) [] () D.Ty :=
  (NormalScannerGrounding.checkChain built jobs).inst (copyAt (BinderCore.keys built.rules) scope)

def childFrame (scope : Nat) (job : Job) (suffix : List Job) :
    Frame (BinderCore.keys built.rules) [] () D.Ty :=
  .bindTo (NormalScanner.site built job.1) (NormalScanner.marker (fam (BinderCore.keys built.rules)))
    (copiedChain built D scope suffix)

inductive Stack (outer : Child) (K : List (Constraint (BinderCore.keys built.rules) [] ())) :
    List (Frame (BinderCore.keys built.rules) [] () D.Ty) → Child → Prop
  | done : Stack outer K [] outer
  | child {parent current : Child} {frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty)}
      (scope : Nat) (checkedJobs : List Job) (job : Job) (suffix : List Job)
      (partition : NormalScannerGrounding.childJobs (NormalScannerGrounding.kind parent.2) =
        checkedJobs ++ job :: suffix)
      (selected : NormalChildViews.child parent.2 job.2 = some current)
      (root : ¬ NormalRootMatching.Redex built parent.2)
      (checked : NormalChildViews.JobsNormal built parent.2 checkedJobs)
      (fields : Fields built K parent scope)
      (outside : Stack outer K frames parent) :
      Stack outer K (childFrame built D scope job suffix :: frames) current

theorem Stack.extend {outer current : Child}
    {K extra : List (Constraint (BinderCore.keys built.rules) [] ())}
    {frames : List (Frame (BinderCore.keys built.rules) [] () D.Ty)}
    (known : Stack built D outer K frames current) (live : Solvable (K ++ extra)) :
    Stack built D outer (K ++ extra) frames current := by
  induction known with
  | done => exact .done
  | child scope checkedJobs job suffix partition selected root checked fields _ ih =>
      exact .child scope checkedJobs job suffix partition selected root checked (Fields.extend built fields live) ih

theorem Stack.empty {outer current : Child}
    {K : List (Constraint (BinderCore.keys built.rules) [] ())}
    (known : Stack built D outer K [] current) : current = outer := by
  cases known
  rfl

theorem job_checked {parent current : Child} (job : Job)
    (selected : NormalChildViews.child parent.2 job.2 = some current)
    (normal : NormalStructure.Normal built current.2) : NormalChildViews.JobNormal built parent.2 job :=
  ⟨current, selected, normal⟩

theorem all_checked_normal (parent : Child) (checkedJobs : List Job)
    (partition : NormalScannerGrounding.childJobs (NormalScannerGrounding.kind parent.2) = checkedJobs)
    (root : ¬ NormalRootMatching.Redex built parent.2)
    (checked : NormalChildViews.JobsNormal built parent.2 checkedJobs) : NormalStructure.Normal built parent.2 := by
  apply NormalStructure.normal_of_parts built parent.2 root
  apply (NormalChildViews.childrenNormal_iff_jobs built parent.2).mpr
  rw [partition]
  exact checked

theorem different_scope_no_empty_stack
    (K : List (Constraint (BinderCore.keys built.rules) [] ())) :
    ¬ Stack built D (⟨1, .var 0⟩ : Child) K [] (⟨2, .var 0⟩ : Child) := by
  intro known
  have same := Stack.empty built D known
  have scopes := congrArg Sigma.fst same
  exact (by decide : (2 : Nat) ≠ 1) scopes

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerStack

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerStack.Fields.pattern
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.NormalScannerStack.Stack.extend
