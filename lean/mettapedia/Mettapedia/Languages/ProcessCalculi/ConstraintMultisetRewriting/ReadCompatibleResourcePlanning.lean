import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PositiveResourceSchedules
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadPortPushouts

/-!
# Resource planning with source-compatible read ports

The existing resource semantics is indexed by guard-free source rules whose
tells hold under one fixed shared model. Each instance records a finite read
prototype and proves that every source read port has its expected value under
that same model. Prototype identities describe per-firing read alias classes;
they need not be occupied identities of the eventual implementation.

This refines the instance carrier of `ResourceInteraction.System`. It adds
no transition calculus. Its observation is a complete sequential resource
bag, not physical identity or a quotient of concurrent traces.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadCompatibleResourcePlanning

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.GSLT.Causality
open PositiveResourceProjection (realized readFootprint)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  (A : SubstitutionAction T S) (assignment : S) (label : O → T)

structure AdmittedRule where
  rule : RuleInstance T
  noChecks : rule.checks = []
  tells : A.Models assignment rule.tell

structure ReadPlan (rule : RuleInstance T) where
  prototype : List O
  compatible : List.Forall₂
    (fun pattern occurrence => A.apply assignment pattern = realized A assignment label occurrence)
    rule.read prototype

namespace ReadPlan

variable {A assignment label} {rule : RuleInstance T}

def selection (plan : ReadPlan A assignment label rule) : Selection O := ⟨[], plan.prototype, []⟩

def portClass (plan : ReadPlan A assignment label rule) (port : Fin plan.prototype.length) :
    ReadPortPushouts.Rows plan.prototype.toFinset :=
  ReadPortPushouts.readQuotient plan.selection ⟨port⟩

theorem portClass_value (plan : ReadPlan A assignment label rule) (port : Fin plan.prototype.length) :
    (plan.portClass port).val = plan.prototype.get port := rfl

end ReadPlan

def resources : ResourceInteraction.System.{uT, max uT uO} T where
  Site := ULift.{uO} (AdmittedRule A assignment)
  Instance source := ULift.{uT} (ReadPlan A assignment label source.down.rule)
  consume := fun {source} _ => (source.down.rule.take.map (A.apply assignment) : Multiset T)
  read := fun instance_ => readFootprint A assignment label instance_.down.selection
  produce := fun {source} _ => (source.down.rule.produce.map (A.apply assignment) : Multiset T)

/-- The allocation realizes prototype classes by distinct physical rows.
Only read ports may alias; consuming ports will be allocated separately. -/
structure ReadRealization {rule : RuleInstance T} (plan : ReadPlan A assignment label rule)
    (actual : Selection O) where
  embedding : ReadPortPushouts.Rows plan.prototype.toFinset → O
  injective : Function.Injective embedding
  ports : actual.read = List.ofFn (fun port => embedding (plan.portClass port))
  values : ∀ support, realized A assignment label (embedding support) =
    realized A assignment label support.val

namespace ReadRealization

variable {A assignment label} {rule : RuleInstance T}
  {plan : ReadPlan A assignment label rule} {actual : Selection O}

theorem read_length (realization : ReadRealization A assignment label plan actual) :
    actual.read.length = plan.prototype.length := by rw [realization.ports, List.length_ofFn]

/-- A repeated read port and a distinct equal-valued read row remain
different cases: the equivalence compares physical prototype identities. -/
theorem alias_iff (realization : ReadRealization A assignment label plan actual)
    (first second : Fin plan.prototype.length) :
    realization.embedding (plan.portClass first) = realization.embedding (plan.portClass second) ↔
      plan.prototype.get first = plan.prototype.get second := by
  constructor
  · intro same
    exact congrArg Subtype.val (realization.injective same)
  · intro same
    exact congrArg realization.embedding (Subtype.ext same)

end ReadRealization
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ReadCompatibleResourcePlanning
