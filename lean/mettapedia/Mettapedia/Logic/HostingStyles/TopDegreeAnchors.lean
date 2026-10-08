import Mettapedia.Logic.HostingStyles.TermsAsDerivations
import Mettapedia.Logic.HostingStyles.UnionExhausting
import Mettapedia.Logic.HostingStyles.AuthoredCertificates
import Mettapedia.Languages.TuringMachine.UniversalHosting
import Mettapedia.GSLT.Dedukti.TableEvaluator

/-!
# Universal hosts, as statements of one form

`Universality` defines `HostsEvery host sources`: every theory of a class has
a hosting map into the host.  This module states the hosts built for
computation in that form, next to the hosts for proof systems that are
already there.

| Host | Class it hosts | Statement |
|---|---|---|
| the universal Turing-machine theory | every machine on its configurations | `universalTheory_hostsEvery_machineTheory` |
| the rule-table evaluator | the running presentation of every theory given by a table | `tableEvaluator_hostsEvery` |
| the rule-table evaluator | the same theories as members of the common class | `tableEvaluator_hostsEvery_calculi` |
| the union with componentwise reduction | every member of a family in the common class | existing `sumReducing_hostsEvery` |
| the framework over the union | every member of a family of proof systems, with nothing added | existing `universalFramework_hostsExhaustively` |

The hosting relation between theories is a preorder (`HostedBy.refl`,
`HostedBy.trans`); a host of a class is an upper bound of the class in it.

## Limits, each proved

* A theory without reduction hosts no calculus that has a step
  (`static_not_hosting_rewriting`): not the framework with rules as constants
  (`framework_not_hosting_rewriting`).  A host for proof systems kept apart is
  not thereby a host for computation.
* The rule-table evaluator is strictly above every orthogonal theory given by
  a table (existing `orthogonal_strictly_below`) and does not host a mutable
  space (existing `space_not_hosted_by_tableEvaluator`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory)
open Mettapedia.GSLT.Dedukti
  (Theory Step rewritingTheory RuleTable tableEvaluator loadMap loadMap_hosting)
open Mettapedia.Languages.TuringMachine
  (Machine base universal configurationGSLT intoUniversalTheory intoUniversalTheory_hosting)
open Framework

/-! ## The hosting preorder -/

/-- One theory is hosted by another: there is a hosting map. -/
def HostedBy (source host : ContextTheory.{0}) : Prop :=
  ∃ map : ContextMap source host, map.Hosting

theorem HostedBy.refl (theory : ContextTheory.{0}) : HostedBy theory theory :=
  ⟨ContextMap.id theory, ContextMap.hosting_id theory⟩

theorem HostedBy.trans {first second third : ContextTheory.{0}} (lower : HostedBy first second)
    (upper : HostedBy second third) : HostedBy first third := by
  obtain ⟨lowerMap, lowerHosting⟩ := lower
  obtain ⟨upperMap, upperHosting⟩ := upper
  exact ⟨upperMap.comp lowerMap, upperHosting.comp lowerHosting⟩

/-- A host of a class is an upper bound of the class in the hosting
preorder. -/
theorem hostsEvery_iff (host : ContextTheory.{0}) (sources : ContextTheory.{0} → Prop) :
    HostsEvery host sources ↔ ∀ source, sources source → HostedBy source host :=
  Iff.rfl

/-! ## The universal Turing-machine theory -/

/-- The machines, each on its configurations. -/
def MachineTheory (source : ContextTheory.{0}) : Prop :=
  ∃ machine : Machine, source = (configurationGSLT machine).termsAlone

/-- **The universal Turing-machine theory hosts every machine**, in the
category of theories presented through their contexts. -/
theorem universalTheory_hostsEvery_machineTheory :
    HostsEvery (contextTheory base universal) MachineTheory := by
  rintro source ⟨machine, rfl⟩
  exact ⟨intoUniversalTheory machine, intoUniversalTheory_hosting machine⟩

/-! ## The rule-table evaluator -/

/-- The running presentations of the theories given by a table. -/
def TabularTheory (source : ContextTheory.{0}) : Prop :=
  ∃ (theory : Theory) (table : RuleTable), theory.Tabular table ∧ source = rewritingTheory theory

/-- **The rule-table evaluator hosts the running presentation of every theory
given by a table.** -/
theorem tableEvaluator_hostsEvery : HostsEvery tableEvaluator TabularTheory := by
  rintro source ⟨theory, table, tabular, rfl⟩
  exact ⟨loadMap theory table, loadMap_hosting tabular⟩

/-- The same theories, as members of the common class. -/
def TabularCalculus (source : ContextTheory.{0}) : Prop :=
  ∃ (theory : Theory) (table : RuleTable), theory.Tabular table ∧ source = termTheory theory

theorem tabularCalculus_reducing (source : ContextTheory.{0}) (member : TabularCalculus source) :
    Reducing source := by
  obtain ⟨theory, _, _, rfl⟩ := member
  exact termTheory_reducing theory

/-- **The rule-table evaluator hosts every calculus of the common class that
is given by a table.** -/
theorem tableEvaluator_hostsEvery_calculi : HostsEvery tableEvaluator TabularCalculus := by
  rintro source ⟨theory, table, tabular, rfl⟩
  exact ⟨(loadMap theory table).comp (formedMap theory),
    (loadMap_hosting tabular).comp (formedMap_hosting theory)⟩

/-! ## A host for proof systems is not thereby a host for computation -/

/-- **A theory without reduction hosts no calculus that has a step.** -/
theorem static_not_hosting_rewriting {theory : Theory} {source target : LanguageDef.LF.Term}
    (step : Step theory source target) {host : ContextTheory.{0}} (static : host.Static)
    (map : ContextMap (rewritingTheory theory) host) : ¬ map.Hosting :=
  map.not_hosting_of_step_into_static static (interface := ()) step

/-- In particular the framework with rules as constants hosts no calculus
with a step, whatever its signature. -/
theorem framework_not_hosting_rewriting {theory : Theory} {source target : LanguageDef.LF.Term}
    (step : Step theory source target) {B : Type} (signature : Signature B)
    (map : ContextMap (rewritingTheory theory) (frameworkTheory signature)) : ¬ map.Hosting :=
  static_not_hosting_rewriting step (frameworkTheory_static signature) map

/-- The pure calculus is such a calculus. -/
theorem framework_not_hosting_beta {B : Type} (signature : Signature B)
    (map : ContextMap (rewritingTheory Theory.empty) (frameworkTheory signature)) :
    ¬ map.Hosting :=
  framework_not_hosting_rewriting
    (Mettapedia.GSLT.Dedukti.Step.root (.beta (.srt .type) (.var 0) (.srt .kind))) signature map

#print axioms universalTheory_hostsEvery_machineTheory
#print axioms tableEvaluator_hostsEvery
#print axioms tableEvaluator_hostsEvery_calculi
#print axioms framework_not_hosting_beta

end Mettapedia.Logic.HostingStyles
