import Mettapedia.Machines.ObserverLicence.PortfolioBridge

/-!
# From a classified admission key to the operational host law

An analyser must justify quietness of the regions it labels quiet and match
the observer demand. Those are local analysis obligations, not an assumed
whole-run equivalence. The computed positive-demand admission then inherits
the existing host-run refinement and actual witness publication. Validated
zero demand is the separate no-generator-execution case.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ObserverLicence.AdmissionSoundness

open Mettapedia.GSLT.Dynamics.IterativeDeepeningWitness (IsAnswer)

variable {Store State Answer Event HostState Result : Type}

structure Analyser (system : PortfolioReach.System Store State Answer Event) where
  key : Store → Nat → State → LicenceKey
  quietCertificate : ∀ store demand root,
    (key store demand root).producer.quiet = true → PortfolioReach.Quiet system store root
  demandCertificate : ∀ store demand root,
    (requirements (key store demand root).order (key store demand root).consumer).demand = some demand

/-- A concrete analyser for the explicitly pure search-space interface. This
does not classify an arbitrary native program as pure. -/
def pureSpaceAnalyser (space : Mettapedia.GSLT.Dynamics.IterativeDeepeningWitness.Space State Answer) :
    Analyser (PortfolioReach.System.ofSpace (σ := Store) (E := Event) space) where
  key _ demand _ := ⟨.bag, .pure, .select demand, true, true⟩
  quietCertificate store _ root _ := PortfolioReach.ofSpace_quiet space store root
  demandCertificate _ demand _ := by simp [requirements]

def Permitted {system : PortfolioReach.System Store State Answer Event} (analysis : Analyser system)
    (store : Store) (demand : Nat) (root : State) : Prop :=
  0 < demand ∧ admission (analysis.key store demand root) .witnessPortfolio = true

theorem pure_space_has_positive_admissions
    (space : Mettapedia.GSLT.Dynamics.IterativeDeepeningWitness.Space State Answer)
    (store : Store) (demand : Nat) (root : State) (positive : 0 < demand) :
    Permitted (pureSpaceAnalyser (Event := Event) space) store demand root := by
  refine ⟨positive, ?_⟩
  cases demand with
  | zero => omega
  | succ demand => rfl

theorem permitted_region_is_quiet {system : PortfolioReach.System Store State Answer Event}
    (analysis : Analyser system) (store : Store) (demand : Nat) (root : State)
    (permitted : Permitted analysis store demand root) : PortfolioReach.Quiet system store root := by
  have positive : 0 < demand := permitted.1
  have nonzero : (analysis.key store demand root).consumer ≠ .select 0 := by
    intro zero
    have counted := analysis.demandCertificate store demand root
    rw [zero] at counted
    simp only [requirements, Option.some.injEq] at counted
    omega
  have classified := nonzero_portfolio_requires_quiet (analysis.key store demand root).order
    (analysis.key store demand root).producer (analysis.key store demand root).consumer
    (analysis.key store demand root).innerAggregatesComplete (analysis.key store demand root).boundaryLicensed
    nonzero permitted.2
  exact analysis.quietCertificate store demand root classified.1

theorem classified_admission_preserves_host_runs
    (system : PortfolioReach.System Store State Answer Event)
    (host : PortfolioReach.Host Store HostState State Answer Event Result)
    (analysis : Analyser system)
    {before after : PortfolioReach.HostState Store Event HostState}
    (run : Relation.ReflTransGen (PortfolioReach.HostStep system host
      (PortfolioReach.machineServes system (Permitted analysis))) before after) :
    Relation.ReflTransGen (PortfolioReach.HostStep system host
      (PortfolioReach.specServes system (Permitted analysis))) before after :=
  PortfolioReach.machine_runs_refine_spec system host (Permitted analysis)
    (permitted_region_is_quiet analysis) run

theorem classified_once_really_publishes
    (system : PortfolioReach.System Store State Answer Event) (analysis : Analyser system)
    (store : Store) (root : State) (permitted : Permitted analysis store 1 root)
    {value : Answer} (answer : IsAnswer (system.space store) root value) (log : List Event) :
    ∃ rounds witness,
      PortfolioReach.batch (PortfolioReach.portfolio system root 1
        (PortfolioReach.rounds (PortfolioReach.doubling 1) rounds) store log) = some [witness] ∧
      IsAnswer (system.space store) root witness ∧
      (PortfolioReach.portfolio system root 1
        (PortfolioReach.rounds (PortfolioReach.doubling 1) rounds) store log).world = ⟨store, log, none⟩ :=
  PortfolioReach.once_publishes system (permitted_region_is_quiet analysis store 1 root permitted) answer log

end Mettapedia.Machines.ObserverLicence.AdmissionSoundness
