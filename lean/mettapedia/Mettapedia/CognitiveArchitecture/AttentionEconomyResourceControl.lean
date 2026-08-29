import Mettapedia.CognitiveArchitecture.AttentionEconomy
import Mettapedia.GSLT.Core.ResourceAwareControl

/-!
# Attention-economy resource-control bridge

An economic attention network supplies two independent resource accounts to
generic observation control: a short-term fund and a long-term fund.  Exact
joint funding is their product.  Projection of a joint certificate recovers
an exact certificate for each instrument, while funding one instrument alone
cannot authorize demand on the other.

This bridge is intentionally one-way.  Generic resource control does not
depend on ECAN terminology, and an attention account does not create semantic
execution or scheduling authority.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CognitiveArchitecture.AttentionEconomyResourceControl

open Mettapedia.CognitiveArchitecture.AttentionEconomy
open Mettapedia.GSLT.Core.ResourceAwareControl

universe uItem uActor uCurrency

/-- The exact resource account exposed by an attention economy. -/
abbrev ImportanceAccount (Actor : Type uActor) (Currency : Type uCurrency)
    [Zero Currency] :=
  Fund .shortTerm Actor Currency × Fund .longTerm Actor Currency

/-- Pair independently certified STI and LTI decompositions over the same
occurrence batch. -/
def pairFunding {Item : Type uItem} {Actor : Type uActor}
    {Currency : Type uCurrency} [AddCommMonoid Currency]
    {batch : List Item}
    {shortDemand : Item → Fund .shortTerm Actor Currency}
    {longDemand : Item → Fund .longTerm Actor Currency}
    {shortSource : Fund .shortTerm Actor Currency}
    {longSource : Fund .longTerm Actor Currency}
    (short : BatchSeparation _ shortDemand shortSource batch)
    (long : BatchSeparation _ longDemand longSource batch) :
    BatchSeparation (ImportanceAccount Actor Currency)
      (fun item => (shortDemand item, longDemand item))
      (shortSource, longSource) batch :=
  short.pair long

/-- Forget the LTI coordinate of a paired account without disturbing its STI
certificate. -/
def projectShortTerm {Item : Type uItem} {Actor : Type uActor}
    {Currency : Type uCurrency} [AddCommMonoid Currency]
    {batch : List Item}
    {demand : Item → ImportanceAccount Actor Currency}
    {source : ImportanceAccount Actor Currency}
    (joint : BatchSeparation _ demand source batch) :
    BatchSeparation (Fund .shortTerm Actor Currency)
      (fun item => (demand item).1) source.1 batch :=
  joint.map (AddMonoidHom.fst _ _)

/-- Forget the STI coordinate of a paired account without disturbing its LTI
certificate. -/
def projectLongTerm {Item : Type uItem} {Actor : Type uActor}
    {Currency : Type uCurrency} [AddCommMonoid Currency]
    {batch : List Item}
    {demand : Item → ImportanceAccount Actor Currency}
    {source : ImportanceAccount Actor Currency}
    (joint : BatchSeparation _ demand source batch) :
    BatchSeparation (Fund .longTerm Actor Currency)
      (fun item => (demand item).2) source.2 batch :=
  joint.map (AddMonoidHom.snd _ _)

/-- Read the two circulating totals as two coordinates.  They are not summed
into one scalar budget. -/
def fundTotals {Actor : Type uActor} {Currency : Type uCurrency}
    [AddCommMonoid Currency] :
    ImportanceAccount Actor Currency →+ Currency × Currency :=
  AddMonoidHom.prodMap Fund.totalHom Fund.totalHom

/-- Exact joint funding projects to the exact pair of currency totals. -/
def projectTotals {Item : Type uItem} {Actor : Type uActor}
    {Currency : Type uCurrency} [AddCommMonoid Currency]
    {batch : List Item}
    {demand : Item → ImportanceAccount Actor Currency}
    {source : ImportanceAccount Actor Currency}
    (joint : BatchSeparation _ demand source batch) :
    BatchSeparation (Currency × Currency)
      (fun item =>
        (Fund.total (demand item).1, Fund.total (demand item).2))
      (Fund.total source.1, Fund.total source.2) batch :=
  joint.map fundTotals

theorem pairFunding_short_frame_exact
    {Item : Type uItem} {Actor : Type uActor}
    {Currency : Type uCurrency} [AddCommMonoid Currency]
    {batch : List Item}
    {shortDemand : Item → Fund .shortTerm Actor Currency}
    {longDemand : Item → Fund .longTerm Actor Currency}
    {shortSource : Fund .shortTerm Actor Currency}
    {longSource : Fund .longTerm Actor Currency}
    (short : BatchSeparation _ shortDemand shortSource batch)
    (long : BatchSeparation _ longDemand longSource batch) :
    (projectShortTerm (pairFunding short long)).frame = short.frame :=
  rfl

theorem pairFunding_long_frame_exact
    {Item : Type uItem} {Actor : Type uActor}
    {Currency : Type uCurrency} [AddCommMonoid Currency]
    {batch : List Item}
    {shortDemand : Item → Fund .shortTerm Actor Currency}
    {longDemand : Item → Fund .longTerm Actor Currency}
    {shortSource : Fund .shortTerm Actor Currency}
    {longSource : Fund .longTerm Actor Currency}
    (short : BatchSeparation _ shortDemand shortSource batch)
    (long : BatchSeparation _ longDemand longSource batch) :
    (projectLongTerm (pairFunding short long)).frame = long.frame :=
  rfl

/-! ## Positive and negative controls -/

namespace Canary

def shortFund (amount : ℕ) : Fund .shortTerm Unit ℕ where
  balances := Finsupp.single () amount

def longFund (amount : ℕ) : Fund .longTerm Unit ℕ where
  balances := Finsupp.single () amount

def shortDemand (_ : Unit) : Fund .shortTerm Unit ℕ := shortFund 1

def longDemand (_ : Unit) : Fund .longTerm Unit ℕ := longFund 2

def shortSeparation :
    BatchSeparation _ shortDemand (shortFund 1) [()] where
  frame := 0
  source_eq := by
    ext
    simp [shortDemand, shortFund, batchDemand]

def longSeparation :
    BatchSeparation _ longDemand (longFund 2) [()] where
  frame := 0
  source_eq := by
    ext
    simp [longDemand, longFund, batchDemand]

def jointSeparation :
    BatchSeparation (ImportanceAccount Unit ℕ)
      (fun item => (shortDemand item, longDemand item))
      (shortFund 1, longFund 2) [()] :=
  pairFunding shortSeparation longSeparation

/-- Positive control: joint certification retains both independent residual
funds and their two exact totals. -/
theorem joint_funding_projects_exactly :
    (projectShortTerm jointSeparation).frame = shortSeparation.frame ∧
    (projectLongTerm jointSeparation).frame = longSeparation.frame ∧
    (projectTotals jointSeparation).frame = (0, 0) := by
  exact ⟨rfl, rfl, rfl⟩

/-- One unit of LTI cannot fund a two-unit LTI demand, regardless of the STI
account. -/
theorem insufficient_longTerm_refuses_separation :
    ¬ Nonempty
      (BatchSeparation (Fund .longTerm Unit ℕ)
        longDemand (longFund 1) [()]) := by
  rintro ⟨separation⟩
  have totalEquation := congrArg Fund.total
    separation.source_eq
  rw [Fund.total_add] at totalEquation
  simp [longDemand, longFund, batchDemand, Fund.total,
    Finsupp.sum_single_index] at totalEquation
  omega

/-- Consequently, a valid STI certificate cannot be promoted to a joint
attention certificate when the LTI side is unfunded. -/
theorem shortTerm_funding_does_not_grant_joint_funding :
    Nonempty (BatchSeparation _ shortDemand (shortFund 1) [()]) ∧
    ¬ Nonempty
      (BatchSeparation (ImportanceAccount Unit ℕ)
        (fun item => (shortDemand item, longDemand item))
        (shortFund 1, longFund 1) [()]) := by
  constructor
  · exact ⟨shortSeparation⟩
  · rintro ⟨joint⟩
    exact insufficient_longTerm_refuses_separation
      ⟨projectLongTerm joint⟩

end Canary

/-! ## Axiom audit -/

#print axioms pairFunding_short_frame_exact
#print axioms pairFunding_long_frame_exact
#print axioms Canary.joint_funding_projects_exactly
#print axioms Canary.insufficient_longTerm_refuses_separation
#print axioms Canary.shortTerm_funding_does_not_grant_joint_funding

end Mettapedia.CognitiveArchitecture.AttentionEconomyResourceControl
