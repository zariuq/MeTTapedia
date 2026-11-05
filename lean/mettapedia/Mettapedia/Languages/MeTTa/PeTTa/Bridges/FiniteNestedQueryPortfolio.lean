import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQueryDriver
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PureCallPortfolio

/-!
# Observation-qualified finite insertion drivers

Source dispatch is certified from the selected actual clause. Each attempt
revalidates current binding and read domains, then runs the private phase
worker. Exhaustion and failed validation restore the exact entrance and use
reference execution. Exact evaluator pages decline: phase allowance is not
source fuel, and no native publication or profitability claim is made here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQueryPortfolio

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.GSLT.LanguageDef.FiniteEnvironmentCompilation
open Mettapedia.GSLT.Dynamics ConjunctiveRegionProvenance ObservationQualified
open FlatQueryRowCodec FlatQueryDomainInvariant FiniteNestedQueryDriver
open Eval SpaceSemantics NamedSpaces
open DeclarativeSpec (Runs)

variable {Value Regime : Type} [DecidableEq Value]

theorem source_meaning {codec : Codec Value} {names : Inventory String} {program : Program}
    {queries : List (Query codec names)} {head : FlatQueryOutputDomain.Head codec names}
    {driver spaceName temporary progress : String} {target : Handle}
    (certificate : Certificate program queries head driver spaceName temporary progress target)
    (domain : Finset Value) (constants : ∀ value, Cell.constant value ∈ head.2.cells → value ∈ domain)
    (caller : Subst) (location : Subst.lookup caller spaceName = some (Effects.handleValue target))
    (allowance : Nat) (before after : Effects.State) (counts : List Nat)
    (bound : BindingsInDomain codec names domain (callee spaceName target)) (valid : ViewsInDomain domain queries before)
    (completed : FiniteNestedQueryIteration.iterate queries head target (callee spaceName target) allowance before = some (after, counts)) :
    PureCallPortfolio.sourceMeaning program caller (call driver spaceName) before =
      {PureCallPortfolio.complete after (Effects.boolean true)} := by
  have returned := certificate.calls caller before after location
    (body_returns certificate domain constants bound allowance before after counts valid completed)
  ext observed
  change Runs program {state := before, control := .evaluate caller (call driver spaceName)}
    (.complete observed.state observed.answers observed.input observed.output) ↔ _
  rw [pure_returns_derivation_iff program caller before after (call driver spaceName) (Effects.boolean true) returned]
  cases observed
  simp [PureCallPortfolio.complete, PureCallPortfolio.Completed.mk.injEq]

def region {codec : Codec Value} {names : Inventory String} {program : Program}
    {queries : List (Query codec names)} {head : FlatQueryOutputDomain.Head codec names}
    {driver spaceName temporary progress : String} {target : Handle}
    (regime : Regime) (certificate : Certificate program queries head driver spaceName temporary progress target)
    (domain : Finset Value) (constants : ∀ value, Cell.constant value ∈ head.2.cells → value ∈ domain)
    (caller : Subst) (location : Subst.lookup caller spaceName = some (Effects.handleValue target)) (allowance : Nat) :
    CertifiedRegion (PureCallPortfolio.boundary program caller (call driver spaceName)) Regime where
  regime := regime
  Artifact := PureCallPortfolio.Completed
  attempt before :=
    if validateBindings codec names domain (callee spaceName target) && validateViews domain queries before then
      match FiniteNestedQueryIteration.iterate queries head target (callee spaceName target) allowance before with
      | none => .declined before
      | some receipt => .committed (PureCallPortfolio.complete receipt.1 (Effects.boolean true))
    else .declined before
  decode observed := {observed}
  restores before restored declined := by
    dsimp only at declined
    split at declined
    · split at declined
      · exact (PartialRegionPlan.Attempt.declined.inj declined).symm
      · cases declined
    · exact (PartialRegionPlan.Attempt.declined.inj declined).symm
  exact before observed committed := by
    split at committed
    next valid =>
      obtain ⟨bound, views⟩ := Bool.and_eq_true_iff.mp valid
      split at committed
      · cases committed
      next receipt completed =>
        cases PartialRegionPlan.Attempt.committed.inj committed
        exact (source_meaning certificate domain constants caller location allowance before receipt.1 receipt.2
          ((validateBindings_iff codec names domain _).mp bound) ((validateViews_iff domain queries before).mp views) completed).symm
    next refused => cases committed

def classify {codec : Codec Value} {names : Inventory String} (observation : PureCallExtraction.Observation)
    (regime : Regime) (program : Program) (queries : List (Query codec names)) (head : FlatQueryOutputDomain.Head codec names)
    (driver spaceName temporary progress : String) (target : Handle) (domain : Finset Value)
    (constants : ∀ value, Cell.constant value ∈ head.2.cells → value ∈ domain)
    (caller : Subst) (location : Subst.lookup caller spaceName = some (Effects.handleValue target)) (allowance : Nat) :
    Option (CertifiedRegion (PureCallPortfolio.boundary program caller (call driver spaceName)) Regime) :=
  match observation with
  | .exactPage => none
  | .completedResult => (prepare program queries head driver spaceName temporary progress target).map
      (fun certificate => region regime certificate domain constants caller location allowance)

theorem exact_page_refuses {codec : Codec Value} {names : Inventory String}
    (regime : Regime) (program : Program) (queries : List (Query codec names)) (head : FlatQueryOutputDomain.Head codec names)
    (driver spaceName temporary progress : String) (target : Handle) (domain : Finset Value)
    (constants : ∀ value, Cell.constant value ∈ head.2.cells → value ∈ domain)
    (caller : Subst) (location : Subst.lookup caller spaceName = some (Effects.handleValue target)) (allowance : Nat) :
    classify .exactPage regime program queries head driver spaceName temporary progress target domain constants caller location allowance = none := rfl

theorem execute_exact {codec : Codec Value} {names : Inventory String} {program : Program}
    {queries : List (Query codec names)} {head : FlatQueryOutputDomain.Head codec names}
    {driver spaceName temporary progress : String} {target : Handle}
    (regime : Regime) (certificate : Certificate program queries head driver spaceName temporary progress target)
    (domain : Finset Value) (constants : ∀ value, Cell.constant value ∈ head.2.cells → value ∈ domain)
    (caller : Subst) (location : Subst.lookup caller spaceName = some (Effects.handleValue target)) (allowance : Nat) (before : Effects.State) :
    (region regime certificate domain constants caller location allowance).execute before =
      PureCallPortfolio.sourceMeaning program caller (call driver spaceName) before :=
  congrFun (region regime certificate domain constants caller location allowance).execute_eq_reference before

theorem sufficient_allowance_commits {codec : Codec Value} {names : Inventory String} {program : Program}
    {queries : List (Query codec names)} {head : FlatQueryOutputDomain.Head codec names}
    {driver spaceName temporary progress : String} {target : Handle}
    (regime : Regime) (certificate : Certificate program queries head driver spaceName temporary progress target)
    (domain : Finset Value) (constants : ∀ value, Cell.constant value ∈ head.2.cells → value ∈ domain)
    (caller : Subst) (location : Subst.lookup caller spaceName = some (Effects.handleValue target))
    (data : FiniteNestedQueryCompletion.DataHead head)
    (covered : FiniteNestedQueryCompletion.Covered queries (callee spaceName target))
    (bound : BindingsInDomain codec names domain (callee spaceName target))
    (before : Effects.State) (rows : List Atom) (valid : ViewsInDomain domain queries before)
    (snapshot : before.read target = some rows) :
    ∃ after, (region regime certificate domain constants caller location (domain.card ^ head.2.cells.length + 1)).attempt before =
      .committed (PureCallPortfolio.complete after (Effects.boolean true)) := by
  obtain ⟨after, counts, completed⟩ := FiniteNestedQueryIteration.catalogue_allowance domain queries head data constants target
    (callee spaceName target) before rows bound valid covered snapshot
  refine ⟨after, ?_⟩
  simp only [region, (validateBindings_iff codec names domain _).mpr bound,
    (validateViews_iff domain queries before).mpr valid, Bool.and_self, ↓reduceIte, completed]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.FiniteNestedQueryPortfolio
