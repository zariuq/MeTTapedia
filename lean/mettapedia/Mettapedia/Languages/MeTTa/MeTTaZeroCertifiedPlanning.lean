import Mettapedia.GSLT.Core.CertifiedPlanning
import Mettapedia.Languages.MeTTa.MeTTaZeroLanguageAdequacy

/-!
# Certified implementation planning for query-first MeTTa Zero

The query-first Zero semantics names an exact occurrence-bag observation, and
the authored five-field language has a generic interpreter proved adequate for
that observation.  This module connects those facts to the reusable planning
theory.

The exact-bag observer may be weakened explicitly to support, but the reverse
map is impossible.  Alternative implementations may be selected per public
entry point, with a semantic reference fallback and a one-entry finite support
certificate.  Changing availability information for an unrelated entry point
therefore leaves an existing compiled choice unchanged.
-/

namespace Mettapedia.Languages.MeTTa.MeTTaZeroCertifiedPlanning

open Mettapedia.GSLT
open Mettapedia.Languages.MeTTa.MeTTaZero
open Mettapedia.Languages.MeTTa.MeTTaZeroLanguageAdequacy
open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Exact observations and their lawful quotient -/

/-- The occurrence-bag to support projection, with its information loss named
in the type. -/
def exactToSupport :
    ObservationRefinement (fun _ : Unit => Multiset Pattern)
      (fun _ : Unit => Finset Pattern) where
  forget := fun _ answers => support answers

/-- The authored generic interpreter remains certified when a consumer asks
only which answers occur. -/
noncomputable def authoredSupportRealization (model : Model) :
    SimpleRealization (KernelRequest model) (Multiset Pattern)
      (Finset Pattern) :=
  exactToSupport.mapRealization (authoredRealization model)

/-- Support observation of an authored execution is exactly the support of
the semantic occurrence bag. -/
theorem authoredSupportRealization_observes (model : Model)
    (request : KernelRequest model) :
    (authoredSupportRealization model).observeArtifact ()
        ((authoredSupportRealization model).compile () request) =
      support (semanticAnswers request) :=
  (authoredSupportRealization model).adequate () request

/-- Negative: the support quotient cannot be promoted back to exact
multiplicity by supplying a decoder. -/
theorem no_exact_multiplicity_recovery_from_support (answer : Pattern) :
    ¬ ∃ recover : Finset Pattern → Nat,
        ∀ answers : Multiset Pattern,
          recover (exactToSupport.forget () answers) =
            multiplicity answer answers :=
  no_multiplicity_observer_from_support answer

/-! ## Comparing the semantic and authored routes -/

/-- The semantic reference route retains the request as its artifact.  It is
an executable specification, not a claim about an optimized backend. -/
def semanticReferenceRealization (model : Model) :
    SimpleRealization (KernelRequest model) (KernelRequest model)
      (Multiset Pattern) :=
  Realization.identity (fun _ request => semanticAnswers request)

/-- The authored five-field interpreter and the semantic reference are joined
by an exact occurrence-bag 2-cell despite producing unrelated artifacts. -/
noncomputable def authoredReferenceCell (model : Model) :
    ObservationCell (authoredRealization model)
      (semanticReferenceRealization model) :=
  ObservationCell.ofSourceAgreement _ _ (by intros; rfl)

/-- The exact 2-cell descends through the support quotient. -/
noncomputable def authoredReferenceSupportCell (model : Model) :
    ObservationCell (exactToSupport.mapRealization (authoredRealization model))
      (exactToSupport.mapRealization (semanticReferenceRealization model)) :=
  (authoredReferenceCell model).mapObservation _ _ exactToSupport

/-! ## Entry-point-local generated plans -/

/-- The two public Zero operations are independent plan dependencies. -/
inductive EntryPoint where
  | query
  | evaluate
deriving DecidableEq, Repr

/-- Identify the one entry point a request invokes. -/
def entryPoint {model : Model} : KernelRequest model → EntryPoint
  | .query .. => .query
  | .evaluate .. => .evaluate

/-- A generated artifact is either the exact bag emitted by the authored
interpreter or the original request retained for the semantic fallback. -/
abbrev PlannedArtifact (model : Model) :=
  Multiset Pattern ⊕ KernelRequest model

/-- Compile one request according to the availability bit for its entry point.
The plan's support is exactly that singleton bit. -/
noncomputable def requestPlan (model : Model) (request : KernelRequest model) :
    FinitelySupportedPlan EntryPoint Bool (PlannedArtifact model) :=
  (FinitelySupportedPlan.read (Value := Bool) (entryPoint request)).map
    fun available =>
      if available = true then
        .inl (executeAuthored request)
      else
        .inr request

@[simp] theorem requestPlan_support (model : Model)
    (request : KernelRequest model) :
    (requestPlan model request).support = {entryPoint request} :=
  rfl

/-- Request-local planning is a certified realization for every availability
environment.  Backend selection changes artifacts, never Zero's exact answer
bag. -/
noncomputable def plannedRealization (model : Model) :
    PlannedRealization (Declaration := EntryPoint) Bool
      (fun _ : Unit => KernelRequest model)
      (fun _ : Unit => PlannedArtifact model)
      (fun _ : Unit => Multiset Pattern) where
  plan := fun _ request => requestPlan model request
  observeSource := fun _ request => semanticAnswers request
  observeArtifact := fun _ => Sum.elim id semanticAnswers
  adequate := by
    intro _ request environment
    change Sum.elim id semanticAnswers
        (if environment (entryPoint request) = true then
          .inl (executeAuthored request)
        else
          .inr request) = semanticAnswers request
    by_cases available : environment (entryPoint request) = true
    · rw [if_pos available]
      exact (authoredRealization model).adequate () request
    · rw [if_neg available]
      rfl

/-- Freezing any availability environment yields an ordinary exact-bag
realization suitable for composition with later certified lowering stages. -/
noncomputable def realizationAt (model : Model)
    (availability : EntryPoint → Bool) :
    SimpleRealization (KernelRequest model) (PlannedArtifact model)
      (Multiset Pattern) :=
  (plannedRealization model).freeze availability

/-- Positive: every generated choice, including a fallback choice, preserves
the exact semantic occurrence bag. -/
theorem realizationAt_observes_exactly (model : Model)
    (availability : EntryPoint → Bool) (request : KernelRequest model) :
    (realizationAt model availability).observeArtifact ()
        ((realizationAt model availability).compile () request) =
      semanticAnswers request :=
  by
    simpa [realizationAt, plannedRealization, PlannedRealization.freeze] using
      (realizationAt model availability).adequate () request

/-- Changing only evaluation availability cannot invalidate a query plan. -/
theorem query_plan_stable_under_evaluation_change (model : Model)
    (space : model.Space) (spaceTerm pattern template : Pattern)
    {first second : EntryPoint → Bool}
    (querySame : first .query = second .query) :
    (requestPlan model (.query space spaceTerm pattern template)).run first =
      (requestPlan model (.query space spaceTerm pattern template)).run second := by
  apply (requestPlan model
    (.query space spaceTerm pattern template)).stable
  intro dependency member
  simp only [requestPlan_support, Finset.mem_singleton] at member
  subst dependency
  exact querySame

/-- Negative: changing the availability bit inside the support genuinely
changes the selected artifact branch.  Such a revision must invalidate the
cached choice. -/
theorem query_plan_changes_at_supported_dependency (model : Model)
    (space : model.Space) (spaceTerm pattern template : Pattern) :
    (requestPlan model (.query space spaceTerm pattern template)).run
        (fun _ => false) ≠
      (requestPlan model (.query space spaceTerm pattern template)).run
        (fun dependency => dependency == .query) := by
  change
    (Sum.inr (.query space spaceTerm pattern template) : PlannedArtifact model) ≠
      Sum.inl (executeAuthored (.query space spaceTerm pattern template))
  intro equal
  cases equal

/-- Negative admission canary: disabling evaluation selects the reference
fallback rather than attempting the authored branch. -/
theorem disabled_evaluation_selects_fallback (model : Model)
    (space : model.Space) (spaceTerm subject : Pattern) :
    (requestPlan model (.evaluate space spaceTerm subject)).run
        (fun _ => false) =
      .inr (.evaluate space spaceTerm subject) := by
  rfl

end Mettapedia.Languages.MeTTa.MeTTaZeroCertifiedPlanning
