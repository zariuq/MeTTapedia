import Mettapedia.TypeTheory.ScopedIdentity
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing
import Mettapedia.TypeTheory.Calculi.StagedScopedReflective.RegularTwoSortImage
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Contextual.SyntacticJudgmentalIdentityEliminator
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredDeclarationSignature

/-!
# Scoped-identity status of the current MeTTa type theories

This file separates three questions which are easy to conflate:

* whether typing derivations themselves are retained as data;
* whether an object language has identity formation, reflexivity, and a
  computational eliminator; and
* whether a larger route language may contain a proof-irrelevant checked
  region without collapsing every route.

The results are diagnostic.  They do not select a final Prime identity
theory.  In particular, proposition-valued typing evidence is a useful
authorization boundary, but it cannot also serve as a proof-relevant account
of how a judgment was obtained.
-/

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.ScopedIdentityStatus

open Mettapedia.TypeTheory.ScopedIdentity

universe uEvidence

/-- A representation retains distinct receipts when two unequal inhabitants
can witness the same represented judgment. -/
def HasDistinctReceipts (Evidence : Sort uEvidence) : Prop :=
  Exists fun first : Evidence => Exists fun second : Evidence => first ≠ second

/-- Proposition-valued evidence cannot retain two distinct receipts. -/
theorem prop_has_no_distinct_receipts (Evidence : Prop) :
    Not (HasDistinctReceipts Evidence) := by
  rintro ⟨first, second, distinct⟩
  exact distinct (Subsingleton.elim first second)

namespace TwoSort

open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Context
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Permissive.Typing

/-- The current Pure judgment does contain identity formation and
reflexivity. -/
abbrev IdentityReceipt : Prop :=
  HasType (.nil : Ctx 0) (.refl .u0) (.id .u1 .u0 .u0)

def identityReceipt : IdentityReceipt :=
  .refl_intro (.u0_type (.nil : Ctx 0))

theorem identity_is_inhabited : Nonempty IdentityReceipt :=
  Nonempty.intro identityReceipt

/-- No Pure typing judgment can retain distinct derivation receipts because
`HasType` lives in `Prop`.  This says nothing by itself about whether an
object-level identity type satisfies K. -/
theorem typing_receipts_subsingleton {binders : Nat}
    {context : Ctx binders} {term type : ScopedTerm binders} :
    Subsingleton (HasType context term type) :=
  inferInstance

/-- A falsifiable global criterion: some Pure typing judgment retains two
different derivation receipts. -/
def RetainsSomeTypingRoutes : Prop :=
  Exists fun binders : Nat =>
    Exists fun context : Ctx binders =>
      Exists fun term : ScopedTerm binders =>
        Exists fun type : ScopedTerm binders =>
          HasDistinctReceipts (HasType context term type)

/-- The current Pure judgment provably fails the route-retention criterion. -/
theorem does_not_retain_typing_routes : Not RetainsSomeTypingRoutes := by
  rintro ⟨binders, context, term, type, distinct⟩
  exact prop_has_no_distinct_receipts (HasType context term type) distinct

end TwoSort

namespace StagedCandidate

open Mettapedia.TypeTheory.Calculi.StagedScopedReflective.RegularTwoSortImage

abbrev RegularExactness := NativeRegularExactness

/-- Independently of identity policy, the staged-reflective candidate is not
exact against the separately specified regular two-sort judgment. This theorem
does not establish what any C runtime implements. -/
theorem not_regular_exact : Not RegularExactness :=
  nativeRegularExactness_false

end StagedCandidate

namespace ComputationalIdentity

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.SyntacticJudgmentalIdentityEliminator
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.SyntacticJudgmentalPi
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeIndexedFamilies.Intrinsic
open Mettapedia.TypeTheory.JudgmentalEquality

/-- The cumulative-tower theory retains an actual J/iota conversion receipt,
not merely proposition-valued support for convertibility. -/
abbrev JIotaRoute :=
  ConversionEvidence
    (termComputation nativeIotaRetainedRoot formedIdentityContext)
    identityIotaCell.source identityIotaCell.target

def jIotaRoute : JIotaRoute := identityIotaConversion

/-- J computes between syntactically different endpoints, while the authored
evidence rejects an unrelated target. -/
theorem j_computation_is_nontrivial_and_selective :
    Nonempty JIotaRoute /\
      identityIotaCell.source.code ≠ identityIotaCell.target.code /\
      IsEmpty (IotaEvidence 4 identityIotaLeft (.var 1)) :=
  And.intro (Nonempty.intro jIotaRoute)
    (And.intro identityIota_endpoints_not_equal
      wrongIdentityTarget_has_noEvidence)

end ComputationalIdentity

/-! ## Joint status theorem -/

/-- The desired scoping shape is consistent, but the current artifacts divide
its responsibilities: Pure is a proposition-valued checked boundary; the
cumulative tower retains computational identity and occurrence receipts; and
the staged candidate still fails regular-kernel exactness. -/
theorem current_artifacts_are_layers_not_one_settled_identity_theory :
    HasDistinctRoutes BubbleCanary.layer /\
      ScopedRouteUIP BubbleCanary.layer BubbleCanary.checkedOnly /\
      Not TwoSort.RetainsSomeTypingRoutes /\
      Not StagedCandidate.RegularExactness /\
      Nonempty ComputationalIdentity.JIotaRoute := by
  exact And.intro BubbleCanary.layer_hasDistinctRoutes <|
    And.intro BubbleCanary.checkedOnly_scopedUIP <|
      And.intro TwoSort.does_not_retain_typing_routes <|
        And.intro StagedCandidate.not_regular_exact <|
          Nonempty.intro ComputationalIdentity.jIotaRoute

/-! ## Axiom audit -/

#print axioms prop_has_no_distinct_receipts
#print axioms TwoSort.identity_is_inhabited
#print axioms TwoSort.does_not_retain_typing_routes
#print axioms StagedCandidate.not_regular_exact
#print axioms ComputationalIdentity.j_computation_is_nontrivial_and_selective
#print axioms current_artifacts_are_layers_not_one_settled_identity_theory

end Mettapedia.Languages.MeTTa.PrimeCandidates.ScopedIdentityStatus
