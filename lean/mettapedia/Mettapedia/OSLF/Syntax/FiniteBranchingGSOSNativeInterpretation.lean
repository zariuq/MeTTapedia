import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSNativeCorrespondence
import Mettapedia.GSLT.Topos.PresheafPredicateGenericTruth

/-!
# The sieve and complete dependent interpretation of admitted ND clauses

The independently authored matching predicate is classified by the actual
native truth object. Its sieve reads the complete matching judgment at every
future context, including the authored negative addresses. The native sum
certificate is equivalent to an ordinary matching receipt together with its
actual target witness. Both directions retain the entire assignment, clause
identifier and supplied positive-occurrence identifiers. The source and
dependent-result projections commute with that comparison.

The finite-action reconstruction supplies this same interpretation for an
arbitrary natural law. It does not reconstruct redundant earlier identifiers
from the extensional law, or equate present absence with arbitrary future
extensions. Matching domains use the exact successor-image action already
proved for the actual operational lifting.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.NativeInterpretation

open _root_.CategoryTheory Mettapedia.TypeTheory
open Mettapedia.OSLF.DeterministicGSOS (Signature)
open Mettapedia.GSLT.Topos
open Premises NativeEdges NativePremises PresheafEventCertificates
open DisplayedPresheafTransport DisplayedPresheafComprehension

universe u
variable {S : Signature.{u}} {Actions : S.Srt → Type u}
variable {C : Type u} [Category.{u} C]
variable (authored : AuthoredPresentation S Actions)
variable (worlds : Cᵒᵖ ⥤ S.Families)
variable (steps : worlds ⟶ worlds ⋙ behaviourFunctor S Actions)

def guardCharacteristic {sort : S.Srt} {operator : S.Operator sort}
    (pattern : Pattern (Actions := Actions) operator) :
    children worlds operator ⟶ omegaFunctor (C := C) :=
  chiOfSubfunctor.{u, u} (C := C) (children worlds operator)
    (guard authored worlds steps pattern)

/-- The ordinary native proposition recovers exactly the independent guard. -/
theorem guard_classifies {sort : S.Srt} {operator : S.Operator sort}
    (pattern : Pattern (Actions := Actions) operator) :
    (PresheafPredicateGenericTruth.truthPredicate C).preimage
      (guardCharacteristic authored worlds steps pattern) = guard authored worlds steps pattern :=
  PresheafPredicateGenericTruth.characteristic_classifies _ _

theorem guard_characteristic_unique {sort : S.Srt} {operator : S.Operator sort}
    (pattern : Pattern (Actions := Actions) operator)
    (candidate : children worlds operator ⟶ omegaFunctor (C := C))
    (classifies : (PresheafPredicateGenericTruth.truthPredicate C).preimage candidate =
      guard authored worlds steps pattern) :
    candidate = guardCharacteristic authored worlds steps pattern :=
  PresheafPredicateGenericTruth.characteristic_unique _ _ candidate classifies

/-- A sieve tests the actual matching domain after the supplied change;
it retains future-sensitive native negation at every negative address. -/
theorem guard_sieve_readout {sort : S.Srt} {operator : S.Operator sort}
    (pattern : Pattern (Actions := Actions) operator)
    {world future : Cᵒᵖ} (change : world ⟶ future)
    (given : (children worlds operator).obj world) :
    ((guardCharacteristic authored worlds steps pattern).app world given).arrows change.unop ↔
      ∃ input : Input pattern (S.polynomial.Free (worlds.obj future)),
        Matches pattern (arguments authored worlds steps future
          ((children worlds operator).map change given)) input := by
  change (children worlds operator).map change given ∈
    (guard authored worlds steps pattern).obj future ↔ _
  exact guard_iff_matching authored worlds steps future pattern _

variable (PremiseOrigins : Type u) (world : Cᵒᵖ)
variable {sort : S.Srt} (operator : S.Operator sort) (action : Actions sort)

def matchingSource (receipt : MatchingReceipt authored worlds steps PremiseOrigins world operator action) :
    S.Term (worlds.obj world) sort :=
  IndexedPolynomial.Free.node S.polynomial operator receipt.1

def matchingTarget (receipt : MatchingReceipt authored worlds steps PremiseOrigins world operator action) :
    S.Term (worlds.obj world) sort :=
  IndexedPolynomial.Free.join S.polynomial receipt.2.1.target

/-- This independent domain has ordinary rule matching, every supplied
occurrence identifier and a witness at the rule's flattened target. -/
abbrev MatchingEvidence (A : DisplayedFamily (terms worlds sort)) :=
  Σ receipt : MatchingReceipt authored worlds steps PremiseOrigins world operator action,
    A.obj ⟨world, matchingTarget authored worlds steps PremiseOrigins world operator action receipt⟩

/-- The actual chosen native dependent sum has both inverse readouts into
the independently formed rule-and-witness domain, without normalizing it. -/
def certificateTotalEquiv (A : DisplayedFamily (terms worlds sort)) :
    (totalSpace ((firingSpan authored worlds steps PremiseOrigins operator action).certificates A)).obj world ≃
      MatchingEvidence authored worlds steps PremiseOrigins world operator action A :=
  ((firingSpan authored worlds steps PremiseOrigins operator action).certificateTotalIso A).app world |>.toEquiv |>.trans
    (Equiv.sigmaCongr (matchingReceiptEquiv authored worlds steps PremiseOrigins world operator action)
      (fun _ => Equiv.refl _))

theorem certificate_code_event (A : DisplayedFamily (terms worlds sort))
    (certificate : (totalSpace
      ((firingSpan authored worlds steps PremiseOrigins operator action).certificates A)).obj world) :
    (certificateTotalEquiv authored worlds steps PremiseOrigins world operator action A certificate).1 =
      matchingReceiptEquiv authored worlds steps PremiseOrigins world operator action
        (((firingSpan authored worlds steps PremiseOrigins operator action).eventReadout A).app world certificate) :=
  rfl

/-- The source interface is exactly the node of the stored passive sources. -/
theorem certificate_code_source (A : DisplayedFamily (terms worlds sort))
    (certificate : (totalSpace
      ((firingSpan authored worlds steps PremiseOrigins operator action).certificates A)).obj world) :
    matchingSource authored worlds steps PremiseOrigins world operator action
      (certificateTotalEquiv authored worlds steps PremiseOrigins world operator action A certificate).1 =
        certificate.1 :=
  certificate.2.property

/-- The complete dependent result is unchanged by the independent readout. -/
theorem certificate_code_result (A : DisplayedFamily (terms worlds sort))
    (certificate : (totalSpace
      ((firingSpan authored worlds steps PremiseOrigins operator action).certificates A)).obj world) :
    (⟨matchingTarget authored worlds steps PremiseOrigins world operator action
        (certificateTotalEquiv authored worlds steps PremiseOrigins world operator action A certificate).1,
      (certificateTotalEquiv authored worlds steps PremiseOrigins world operator action A certificate).2⟩ :
        (totalSpace A).obj world) =
      ((firingSpan authored worlds steps PremiseOrigins operator action).resultReadout A).app world certificate :=
  rfl

/-- An independently supplied source-family consumer has the actual native
sum elimination contract over the entire authored matching domain. -/
def eliminationEquiv (A : DisplayedFamily (terms worlds sort)) (D : DisplayedFamily (terms worlds sort)) :
    ((firingSpan authored worlds steps PremiseOrigins operator action).certificates A ⟶ D) ≃
      (reindexDisplayed (firingSpan authored worlds steps PremiseOrigins operator action).target A ⟶
        reindexDisplayed (firingSpan authored worlds steps PremiseOrigins operator action).source D) :=
  (firingSpan authored worlds steps PremiseOrigins operator action).eliminationEquiv A D

theorem support_readout (A : DisplayedFamily (terms worlds sort)) :
    support ((firingSpan authored worlds steps PremiseOrigins operator action).certificates A) =
      PresheafEventModalities.diamond
        (firingSpan authored worlds steps PremiseOrigins operator action).eventGraph (support A) :=
  (firingSpan authored worlds steps PremiseOrigins operator action).support_eq_eventDiamond A

end Mettapedia.OSLF.FiniteBranching.NativeInterpretation
