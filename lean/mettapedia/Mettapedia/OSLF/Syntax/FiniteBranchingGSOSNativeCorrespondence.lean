import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSNativeFiring
import Mettapedia.OSLF.Syntax.FiniteBranchingGSOSRuleQuotient
import Mathlib.Data.Fintype.EquivFin

/-!
# The admitted finite-action law correspondence with native firing domains

An independently supplied finite presentation is authored with a finite
enumeration whose identifiers correspond bijectively to its actual clauses.
This preserves its complete denotation and the prescribed universe bound.
For finite action carriers, the already earned reconstruction of arbitrary
natural finite-per-action laws therefore supplies actual native firing
domains. Their complete dependent receipt interpretation and rule target
readouts are the same constructions used for separately authored clauses.

The reconstructed clause identifiers do not recover redundant identifiers
of an earlier authored presentation. Infinite action carriers retain the
forward clause interpretation, not this unrestricted reconstruction theorem.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.FiniteBranching.NativeCorrespondence

open _root_.CategoryTheory Mettapedia.TypeTheory
open Mettapedia.OSLF.DeterministicGSOS (Signature)
open Premises NativeEdges NativePremises
open Classical

universe u
variable {S : Signature.{u}} {Actions : S.Srt → Type u}

def ofPresentation (presentation : Presentation S Actions) : AuthoredPresentation S Actions where
  Origin sort operator action := ULift.{u} (Fin (presentation sort operator action).card)
  finite _ _ _ := inferInstance
  rule sort operator action origin := ((presentation sort operator action).equivFin.symm origin.down).val

/-- The small identifiers retain exactly the supplied finite clauses. -/
def clauseEquiv (presentation : Presentation S Actions) (sort : S.Srt)
    (operator : S.Operator sort) (action : Actions sort) :
    (ofPresentation presentation).Origin sort operator action ≃
      {rule : Rule (Actions := Actions) operator // rule ∈ presentation sort operator action} :=
  Equiv.ulift.trans (presentation sort operator action).equivFin.symm

theorem readout_ofPresentation (presentation : Presentation S Actions) :
    (ofPresentation presentation).readout = presentation := by
  funext sort operator action
  let _ : Fintype (ULift.{u} (Fin (presentation sort operator action).card)) :=
    @Fintype.ofFinite _ ((ofPresentation presentation).finite sort operator action)
  apply Finset.ext
  intro rule
  change rule ∈ Finset.univ.image
    (fun origin : ULift.{u} (Fin (presentation sort operator action).card) =>
      ((presentation sort operator action).equivFin.symm origin.down).val) ↔
        rule ∈ presentation sort operator action
  rw [Finset.mem_image]
  constructor
  · rintro ⟨origin, _, same⟩
    exact same ▸ ((presentation sort operator action).equivFin.symm origin.down).property
  · intro member
    refine ⟨⟨(presentation sort operator action).equivFin ⟨rule, member⟩⟩, Finset.mem_univ _, ?_⟩
    exact congrArg Subtype.val ((presentation sort operator action).equivFin.symm_apply_apply ⟨rule, member⟩)

theorem law_ofPresentation (presentation : Presentation S Actions) :
    NativePremises.law (ofPresentation presentation) = Presentation.toLaw presentation := by
  unfold NativePremises.law
  rw [readout_ofPresentation]

variable [∀ sort, Finite (Actions sort)]

def canonical (candidate : Law S Actions) : AuthoredPresentation S Actions :=
  ofPresentation (Reconstruction.fromLaw candidate)

/-- The complete natural law is recovered through the independently
constructed finite rule format and its earned support/interpolation proofs. -/
theorem canonical_law (candidate : Law S Actions) :
    NativePremises.law (canonical candidate) = candidate :=
  (law_ofPresentation (Reconstruction.fromLaw candidate)).trans (Reconstruction.law_roundtrip candidate)

variable {C : Type u} [Category.{u} C]
variable (worlds : Cᵒᵖ ⥤ S.Families)
variable (steps : worlds ⟶ worlds ⋙ behaviourFunctor S Actions)

/-- The actual arbitrary-law constructor behavior has exactly the native
firing readout of its independent finite-action reconstruction. Its native
domains retain complete matching assignments and occurrence identifiers. -/
theorem operational_correspondence (candidate : Law S Actions)
    (PremiseOrigins : Type u) [Nonempty PremiseOrigins]
    (world : Cᵒᵖ) {sort : S.Srt} (operator : S.Operator sort) (action : Actions sort)
    (given : (children worlds operator).obj world) (target : S.Term (worlds.obj world) sort) :
    target ∈ Operational.coalgebra candidate (steps.app world) PUnit.unit sort
      (IndexedPolynomial.Free.node S.polynomial operator given) action ↔
    ∃ firing : NativePremises.Firing (canonical candidate) worlds steps PremiseOrigins world operator action,
      firing.children = given ∧ firing.target = target := by
  simpa only [canonical_law] using
    (operational_iff_nativeFiring (canonical candidate) worlds steps PremiseOrigins world
      operator action given target)

/-- Complete matching receipts, including the independent per-occurrence
identifiers, classify the actual native domain in both directions. -/
def domainEquiv (candidate : Law S Actions) (PremiseOrigins : Type u) (world : Cᵒᵖ)
    {sort : S.Srt} (operator : S.Operator sort) (action : Actions sort) :
    NativePremises.Firing (canonical candidate) worlds steps PremiseOrigins world operator action ≃
      MatchingReceipt (canonical candidate) worlds steps PremiseOrigins world operator action :=
  matchingReceiptEquiv (canonical candidate) worlds steps PremiseOrigins world operator action

end Mettapedia.OSLF.FiniteBranching.NativeCorrespondence
