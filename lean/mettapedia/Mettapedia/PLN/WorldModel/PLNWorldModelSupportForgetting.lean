import Mettapedia.PLN.WorldModel.PLNWorldModelGeneric
import Mettapedia.PLN.WorldModel.GenericWorldModelForgetting

/-!
# Support-Tracked WM Forgetting Layer

A forgetting layer with explicit supports and scope footprints.  A state is
*supported* in a scope when every support lies inside the scope's footprint,
and *clean* for it when no support meets the footprint.

Forgetting a scope is asked to commute with revision (`forget_add`), to erase
every supported state (`forget_eq_zero_of_supported`) and to fix every clean
state (`forget_eq_self_of_clean`).  Two laws follow:

* **exact unlearning on clean bases** (`exactInverse_of_clean`): forgetting a
  supported revision of a clean base recovers the base exactly;
* **absorption on every base** (`forget_add_of_supported`): forgetting after a
  supported revision is forgetting before it.

The exact inverse cannot be asked of every base.  A base that already carries
forgotten material must lose it too, and a layer that undoes a revision on
every base forgets nothing while the revision is zero
(`GenericWorldModelForgetting.ForgettingLayer.exactInverse_everywhere_degenerate`).

Supported revisions carry no evidence outside the forgotten scope
(`exactInverse_revision_supported_outside_zero`).
-/

namespace Mettapedia.PLN.WorldModel.PLNWorldModelSupportForgetting

open Mettapedia.PLN.Evidence.EvidenceClass
open Mettapedia.PLN.WorldModel.PLNWorldModelGeneric
open Mettapedia.PLN.WorldModel.GenericWorldModelForgetting

variable {State Scope Query Ev Supp : Type*}
variable [EvidenceType State] [AddCommMonoid Ev] [AdditiveWorldModel State Query Ev]

/-- Forgetting layer enriched with supports and scope footprints.  Forgetting
commutes with revision, erases states supported inside the footprint and fixes
states whose supports avoid it. -/
structure SupportTrackedForgettingLayer (State Scope Query Ev Supp : Type*)
    [EvidenceType State] [AddCommMonoid Ev] [AdditiveWorldModel State Query Ev]
    extends ForgettingLayer State Scope Query Ev where
  scopeFootprint : Scope → Finset Supp
  support : State → Query → Finset Supp
  forget_add : ∀ (S : Scope) (W₁ W₂ : State), forget S (W₁ + W₂) = forget S W₁ + forget S W₂
  forget_eq_zero_of_supported :
    ∀ {S : Scope} {Δ : State}, (∀ q, support Δ q ⊆ scopeFootprint S) → forget S Δ = 0
  forget_eq_self_of_clean :
    ∀ {S : Scope} {W : State}, (∀ q, Disjoint (support W q) (scopeFootprint S)) →
      forget S W = W

namespace SupportTrackedForgettingLayer

variable {State Scope Query Ev Supp : Type*}
variable [EvidenceType State] [AddCommMonoid Ev] [AdditiveWorldModel State Query Ev]

/-- `Δ` is supported in scope `S`: every support of `Δ` lies inside the footprint. -/
def Supported (F : SupportTrackedForgettingLayer State Scope Query Ev Supp)
    (S : Scope) (Δ : State) : Prop :=
  ∀ q, F.support Δ q ⊆ F.scopeFootprint S

/-- `W` is clean for scope `S`: no support of `W` meets the footprint. -/
def Clean (F : SupportTrackedForgettingLayer State Scope Query Ev Supp)
    (S : Scope) (W : State) : Prop :=
  ∀ q, Disjoint (F.support W q) (F.scopeFootprint S)

/-- **Exact unlearning on clean bases**: forgetting a supported revision of a
clean base recovers the base. -/
theorem exactInverse_of_clean
    (F : SupportTrackedForgettingLayer State Scope Query Ev Supp)
    {S : Scope} {Δ W : State}
    (hsupp : F.Supported S Δ) (hclean : F.Clean S W) :
    F.forget S (W + Δ) = W := by
  rw [F.forget_add, F.forget_eq_self_of_clean hclean, F.forget_eq_zero_of_supported hsupp,
    add_zero]

/-- **Absorption on every base**: a supported revision leaves no trace after
forgetting, whatever the base already carries. -/
theorem forget_add_of_supported
    (F : SupportTrackedForgettingLayer State Scope Query Ev Supp)
    {S : Scope} {Δ : State} (hsupp : F.Supported S Δ) (W : State) :
    F.forget S (W + Δ) = F.forget S W := by
  rw [F.forget_add, F.forget_eq_zero_of_supported hsupp, add_zero]

/-- A supported revision contributes no evidence to any query outside the
forgotten scope. -/
theorem exactInverse_revision_supported_outside_zero
    (F : SupportTrackedForgettingLayer State Scope Query Ev Supp)
    (hzero : GenericWorldModelZeroPreserving (State := State) (Query := Query) (Ev := Ev))
    {S : Scope} {Δ : State}
    (hsupp : ∀ q, F.support Δ q ⊆ F.scopeFootprint S) :
    ∀ q, ¬ F.inScope S q →
      AdditiveWorldModel.extract
        (State := State) (Query := Query) (Ev := Ev) Δ q = 0 :=
  ForgettingLayer.erased_revision_supported
    (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
    F.toForgettingLayer hzero (F.forget_eq_zero_of_supported hsupp)

/-- Hence a supported revision cannot carry evidence outside the scope. -/
theorem no_exactInverse_revision_of_nonzero_outside_scope_of_supported
    (F : SupportTrackedForgettingLayer State Scope Query Ev Supp)
    (hzero : GenericWorldModelZeroPreserving (State := State) (Query := Query) (Ev := Ev))
    {S : Scope} {Δ : State} {q : Query}
    (hsupp : ∀ q, F.support Δ q ⊆ F.scopeFootprint S)
    (hout : ¬ F.inScope S q)
    (hne :
      AdditiveWorldModel.extract
        (State := State) (Query := Query) (Ev := Ev) Δ q ≠ 0) :
    False :=
  ForgettingLayer.not_erased_of_nonzero_outside_scope
    (State := State) (Scope := Scope) (Query := Query) (Ev := Ev)
    F.toForgettingLayer hzero hout hne (F.forget_eq_zero_of_supported hsupp)

end SupportTrackedForgettingLayer
end Mettapedia.PLN.WorldModel.PLNWorldModelSupportForgetting
