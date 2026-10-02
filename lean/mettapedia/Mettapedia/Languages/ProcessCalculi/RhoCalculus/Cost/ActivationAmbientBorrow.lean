import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.AdministrativeFrame
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationRuntimeControls

/-!
# Ambient funding across transparent contact frames

Concrete rho contact is parallel composition. An inner empty purse does not
block a matching positive outer purse at the same nominal location. This is
distinct from a generated free-constructor context whose reduction premise
requires the inner administrative funding envelope to succeed on its own.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe u

/-- In the actual relation, a matching outer head funds an inner whole COMM
whose own administrative purse is empty. Its inner empty purse is retained. -/
theorem locatedContact_outer_head_funds_inner {Ground : Type u}
    (location : CostName Ground) (body payload : CostTerm Ground)
    (signature : CostSig Ground) (valid : signature.RuntimeValid)
    (tail : CostStack Ground) :
    CostStep
      (locatedContact location
        (locatedContact location
          (.signed (.par (.recv location body) (.send location payload)) signature) .empty)
        (.cons signature tail)).components
      location signature
      (locatedContact location
        (locatedContact location (body.commSubst payload) .empty) tail).components := by
  have actual := CostStep.wholeRecvSend
    (context := (CostTerm.purse location .empty ::ₘ 0))
    (body := body) (payload := payload) valid
    (LocatedTokenCover.singleHead location signature valid tail)
  simpa only [locatedContact, CostTerm.components,
    LocatedPurse.configComponents, Multiset.map_singleton, LocatedPurse.toTerm, Multiset.cons_zero,
    add_assoc, add_comm, add_left_comm] using actual

/-- The same inner envelope is blocked in isolation, while the surrounding
matching cell enables a real charged event. -/
theorem locatedContact_isolation_does_not_reflect_ambient_funding {Ground : Type u}
    (location : CostName Ground) (body payload : CostTerm Ground)
    (signature : CostSig Ground) (valid : signature.RuntimeValid)
    (tail : CostStack Ground) :
    (∀ spend target, ¬ CostStep
      (locatedContact location
        (.signed (.par (.recv location body) (.send location payload)) signature) .empty).components location spend target) ∧
    CostStep
      (locatedContact location
        (locatedContact location
          (.signed (.par (.recv location body) (.send location payload)) signature) .empty)
        (.cons signature tail)).components
      location signature
      (locatedContact location
        (locatedContact location (body.commSubst payload) .empty) tail).components := by
  constructor
  · intro spend target
    exact CostStep.signed_with_empty_purse_blocked _ _ _ _ _ _
  · exact locatedContact_outer_head_funds_inner location body payload signature valid tail

namespace ActivationAmbientBorrowControls

def channel : RawCostName := .signature ["shared"]

def redex : RawCostTerm :=
  .signed (.par (.recv channel .nil) (.send channel .nil)) ["a"]

def source : RawCostTerm :=
  .par (.par redex (.purse channel [])) (.purse channel [["a"]])

def isolated : RawCostTerm := .par redex (.purse channel [])

def wrongLocation : RawCostTerm :=
  .par isolated (.purse (.signature ["elsewhere"]) [["a"]])

theorem source_wellFormed : source.wellFormed = true := by decide +kernel

def run := ActivationControls.initialRun 2 source source_wellFormed

/-- The existing occurrence-bearing runtime spends the outer head, retaining
two empty purses; the isolated and wrong-location counterparts are blocked. -/
theorem actual_ambient_borrow :
    source.supported = true ∧ run.2.2.depth = 1 ∧ run.2.2.consumedPurseCells = 1 ∧
    run.2.2.rawEmission.map RawEmittedEvent.rawSpend = [["a"]] ∧
    (run.2.1.map RawTraceComponent.term).count (.purse channel []) = 2 ∧
    runtimeCostFrontier isolated = some [] ∧ runtimeCostFrontier wrongLocation = some [] := by
  decide +kernel

end ActivationAmbientBorrowControls
end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
