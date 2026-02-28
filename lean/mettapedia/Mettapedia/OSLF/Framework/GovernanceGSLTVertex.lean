import Mettapedia.OSLF.Framework.GovernanceInstance
import Mettapedia.OSLF.Framework.HypercubeGSLTFunctor
import Mettapedia.OSLF.Framework.PyashCoreProofs
import Mettapedia.OSLF.Framework.GovNormCycle

/-!
# Governance GSLT Vertex Integration

Connects the governance DDLPlus/OSLF layer to the broader GSLT framework.

## Architecture

```
PyashCore (LanguageDef, operational engine)
    │
    │  pyashCoreOSLF = govOSLF     (OSLF pipeline, Galois ◇ ⊣ □)
    │
    ├──→ GovernanceDDLBundle       (accessibility + deontic frame)
    │       ↓
    │   govDDLFrameClosed          (DDLPlusFrame on live states)
    │       ↓
    │   CJ_3/D/4/6/Kant            (all CJ theorems specialised)
    │
    └──→ governanceForwardFiber    (unit-indexed ForwardFiber over PyashCore)
```

## Design Note

PyashCore is a standalone `LanguageDef`, not a `vertexLanguageDef v` for
any PLN `ProbabilityVertex`.  The `GovernanceDDLBundle` captures the full
deontic reasoning setup independently of the PLN vertex structure.

For GSLT integration, `GovernanceForwardFiber` embeds PyashCore as a
degenerate fiber (unit-indexed, constant language).
-/

namespace Mettapedia.OSLF.Framework.GovernanceGSLTVertex

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.PyashCoreInstance
open Mettapedia.OSLF.Framework.LangMorphism
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.HypercubeGSLTFunctor
open Mettapedia.Logic.DDLPlus.Core
open Mettapedia.Logic.DDLPlus.Theorems
open Mettapedia.Logic.DDLPlus.DTSBridge
open Mettapedia.OSLF.Framework.GovernanceInstance
open Mettapedia.OSLF.Framework.GovNormCycle

/-! ## §1 GovernanceDDLBundle

A `GovernanceDDLBundle` packages everything needed for governance deontic
reasoning: a closed accessibility context (liveness + seriality + closure)
together with a deontic frame over the live subtype. -/

/-- A complete governance reasoning setup:
    accessibility + deontic frame over the live subtype. -/
structure GovernanceDDLBundle where
  /-- The accessibility structure (live states, seriality, closure). -/
  acc  : ClosedGovAccessibility
  /-- The deontic frame (obligation structure over live states). -/
  frame : GovFrame { p : Pattern // acc.live p }

/-- Extract the DDLPlusFrame from a GovernanceDDLBundle. -/
noncomputable def GovernanceDDLBundle.toDDLPlusFrame (b : GovernanceDDLBundle) :
    DDLPlusFrame { p : Pattern // b.acc.live p } :=
  govDDLFrameClosed b.acc b.frame

/-! ## §2 Specialised CJ Theorems

All Carmo-Jones DDL+ theorems apply to any `GovernanceDDLBundle`. -/

/-- CJ_3 for any governance bundle: □ₚ implies □ₐ. -/
theorem GovernanceDDLBundle.cj3 (b : GovernanceDDLBundle)
    (φ : Meaning Unit { p : Pattern // b.acc.live p })
    (ctx : Unit) (v : { p : Pattern // b.acc.live p }) :
    box_p b.toDDLPlusFrame φ ctx v →
    box_a b.toDDLPlusFrame φ ctx v :=
  CJ_3 b.toDDLPlusFrame φ ctx v

/-- Axiom D for any governance bundle: □ₐ implies ◇ₐ. -/
theorem GovernanceDDLBundle.axiomD (b : GovernanceDDLBundle)
    (φ : Meaning Unit { p : Pattern // b.acc.live p })
    (ctx : Unit) (v : { p : Pattern // b.acc.live p }) :
    box_a b.toDDLPlusFrame φ ctx v →
    dia_a b.toDDLPlusFrame φ ctx v :=
  axiomD_actual b.toDDLPlusFrame φ ctx v

/-- CJ_4 for any governance bundle: contradictions are never obligatory. -/
theorem GovernanceDDLBundle.cj4 (b : GovernanceDDLBundle)
    (A : Meaning Unit { p : Pattern // b.acc.live p }) :
    modal_valid (pnot (cond_obl b.toDDLPlusFrame pbot A)) :=
  CJ_4 b.toDDLPlusFrame A

/-- CJ_6 for any governance bundle: obligation restricted to its satisfiers.
    `O⟨B|A⟩ → O⟨B|A∧B⟩`   (CJDDLplus.thy §CJ_6) -/
theorem GovernanceDDLBundle.cj6 (b : GovernanceDDLBundle)
    (A B : Meaning Unit { p : Pattern // b.acc.live p }) :
    modal_valid (pimp (cond_obl b.toDDLPlusFrame B A)
                      (cond_obl b.toDDLPlusFrame B (pand A B))) :=
  CJ_6 b.toDDLPlusFrame B A

/-- Kant's law for any governance bundle: necessity precludes actual obligation. -/
theorem GovernanceDDLBundle.kant (b : GovernanceDDLBundle)
    (φ : Meaning Unit { p : Pattern // b.acc.live p })
    (ctx : Unit) (v : { p : Pattern // b.acc.live p })
    (hbox : box_a b.toDDLPlusFrame φ ctx v) :
    ¬ actual_obl b.toDDLPlusFrame φ ctx v :=
  box_a_implies_not_actual_obl b.toDDLPlusFrame ctx v φ hbox

/-- CJ_14a for any governance bundle: conditional obligation + av-box + two witnesses
    → actual obligation. (Direct delegation — see DDLPlus.Theorems for full statement.) -/
theorem GovernanceDDLBundle.cj14a (b : GovernanceDDLBundle)
    (A B : Meaning Unit { p : Pattern // b.acc.live p }) :
    modal_valid (pimp
      (pand (pand (pand (cond_obl b.toDDLPlusFrame A B)
                        (box_a b.toDDLPlusFrame B))
                  (dia_a b.toDDLPlusFrame A))
            (dia_a b.toDDLPlusFrame (pnot A)))
      (actual_obl b.toDDLPlusFrame A)) :=
  CJ_14a b.toDDLPlusFrame A B

/-! ## §3 GSLT Unit Fiber

PyashCore as a degenerate forward fiber (indexed by `Unit`).
This embeds governance into the GSLT categorical framework. -/

/-- The PyashCore identity forward simulation: the language does not change
    along the unique morphism in the unit preorder. -/
def pyashCoreIdMorphism : ForwardMorphism pyashCore pyashCore where
  mapTerm := id
  forward_sim _ q hred := ⟨q, .single hred, rfl⟩

/-- The governance (PyashCore) forward fiber: a degenerate fiber indexed by `Unit`
    where the language is constantly `pyashCore`.  All morphisms are identities. -/
def governanceForwardFiber : ForwardFiber Unit where
  lang  := fun _ => pyashCore
  morph := fun _ => pyashCoreIdMorphism

/-- The governance OSLF type system is the one produced by `govOSLF`. -/
theorem governanceForwardFiber_oslf :
    govOSLF = langOSLF pyashCore "State" := rfl

/-- ◇ in the governance fiber = existence of a one-step successor. -/
theorem governanceForwardFiber_diamond (φ : Pattern → Prop) (p : Pattern) :
    langDiamond pyashCore φ p ↔ ∃ q, langReduces pyashCore p q ∧ φ q :=
  langDiamond_spec pyashCore φ p

/-- □ in the governance fiber = all predecessors satisfy φ. -/
theorem governanceForwardFiber_box (φ : Pattern → Prop) (p : Pattern) :
    langBox pyashCore φ p ↔ ∀ q, langReduces pyashCore q p → φ q :=
  langBox_spec pyashCore φ p

/-! ## §4 Canonical Live Predicate

`isGovLive` (from `GovernanceInstance.lean`) identifies non-terminated
PyashCore states (instruction ≠ Done).

**Mathematical fact**: `isGovLive` is NOT forward-closed under PyashCore reduction.
The counterexample is `pyashStateRunning` (RunDo instruction): it is live, reduces
to `pyashStateDoneOk` (Done instruction), which is not live.  This is proven in
`PyashCoreProofs.lean` as `pyashCore_isGovLive_not_closed`.

Consequently, `ClosedGovAccessibility` with `live = isGovLive` cannot be
instantiated for PyashCore.  The architecture is designed for infinite/reactive
process languages where a meaningful live set IS forward-closed.

The function below retains `isGovLive` as the declared live predicate and
exposes both proofs as parameters, so the architectural wiring is complete —
the obligation to supply the proofs surfaces only at instantiation time.  This
is the correct design: the DDLPlus/governance reasoning infrastructure is
language-agnostic and applies to any language with a forward-closed live set. -/

/-- A closed accessibility for `isGovLive`, parameterized by the proofs of
    seriality and closure (which depend on PyashCore's operational semantics).

    **Note**: As proven by `pyashCore_isGovLive_not_closed`, the closure
    property `hclosed` does NOT hold for PyashCore with `live = isGovLive`.
    This function serves as the correct architectural hook; instantiation
    requires a different live predicate for a terminating language like PyashCore. -/
def isGovLiveAccessibility
    (hserial : ∀ p, isGovLive p → ∃ q, langReduces pyashCore p q)
    (hclosed : ∀ p q, isGovLive p → langReduces pyashCore p q → isGovLive q) :
    ClosedGovAccessibility where
  live   := isGovLive
  step   := langReduces pyashCore
  serial := hserial
  closed := hclosed

/-! ## §5 Norm-Cycle Bundle

`GovNormCycle` provides a concrete `ClosedGovAccessibility` instance with a
2-state reactive loop (`GovDeliberate ↔ GovEnact`).  This allows constructing
a concrete `GovernanceDDLBundle` without relying on PyashCore's operational semantics.

The norm-cycle is the canonical governance accessibility model: an idealized
deliberation–enactment loop that never terminates, satisfying both seriality and
closure constructively. -/

/-- Construct a concrete governance bundle over the norm cycle.
    Supply a `GovFrame` for the obligation structure; accessibility is `govNormCycleAccessibility`. -/
def govNormCycleBundle
    (gf : GovFrame { p : Pattern // govNormLive p }) :
    GovernanceDDLBundle :=
  { acc := govNormCycleAccessibility, frame := gf }

/-! ## §6 Summary

The governance DDLPlus integration is complete:
- `GovernanceDDLBundle`: the packaging type (acc + frame)
- `GovernanceDDLBundle.toDDLPlusFrame`: induces a DDLPlusFrame
- CJ_3, D, 4, 6, Kant, CJ_14a: all proven for any bundle
- `governanceForwardFiber`: embeds PyashCore into the GSLT framework as a
  degenerate unit-indexed fiber
- `isGovLiveAccessibility`: PyashCore hook (seriality + closure parameters;
  closure NOT satisfiable for PyashCore, proven by `pyashCore_isGovLive_not_closed`)
- `govNormCycleBundle`: concrete bundle using the deliberate ↔ enact reactive loop
  (0 sorries, 0 axioms — seriality and closure constructively proven)
-/

#check @GovernanceDDLBundle.toDDLPlusFrame
#check @GovernanceDDLBundle.cj3
#check @GovernanceDDLBundle.axiomD
#check @GovernanceDDLBundle.cj4
#check @GovernanceDDLBundle.kant
#check @GovernanceDDLBundle.cj14a
#check @governanceForwardFiber
#check @isGovLiveAccessibility
#check @govNormCycleBundle

end Mettapedia.OSLF.Framework.GovernanceGSLTVertex
