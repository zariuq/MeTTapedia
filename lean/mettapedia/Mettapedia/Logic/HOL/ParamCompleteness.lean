import Mettapedia.Logic.HOL.ParamTruthLemma
import Mettapedia.Logic.HOL.ParamWorld
import Mettapedia.Logic.HOL.Semantics.HeytingHenkin

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-!
# Root Counterworld Packaging for the Mainline Param Path  [MAINLINE]

This file packages the saturated root-world output of `ParamTruthLemma` into the
named boundary consumed by the remaining plain-completeness endgame.

- `RootCounterworld` is the direct mainline object: a saturated parameterized
  root world that contains all lifted hypotheses and omits the lifted
  conclusion.
- `HasRootCounterworld` is the proposition-level packaging of that object.
- Under the corrected root witness bridge, `HasRootCounterworld Δ φ` is
  equivalent to `¬ ExtDerivation Const Δ φ`.
-/

namespace ParamCompleteness

/-- A direct mainline parameterized root counterworld for the sequent `Δ ⊢ φ`.

The key correction over the earlier false shell is that the root world carries
its own parameter context `Γ`; it is not frozen to `[]`. -/
structure RootCounterworld
    (Base : Type u) (Const : Ty Base → Type v)
    (Δ : List (ClosedFormula Const)) (φ : ClosedFormula Const) where
  Γ : Ctx Base
  world : PrimeTheory.Saturated Const Γ
  hyps :
    ∀ ψ, ψ ∈ Δ → liftParamFormula Γ ψ ∈ world.carrier
  not_concl :
    liftParamFormula Γ φ ∉ world.carrier

/-- Explicit alias emphasizing that `RootCounterworld` is now parameterized by a
hidden root context. -/
abbrev ParamRootCounterworld := RootCounterworld

/-- Proposition-level packaging of the root counterworld boundary. -/
abbrev HasRootCounterworld
    (Base : Type u) (Const : Ty Base → Type v)
    (Δ : List (ClosedFormula Const)) (φ : ClosedFormula Const) : Prop :=
  Nonempty (RootCounterworld Base Const Δ φ)

/-- Proposition-level alias for the parameterized-root viewpoint. -/
abbrev HasParamRootCounterworld := HasRootCounterworld

/-- Direct mainline bridge from non-provability to root counterworld existence.

This is the boundary the public mainline should expose: it talks directly about
the existence of the semantic counterworld object, without committing to any
particular internal witness-axiom transport mechanism. -/
structure RootCounterworldBridge
    (Base : Type u) (Const : Ty Base → Type v) where
  hasRootCounterworld_of_not_provable :
    ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
      ¬ ExtDerivation Const Δ φ →
        HasRootCounterworld Base Const Δ φ

/-- The remaining semantic export boundary for the direct growing-domain route.

It packages exactly one theorem: every parameterized root counterworld can be
turned into a standard `HeytingHenkinModel` countermodel for the original
sequent.
-/
structure RootCounterworldCountermodelBridge
    (Base : Type u) (Const : Ty Base → Type v) where
  countermodel_of_rootCounterworld :
    ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
      RootCounterworld Base Const Δ φ →
        ∃ M : HeytingHenkinModel.{u, v, w} Base Const,
          ¬ HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)

theorem RootCounterworld.to_exists_world
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const}
    (C : RootCounterworld Base Const Δ φ) :
    ∃ Γ : Ctx Base,
      ∃ W : PrimeTheory.Saturated Const Γ,
        (∀ ψ, ψ ∈ Δ → liftParamFormula Γ ψ ∈ W.carrier) ∧
        liftParamFormula Γ φ ∉ W.carrier :=
  ⟨C.Γ, C.world, C.hyps, C.not_concl⟩

theorem hasRootCounterworld_of_exists_world
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const}
    (h :
      ∃ Γ : Ctx Base,
        ∃ W : PrimeTheory.Saturated Const Γ,
          (∀ ψ, ψ ∈ Δ → liftParamFormula Γ ψ ∈ W.carrier) ∧
          liftParamFormula Γ φ ∉ W.carrier) :
    HasRootCounterworld Base Const Δ φ := by
  rcases h with ⟨Γ, W, hΔ, hNot⟩
  exact ⟨⟨Γ, W, hΔ, hNot⟩⟩

/-- Any direct root counterworld refutes derivability of the original sequent. -/
theorem RootCounterworld.not_provable
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const}
    (C : RootCounterworld Base Const Δ φ) :
    ¬ ExtDerivation Const Δ φ := by
  intro d
  have dLift :
      ExtDerivation (ParamConst Const C.Γ)
        (Δ.map (liftParamFormula C.Γ))
        (liftParamFormula C.Γ φ) :=
    ExtDerivation.mapConst
      (fun {τ} c => (ParamConst.base c : ParamConst Const C.Γ τ))
      d
  have hMem :
      liftParamFormula C.Γ φ ∈ C.world.carrier :=
    C.world.closed <|
      ClosedTheorySet.provable_of_closedTheory
        (Const := ParamConst Const C.Γ)
        (T := C.world.carrier)
        (Δ := Δ.map (liftParamFormula C.Γ))
        (hΔ := by
          intro ψ hψ
          rcases List.mem_map.mp hψ with ⟨χ, hχ, rfl⟩
          exact C.hyps χ hχ)
        dLift
  exact C.not_concl hMem

/-- The parameterized root world immediately gives a forcing counterexample at
its own context. -/
theorem RootCounterworld.forces_counterexample
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const}
    (C : RootCounterworld Base Const Δ φ) :
    (∀ ψ, ψ ∈ Δ → C.world.Forces (liftParamFormula C.Γ ψ)) ∧
      ¬ C.world.Forces (liftParamFormula C.Γ φ) := by
  constructor
  · intro ψ hψ
    exact (PrimeTheory.Saturated.forces_iff_mem
      (W := C.world)
      (liftParamFormula C.Γ ψ)).2 (C.hyps ψ hψ)
  · intro hForce
    exact C.not_concl
      ((PrimeTheory.Saturated.forces_iff_mem
        (W := C.world)
        (liftParamFormula C.Γ φ)).1 hForce)

/-- The underlying growing world attached to a direct root counterworld.

Positive example:
this is the honest world object consumed by the direct parameterized Kripke
route.

Negative example:
this does not yet package a full `HeytingHenkinModel`; it is only the root
world sitting inside the growing frame.
-/
def RootCounterworld.toGrowingWorld
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const}
    (C : RootCounterworld Base Const Δ φ) :
    GrowingWorld Base Const :=
  ⟨C.Γ, C.world.toPrimeTheory⟩

/-- Every hypothesis of a root counterworld is true at its underlying growing
world in the new upper-set truth object. -/
theorem RootCounterworld.mem_formulaUpperSet_of_hyp
    {Δ : List (ClosedFormula Const)} {φ ψ : ClosedFormula Const}
    (C : RootCounterworld Base Const Δ φ)
    (hψ : ψ ∈ Δ) :
    C.toGrowingWorld ∈
      GrowingWorld.formulaUpperSet (Base := Base) (Const := Const) ψ := by
  exact C.hyps ψ hψ

/-- The conclusion of a root counterworld is false at its underlying growing
world in the new upper-set truth object. -/
theorem RootCounterworld.not_mem_formulaUpperSet_concl
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const}
    (C : RootCounterworld Base Const Δ φ) :
    C.toGrowingWorld ∉
      GrowingWorld.formulaUpperSet (Base := Base) (Const := Const) φ := by
  exact C.not_concl

theorem not_provable_of_hasRootCounterworld
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const}
    (h : HasRootCounterworld Base Const Δ φ) :
    ¬ ExtDerivation Const Δ φ := by
  rcases h with ⟨C⟩
  exact C.not_provable

/-- At the honest mainline boundary, a direct root-counterworld bridge is
equivalent to the existence of root counterworlds for all non-provable
sequents. -/
theorem hasRootCounterworld_iff_not_provable_of_bridge
    (R : RootCounterworldBridge Base Const)
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const} :
    HasRootCounterworld Base Const Δ φ ↔ ¬ ExtDerivation Const Δ φ := by
  constructor
  · exact not_provable_of_hasRootCounterworld (Base := Base) (Const := Const)
  · exact R.hasRootCounterworld_of_not_provable

/-- A root-level saturation bridge already yields the direct mainline
root-counterworld boundary. -/
theorem hasRootCounterworld_of_not_provable_of_rootSaturationBridge
    (B : RootSaturationBridge Base Const)
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const}
    (hNot : ¬ ExtDerivation Const Δ φ) :
    HasRootCounterworld Base Const Δ φ := by
  rcases exists_root_world_saturated_of_bridge
    (Base := Base)
    (Const := Const)
    (B := B)
    (Δ := Δ)
    (φ := φ)
    hNot with ⟨W, hΔ, hNotφ⟩
  exact ⟨⟨[], W, hΔ, hNotφ⟩⟩

/-- Mainline equivalence at the root-saturation boundary. -/
theorem hasRootCounterworld_iff_not_provable_of_rootSaturationBridge
    (B : RootSaturationBridge Base Const)
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const} :
    HasRootCounterworld Base Const Δ φ ↔ ¬ ExtDerivation Const Δ φ := by
  constructor
  · exact not_provable_of_hasRootCounterworld (Base := Base) (Const := Const)
  · exact hasRootCounterworld_of_not_provable_of_rootSaturationBridge
      (Base := Base)
      (Const := Const)
      B

/-- A root-level saturation bridge induces the direct mainline
root-counterworld bridge. -/
def RootSaturationBridge.toRootCounterworldBridge
    (B : RootSaturationBridge Base Const) :
    RootCounterworldBridge Base Const where
  hasRootCounterworld_of_not_provable := by
    intro Δ φ hNot
    exact hasRootCounterworld_of_not_provable_of_rootSaturationBridge
      (Base := Base)
      (Const := Const)
      B
      hNot

/-- A saturation-preserving extension theorem already yields the direct
mainline root-counterworld boundary. -/
theorem hasRootCounterworld_of_not_provable_of_saturate
    (hSaturate :
      ∀ {Γ : Ctx Base} {χ : ClosedFormula (ParamConst Const Γ)},
        (W : PrimeTheory Const Γ) →
        χ ∉ W.carrier →
        ∃ Ws : PrimeTheory.Saturated Const Γ,
          (∀ {ψ : ClosedFormula (ParamConst Const Γ)},
            ψ ∈ W.carrier → ψ ∈ Ws.carrier) ∧
          χ ∉ Ws.carrier)
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const}
    (hNot : ¬ ExtDerivation Const Δ φ) :
    HasRootCounterworld Base Const Δ φ := by
  rcases exists_root_world_saturated_of
    (Base := Base)
    (Const := Const)
    (hSaturate := hSaturate)
    (Δ := Δ)
    (φ := φ)
    hNot with ⟨W, hΔ, hNotφ⟩
  exact ⟨⟨[], W, hΔ, hNotφ⟩⟩

/-- Mainline equivalence at the saturation-preserving extension boundary. -/
theorem hasRootCounterworld_iff_not_provable_of_saturate
    (hSaturate :
      ∀ {Γ : Ctx Base} {χ : ClosedFormula (ParamConst Const Γ)},
        (W : PrimeTheory Const Γ) →
        χ ∉ W.carrier →
        ∃ Ws : PrimeTheory.Saturated Const Γ,
          (∀ {ψ : ClosedFormula (ParamConst Const Γ)},
            ψ ∈ W.carrier → ψ ∈ Ws.carrier) ∧
          χ ∉ Ws.carrier)
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const} :
    HasRootCounterworld Base Const Δ φ ↔ ¬ ExtDerivation Const Δ φ := by
  constructor
  · exact not_provable_of_hasRootCounterworld (Base := Base) (Const := Const)
  · exact hasRootCounterworld_of_not_provable_of_saturate
      (Base := Base)
      (Const := Const)
      hSaturate

/-- An arbitrary-context saturation bridge already yields the direct mainline
root-counterworld boundary. -/
theorem hasRootCounterworld_of_not_provable_of_saturationBridge
    (B : PrimeTheory.SaturationBridge Base Const)
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const}
    (hNot : ¬ ExtDerivation Const Δ φ) :
    HasRootCounterworld Base Const Δ φ := by
  rcases exists_root_world_saturated_of_saturationBridge
    (Base := Base)
    (Const := Const)
    (B := B)
    (Δ := Δ)
    (φ := φ)
    hNot with ⟨W, hΔ, hNotφ⟩
  exact ⟨⟨[], W, hΔ, hNotφ⟩⟩

/-- Mainline equivalence at the arbitrary-context saturation-bridge boundary. -/
theorem hasRootCounterworld_iff_not_provable_of_saturationBridge
    (B : PrimeTheory.SaturationBridge Base Const)
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const} :
    HasRootCounterworld Base Const Δ φ ↔ ¬ ExtDerivation Const Δ φ := by
  constructor
  · exact not_provable_of_hasRootCounterworld (Base := Base) (Const := Const)
  · exact hasRootCounterworld_of_not_provable_of_saturationBridge
      (Base := Base)
      (Const := Const)
      B

/-- An arbitrary-context saturation bridge induces the direct mainline
root-counterworld bridge. -/
def PrimeTheory.SaturationBridge.toRootCounterworldBridge
    (B : PrimeTheory.SaturationBridge Base Const) :
    RootCounterworldBridge Base Const where
  hasRootCounterworld_of_not_provable := by
    intro Δ φ hNot
    exact hasRootCounterworld_of_not_provable_of_saturationBridge
      (Base := Base)
      (Const := Const)
      B
      hNot

/-- A saturation-preserving extension theorem induces the direct mainline
root-counterworld bridge. -/
def rootCounterworldBridgeOfSaturate
    (hSaturate :
      ∀ {Γ : Ctx Base} {χ : ClosedFormula (ParamConst Const Γ)},
        (W : PrimeTheory Const Γ) →
        χ ∉ W.carrier →
        ∃ Ws : PrimeTheory.Saturated Const Γ,
          (∀ {ψ : ClosedFormula (ParamConst Const Γ)},
            ψ ∈ W.carrier → ψ ∈ Ws.carrier) ∧
          χ ∉ Ws.carrier) :
    RootCounterworldBridge Base Const where
  hasRootCounterworld_of_not_provable := by
    intro Δ φ hNot
    exact hasRootCounterworld_of_not_provable_of_saturate
      (Base := Base)
      (Const := Const)
      hSaturate
      hNot

/-- The corrected root witness bridge produces a direct mainline root
counterworld from ordinary non-provability. -/
theorem hasRootCounterworld_of_not_provable
    (B : RootExWitnessBridge Base Const)
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const}
    (hNot : ¬ ExtDerivation Const Δ φ) :
    HasRootCounterworld Base Const Δ φ := by
  rcases exists_root_world_saturated_of_rootExWitness_bridge
    (Base := Base)
    (Const := Const)
    (B := B)
    (Δ := Δ)
    (φ := φ)
    hNot with ⟨W, hΔ, hNotφ⟩
  exact ⟨⟨[], W, hΔ, hNotφ⟩⟩

/-- Mainline equivalence: under the corrected root witness bridge, root
counterworld existence is exactly non-provability. -/
theorem hasRootCounterworld_iff_not_provable
    (B : RootExWitnessBridge Base Const)
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const} :
    HasRootCounterworld Base Const Δ φ ↔ ¬ ExtDerivation Const Δ φ := by
  constructor
  · exact not_provable_of_hasRootCounterworld (Base := Base) (Const := Const)
  · exact hasRootCounterworld_of_not_provable (Base := Base) (Const := Const) B

/-- Compatibility layer: the older corrected witness bridge induces the more
honest direct root-counterworld bridge. -/
def RootExWitnessBridge.toRootCounterworldBridge
    (B : RootExWitnessBridge Base Const) :
    RootCounterworldBridge Base Const where
  hasRootCounterworld_of_not_provable := by
    intro Δ φ hNot
    exact hasRootCounterworld_of_not_provable
      (Base := Base)
      (Const := Const)
      B
      hNot

end ParamCompleteness

end Mettapedia.Logic.HOL
