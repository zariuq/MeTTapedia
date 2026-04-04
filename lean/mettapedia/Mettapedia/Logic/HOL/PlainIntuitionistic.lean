import Mettapedia.Logic.HOL.IntuitionisticSoundness
import Mettapedia.Logic.HOL.IntuitionisticCompleteness
import Mettapedia.Logic.HOL.ParamCompleteness
import Mettapedia.Logic.HOL.CanonicalRepresentedModel
import Mettapedia.Logic.HOL.Semantics.Reduct

namespace Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-!
# Plain Intuitionistic HOL Mainline  [MAINLINE]

This module is the public entrypoint for the plain intuitionistic-extensional
HOL metatheory.

It intentionally stays on the direct mainline:

- intuitionistic soundness for the original signature,
- the internal cumulative-Henkin completeness milestone,
- and the canonical validity/provability interface used by the future direct
  original-signature completeness proof.

The final unconditional completeness theorem
`plain_intuitionistic_completeness` will be assembled here once the
growing-domain Kripke construction in `ParamWorld.lean` / `ParamCompleteness.lean`
is complete.

It intentionally does NOT import the original-reflection reduction / obstruction
files. Those files analyze an auxiliary constant-based bridge that is useful for
diagnostics and strengthened reflection theorems, but they are not the main
route to plain intuitionistic original-signature completeness.
-/
namespace PlainIntuitionistic

/--
Original-signature semantic validity from finite assumptions in all
intuitionistic/extensional Heyting-Henkin models.
-/
def OriginalValidFrom
    (Δ : List (ClosedFormula Const))
    (φ : ClosedFormula Const) : Prop :=
  ∀ M : HeytingHenkinModel.{u, v, w} Base Const,
    HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)

/-- Plain intuitionistic soundness for closed theorems over the original signature. -/
theorem theorem_sound
    {φ : ClosedFormula Const}
    (d : ExtDerivation.Theorem Const φ)
    (M : HeytingHenkinModel.{u, v, w} Base Const) :
    HeytingHenkinModel.models M φ :=
  IntuitionisticSoundness.theorem_sound d M

/-- Ordinary derivability implies original-signature semantic validity. -/
theorem validFrom_of_provable
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const}
    (hProv : ExtDerivation Const Δ φ) :
    OriginalValidFrom (Base := Base) (Const := Const) Δ φ := by
  intro M
  simpa [OriginalValidFrom] using
    (IntuitionisticSoundness.derivation_sound
      (Base := Base)
      (Const := Const)
      (d := hProv)
      (M := M)
      (ρ := fun v => nomatch v)
      (by intro τ v; nomatch v))

/--
Internal cumulative-Henkin completeness milestone:
canonical Henkin validity is equivalent to provability in the cumulative Henkin
language.
-/
theorem canonicalHenkinValidFrom_iff_provable
    {Δ : List (ClosedFormula (HenkinConstInfinity.HInf Base Const))}
    {φ : ClosedFormula (HenkinConstInfinity.HInf Base Const)} :
    HenkinConstInfinity.CanonicalHenkinValidFrom
        (Base := Base)
        (Const := Const)
        Δ
        φ ↔
      ClosedTheorySet.Provable
        (Const := HenkinConstInfinity.HInf Base Const)
        (fun ψ => ψ ∈ Δ ∨ ψ ∈ HenkinConstInfinity.HenkinAxioms (Base := Base) (Const := Const))
        φ :=
  HenkinConstInfinity.canonicalHenkinValidFrom_iff_provable
    (Base := Base)
    (Const := Const)

/--
If an original-signature derivation is already known, its cumulative-Henkin lift
is canonically valid.
-/
theorem liftBase_canonicalHenkinValidFrom_of_provable
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const}
    (hProv : ExtDerivation Const Δ φ) :
    HenkinConstInfinity.CanonicalHenkinValidFrom
      (Base := Base)
      (Const := Const)
      (Δ.map (HenkinConstInfinity.liftBaseClosedFormula (Base := Base) (Const := Const)))
      (HenkinConstInfinity.liftBaseClosedFormula (Base := Base) (Const := Const) φ) :=
  HenkinConstInfinity.liftBase_canonicalHenkinValidFrom_of_provable
    (Base := Base)
    (Const := Const)
    hProv

/--
Original-signature semantic validity transports along the base-constant embedding
into the cumulative Henkin signature.
-/
theorem liftBase_validFrom_of_validFrom
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const}
    (hValid :
      ∀ M : HeytingHenkinModel.{u, v, w} Base Const,
        HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) :
    ∀ M : HeytingHenkinModel.{u, max u (v + 1), w}
        Base (HenkinConstInfinity.HInf Base Const),
      HeytingHenkinModel.modelsFrom M
        (Δ.map (HenkinConstInfinity.liftBaseClosedFormula (Base := Base) (Const := Const)))
        (HenkinConstInfinity.liftBaseClosedFormula (Base := Base) (Const := Const) φ)
        (fun v => nomatch v) := by
  intro M
  change
    HeytingHenkinModel.modelsFrom M
      (Δ.map (mapConst (fun {τ} c => HenkinConstInfinity.base c)))
      (mapConst (fun {τ} c => HenkinConstInfinity.base c) φ)
      (fun v => nomatch v)
  let Mred : HeytingHenkinModel.{u, v, w} Base Const :=
    HeytingHenkinModel.reduct
      (Base := Base)
      (Const := Const)
      (Const' := HenkinConstInfinity.HInf Base Const)
      (fun {τ} c => HenkinConstInfinity.base c)
      M
  have hBase := hValid Mred
  exact
    (HeytingHenkinModel.modelsFrom_mapConst_iff
      (Base := Base)
      (Const := Const)
      (Const' := HenkinConstInfinity.HInf Base Const)
      (fun {τ} c => HenkinConstInfinity.base c)
      M
      Δ
      φ
      (fun v => nomatch v)).mp hBase

/--
Direct growing-domain endgame reduction:
if a saturated root counterworld can always be turned into a standard
`HeytingHenkinModel` countermodel, then the corrected root witness bridge already
implies original-signature completeness.

Positive example:
this is the intended mainline interface for the `ParamWorld` / `ParamTruthLemma`
route.

Negative example:
this does NOT assume the too-strong lifted cumulative-Henkin non-provability
principle from the auxiliary obstruction files.
-/

theorem provable_of_rootCountermodel
    (hCountermodel :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ¬ ExtDerivation Const Δ φ →
          ∃ M : HeytingHenkinModel.{u, v, w} Base Const,
            ¬ HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v))
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const}
    (hValid :
      ∀ M : HeytingHenkinModel.{u, v, w} Base Const,
        HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) :
    ExtDerivation Const Δ φ := by
  classical
  by_contra hNot
  rcases hCountermodel hNot with ⟨M, hM⟩
  exact hM (hValid M)

theorem validFrom_iff_provable_of_rootCountermodel
    (hCountermodel :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ¬ ExtDerivation Const Δ φ →
          ∃ M : HeytingHenkinModel.{u, v, w} Base Const,
            ¬ HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v))
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    (∀ M : HeytingHenkinModel.{u, v, w} Base Const,
      HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) ↔
      ExtDerivation Const Δ φ := by
  constructor
  · intro hValid
    exact provable_of_rootCountermodel
      (Base := Base)
      (Const := Const)
      hCountermodel
      hValid
  · exact validFrom_of_provable (Base := Base) (Const := Const)

theorem provable_of_rootCounterworld_bridge_and_rootCounterworld_countermodel
    (R : ParamCompleteness.RootCounterworldBridge Base Const)
    (hCounter :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ParamCompleteness.RootCounterworld Base Const Δ φ →
          ∃ M : HeytingHenkinModel.{u, v, w} Base Const,
            ¬ HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v))
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const}
    (hValid :
      ∀ M : HeytingHenkinModel.{u, v, w} Base Const,
        HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) :
    ExtDerivation Const Δ φ := by
  exact provable_of_rootCountermodel
    (Base := Base)
    (Const := Const)
    (hCountermodel := by
      intro Δ φ hNot
      let C : ParamCompleteness.RootCounterworld Base Const Δ φ :=
        Classical.choice (R.hasRootCounterworld_of_not_provable hNot)
      exact hCounter C)
    hValid

theorem validFrom_iff_provable_of_rootCounterworld_bridge_and_rootCounterworld_countermodel
    (R : ParamCompleteness.RootCounterworldBridge Base Const)
    (hCounter :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ParamCompleteness.RootCounterworld Base Const Δ φ →
          ∃ M : HeytingHenkinModel.{u, v, w} Base Const,
            ¬ HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v))
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    (∀ M : HeytingHenkinModel.{u, v, w} Base Const,
      HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) ↔
      ExtDerivation Const Δ φ := by
  constructor
  · intro hValid
    exact provable_of_rootCounterworld_bridge_and_rootCounterworld_countermodel
      (Base := Base)
      (Const := Const)
      R
      hCounter
      hValid
  · exact validFrom_of_provable (Base := Base) (Const := Const)

/--
Current strongest public mainline theorem at the direct root-counterworld
boundary.

The only remaining premise is the honest semantic export from parameterized
root counterworlds to standard `HeytingHenkinModel` countermodels.
-/
theorem plain_intuitionistic_completeness_of_rootCounterworld_bridge_and_rootCounterworld_countermodel
    (R : ParamCompleteness.RootCounterworldBridge Base Const)
    (hCounter :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ParamCompleteness.RootCounterworld Base Const Δ φ →
          ∃ M : HeytingHenkinModel.{u, v, w} Base Const,
            ¬ HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v))
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    (∀ M : HeytingHenkinModel.{u, v, w} Base Const,
      HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) ↔
      ExtDerivation Const Δ φ := by
  exact
    validFrom_iff_provable_of_rootCounterworld_bridge_and_rootCounterworld_countermodel
      (Base := Base)
      (Const := Const)
      R
      hCounter
      (Δ := Δ)
      (φ := φ)

/--
Current cleanest public theorem surface for the direct growing-domain route:
a proof-theoretic root-counterworld bridge plus a semantic root-countermodel
bridge yield plain intuitionistic completeness.
-/
theorem plain_intuitionistic_completeness_of_rootCounterworld_bridges
    (R : ParamCompleteness.RootCounterworldBridge Base Const)
    (C : ParamCompleteness.RootCounterworldCountermodelBridge.{u, v, w} Base Const)
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    (∀ M : HeytingHenkinModel.{u, v, w} Base Const,
      HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) ↔
      ExtDerivation Const Δ φ := by
  exact
    plain_intuitionistic_completeness_of_rootCounterworld_bridge_and_rootCounterworld_countermodel
      (Base := Base)
      (Const := Const)
      R
      (hCounter := by
        intro Δ φ Cw
        exact C.countermodel_of_rootCounterworld Cw)
      (Δ := Δ)
      (φ := φ)

theorem provable_of_rootSaturation_bridge_and_rootCounterworld_countermodel
    (hCounter :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ParamCompleteness.RootCounterworld Base Const Δ φ →
          ∃ M : HeytingHenkinModel.{u, v, w} Base Const,
            ¬ HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v))
    (B : RootSaturationBridge Base Const)
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const}
    (hValid :
      ∀ M : HeytingHenkinModel.{u, v, w} Base Const,
        HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) :
    ExtDerivation Const Δ φ := by
  exact provable_of_rootCounterworld_bridge_and_rootCounterworld_countermodel
    (Base := Base)
    (Const := Const)
    (R := ParamCompleteness.RootSaturationBridge.toRootCounterworldBridge
      (Base := Base)
      (Const := Const)
      B)
    hCounter
    hValid

theorem validFrom_iff_provable_of_rootSaturation_bridge_and_rootCounterworld_countermodel
    (hCounter :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ParamCompleteness.RootCounterworld Base Const Δ φ →
          ∃ M : HeytingHenkinModel.{u, v, w} Base Const,
            ¬ HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v))
    (B : RootSaturationBridge Base Const)
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    (∀ M : HeytingHenkinModel.{u, v, w} Base Const,
      HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) ↔
      ExtDerivation Const Δ φ := by
  exact validFrom_iff_provable_of_rootCounterworld_bridge_and_rootCounterworld_countermodel
    (Base := Base)
    (Const := Const)
    (R := ParamCompleteness.RootSaturationBridge.toRootCounterworldBridge
      (Base := Base)
      (Const := Const)
      B)
    hCounter

/--
Current strongest public theorem at the root-saturation boundary.

This removes the older source witness-shell packaging from the public statement;
the only remaining premises are the honest saturation bridge and the semantic
export from root counterworlds.
-/
theorem plain_intuitionistic_completeness_of_rootSaturation_bridge_and_rootCounterworld_countermodel
    (hCounter :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ParamCompleteness.RootCounterworld Base Const Δ φ →
          ∃ M : HeytingHenkinModel.{u, v, w} Base Const,
            ¬ HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v))
    (B : RootSaturationBridge Base Const)
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    (∀ M : HeytingHenkinModel.{u, v, w} Base Const,
      HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) ↔
      ExtDerivation Const Δ φ := by
  exact validFrom_iff_provable_of_rootSaturation_bridge_and_rootCounterworld_countermodel
    (Base := Base)
    (Const := Const)
    hCounter
    B

theorem provable_of_saturate_and_rootCounterworld_countermodel
    (hSaturate :
      ∀ {Γ : Ctx Base} {χ : ClosedFormula (ParamConst Const Γ)},
        (W : PrimeTheory Const Γ) →
        χ ∉ W.carrier →
        ∃ Ws : PrimeTheory.Saturated Const Γ,
          (∀ {ψ : ClosedFormula (ParamConst Const Γ)},
            ψ ∈ W.carrier → ψ ∈ Ws.carrier) ∧
          χ ∉ Ws.carrier)
    (hCounter :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ParamCompleteness.RootCounterworld Base Const Δ φ →
          ∃ M : HeytingHenkinModel.{u, v, w} Base Const,
            ¬ HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v))
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const}
    (hValid :
      ∀ M : HeytingHenkinModel.{u, v, w} Base Const,
        HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) :
    ExtDerivation Const Δ φ := by
  exact provable_of_rootCounterworld_bridge_and_rootCounterworld_countermodel
    (Base := Base)
    (Const := Const)
    (R := ParamCompleteness.rootCounterworldBridgeOfSaturate
      (Base := Base)
      (Const := Const)
      hSaturate)
    hCounter
    hValid

theorem validFrom_iff_provable_of_saturate_and_rootCounterworld_countermodel
    (hSaturate :
      ∀ {Γ : Ctx Base} {χ : ClosedFormula (ParamConst Const Γ)},
        (W : PrimeTheory Const Γ) →
        χ ∉ W.carrier →
        ∃ Ws : PrimeTheory.Saturated Const Γ,
          (∀ {ψ : ClosedFormula (ParamConst Const Γ)},
            ψ ∈ W.carrier → ψ ∈ Ws.carrier) ∧
          χ ∉ Ws.carrier)
    (hCounter :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ParamCompleteness.RootCounterworld Base Const Δ φ →
          ∃ M : HeytingHenkinModel.{u, v, w} Base Const,
            ¬ HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v))
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    (∀ M : HeytingHenkinModel.{u, v, w} Base Const,
      HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) ↔
      ExtDerivation Const Δ φ := by
  exact validFrom_iff_provable_of_rootCounterworld_bridge_and_rootCounterworld_countermodel
    (Base := Base)
    (Const := Const)
    (R := ParamCompleteness.rootCounterworldBridgeOfSaturate
      (Base := Base)
      (Const := Const)
      hSaturate)
    hCounter

/--
Current cleanest public theorem at the saturation-preserving extension
boundary.

The remaining mainline gap is now exposed as one specific theorem:
prime theories must admit saturation preserving omission of a designated
formula.
-/
theorem plain_intuitionistic_completeness_of_saturate_and_rootCounterworld_countermodel
    (hSaturate :
      ∀ {Γ : Ctx Base} {χ : ClosedFormula (ParamConst Const Γ)},
        (W : PrimeTheory Const Γ) →
        χ ∉ W.carrier →
        ∃ Ws : PrimeTheory.Saturated Const Γ,
          (∀ {ψ : ClosedFormula (ParamConst Const Γ)},
            ψ ∈ W.carrier → ψ ∈ Ws.carrier) ∧
          χ ∉ Ws.carrier)
    (hCounter :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ParamCompleteness.RootCounterworld Base Const Δ φ →
          ∃ M : HeytingHenkinModel.{u, v, w} Base Const,
            ¬ HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v))
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    (∀ M : HeytingHenkinModel.{u, v, w} Base Const,
      HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) ↔
      ExtDerivation Const Δ φ := by
  exact validFrom_iff_provable_of_saturate_and_rootCounterworld_countermodel
    (Base := Base)
    (Const := Const)
    hSaturate
    hCounter

theorem provable_of_saturationBridge_and_rootCounterworld_countermodel
    (B : PrimeTheory.SaturationBridge Base Const)
    (hCounter :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ParamCompleteness.RootCounterworld Base Const Δ φ →
          ∃ M : HeytingHenkinModel.{u, v, w} Base Const,
            ¬ HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v))
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const}
    (hValid :
      ∀ M : HeytingHenkinModel.{u, v, w} Base Const,
        HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) :
    ExtDerivation Const Δ φ := by
  exact provable_of_rootCounterworld_bridge_and_rootCounterworld_countermodel
    (Base := Base)
    (Const := Const)
    (R := ParamCompleteness.PrimeTheory.SaturationBridge.toRootCounterworldBridge
      (Base := Base)
      (Const := Const)
      B)
    hCounter
    hValid

theorem validFrom_iff_provable_of_saturationBridge_and_rootCounterworld_countermodel
    (B : PrimeTheory.SaturationBridge Base Const)
    (hCounter :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ParamCompleteness.RootCounterworld Base Const Δ φ →
          ∃ M : HeytingHenkinModel.{u, v, w} Base Const,
            ¬ HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v))
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    (∀ M : HeytingHenkinModel.{u, v, w} Base Const,
      HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) ↔
      ExtDerivation Const Δ φ := by
  exact validFrom_iff_provable_of_rootCounterworld_bridge_and_rootCounterworld_countermodel
    (Base := Base)
    (Const := Const)
    (R := ParamCompleteness.PrimeTheory.SaturationBridge.toRootCounterworldBridge
      (Base := Base)
      (Const := Const)
      B)
    hCounter

/--
Current strongest public theorem at the arbitrary-context saturation-bridge
boundary.

The only remaining premises are now the exact local saturation bridge and the
semantic export from root counterworlds.
-/
theorem plain_intuitionistic_completeness_of_saturationBridge_and_rootCounterworld_countermodel
    (B : PrimeTheory.SaturationBridge Base Const)
    (hCounter :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ParamCompleteness.RootCounterworld Base Const Δ φ →
          ∃ M : HeytingHenkinModel.{u, v, w} Base Const,
            ¬ HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v))
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    (∀ M : HeytingHenkinModel.{u, v, w} Base Const,
      HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) ↔
      ExtDerivation Const Δ φ := by
  exact validFrom_iff_provable_of_saturationBridge_and_rootCounterworld_countermodel
    (Base := Base)
    (Const := Const)
    B
    hCounter

theorem provable_of_rootExWitness_bridge_and_rootCounterworld_countermodel
    (hCounter :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ParamCompleteness.RootCounterworld Base Const Δ φ →
          ∃ M : HeytingHenkinModel.{u, v, w} Base Const,
            ¬ HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v))
    (B : RootExWitnessBridge Base Const)
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const}
    (hValid :
      ∀ M : HeytingHenkinModel.{u, v, w} Base Const,
        HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) :
    ExtDerivation Const Δ φ := by
  exact provable_of_rootCounterworld_bridge_and_rootCounterworld_countermodel
    (Base := Base)
    (Const := Const)
    (R := ParamCompleteness.RootExWitnessBridge.toRootCounterworldBridge
      (Base := Base)
      (Const := Const)
      B)
    hCounter
    hValid

theorem provable_of_rootExWitness_bridge_and_root_countermodel
    (hCounter :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        (∃ Γ : Ctx Base,
            ∃ W : PrimeTheory.Saturated Const Γ,
              (∀ ψ, ψ ∈ Δ → liftParamFormula Γ ψ ∈ W.carrier) ∧
              liftParamFormula Γ φ ∉ W.carrier) →
          ∃ M : HeytingHenkinModel.{u, v, w} Base Const,
            ¬ HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v))
    (B : RootExWitnessBridge Base Const)
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const}
    (hValid :
      ∀ M : HeytingHenkinModel.{u, v, w} Base Const,
        HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) :
    ExtDerivation Const Δ φ := by
  exact provable_of_rootExWitness_bridge_and_rootCounterworld_countermodel
    (Base := Base)
    (Const := Const)
    (hCounter := by
      intro Δ φ C
      exact hCounter C.to_exists_world)
    B
    hValid

/--
The direct growing-domain completeness reduction stated as validity iff
provability at the corrected root witness boundary.
-/
theorem validFrom_iff_provable_of_rootExWitness_bridge_and_rootCounterworld_countermodel
    (hCounter :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ParamCompleteness.RootCounterworld Base Const Δ φ →
          ∃ M : HeytingHenkinModel.{u, v, w} Base Const,
            ¬ HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v))
    (B : RootExWitnessBridge Base Const)
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    (∀ M : HeytingHenkinModel.{u, v, w} Base Const,
      HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) ↔
      ExtDerivation Const Δ φ := by
  exact validFrom_iff_provable_of_rootCounterworld_bridge_and_rootCounterworld_countermodel
    (Base := Base)
    (Const := Const)
    (R := ParamCompleteness.RootExWitnessBridge.toRootCounterworldBridge
      (Base := Base)
      (Const := Const)
      B)
    hCounter

theorem validFrom_iff_provable_of_rootExWitness_bridge_and_root_countermodel
    (hCounter :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        (∃ Γ : Ctx Base,
            ∃ W : PrimeTheory.Saturated Const Γ,
              (∀ ψ, ψ ∈ Δ → liftParamFormula Γ ψ ∈ W.carrier) ∧
              liftParamFormula Γ φ ∉ W.carrier) →
          ∃ M : HeytingHenkinModel.{u, v, w} Base Const,
            ¬ HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v))
    (B : RootExWitnessBridge Base Const)
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    (∀ M : HeytingHenkinModel.{u, v, w} Base Const,
      HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) ↔
      ExtDerivation Const Δ φ := by
  exact validFrom_iff_provable_of_rootExWitness_bridge_and_rootCounterworld_countermodel
    (Base := Base)
    (Const := Const)
    (hCounter := by
      intro Δ φ C
      exact hCounter C.to_exists_world)
    B

/--
If a lifted canonical counterworld can always be turned into a standard
`HeytingHenkinModel` countermodel, then the remaining plain-completeness gap can
be stated entirely at the canonical-world layer.

Positive example:
the canonical-world counterexample theorem in
`CanonicalModel.lean` is enough once such a bridge is available.

Negative example:
without this bridge, the existing canonical counterworld machinery does not yet
directly discharge `OriginalValidFrom`.
-/
theorem liftBase_countermodel_of_canonical_counterworld
    (hBridge :
      ∀ {Δ : List (ClosedFormula (HenkinConstInfinity.HInf Base Const))}
        {φ : ClosedFormula (HenkinConstInfinity.HInf Base Const)},
        (∃ W : HenkinConstInfinity.World Base Const,
            W ∈ HenkinConstInfinity.contextDenote
                  (Base := Base)
                  (Const := Const)
                  Δ
                  (HenkinConstInfinity.emptyClosedSubst Base Const) ∧
            ¬ HenkinConstInfinity.modelsFrom
                  (Base := Base)
                  (Const := Const)
                  Δ
                  φ
                  (HenkinConstInfinity.emptyClosedSubst Base Const)) →
          ∃ M : HeytingHenkinModel.{u, max u (v + 1), w}
              Base (HenkinConstInfinity.HInf Base Const),
            ¬ HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v))
    (hCanonicalCounter :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ¬ ExtDerivation Const Δ φ →
        ∃ W : HenkinConstInfinity.World Base Const,
          W ∈ HenkinConstInfinity.contextDenote
                (Base := Base)
                (Const := Const)
                (Δ.map
                  (HenkinConstInfinity.liftBaseClosedFormula
                    (Base := Base) (Const := Const)))
                (HenkinConstInfinity.emptyClosedSubst Base Const) ∧
          ¬ HenkinConstInfinity.modelsFrom
                (Base := Base)
                (Const := Const)
                (Δ.map
                  (HenkinConstInfinity.liftBaseClosedFormula
                    (Base := Base) (Const := Const)))
                (HenkinConstInfinity.liftBaseClosedFormula
                  (Base := Base) (Const := Const) φ)
                (HenkinConstInfinity.emptyClosedSubst Base Const)) :
    ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
      ¬ ExtDerivation Const Δ φ →
      ∃ M : HeytingHenkinModel.{u, max u (v + 1), w}
          Base (HenkinConstInfinity.HInf Base Const),
        ¬ HeytingHenkinModel.modelsFrom M
            (Δ.map
              (HenkinConstInfinity.liftBaseClosedFormula
                (Base := Base) (Const := Const)))
            (HenkinConstInfinity.liftBaseClosedFormula
              (Base := Base) (Const := Const) φ)
            (fun v => nomatch v) := by
  intro Δ φ hNot
  rcases hCanonicalCounter hNot with ⟨W, hWΔ, hWNot⟩
  exact hBridge ⟨W, hWΔ, hWNot⟩

/--
Direct represented-canonical bridge:
lifted cumulative-Henkin non-provability yields an explicit canonical Henkin
counterexample, and the represented canonical package exports that
counterexample to a standard `HeytingHenkinModel`.
-/
theorem liftBase_countermodel_of_liftBase_notProvable_via_canonicalRepresented
    (hLiftNotProvable :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ¬ ExtDerivation Const Δ φ →
          ¬ ClosedTheorySet.Provable
              (Const := HenkinConstInfinity.HInf Base Const)
              (fun ψ =>
                ψ ∈ Δ.map
                  (HenkinConstInfinity.liftBaseClosedFormula
                    (Base := Base) (Const := Const)) ∨
                  ψ ∈ HenkinConstInfinity.HenkinAxioms
                    (Base := Base) (Const := Const))
              (HenkinConstInfinity.liftBaseClosedFormula
                (Base := Base) (Const := Const) φ)) :
    ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
      ¬ ExtDerivation Const Δ φ →
        ∃ M : HeytingHenkinModel.{u, max u (v + 1), v + 1}
            Base (HenkinConstInfinity.HInf Base Const),
          ¬ HeytingHenkinModel.modelsFrom M
              (Δ.map
                (HenkinConstInfinity.liftBaseClosedFormula
                  (Base := Base) (Const := Const)))
              (HenkinConstInfinity.liftBaseClosedFormula
                (Base := Base) (Const := Const) φ)
              (fun v => nomatch v) := by
  intro Δ φ hNot
  rcases HenkinConstInfinity.exists_canonical_counterworld_of_list_notProvable
      (Base := Base)
      (Const := Const)
      (Δ := Δ.map
        (HenkinConstInfinity.liftBaseClosedFormula
          (Base := Base) (Const := Const)))
      (φ := HenkinConstInfinity.liftBaseClosedFormula
        (Base := Base) (Const := Const) φ)
      (hNot := hLiftNotProvable hNot) with
    ⟨W, hWΔ, hWHenkin, hWNotφ⟩
  have hWCtx :
      W ∈ HenkinConstInfinity.contextDenote
            (Base := Base)
            (Const := Const)
            (Δ.map
              (HenkinConstInfinity.liftBaseClosedFormula
                (Base := Base) (Const := Const)))
            (HenkinConstInfinity.emptyClosedSubst Base Const) := by
    apply (HenkinConstInfinity.mem_contextDenote_empty_iff
      (Base := Base)
      (Const := Const)
      (W := W)
      (Δ := Δ.map
        (HenkinConstInfinity.liftBaseClosedFormula
          (Base := Base) (Const := Const)))).2
    intro ψ hψ
    exact (HenkinConstInfinity.mem_denoteFormula_empty_iff
      (Base := Base)
      (Const := Const)
      (W := W)
      (φ := ψ)).1 <|
      hWΔ hψ
  exact
    HenkinConstInfinity.exists_countermodel_of_henkin_counterexample
      (Base := Base)
      (Const := Const)
      (Δ := Δ.map
        (HenkinConstInfinity.liftBaseClosedFormula
          (Base := Base) (Const := Const)))
      (φ := HenkinConstInfinity.liftBaseClosedFormula
        (Base := Base) (Const := Const) φ)
      ⟨⟨W, hWHenkin⟩, hWCtx, hWNotφ⟩

/--
The represented-canonical lifted countermodel theorem descends back to an
original-signature countermodel by reduct along the base embedding.
-/
theorem countermodel_of_liftBase_notProvable_via_canonicalRepresented
    (hLiftNotProvable :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ¬ ExtDerivation Const Δ φ →
          ¬ ClosedTheorySet.Provable
              (Const := HenkinConstInfinity.HInf Base Const)
              (fun ψ =>
                ψ ∈ Δ.map
                  (HenkinConstInfinity.liftBaseClosedFormula
                    (Base := Base) (Const := Const)) ∨
                  ψ ∈ HenkinConstInfinity.HenkinAxioms
                    (Base := Base) (Const := Const))
              (HenkinConstInfinity.liftBaseClosedFormula
                (Base := Base) (Const := Const) φ)) :
    ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
      ¬ ExtDerivation Const Δ φ →
        ∃ M : HeytingHenkinModel.{u, v, v + 1} Base Const,
          ¬ HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v) := by
  intro Δ φ hNot
  rcases liftBase_countermodel_of_liftBase_notProvable_via_canonicalRepresented
      (Base := Base)
      (Const := Const)
      hLiftNotProvable
      hNot with
    ⟨M, hM⟩
  let Mred : HeytingHenkinModel.{u, v, v + 1} Base Const :=
    HeytingHenkinModel.reduct
      (Base := Base)
      (Const := Const)
      (Const' := HenkinConstInfinity.HInf Base Const)
      (fun {τ} c => HenkinConstInfinity.base c)
      M
  refine ⟨Mred, ?_⟩
  intro hModels
  exact hM <|
    (HeytingHenkinModel.modelsFrom_mapConst_iff
      (Base := Base)
      (Const := Const)
      (Const' := HenkinConstInfinity.HInf Base Const)
      (fun {τ} c => HenkinConstInfinity.base c)
      M
      Δ
      φ
      (fun v => nomatch v)).mp hModels

/--
Stronger diagnostic reduction:
if original non-provability can be turned into non-provability of the lifted
cumulative-Henkin sequent, then the existing canonical countermodel theorem
already provides the lifted canonical counterworld.

Positive example:
this isolates one tempting proof-theoretic route very explicitly.

Negative example:
this is NOT the intended general mainline theorem boundary, because cumulative
Henkinization genuinely adds fresh witnesses; the empty-signature obstruction
shows that such a lifted non-provability principle is too strong in general.
-/
theorem liftBase_canonical_counterworld_of_liftBase_notProvable
    (hLiftNotProvable :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ¬ ExtDerivation Const Δ φ →
          ¬ ClosedTheorySet.Provable
              (Const := HenkinConstInfinity.HInf Base Const)
              (fun ψ =>
                ψ ∈ Δ.map
                  (HenkinConstInfinity.liftBaseClosedFormula
                    (Base := Base) (Const := Const)) ∨
                  ψ ∈ HenkinConstInfinity.HenkinAxioms
                    (Base := Base) (Const := Const))
              (HenkinConstInfinity.liftBaseClosedFormula
                (Base := Base) (Const := Const) φ)) :
    ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
      ¬ ExtDerivation Const Δ φ →
        ∃ W : HenkinConstInfinity.World Base Const,
          W ∈ HenkinConstInfinity.contextDenote
                (Base := Base)
                (Const := Const)
                (Δ.map
                  (HenkinConstInfinity.liftBaseClosedFormula
                    (Base := Base) (Const := Const)))
                (HenkinConstInfinity.emptyClosedSubst Base Const) ∧
          ¬ HenkinConstInfinity.modelsFrom
                (Base := Base)
                (Const := Const)
                (Δ.map
                  (HenkinConstInfinity.liftBaseClosedFormula
                    (Base := Base) (Const := Const)))
                (HenkinConstInfinity.liftBaseClosedFormula
                  (Base := Base) (Const := Const) φ)
                (HenkinConstInfinity.emptyClosedSubst Base Const) := by
  intro Δ φ hNot
  exact HenkinConstInfinity.exists_canonical_countermodel_of_list_notProvable
    (Base := Base)
    (Const := Const)
    (Δ := Δ.map
      (HenkinConstInfinity.liftBaseClosedFormula
        (Base := Base) (Const := Const)))
    (φ := HenkinConstInfinity.liftBaseClosedFormula
      (Base := Base) (Const := Const) φ)
    (hNot := hLiftNotProvable hNot)

/--
Route 1 endgame reduction:
if every non-derivable original sequent has a standard cumulative-Henkin
countermodel for its lifted form, then original-signature semantic validity
already implies derivability.

This is the direct Henkin path for plain intuitionistic completeness:
the remaining gap is a lifted countermodel theorem, not any reflection theorem.
-/
theorem provable_of_liftBase_countermodel
    (hCounter :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ¬ ExtDerivation Const Δ φ →
        ∃ M : HeytingHenkinModel.{u, max u (v + 1), w}
            Base (HenkinConstInfinity.HInf Base Const),
          ¬ HeytingHenkinModel.modelsFrom M
              (Δ.map
                (HenkinConstInfinity.liftBaseClosedFormula
                  (Base := Base) (Const := Const)))
              (HenkinConstInfinity.liftBaseClosedFormula
                (Base := Base) (Const := Const) φ)
              (fun v => nomatch v))
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const}
    (hValid :
      ∀ M : HeytingHenkinModel.{u, v, w} Base Const,
        HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) :
    ExtDerivation Const Δ φ := by
  classical
  by_contra hNot
  rcases hCounter hNot with ⟨M, hM⟩
  have hLift :
      ∀ M : HeytingHenkinModel.{u, max u (v + 1), w}
          Base (HenkinConstInfinity.HInf Base Const),
        HeytingHenkinModel.modelsFrom M
          (Δ.map
            (HenkinConstInfinity.liftBaseClosedFormula
              (Base := Base) (Const := Const)))
          (HenkinConstInfinity.liftBaseClosedFormula
            (Base := Base) (Const := Const) φ)
          (fun v => nomatch v) :=
    liftBase_validFrom_of_validFrom (Base := Base) (Const := Const) hValid
  exact hM (hLift M)

/--
Plain completeness can also be reduced in two explicit Henkin-style steps:

1. produce a lifted canonical counterworld from original non-provability;
2. bridge that canonical counterworld to a standard `HeytingHenkinModel`.

This keeps the remaining endgame theorem boundary honest.
-/
theorem provable_of_liftBase_canonical_counterworld
    (hBridge :
      ∀ {Δ : List (ClosedFormula (HenkinConstInfinity.HInf Base Const))}
        {φ : ClosedFormula (HenkinConstInfinity.HInf Base Const)},
        (∃ W : HenkinConstInfinity.World Base Const,
            W ∈ HenkinConstInfinity.contextDenote
                  (Base := Base)
                  (Const := Const)
                  Δ
                  (HenkinConstInfinity.emptyClosedSubst Base Const) ∧
            ¬ HenkinConstInfinity.modelsFrom
                  (Base := Base)
                  (Const := Const)
                  Δ
                  φ
                  (HenkinConstInfinity.emptyClosedSubst Base Const)) →
          ∃ M : HeytingHenkinModel.{u, max u (v + 1), w}
              Base (HenkinConstInfinity.HInf Base Const),
            ¬ HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v))
    (hCanonicalCounter :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ¬ ExtDerivation Const Δ φ →
        ∃ W : HenkinConstInfinity.World Base Const,
          W ∈ HenkinConstInfinity.contextDenote
                (Base := Base)
                (Const := Const)
                (Δ.map
                  (HenkinConstInfinity.liftBaseClosedFormula
                    (Base := Base) (Const := Const)))
                (HenkinConstInfinity.emptyClosedSubst Base Const) ∧
          ¬ HenkinConstInfinity.modelsFrom
                (Base := Base)
                (Const := Const)
                (Δ.map
                  (HenkinConstInfinity.liftBaseClosedFormula
                    (Base := Base) (Const := Const)))
                (HenkinConstInfinity.liftBaseClosedFormula
                  (Base := Base) (Const := Const) φ)
                (HenkinConstInfinity.emptyClosedSubst Base Const))
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const}
    (hValid :
      ∀ M : HeytingHenkinModel.{u, v, w} Base Const,
        HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) :
    ExtDerivation Const Δ φ := by
  exact
    provable_of_liftBase_countermodel
      (Base := Base)
      (Const := Const)
      (liftBase_countermodel_of_canonical_counterworld
        (Base := Base)
        (Const := Const)
        hBridge
        hCanonicalCounter)
      hValid

/--
Mainline completeness reduction at the fully split Henkin boundary:

1. original non-provability implies lifted cumulative-Henkin non-provability;
2. lifted canonical counterworlds can be bridged to standard
   `HeytingHenkinModel`s.

This is the repo's current direct Route 1 endgame statement.
-/
theorem provable_of_liftBase_notProvable_and_canonical_counterworld
    (hBridge :
      ∀ {Δ : List (ClosedFormula (HenkinConstInfinity.HInf Base Const))}
        {φ : ClosedFormula (HenkinConstInfinity.HInf Base Const)},
        (∃ W : HenkinConstInfinity.World Base Const,
            W ∈ HenkinConstInfinity.contextDenote
                  (Base := Base)
                  (Const := Const)
                  Δ
                  (HenkinConstInfinity.emptyClosedSubst Base Const) ∧
            ¬ HenkinConstInfinity.modelsFrom
                  (Base := Base)
                  (Const := Const)
                  Δ
                  φ
                  (HenkinConstInfinity.emptyClosedSubst Base Const)) →
          ∃ M : HeytingHenkinModel.{u, max u (v + 1), w}
              Base (HenkinConstInfinity.HInf Base Const),
            ¬ HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v))
    (hLiftNotProvable :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ¬ ExtDerivation Const Δ φ →
          ¬ ClosedTheorySet.Provable
              (Const := HenkinConstInfinity.HInf Base Const)
              (fun ψ =>
                ψ ∈ Δ.map
                  (HenkinConstInfinity.liftBaseClosedFormula
                    (Base := Base) (Const := Const)) ∨
                  ψ ∈ HenkinConstInfinity.HenkinAxioms
                    (Base := Base) (Const := Const))
              (HenkinConstInfinity.liftBaseClosedFormula
                (Base := Base) (Const := Const) φ))
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const}
    (hValid :
      ∀ M : HeytingHenkinModel.{u, v, w} Base Const,
        HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) :
    ExtDerivation Const Δ φ := by
  exact
    provable_of_liftBase_canonical_counterworld
      (Base := Base)
      (Const := Const)
      hBridge
      (liftBase_canonical_counterworld_of_liftBase_notProvable
        (Base := Base)
        (Const := Const)
        hLiftNotProvable)
      hValid

/--
The fully split Henkin endgame, stated as validity iff provability.
-/
theorem validFrom_iff_provable_of_liftBase_notProvable_and_canonical_counterworld
    (hBridge :
      ∀ {Δ : List (ClosedFormula (HenkinConstInfinity.HInf Base Const))}
        {φ : ClosedFormula (HenkinConstInfinity.HInf Base Const)},
        (∃ W : HenkinConstInfinity.World Base Const,
            W ∈ HenkinConstInfinity.contextDenote
                  (Base := Base)
                  (Const := Const)
                  Δ
                  (HenkinConstInfinity.emptyClosedSubst Base Const) ∧
            ¬ HenkinConstInfinity.modelsFrom
                  (Base := Base)
                  (Const := Const)
                  Δ
                  φ
                  (HenkinConstInfinity.emptyClosedSubst Base Const)) →
          ∃ M : HeytingHenkinModel.{u, max u (v + 1), w}
              Base (HenkinConstInfinity.HInf Base Const),
            ¬ HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v))
    (hLiftNotProvable :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ¬ ExtDerivation Const Δ φ →
          ¬ ClosedTheorySet.Provable
              (Const := HenkinConstInfinity.HInf Base Const)
              (fun ψ =>
                ψ ∈ Δ.map
                  (HenkinConstInfinity.liftBaseClosedFormula
                    (Base := Base) (Const := Const)) ∨
                  ψ ∈ HenkinConstInfinity.HenkinAxioms
                    (Base := Base) (Const := Const))
              (HenkinConstInfinity.liftBaseClosedFormula
                (Base := Base) (Const := Const) φ))
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    (∀ M : HeytingHenkinModel.{u, v, w} Base Const,
      HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) ↔
      ExtDerivation Const Δ φ := by
  constructor
  · intro hValid
    exact
      provable_of_liftBase_notProvable_and_canonical_counterworld
        (Base := Base)
        (Const := Const)
        hBridge
        hLiftNotProvable
        hValid
  · exact validFrom_of_provable (Base := Base) (Const := Const)

/--
Represented-canonical version of the split Henkin endgame: the only remaining
input is the lifted non-provability theorem.
-/
theorem provable_of_liftBase_notProvable_via_canonicalRepresented
    (hLiftNotProvable :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ¬ ExtDerivation Const Δ φ →
          ¬ ClosedTheorySet.Provable
              (Const := HenkinConstInfinity.HInf Base Const)
              (fun ψ =>
                ψ ∈ Δ.map
                  (HenkinConstInfinity.liftBaseClosedFormula
                    (Base := Base) (Const := Const)) ∨
                  ψ ∈ HenkinConstInfinity.HenkinAxioms
                    (Base := Base) (Const := Const))
              (HenkinConstInfinity.liftBaseClosedFormula
                (Base := Base) (Const := Const) φ))
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const}
    (hValid :
      ∀ M : HeytingHenkinModel.{u, v, v + 1} Base Const,
        HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) :
    ExtDerivation Const Δ φ := by
  exact
    provable_of_liftBase_countermodel
      (Base := Base)
      (Const := Const)
      (hCounter :=
        liftBase_countermodel_of_liftBase_notProvable_via_canonicalRepresented
          (Base := Base)
          (Const := Const)
          hLiftNotProvable)
      hValid

/--
Represented-canonical split Henkin completeness reduction stated as validity iff
provability.
-/
theorem validFrom_iff_provable_of_liftBase_notProvable_via_canonicalRepresented
    (hLiftNotProvable :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ¬ ExtDerivation Const Δ φ →
          ¬ ClosedTheorySet.Provable
              (Const := HenkinConstInfinity.HInf Base Const)
              (fun ψ =>
                ψ ∈ Δ.map
                  (HenkinConstInfinity.liftBaseClosedFormula
                    (Base := Base) (Const := Const)) ∨
                  ψ ∈ HenkinConstInfinity.HenkinAxioms
                    (Base := Base) (Const := Const))
              (HenkinConstInfinity.liftBaseClosedFormula
                (Base := Base) (Const := Const) φ))
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    (∀ M : HeytingHenkinModel.{u, v, v + 1} Base Const,
      HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) ↔
      ExtDerivation Const Δ φ := by
  constructor
  · intro hValid
    exact
      provable_of_liftBase_notProvable_via_canonicalRepresented
        (Base := Base)
        (Const := Const)
        hLiftNotProvable
        hValid
  · exact validFrom_of_provable (Base := Base) (Const := Const)

/--
Current strongest public completeness theorem on the represented-canonical
Route 1 surface.

The semantic/export side is fully discharged; the sole remaining premise is the
proof-theoretic lifted non-provability bridge.
-/
theorem plain_intuitionistic_completeness_of_liftBase_notProvable_via_canonicalRepresented
    (hLiftNotProvable :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ¬ ExtDerivation Const Δ φ →
          ¬ ClosedTheorySet.Provable
              (Const := HenkinConstInfinity.HInf Base Const)
              (fun ψ =>
                ψ ∈ Δ.map
                  (HenkinConstInfinity.liftBaseClosedFormula
                    (Base := Base) (Const := Const)) ∨
                  ψ ∈ HenkinConstInfinity.HenkinAxioms
                    (Base := Base) (Const := Const))
              (HenkinConstInfinity.liftBaseClosedFormula
                (Base := Base) (Const := Const) φ))
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    (∀ M : HeytingHenkinModel.{u, v, v + 1} Base Const,
      HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) ↔
      ExtDerivation Const Δ φ := by
  exact validFrom_iff_provable_of_liftBase_notProvable_via_canonicalRepresented
    (Base := Base)
    (Const := Const)
    hLiftNotProvable

/--
Plain intuitionistic original-signature completeness follows from the lifted
cumulative-Henkin countermodel theorem supplied by the direct Henkin path.

This is stated in fully explicit `modelsFrom` form to keep the remaining gap
visible without relying on universe-polymorphic abbreviation inference.
-/
theorem validFrom_iff_provable_of_liftBase_countermodel
    (hCounter :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ¬ ExtDerivation Const Δ φ →
        ∃ M : HeytingHenkinModel.{u, max u (v + 1), w}
            Base (HenkinConstInfinity.HInf Base Const),
          ¬ HeytingHenkinModel.modelsFrom M
              (Δ.map
                (HenkinConstInfinity.liftBaseClosedFormula
                  (Base := Base) (Const := Const)))
              (HenkinConstInfinity.liftBaseClosedFormula
                  (Base := Base) (Const := Const) φ)
              (fun v => nomatch v))
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    (∀ M : HeytingHenkinModel.{u, v, w} Base Const,
      HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) ↔
      ExtDerivation Const Δ φ := by
  constructor
  · intro hValid
    exact
      provable_of_liftBase_countermodel
        (Base := Base)
        (Const := Const)
        hCounter
        hValid
  · exact validFrom_of_provable (Base := Base) (Const := Const)

/--
The same completeness reduction stated at the sharper canonical-world boundary.
-/
theorem validFrom_iff_provable_of_liftBase_canonical_counterworld
    (hBridge :
      ∀ {Δ : List (ClosedFormula (HenkinConstInfinity.HInf Base Const))}
        {φ : ClosedFormula (HenkinConstInfinity.HInf Base Const)},
        (∃ W : HenkinConstInfinity.World Base Const,
            W ∈ HenkinConstInfinity.contextDenote
                  (Base := Base)
                  (Const := Const)
                  Δ
                  (HenkinConstInfinity.emptyClosedSubst Base Const) ∧
            ¬ HenkinConstInfinity.modelsFrom
                  (Base := Base)
                  (Const := Const)
                  Δ
                  φ
                  (HenkinConstInfinity.emptyClosedSubst Base Const)) →
          ∃ M : HeytingHenkinModel.{u, max u (v + 1), w}
              Base (HenkinConstInfinity.HInf Base Const),
            ¬ HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v))
    (hCanonicalCounter :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ¬ ExtDerivation Const Δ φ →
        ∃ W : HenkinConstInfinity.World Base Const,
          W ∈ HenkinConstInfinity.contextDenote
                (Base := Base)
                (Const := Const)
                (Δ.map
                  (HenkinConstInfinity.liftBaseClosedFormula
                    (Base := Base) (Const := Const)))
                (HenkinConstInfinity.emptyClosedSubst Base Const) ∧
          ¬ HenkinConstInfinity.modelsFrom
                (Base := Base)
                (Const := Const)
                (Δ.map
                  (HenkinConstInfinity.liftBaseClosedFormula
                    (Base := Base) (Const := Const)))
                (HenkinConstInfinity.liftBaseClosedFormula
                  (Base := Base) (Const := Const) φ)
                (HenkinConstInfinity.emptyClosedSubst Base Const))
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    (∀ M : HeytingHenkinModel.{u, v, w} Base Const,
      HeytingHenkinModel.modelsFrom M Δ φ (fun v => nomatch v)) ↔
      ExtDerivation Const Δ φ := by
  constructor
  · intro hValid
    exact
      provable_of_liftBase_canonical_counterworld
        (Base := Base)
        (Const := Const)
        hBridge
        hCanonicalCounter
        hValid
  · exact validFrom_of_provable (Base := Base) (Const := Const)

end PlainIntuitionistic

end Mettapedia.Logic.HOL
