import Mettapedia.Logic.HOL.IntuitionisticCompleteness
import Mettapedia.Logic.HOL.OriginalReflectionWitnessed

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

namespace HenkinConstInfinity

/-!
# Original-Signature Reflection Reduction

This file does not prove the final original-signature completeness theorem.
Instead, it packages the exact remaining proof-theoretic bridge:

- a finite-stage reduction of lifted `HInf` provability, and
- an iterated one-step stage-reflection principle.

Once those two ingredients are supplied, reflection back to the original
signature is immediate.

Important status boundary after the certified obstruction:

- the bounded `StageProvableUpTo` predicate below remains useful as an internal
  transport device inside `HInf`,
- but it is no longer the right public target by itself,
- and the mathematically clean replacement target is now a
  `BaseWitnesses`-parameterized original-signature reflection theorem.
-/

/-- Lifted original-signature provability inside the cumulative Henkin language. -/
def OriginalLiftProvable
    (Δ : List (ClosedFormula Const))
    (φ : ClosedFormula Const) : Prop :=
  ClosedTheorySet.Provable
    (Const := HInf Base Const)
    (fun ψ =>
      ψ ∈ Δ.map (liftBaseClosedFormula (Base := Base) (Const := Const)) ∨
        ψ ∈ HenkinAxioms (Base := Base) (Const := Const))
    (liftBaseClosedFormula (Base := Base) (Const := Const) φ)

/-- Stage-`0` lifted provability over the original signature. -/
def StageZeroLiftedProvable
    (Δ : List (ClosedFormula Const))
    (φ : ClosedFormula Const) : Prop :=
  ExtDerivation (HenkinConstStage Base Const 0)
    (Δ.map (HenkinConstStage.liftBaseClosedFormula (Base := Base) (Const := Const) 0))
    (HenkinConstStage.liftBaseClosedFormula (Base := Base) (Const := Const) 0 φ)

/--
Lifted provability using only Henkin axioms generated up to stage `n`.

After the obstruction theorem, this should be read as a provisional bounded-`HInf`
transport predicate, not as the final public original-signature target.
-/
def StageProvableUpTo
    (n : Nat)
    (Δ : List (ClosedFormula Const))
    (φ : ClosedFormula Const) : Prop :=
  ClosedTheorySet.Provable
    (Const := HInf Base Const)
    (fun ψ =>
      ψ ∈ Δ.map (liftBaseClosedFormula (Base := Base) (Const := Const)) ∨
        ψ ∈ HenkinAxiomsUpTo (Base := Base) (Const := Const) n)
    (liftBaseClosedFormula (Base := Base) (Const := Const) φ)

theorem originalLiftProvable_of_provable
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const}
    (hProv : ExtDerivation Const Δ φ) :
    OriginalLiftProvable (Base := Base) (Const := Const) Δ φ :=
  liftBase_provable (Base := Base) (Const := Const) hProv

theorem stageZeroLiftedProvable_iff_originalProvable
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    StageZeroLiftedProvable (Base := Base) (Const := Const) Δ φ ↔
      ExtDerivation Const Δ φ := by
  constructor
  · exact
      HenkinConstStage.original_closedTheory_of_stageZero
        (Base := Base) (Const := Const)
  · intro hProv
    exact
      HenkinConstStage.liftBase_closedTheory_zero_of_original
        (Base := Base) (Const := Const)
        hProv

theorem stageProvableUpTo_mono
    {m n : Nat} (hmn : m ≤ n)
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    StageProvableUpTo (Base := Base) (Const := Const) m Δ φ →
      StageProvableUpTo (Base := Base) (Const := Const) n Δ φ := by
  exact
    ClosedTheorySet.provable_mono
      (Const := HInf Base Const)
      (T := fun ψ =>
        ψ ∈ Δ.map (liftBaseClosedFormula (Base := Base) (Const := Const)) ∨
          ψ ∈ HenkinAxiomsUpTo (Base := Base) (Const := Const) m)
      (U := fun ψ =>
        ψ ∈ Δ.map (liftBaseClosedFormula (Base := Base) (Const := Const)) ∨
          ψ ∈ HenkinAxiomsUpTo (Base := Base) (Const := Const) n)
      (φ := liftBaseClosedFormula (Base := Base) (Const := Const) φ)
      (hTU := by
        intro ψ hψ
        rcases hψ with hψ | hψ
        · exact Or.inl hψ
        · exact Or.inr <|
            henkinAxiomsUpTo_mono (Base := Base) (Const := Const) hmn hψ)

theorem finiteStageReduction_stageProvableUpTo
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    OriginalLiftProvable (Base := Base) (Const := Const) Δ φ →
      ∃ n : Nat, StageProvableUpTo (Base := Base) (Const := Const) n Δ φ := by
  intro hLift
  rcases hLift with ⟨Γ, hΓ, hDeriv⟩
  rcases exists_henkinAxiomsUpTo_list_bound
      (Base := Base)
      (Const := Const)
      Γ with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  exact
    ClosedTheorySet.provable_of_closedTheory
      (Const := HInf Base Const)
      (T := fun ψ =>
        ψ ∈ Δ.map (liftBaseClosedFormula (Base := Base) (Const := Const)) ∨
          ψ ∈ HenkinAxiomsUpTo (Base := Base) (Const := Const) n)
      (Δ := Γ)
      (hΔ := by
        intro ψ hψ
        rcases hΓ ψ hψ with hψΔ | hψHenkin
        · exact Or.inl hψΔ
        · exact Or.inr (hn hψ hψHenkin))
      hDeriv

/--
`FiniteStageReduction StageProvable` says every lifted original-signature
provability problem in `HInf` reduces to some finite stage measured by
`StageProvable`.
-/
def FiniteStageReduction
    (StageProvable : Nat → List (ClosedFormula Const) → ClosedFormula Const → Prop) :
    Prop :=
  ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
    OriginalLiftProvable (Base := Base) (Const := Const) Δ φ →
      ∃ n : Nat, StageProvable n Δ φ

theorem finiteStageReduction_instance :
    FiniteStageReduction
      (fun n Δ φ => StageProvableUpTo (Base := Base) (Const := Const) n Δ φ) := by
  intro Δ φ hLift
  exact finiteStageReduction_stageProvableUpTo (Base := Base) (Const := Const) hLift

/--
`OneStepStageReflection StageProvable` says a proof problem at stage `n + 1`
can always be reflected one step down to stage `n`.
-/
def OneStepStageReflection
    (StageProvable : Nat → List (ClosedFormula Const) → ClosedFormula Const → Prop) :
    Prop :=
  ∀ (n : Nat) {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
    StageProvable (n + 1) Δ φ → StageProvable n Δ φ

/--
Restated original-signature reflection target after the obstruction theorem.

The final bridge is now packaged together with explicit source witness data:
- a chosen `BaseWitnesses` structure for the original signature, and
- the reflection theorem proved relative to that witnessed source.
-/
structure WitnessedOriginalReflectionTarget where
  witnesses : BaseWitnesses Base Const
  reflect :
    ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
      OriginalLiftProvable (Base := Base) (Const := Const) Δ φ →
        ExtDerivation Const Δ φ

/--
Corrected stage/reflection package after the obstruction theorem.

This is the new abstraction layer that future bridge work should target:
- a witnessed original source signature,
- a stage-indexed internal provability predicate,
- finite reduction into that stage predicate,
- and the stage-`0` bridge back to the original signature.

The only missing ingredient is then the one-step stage reflection theorem.
-/
structure WitnessedStageReductionPackage where
  witnesses : BaseWitnesses Base Const
  StageProvable : Nat → List (ClosedFormula Const) → ClosedFormula Const → Prop
  finite :
    FiniteStageReduction (Base := Base) (Const := Const) StageProvable
  zero :
    ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
      StageProvable 0 Δ φ →
        StageZeroLiftedProvable (Base := Base) (Const := Const) Δ φ

/--
Reformulated remaining blocker after the obstruction theorem:

for a corrected witnessed-source stage package, the only missing ingredient is
the one-step stage reflection theorem for its chosen `StageProvable` predicate.
-/
def OneStepWitnessedStageReflectionGoal
    (P : WitnessedStageReductionPackage (Base := Base) (Const := Const)) : Prop :=
  OneStepStageReflection (Base := Base) (Const := Const) P.StageProvable

/--
Concrete stage-local Henkin axioms living in stage `n`.

These are exactly the witness/counterexample axioms generated at some earlier
stage `m`, then lifted into the current stage `n`. Equivalently, stage `n`
contains axioms generated strictly below it, since the axiom for stage `m`
already lives in stage `m + 1`.
-/
def StageLanguageHenkinAxioms
    (n : Nat) : ClosedTheorySet (HenkinConstStage Base Const n) :=
  fun ψ =>
    ∃ m : Nat, ∃ hm : m + 1 ≤ n,
      (∃ (σ : Ty Base) (φ : Formula (HenkinConstStage Base Const m) [σ]),
        ψ =
          HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const) hm
            (HenkinConstStage.exWitnessAxiom (Base := Base) (Const := Const) φ)) ∨
      (∃ (σ : Ty Base) (φ : Formula (HenkinConstStage Base Const m) [σ]),
        ψ =
          HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const) hm
            (HenkinConstStage.allCounterexampleAxiom (Base := Base) (Const := Const) φ))

/--
Concrete stage-language provability candidate for the witnessed-source bridge.

At stage `n`, we ask for a derivation in the actual stage language from:
- the original assumptions lifted directly to stage `n`, and
- a finite list of stage-local Henkin axioms already available in stage `n`.

This is the first non-provisional candidate for the `StageProvable` field of a
future `WitnessedStageReductionPackage`.
-/
def StageLanguageProvable
    (n : Nat)
    (Δ : List (ClosedFormula Const))
    (φ : ClosedFormula Const) : Prop :=
  ∃ Γ : List (ClosedFormula (HenkinConstStage Base Const n)),
    (∀ {ψ : ClosedFormula (HenkinConstStage Base Const n)},
        ψ ∈ Γ → ψ ∈ StageLanguageHenkinAxioms (Base := Base) (Const := Const) n) ∧
    ExtDerivation (HenkinConstStage Base Const n)
      (Δ.map (HenkinConstStage.liftBaseClosedFormula (Base := Base) (Const := Const) n) ++ Γ)
      (HenkinConstStage.liftBaseClosedFormula (Base := Base) (Const := Const) n φ)

theorem not_mem_stageLanguageHenkinAxioms_zero
    {ψ : ClosedFormula (HenkinConstStage Base Const 0)} :
    ψ ∉ StageLanguageHenkinAxioms (Base := Base) (Const := Const) 0 := by
  intro hψ
  rcases hψ with ⟨m, hm, -⟩
  exact Nat.not_succ_le_zero m hm

theorem stageLanguageProvable_zero
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    StageLanguageProvable (Base := Base) (Const := Const) 0 Δ φ →
      StageZeroLiftedProvable (Base := Base) (Const := Const) Δ φ := by
  rintro ⟨Γ, hΓ, hDeriv⟩
  refine ExtDerivation.mono ?_ hDeriv
  intro ψ hψ
  rcases List.mem_append.mp hψ with hψ | hψ
  · exact hψ
  · exfalso
    exact
      not_mem_stageLanguageHenkinAxioms_zero (Base := Base) (Const := Const)
        (ψ := ψ) (hΓ hψ)

/--
Concrete reformulation of the remaining hard theorem:

prove that stage-language provability reflects one step down from stage `n + 1`
to stage `n`.
-/
def StageLanguageOneStepReflectionGoal : Prop :=
  OneStepStageReflection (Base := Base) (Const := Const)
    (StageLanguageProvable (Base := Base) (Const := Const))

/--
Concrete finite-stage reduction goal for the corrected stage-language bridge.

This is the remaining descent theorem specialized to the first real
stage-language predicate, rather than to an abstract placeholder.
-/
def StageLanguageFiniteReductionGoal : Prop :=
  FiniteStageReduction (Base := Base) (Const := Const)
    (StageLanguageProvable (Base := Base) (Const := Const))

/--
If lifted `HInf` provability always reduces to some finite stage, and finite
stages reflect stepwise down to stage `0`, then original-signature reflection
follows immediately.
-/
theorem originalProvable_of_stageReduction
    (StageProvable : Nat → List (ClosedFormula Const) → ClosedFormula Const → Prop)
    (hZero :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        StageProvable 0 Δ φ → ExtDerivation Const Δ φ)
    (hFinite :
      FiniteStageReduction (Base := Base) (Const := Const) StageProvable)
    (hStep :
      OneStepStageReflection (Base := Base) (Const := Const) StageProvable)
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    OriginalLiftProvable (Base := Base) (Const := Const) Δ φ →
      ExtDerivation Const Δ φ := by
  intro hLift
  rcases hFinite hLift with ⟨n, hn⟩
  have hCollapse :
      ∀ {n : Nat} {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        StageProvable n Δ φ → ExtDerivation Const Δ φ := by
    intro n
    induction n with
    | zero =>
        intro Δ φ hStage
        exact hZero hStage
    | succ n ih =>
        intro Δ φ hStage
        exact ih (hStep n hStage)
  exact hCollapse hn

/--
Witnessed-source restatement of `originalProvable_of_stageReduction`.

The proof obligations are unchanged, but the target is now phrased at the
correct theorem boundary: source signatures carry closed base witnesses.
-/
def witnessedOriginalReflection_of_stageReduction
    (W : BaseWitnesses Base Const)
    (StageProvable : Nat → List (ClosedFormula Const) → ClosedFormula Const → Prop)
    (hZero :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        StageProvable 0 Δ φ → ExtDerivation Const Δ φ)
    (hFinite :
      FiniteStageReduction (Base := Base) (Const := Const) StageProvable)
    (hStep :
      OneStepStageReflection (Base := Base) (Const := Const) StageProvable) :
    WitnessedOriginalReflectionTarget (Base := Base) (Const := Const) := by
  refine ⟨W, ?_⟩
  intro Δ φ hLift
  exact originalProvable_of_stageReduction
    (Base := Base)
    (Const := Const)
    StageProvable
    hZero
    hFinite
    hStep
    hLift

/--
The only substantive remaining blockers for proof-theoretic reflection are:

- proving a `FiniteStageReduction`, and
- proving a `OneStepStageReflection`.

Everything else is now transport.
-/
theorem originalProvable_of_finiteStageReduction_and_oneStepReflection
    (StageProvable : Nat → List (ClosedFormula Const) → ClosedFormula Const → Prop)
    (hFinite :
      FiniteStageReduction (Base := Base) (Const := Const) StageProvable)
    (hStep :
      OneStepStageReflection (Base := Base) (Const := Const) StageProvable)
    (hZero :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        StageProvable 0 Δ φ → StageZeroLiftedProvable (Base := Base) (Const := Const) Δ φ)
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    OriginalLiftProvable (Base := Base) (Const := Const) Δ φ →
      ExtDerivation Const Δ φ := by
  apply originalProvable_of_stageReduction
    (Base := Base)
    (Const := Const)
    StageProvable
  · intro Δ φ hStage
    exact (stageZeroLiftedProvable_iff_originalProvable
      (Base := Base)
      (Const := Const)
      (Δ := Δ)
      (φ := φ)).1 (hZero hStage)
  · exact hFinite
  · exact hStep

/--
Witnessed-source restatement of the finite-stage plus one-step reflection bridge.

This is the current mathematically honest theorem target shape for the final
original-signature reflection result.
-/
def witnessedOriginalReflection_of_finiteStageReduction_and_oneStepReflection
    (W : BaseWitnesses Base Const)
    (StageProvable : Nat → List (ClosedFormula Const) → ClosedFormula Const → Prop)
    (hFinite :
      FiniteStageReduction (Base := Base) (Const := Const) StageProvable)
    (hStep :
      OneStepStageReflection (Base := Base) (Const := Const) StageProvable)
    (hZero :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        StageProvable 0 Δ φ → StageZeroLiftedProvable (Base := Base) (Const := Const) Δ φ) :
    WitnessedOriginalReflectionTarget (Base := Base) (Const := Const) := by
  refine ⟨W, ?_⟩
  intro Δ φ hLift
  exact originalProvable_of_finiteStageReduction_and_oneStepReflection
    (Base := Base)
    (Const := Const)
    StageProvable
    hFinite
    hStep
    hZero
    hLift

/--
Once the reformulated one-step stage reflection goal is proved for a corrected
witnessed-source package, the final witnessed original reflection target follows
immediately.
-/
def WitnessedStageReductionPackage.toWitnessedOriginalReflectionTarget
    (P : WitnessedStageReductionPackage (Base := Base) (Const := Const))
    (hStep : OneStepWitnessedStageReflectionGoal (Base := Base) (Const := Const) P) :
    WitnessedOriginalReflectionTarget (Base := Base) (Const := Const) :=
  witnessedOriginalReflection_of_finiteStageReduction_and_oneStepReflection
    (Base := Base)
    (Const := Const)
    P.witnesses
    P.StageProvable
    P.finite
    hStep
    P.zero

/--
The concrete witnessed-source reduction package built from the new stage-language
predicate, once its finite-stage descent theorem is supplied.
-/
def stageLanguageWitnessedStageReductionPackage
    (W : BaseWitnesses Base Const)
    (hFinite : StageLanguageFiniteReductionGoal (Base := Base) (Const := Const)) :
    WitnessedStageReductionPackage (Base := Base) (Const := Const) where
  witnesses := W
  StageProvable := StageLanguageProvable (Base := Base) (Const := Const)
  finite := hFinite
  zero := stageLanguageProvable_zero (Base := Base) (Const := Const)

/--
Once the concrete stage-language finite reduction and one-step reflection goals
are proved, the witnessed original reflection target follows immediately.
-/
def stageLanguageWitnessedOriginalReflectionTarget
    (W : BaseWitnesses Base Const)
    (hFinite : StageLanguageFiniteReductionGoal (Base := Base) (Const := Const))
    (hStep : StageLanguageOneStepReflectionGoal (Base := Base) (Const := Const)) :
    WitnessedOriginalReflectionTarget (Base := Base) (Const := Const) :=
  (stageLanguageWitnessedStageReductionPackage
    (Base := Base)
    (Const := Const)
    W
    hFinite).toWitnessedOriginalReflectionTarget hStep

end HenkinConstInfinity

end Mettapedia.Logic.HOL
