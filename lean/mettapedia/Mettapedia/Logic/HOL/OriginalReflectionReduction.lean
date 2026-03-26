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
The corrected one-step conservativity theorem boundary (GPT-5.4 Pro route).

Parameterized by `BaseWitnesses` to avoid the empty-signature obstruction.
Uses `ClosedTheorySet.Provable` (not list-based) so it composes directly
with `RecursiveStageTheory`.

This is the single remaining hard theorem for original-signature completeness.
-/
def WitnessedTheoryConservativityGoal
    (_W : BaseWitnesses Base Const) : Prop :=
  ∀ {T : ClosedTheorySet Const} {φ : ClosedFormula Const},
    ClosedTheorySet.Provable
      (Const := OneStepHenkinConst Base Const)
      (fun ψ =>
        (∃ χ : ClosedFormula Const,
            χ ∈ T ∧
            OneStepHenkinConst.liftClosedFormula
              (Base := Base) (Const := Const) χ = ψ) ∨
          ψ ∈ OneStepHenkinConst.ExactHenkinAxioms
            (Base := Base) (Const := Const))
      (OneStepHenkinConst.liftClosedFormula
        (Base := Base) (Const := Const) φ) →
    ClosedTheorySet.Provable (Const := Const) T φ

/- 
`WitnessedTheoryConservativityGoal` is kept as the parameterized theorem
boundary for the final reflection bridge, but it is not proved here.

The earlier attempt to prove it by direct fresh-constant retraction was the
wrong abstraction, and the newer obstruction analysis in
`OriginalReflectionObstruction.lean` indicates that this candidate may still be
too strong even with `BaseWitnesses`.

Downstream composition remains parameterized by any future corrected
conservativity theorem.
-/

/-- Lift base witnesses through the recursive Henkin stage tower.
    At each stage, the source witnesses are embedded into the larger signature. -/
def baseWitnessesOf (W : BaseWitnesses Base Const) :
    ∀ n, BaseWitnesses Base (HenkinConstStage Base Const n)
  | 0 => ⟨fun b =>
      mapConst (HenkinConstStage.ofBase (Base := Base) (Const := Const)) (W.witness b)⟩
  | n + 1 => ⟨fun b =>
      mapConst (HenkinConstStage.lift (Base := Base) (Const := Const) (Nat.le_succ n))
        ((baseWitnessesOf W n).witness b)⟩

/--
The Hilbert-epsilon scheme (Hε) / independence of premise.
For each one-variable formula φ : Formula Const [σ]:

  ∃x:σ. (∃y:σ. φ(y)) → φ(x)

This is the source-language principle forced by the `exWitness` axiom
after abstracting the fresh witness constant. NOT intuitionistically provable.
-/
def HεScheme {σ : Ty Base} (φ : Formula Const [σ]) : ClosedFormula Const :=
  .ex (.imp (weaken (Base := Base) (σ := σ) (.ex φ)) φ)

/--
The drinker paradox scheme (DP).
For each one-variable formula φ : Formula Const [σ]:

  ∃x:σ. φ(x) → ∀y:σ. φ(y)

This is the source-language principle forced by the `allCounterexample` axiom
after abstracting the fresh counterexample constant. NOT intuitionistically provable.
-/
def DPScheme {σ : Ty Base} (φ : Formula Const [σ]) : ClosedFormula Const :=
  .ex (.imp φ (weaken (Base := Base) (σ := σ) (.all φ)))

/-- The set of all source-language Hε and DP scheme instances. -/
def SourceStepSchemes : ClosedTheorySet Const :=
  fun ψ =>
    (∃ (σ : Ty Base) (φ : Formula Const [σ]), ψ = HεScheme (Base := Base) φ) ∨
    (∃ (σ : Ty Base) (φ : Formula Const [σ]), ψ = DPScheme (Base := Base) φ)

/-- Original-signature provability with the Route 2 source schemes available
as additional assumptions. -/
def SourceSchemeProvable
    (Δ : List (ClosedFormula Const))
    (φ : ClosedFormula Const) : Prop :=
  ClosedTheorySet.Provable
    (Const := Const)
    (fun ψ => ψ ∈ Δ ∨ ψ ∈ SourceStepSchemes (Base := Base) (Const := Const))
    φ

/--
Route 2 final target: reflection back to the original signature lands in
source HOL augmented by the Hε / DP schemes forced by one-step Henkinization.
-/
structure SchemeExtendedReflectionTarget where
  witnesses : BaseWitnesses Base Const
  reflect :
    ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
      OriginalLiftProvable (Base := Base) (Const := Const) Δ φ →
        SourceSchemeProvable (Base := Base) (Const := Const) Δ φ

/--
The corrected one-step reflection theorem boundary (GPT-5.4 Pro route).

Replaces `WitnessedTheoryConservativityGoal` (which is FALSE for intuitionistic HOL).
The conclusion lands in source HOL + Hε + DP, not plain source HOL.

This is the closest TRUE theorem to the original conservativity target:
- exact witness axioms eliminate to source Hε instances,
- exact counterexample axioms eliminate to source DP instances,
- fresh-constant abstraction removes the named constants but preserves the principles.
-/
def SchemeReflectionGoal
    (_W : BaseWitnesses Base Const) : Prop :=
  ∀ {T : ClosedTheorySet Const} {φ : ClosedFormula Const},
    ClosedTheorySet.Provable
      (Const := OneStepHenkinConst Base Const)
      (fun ψ =>
        (∃ χ : ClosedFormula Const,
            χ ∈ T ∧
            OneStepHenkinConst.liftClosedFormula
              (Base := Base) (Const := Const) χ = ψ) ∨
          ψ ∈ OneStepHenkinConst.ExactHenkinAxioms
            (Base := Base) (Const := Const))
      (OneStepHenkinConst.liftClosedFormula
        (Base := Base) (Const := Const) φ) →
    ClosedTheorySet.Provable
      (Const := Const)
      (fun ψ => ψ ∈ T ∨ ψ ∈ SourceStepSchemes (Base := Base) (Const := Const))
      φ
/-- The abstraction of the exWitness axiom equals the Hε body. -/
theorem abstractConst_exWitnessAxiom
    {σ : Ty Base} (φ : Formula Const [σ]) :
    abstractConstAt
      (OneStepHenkinConst.exWitness (Base := Base) (Const := Const) φ)
      ([] : Ctx Base)
      (Term.imp
        (.ex (OneStepHenkinConst.liftFormula (Base := Base) (Const := Const) φ))
        (OneStepHenkinConst.exWitnessInstance (Base := Base) (Const := Const) φ)) =
    Term.imp
      (weaken (Base := Base) (σ := σ) (.ex (OneStepHenkinConst.liftFormula φ)))
      (OneStepHenkinConst.liftFormula φ) := by
  unfold abstractConstAt; congr 1
  · exact abstractConstAt_noOccurrence [] _
      (.ex (OneStepHenkinConst.noConstOccurrence_liftTerm _ (OneStepHenkinConst.exWitness_ne_base φ) _))
  · show abstractConstAt _ [] (instantiate (.const (.exWitness φ)) (OneStepHenkinConst.liftFormula φ)) = _
    rw [abstractConstAt_instantiate]
    simp [abstractConstAt, abstractConstAt_noOccurrence,
      OneStepHenkinConst.noConstOccurrence_liftTerm, OneStepHenkinConst.exWitness_ne_base]
    simp only [varAtDepth, insertRen, instantiate]
    rw [subst_rename (Base := Base) (Const := OneStepHenkinConst Base Const)]
    convert subst_id (OneStepHenkinConst.liftFormula (Base := Base) (Const := Const) φ) using 2
    ext τ v; cases v with | vz => rfl | vs v => cases v

/-- The Hε scheme lifts to .ex of the abstracted axiom body. -/
theorem liftClosedFormula_HεScheme
    {σ : Ty Base} (φ : Formula Const [σ]) :
    OneStepHenkinConst.liftClosedFormula (Base := Base) (Const := Const)
      (HεScheme (Base := Base) φ) =
    .ex (Term.imp
      (weaken (Base := Base) (σ := σ) (.ex (OneStepHenkinConst.liftFormula φ)))
      (OneStepHenkinConst.liftFormula φ)) := by
  simp only [HεScheme, OneStepHenkinConst.liftClosedFormula,
    WitnessProvider.liftClosedFormula, mapConst]
  congr 1; congr 1
  exact mapConst_rename OneStepHenkinConst.lift Rename.weaken (.ex φ)

theorem exWitness_axiom_to_scheme
    (_W : BaseWitnesses Base Const) {σ : Ty Base}
    (φ : Formula Const [σ])
    {Γ : List (ClosedFormula (OneStepHenkinConst Base Const))}
    (hΓ : ∀ ψ ∈ Γ, NoConstOccurrence
      (OneStepHenkinConst.exWitness (Base := Base) φ) ψ)
    {ψ : ClosedFormula (OneStepHenkinConst Base Const)}
    (hψ : NoConstOccurrence (OneStepHenkinConst.exWitness (Base := Base) φ) ψ)
    (d : ExtDerivation (OneStepHenkinConst Base Const)
      (Γ ++ [.imp (.ex (OneStepHenkinConst.liftFormula (Base := Base) (Const := Const) φ))
                    (OneStepHenkinConst.exWitnessInstance (Base := Base) (Const := Const) φ)])
      ψ) :
    ExtDerivation (OneStepHenkinConst Base Const)
      (Γ ++ [OneStepHenkinConst.liftClosedFormula (Base := Base) (Const := Const)
                (HεScheme (Base := Base) φ)])
      ψ := by
  -- Step 1: move the axiom A from context to consequent
  let A := Term.imp (.ex (OneStepHenkinConst.liftFormula φ))
    (OneStepHenkinConst.exWitnessInstance φ)
  let c := OneStepHenkinConst.exWitness (Base := Base) (Const := Const) φ
  -- Step 2: impI moves A to the right
  have d_reorder : ExtDerivation _ (A :: Γ) ψ :=
    ExtDerivation.mono (fun {χ} hχ => by
      simp only [List.mem_cons, List.mem_append] at hχ ⊢; tauto) d
  have d1 : ExtDerivation _ Γ (.imp A ψ) := ExtDerivation.impI d_reorder
  -- Step 3: abstract the fresh constant c
  -- Step 3: abstract the fresh constant c from the derivation
  have d2 := ExtDerivation.abstractConstAt_deriv (Γ := []) (Ξ := []) c d1
  -- d2 : ExtD (Γ.map (abstractConst c)) (abstractConst c (A.imp ψ))
  -- This is in context [σ] (abstractConst adds σ to the context).
  --
  -- Key equations (need proofs):
  -- (a) Γ.map (abstractConst c) = weakenHyps Γ  [by noOccurrence on each element]
  -- (b) abstractConst c (A.imp ψ) = (abstractConst c A).imp (weaken ψ)  [by abstractConst on .imp + noOcc on ψ]
  -- (c) abstractConst c A = body where body is the Hε body  [the hard computation]
  -- (d) lift(HεScheme φ) = .ex body  [connecting the scheme to the body]
  --
  -- Equation (a): Γ.map (abstractConst c) = weakenHyps Γ
  have heq_ctx : List.map (abstractConstAt c ([] : Ctx Base)) Γ =
      weakenHyps (Base := Base) (Const := OneStepHenkinConst Base Const) (σ := σ) Γ := by
    simp only [weakenHyps]
    apply List.map_congr_left
    intro χ hχ
    exact abstractConstAt_noOccurrence [] χ (hΓ χ hχ)
  -- Equation (b): abstractConst c ψ = weaken ψ
  have heq_ψ : abstractConstAt c ([] : Ctx Base) ψ = weaken (σ := σ) ψ :=
    abstractConstAt_noOccurrence [] ψ hψ
  rw [heq_ctx] at d2
  -- Rewrite d2's conclusion: abstractConstAt c [] (.imp A ψ) = .imp (body) (weaken ψ)
  have heq_concl : abstractConstAt c ([] : Ctx Base) (Term.imp A ψ) =
      Term.imp (abstractConstAt c [] A) (weaken (σ := σ) ψ) := by
    conv_lhs => unfold abstractConstAt; rw [heq_ψ]
  rw [heq_concl] at d2
  -- d2 : ExtD (weakenHyps Γ) (.imp (abstractConstAt c [] A) (weaken ψ))
  -- Connect to HεScheme
  let body := abstractConstAt c ([] : Ctx Base) A
  rw [liftClosedFormula_HεScheme, ← abstractConst_exWitnessAxiom φ]
  -- Goal: ExtD (Γ ++ [.ex body]) ψ
  apply ExtDerivation.exE (σ := σ) (φ := body) (ψ := ψ)
  · exact ExtDerivation.hyp (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
  · apply ExtDerivation.impE (φ := body)
    · exact ExtDerivation.mono (fun hχ => by
        simp only [weakenHyps, List.map_append, List.map_cons, List.map_nil,
          List.mem_cons, List.mem_append] at hχ ⊢
        tauto) d2
    · exact ExtDerivation.hyp (List.mem_cons.mpr (Or.inl rfl))

/-- The abstraction of the allCounterexample axiom equals the DP body. -/
theorem abstractConst_allCounterexampleAxiom
    {σ : Ty Base} (φ : Formula Const [σ]) :
    abstractConstAt
      (OneStepHenkinConst.allCounterexample (Base := Base) (Const := Const) φ)
      ([] : Ctx Base)
      (Term.imp
        (OneStepHenkinConst.allCounterexampleInstance (Base := Base) (Const := Const) φ)
        (.all (OneStepHenkinConst.liftFormula (Base := Base) (Const := Const) φ))) =
    Term.imp
      (OneStepHenkinConst.liftFormula φ)
      (weaken (Base := Base) (σ := σ) (.all (OneStepHenkinConst.liftFormula φ))) := by
  unfold abstractConstAt; congr 1
  · show abstractConstAt _ [] (instantiate (.const (.allCounterexample φ)) (OneStepHenkinConst.liftFormula φ)) = _
    rw [abstractConstAt_instantiate]
    simp [abstractConstAt, abstractConstAt_noOccurrence,
      OneStepHenkinConst.noConstOccurrence_liftTerm, OneStepHenkinConst.allCounterexample_ne_base]
    simp only [varAtDepth, insertRen, instantiate]
    rw [subst_rename (Base := Base) (Const := OneStepHenkinConst Base Const)]
    convert subst_id (OneStepHenkinConst.liftFormula (Base := Base) (Const := Const) φ) using 2
    ext τ v; cases v with | vz => rfl | vs v => cases v
  · exact abstractConstAt_noOccurrence [] _
      (.all (OneStepHenkinConst.noConstOccurrence_liftTerm _ (OneStepHenkinConst.allCounterexample_ne_base φ) _))

/-- The DP scheme lifts to .ex of the abstracted axiom body. -/
theorem liftClosedFormula_DPScheme
    {σ : Ty Base} (φ : Formula Const [σ]) :
    OneStepHenkinConst.liftClosedFormula (Base := Base) (Const := Const)
      (DPScheme (Base := Base) φ) =
    .ex (Term.imp
      (OneStepHenkinConst.liftFormula φ)
      (weaken (Base := Base) (σ := σ) (.all (OneStepHenkinConst.liftFormula φ)))) := by
  simp only [DPScheme, OneStepHenkinConst.liftClosedFormula,
    WitnessProvider.liftClosedFormula, mapConst]
  congr 1; congr 1
  exact mapConst_rename OneStepHenkinConst.lift Rename.weaken (.all φ)

/-- Step 1b: A single allCounterexample axiom eliminates to a DP scheme instance. -/
theorem allCounterexample_axiom_to_scheme
    (_W : BaseWitnesses Base Const) {σ : Ty Base}
    (φ : Formula Const [σ])
    {Γ : List (ClosedFormula (OneStepHenkinConst Base Const))}
    (hΓ : ∀ ψ ∈ Γ, NoConstOccurrence
      (OneStepHenkinConst.allCounterexample (Base := Base) φ) ψ)
    {ψ : ClosedFormula (OneStepHenkinConst Base Const)}
    (hψ : NoConstOccurrence (OneStepHenkinConst.allCounterexample (Base := Base) φ) ψ)
    (d : ExtDerivation (OneStepHenkinConst Base Const)
      (Γ ++ [.imp (OneStepHenkinConst.allCounterexampleInstance (Base := Base) (Const := Const) φ)
                    (.all (OneStepHenkinConst.liftFormula (Base := Base) (Const := Const) φ))])
      ψ) :
    ExtDerivation (OneStepHenkinConst Base Const)
      (Γ ++ [OneStepHenkinConst.liftClosedFormula (Base := Base) (Const := Const)
                (DPScheme (Base := Base) φ)])
      ψ := by
  let A := Term.imp
    (OneStepHenkinConst.allCounterexampleInstance φ)
    (.all (OneStepHenkinConst.liftFormula φ))
  let c := OneStepHenkinConst.allCounterexample (Base := Base) (Const := Const) φ
  have d_reorder : ExtDerivation _ (A :: Γ) ψ :=
    ExtDerivation.mono (fun {χ} hχ => by
      simp only [List.mem_cons, List.mem_append] at hχ ⊢; tauto) d
  have d1 : ExtDerivation _ Γ (.imp A ψ) := ExtDerivation.impI d_reorder
  have d2 := ExtDerivation.abstractConstAt_deriv (Γ := []) (Ξ := []) c d1
  have heq_ctx : List.map (abstractConstAt c ([] : Ctx Base)) Γ =
      weakenHyps (Base := Base) (Const := OneStepHenkinConst Base Const) (σ := σ) Γ := by
    simp only [weakenHyps]
    apply List.map_congr_left
    intro χ hχ
    exact abstractConstAt_noOccurrence [] χ (hΓ χ hχ)
  have heq_ψ : abstractConstAt c ([] : Ctx Base) ψ = weaken (σ := σ) ψ :=
    abstractConstAt_noOccurrence [] ψ hψ
  rw [heq_ctx] at d2
  have heq_concl : abstractConstAt c ([] : Ctx Base) (Term.imp A ψ) =
      Term.imp (abstractConstAt c [] A) (weaken (σ := σ) ψ) := by
    conv_lhs => unfold abstractConstAt; rw [heq_ψ]
  rw [heq_concl] at d2
  let body := abstractConstAt c ([] : Ctx Base) A
  rw [liftClosedFormula_DPScheme, ← abstractConst_allCounterexampleAxiom φ]
  apply ExtDerivation.exE (σ := σ) (φ := body) (ψ := ψ)
  · exact ExtDerivation.hyp (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl)))
  · apply ExtDerivation.impE (φ := body)
    · exact ExtDerivation.mono (fun hχ => by
        simp only [weakenHyps, List.map_append, List.map_cons, List.map_nil,
          List.mem_cons, List.mem_append] at hχ ⊢
        tauto) d2
    · exact ExtDerivation.hyp (List.mem_cons.mpr (Or.inl rfl))

/--
Lifted one-step scheme elimination (Route 2 core theorem).

From provability in the one-step language using lifted source axioms plus
exact Henkin axioms, produce provability using lifted source axioms plus
lifted Hε/DP scheme instances. Stays entirely in `OneStepHenkinConst`.

Council: Brown, Carneiro, McBride, Pfenning, Weirich, Coquand, Knuth, Tao, Tang.
Dedup-aware accumulator: duplicate axioms removed via `mono` before elimination.
-/
theorem liftedSchemeElimination
    (W : BaseWitnesses Base Const)
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (hProv : ClosedTheorySet.Provable
      (Const := OneStepHenkinConst Base Const)
      (fun ψ =>
        (∃ χ : ClosedFormula Const,
            χ ∈ T ∧
            OneStepHenkinConst.liftClosedFormula
              (Base := Base) (Const := Const) χ = ψ) ∨
          ψ ∈ OneStepHenkinConst.ExactHenkinAxioms
            (Base := Base) (Const := Const))
      (OneStepHenkinConst.liftClosedFormula
        (Base := Base) (Const := Const) φ)) :
    ClosedTheorySet.Provable
      (Const := OneStepHenkinConst Base Const)
      (fun ψ =>
        ∃ χ : ClosedFormula Const,
          (χ ∈ T ∨ χ ∈ SourceStepSchemes (Base := Base) (Const := Const)) ∧
            OneStepHenkinConst.liftClosedFormula
              (Base := Base) (Const := Const) χ = ψ)
      (OneStepHenkinConst.liftClosedFormula
        (Base := Base) (Const := Const) φ) := by
  rcases hProv with ⟨Γ, hΓ, d⟩
  -- Accumulator induction: process Γ, replacing exact axioms with schemes.
  -- Invariant: acc has only lifted (source ∪ schemes); rest has lifted source ∪ exact axioms.
  suffices hElim :
      ∀ (acc rest : List (ClosedFormula (OneStepHenkinConst Base Const))),
        (∀ ψ ∈ acc,
          ∃ χ : ClosedFormula Const,
            (χ ∈ T ∨ χ ∈ SourceStepSchemes (Base := Base) (Const := Const)) ∧
              OneStepHenkinConst.liftClosedFormula
                (Base := Base) (Const := Const) χ = ψ) →
        (∀ ψ ∈ rest,
          (∃ χ : ClosedFormula Const,
              χ ∈ T ∧
              OneStepHenkinConst.liftClosedFormula
                (Base := Base) (Const := Const) χ = ψ) ∨
            ψ ∈ OneStepHenkinConst.ExactHenkinAxioms
              (Base := Base) (Const := Const)) →
        ExtDerivation (OneStepHenkinConst Base Const) (acc ++ rest)
          (OneStepHenkinConst.liftClosedFormula
            (Base := Base) (Const := Const) φ) →
        ∃ Γ' : List (ClosedFormula (OneStepHenkinConst Base Const)),
          (∀ ψ ∈ Γ',
            ∃ χ : ClosedFormula Const,
              (χ ∈ T ∨ χ ∈ SourceStepSchemes (Base := Base) (Const := Const)) ∧
                OneStepHenkinConst.liftClosedFormula
                  (Base := Base) (Const := Const) χ = ψ) ∧
          ExtDerivation (OneStepHenkinConst Base Const) Γ'
            (OneStepHenkinConst.liftClosedFormula
              (Base := Base) (Const := Const) φ) by
    have ⟨Γ', hΓ', d'⟩ := hElim [] Γ (by simp) hΓ (by simpa using d)
    exact ⟨Γ', fun ψ hψ => hΓ' ψ hψ, d'⟩
  intro acc rest hAcc hRest d
  induction rest generalizing acc with
  | nil => exact ⟨acc, hAcc, by simpa using d⟩
  | cons χ rest ih =>
      have hχ_class := hRest χ (by simp)
      have hrest := fun ψ hψ => hRest ψ (List.mem_cons_of_mem _ hψ)
      have heq : acc ++ χ :: rest = (acc ++ [χ]) ++ rest := by
        simp [List.append_assoc]
      rcases hχ_class with ⟨χ_src, hχ_src, hχ_eq⟩ | hχ_exact
      · -- Case 1: χ is a lifted source formula → move to acc
        exact ih (acc ++ [χ])
          (by intro ψ hψ
              simp only [List.mem_append, List.mem_singleton] at hψ
              rcases hψ with hψ | rfl
              · exact hAcc ψ hψ
              · exact ⟨χ_src, Or.inl hχ_src, hχ_eq⟩)
          hrest
          (heq ▸ d)
      · -- Case 2/3: χ is an exact axiom
        -- Check if χ appears later in rest (dedup check via Classical)
        by_cases hdup : χ ∈ rest
        · -- Case 2: duplicate → remove via mono
          exact ih acc hAcc hrest (ExtDerivation.mono (fun {ψ} hψ => by
            simp only [List.mem_append, List.mem_cons] at hψ ⊢
            rcases hψ with h | rfl | h
            · exact Or.inl h
            · exact Or.inr hdup
            · exact Or.inr h) d)
        · -- Case 3: last copy → eliminate using local lemma
          -- Reorder: move χ from middle to end
          have d_reorder : ExtDerivation _ ((acc ++ rest) ++ [χ])
              (OneStepHenkinConst.liftClosedFormula φ) :=
            ExtDerivation.mono (fun {ψ} hψ => by
              simp only [List.mem_append, List.mem_cons, List.mem_singleton] at hψ ⊢
              tauto) d
          -- Classify the exact axiom
          rcases hχ_exact with ⟨σ₀, φ₀, hχ_eq_ex⟩ | ⟨σ₀, φ₀, hχ_eq_all⟩
          · -- exWitness axiom for φ₀
            subst hχ_eq_ex
            -- Establish NoConstOccurrence for the fresh constant
            have hΓ_no : ∀ ψ ∈ acc ++ rest,
                NoConstOccurrence (OneStepHenkinConst.exWitness (Base := Base) φ₀) ψ := by
              intro ψ hψ
              simp only [List.mem_append] at hψ
              rcases hψ with hψ_acc | hψ_rest
              · -- ψ ∈ acc: all lifted source/scheme formulas
                rcases hAcc ψ hψ_acc with ⟨χ_s, _, hχ_s_eq⟩
                rw [← hχ_s_eq]
                exact OneStepHenkinConst.noConstOccurrence_liftTerm _
                  (OneStepHenkinConst.exWitness_ne_base φ₀) _
              · -- ψ ∈ rest: lifted source or exact axiom, but NOT a copy of χ
                rcases hrest ψ hψ_rest with ⟨χ_s, _, hχ_s_eq⟩ | hψ_ax
                · -- lifted source
                  rw [← hχ_s_eq]
                  exact OneStepHenkinConst.noConstOccurrence_liftTerm _
                    (OneStepHenkinConst.exWitness_ne_base φ₀) _
                · -- exact axiom, different from χ
                  -- ψ is an exact axiom different from χ (since χ ∉ rest but ψ ∈ rest)
                  rcases hψ_ax with ⟨σ₁, φ₁, hψ_ex⟩ | ⟨σ₁, φ₁, hψ_all⟩
                  · -- exWitness axiom for φ₁ — .exWitness φ₀ doesn't appear
                    subst hψ_ex
                    -- NoConstOccurrence on .const (.exWitness φ₁)
                    have hconst_no : NoConstOccurrence
                        (OneStepHenkinConst.exWitness (Base := Base) φ₀)
                        (Term.const (OneStepHenkinConst.exWitness (Base := Base) φ₁) :
                          Term _ [] σ₁) := by
                      by_cases hσ : σ₁ = σ₀
                      · subst hσ
                        apply NoConstOccurrence.const_same_ne
                        intro heq; cases heq; exact hdup hψ_rest
                      · exact .const_diff_type (Ne.symm hσ) _
                    exact .imp
                      (.ex (OneStepHenkinConst.noConstOccurrence_liftTerm _ (OneStepHenkinConst.exWitness_ne_base φ₀) φ₁))
                      (noConstOccurrence_instantiate hconst_no
                        (OneStepHenkinConst.noConstOccurrence_liftTerm _ (OneStepHenkinConst.exWitness_ne_base φ₀) φ₁))
                  · -- allCounterexample axiom — .exWitness φ₀ doesn't appear
                    subst hψ_all
                    have hconst_no : NoConstOccurrence
                        (OneStepHenkinConst.exWitness (Base := Base) φ₀)
                        (Term.const (OneStepHenkinConst.allCounterexample (Base := Base) φ₁) :
                          Term _ [] σ₁) := by
                      by_cases hσ : σ₁ = σ₀
                      · subst hσ
                        exact .const_same_ne _ (by intro h; cases h)
                      · exact .const_diff_type (Ne.symm hσ) _
                    exact .imp
                      (noConstOccurrence_instantiate hconst_no
                        (OneStepHenkinConst.noConstOccurrence_liftTerm _ (OneStepHenkinConst.exWitness_ne_base φ₀) φ₁))
                      (.all (OneStepHenkinConst.noConstOccurrence_liftTerm _ (OneStepHenkinConst.exWitness_ne_base φ₀) φ₁))
            have hψ_no : NoConstOccurrence
                (OneStepHenkinConst.exWitness (Base := Base) φ₀)
                (OneStepHenkinConst.liftClosedFormula φ) :=
              OneStepHenkinConst.noConstOccurrence_liftTerm _
                (OneStepHenkinConst.exWitness_ne_base φ₀) _
            -- Apply the local lemma
            have d_scheme := exWitness_axiom_to_scheme W φ₀ hΓ_no hψ_no d_reorder
            -- d_scheme : ExtD ((acc ++ rest) ++ [lift(HεScheme φ₀)]) liftφ
            -- Continue induction with scheme in acc
            have d_rearr : ExtDerivation _ ((acc ++ [OneStepHenkinConst.liftClosedFormula
                (HεScheme φ₀)]) ++ rest) (OneStepHenkinConst.liftClosedFormula φ) :=
              ExtDerivation.mono (fun {ψ} hψ => by
                simp only [List.mem_append, List.mem_singleton] at hψ ⊢
                tauto) d_scheme
            exact ih (acc ++ [OneStepHenkinConst.liftClosedFormula (HεScheme φ₀)])
              (by intro ψ hψ
                  simp only [List.mem_append, List.mem_singleton] at hψ
                  rcases hψ with hψ | rfl
                  · exact hAcc ψ hψ
                  · exact ⟨HεScheme φ₀,
                      Or.inr (Or.inl ⟨σ₀, φ₀, rfl⟩), rfl⟩)
              hrest
              d_rearr
          · -- allCounterexample axiom for φ₀ (symmetric to exWitness)
            subst hχ_eq_all
            -- NoConstOccurrence for .allCounterexample φ₀ across acc ++ rest
            have hΓ_no : ∀ ψ ∈ acc ++ rest,
                NoConstOccurrence (OneStepHenkinConst.allCounterexample (Base := Base) φ₀) ψ := by
              intro ψ hψ
              simp only [List.mem_append] at hψ
              rcases hψ with hψ_acc | hψ_rest'
              · rcases hAcc ψ hψ_acc with ⟨χ_s, _, hχ_s_eq⟩
                rw [← hχ_s_eq]
                exact OneStepHenkinConst.noConstOccurrence_liftTerm _
                  (OneStepHenkinConst.allCounterexample_ne_base φ₀) _
              · rcases hrest ψ hψ_rest' with ⟨χ_s, _, hχ_s_eq⟩ | hψ_ax
                · rw [← hχ_s_eq]
                  exact OneStepHenkinConst.noConstOccurrence_liftTerm _
                    (OneStepHenkinConst.allCounterexample_ne_base φ₀) _
                · rcases hψ_ax with ⟨σ₁, φ₁, hψ_ex⟩ | ⟨σ₁, φ₁, hψ_all⟩
                  · -- exWitness axiom — .allCounterexample φ₀ doesn't appear
                    subst hψ_ex
                    have hconst_no : NoConstOccurrence
                        (OneStepHenkinConst.allCounterexample (Base := Base) φ₀)
                        (Term.const (OneStepHenkinConst.exWitness (Base := Base) φ₁) :
                          Term _ [] σ₁) := by
                      by_cases hσ : σ₁ = σ₀
                      · subst hσ
                        exact .const_same_ne _ (by intro h; cases h)
                      · exact .const_diff_type (Ne.symm hσ) _
                    exact .imp
                      (.ex (OneStepHenkinConst.noConstOccurrence_liftTerm _ (OneStepHenkinConst.allCounterexample_ne_base φ₀) φ₁))
                      (noConstOccurrence_instantiate hconst_no
                        (OneStepHenkinConst.noConstOccurrence_liftTerm _ (OneStepHenkinConst.allCounterexample_ne_base φ₀) φ₁))
                  · -- allCounterexample axiom for φ₁ — different from φ₀'s axiom
                    subst hψ_all
                    have hconst_no : NoConstOccurrence
                        (OneStepHenkinConst.allCounterexample (Base := Base) φ₀)
                        (Term.const (OneStepHenkinConst.allCounterexample (Base := Base) φ₁) :
                          Term _ [] σ₁) := by
                      by_cases hσ : σ₁ = σ₀
                      · subst hσ
                        apply NoConstOccurrence.const_same_ne
                        intro heq; cases heq; exact hdup hψ_rest'
                      · exact .const_diff_type (Ne.symm hσ) _
                    exact .imp
                      (noConstOccurrence_instantiate hconst_no
                        (OneStepHenkinConst.noConstOccurrence_liftTerm _ (OneStepHenkinConst.allCounterexample_ne_base φ₀) φ₁))
                      (.all (OneStepHenkinConst.noConstOccurrence_liftTerm _ (OneStepHenkinConst.allCounterexample_ne_base φ₀) φ₁))
            have hψ_no : NoConstOccurrence
                (OneStepHenkinConst.allCounterexample (Base := Base) φ₀)
                (OneStepHenkinConst.liftClosedFormula φ) :=
              OneStepHenkinConst.noConstOccurrence_liftTerm _
                (OneStepHenkinConst.allCounterexample_ne_base φ₀) _
            have d_scheme := allCounterexample_axiom_to_scheme W φ₀ hΓ_no hψ_no d_reorder
            have d_rearr : ExtDerivation _ ((acc ++ [OneStepHenkinConst.liftClosedFormula
                (DPScheme φ₀)]) ++ rest) (OneStepHenkinConst.liftClosedFormula φ) :=
              ExtDerivation.mono (fun {ψ} hψ => by
                simp only [List.mem_append, List.mem_singleton] at hψ ⊢
                tauto) d_scheme
            exact ih (acc ++ [OneStepHenkinConst.liftClosedFormula (DPScheme φ₀)])
              (by intro ψ hψ
                  simp only [List.mem_append, List.mem_singleton] at hψ
                  rcases hψ with hψ | rfl
                  · exact hAcc ψ hψ
                  · exact ⟨DPScheme φ₀,
                      Or.inr (Or.inr ⟨σ₀, φ₀, rfl⟩), rfl⟩)
              hrest
              d_rearr

/--
The remaining blocker for full Route 2 reflection: collapsing a one-step derivation
whose hypotheses and conclusion are all in the image of `liftClosedFormula` back to
a source-language derivation.

Known approaches:
- `substConst` infrastructure (term-level constant-to-term substitution using `witnessTerm`)
- `retractDerivation` with `[∀ τ, Nonempty (Const τ)]` assumption (already proved)
- Derivation-level induction with `NoFreshConst` invariant
-/
def SourceCollapseGoal : Prop :=
  ∀ {T : ClosedTheorySet Const} {φ : ClosedFormula Const},
    ClosedTheorySet.Provable
      (Const := OneStepHenkinConst Base Const)
      (fun ψ => ∃ χ : ClosedFormula Const,
        χ ∈ T ∧
          OneStepHenkinConst.liftClosedFormula
            (Base := Base) (Const := Const) χ = ψ)
      (OneStepHenkinConst.liftClosedFormula
        (Base := Base) (Const := Const) φ) →
    ClosedTheorySet.Provable (Const := Const) T φ

/-- Collapse one-step Henkin constants back to closed source terms using base
witnesses for the fresh cases. -/
def collapseConstTerm
    (W : BaseWitnesses Base Const) :
    ∀ {τ : Ty Base}, OneStepHenkinConst Base Const τ → ClosedTerm Const τ
  | _, .base c => .const c
  | τ, .exWitness _ => BaseWitnesses.witnessTerm W τ
  | τ, .allCounterexample _ => BaseWitnesses.witnessTerm W τ

@[simp] theorem substConst_collapse_liftTerm
    (W : BaseWitnesses Base Const)
    {Γ : Ctx Base} {τ : Ty Base}
    (t : Term Const Γ τ) :
    Mettapedia.Logic.HOL.substConst
        (collapseConstTerm (Base := Base) (Const := Const) W)
        (OneStepHenkinConst.liftTerm (Base := Base) (Const := Const) t) = t := by
  induction t with
  | var v =>
      rfl
  | const c =>
      simp [OneStepHenkinConst.liftTerm, WitnessProvider.liftTerm,
        OneStepHenkinConst.witnessProvider, OneStepHenkinConst.lift,
        Mettapedia.Logic.HOL.mapConst, Mettapedia.Logic.HOL.substConst,
        collapseConstTerm, weakenCtx_const]
  | app f t hf ht =>
      simp [OneStepHenkinConst.liftTerm, WitnessProvider.liftTerm,
        Mettapedia.Logic.HOL.mapConst, Mettapedia.Logic.HOL.substConst, hf, ht]
  | lam body ih =>
      simp [OneStepHenkinConst.liftTerm, WitnessProvider.liftTerm,
        Mettapedia.Logic.HOL.mapConst, Mettapedia.Logic.HOL.substConst, ih]
  | top =>
      rfl
  | bot =>
      rfl
  | and p q hp hq =>
      simp [OneStepHenkinConst.liftTerm, WitnessProvider.liftTerm,
        Mettapedia.Logic.HOL.mapConst, Mettapedia.Logic.HOL.substConst, hp, hq]
  | or p q hp hq =>
      simp [OneStepHenkinConst.liftTerm, WitnessProvider.liftTerm,
        Mettapedia.Logic.HOL.mapConst, Mettapedia.Logic.HOL.substConst, hp, hq]
  | imp p q hp hq =>
      simp [OneStepHenkinConst.liftTerm, WitnessProvider.liftTerm,
        Mettapedia.Logic.HOL.mapConst, Mettapedia.Logic.HOL.substConst, hp, hq]
  | not p hp =>
      simp [OneStepHenkinConst.liftTerm, WitnessProvider.liftTerm,
        Mettapedia.Logic.HOL.mapConst, Mettapedia.Logic.HOL.substConst, hp]
  | eq t u ht hu =>
      simp [OneStepHenkinConst.liftTerm, WitnessProvider.liftTerm,
        Mettapedia.Logic.HOL.mapConst, Mettapedia.Logic.HOL.substConst, ht, hu]
  | all p hp =>
      simp [OneStepHenkinConst.liftTerm, WitnessProvider.liftTerm,
        Mettapedia.Logic.HOL.mapConst, Mettapedia.Logic.HOL.substConst, hp]
  | ex p hp =>
      simp [OneStepHenkinConst.liftTerm, WitnessProvider.liftTerm,
        Mettapedia.Logic.HOL.mapConst, Mettapedia.Logic.HOL.substConst, hp]

@[simp] theorem substConst_collapse_liftFormula
    (W : BaseWitnesses Base Const)
    {Γ : Ctx Base}
    (φ : Formula Const Γ) :
    Mettapedia.Logic.HOL.substConst
        (collapseConstTerm (Base := Base) (Const := Const) W)
        (OneStepHenkinConst.liftFormula (Base := Base) (Const := Const) φ) = φ := by
  simpa [OneStepHenkinConst.liftFormula, WitnessProvider.liftFormula] using
    (substConst_collapse_liftTerm (Base := Base) (Const := Const) W φ)

@[simp] theorem substConst_collapse_liftClosedFormula
    (W : BaseWitnesses Base Const)
    (φ : ClosedFormula Const) :
    Mettapedia.Logic.HOL.substConst
        (collapseConstTerm (Base := Base) (Const := Const) W)
        (OneStepHenkinConst.liftClosedFormula (Base := Base) (Const := Const) φ) = φ := by
  simpa [OneStepHenkinConst.liftClosedFormula, WitnessProvider.liftClosedFormula] using
    (substConst_collapse_liftFormula (Base := Base) (Const := Const) W φ)

theorem sourceCollapseGoal_proved
    (W : BaseWitnesses Base Const) :
    SourceCollapseGoal (Base := Base) (Const := Const) := by
  intro T φ hProv
  rcases hProv with ⟨Γ, hΓ, d⟩
  have d' :=
    ExtDerivation.substConst_derivation
      (Base := Base)
      (Const := OneStepHenkinConst Base Const)
      (Const' := Const)
      (collapseConstTerm (Base := Base) (Const := Const) W)
      d
  refine ClosedTheorySet.provable_of_closedTheory
    (Const := Const)
    (T := T)
    (Δ := Γ.map (Mettapedia.Logic.HOL.substConst
      (collapseConstTerm (Base := Base) (Const := Const) W)))
    ?_ ?_
  · intro ψ hψ
    rcases List.mem_map.mp hψ with ⟨χ, hχ, rfl⟩
    rcases hΓ χ hχ with ⟨θ, hθT, hθeq⟩
    rw [← hθeq]
    simpa using hθT
  · simpa using
      ((substConst_collapse_liftClosedFormula
        (Base := Base)
        (Const := Const)
        W
        φ).symm ▸ d')

theorem schemeReflectionGoal_of_sourceCollapse
    (W : BaseWitnesses Base Const)
    (hCollapse : SourceCollapseGoal (Base := Base) (Const := Const)) :
    SchemeReflectionGoal (Base := Base) (Const := Const) W := by
  intro T φ hProv
  exact hCollapse
    (T := fun ψ => ψ ∈ T ∨ ψ ∈ SourceStepSchemes (Base := Base) (Const := Const))
    (φ := φ)
    (liftedSchemeElimination (Base := Base) (Const := Const) W hProv)

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
Stage-local provability over an arbitrary finite-stage context.

This is the generic stage-language predicate behind the original-signature
wrapper `StageLanguageProvable`. It keeps the stage-local proof problem visible
before any later specialization to lifted original formulas.
-/
def InternalStageProvable
    (n : Nat)
    (Θ : List (ClosedFormula (HenkinConstStage Base Const n)))
    (ψ : ClosedFormula (HenkinConstStage Base Const n)) : Prop :=
  ∃ Γ : List (ClosedFormula (HenkinConstStage Base Const n)),
    (∀ {χ : ClosedFormula (HenkinConstStage Base Const n)},
        χ ∈ Γ → χ ∈ StageLanguageHenkinAxioms (Base := Base) (Const := Const) n) ∧
    ExtDerivation (HenkinConstStage Base Const n)
      (Θ ++ Γ)
      ψ

/--
The Henkin axioms generated exactly when passing from stage `n` to stage `n+1`.

These are the genuinely fresh witness/counterexample axioms. Isolating them is
the right theorem boundary for the future one-step reflection argument.
-/
def ExactStepHenkinAxioms
    (n : Nat) : ClosedTheorySet (HenkinConstStage Base Const (n + 1)) :=
  fun ψ =>
    (∃ (σ : Ty Base) (φ : Formula (HenkinConstStage Base Const n) [σ]),
      ψ = HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const)
        (Nat.le_refl (n + 1))
        (HenkinConstStage.exWitnessAxiom (Base := Base) (Const := Const) φ)) ∨
    (∃ (σ : Ty Base) (φ : Formula (HenkinConstStage Base Const n) [σ]),
      ψ = HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const)
        (Nat.le_refl (n + 1))
        (HenkinConstStage.allCounterexampleAxiom (Base := Base) (Const := Const) φ))

theorem exWitnessAxiom_mem_exactStepHenkinAxioms
    {n : Nat} {σ : Ty Base}
    (φ : Formula (HenkinConstStage Base Const n) [σ]) :
    HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const)
      (Nat.le_refl (n + 1))
      (HenkinConstStage.exWitnessAxiom (Base := Base) (Const := Const) φ) ∈
      ExactStepHenkinAxioms (Base := Base) (Const := Const) n :=
  Or.inl ⟨σ, φ, rfl⟩

theorem allCounterexampleAxiom_mem_exactStepHenkinAxioms
    {n : Nat} {σ : Ty Base}
    (φ : Formula (HenkinConstStage Base Const n) [σ]) :
    HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const)
      (Nat.le_refl (n + 1))
      (HenkinConstStage.allCounterexampleAxiom (Base := Base) (Const := Const) φ) ∈
      ExactStepHenkinAxioms (Base := Base) (Const := Const) n :=
  Or.inr ⟨σ, φ, rfl⟩

/--
Stage-`n+1` axioms inherited from strictly earlier Henkin stages.

This isolates the "old" part of the stage-`n+1` axiom stock without yet forcing
it to be expressed as a lifted stage-`n` context.
-/
def PriorStepHenkinAxioms
    (n : Nat) : ClosedTheorySet (HenkinConstStage Base Const (n + 1)) :=
  fun ψ =>
    ∃ m : Nat, ∃ hm : m + 1 ≤ n,
      (∃ (σ : Ty Base) (φ : Formula (HenkinConstStage Base Const m) [σ]),
        ψ =
          HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const)
            (Nat.le_trans hm (Nat.le_succ n))
            (HenkinConstStage.exWitnessAxiom (Base := Base) (Const := Const) φ)) ∨
      (∃ (σ : Ty Base) (φ : Formula (HenkinConstStage Base Const m) [σ]),
        ψ =
          HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const)
            (Nat.le_trans hm (Nat.le_succ n))
            (HenkinConstStage.allCounterexampleAxiom (Base := Base) (Const := Const) φ))

theorem stageLanguageHenkinAxioms_succ_split
    {n : Nat}
    {ψ : ClosedFormula (HenkinConstStage Base Const (n + 1))} :
    ψ ∈ StageLanguageHenkinAxioms (Base := Base) (Const := Const) (n + 1) →
      ψ ∈ PriorStepHenkinAxioms (Base := Base) (Const := Const) n ∨
        ψ ∈ ExactStepHenkinAxioms (Base := Base) (Const := Const) n := by
  intro hψ
  rcases hψ with ⟨m, hm, hψ⟩
  have hmn : m ≤ n := Nat.succ_le_succ_iff.mp hm
  by_cases hEq : m = n
  · subst hEq
    have hm' : hm = Nat.le_refl (m + 1) := Subsingleton.elim _ _
    cases hm'
    right
    rcases hψ with hψ | hψ
    · rcases hψ with ⟨σ, φ, hEqψ⟩
      exact Or.inl ⟨σ, φ, hEqψ⟩
    · rcases hψ with ⟨σ, φ, hEqψ⟩
      exact Or.inr ⟨σ, φ, hEqψ⟩
  · left
    have hm_lt : m < n := lt_of_le_of_ne hmn hEq
    have hm' : m + 1 ≤ n := Nat.succ_le_of_lt hm_lt
    exact ⟨m, hm', hψ⟩

theorem priorStepHenkinAxioms_subset_stageLanguageHenkinAxioms_succ
    (n : Nat) :
    PriorStepHenkinAxioms (Base := Base) (Const := Const) n ⊆
      StageLanguageHenkinAxioms (Base := Base) (Const := Const) (n + 1) := by
  intro ψ hψ
  rcases hψ with ⟨m, hm, hψ⟩
  exact ⟨m, Nat.le_trans hm (Nat.le_succ n), hψ⟩

theorem exactStepHenkinAxioms_subset_stageLanguageHenkinAxioms_succ
    (n : Nat) :
    ExactStepHenkinAxioms (Base := Base) (Const := Const) n ⊆
      StageLanguageHenkinAxioms (Base := Base) (Const := Const) (n + 1) := by
  intro ψ hψ
  rcases hψ with hψ | hψ
  · rcases hψ with ⟨σ, φ, rfl⟩
    refine ⟨n, Nat.le_refl (n + 1), Or.inl ?_⟩
    exact ⟨σ, φ, by simp⟩
  · rcases hψ with ⟨σ, φ, rfl⟩
    refine ⟨n, Nat.le_refl (n + 1), Or.inr ?_⟩
    exact ⟨σ, φ, by simp⟩

theorem internalStageProvable_succ_partition
    {n : Nat}
    {Θ : List (ClosedFormula (HenkinConstStage Base Const (n + 1)))}
    {ψ : ClosedFormula (HenkinConstStage Base Const (n + 1))} :
    InternalStageProvable (Base := Base) (Const := Const) (n + 1) Θ ψ →
      ∃ Γprior Γexact : List (ClosedFormula (HenkinConstStage Base Const (n + 1))),
        (∀ {χ : ClosedFormula (HenkinConstStage Base Const (n + 1))},
            χ ∈ Γprior → χ ∈ PriorStepHenkinAxioms (Base := Base) (Const := Const) n) ∧
        (∀ {χ : ClosedFormula (HenkinConstStage Base Const (n + 1))},
            χ ∈ Γexact → χ ∈ ExactStepHenkinAxioms (Base := Base) (Const := Const) n) ∧
        ExtDerivation (HenkinConstStage Base Const (n + 1))
          (Θ ++ Γprior ++ Γexact)
          ψ := by
  classical
  rintro ⟨Γ, hΓ, hDeriv⟩
  let Γprior : List (ClosedFormula (HenkinConstStage Base Const (n + 1))) :=
    Γ.filter (fun χ => χ ∈ PriorStepHenkinAxioms (Base := Base) (Const := Const) n)
  let Γexact : List (ClosedFormula (HenkinConstStage Base Const (n + 1))) :=
    Γ.filter (fun χ => χ ∈ ExactStepHenkinAxioms (Base := Base) (Const := Const) n)
  refine ⟨Γprior, Γexact, ?_, ?_, ?_⟩
  · intro χ hχ
    simpa using (List.mem_filter.mp hχ).2
  · intro χ hχ
    simpa using (List.mem_filter.mp hχ).2
  · refine ExtDerivation.mono ?_ hDeriv
    intro χ hχ
    rcases List.mem_append.mp hχ with hχ | hχ
    · show χ ∈ (Θ ++ Γprior) ++ Γexact
      exact List.mem_append.mpr <| Or.inl (List.mem_append.mpr <| Or.inl hχ)
    · have hsplit :=
        stageLanguageHenkinAxioms_succ_split
          (Base := Base) (Const := Const) (n := n) (ψ := χ) (hΓ hχ)
      rcases hsplit with hprior | hexact
      · show χ ∈ (Θ ++ Γprior) ++ Γexact
        exact List.mem_append.mpr <| Or.inl <| List.mem_append.mpr <| Or.inr <|
          List.mem_filter.mpr ⟨hχ, by simpa using hprior⟩
      · show χ ∈ (Θ ++ Γprior) ++ Γexact
        exact List.mem_append.mpr <| Or.inr <|
          List.mem_filter.mpr ⟨hχ, by simpa using hexact⟩

/--
Stage-`n+1` provability split into inherited earlier-stage axioms and the
genuinely fresh axioms added exactly at stage `n`.

This is the right intermediate theorem boundary between the structural
partition theorem and the future exact-step reflection theorem.
-/
def SplitStepProvable
    (n : Nat)
    (Θ : List (ClosedFormula (HenkinConstStage Base Const n)))
    (ψ : ClosedFormula (HenkinConstStage Base Const n)) : Prop :=
  ∃ Γprior Γexact : List (ClosedFormula (HenkinConstStage Base Const (n + 1))),
    (∀ {χ : ClosedFormula (HenkinConstStage Base Const (n + 1))},
        χ ∈ Γprior → χ ∈ PriorStepHenkinAxioms (Base := Base) (Const := Const) n) ∧
    (∀ {χ : ClosedFormula (HenkinConstStage Base Const (n + 1))},
        χ ∈ Γexact → χ ∈ ExactStepHenkinAxioms (Base := Base) (Const := Const) n) ∧
    ExtDerivation (HenkinConstStage Base Const (n + 1))
      (Θ.map
          (HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const)
            (Nat.le_succ n)) ++
        Γprior ++ Γexact)
      (HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const)
        (Nat.le_succ n) ψ)

theorem internalStageProvable_succ_to_splitStepProvable
    {n : Nat}
    {Θ : List (ClosedFormula (HenkinConstStage Base Const n))}
    {ψ : ClosedFormula (HenkinConstStage Base Const n)} :
    InternalStageProvable (Base := Base) (Const := Const) (n + 1)
      (Θ.map
        (HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const)
          (Nat.le_succ n)))
      (HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const)
        (Nat.le_succ n) ψ) →
      SplitStepProvable (Base := Base) (Const := Const) n Θ ψ := by
  intro h
  rcases internalStageProvable_succ_partition (Base := Base) (Const := Const) h with
    ⟨Γprior, Γexact, hprior, hexact, hDeriv⟩
  exact ⟨Γprior, Γexact, hprior, hexact, hDeriv⟩

/--
One-step stage-local provability from only the genuinely fresh axioms added at
the next Henkin stage.
-/
def ExactStepProvable
    (n : Nat)
    (Θ : List (ClosedFormula (HenkinConstStage Base Const n)))
    (ψ : ClosedFormula (HenkinConstStage Base Const n)) : Prop :=
  ∃ Γ : List (ClosedFormula (HenkinConstStage Base Const (n + 1))),
    (∀ {χ : ClosedFormula (HenkinConstStage Base Const (n + 1))},
        χ ∈ Γ → χ ∈ ExactStepHenkinAxioms (Base := Base) (Const := Const) n) ∧
    ExtDerivation (HenkinConstStage Base Const (n + 1))
      (Θ.map (HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const) (Nat.le_succ n)) ++ Γ)
      (HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const) (Nat.le_succ n) ψ)

/--
The future generic one-step reflection theorem should target this local
exact-step predicate, not the more blunt cumulative stage-language predicate.
-/
def ExactStepReflectionGoal : Prop :=
  ∀ (n : Nat)
    {Θ : List (ClosedFormula (HenkinConstStage Base Const n))}
    {ψ : ClosedFormula (HenkinConstStage Base Const n)},
      ExactStepProvable (Base := Base) (Const := Const) n Θ ψ →
        ExtDerivation (HenkinConstStage Base Const n) Θ ψ

/--
Recursive finite-stage theory over `HenkinConstStage`.

Stage `0` is exactly the original closed theory lifted into stage `0`.
Stage `n + 1` consists of:
- the theory from stage `n`, lifted one stage up, and
- the genuinely fresh exact-step Henkin axioms added at stage `n`.

This is the council-backed replacement for using only bounded cumulative-Henkin
predicates as the main proof arena.
-/
def RecursiveStageTheory :
    (n : Nat) → List (ClosedFormula Const) →
      ClosedTheorySet (HenkinConstStage Base Const n)
  | 0, Δ =>
      fun ψ => ψ ∈ Δ.map
        (HenkinConstStage.liftBaseClosedFormula (Base := Base) (Const := Const) 0)
  | n + 1, Δ =>
      fun ψ =>
        (∃ χ : ClosedFormula (HenkinConstStage Base Const n),
          χ ∈ RecursiveStageTheory n Δ ∧
            HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const)
              (Nat.le_succ n) χ = ψ) ∨
        ψ ∈ ExactStepHenkinAxioms (Base := Base) (Const := Const) n

/--
Provability over the recursive finite-stage theory.

This is the new concrete stage predicate the council prefers for future finite
reduction and one-step reflection theorems.
-/
def RecursiveStageProvable
    (n : Nat)
    (Δ : List (ClosedFormula Const))
    (φ : ClosedFormula Const) : Prop :=
  ClosedTheorySet.Provable
    (Const := HenkinConstStage Base Const n)
    (RecursiveStageTheory (Base := Base) (Const := Const) n Δ)
    (HenkinConstStage.liftBaseClosedFormula (Base := Base) (Const := Const) n φ)

theorem recursiveStageTheory_lift_mem
    {n : Nat}
    {Δ : List (ClosedFormula Const)}
    {ψ : ClosedFormula (HenkinConstStage Base Const n)} :
    ψ ∈ RecursiveStageTheory (Base := Base) (Const := Const) n Δ →
      HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const)
        (Nat.le_succ n) ψ ∈
        RecursiveStageTheory (Base := Base) (Const := Const) (n + 1) Δ := by
  intro hψ
  exact Or.inl ⟨ψ, hψ, rfl⟩

theorem liftBaseClosedFormula_mem_recursiveStageTheory
    {n : Nat}
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const}
    (hφ : φ ∈ Δ) :
    HenkinConstStage.liftBaseClosedFormula (Base := Base) (Const := Const) n φ ∈
      RecursiveStageTheory (Base := Base) (Const := Const) n Δ := by
  induction n with
  | zero =>
      exact List.mem_map.mpr ⟨φ, hφ, rfl⟩
  | succ n ih =>
      have hLift :
          HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const)
              (Nat.le_succ n)
              (HenkinConstStage.liftBaseClosedFormula (Base := Base) (Const := Const) n φ) ∈
            RecursiveStageTheory (Base := Base) (Const := Const) (n + 1) Δ :=
        recursiveStageTheory_lift_mem (Base := Base) (Const := Const) ih
      simpa using
        (HenkinConstStage.liftBaseClosedFormula_comp
          (Base := Base) (Const := Const) (m := n) (n := n + 1)
          (Nat.le_succ n) φ).symm ▸ hLift

theorem stageLanguageHenkinAxioms_mem_recursiveStageTheory
    {n : Nat}
    {Δ : List (ClosedFormula Const)}
    {ψ : ClosedFormula (HenkinConstStage Base Const n)} :
    ψ ∈ StageLanguageHenkinAxioms (Base := Base) (Const := Const) n →
      ψ ∈ RecursiveStageTheory (Base := Base) (Const := Const) n Δ := by
  induction n with
  | zero =>
      intro hψ
      rcases hψ with ⟨m, hm, _⟩
      exact (Nat.not_succ_le_zero m hm).elim
  | succ n ih =>
      intro hψ
      rcases stageLanguageHenkinAxioms_succ_split
          (Base := Base) (Const := Const) (n := n) (ψ := ψ) hψ with
        hprior | hexact
      · rcases hprior with ⟨m, hm, hprior⟩
        rcases hprior with hprior | hprior
        · rcases hprior with ⟨σ, φ, rfl⟩
          let χ : ClosedFormula (HenkinConstStage Base Const n) :=
            HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const) hm
              (HenkinConstStage.exWitnessAxiom (Base := Base) (Const := Const) φ)
          have hχstage : χ ∈ StageLanguageHenkinAxioms (Base := Base) (Const := Const) n :=
            ⟨m, hm, Or.inl ⟨σ, φ, rfl⟩⟩
          have hχrec : χ ∈ RecursiveStageTheory (Base := Base) (Const := Const) n Δ :=
            ih hχstage
          have hχlift :
              HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const)
                  (Nat.le_succ n) χ ∈
                RecursiveStageTheory (Base := Base) (Const := Const) (n + 1) Δ :=
            recursiveStageTheory_lift_mem (Base := Base) (Const := Const) hχrec
          simpa [χ, HenkinConstStage.liftClosedFormula_comp
            (Base := Base) (Const := Const) hm (Nat.le_succ n)] using hχlift
        · rcases hprior with ⟨σ, φ, rfl⟩
          let χ : ClosedFormula (HenkinConstStage Base Const n) :=
            HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const) hm
              (HenkinConstStage.allCounterexampleAxiom (Base := Base) (Const := Const) φ)
          have hχstage : χ ∈ StageLanguageHenkinAxioms (Base := Base) (Const := Const) n :=
            ⟨m, hm, Or.inr ⟨σ, φ, rfl⟩⟩
          have hχrec : χ ∈ RecursiveStageTheory (Base := Base) (Const := Const) n Δ :=
            ih hχstage
          have hχlift :
              HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const)
                  (Nat.le_succ n) χ ∈
                RecursiveStageTheory (Base := Base) (Const := Const) (n + 1) Δ :=
            recursiveStageTheory_lift_mem (Base := Base) (Const := Const) hχrec
          simpa [χ, HenkinConstStage.liftClosedFormula_comp
            (Base := Base) (Const := Const) hm (Nat.le_succ n)] using hχlift
      · exact Or.inr hexact

theorem recursiveStageProvable_zero
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    RecursiveStageProvable (Base := Base) (Const := Const) 0 Δ φ →
      StageZeroLiftedProvable (Base := Base) (Const := Const) Δ φ := by
  rintro ⟨Γ, hΓ, hDeriv⟩
  refine ExtDerivation.mono ?_ hDeriv
  intro ψ hψ
  rcases hΓ ψ hψ with hψ
  exact hψ

theorem recursiveStageProvable_zero_of_original
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const}
    (hProv : ExtDerivation Const Δ φ) :
    RecursiveStageProvable (Base := Base) (Const := Const) 0 Δ φ := by
  exact
    ClosedTheorySet.provable_of_closedTheory
      (Const := HenkinConstStage Base Const 0)
      (T := RecursiveStageTheory (Base := Base) (Const := Const) 0 Δ)
      (Δ := Δ.map
        (HenkinConstStage.liftBaseClosedFormula (Base := Base) (Const := Const) 0))
      (hΔ := by
        intro ψ hψ
        exact hψ)
      (hφ := HenkinConstStage.liftBase_closedTheory_zero_of_original
        (Base := Base) (Const := Const) hProv)

theorem recursiveStageProvable_zero_iff_originalProvable
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    RecursiveStageProvable (Base := Base) (Const := Const) 0 Δ φ ↔
      ExtDerivation Const Δ φ := by
  constructor
  · intro h
    exact (stageZeroLiftedProvable_iff_originalProvable
      (Base := Base) (Const := Const) (Δ := Δ) (φ := φ)).1
      (recursiveStageProvable_zero (Base := Base) (Const := Const) h)
  · intro h
    exact recursiveStageProvable_zero_of_original
      (Base := Base) (Const := Const) h

/--
Concrete future reduction goal for the recursive finite-stage theory.
-/
def RecursiveStageFiniteReductionGoal : Prop :=
  FiniteStageReduction (Base := Base) (Const := Const)
    (RecursiveStageProvable (Base := Base) (Const := Const))

/--
Concrete future one-step reflection goal for the recursive finite-stage theory.
-/
def RecursiveStageOneStepReflectionGoal : Prop :=
  OneStepStageReflection (Base := Base) (Const := Const)
    (RecursiveStageProvable (Base := Base) (Const := Const))

/--
The recursive-stage one-step reflection theorem is an immediate specialization
of the generic witnessed one-step conservativity goal at each stage.

This is the council-backed cleaner route: instead of forcing the proof through
the stage-language exact/prior split wrappers, instantiate the generic
one-step theorem directly on `RecursiveStageTheory n Δ`.
-/
theorem recursiveStageOneStepReflection_of_witnessedTheoryConservativity
    (W : BaseWitnesses Base Const)
    (hCons :
      ∀ n : Nat,
        WitnessedTheoryConservativityGoal
          (Base := Base)
          (Const := HenkinConstStage Base Const n)
          (baseWitnessesOf (Base := Base) (Const := Const) W n)) :
    RecursiveStageOneStepReflectionGoal (Base := Base) (Const := Const) := by
  intro n Δ φ hStep
  let T : ClosedTheorySet (HenkinConstStage Base Const n) :=
    RecursiveStageTheory (Base := Base) (Const := Const) n Δ
  let ψ : ClosedFormula (HenkinConstStage Base Const n) :=
    HenkinConstStage.liftBaseClosedFormula (Base := Base) (Const := Const) n φ
  have hliftSucc {τ : Ty Base} (c : HenkinConstStage Base Const n τ) :
      HenkinConstStage.lift (Base := Base) (Const := Const) (Nat.le_succ n) c =
        (OneStepHenkinConst.base c : HenkinConstStage Base Const (n + 1) τ) := by
    simp [HenkinConstStage.lift, HenkinConstStage.liftOffset]
  have hliftFormulaEq {Γ : Ctx Base}
      (χ : Formula (HenkinConstStage Base Const n) Γ) :
      OneStepHenkinConst.liftFormula (Base := Base)
        (Const := HenkinConstStage Base Const n) χ =
      HenkinConstStage.liftFormula (Base := Base) (Const := Const)
        (Nat.le_succ n) χ := by
    rw [OneStepHenkinConst.liftFormula, WitnessProvider.liftFormula, HenkinConstStage.liftFormula]
    apply Mettapedia.Logic.HOL.mapConst_ext
    intro τ c
    simpa using hliftSucc c
  have hliftClosedEq
      (χ : ClosedFormula (HenkinConstStage Base Const n)) :
      OneStepHenkinConst.liftClosedFormula (Base := Base)
        (Const := HenkinConstStage Base Const n) χ =
      HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const)
        (Nat.le_succ n) χ := by
    simpa using hliftFormulaEq χ
  have hExInstanceEq {σ : Ty Base}
      (χ : Formula (HenkinConstStage Base Const n) [σ]) :
      OneStepHenkinConst.exWitnessInstance (Base := Base)
        (Const := HenkinConstStage Base Const n) χ =
      HenkinConstStage.exWitnessInstance (Base := Base) (Const := Const) χ := by
    unfold OneStepHenkinConst.exWitnessInstance WitnessProvider.exWitnessInstance
    unfold HenkinConstStage.exWitnessInstance HenkinConstStage.exWitnessTerm
    simp [OneStepHenkinConst.witnessProvider]
    simpa [OneStepHenkinConst.liftFormula, WitnessProvider.liftFormula] using
      congrArg
        (instantiate (Base := Base) (Term.const (OneStepHenkinConst.exWitness χ)))
        (hliftFormulaEq χ)
  have hAllInstanceEq {σ : Ty Base}
      (χ : Formula (HenkinConstStage Base Const n) [σ]) :
      OneStepHenkinConst.allCounterexampleInstance (Base := Base)
        (Const := HenkinConstStage Base Const n) χ =
      HenkinConstStage.allCounterexampleInstance (Base := Base) (Const := Const) χ := by
    unfold OneStepHenkinConst.allCounterexampleInstance
      WitnessProvider.allCounterexampleInstance
    unfold HenkinConstStage.allCounterexampleInstance
      HenkinConstStage.allCounterexampleTerm
    simp [OneStepHenkinConst.witnessProvider]
    simpa [OneStepHenkinConst.liftFormula, WitnessProvider.liftFormula] using
      congrArg
        (instantiate (Base := Base) (Term.const (OneStepHenkinConst.allCounterexample χ)))
        (hliftFormulaEq χ)
  have hliftClosedRefl
      (χ : ClosedFormula (HenkinConstStage Base Const (n + 1))) :
      HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const)
        (Nat.le_refl (n + 1)) χ = χ := by
    rw [HenkinConstStage.liftClosedFormula]
    calc
      mapConst (fun {τ} c =>
          HenkinConstStage.lift (Base := Base) (Const := Const)
            (Nat.le_refl (n + 1)) c) χ
        =
      mapConst (fun {τ} c => c) χ := by
          apply Mettapedia.Logic.HOL.mapConst_ext
          intro τ c
          simpa using
            (HenkinConstStage.lift_add_right_eq_liftOffset
              (Base := Base) (Const := Const)
              (n := n + 1) (k := 0) c)
      _ = χ := Mettapedia.Logic.HOL.mapConst_id χ
  have hExactEq :
      OneStepHenkinConst.ExactHenkinAxioms (Base := Base)
        (Const := HenkinConstStage Base Const n) =
      ExactStepHenkinAxioms (Base := Base) (Const := Const) n := by
    funext ξ
    apply propext
    constructor <;> intro h
    · rcases h with h | h
      · rcases h with ⟨σ, χ, hχ⟩
        left
        refine ⟨σ, χ, ?_⟩
        simpa [HenkinConstStage.exWitnessAxiom, OneStepHenkinConst.ExactHenkinAxioms,
          ExactStepHenkinAxioms, hliftFormulaEq, hExInstanceEq, hliftClosedRefl] using hχ
      · rcases h with ⟨σ, χ, hχ⟩
        right
        refine ⟨σ, χ, ?_⟩
        simpa [HenkinConstStage.allCounterexampleAxiom, OneStepHenkinConst.ExactHenkinAxioms,
          ExactStepHenkinAxioms, hliftFormulaEq, hAllInstanceEq, hliftClosedRefl] using hχ
    · rcases h with h | h
      · rcases h with ⟨σ, χ, hχ⟩
        left
        refine ⟨σ, χ, ?_⟩
        simpa [HenkinConstStage.exWitnessAxiom, OneStepHenkinConst.ExactHenkinAxioms,
          ExactStepHenkinAxioms, hliftFormulaEq, hExInstanceEq, hliftClosedRefl] using hχ
      · rcases h with ⟨σ, χ, hχ⟩
        right
        refine ⟨σ, χ, ?_⟩
        simpa [HenkinConstStage.allCounterexampleAxiom, OneStepHenkinConst.ExactHenkinAxioms,
          ExactStepHenkinAxioms, hliftFormulaEq, hAllInstanceEq, hliftClosedRefl] using hχ
  have hTheoryEq :
      (fun ξ =>
        (∃ χ : ClosedFormula (HenkinConstStage Base Const n),
            χ ∈ T ∧
            OneStepHenkinConst.liftClosedFormula (Base := Base)
              (Const := HenkinConstStage Base Const n) χ = ξ) ∨
          ξ ∈ OneStepHenkinConst.ExactHenkinAxioms (Base := Base)
            (Const := HenkinConstStage Base Const n)) =
      RecursiveStageTheory (Base := Base) (Const := Const) (n + 1) Δ := by
    funext ξ
    apply propext
    constructor <;> intro h
    · rcases h with h | h
      · left
        rcases h with ⟨χ, hχT, hχξ⟩
        exact ⟨χ, hχT, by simpa [hliftClosedEq χ] using hχξ⟩
      · right
        simpa [hExactEq] using h
    · rcases h with h | h
      · left
        rcases h with ⟨χ, hχT, hχξ⟩
        exact ⟨χ, hχT, by simpa [hliftClosedEq χ] using hχξ⟩
      · right
        simpa [hExactEq] using h
  have hψEq :
      OneStepHenkinConst.liftClosedFormula (Base := Base)
        (Const := HenkinConstStage Base Const n) ψ =
      HenkinConstStage.liftBaseClosedFormula (Base := Base) (Const := Const) (n + 1) φ := by
    exact (hliftClosedEq ψ).trans
      (HenkinConstStage.liftBaseClosedFormula_comp
        (Base := Base) (Const := Const) (m := n) (n := n + 1)
        (Nat.le_succ n) φ)
  have hStep' :
      ClosedTheorySet.Provable
        (Const := OneStepHenkinConst Base (HenkinConstStage Base Const n))
        (fun ξ =>
          (∃ χ : ClosedFormula (HenkinConstStage Base Const n),
              χ ∈ T ∧
              OneStepHenkinConst.liftClosedFormula (Base := Base)
                (Const := HenkinConstStage Base Const n) χ = ξ) ∨
            ξ ∈ OneStepHenkinConst.ExactHenkinAxioms (Base := Base)
              (Const := HenkinConstStage Base Const n))
        (OneStepHenkinConst.liftClosedFormula (Base := Base)
          (Const := HenkinConstStage Base Const n) ψ) := by
    simpa [RecursiveStageProvable, hTheoryEq, hψEq]
      using hStep
  change
    ClosedTheorySet.Provable
      (Const := HenkinConstStage Base Const n)
      T
      ψ
  exact (hCons n) hStep'

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
  InternalStageProvable (Base := Base) (Const := Const) n
    (Δ.map (HenkinConstStage.liftBaseClosedFormula (Base := Base) (Const := Const) n))
    (HenkinConstStage.liftBaseClosedFormula (Base := Base) (Const := Const) n φ)

theorem stageLanguageProvable_iff_internalStageProvable
    {n : Nat}
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    StageLanguageProvable (Base := Base) (Const := Const) n Δ φ ↔
      InternalStageProvable (Base := Base) (Const := Const) n
        (Δ.map (HenkinConstStage.liftBaseClosedFormula (Base := Base) (Const := Const) n))
        (HenkinConstStage.liftBaseClosedFormula (Base := Base) (Const := Const) n φ) :=
  Iff.rfl

/--
Direct supported finite-stage proof object for `OriginalLiftProvable`.

This is the council-backed concrete proof object for the >69% route: instead of
first proving a fully general cumulative support theorem, we directly package
the finite stage, a stage-local context, a classification of each staged
assumption, and a derivation of the lifted original conclusion.
-/
structure SupportedOriginalLiftStageProof
    (Δ : List (ClosedFormula Const))
    (φ : ClosedFormula Const) where
  stage : Nat
  context : List (ClosedFormula (HenkinConstStage Base Const stage))
  classify :
    ∀ {ψ : ClosedFormula (HenkinConstStage Base Const stage)},
      ψ ∈ context →
        ψ ∈ Δ.map
          (HenkinConstStage.liftBaseClosedFormula (Base := Base) (Const := Const) stage) ∨
        ψ ∈ StageLanguageHenkinAxioms (Base := Base) (Const := Const) stage
  deriv :
    ExtDerivation (HenkinConstStage Base Const stage)
      context
      (HenkinConstStage.liftBaseClosedFormula (Base := Base) (Const := Const) stage φ)

theorem stageLanguageHenkinAxioms_lift_mem
    {m n : Nat} (hmn : m ≤ n)
    {ψ : ClosedFormula (HenkinConstStage Base Const m)} :
    ψ ∈ StageLanguageHenkinAxioms (Base := Base) (Const := Const) m →
      HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const) hmn ψ ∈
        StageLanguageHenkinAxioms (Base := Base) (Const := Const) n := by
  intro hψ
  rcases hψ with ⟨k, hk, hψ⟩
  refine ⟨k, Nat.le_trans hk hmn, ?_⟩
  rcases hψ with hψ | hψ
  · rcases hψ with ⟨σ, φ, rfl⟩
    left
    refine ⟨σ, φ, ?_⟩
    simpa using
      (HenkinConstStage.liftClosedFormula_comp
        (Base := Base) (Const := Const) hk hmn
        (HenkinConstStage.exWitnessAxiom (Base := Base) (Const := Const) φ))
  · rcases hψ with ⟨σ, φ, rfl⟩
    right
    refine ⟨σ, φ, ?_⟩
    simpa using
      (HenkinConstStage.liftClosedFormula_comp
        (Base := Base) (Const := Const) hk hmn
        (HenkinConstStage.allCounterexampleAxiom (Base := Base) (Const := Const) φ))

theorem SupportedOriginalLiftStageProof.toStageLanguageProvable
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const}
    (P : SupportedOriginalLiftStageProof (Base := Base) (Const := Const) Δ φ) :
    StageLanguageProvable (Base := Base) (Const := Const) P.stage Δ φ := by
  classical
  let Γ : List (ClosedFormula (HenkinConstStage Base Const P.stage)) :=
    P.context.filter (fun ψ =>
      ψ ∈ StageLanguageHenkinAxioms (Base := Base) (Const := Const) P.stage)
  refine ⟨Γ, ?_, ?_⟩
  · intro χ hχ
    simpa using (List.mem_filter.mp hχ).2
  · refine ExtDerivation.mono ?_ P.deriv
    intro χ hχ
    rcases P.classify hχ with hBase | hStage
    · exact List.mem_append.mpr (Or.inl hBase)
    · exact List.mem_append.mpr
        (Or.inr (List.mem_filter.mpr ⟨hχ, by simpa using hStage⟩))

theorem stageLanguageProvable_nonempty_supportedOriginalLiftStageProof
    {n : Nat}
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const}
    (h :
      StageLanguageProvable (Base := Base) (Const := Const) n Δ φ) :
    Nonempty
      (SupportedOriginalLiftStageProof
        (Base := Base) (Const := Const) Δ φ) := by
  rcases h with ⟨Γ, hΓ, hDeriv⟩
  exact ⟨
    { stage := n
      context :=
        Δ.map (HenkinConstStage.liftBaseClosedFormula (Base := Base) (Const := Const) n) ++ Γ
      classify := by
        intro ψ hψ
        rcases List.mem_append.mp hψ with hBase | hStage
        · exact Or.inl hBase
        · exact Or.inr (hΓ hStage)
      deriv := hDeriv }⟩

def SupportedOriginalLiftStageProof.lift
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const}
    (P : SupportedOriginalLiftStageProof (Base := Base) (Const := Const) Δ φ)
    {n : Nat} (hmn : P.stage ≤ n) :
    SupportedOriginalLiftStageProof (Base := Base) (Const := Const) Δ φ := by
  refine
    { stage := n
      context := P.context.map
        (HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const) hmn)
      classify := ?_
      deriv := ?_ }
  · intro ψ hψ
    rcases List.mem_map.mp hψ with ⟨χ, hχ, rfl⟩
    rcases P.classify hχ with hχ | hχ
    · left
      rcases List.mem_map.mp hχ with ⟨θ, hθ, rfl⟩
      exact List.mem_map.mpr ⟨θ, hθ, by
        simpa using
          (HenkinConstStage.liftBaseClosedFormula_comp
            (Base := Base) (Const := Const) hmn θ).symm⟩
    · right
      exact stageLanguageHenkinAxioms_lift_mem
        (Base := Base) (Const := Const) hmn hχ
  · have hDeriv :=
      stageLift_closedTheoryProvable
        (Base := Base) (Const := Const) hmn P.deriv
    simpa using
      (HenkinConstStage.liftBaseClosedFormula_comp
        (Base := Base) (Const := Const) hmn φ).symm ▸ hDeriv

theorem mem_stageLiftedOriginalAssumptions_of_lift_mem
    {n : Nat}
    {Δ : List (ClosedFormula Const)}
    {ψ : ClosedFormula (HenkinConstStage Base Const n)}
    (hψ :
      HenkinConstInfinity.liftClosedFormula (Base := Base) (Const := Const) ψ ∈
        Δ.map (HenkinConstInfinity.liftBaseClosedFormula (Base := Base) (Const := Const))) :
    ψ ∈ Δ.map
      (HenkinConstStage.liftBaseClosedFormula (Base := Base) (Const := Const) n) := by
  rcases List.mem_map.mp hψ with ⟨θ, hθ, hEq⟩
  have hsound :
      HenkinConstInfinity.liftClosedFormula (Base := Base) (Const := Const)
          (HenkinConstStage.liftBaseClosedFormula (Base := Base) (Const := Const) n θ) =
        HenkinConstInfinity.liftBaseClosedFormula (Base := Base) (Const := Const) θ :=
    HenkinConstInfinity.liftBaseClosedFormula_sound
      (Base := Base) (Const := Const) n θ
  have hψEq :
      HenkinConstStage.liftBaseClosedFormula (Base := Base) (Const := Const) n θ = ψ :=
    HenkinConstInfinity.liftClosedFormula_injective
      (Base := Base) (Const := Const) (n := n) (hsound.trans hEq)
  exact List.mem_map.mpr ⟨θ, hθ, hψEq⟩

theorem lift_stage_exWitnessAxiom
    {m n : Nat} (hmn : m + 1 ≤ n) {σ : Ty Base}
    (φ : Formula (HenkinConstStage Base Const m) [σ]) :
    HenkinConstInfinity.liftClosedFormula (Base := Base) (Const := Const)
        (HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const) hmn
          (HenkinConstStage.exWitnessAxiom (Base := Base) (Const := Const) φ)) =
      HenkinConstInfinity.exWitnessAxiom (Base := Base) (Const := Const) φ := by
  rw [HenkinConstInfinity.liftClosedFormula, HenkinConstStage.liftClosedFormula,
    Mettapedia.Logic.HOL.mapConst_comp]
  have hmap :
      Mettapedia.Logic.HOL.mapConst
          (fun {τ} c =>
            HenkinConstInfinity.ofStage (Base := Base) (Const := Const)
              (HenkinConstStage.lift (Base := Base) (Const := Const) hmn c))
          (HenkinConstStage.exWitnessAxiom (Base := Base) (Const := Const) φ) =
        Mettapedia.Logic.HOL.mapConst
          (fun {τ} c =>
            HenkinConstInfinity.ofStage (Base := Base) (Const := Const) c)
          (HenkinConstStage.exWitnessAxiom (Base := Base) (Const := Const) φ) := by
    apply Mettapedia.Logic.HOL.mapConst_ext
    intro τ c
    exact HenkinConstInfinity.ofStage_lift
      (Base := Base) (Const := Const) hmn c
  rw [hmap]
  simp [HenkinConstInfinity.exWitnessAxiom, HenkinConstStage.exWitnessAxiom,
    HenkinConstStage.exWitnessInstance, HenkinConstInfinity.liftFormula,
    HenkinConstInfinity.liftTerm, Mettapedia.Logic.HOL.mapConst]
  have hφlift :
      Mettapedia.Logic.HOL.mapConst
          (fun {τ} c =>
            HenkinConstInfinity.ofStage (Base := Base) (Const := Const)
              (HenkinConstStage.liftOffset (Base := Base) (Const := Const) 1 c)) φ =
        Mettapedia.Logic.HOL.mapConst
          (fun {τ} c =>
            HenkinConstInfinity.ofStage (Base := Base) (Const := Const) c) φ := by
    simpa [HenkinConstInfinity.stageBumpFormula, HenkinConstInfinity.liftFormula]
      using
        (HenkinConstInfinity.liftFormula_stageBump
          (Base := Base) (Const := Const) 1 φ)
  exact ⟨hφlift, by simp [hφlift]⟩

theorem lift_stage_allCounterexampleAxiom
    {m n : Nat} (hmn : m + 1 ≤ n) {σ : Ty Base}
    (φ : Formula (HenkinConstStage Base Const m) [σ]) :
    HenkinConstInfinity.liftClosedFormula (Base := Base) (Const := Const)
        (HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const) hmn
          (HenkinConstStage.allCounterexampleAxiom (Base := Base) (Const := Const) φ)) =
      HenkinConstInfinity.allCounterexampleAxiom (Base := Base) (Const := Const) φ := by
  rw [HenkinConstInfinity.liftClosedFormula, HenkinConstStage.liftClosedFormula,
    Mettapedia.Logic.HOL.mapConst_comp]
  have hmap :
      Mettapedia.Logic.HOL.mapConst
          (fun {τ} c =>
            HenkinConstInfinity.ofStage (Base := Base) (Const := Const)
              (HenkinConstStage.lift (Base := Base) (Const := Const) hmn c))
          (HenkinConstStage.allCounterexampleAxiom (Base := Base) (Const := Const) φ) =
        Mettapedia.Logic.HOL.mapConst
          (fun {τ} c =>
            HenkinConstInfinity.ofStage (Base := Base) (Const := Const) c)
          (HenkinConstStage.allCounterexampleAxiom (Base := Base) (Const := Const) φ) := by
    apply Mettapedia.Logic.HOL.mapConst_ext
    intro τ c
    exact HenkinConstInfinity.ofStage_lift
      (Base := Base) (Const := Const) hmn c
  rw [hmap]
  simp [HenkinConstInfinity.allCounterexampleAxiom,
    HenkinConstStage.allCounterexampleAxiom,
    HenkinConstStage.allCounterexampleInstance,
    HenkinConstInfinity.liftFormula, HenkinConstInfinity.liftTerm,
    Mettapedia.Logic.HOL.mapConst]
  have hφlift :
      Mettapedia.Logic.HOL.mapConst
          (fun {τ} c =>
            HenkinConstInfinity.ofStage (Base := Base) (Const := Const)
              (HenkinConstStage.liftOffset (Base := Base) (Const := Const) 1 c)) φ =
        Mettapedia.Logic.HOL.mapConst
          (fun {τ} c =>
            HenkinConstInfinity.ofStage (Base := Base) (Const := Const) c) φ := by
    simpa [HenkinConstInfinity.stageBumpFormula, HenkinConstInfinity.liftFormula]
      using
        (HenkinConstInfinity.liftFormula_stageBump
          (Base := Base) (Const := Const) 1 φ)
  exact ⟨by simp [hφlift], hφlift⟩

/--
Direct supported-stage construction target for the new >69% route.

The finite-stage reduction problem is reduced to constructing this supported
object directly from `OriginalLiftProvable`.
-/
def SupportedOriginalLiftConstructionGoal : Prop :=
  ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
    OriginalLiftProvable (Base := Base) (Const := Const) Δ φ →
      Nonempty
        (SupportedOriginalLiftStageProof
          (Base := Base) (Const := Const) Δ φ)

theorem internalStageProvable_of_derivation
    {n : Nat}
    {Θ : List (ClosedFormula (HenkinConstStage Base Const n))}
    {ψ : ClosedFormula (HenkinConstStage Base Const n)} :
    ExtDerivation (HenkinConstStage Base Const n) Θ ψ →
      InternalStageProvable (Base := Base) (Const := Const) n Θ ψ := by
  intro h
  refine ⟨[], ?_, ?_⟩
  · intro χ hχ
    simp at hχ
  · simpa using h

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

theorem stageLanguageProvable_to_recursiveStageProvable
    {n : Nat}
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    StageLanguageProvable (Base := Base) (Const := Const) n Δ φ →
      RecursiveStageProvable (Base := Base) (Const := Const) n Δ φ := by
  rintro ⟨Γ, hΓ, hDeriv⟩
  refine ⟨Δ.map
      (HenkinConstStage.liftBaseClosedFormula (Base := Base) (Const := Const) n) ++ Γ,
    ?_, ?_⟩
  · intro ψ hψ
    rcases List.mem_append.mp hψ with hψ | hψ
    · rcases List.mem_map.mp hψ with ⟨φ, hφ, rfl⟩
      exact liftBaseClosedFormula_mem_recursiveStageTheory
        (Base := Base) (Const := Const) hφ
    · exact stageLanguageHenkinAxioms_mem_recursiveStageTheory
        (Base := Base) (Const := Const) (Δ := Δ) (hΓ hψ)
  · simpa [StageLanguageProvable] using hDeriv

/--
Concrete reformulation of the remaining hard theorem:

prove that stage-language provability reflects one step down from stage `n + 1`
to stage `n`.
-/
def StageLanguageOneStepReflectionGoal : Prop :=
  OneStepStageReflection (Base := Base) (Const := Const)
    (StageLanguageProvable (Base := Base) (Const := Const))

/--
Future absorption theorem for the inherited part of a stage-`n+1` derivation.

Once this is proved, only the genuinely fresh axioms remain, and the future
exact-step reflection theorem can finish the one-step stage reflection argument.
-/
def PriorStepReductionGoal : Prop :=
  ∀ (n : Nat)
    {Θ : List (ClosedFormula (HenkinConstStage Base Const n))}
    {ψ : ClosedFormula (HenkinConstStage Base Const n)},
      SplitStepProvable (Base := Base) (Const := Const) n Θ ψ →
        ExactStepProvable (Base := Base) (Const := Const) n Θ ψ

/--
Remaining stage-language-to-split reduction goal.

This is the concrete specialization of the split-step layer to original lifted
assumptions. Once proved, the exact remaining burden is only:
- absorb the inherited prior-stage assumptions, and
- reflect the genuinely fresh exact-step assumptions.
-/
def SplitStageLanguageReductionGoal : Prop :=
  ∀ (n : Nat)
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const},
      StageLanguageProvable (Base := Base) (Const := Const) (n + 1) Δ φ →
        SplitStepProvable (Base := Base) (Const := Const) n
          (Δ.map (HenkinConstStage.liftBaseClosedFormula (Base := Base) (Const := Const) n))
          (HenkinConstStage.liftBaseClosedFormula (Base := Base) (Const := Const) n φ)

theorem splitStageLanguageReductionGoal_proved :
    SplitStageLanguageReductionGoal (Base := Base) (Const := Const) := by
  intro n Δ φ hStage
  apply internalStageProvable_succ_to_splitStepProvable (Base := Base) (Const := Const)
  have hlist :
      List.map
        (HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const) (Nat.le_succ n))
        (List.map (HenkinConstStage.liftBaseClosedFormula (Base := Base) (Const := Const) n) Δ) =
      List.map (HenkinConstStage.liftBaseClosedFormula (Base := Base) (Const := Const) (n + 1)) Δ := by
    rw [List.map_map]; congr 1; ext ψ
    exact HenkinConstStage.liftBaseClosedFormula_comp (Nat.le_succ n) ψ
  rw [hlist, HenkinConstStage.liftBaseClosedFormula_comp (Nat.le_succ n)]
  exact hStage

/--
Concrete finite-stage reduction goal for the corrected stage-language bridge.

This is the remaining descent theorem specialized to the first real
stage-language predicate, rather than to an abstract placeholder.
-/
def StageLanguageFiniteReductionGoal : Prop :=
  FiniteStageReduction (Base := Base) (Const := Const)
    (StageLanguageProvable (Base := Base) (Const := Const))

theorem stageLanguageFiniteReduction_of_supportedOriginalLift
    (hSupported :
      SupportedOriginalLiftConstructionGoal (Base := Base) (Const := Const)) :
    StageLanguageFiniteReductionGoal (Base := Base) (Const := Const) := by
  intro Δ φ hLift
  rcases hSupported hLift with ⟨P⟩
  exact ⟨P.stage, P.toStageLanguageProvable⟩

theorem supportedOriginalLiftConstruction_of_stageLanguageFiniteReduction
    (hFinite :
      StageLanguageFiniteReductionGoal (Base := Base) (Const := Const)) :
    SupportedOriginalLiftConstructionGoal (Base := Base) (Const := Const) := by
  intro Δ φ hLift
  rcases hFinite hLift with ⟨n, hStage⟩
  exact stageLanguageProvable_nonempty_supportedOriginalLiftStageProof
    (Base := Base) (Const := Const) (n := n) hStage

theorem stageLanguageFiniteReductionGoal_iff_supportedOriginalLiftConstructionGoal :
    StageLanguageFiniteReductionGoal (Base := Base) (Const := Const) ↔
      SupportedOriginalLiftConstructionGoal (Base := Base) (Const := Const) := by
  constructor
  · exact supportedOriginalLiftConstruction_of_stageLanguageFiniteReduction
      (Base := Base) (Const := Const)
  · exact stageLanguageFiniteReduction_of_supportedOriginalLift
      (Base := Base) (Const := Const)

theorem recursiveStageFiniteReduction_of_stageLanguage
    (hFinite : StageLanguageFiniteReductionGoal (Base := Base) (Const := Const)) :
    RecursiveStageFiniteReductionGoal (Base := Base) (Const := Const) := by
  intro Δ φ hLift
  rcases hFinite hLift with ⟨n, hStage⟩
  exact ⟨n, stageLanguageProvable_to_recursiveStageProvable
    (Base := Base) (Const := Const) hStage⟩

theorem recursiveStageFiniteReduction_of_supportedOriginalLift
    (hSupported :
      SupportedOriginalLiftConstructionGoal (Base := Base) (Const := Const)) :
    RecursiveStageFiniteReductionGoal (Base := Base) (Const := Const) := by
  exact recursiveStageFiniteReduction_of_stageLanguage
    (Base := Base) (Const := Const)
    (stageLanguageFiniteReduction_of_supportedOriginalLift
      (Base := Base) (Const := Const) hSupported)

theorem stageLanguageOneStepReflection_of_priorStepReduction_and_exactStepReflection
    (hSplit : SplitStageLanguageReductionGoal (Base := Base) (Const := Const))
    (hPrior : PriorStepReductionGoal (Base := Base) (Const := Const))
    (hExact : ExactStepReflectionGoal (Base := Base) (Const := Const)) :
    StageLanguageOneStepReflectionGoal (Base := Base) (Const := Const) := by
  intro n Δ φ hStage
  have hSplit :=
    hSplit n hStage
  have hExactProv :
      ExactStepProvable (Base := Base) (Const := Const) n
        (Δ.map (HenkinConstStage.liftBaseClosedFormula (Base := Base) (Const := Const) n))
        (HenkinConstStage.liftBaseClosedFormula (Base := Base) (Const := Const) n φ) :=
    hPrior n hSplit
  exact internalStageProvable_of_derivation (Base := Base) (Const := Const) (hExact n hExactProv)

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

theorem sourceSchemeProvable_of_original
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const}
    (hProv : ExtDerivation Const Δ φ) :
    SourceSchemeProvable (Base := Base) (Const := Const) Δ φ := by
  exact
    ClosedTheorySet.provable_of_closedTheory
      (Const := Const)
      (T := fun ψ =>
        ψ ∈ Δ ∨ ψ ∈ SourceStepSchemes (Base := Base) (Const := Const))
      (Δ := Δ)
      (hΔ := by
        intro ψ hψ
        exact Or.inl hψ)
      (hφ := hProv)

theorem sourceSchemeProvable_of_stageZero
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    StageZeroLiftedProvable (Base := Base) (Const := Const) Δ φ →
      SourceSchemeProvable (Base := Base) (Const := Const) Δ φ := by
  intro hStage
  exact sourceSchemeProvable_of_original
    (Base := Base)
    (Const := Const)
    ((stageZeroLiftedProvable_iff_originalProvable
      (Base := Base)
      (Const := Const)
      (Δ := Δ)
      (φ := φ)).1 hStage)

/--
Route 2 analogue of `originalProvable_of_stageReduction`:
if stage-`0` collapses to source HOL plus the step schemes, then the finite-stage
bridge yields scheme-extended original-signature reflection.
-/
theorem sourceSchemeProvable_of_stageReduction
    (StageProvable : Nat → List (ClosedFormula Const) → ClosedFormula Const → Prop)
    (hZero :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        StageProvable 0 Δ φ →
          SourceSchemeProvable (Base := Base) (Const := Const) Δ φ)
    (hFinite :
      FiniteStageReduction (Base := Base) (Const := Const) StageProvable)
    (hStep :
      OneStepStageReflection (Base := Base) (Const := Const) StageProvable)
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    OriginalLiftProvable (Base := Base) (Const := Const) Δ φ →
      SourceSchemeProvable (Base := Base) (Const := Const) Δ φ := by
  intro hLift
  rcases hFinite hLift with ⟨n, hn⟩
  have hCollapse :
      ∀ {n : Nat} {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        StageProvable n Δ φ →
          SourceSchemeProvable (Base := Base) (Const := Const) Δ φ := by
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
Route 2 witnessed-source restatement of `sourceSchemeProvable_of_stageReduction`.

This is the generic transport theorem once the stage package collapses at
stage `0` to source provability with the Hε / DP schemes available.
-/
def schemeExtendedReflection_of_stageReduction
    (W : BaseWitnesses Base Const)
    (StageProvable : Nat → List (ClosedFormula Const) → ClosedFormula Const → Prop)
    (hZero :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        StageProvable 0 Δ φ →
          SourceSchemeProvable (Base := Base) (Const := Const) Δ φ)
    (hFinite :
      FiniteStageReduction (Base := Base) (Const := Const) StageProvable)
    (hStep :
      OneStepStageReflection (Base := Base) (Const := Const) StageProvable) :
    SchemeExtendedReflectionTarget (Base := Base) (Const := Const) := by
  refine ⟨W, ?_⟩
  intro Δ φ hLift
  exact sourceSchemeProvable_of_stageReduction
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
Route 2 stage-reduction package: the stage-`0` collapse lands in source HOL
with the Hε / DP schemes available as assumptions.
-/
structure SchemeStageReductionPackage where
  witnesses : BaseWitnesses Base Const
  StageProvable : Nat → List (ClosedFormula Const) → ClosedFormula Const → Prop
  finite :
    FiniteStageReduction (Base := Base) (Const := Const) StageProvable
  zero :
    ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
      StageProvable 0 Δ φ →
        SourceSchemeProvable (Base := Base) (Const := Const) Δ φ

/-- Route 2 reformulation of the remaining stage-reflection blocker. -/
def OneStepSchemeStageReflectionGoal
    (P : SchemeStageReductionPackage (Base := Base) (Const := Const)) : Prop :=
  OneStepStageReflection (Base := Base) (Const := Const) P.StageProvable

/--
Once the Route 2 one-step stage reflection theorem is proved for a corrected
stage package, the final scheme-extended reflection target follows immediately.
-/
def SchemeStageReductionPackage.toSchemeExtendedReflectionTarget
    (P : SchemeStageReductionPackage (Base := Base) (Const := Const))
    (hStep : OneStepSchemeStageReflectionGoal (Base := Base) (Const := Const) P) :
    SchemeExtendedReflectionTarget (Base := Base) (Const := Const) :=
  schemeExtendedReflection_of_stageReduction
    (Base := Base)
    (Const := Const)
    P.witnesses
    P.StageProvable
    P.zero
    P.finite
    hStep

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

/-- Vacuous existential witness axiom: `⊢ ∃x.φ → φ` when φ doesn't use x
    (i.e., φ = weaken θ for some closed θ). -/
theorem vacuous_exWitness_axiom_theorem
    {n : Nat} {σ : Ty Base}
    (θ : ClosedFormula (HenkinConstStage Base Const n)) :
    ExtDerivation (HenkinConstStage Base Const n) []
      (.imp (.ex (weaken (Base := Base) (Const := HenkinConstStage Base Const n) (σ := σ) θ)) θ) := by
  apply ExtDerivation.impI
  apply ExtDerivation.exE
    (σ := σ)
    (φ := weaken (Base := Base) (Const := HenkinConstStage Base Const n) (σ := σ) θ)
    (ψ := θ)
  · exact .hyp (by simp)
  · exact .hyp (by simp [weakenHyps])

/-- Vacuous universal counterexample axiom: `⊢ φ → ∀x.φ` when φ doesn't use x. -/
theorem vacuous_allCounterexample_axiom_theorem
    {n : Nat} {σ : Ty Base}
    (θ : ClosedFormula (HenkinConstStage Base Const n)) :
    ExtDerivation (HenkinConstStage Base Const n) []
      (.imp θ (.all (weaken (Base := Base) (Const := HenkinConstStage Base Const n) (σ := σ) θ))) := by
  apply ExtDerivation.impI
  apply ExtDerivation.allI
  -- context is: weakenHyps [θ] = [weaken θ]
  -- need to derive: weaken θ
  exact .hyp (by simp [weakenHyps])

-- The structural vacuity lemma `weaken_of_instantiate_const_noOccurrence`
-- lives in Subst.lean. It says: if `instantiate (.const c) φ = θ` and `c`
-- doesn't occur in `θ`, then `φ = weaken θ`. Used below for vacuous axioms.

/-- True classification: if a stage-n formula's HInf lift is a Henkin axiom,
    then either it's a stage-language Henkin axiom OR it's a theorem
    (derivable from empty context) at stage n.

    The second case handles vacuous axioms like `∃x.⊤ → ⊤` where the
    witness constant disappears after instantiation. -/
theorem lift_mem_henkinAxioms_stage_or_theorem
    {n : Nat}
    {ψ : ClosedFormula (HenkinConstStage Base Const n)}
    (h :
      HenkinConstInfinity.liftClosedFormula (Base := Base) (Const := Const) ψ ∈
        HenkinConstInfinity.HenkinAxioms (Base := Base) (Const := Const)) :
    ψ ∈ StageLanguageHenkinAxioms (Base := Base) (Const := Const) n ∨
    ExtDerivation (HenkinConstStage Base Const n) [] ψ := by
  rcases h with ⟨k, σ, φ_k, hEq⟩ | ⟨k, σ, φ_k, hEq⟩
  · -- ExWitness case
    by_cases hkn : k + 1 ≤ n
    · -- Non-vacuous: stage-language axiom
      left
      have hψEq : ψ =
          HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const) hkn
            (HenkinConstStage.exWitnessAxiom (Base := Base) (Const := Const) φ_k) :=
        HenkinConstInfinity.liftClosedFormula_injective
          (Base := Base) (Const := Const) (n := n)
          (hEq.trans (lift_stage_exWitnessAxiom
            (Base := Base) (Const := Const) hkn φ_k).symm)
      exact ⟨k, hkn, Or.inl ⟨σ, φ_k, hψEq⟩⟩
    · -- Vacuous: witness constant can't appear at stage n, formula is a theorem
      right
      -- Decompose ψ into .imp antecedent consequent
      let impW := HenkinConstInfinity.liftFormula_eq_imp_inv
        (Base := Base) (Const := Const) hEq
      -- antecedent lifts to .ex (liftFormula φ_k)
      let exW := HenkinConstInfinity.liftFormula_eq_ex_inv
        (Base := Base) (Const := Const) (σ := σ) impW.soundAntecedent
      have hnk : n ≤ k := by omega
      -- The consequent's lift has no occurrence of the future witness constant
      have hno : NoConstOccurrence (.exWitness (n := k) φ_k)
          (HenkinConstInfinity.liftFormula (Base := Base) (Const := Const)
            impW.consequent) :=
        noConstOccurrence_liftTerm_exWitness_future hnk φ_k impW.consequent
      -- instantiate(.const(exWitness), liftFormula exW.body) = liftFormula impW.consequent
      have h_inst : instantiate (Base := Base)
          (.const (.exWitness (n := k) φ_k))
          (HenkinConstInfinity.liftFormula (Base := Base) (Const := Const) exW.body) =
        HenkinConstInfinity.liftFormula (Base := Base) (Const := Const)
          impW.consequent := by
        conv_lhs => rw [exW.soundBody]
        exact impW.soundConsequent.symm
      -- By vacuity: exW.body = weaken impW.consequent at HInf level
      have hbody_weaken := weaken_of_instantiate_const_noOccurrence
        (HenkinConstInfinity.exWitness (n := k) φ_k) _ _ h_inst hno
      -- Pull back to stage n via liftFormula injectivity
      have hbody_stage : exW.body =
          weaken (Base := Base) (σ := σ) impW.consequent :=
        HenkinConstInfinity.liftFormula_injective
          (Base := Base) (Const := Const) (n := n)
          (hbody_weaken.trans (mapConst_weaken _ _).symm)
      -- Reconstruct ψ and apply the vacuous axiom theorem
      rw [impW.shape, exW.shape, hbody_stage]
      exact vacuous_exWitness_axiom_theorem (σ := σ) impW.consequent
  · -- AllCounterexample case (symmetric)
    by_cases hkn : k + 1 ≤ n
    · left
      have hψEq : ψ =
          HenkinConstStage.liftClosedFormula (Base := Base) (Const := Const) hkn
            (HenkinConstStage.allCounterexampleAxiom (Base := Base) (Const := Const) φ_k) :=
        HenkinConstInfinity.liftClosedFormula_injective
          (Base := Base) (Const := Const) (n := n)
          (hEq.trans (lift_stage_allCounterexampleAxiom
            (Base := Base) (Const := Const) hkn φ_k).symm)
      exact ⟨k, hkn, Or.inr ⟨σ, φ_k, hψEq⟩⟩
    · right
      let impW := HenkinConstInfinity.liftFormula_eq_imp_inv
        (Base := Base) (Const := Const) hEq
      let allW := HenkinConstInfinity.liftFormula_eq_all_inv
        (Base := Base) (Const := Const) (σ := σ) impW.soundConsequent
      have hnk : n ≤ k := by omega
      have hno : NoConstOccurrence (.allCounterexample (n := k) φ_k)
          (HenkinConstInfinity.liftFormula (Base := Base) (Const := Const)
            impW.antecedent) :=
        noConstOccurrence_liftTerm_allCounterexample_future hnk φ_k impW.antecedent
      have h_inst : instantiate (Base := Base)
          (.const (.allCounterexample (n := k) φ_k))
          (HenkinConstInfinity.liftFormula (Base := Base) (Const := Const) allW.body) =
        HenkinConstInfinity.liftFormula (Base := Base) (Const := Const)
          impW.antecedent := by
        conv_lhs => rw [allW.soundBody]
        exact impW.soundAntecedent.symm
      have hbody_weaken := weaken_of_instantiate_const_noOccurrence
        (HenkinConstInfinity.allCounterexample (n := k) φ_k) _ _ h_inst hno
      have hbody_stage : allW.body =
          weaken (Base := Base) (σ := σ) impW.antecedent :=
        HenkinConstInfinity.liftFormula_injective
          (Base := Base) (Const := Const) (n := n)
          (hbody_weaken.trans (mapConst_weaken _ _).symm)
      rw [impW.shape, allW.shape, hbody_stage]
      exact vacuous_allCounterexample_axiom_theorem (σ := σ) impW.antecedent

/-- The consumer theorem: `supportedStageDerivation_of_deriv` implies
    `SupportedOriginalLiftConstructionGoal`. -/
theorem supportedOriginalLiftConstructionGoal_proved :
    SupportedOriginalLiftConstructionGoal (Base := Base) (Const := Const) := by
  intro Δ φ hLift
  rcases hLift with ⟨GammaInf, hGammaInf, dInf⟩
  -- Get the staged derivation
  obtain ⟨S⟩ := supportedStageDerivation_of_deriv (Base := Base) (Const := Const) dInf
  -- Pre-classify: each element of S.context has its HInf lift in GammaInf
  -- and GammaInf's membership guarantees classify it.
  -- We extract the classify function WITHOUT rewriting GammaInf.
  -- 3-way classify: each ψ ∈ S.context is base-lift, stage-axiom, or theorem
  have h3way :
      ∀ ψ ∈ S.context,
        ψ ∈ Δ.map (HenkinConstStage.liftBaseClosedFormula
          (Base := Base) (Const := Const) S.stage) ∨
        ψ ∈ StageLanguageHenkinAxioms (Base := Base) (Const := Const) S.stage ∨
        ExtDerivation (HenkinConstStage Base Const S.stage) [] ψ := by
    intro ψ hψ
    have hlift : HenkinConstInfinity.liftFormula (Base := Base) (Const := Const) ψ ∈
        S.context.map (HenkinConstInfinity.liftFormula (Base := Base) (Const := Const)) :=
      List.mem_map.mpr ⟨ψ, hψ, rfl⟩
    have hmem : HenkinConstInfinity.liftFormula (Base := Base) (Const := Const) ψ ∈ GammaInf :=
      cast (by rw [S.soundContext]) hlift
    rcases hGammaInf _ hmem with hBase | hHenkin
    · exact Or.inl (mem_stageLiftedOriginalAssumptions_of_lift_mem
        (Base := Base) (Const := Const) hBase)
    · rcases lift_mem_henkinAxioms_stage_or_theorem
        (Base := Base) (Const := Const) hHenkin with hStage | hThm
      · exact Or.inr (Or.inl hStage)
      · exact Or.inr (Or.inr hThm)
  -- Discharge theorem elements from the derivation, keeping only base-lifts and stage-axioms
  -- Use discharge_head_theorem iteratively
  have hφEq : S.formula =
      HenkinConstStage.liftBaseClosedFormula (Base := Base) (Const := Const) S.stage φ :=
    HenkinConstInfinity.liftClosedFormula_injective
      (Base := Base) (Const := Const) (n := S.stage)
      (S.soundFormula.trans (HenkinConstInfinity.liftBaseClosedFormula_sound
        (Base := Base) (Const := Const) S.stage φ).symm)
  -- Discharge theorem elements using accumulator induction
  suffices hDischarge :
      ∀ (acc Θ : List (ClosedFormula (HenkinConstStage Base Const S.stage))),
        (∀ ψ ∈ Θ,
          ψ ∈ Δ.map (HenkinConstStage.liftBaseClosedFormula
            (Base := Base) (Const := Const) S.stage) ∨
          ψ ∈ StageLanguageHenkinAxioms (Base := Base) (Const := Const) S.stage ∨
          ExtDerivation (HenkinConstStage Base Const S.stage) [] ψ) →
        ExtDerivation (HenkinConstStage Base Const S.stage) (acc ++ Θ)
          (HenkinConstStage.liftBaseClosedFormula
            (Base := Base) (Const := Const) S.stage φ) →
        ∃ Θ' : List (ClosedFormula (HenkinConstStage Base Const S.stage)),
          (∀ ψ ∈ Θ',
            ψ ∈ Δ.map (HenkinConstStage.liftBaseClosedFormula
              (Base := Base) (Const := Const) S.stage) ∨
            ψ ∈ StageLanguageHenkinAxioms (Base := Base) (Const := Const) S.stage) ∧
          ExtDerivation (HenkinConstStage Base Const S.stage) (acc ++ Θ')
            (HenkinConstStage.liftBaseClosedFormula
              (Base := Base) (Const := Const) S.stage φ) by
    have ⟨ctx', hcl, d'⟩ := hDischarge [] S.context h3way (by simpa using hφEq ▸ S.deriv)
    exact ⟨⟨S.stage, ctx', fun hψ => hcl _ hψ, by simpa using d'⟩⟩
  intro acc Θ hΘ d
  induction Θ generalizing acc with
  | nil => exact ⟨[], by simp, d⟩
  | cons χ rest ih =>
      have hχ_class := hΘ χ (by simp)
      have hrest : ∀ ψ ∈ rest, _ := fun ψ hψ => hΘ ψ (List.mem_cons_of_mem _ hψ)
      have heq_fwd : acc ++ χ :: rest = (acc ++ [χ]) ++ rest := by
        simp [List.append_assoc]
      have heq_bwd : ∀ Θ', (acc ++ [χ]) ++ Θ' = acc ++ (χ :: Θ') := by
        intro Θ'; simp [List.append_assoc]
      rcases hχ_class with hKeep | hKeep | hThm
      · -- base-lift: keep χ, move to accumulator
        have ⟨Θ', hP', d''⟩ := ih (acc ++ [χ]) hrest (heq_fwd ▸ d)
        exact ⟨χ :: Θ', fun ψ hψ => by
          rcases List.mem_cons.mp hψ with rfl | hψ'
          · exact Or.inl hKeep
          · exact hP' ψ hψ', heq_bwd Θ' ▸ d''⟩
      · -- stage-axiom: keep χ, same
        have ⟨Θ', hP', d''⟩ := ih (acc ++ [χ]) hrest (heq_fwd ▸ d)
        exact ⟨χ :: Θ', fun ψ hψ => by
          rcases List.mem_cons.mp hψ with rfl | hψ'
          · exact Or.inr hKeep
          · exact hP' ψ hψ', heq_bwd Θ' ▸ d''⟩
      · -- theorem: discharge χ by reordering to head then cutting
        have d_reorder :
            ExtDerivation (HenkinConstStage Base Const S.stage)
              (χ :: (acc ++ rest))
              (HenkinConstStage.liftBaseClosedFormula
                (Base := Base) (Const := Const) S.stage φ) :=
          by
            refine ExtDerivation.mono ?_ d
            intro ψ hψ
            simp only [List.mem_append, List.mem_cons] at hψ ⊢
            tauto
        exact ih acc hrest (ExtDerivation.discharge_head_theorem hThm d_reorder)

/--
The concrete witnessed-source reduction package built from the recursive stage
predicate.

At this point all ingredients except one-step witnessed conservativity are
already proved:
- finite reduction comes from the supported original-lift construction theorem,
- stage `0` collapses to the original signature via the established bridge.
-/
def recursiveStageWitnessedStageReductionPackage
    (W : BaseWitnesses Base Const) :
    WitnessedStageReductionPackage (Base := Base) (Const := Const) where
  witnesses := W
  StageProvable := RecursiveStageProvable (Base := Base) (Const := Const)
  finite :=
    recursiveStageFiniteReduction_of_supportedOriginalLift
      (Base := Base) (Const := Const)
      (supportedOriginalLiftConstructionGoal_proved
        (Base := Base) (Const := Const))
  zero := recursiveStageProvable_zero (Base := Base) (Const := Const)

/--
Concrete Route 2 stage-reduction package built from the recursive stage
predicate. The finite reduction is unchanged; only the stage-`0` collapse now
lands in source HOL plus the Hε / DP schemes.
-/
def recursiveStageSchemeReductionPackage
    (W : BaseWitnesses Base Const) :
    SchemeStageReductionPackage (Base := Base) (Const := Const) where
  witnesses := W
  StageProvable := RecursiveStageProvable (Base := Base) (Const := Const)
  finite :=
    recursiveStageFiniteReduction_of_supportedOriginalLift
      (Base := Base) (Const := Const)
      (supportedOriginalLiftConstructionGoal_proved
        (Base := Base) (Const := Const))
  zero := by
    intro Δ φ hStage
    exact sourceSchemeProvable_of_original
      (Base := Base)
      (Const := Const)
      ((recursiveStageProvable_zero_iff_originalProvable
        (Base := Base)
        (Const := Const)
        (Δ := Δ)
        (φ := φ)).1 hStage)

/--
Council-backed final composition theorem for Route 2 proof-theoretic reflection.

Once the recursive stage package is available, the only remaining hypothesis is
the Route 2 one-step stage reflection theorem. The conclusion lands in source
HOL plus the Hε / DP schemes, not plain source HOL.
-/
def schemeExtendedReflectionTarget_proved
    (W : BaseWitnesses Base Const)
    (hStep :
      OneStepSchemeStageReflectionGoal
        (Base := Base)
        (Const := Const)
        (recursiveStageSchemeReductionPackage
          (Base := Base)
          (Const := Const)
          W)) :
    SchemeExtendedReflectionTarget (Base := Base) (Const := Const) :=
  (recursiveStageSchemeReductionPackage
    (Base := Base)
    (Const := Const)
    W).toSchemeExtendedReflectionTarget hStep

/--
Pointwise Route 2 corollary of the final scheme-extended reflection target.
-/
theorem sourceSchemeProvable_of_recursiveStageSchemeReflection
    (W : BaseWitnesses Base Const)
    (hStep :
      OneStepSchemeStageReflectionGoal
        (Base := Base)
        (Const := Const)
        (recursiveStageSchemeReductionPackage
          (Base := Base)
          (Const := Const)
          W))
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    OriginalLiftProvable (Base := Base) (Const := Const) Δ φ →
      SourceSchemeProvable (Base := Base) (Const := Const) Δ φ :=
  (schemeExtendedReflectionTarget_proved
    (Base := Base)
    (Const := Const)
    W
    hStep).reflect

/--
Council-backed final composition theorem for original-signature reflection.

Once the generic witnessed one-step conservativity theorem is available at each
recursive stage, all remaining bridge work is pure composition.
-/
def witnessedOriginalReflectionTarget_proved
    (W : BaseWitnesses Base Const)
    (hCons :
      ∀ n : Nat,
        WitnessedTheoryConservativityGoal
          (Base := Base)
          (Const := HenkinConstStage Base Const n)
          (baseWitnessesOf (Base := Base) (Const := Const) W n)) :
    WitnessedOriginalReflectionTarget (Base := Base) (Const := Const) :=
  (recursiveStageWitnessedStageReductionPackage
    (Base := Base)
    (Const := Const)
    W).toWitnessedOriginalReflectionTarget
    (recursiveStageOneStepReflection_of_witnessedTheoryConservativity
      (Base := Base) (Const := Const) W hCons)

/--
Pointwise corollary of the final witnessed reflection target.
-/
theorem originalProvable_of_witnessedTheoryConservativity
    (W : BaseWitnesses Base Const)
    (hCons :
      ∀ n : Nat,
        WitnessedTheoryConservativityGoal
          (Base := Base)
          (Const := HenkinConstStage Base Const n)
          (baseWitnessesOf (Base := Base) (Const := Const) W n))
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const} :
    OriginalLiftProvable (Base := Base) (Const := Const) Δ φ →
      ExtDerivation Const Δ φ :=
  (witnessedOriginalReflectionTarget_proved
    (Base := Base) (Const := Const) W hCons).reflect

end HenkinConstInfinity

end Mettapedia.Logic.HOL
