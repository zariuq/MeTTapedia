import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.CanonicalBridge
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.ClosedTermPreModelBridge
import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.ClosedTermWorldModel

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL
open Mettapedia.PLN.WorldModel.PLNWorldModel
open ClosedTermCanonicalWorldModel
open scoped ENNReal

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

namespace CompletenessFrontier

/-- A closed frontier has a singleton world-model counterexample when one
canonical closed world gives strength `1` to every antecedent query and strength
`0` to the succedent query. -/
structure SingletonWorldModelCounterexample
    (F : CompletenessFrontier Const []) : Type (max u v) where
  world : ClosedTheorySet.World Const
  antecedent_strength_one :
    ∀ {φ : ClosedFormula Const}, φ ∈ F.antecedents →
      BinaryWorldModel.queryStrength
          (State := Multiset (ClosedTheorySet.World Const))
          (Query := CanonicalQuery Const)
          ({world} : Multiset (ClosedTheorySet.World Const)) φ = 1
  succedent_strength_zero :
    BinaryWorldModel.queryStrength
        (State := Multiset (ClosedTheorySet.World Const))
        (Query := CanonicalQuery Const)
        ({world} : Multiset (ClosedTheorySet.World Const)) F.succedent = 0

namespace SingletonWorldModelCounterexample

theorem antecedent_mem
    {F : CompletenessFrontier Const []}
    (C : SingletonWorldModelCounterexample (Const := Const) F)
    {φ : ClosedFormula Const} (hφ : φ ∈ F.antecedents) :
    φ ∈ C.world.carrier :=
  (singleton_adequacy_strength_one
    (Base := Base) (Const := Const) C.world φ).2
    (C.antecedent_strength_one hφ)

theorem succedent_not_mem
    {F : CompletenessFrontier Const []}
    (C : SingletonWorldModelCounterexample (Const := Const) F) :
    F.succedent ∉ C.world.carrier :=
  (singleton_adequacy_strength_zero
    (Base := Base) (Const := Const) C.world F.succedent).2
    C.succedent_strength_zero

/-- A singleton world-model counterexample is already an ordinary canonical-world
counterexample. -/
theorem to_world_counterexample
    {F : CompletenessFrontier Const []}
    (C : SingletonWorldModelCounterexample (Const := Const) F) :
    (∀ φ, φ ∈ F.antecedents → φ ∈ C.world.carrier) ∧
      F.succedent ∉ C.world.carrier :=
  ⟨fun _ hφ => C.antecedent_mem hφ, C.succedent_not_mem⟩

/-- Singleton strength counterexamples refute native closed derivability. -/
theorem not_derivable
    {F : CompletenessFrontier Const []}
    (C : SingletonWorldModelCounterexample (Const := Const) F) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  exact CompletenessFrontier.not_derivable_of_world_counterexample
    (F := F) (W := C.world)
    (fun φ hφ => C.antecedent_mem hφ)
    C.succedent_not_mem

end SingletonWorldModelCounterexample

/-- Upgrade an ordinary canonical-world counterexample to the singleton
world-model/evidence presentation. -/
def singletonWorldModelCounterexampleOfWorldCounterexample
    {F : CompletenessFrontier Const []}
    {W : ClosedTheorySet.World Const}
    (hAnte : ∀ φ, φ ∈ F.antecedents → φ ∈ W.carrier)
    (hSucc : F.succedent ∉ W.carrier) :
    SingletonWorldModelCounterexample (Const := Const) F where
  world := W
  antecedent_strength_one := by
    intro φ hφ
    exact queryStrength_singleton_of_satisfies
      (Base := Base) (Const := Const) W φ (hAnte φ hφ)
  succedent_strength_zero :=
    queryStrength_singleton_of_not_satisfies
      (Base := Base) (Const := Const) W F.succedent hSucc

theorem not_derivable_of_singletonWorldModelCounterexample
    {F : CompletenessFrontier Const []}
    (C : SingletonWorldModelCounterexample (Const := Const) F) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent :=
  C.not_derivable

/-- A Henkin model realizing a canonical world and semantically satisfying all
antecedents while refuting the succedent yields the singleton world-model
counterexample for the same frontier. -/
def singletonWorldModelCounterexampleOfQuotientRealizationSemanticCounterexample
    {F : CompletenessFrontier Const []}
    {M : HenkinModel.{u, v, w} Base Const}
    {W : ClosedTheorySet.World Const}
    (R : ClosedTermPreModelBridge.QuotientRealization M W.carrier)
    (hAnte : ∀ φ, φ ∈ F.antecedents → HenkinModel.models M φ)
    (hSucc : ¬ HenkinModel.models M F.succedent) :
    SingletonWorldModelCounterexample (Const := Const) F :=
  singletonWorldModelCounterexampleOfWorldCounterexample
    (Base := Base) (Const := Const) (W := W)
    (fun φ hφ =>
      (ClosedTermPreModelBridge.quotientRealization_models_iff_world_mem
        (M := M) W R φ).1 (hAnte φ hφ))
    (by
      intro hmem
      exact hSucc
        ((ClosedTermPreModelBridge.quotientRealization_models_iff_world_mem
          (M := M) W R F.succedent).2 hmem))

/-- Under a quotient realization of its world, a singleton world-model
counterexample semantically satisfies every antecedent. -/
theorem SingletonWorldModelCounterexample.antecedent_models_of_quotientRealization
    {F : CompletenessFrontier Const []}
    (C : SingletonWorldModelCounterexample (Const := Const) F)
    {M : HenkinModel.{u, v, w} Base Const}
    (R : ClosedTermPreModelBridge.QuotientRealization M C.world.carrier)
    {φ : ClosedFormula Const} (hφ : φ ∈ F.antecedents) :
    HenkinModel.models M φ :=
  (ClosedTermPreModelBridge.quotientRealization_models_iff_world_mem
    (M := M) C.world R φ).2 (C.antecedent_mem hφ)

/-- Under a quotient realization of its world, a singleton world-model
counterexample semantically refutes the succedent. -/
theorem SingletonWorldModelCounterexample.not_models_succedent_of_quotientRealization
    {F : CompletenessFrontier Const []}
    (C : SingletonWorldModelCounterexample (Const := Const) F)
    {M : HenkinModel.{u, v, w} Base Const}
    (R : ClosedTermPreModelBridge.QuotientRealization M C.world.carrier) :
    ¬ HenkinModel.models M F.succedent :=
  ClosedTermPreModelBridge.quotientRealization_not_models_of_world_not_mem
    (M := M) C.world R C.succedent_not_mem

/-- Native derivability preserves singleton query strength at canonical worlds:
if all closed antecedents have strength `1`, then the succedent also has
strength `1`. -/
theorem singletonStrength_preservation_of_derivable
    {F : CompletenessFrontier Const []}
    (hDer : Derivable (Base := Base) (Const := Const) F.antecedents F.succedent)
    (W : ClosedTheorySet.World Const)
    (hAnte :
      ∀ {φ : ClosedFormula Const}, φ ∈ F.antecedents →
        BinaryWorldModel.queryStrength
            (State := Multiset (ClosedTheorySet.World Const))
            (Query := CanonicalQuery Const)
            ({W} : Multiset (ClosedTheorySet.World Const)) φ = 1) :
    BinaryWorldModel.queryStrength
        (State := Multiset (ClosedTheorySet.World Const))
        (Query := CanonicalQuery Const)
        ({W} : Multiset (ClosedTheorySet.World Const)) F.succedent = 1 := by
  have hAnteMem : ∀ φ, φ ∈ F.antecedents → φ ∈ W.carrier := by
    intro φ hφ
    exact (singleton_adequacy_strength_one
      (Base := Base) (Const := Const) W φ).2 (hAnte hφ)
  have hSuccMem : F.succedent ∈ W.carrier :=
    Derivable.mem_world_of_derivable (W := W) hAnteMem hDer
  exact queryStrength_singleton_of_satisfies
    (Base := Base) (Const := Const) W F.succedent hSuccMem

theorem not_nonempty_singletonWorldModelCounterexample_of_derivable
    {F : CompletenessFrontier Const []}
    (hDer : Derivable (Base := Base) (Const := Const) F.antecedents F.succedent) :
    ¬ Nonempty (SingletonWorldModelCounterexample (Const := Const) F) := by
  rintro ⟨C⟩
  exact C.not_derivable hDer

/-- Singleton world-model semantic consequence for closed frontiers: every
canonical singleton state that gives strength `1` to all antecedents also gives
strength `1` to the succedent. -/
def SingletonStrengthConsequence (F : CompletenessFrontier Const []) : Prop :=
  ∀ W : ClosedTheorySet.World Const,
    (∀ {φ : ClosedFormula Const}, φ ∈ F.antecedents →
      BinaryWorldModel.queryStrength
          (State := Multiset (ClosedTheorySet.World Const))
          (Query := CanonicalQuery Const)
          ({W} : Multiset (ClosedTheorySet.World Const)) φ = 1) →
    BinaryWorldModel.queryStrength
        (State := Multiset (ClosedTheorySet.World Const))
        (Query := CanonicalQuery Const)
        ({W} : Multiset (ClosedTheorySet.World Const)) F.succedent = 1

theorem singletonStrengthConsequence_of_derivable
    {F : CompletenessFrontier Const []}
    (hDer : Derivable (Base := Base) (Const := Const) F.antecedents F.succedent) :
    SingletonStrengthConsequence (Base := Base) (Const := Const) F := by
  intro W hAnte
  exact singletonStrength_preservation_of_derivable
    (Base := Base) (Const := Const) hDer W hAnte

theorem not_singletonStrengthConsequence_of_counterexample
    {F : CompletenessFrontier Const []}
    (C : SingletonWorldModelCounterexample (Const := Const) F) :
    ¬ SingletonStrengthConsequence (Base := Base) (Const := Const) F := by
  intro hCons
  have hOne :
      BinaryWorldModel.queryStrength
          (State := Multiset (ClosedTheorySet.World Const))
          (Query := CanonicalQuery Const)
          ({C.world} : Multiset (ClosedTheorySet.World Const)) F.succedent = 1 :=
    hCons C.world C.antecedent_strength_one
  exact zero_ne_one (C.succedent_strength_zero.symm.trans hOne)

/-- A Henkin model that realizes the closed-term quotient carrier and separates
the frontier gives a direct native-derivability refutation. -/
theorem not_derivable_of_quotientRealizationSemanticCounterexample
    {F : CompletenessFrontier Const []}
    {M : HenkinModel.{u, v, w} Base Const}
    {W : ClosedTheorySet.World Const}
    (R : ClosedTermPreModelBridge.QuotientRealization M W.carrier)
    (hAnte : ∀ φ, φ ∈ F.antecedents → HenkinModel.models M φ)
    (hSucc : ¬ HenkinModel.models M F.succedent) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent :=
  (singletonWorldModelCounterexampleOfQuotientRealizationSemanticCounterexample
    (Base := Base) (Const := Const) (W := W) R hAnte hSucc).not_derivable

/-- The same realized quotient-model separation refutes singleton
query-strength consequence. -/
theorem not_singletonStrengthConsequence_of_quotientRealizationSemanticCounterexample
    {F : CompletenessFrontier Const []}
    {M : HenkinModel.{u, v, w} Base Const}
    {W : ClosedTheorySet.World Const}
    (R : ClosedTermPreModelBridge.QuotientRealization M W.carrier)
    (hAnte : ∀ φ, φ ∈ F.antecedents → HenkinModel.models M φ)
    (hSucc : ¬ HenkinModel.models M F.succedent) :
    ¬ SingletonStrengthConsequence (Base := Base) (Const := Const) F :=
  not_singletonStrengthConsequence_of_counterexample
    (Base := Base) (Const := Const)
    (singletonWorldModelCounterexampleOfQuotientRealizationSemanticCounterexample
      (Base := Base) (Const := Const) (W := W) R hAnte hSucc)

theorem singletonStrengthConsequence_iff_no_counterexample
    (F : CompletenessFrontier Const []) :
    SingletonStrengthConsequence (Base := Base) (Const := Const) F ↔
      ¬ Nonempty (SingletonWorldModelCounterexample (Const := Const) F) := by
  constructor
  · intro hCons
    rintro ⟨C⟩
    exact not_singletonStrengthConsequence_of_counterexample
      (Base := Base) (Const := Const) C hCons
  · intro hNo W hAnte
    classical
    by_cases hSucc : canonicalWorldSatisfies W F.succedent
    · exact queryStrength_singleton_of_satisfies
        (Base := Base) (Const := Const) W F.succedent hSucc
    · let hCounter : SingletonWorldModelCounterexample (Const := Const) F :=
        { world := W
          antecedent_strength_one := hAnte
          succedent_strength_zero :=
            queryStrength_singleton_of_not_satisfies
              (Base := Base) (Const := Const) W F.succedent hSucc }
      exact False.elim (hNo ⟨hCounter⟩)

theorem not_singletonStrengthConsequence_iff_counterexample
    (F : CompletenessFrontier Const []) :
    ¬ SingletonStrengthConsequence (Base := Base) (Const := Const) F ↔
      Nonempty (SingletonWorldModelCounterexample (Const := Const) F) := by
  classical
  constructor
  · intro hNot
    by_contra hNo
    exact hNot ((singletonStrengthConsequence_iff_no_counterexample
      (Base := Base) (Const := Const) F).2 hNo)
  · rintro ⟨C⟩
    exact not_singletonStrengthConsequence_of_counterexample
      (Base := Base) (Const := Const) C

/-- Once the Henkin witness fields upgrade a prime separating extension to a
canonical world, it also yields the singleton world-model counterexample used by
the evidence endpoint. -/
def singletonWorldModelCounterexampleOfPrimeSeparatingExtension
    {F : CompletenessFrontier Const []}
    {U : ClosedTheorySet Const}
    (hFU : PrimeSeparatingExtension (Const := Const) F U)
    (hExistsWitness :
      ∀ {σ : Ty Base} {φ : Formula Const [σ]},
        (.ex φ : ClosedFormula Const) ∈ U →
          ∃ t : ClosedTerm Const σ, instantiate (Base := Base) t φ ∈ U)
    (hAllCounterexample :
      ∀ {σ : Ty Base} {φ : Formula Const [σ]},
        (.all φ : ClosedFormula Const) ∉ U →
          ∃ t : ClosedTerm Const σ, instantiate (Base := Base) t φ ∉ U) :
    SingletonWorldModelCounterexample (Const := Const) F :=
  singletonWorldModelCounterexampleOfWorldCounterexample
    (Base := Base) (Const := Const)
    (W := hFU.toWorld hExistsWitness hAllCounterexample)
    (fun _ hφ => hFU.contains_antecedents hφ)
    hFU.omits_succedent

theorem not_derivable_of_primeSeparatingExtension_with_witnesses
    {F : CompletenessFrontier Const []}
    {U : ClosedTheorySet Const}
    (hFU : PrimeSeparatingExtension (Const := Const) F U)
    (hExistsWitness :
      ∀ {σ : Ty Base} {φ : Formula Const [σ]},
        (.ex φ : ClosedFormula Const) ∈ U →
          ∃ t : ClosedTerm Const σ, instantiate (Base := Base) t φ ∈ U)
    (hAllCounterexample :
      ∀ {σ : Ty Base} {φ : Formula Const [σ]},
        (.all φ : ClosedFormula Const) ∉ U →
          ∃ t : ClosedTerm Const σ, instantiate (Base := Base) t φ ∉ U) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent :=
  (singletonWorldModelCounterexampleOfPrimeSeparatingExtension
    (Base := Base) (Const := Const) hFU hExistsWitness hAllCounterexample).not_derivable

end CompletenessFrontier

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
