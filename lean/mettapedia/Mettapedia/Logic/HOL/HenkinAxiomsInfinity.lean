import Mettapedia.Logic.HOL.HenkinizationInfinity
import Mettapedia.Logic.HOL.CanonicalTheory
import Mettapedia.Logic.HOL.PrimeHenkinExtension

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

namespace HenkinConstInfinity

/-- The cumulative infinitary signature used in the internal Henkin completeness path. -/
abbrev HInf (Base : Type u) (Const : Ty Base → Type v) : Ty Base → Type (max u (v + 1)) :=
  HenkinConstInfinity Base Const

/-- The existential Henkin axiom attached to a finite-stage one-variable formula. -/
def exWitnessAxiom {n : Nat} {σ : Ty Base}
    (φ : Formula (HenkinConstStage Base Const n) [σ]) :
    ClosedFormula (HInf Base Const) :=
  .imp
    (.ex (liftFormula (Base := Base) (Const := Const) φ))
    (instantiate (Base := Base)
      (liftTerm (Base := Base) (Const := Const)
        (HenkinConstStage.exWitnessTerm (Base := Base) (Const := Const) φ))
      (liftFormula (Base := Base) (Const := Const) φ))

/-- The universal counterexample Henkin axiom attached to a finite-stage one-variable formula. -/
def allCounterexampleAxiom {n : Nat} {σ : Ty Base}
    (φ : Formula (HenkinConstStage Base Const n) [σ]) :
    ClosedFormula (HInf Base Const) :=
  .imp
    (instantiate (Base := Base)
      (liftTerm (Base := Base) (Const := Const)
        (HenkinConstStage.allCounterexampleTerm (Base := Base) (Const := Const) φ))
      (liftFormula (Base := Base) (Const := Const) φ))
    (.all (liftFormula (Base := Base) (Const := Const) φ))

/-- The theory set of existential witness axioms over the cumulative Henkin signature. -/
def ExWitnessAxioms : ClosedTheorySet (HInf Base Const) :=
  fun ψ =>
    ∃ (n : Nat) (σ : Ty Base) (φ : Formula (HenkinConstStage Base Const n) [σ]),
      ψ = exWitnessAxiom (Base := Base) (Const := Const) φ

/-- The theory set of universal counterexample axioms over the cumulative Henkin signature. -/
def AllCounterexampleAxioms : ClosedTheorySet (HInf Base Const) :=
  fun ψ =>
    ∃ (n : Nat) (σ : Ty Base) (φ : Formula (HenkinConstStage Base Const n) [σ]),
      ψ = allCounterexampleAxiom (Base := Base) (Const := Const) φ

/-- The full cumulative Henkin axiom family. -/
def HenkinAxioms : ClosedTheorySet (HInf Base Const) :=
  ExWitnessAxioms ∪ AllCounterexampleAxioms

theorem exWitnessAxiom_mem_exWitnessAxioms {n : Nat} {σ : Ty Base}
    (φ : Formula (HenkinConstStage Base Const n) [σ]) :
    exWitnessAxiom (Base := Base) (Const := Const) φ ∈
      ExWitnessAxioms :=
  ⟨n, σ, φ, rfl⟩

theorem allCounterexampleAxiom_mem_allCounterexampleAxioms {n : Nat} {σ : Ty Base}
    (φ : Formula (HenkinConstStage Base Const n) [σ]) :
    allCounterexampleAxiom (Base := Base) (Const := Const) φ ∈
      AllCounterexampleAxioms :=
  ⟨n, σ, φ, rfl⟩

theorem exWitnessAxiom_mem_henkinAxioms {n : Nat} {σ : Ty Base}
    (φ : Formula (HenkinConstStage Base Const n) [σ]) :
    exWitnessAxiom (Base := Base) (Const := Const) φ ∈
      HenkinAxioms :=
  Or.inl (exWitnessAxiom_mem_exWitnessAxioms (Base := Base) (Const := Const) φ)

theorem allCounterexampleAxiom_mem_henkinAxioms {n : Nat} {σ : Ty Base}
    (φ : Formula (HenkinConstStage Base Const n) [σ]) :
    allCounterexampleAxiom (Base := Base) (Const := Const) φ ∈
      HenkinAxioms :=
  Or.inr
    (allCounterexampleAxiom_mem_allCounterexampleAxioms
      (Base := Base) (Const := Const) φ)

theorem exists_witness_of_containsExWitnessAxioms
    {T : ClosedTheorySet (HInf Base Const)}
    (hClosed : ClosedTheorySet.DeductivelyClosed (Const := HInf Base Const) T)
    (hAxioms :
      ExWitnessAxioms ⊆ T)
    {σ : Ty Base} {φ : Formula (HInf Base Const) [σ]}
    (hEx : (.ex φ : ClosedFormula (HInf Base Const)) ∈ T) :
    ∃ t : ClosedTerm (HInf Base Const) σ, instantiate (Base := Base) t φ ∈ T := by
  rcases exists_stage_formula (Base := Base) (Const := Const) φ with ⟨n, φ', hφ⟩
  let t : ClosedTerm (HInf Base Const) σ :=
    liftTerm (Base := Base) (Const := Const)
      (HenkinConstStage.exWitnessTerm (Base := Base) (Const := Const) φ')
  have hAx :
      exWitnessAxiom (Base := Base) (Const := Const) φ' ∈ T :=
    hAxioms (exWitnessAxiom_mem_exWitnessAxioms (Base := Base) (Const := Const) φ')
  have hEx' :
      (.ex (liftFormula (Base := Base) (Const := Const) φ') :
        ClosedFormula (HInf Base Const)) ∈ T := by
    simpa [hφ] using hEx
  have hInstProv :
      ClosedTheorySet.Provable (Const := HInf Base Const) T
        (instantiate (Base := Base) t (liftFormula (Base := Base) (Const := Const) φ')) :=
    ClosedTheorySet.provable_mp
      (Const := HInf Base Const)
      (T := T)
      (φ := .ex (liftFormula (Base := Base) (Const := Const) φ'))
      (ψ := instantiate (Base := Base) t
        (liftFormula (Base := Base) (Const := Const) φ'))
      (ClosedTheorySet.provable_of_mem (Const := HInf Base Const) hAx)
      (ClosedTheorySet.provable_of_mem (Const := HInf Base Const) hEx')
  refine ⟨t, ?_⟩
  have hInstMem :
      instantiate (Base := Base) t
        (liftFormula (Base := Base) (Const := Const) φ') ∈ T :=
    hClosed hInstProv
  simpa [t, hφ] using hInstMem

theorem all_counterexample_of_containsAllCounterexampleAxioms
    {T : ClosedTheorySet (HInf Base Const)}
    (hClosed : ClosedTheorySet.DeductivelyClosed (Const := HInf Base Const) T)
    (hAxioms :
      AllCounterexampleAxioms ⊆ T)
    {σ : Ty Base} {φ : Formula (HInf Base Const) [σ]}
    (hAll : (.all φ : ClosedFormula (HInf Base Const)) ∉ T) :
    ∃ t : ClosedTerm (HInf Base Const) σ, instantiate (Base := Base) t φ ∉ T := by
  rcases exists_stage_formula (Base := Base) (Const := Const) φ with ⟨n, φ', hφ⟩
  let t : ClosedTerm (HInf Base Const) σ :=
    liftTerm (Base := Base) (Const := Const)
      (HenkinConstStage.allCounterexampleTerm (Base := Base) (Const := Const) φ')
  refine ⟨t, ?_⟩
  intro hInst
  have hInst' :
      instantiate (Base := Base) t
        (liftFormula (Base := Base) (Const := Const) φ') ∈ T := by
    simpa [hφ] using hInst
  have hAx :
      allCounterexampleAxiom (Base := Base) (Const := Const) φ' ∈ T :=
    hAxioms
      (allCounterexampleAxiom_mem_allCounterexampleAxioms
        (Base := Base) (Const := Const) φ')
  have hAllProv :
      ClosedTheorySet.Provable (Const := HInf Base Const) T
        (.all (liftFormula (Base := Base) (Const := Const) φ')) :=
    ClosedTheorySet.provable_mp
      (Const := HInf Base Const)
      (T := T)
      (φ := instantiate (Base := Base) t
        (liftFormula (Base := Base) (Const := Const) φ'))
      (ψ := .all (liftFormula (Base := Base) (Const := Const) φ'))
      (ClosedTheorySet.provable_of_mem (Const := HInf Base Const) hAx)
      (ClosedTheorySet.provable_of_mem (Const := HInf Base Const) hInst')
  have hAll' :
      (.all (liftFormula (Base := Base) (Const := Const) φ') :
        ClosedFormula (HInf Base Const)) ∈ T :=
    hClosed hAllProv
  exact hAll (by simpa [hφ] using hAll')

theorem exists_witness_of_containsHenkinAxioms
    {T : ClosedTheorySet (HInf Base Const)}
    (hClosed : ClosedTheorySet.DeductivelyClosed (Const := HInf Base Const) T)
    (hAxioms : HenkinAxioms ⊆ T)
    {σ : Ty Base} {φ : Formula (HInf Base Const) [σ]}
    (hEx : (.ex φ : ClosedFormula (HInf Base Const)) ∈ T) :
    ∃ t : ClosedTerm (HInf Base Const) σ, instantiate (Base := Base) t φ ∈ T := by
  refine exists_witness_of_containsExWitnessAxioms (Base := Base) (Const := Const)
    hClosed ?_ hEx
  intro ψ hψ
  exact hAxioms (Or.inl hψ)

theorem all_counterexample_of_containsHenkinAxioms
    {T : ClosedTheorySet (HInf Base Const)}
    (hClosed : ClosedTheorySet.DeductivelyClosed (Const := HInf Base Const) T)
    (hAxioms : HenkinAxioms ⊆ T)
    {σ : Ty Base} {φ : Formula (HInf Base Const) [σ]}
    (hAll : (.all φ : ClosedFormula (HInf Base Const)) ∉ T) :
    ∃ t : ClosedTerm (HInf Base Const) σ, instantiate (Base := Base) t φ ∉ T := by
  refine all_counterexample_of_containsAllCounterexampleAxioms
    (Base := Base) (Const := Const) hClosed ?_ hAll
  intro ψ hψ
  exact hAxioms (Or.inr hψ)

theorem exists_world_of_consistent_with_henkinAxioms
    {T : ClosedTheorySet (HInf Base Const)}
    (hCons :
      ClosedTheorySet.Consistent (Const := HInf Base Const)
        (T ∪ HenkinAxioms)) :
    ∃ W : ClosedTheorySet.World (HInf Base Const),
      (∀ {ψ : ClosedFormula (HInf Base Const)}, ψ ∈ T → ψ ∈ W.carrier) ∧
      HenkinAxioms ⊆ W.carrier := by
  rcases ClosedTheorySet.exists_prime_extension_of_consistent
      (Const := HInf Base Const)
      (T := T ∪ HenkinAxioms)
      hCons with ⟨U, hExt, hClosed, hUCons, hPrime⟩
  have hBase : ∀ {ψ : ClosedFormula (HInf Base Const)}, ψ ∈ T → ψ ∈ U := by
    intro ψ hψ
    exact hExt (Or.inl hψ)
  have hHenkin : HenkinAxioms ⊆ U := by
    intro ψ hψ
    exact hExt (Or.inr hψ)
  refine ⟨
    { carrier := U
      closed := hClosed
      consistent := hUCons
      prime_or := hPrime
      exists_witness := ?_
      all_counterexample := ?_ },
    hBase,
    hHenkin⟩
  · intro σ φ hEx
    exact exists_witness_of_containsHenkinAxioms
      (Base := Base) (Const := Const) hClosed hHenkin hEx
  · intro σ φ hAll
    exact all_counterexample_of_containsHenkinAxioms
      (Base := Base) (Const := Const) hClosed hHenkin hAll

theorem exists_world_separating_of_notProvable
    {T : ClosedTheorySet (HInf Base Const)}
    {φ : ClosedFormula (HInf Base Const)}
    (hHenkin : HenkinAxioms ⊆ T)
    (hNot : ¬ClosedTheorySet.Provable (Const := HInf Base Const) T φ) :
    ∃ W : ClosedTheorySet.World (HInf Base Const),
      (∀ {ψ : ClosedFormula (HInf Base Const)}, ψ ∈ T → ψ ∈ W.carrier) ∧
      HenkinAxioms ⊆ W.carrier ∧
      φ ∉ W.carrier := by
  rcases ClosedTheorySet.exists_prime_extension_separating
      (Const := HInf Base Const)
      (T := T)
      (φ := φ)
      hNot with
    ⟨U, hExt, hClosed, hUCons, hPrime, hOmit⟩
  have hHenkinU : HenkinAxioms ⊆ U := by
    intro ψ hψ
    exact hExt (hHenkin hψ)
  refine ⟨
    { carrier := U
      closed := hClosed
      consistent := hUCons
      prime_or := hPrime
      exists_witness := ?_
      all_counterexample := ?_ },
    hExt,
    hHenkinU,
    hOmit⟩
  · intro σ ψ hEx
    exact exists_witness_of_containsHenkinAxioms
      (Base := Base) (Const := Const) hClosed hHenkinU hEx
  · intro σ ψ hAll
    exact all_counterexample_of_containsHenkinAxioms
      (Base := Base) (Const := Const) hClosed hHenkinU hAll

end HenkinConstInfinity

end Mettapedia.Logic.HOL
