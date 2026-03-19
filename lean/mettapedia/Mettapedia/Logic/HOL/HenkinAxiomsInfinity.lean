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

/-- The existential Henkin axioms generated specifically from stage `n` formulas. -/
def ExWitnessAxiomsAtStage (n : Nat) : ClosedTheorySet (HInf Base Const) :=
  fun ψ =>
    ∃ (σ : Ty Base) (φ : Formula (HenkinConstStage Base Const n) [σ]),
      ψ = exWitnessAxiom (Base := Base) (Const := Const) φ

/-- The universal counterexample Henkin axioms generated specifically from stage `n` formulas. -/
def AllCounterexampleAxiomsAtStage (n : Nat) : ClosedTheorySet (HInf Base Const) :=
  fun ψ =>
    ∃ (σ : Ty Base) (φ : Formula (HenkinConstStage Base Const n) [σ]),
      ψ = allCounterexampleAxiom (Base := Base) (Const := Const) φ

/-- The cumulative Henkin axioms generated specifically from stage `n` formulas. -/
def HenkinAxiomsAtStage (n : Nat) : ClosedTheorySet (HInf Base Const) :=
  ExWitnessAxiomsAtStage (Base := Base) (Const := Const) n ∪
    AllCounterexampleAxiomsAtStage (Base := Base) (Const := Const) n

/-- The cumulative Henkin axioms generated up to stage `n`. -/
def HenkinAxiomsUpTo (n : Nat) : ClosedTheorySet (HInf Base Const) :=
  fun ψ => ∃ k : Nat, k ≤ n ∧ ψ ∈ HenkinAxiomsAtStage (Base := Base) (Const := Const) k

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

theorem exWitnessAxiom_mem_exWitnessAxiomsAtStage {n : Nat} {σ : Ty Base}
    (φ : Formula (HenkinConstStage Base Const n) [σ]) :
    exWitnessAxiom (Base := Base) (Const := Const) φ ∈
      ExWitnessAxiomsAtStage (Base := Base) (Const := Const) n :=
  ⟨σ, φ, rfl⟩

theorem allCounterexampleAxiom_mem_allCounterexampleAxiomsAtStage
    {n : Nat} {σ : Ty Base}
    (φ : Formula (HenkinConstStage Base Const n) [σ]) :
    allCounterexampleAxiom (Base := Base) (Const := Const) φ ∈
      AllCounterexampleAxiomsAtStage (Base := Base) (Const := Const) n :=
  ⟨σ, φ, rfl⟩

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

theorem exWitnessAxiomsAtStage_subset_henkinAxioms (n : Nat) :
    ExWitnessAxiomsAtStage (Base := Base) (Const := Const) n ⊆
      HenkinAxioms (Base := Base) (Const := Const) := by
  intro ψ hψ
  rcases hψ with ⟨σ, φ, rfl⟩
  exact exWitnessAxiom_mem_henkinAxioms (Base := Base) (Const := Const) φ

theorem allCounterexampleAxiomsAtStage_subset_henkinAxioms (n : Nat) :
    AllCounterexampleAxiomsAtStage (Base := Base) (Const := Const) n ⊆
      HenkinAxioms (Base := Base) (Const := Const) := by
  intro ψ hψ
  rcases hψ with ⟨σ, φ, rfl⟩
  exact allCounterexampleAxiom_mem_henkinAxioms (Base := Base) (Const := Const) φ

theorem henkinAxiomsAtStage_subset_henkinAxioms (n : Nat) :
    HenkinAxiomsAtStage (Base := Base) (Const := Const) n ⊆
      HenkinAxioms (Base := Base) (Const := Const) := by
  intro ψ hψ
  rcases hψ with hψ | hψ
  · exact exWitnessAxiomsAtStage_subset_henkinAxioms (Base := Base) (Const := Const) n hψ
  · exact
      allCounterexampleAxiomsAtStage_subset_henkinAxioms
        (Base := Base) (Const := Const) n hψ

theorem henkinAxiomsAtStage_subset_henkinAxiomsUpTo {m n : Nat} (hmn : m ≤ n) :
    HenkinAxiomsAtStage (Base := Base) (Const := Const) m ⊆
      HenkinAxiomsUpTo (Base := Base) (Const := Const) n := by
  intro ψ hψ
  exact ⟨m, hmn, hψ⟩

theorem henkinAxiomsUpTo_mono {m n : Nat} (hmn : m ≤ n) :
    HenkinAxiomsUpTo (Base := Base) (Const := Const) m ⊆
      HenkinAxiomsUpTo (Base := Base) (Const := Const) n := by
  intro ψ hψ
  rcases hψ with ⟨k, hkm, hkψ⟩
  exact ⟨k, Nat.le_trans hkm hmn, hkψ⟩

theorem henkinAxiomsUpTo_subset_henkinAxioms (n : Nat) :
    HenkinAxiomsUpTo (Base := Base) (Const := Const) n ⊆
      HenkinAxioms (Base := Base) (Const := Const) := by
  intro ψ hψ
  rcases hψ with ⟨k, -, hkψ⟩
  exact henkinAxiomsAtStage_subset_henkinAxioms (Base := Base) (Const := Const) k hkψ

theorem mem_henkinAxioms_iff_exists_stage
    {ψ : ClosedFormula (HInf Base Const)} :
    ψ ∈ HenkinAxioms (Base := Base) (Const := Const) ↔
      ∃ n : Nat, ψ ∈ HenkinAxiomsAtStage (Base := Base) (Const := Const) n := by
  constructor
  · intro hψ
    rcases hψ with hψ | hψ
    · rcases hψ with ⟨n, σ, φ, rfl⟩
      exact ⟨n, Or.inl ⟨σ, φ, rfl⟩⟩
    · rcases hψ with ⟨n, σ, φ, rfl⟩
      exact ⟨n, Or.inr ⟨σ, φ, rfl⟩⟩
  · rintro ⟨n, hψ⟩
    exact henkinAxiomsAtStage_subset_henkinAxioms (Base := Base) (Const := Const) n hψ

theorem mem_henkinAxiomsUpTo_iff_exists_stage_le
    {n : Nat} {ψ : ClosedFormula (HInf Base Const)} :
    ψ ∈ HenkinAxiomsUpTo (Base := Base) (Const := Const) n ↔
      ∃ k : Nat, k ≤ n ∧ ψ ∈ HenkinAxiomsAtStage (Base := Base) (Const := Const) k := by
  rfl

theorem exists_henkinAxiomsUpTo_list_bound
    (Γ : List (ClosedFormula (HInf Base Const))) :
    ∃ n : Nat,
      ∀ {ψ : ClosedFormula (HInf Base Const)},
        ψ ∈ Γ →
        ψ ∈ HenkinAxioms (Base := Base) (Const := Const) →
        ψ ∈ HenkinAxiomsUpTo (Base := Base) (Const := Const) n := by
  induction Γ with
  | nil =>
      refine ⟨0, ?_⟩
      intro ψ hψ
      cases hψ
  | cons ψ Γ ih =>
      rcases ih with ⟨n, hn⟩
      by_cases hψHenkin : ψ ∈ HenkinAxioms (Base := Base) (Const := Const)
      · rcases (mem_henkinAxioms_iff_exists_stage (Base := Base) (Const := Const) (ψ := ψ)).1 hψHenkin with
          ⟨k, hk⟩
        refine ⟨max k n, ?_⟩
        intro ξ hξ hξHenkin
        rcases List.mem_cons.mp hξ with hEq | hξ
        · exact
            henkinAxiomsAtStage_subset_henkinAxiomsUpTo
              (Base := Base)
              (Const := Const)
              (m := k)
              (n := max k n)
              (Nat.le_max_left _ _)
              (by simpa [hEq] using hk)
        · exact
            henkinAxiomsUpTo_mono
              (Base := Base)
              (Const := Const)
              (m := n)
              (n := max k n)
              (Nat.le_max_right _ _)
              (hn hξ hξHenkin)
      · refine ⟨n, ?_⟩
        intro ξ hξ hξHenkin
        rcases List.mem_cons.mp hξ with hEq | hξ
        · exact False.elim (hψHenkin (by simpa [hEq] using hξHenkin))
        · exact hn hξ hξHenkin

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
