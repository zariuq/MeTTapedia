import Mettapedia.Logic.HOL.ParamWorld
import Mettapedia.Logic.HOL.CanonicalExtension

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u}

/-!
# Truth Lemma for Growing-Domain Kripke Model  [MAINLINE]

This file proves that membership in a `PrimeTheory` satisfies the Kripke
forcing clauses for all connectives. Combined with the growing-domain
infrastructure in `ParamWorld.lean`, this gives the truth lemma for the
plain intuitionistic HOL completeness proof.

## Proved (>80% confidence cases)
- Propositional: ⊤, ⊥, ∧, ∨
- Implication and negation (using same-context prime extension)
- Universal (using cross-context `exists_paramExt_omitting`)
- Existential forward direction (forcing → membership)

## Deferred
- Constructing saturated prime theories (existential witness closure) from
  arbitrary non-provability remains separate infrastructure work.
-/

section HelperLemmas

variable {Const : Ty Base → Type v}

/-- Universal elimination at the theory-set level. -/
theorem ClosedTheorySet.provable_allE
    {T : ClosedTheorySet Const}
    {σ : Ty Base} {ψ : Formula Const [σ]}
    (t : ClosedTerm Const σ)
    (h : ClosedTheorySet.Provable T (.all ψ)) :
    ClosedTheorySet.Provable T (instantiate (Base := Base) t ψ) := by
  rcases h with ⟨support, hSup, d⟩
  exact ⟨support, hSup, .allE t d⟩

/-- Existential introduction at the theory-set level. -/
theorem ClosedTheorySet.provable_exI
    {T : ClosedTheorySet Const}
    {σ : Ty Base} {ψ : Formula Const [σ]}
    (t : ClosedTerm Const σ)
    (h : ClosedTheorySet.Provable T (instantiate (Base := Base) t ψ)) :
    ClosedTheorySet.Provable T (.ex ψ) := by
  rcases h with ⟨support, hSup, d⟩
  exact ⟨support, hSup, .exI t d⟩

/-- Negation introduction from insert: if `insert φ T ⊢ ⊥`, then `T ⊢ ¬φ`. -/
theorem ClosedTheorySet.provable_not_of_insert
    {T : ClosedTheorySet Const}
    {φ : ClosedFormula Const}
    (h : ClosedTheorySet.Provable (insert φ T) (.bot : ClosedFormula Const)) :
    ClosedTheorySet.Provable T (.not φ) := by
  rcases h with ⟨Γ, hΓ, hBot⟩
  let Γ' : List (ClosedFormula Const) := Γ.filter (fun ξ => ξ ≠ φ)
  have hmono : ExtDerivation Const (φ :: Γ') .bot := by
    refine ExtDerivation.mono ?_ hBot
    intro ξ hξ
    by_cases hEq : ξ = φ
    · subst hEq; simp
    · simp [Γ', List.mem_filter, hξ, hEq]
  refine ⟨Γ', ?_, .notI hmono⟩
  intro ξ hξ
  have hξΓ : ξ ∈ Γ := (List.mem_filter.mp hξ).1
  have hξNe : ξ ≠ φ := by
    intro hEq
    have := (List.mem_filter.mp hξ).2
    simp [hEq] at this
  have hξInsert := hΓ ξ hξΓ
  simp at hξInsert
  exact hξInsert.resolve_left hξNe

end HelperLemmas

section TruthLemma

variable {Const : Ty Base → Type v} {Γ : Ctx Base}

namespace PrimeTheory

/-- The right boundary for existential-backward reasoning:
a prime theory equipped with existential witness closure. -/
structure Saturated (Const : Ty Base → Type v) (Γ : Ctx Base)
    extends PrimeTheory Const Γ where
  exists_witness :
    ∀ {σ : Ty Base} {ψ : Formula (ParamConst Const Γ) [σ]},
      (.ex ψ : ClosedFormula (ParamConst Const Γ)) ∈ carrier →
        ∃ t : ClosedTerm (ParamConst Const Γ) σ,
          instantiate (Base := Base) t ψ ∈ carrier

/-- One-step existential witness axioms over `ParamConst Const Γ` from a
designated witness chooser. -/
def ExWitnessAxioms
    (choose :
      {σ : Ty Base} →
        Formula (ParamConst Const Γ) [σ] →
          ClosedTerm (ParamConst Const Γ) σ) :
    ClosedTheorySet (ParamConst Const Γ) :=
  fun χ =>
    ∃ (σ : Ty Base) (ψ : Formula (ParamConst Const Γ) [σ]),
      χ = (.imp (.ex ψ) (instantiate (Base := Base) (choose ψ) ψ))

/-- Any deductively closed theory containing all designated existential witness
axioms is existentially witness-closed. -/
theorem exists_witness_of_containsExWitnessAxioms
    (choose :
      {σ : Ty Base} →
        Formula (ParamConst Const Γ) [σ] →
          ClosedTerm (ParamConst Const Γ) σ)
    {T : ClosedTheorySet (ParamConst Const Γ)}
    (hClosed : ClosedTheorySet.DeductivelyClosed T)
    (hAxioms : ExWitnessAxioms (Γ := Γ) choose ⊆ T)
    {σ : Ty Base} {ψ : Formula (ParamConst Const Γ) [σ]}
    (hEx : (.ex ψ : ClosedFormula (ParamConst Const Γ)) ∈ T) :
    ∃ t : ClosedTerm (ParamConst Const Γ) σ,
      instantiate (Base := Base) t ψ ∈ T := by
  let t : ClosedTerm (ParamConst Const Γ) σ := choose ψ
  have hAx :
      (.imp (.ex ψ) (instantiate (Base := Base) t ψ) :
        ClosedFormula (ParamConst Const Γ)) ∈ T :=
    hAxioms ⟨σ, ψ, rfl⟩
  have hInstProv :
      ClosedTheorySet.Provable T (instantiate (Base := Base) t ψ) :=
    ClosedTheorySet.provable_mp
      (ClosedTheorySet.provable_of_mem hAx)
      (ClosedTheorySet.provable_of_mem hEx)
  exact ⟨t, hClosed hInstProv⟩

/-- If adding designated witness axioms to a prime theory still does not prove
`χ`, one can take a separating prime extension that is existentially saturated
for that chooser. -/
theorem exists_saturated_extension_separating_of_notProvable
    (choose :
      {σ : Ty Base} →
        Formula (ParamConst Const Γ) [σ] →
          ClosedTerm (ParamConst Const Γ) σ)
    {W : PrimeTheory Const Γ}
    {χ : ClosedFormula (ParamConst Const Γ)}
    (hNot :
      ¬ ClosedTheorySet.Provable
          (fun φ =>
            φ ∈ W.carrier ∨
              φ ∈ ExWitnessAxioms (Γ := Γ) choose)
          χ) :
    ∃ Ws : PrimeTheory.Saturated Const Γ,
      (∀ {ψ : ClosedFormula (ParamConst Const Γ)},
        ψ ∈ W.carrier → ψ ∈ Ws.carrier) ∧
      χ ∉ Ws.carrier := by
  rcases ClosedTheorySet.exists_prime_extension_separating (T := fun φ =>
      φ ∈ W.carrier ∨ φ ∈ ExWitnessAxioms (Γ := Γ) choose) (φ := χ) hNot with
    ⟨U, hExt, hClosed, hCons, hPrime, hOmit⟩
  have hExtW :
      ∀ {ψ : ClosedFormula (ParamConst Const Γ)},
        ψ ∈ W.carrier → ψ ∈ U := by
    intro ψ hψ
    exact hExt (Or.inl hψ)
  have hExtAxioms :
      ExWitnessAxioms (Γ := Γ) choose ⊆ U := by
    intro ψ hψ
    exact hExt (Or.inr hψ)
  refine ⟨
    { carrier := U
      closed := hClosed
      consistent := hCons
      prime_or := hPrime
      exists_witness := ?_ },
    hExtW,
    hOmit⟩
  intro σ ψ hEx
  exact exists_witness_of_containsExWitnessAxioms
    (Γ := Γ)
    choose
    hClosed
    hExtAxioms
    hEx

/-- Set-level variant of `exists_saturated_extension_separating_of_notProvable`:
starting from an arbitrary base theory set `T`, not necessarily a prime theory. -/
theorem exists_saturated_world_separating_of_notProvable
    (choose :
      {σ : Ty Base} →
        Formula (ParamConst Const Γ) [σ] →
          ClosedTerm (ParamConst Const Γ) σ)
    {T : ClosedTheorySet (ParamConst Const Γ)}
    {χ : ClosedFormula (ParamConst Const Γ)}
    (hNot :
      ¬ ClosedTheorySet.Provable
          (fun φ =>
            φ ∈ T ∨
              φ ∈ ExWitnessAxioms (Γ := Γ) choose)
          χ) :
    ∃ Ws : PrimeTheory.Saturated Const Γ,
      (∀ {ψ : ClosedFormula (ParamConst Const Γ)},
        ψ ∈ T → ψ ∈ Ws.carrier) ∧
      χ ∉ Ws.carrier := by
  rcases ClosedTheorySet.exists_prime_extension_separating (T := fun φ =>
      φ ∈ T ∨ φ ∈ ExWitnessAxioms (Γ := Γ) choose) (φ := χ) hNot with
    ⟨U, hExt, hClosed, hCons, hPrime, hOmit⟩
  have hExtT :
      ∀ {ψ : ClosedFormula (ParamConst Const Γ)},
        ψ ∈ T → ψ ∈ U := by
    intro ψ hψ
    exact hExt (Or.inl hψ)
  have hExtAxioms :
      ExWitnessAxioms (Γ := Γ) choose ⊆ U := by
    intro ψ hψ
    exact hExt (Or.inr hψ)
  refine ⟨
    { carrier := U
      closed := hClosed
      consistent := hCons
      prime_or := hPrime
      exists_witness := ?_ },
    hExtT,
    hOmit⟩
  intro σ ψ hEx
  exact exists_witness_of_containsExWitnessAxioms
    (Γ := Γ)
    choose
    hClosed
    hExtAxioms
    hEx

/-- Exact arbitrary-context bridge for saturation preserving omission.

This packages a chooser together with the only missing local conservativity
premise needed to saturate a prime theory while preserving omission of a
designated formula. -/
structure SaturationBridge (Base : Type u) (Const : Ty Base → Type v) where
  choose :
    {Γ : Ctx Base} →
      {σ : Ty Base} →
        Formula (ParamConst Const Γ) [σ] →
          ClosedTerm (ParamConst Const Γ) σ
  augmented_notProvable :
    ∀ {Γ : Ctx Base}
      {W : PrimeTheory Const Γ}
      {χ : ClosedFormula (ParamConst Const Γ)},
      χ ∉ W.carrier →
        ¬ ClosedTheorySet.Provable
            (fun φ =>
              φ ∈ W.carrier ∨
                φ ∈ ExWitnessAxioms (Γ := Γ) choose)
            χ

/-- A saturation bridge immediately yields omission-preserving saturation for
arbitrary prime theories. -/
theorem SaturationBridge.saturate
    (B : SaturationBridge Base Const)
    {Γ : Ctx Base}
    {W : PrimeTheory Const Γ}
    {χ : ClosedFormula (ParamConst Const Γ)}
    (hOmit : χ ∉ W.carrier) :
    ∃ Ws : PrimeTheory.Saturated Const Γ,
      (∀ {ψ : ClosedFormula (ParamConst Const Γ)},
        ψ ∈ W.carrier → ψ ∈ Ws.carrier) ∧
      χ ∉ Ws.carrier := by
  exact exists_saturated_extension_separating_of_notProvable
    (Base := Base)
    (Const := Const)
    (Γ := Γ)
    (choose := B.choose)
    (W := W)
    (χ := χ)
    (B.augmented_notProvable hOmit)

end PrimeTheory

/-! ### Propositional truth lemma -/

theorem PrimeTheory.mem_and_iff {W : PrimeTheory Const Γ}
    {φ ψ : ClosedFormula (ParamConst Const Γ)} :
    (.and φ ψ : ClosedFormula (ParamConst Const Γ)) ∈ W.carrier ↔
      φ ∈ W.carrier ∧ ψ ∈ W.carrier :=
  ⟨fun h => ⟨W.and_left_mem h, W.and_right_mem h⟩,
   fun ⟨hφ, hψ⟩ => W.and_mem hφ hψ⟩

theorem PrimeTheory.mem_or_iff {W : PrimeTheory Const Γ}
    {φ ψ : ClosedFormula (ParamConst Const Γ)} :
    (.or φ ψ : ClosedFormula (ParamConst Const Γ)) ∈ W.carrier ↔
      φ ∈ W.carrier ∨ ψ ∈ W.carrier :=
  ⟨fun h => W.prime_or h,
   fun h => h.elim W.or_left_mem W.or_right_mem⟩

/-! ### Implication truth lemma -/

/-- Kripke forcing clause for implication on same-context prime theories. -/
def PrimeTheory.ForcesImp (W : PrimeTheory Const Γ)
    (φ ψ : ClosedFormula (ParamConst Const Γ)) : Prop :=
  ∀ ⦃V : PrimeTheory Const Γ⦄,
    (∀ {χ : ClosedFormula (ParamConst Const Γ)}, χ ∈ W.carrier → χ ∈ V.carrier) →
    φ ∈ V.carrier → ψ ∈ V.carrier

/-- If `φ → ψ ∉ W.carrier`, then `insert φ W.carrier` does not prove `ψ`. -/
theorem PrimeTheory.not_provable_insert_of_imp_not_mem
    {W : PrimeTheory Const Γ}
    {φ ψ : ClosedFormula (ParamConst Const Γ)}
    (hImp : (.imp φ ψ : ClosedFormula (ParamConst Const Γ)) ∉ W.carrier) :
    ¬ ClosedTheorySet.Provable (insert φ W.carrier) ψ := by
  intro hψ
  exact hImp (W.closed (ClosedTheorySet.provable_imp_of_insert hψ))

/-- The implication truth lemma: the Kripke forcing clause for `→` is
equivalent to membership of the implication formula.

Forward (forcing → membership) uses proof by contradiction + Lindenbaum
prime extension separating `{φ}` from `ψ`.
Backward (membership → forcing) is direct via monotonicity + modus ponens. -/
theorem PrimeTheory.forcesImp_iff_mem {W : PrimeTheory Const Γ}
    {φ ψ : ClosedFormula (ParamConst Const Γ)} :
    W.ForcesImp φ ψ ↔
      (.imp φ ψ : ClosedFormula (ParamConst Const Γ)) ∈ W.carrier := by
  constructor
  · -- forcing → membership (hard direction)
    intro hForces
    by_contra hImp
    have hNotProv := W.not_provable_insert_of_imp_not_mem hImp
    rcases ClosedTheorySet.exists_prime_extension_separating hNotProv with
      ⟨U, hExt, hClosed, hCons, hPrime, hOmit⟩
    -- Build V : PrimeTheory extending W ∪ {φ}, omitting ψ
    let V : PrimeTheory Const Γ := ⟨U, hClosed, hCons, hPrime⟩
    have hWV : ∀ {χ : ClosedFormula (ParamConst Const Γ)},
        χ ∈ W.carrier → χ ∈ V.carrier := fun hχ =>
      hExt (Set.mem_insert_of_mem _ hχ)
    have hφV : φ ∈ V.carrier :=
      hExt (Set.mem_insert _ _)
    have hψV : ψ ∈ V.carrier := hForces hWV hφV
    exact hOmit hψV
  · -- membership → forcing (easy direction)
    intro hImp V hWV hφ
    exact V.mp (hWV hImp) hφ

/-! ### Negation truth lemma -/

/-- Kripke forcing clause for negation on same-context prime theories. -/
def PrimeTheory.ForcesNot (W : PrimeTheory Const Γ)
    (φ : ClosedFormula (ParamConst Const Γ)) : Prop :=
  ∀ ⦃V : PrimeTheory Const Γ⦄,
    (∀ {χ : ClosedFormula (ParamConst Const Γ)}, χ ∈ W.carrier → χ ∈ V.carrier) →
    φ ∉ V.carrier

/-- The negation truth lemma. -/
theorem PrimeTheory.forcesNot_iff_mem {W : PrimeTheory Const Γ}
    {φ : ClosedFormula (ParamConst Const Γ)} :
    W.ForcesNot φ ↔
      (.not φ : ClosedFormula (ParamConst Const Γ)) ∈ W.carrier := by
  constructor
  · -- forcing → membership
    intro hForces
    by_contra hNot
    -- If ¬φ ∉ W.carrier, then insert φ W.carrier is consistent
    -- (because if it proved ⊥, by impI W.carrier proves φ → ⊥ = ¬φ, contradiction)
    have hCons : ClosedTheorySet.Consistent (insert φ W.carrier) := by
      intro hIncons
      exact hNot (W.closed (ClosedTheorySet.provable_not_of_insert hIncons))
    rcases ClosedTheorySet.exists_prime_extension_of_consistent hCons with
      ⟨U, hExt, hClosed, hUCons, hPrime⟩
    let V : PrimeTheory Const Γ := ⟨U, hClosed, hUCons, hPrime⟩
    have hWV : ∀ {χ : ClosedFormula (ParamConst Const Γ)},
        χ ∈ W.carrier → χ ∈ V.carrier := fun hχ =>
      hExt (Set.mem_insert_of_mem _ hχ)
    have hφV : φ ∈ V.carrier := hExt (Set.mem_insert _ _)
    exact hForces hWV hφV
  · -- membership → forcing
    intro hNot V hWV hφ
    have hNotV := hWV hNot
    exact V.bot_not_mem (V.closed
      (ClosedTheorySet.provable_bot_of_not
        (ClosedTheorySet.provable_of_mem hNotV)
        (ClosedTheorySet.provable_of_mem hφ)))

/-! ### Universal truth lemma -/

/-- Cross-context Kripke forcing for universals. V lives at `σ :: Γ`,
extending W's theory via `liftParamCtxFormula`. -/
def PrimeTheory.ForcesAll (W : PrimeTheory Const Γ)
    (σ : Ty Base) (ψ : Formula (ParamConst Const Γ) [σ]) : Prop :=
  ∀ (V : PrimeTheory Const (σ :: Γ)),
    (∀ {φ : ClosedFormula (ParamConst Const Γ)},
      φ ∈ W.carrier → liftParamCtxFormula σ φ ∈ V.carrier) →
    ∀ t : ClosedTerm (ParamConst Const (σ :: Γ)) σ,
      instantiate t (liftParamCtx ψ) ∈ V.carrier

/-- The universal truth lemma: the Kripke forcing clause for `∀` is
equivalent to membership.

Forward uses `exists_paramExt_omitting` for the contrapositive.
Backward uses allE at the extended world. -/
theorem PrimeTheory.forcesAll_iff_mem {W : PrimeTheory Const Γ}
    {σ : Ty Base} {ψ : Formula (ParamConst Const Γ) [σ]} :
    W.ForcesAll σ ψ ↔
      (.all ψ : ClosedFormula (ParamConst Const Γ)) ∈ W.carrier := by
  constructor
  · -- forcing → membership (uses exists_paramExt_omitting)
    intro hForces
    by_contra hAll
    rcases W.exists_paramExt_omitting hAll with ⟨V, hMono, t, hOmit⟩
    exact hOmit (hForces V hMono t)
  · -- membership → forcing (uses allE)
    intro hAll V hMono t
    -- (.all ψ) ∈ W.carrier, so liftParamCtxFormula σ (.all ψ) ∈ V.carrier
    have hAllV := hMono hAll
    -- liftParamCtxFormula σ (.all ψ) = .all (liftParamCtx ψ)
    -- (since mapConst preserves .all)
    have hEq : liftParamCtxFormula σ (.all ψ : ClosedFormula (ParamConst Const Γ)) =
        (.all (liftParamCtx ψ) : ClosedFormula (ParamConst Const (σ :: Γ))) := rfl
    rw [hEq] at hAllV
    -- By allE with t, instantiate t (liftParamCtx ψ) ∈ V.carrier
    exact V.closed (ClosedTheorySet.provable_allE t
      (ClosedTheorySet.provable_of_mem hAllV))

/-! ### Existential truth lemma -/

/-- Forward direction: a witness in the carrier implies the existential
is in the carrier. -/
theorem PrimeTheory.ex_mem_of_witness {W : PrimeTheory Const Γ}
    {σ : Ty Base} {ψ : Formula (ParamConst Const Γ) [σ]}
    {t : ClosedTerm (ParamConst Const Γ) σ}
    (ht : instantiate (Base := Base) t ψ ∈ W.carrier) :
    (.ex ψ : ClosedFormula (ParamConst Const Γ)) ∈ W.carrier :=
  W.closed (ClosedTheorySet.provable_exI t
    (ClosedTheorySet.provable_of_mem ht))

/-- Kripke forcing clause for existential formulas at a fixed context. -/
def PrimeTheory.ForcesEx (W : PrimeTheory Const Γ)
    (σ : Ty Base) (ψ : Formula (ParamConst Const Γ) [σ]) : Prop :=
  ∃ t : ClosedTerm (ParamConst Const Γ) σ,
    instantiate (Base := Base) t ψ ∈ W.carrier

/-- Existential forcing implies existential membership for any prime theory. -/
theorem PrimeTheory.mem_ex_of_forcesEx {W : PrimeTheory Const Γ}
    {σ : Ty Base} {ψ : Formula (ParamConst Const Γ) [σ]}
    (hForces : W.ForcesEx σ ψ) :
    (.ex ψ : ClosedFormula (ParamConst Const Γ)) ∈ W.carrier := by
  rcases hForces with ⟨t, ht⟩
  exact W.ex_mem_of_witness ht

/-- Backward direction on the right theory boundary:
if `∃x.ψ` is in a saturated prime carrier, a concrete witness instance is too. -/
theorem PrimeTheory.witness_of_ex_mem {W : PrimeTheory.Saturated Const Γ}
    {σ : Ty Base} {ψ : Formula (ParamConst Const Γ) [σ]}
    (h : (.ex ψ : ClosedFormula (ParamConst Const Γ)) ∈ W.carrier) :
    ∃ t : ClosedTerm (ParamConst Const Γ) σ,
      instantiate (Base := Base) t ψ ∈ W.carrier :=
  W.exists_witness h

/-- Existential membership implies existential forcing on saturated worlds. -/
theorem PrimeTheory.forcesEx_of_mem {W : PrimeTheory.Saturated Const Γ}
    {σ : Ty Base} {ψ : Formula (ParamConst Const Γ) [σ]}
    (h : (.ex ψ : ClosedFormula (ParamConst Const Γ)) ∈ W.carrier) :
    W.ForcesEx σ ψ := by
  exact W.exists_witness h

/-- Existential truth lemma at the saturated-world boundary. -/
theorem PrimeTheory.forcesEx_iff_mem {W : PrimeTheory.Saturated Const Γ}
    {σ : Ty Base} {ψ : Formula (ParamConst Const Γ) [σ]} :
    W.ForcesEx σ ψ ↔
      (.ex ψ : ClosedFormula (ParamConst Const Γ)) ∈ W.carrier := by
  constructor
  · intro hForces
    exact PrimeTheory.mem_ex_of_forcesEx (W := W.toPrimeTheory) hForces
  · intro hEx
    exact PrimeTheory.forcesEx_of_mem (W := W) hEx

/-- Recursive forcing predicate on saturated prime theories.

Logical connectives use the Kripke clauses proved above. Residual atomic /
application / equality-shaped formulas are evaluated by direct carrier
membership at the current world. -/
def PrimeTheory.Saturated.Forces (W : PrimeTheory.Saturated Const Γ) :
    ClosedFormula (ParamConst Const Γ) → Prop
  | .top => True
  | .bot => False
  | .and φ ψ => W.Forces φ ∧ W.Forces ψ
  | .or φ ψ => W.Forces φ ∨ W.Forces ψ
  | .imp φ ψ => W.toPrimeTheory.ForcesImp φ ψ
  | .not φ => W.toPrimeTheory.ForcesNot φ
  | .all ψ => W.toPrimeTheory.ForcesAll _ ψ
  | .ex ψ => W.ForcesEx _ ψ
  | φ => φ ∈ W.carrier

/-- Saturated-world truth lemma: recursive forcing is exactly carrier
membership. This is the wrapper theorem that turns the clausewise lemmas above
into a root-world counterexample theorem. -/
theorem PrimeTheory.Saturated.forces_iff_mem {W : PrimeTheory.Saturated Const Γ} :
    ∀ φ : ClosedFormula (ParamConst Const Γ), W.Forces φ ↔ φ ∈ W.carrier
  | .var v => nomatch v
  | .const _ => by simp [PrimeTheory.Saturated.Forces]
  | .app _ _ => by simp [PrimeTheory.Saturated.Forces]
  | .top => by
      constructor
      · intro _
        exact PrimeTheory.top_mem (W := W.toPrimeTheory)
      · intro _
        simp [PrimeTheory.Saturated.Forces]
  | .bot => by
      constructor
      · intro h
        exact False.elim (by simpa [PrimeTheory.Saturated.Forces] using h)
      · intro h
        simpa [PrimeTheory.Saturated.Forces]
          using (PrimeTheory.bot_not_mem (W := W.toPrimeTheory) h)
  | .and φ ψ => by
      simpa [PrimeTheory.Saturated.Forces, forces_iff_mem (W := W) φ, forces_iff_mem (W := W) ψ]
        using (PrimeTheory.mem_and_iff (W := W.toPrimeTheory) (φ := φ) (ψ := ψ)).symm
  | .or φ ψ => by
      simpa [PrimeTheory.Saturated.Forces, forces_iff_mem (W := W) φ, forces_iff_mem (W := W) ψ]
        using (PrimeTheory.mem_or_iff (W := W.toPrimeTheory) (φ := φ) (ψ := ψ)).symm
  | .imp φ ψ => by
      simpa [PrimeTheory.Saturated.Forces]
        using (PrimeTheory.forcesImp_iff_mem (W := W.toPrimeTheory) (φ := φ) (ψ := ψ))
  | .not φ => by
      simpa [PrimeTheory.Saturated.Forces]
        using (PrimeTheory.forcesNot_iff_mem (W := W.toPrimeTheory) (φ := φ))
  | .eq _ _ => by simp [PrimeTheory.Saturated.Forces]
  | .all ψ => by
      simpa [PrimeTheory.Saturated.Forces]
        using (PrimeTheory.forcesAll_iff_mem (W := W.toPrimeTheory) (ψ := ψ))
  | .ex ψ => by
      simpa [PrimeTheory.Saturated.Forces]
        using (PrimeTheory.forcesEx_iff_mem (W := W) (ψ := ψ))

end TruthLemma

/-! ## Root World Construction -/

section RootWorld

variable {Const : Ty Base → Type v}

/-- Compact package for the remaining root-level saturation bridge.

It isolates exactly one unresolved ingredient: lifted augmented non-provability
for the chosen witness axioms at context `[]`. -/
structure RootSaturationBridge (Base : Type u) (Const : Ty Base → Type v) where
  choose :
    {σ : Ty Base} →
      Formula (ParamConst Const ([] : Ctx Base)) [σ] →
        ClosedTerm (ParamConst Const ([] : Ctx Base)) σ
  lifted_augmented_notProvable :
    ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
      ¬ ExtDerivation Const Δ φ →
        ¬ ClosedTheorySet.Provable
            (fun ψ =>
              ψ ∈ (Δ.map (liftParamFormula [])) ∨
                ψ ∈ PrimeTheory.ExWitnessAxioms
                  (Base := Base) (Const := Const) (Γ := ([] : Ctx Base)) choose)
            (liftParamFormula [] φ)

/-- Retract `ParamConst Const []` back to `Const`.

At context `[]`, `Var [] τ` is empty, so `ParamConst Const [] τ = Const τ ⊕ Empty`.
The retraction maps `Sum.inl c` back to `c`. -/
def retractParamEmpty : ∀ {τ : Ty Base}, ParamConst Const ([] : Ctx Base) τ → Const τ
  | _, Sum.inl c => c
  | _, Sum.inr v => nomatch v

@[simp] theorem retractParamEmpty_liftParam {τ : Ty Base} (c : Const τ) :
    retractParamEmpty (Sum.inl c : ParamConst Const ([] : Ctx Base) τ) = c := rfl

/-- At root context `[]`, every parameterized term is exactly the lift of its
retraction back to the original signature. -/
@[simp] theorem liftParam_retractParamEmpty
    {Γ : Ctx Base} {τ : Ty Base}
    (t : Term (ParamConst Const ([] : Ctx Base)) Γ τ) :
    liftParam (Base := Base) (Const := Const) (Γ' := ([] : Ctx Base))
      (mapConst (fun {τ} => retractParamEmpty (Base := Base) (Const := Const) (τ := τ)) t) = t := by
  rw [show liftParam (Base := Base) (Const := Const) (Γ' := ([] : Ctx Base))
      (mapConst (fun {τ} => retractParamEmpty (Base := Base) (Const := Const) (τ := τ)) t) =
      mapConst (fun {τ} (c : Const τ) => Sum.inl c)
        (mapConst (fun {τ} => retractParamEmpty (Base := Base) (Const := Const) (τ := τ)) t) by
      rfl]
  rw [Mettapedia.Logic.HOL.mapConst_comp]
  calc
    mapConst
        (fun {τ} c =>
          Sum.inl
            (retractParamEmpty (Base := Base) (Const := Const) (τ := τ) c))
        t =
      mapConst (fun {τ} c => c) t := by
        apply Mettapedia.Logic.HOL.mapConst_ext
        intro τ c
        cases c with
        | inl c => rfl
        | inr v => cases v
    _ = t := Mettapedia.Logic.HOL.mapConst_id t

/-- Retract a root-context witness chooser back to the original signature. -/
def rootChoose
    (choose :
      {σ : Ty Base} →
        Formula (ParamConst Const ([] : Ctx Base)) [σ] →
          ClosedTerm (ParamConst Const ([] : Ctx Base)) σ) :
    {σ : Ty Base} → Formula Const [σ] → ClosedTerm Const σ
  | _, ψ =>
      mapConst (fun {τ} => retractParamEmpty (Base := Base) (Const := Const) (τ := τ))
        (choose (liftParam (Base := Base) (Const := Const) (Γ' := ([] : Ctx Base)) ψ))

@[simp] theorem liftParam_rootChoose
    (choose :
      {σ : Ty Base} →
        Formula (ParamConst Const ([] : Ctx Base)) [σ] →
          ClosedTerm (ParamConst Const ([] : Ctx Base)) σ)
    {σ : Ty Base} (ψ : Formula Const [σ]) :
    liftParamTerm (Base := Base) (Const := Const) ([] : Ctx Base)
      (rootChoose (Base := Base) (Const := Const) choose ψ) =
      choose (liftParam (Base := Base) (Const := Const) (Γ' := ([] : Ctx Base)) ψ) := by
  unfold rootChoose liftParamTerm
  simpa using
    (liftParam_retractParamEmpty
      (Base := Base)
      (Const := Const)
      (Γ := [])
      (τ := σ)
      (t := choose (liftParam (Base := Base) (Const := Const) (Γ' := ([] : Ctx Base)) ψ)))

/-- Source-signature witness axioms induced by a root-context parameter chooser. -/
def RootExWitnessAxioms
    (choose :
      {σ : Ty Base} →
        Formula (ParamConst Const ([] : Ctx Base)) [σ] →
          ClosedTerm (ParamConst Const ([] : Ctx Base)) σ) :
    ClosedTheorySet Const :=
  fun χ =>
    ∃ (σ : Ty Base) (ψ : Formula Const [σ]),
      χ =
        (.imp
          (.ex ψ)
          (instantiate (Base := Base)
            (rootChoose (Base := Base) (Const := Const) choose ψ) ψ))

/-- Retracting a root witness axiom lands in the corresponding source-side
witness-axiom family. -/
theorem mem_rootExWitnessAxioms_of_mem_retract
    (choose :
      {σ : Ty Base} →
        Formula (ParamConst Const ([] : Ctx Base)) [σ] →
          ClosedTerm (ParamConst Const ([] : Ctx Base)) σ)
    {χ : ClosedFormula (ParamConst Const ([] : Ctx Base))}
    (hχ :
      χ ∈ PrimeTheory.ExWitnessAxioms
        (Base := Base) (Const := Const) (Γ := ([] : Ctx Base)) choose) :
    mapConst (fun {τ} => retractParamEmpty (Base := Base) (Const := Const) (τ := τ)) χ ∈
      RootExWitnessAxioms (Base := Base) (Const := Const) choose := by
  rcases hχ with ⟨σ, ψ, rfl⟩
  refine ⟨σ, mapConst (fun {τ} => retractParamEmpty (Base := Base) (Const := Const) (τ := τ)) ψ, ?_⟩
  have hψ :
      liftParam (Base := Base) (Const := Const) (Γ' := ([] : Ctx Base))
        (mapConst (fun {τ} => retractParamEmpty (Base := Base) (Const := Const) (τ := τ)) ψ) = ψ :=
    liftParam_retractParamEmpty (Base := Base) (Const := Const) ψ
  change
    mapConst (fun {τ} => retractParamEmpty (Base := Base) (Const := Const) (τ := τ))
        (.imp (.ex ψ) (instantiate (Base := Base) (choose ψ) ψ)) =
      (.imp
        (.ex (mapConst (fun {τ} => retractParamEmpty (Base := Base) (Const := Const) (τ := τ)) ψ))
        (instantiate (Base := Base)
          (rootChoose (Base := Base) (Const := Const) choose
            (mapConst (fun {τ} => retractParamEmpty (Base := Base) (Const := Const) (τ := τ)) ψ))
          (mapConst (fun {τ} => retractParamEmpty (Base := Base) (Const := Const) (τ := τ)) ψ)))
  simpa [rootChoose, hψ, Mettapedia.Logic.HOL.mapConst, Mettapedia.Logic.HOL.mapConst_instantiate]

/-- `mapConst retractParamEmpty` is a left inverse of `liftParam` at context `[]`. -/
@[simp] theorem mapConst_retractParamEmpty_liftParam
    (t : Term Const Γ τ) :
    mapConst retractParamEmpty
      (liftParam (Γ' := ([] : Ctx Base)) t) = t := by
  induction t with
  | var v => rfl
  | const c => rfl
  | app _ _ ih₁ ih₂ => simp [liftParam, mapConst, ih₁, ih₂]
  | lam _ ih => simp [liftParam, mapConst, ih]
  | top => rfl
  | bot => rfl
  | and _ _ ih₁ ih₂ => simp [liftParam, mapConst, ih₁, ih₂]
  | or _ _ ih₁ ih₂ => simp [liftParam, mapConst, ih₁, ih₂]
  | imp _ _ ih₁ ih₂ => simp [liftParam, mapConst, ih₁, ih₂]
  | not _ ih => simp [liftParam, mapConst, ih]
  | eq _ _ ih₁ ih₂ => simp [liftParam, mapConst, ih₁, ih₂]
  | all _ ih => simp [liftParam, mapConst, ih]
  | ex _ ih => simp [liftParam, mapConst, ih]

/-- `mapConst (Sum.inl)` is a left inverse of `mapConst retractParamEmpty`
for formulas that are lifts. -/
theorem retractParamEmpty_derivation
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const}
    (d : ExtDerivation (ParamConst Const ([] : Ctx Base))
      (Δ.map (liftParamFormula []))
      (liftParamFormula [] φ)) :
    ExtDerivation Const Δ φ := by
  have d' := ExtDerivation.mapConst retractParamEmpty d
  have hΔ : (Δ.map (liftParamFormula [])).map
      (Mettapedia.Logic.HOL.mapConst (fun {τ} => retractParamEmpty)) = Δ := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id Δ]
    exact List.map_congr_left fun χ _ => mapConst_retractParamEmpty_liftParam χ
  rw [hΔ] at d'
  convert d' using 1
  exact (mapConst_retractParamEmpty_liftParam φ).symm

/-- Non-provability transfers from `Const` to `ParamConst Const []`:
if `Const` can't derive `φ` from `Δ`, then `ParamConst Const []` can't
derive the lift. -/
theorem not_provable_liftParam_of_not_provable
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const}
    (h : ¬ ExtDerivation Const Δ φ) :
    ¬ ClosedTheorySet.Provable
      (Const := ParamConst Const ([] : Ctx Base))
      (fun ψ => ψ ∈ (Δ.map (liftParamFormula [])))
      (liftParamFormula [] φ) := by
  intro ⟨support, hSup, d⟩
  apply h
  apply retractParamEmpty_derivation
  exact ExtDerivation.mono (fun {ψ} hψ => hSup ψ hψ) d

/-- Any lifted derivation using root witness axioms retracts to a source-side
derivation using the corresponding retracted witness axioms. -/
theorem provable_rootExWitness_of_lifted_augmented
    (choose :
      {σ : Ty Base} →
        Formula (ParamConst Const ([] : Ctx Base)) [σ] →
          ClosedTerm (ParamConst Const ([] : Ctx Base)) σ)
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const}
    (hProv :
      ClosedTheorySet.Provable
        (Const := ParamConst Const ([] : Ctx Base))
        (fun ψ =>
          ψ ∈ (Δ.map (liftParamFormula [])) ∨
            ψ ∈ PrimeTheory.ExWitnessAxioms
              (Base := Base) (Const := Const) (Γ := ([] : Ctx Base)) choose)
        (liftParamFormula [] φ)) :
    ClosedTheorySet.Provable
      (Const := Const)
      (fun ψ =>
        ψ ∈ Δ ∨
          ψ ∈ RootExWitnessAxioms (Base := Base) (Const := Const) choose)
      φ := by
  rcases hProv with ⟨support, hSup, d⟩
  refine ⟨
    support.map (mapConst (fun {τ} => retractParamEmpty (Base := Base) (Const := Const) (τ := τ))),
    ?_,
    ?_⟩
  · intro ψ hψ
    rcases List.mem_map.mp hψ with ⟨ξ, hξ, rfl⟩
    rcases hSup ξ hξ with hξ | hξ
    · left
      rcases List.mem_map.mp hξ with ⟨χ, hχ, hEq⟩
      subst hEq
      simpa using hχ
    · right
      exact mem_rootExWitnessAxioms_of_mem_retract
        (Base := Base)
        (Const := Const)
        choose
        hξ
  · have d' :=
      ExtDerivation.mapConst
        (fun {τ} => retractParamEmpty (Base := Base) (Const := Const) (τ := τ))
        d
    simpa using d'

/-- Contrapositive transport of non-provability from the source augmented
witness theory to the lifted root augmented theory. -/
theorem not_provable_liftParam_augmented_of_not_provable_rootExWitness
    (choose :
      {σ : Ty Base} →
        Formula (ParamConst Const ([] : Ctx Base)) [σ] →
          ClosedTerm (ParamConst Const ([] : Ctx Base)) σ)
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const}
    (hNot :
      ¬ ClosedTheorySet.Provable
        (Const := Const)
        (fun ψ =>
          ψ ∈ Δ ∨
            ψ ∈ RootExWitnessAxioms (Base := Base) (Const := Const) choose)
        φ) :
    ¬ ClosedTheorySet.Provable
      (Const := ParamConst Const ([] : Ctx Base))
      (fun ψ =>
        ψ ∈ (Δ.map (liftParamFormula [])) ∨
          ψ ∈ PrimeTheory.ExWitnessAxioms
            (Base := Base) (Const := Const) (Γ := ([] : Ctx Base)) choose)
      (liftParamFormula [] φ) := by
  intro hProv
  exact hNot
    (provable_rootExWitness_of_lifted_augmented
      (Base := Base)
      (Const := Const)
      choose
      hProv)

/-- Corrected root-level bridge:
source-side non-provability is measured against the retracted witness axioms
induced by the chosen root witness policy. -/
structure RootExWitnessBridge (Base : Type u) (Const : Ty Base → Type v) where
  choose :
    {σ : Ty Base} →
      Formula (ParamConst Const ([] : Ctx Base)) [σ] →
        ClosedTerm (ParamConst Const ([] : Ctx Base)) σ
  rootExWitness_notProvable :
    ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
      ¬ ExtDerivation Const Δ φ →
        ¬ ClosedTheorySet.Provable
            (Const := Const)
            (fun ψ =>
              ψ ∈ Δ ∨
                ψ ∈ RootExWitnessAxioms
                  (Base := Base) (Const := Const) choose)
            φ

/-- The corrected source-side bridge automatically induces the older lifted
root-saturation bridge. -/
def RootExWitnessBridge.toRootSaturationBridge
    (B : RootExWitnessBridge Base Const) :
    RootSaturationBridge Base Const where
  choose := B.choose
  lifted_augmented_notProvable := by
    intro Δ φ hNot
    exact not_provable_liftParam_augmented_of_not_provable_rootExWitness
      (Base := Base)
      (Const := Const)
      B.choose
      (B.rootExWitness_notProvable hNot)

/-- Build a root world from a non-provable sequent.

Given `¬ ExtDerivation Const Δ φ`, constructs a `PrimeTheory` at context `[]`
where every hypothesis in `Δ` is present (lifted) and `φ` is absent (lifted). -/
theorem exists_root_world
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const}
    (hNotProv : ¬ ExtDerivation Const Δ φ) :
    ∃ W : PrimeTheory Const ([] : Ctx Base),
      (∀ ψ, ψ ∈ Δ → liftParamFormula [] ψ ∈ W.carrier) ∧
      liftParamFormula [] φ ∉ W.carrier := by
  have hNotProvLifted := not_provable_liftParam_of_not_provable hNotProv
  -- The lifted hypotheses theory
  let T : ClosedTheorySet (ParamConst Const ([] : Ctx Base)) :=
    fun ψ => ψ ∈ (Δ.map (liftParamFormula []))
  -- T doesn't prove liftParamFormula [] φ
  have hNotProvT : ¬ ClosedTheorySet.Provable T (liftParamFormula [] φ) :=
    hNotProvLifted
  -- Apply Lindenbaum prime extension
  rcases ClosedTheorySet.exists_prime_extension_separating hNotProvT with
    ⟨U, hExt, hClosed, hCons, hPrime, hOmit⟩
  exact ⟨⟨U, hClosed, hCons, hPrime⟩,
    fun ψ hψ => hExt (show liftParamFormula [] ψ ∈ Δ.map (liftParamFormula []) from
      List.mem_map.mpr ⟨ψ, hψ, rfl⟩),
    hOmit⟩

/-- Root-world saturated packaging from an explicit augmented non-provability
assumption at context `[]`. -/
theorem exists_root_world_saturated_of_notProvable_augmented
    (choose :
      {σ : Ty Base} →
        Formula (ParamConst Const ([] : Ctx Base)) [σ] →
          ClosedTerm (ParamConst Const ([] : Ctx Base)) σ)
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const}
    (hNotAug :
      ¬ ClosedTheorySet.Provable
          (fun ψ =>
            ψ ∈ (Δ.map (liftParamFormula [])) ∨
              ψ ∈ PrimeTheory.ExWitnessAxioms
                (Base := Base) (Const := Const) (Γ := ([] : Ctx Base)) choose)
          (liftParamFormula [] φ)) :
    ∃ W : PrimeTheory.Saturated Const ([] : Ctx Base),
      (∀ ψ, ψ ∈ Δ → liftParamFormula [] ψ ∈ W.carrier) ∧
      liftParamFormula [] φ ∉ W.carrier := by
  rcases PrimeTheory.exists_saturated_world_separating_of_notProvable
      (Base := Base) (Const := Const) (Γ := ([] : Ctx Base))
      (choose := choose)
      (T := fun ψ => ψ ∈ (Δ.map (liftParamFormula [])))
      (χ := liftParamFormula [] φ)
      hNotAug with ⟨W, hExt, hOmit⟩
  refine ⟨W, ?_, hOmit⟩
  intro ψ hψ
  exact hExt (List.mem_map.mpr ⟨ψ, hψ, rfl⟩)

/-- Corrected root packaging from source-side augmented non-provability:
the exact source boundary is ordinary assumptions plus the retracted witness
axioms induced by the chosen root witness policy. -/
theorem exists_root_world_saturated_of_rootExWitness_notProvable
    (choose :
      {σ : Ty Base} →
        Formula (ParamConst Const ([] : Ctx Base)) [σ] →
          ClosedTerm (ParamConst Const ([] : Ctx Base)) σ)
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const}
    (hNot :
      ¬ ClosedTheorySet.Provable
        (Const := Const)
        (fun ψ =>
          ψ ∈ Δ ∨
            ψ ∈ RootExWitnessAxioms (Base := Base) (Const := Const) choose)
        φ) :
    ∃ W : PrimeTheory.Saturated Const ([] : Ctx Base),
      (∀ ψ, ψ ∈ Δ → liftParamFormula [] ψ ∈ W.carrier) ∧
      liftParamFormula [] φ ∉ W.carrier := by
  exact exists_root_world_saturated_of_notProvable_augmented
    (Base := Base)
    (Const := Const)
    (choose := choose)
    (Δ := Δ)
    (φ := φ)
    (hNotAug :=
      not_provable_liftParam_augmented_of_not_provable_rootExWitness
        (Base := Base)
        (Const := Const)
        choose
        hNot)

/-- Consumer theorem for the corrected source-side witness bridge. -/
theorem exists_root_world_saturated_of_rootExWitness_bridge
    (B : RootExWitnessBridge Base Const)
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const}
    (hNotProv : ¬ ExtDerivation Const Δ φ) :
    ∃ W : PrimeTheory.Saturated Const ([] : Ctx Base),
      (∀ ψ, ψ ∈ Δ → liftParamFormula [] ψ ∈ W.carrier) ∧
      liftParamFormula [] φ ∉ W.carrier := by
  exact exists_root_world_saturated_of_rootExWitness_notProvable
    (Base := Base)
    (Const := Const)
    (choose := B.choose)
    (Δ := Δ)
    (φ := φ)
    (hNot := B.rootExWitness_notProvable hNotProv)

/-- Root-world saturated packaging from a lifted augmented non-provability
bridge over ordinary non-provability. -/
theorem exists_root_world_saturated_of_lifted_augmented_notProvable
    (choose :
      {σ : Ty Base} →
        Formula (ParamConst Const ([] : Ctx Base)) [σ] →
          ClosedTerm (ParamConst Const ([] : Ctx Base)) σ)
    (hLiftNotProvableAugmented :
      ∀ {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const},
        ¬ ExtDerivation Const Δ φ →
          ¬ ClosedTheorySet.Provable
              (fun ψ =>
                ψ ∈ (Δ.map (liftParamFormula [])) ∨
                  ψ ∈ PrimeTheory.ExWitnessAxioms
                    (Base := Base) (Const := Const) (Γ := ([] : Ctx Base)) choose)
              (liftParamFormula [] φ))
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const}
    (hNotProv : ¬ ExtDerivation Const Δ φ) :
    ∃ W : PrimeTheory.Saturated Const ([] : Ctx Base),
      (∀ ψ, ψ ∈ Δ → liftParamFormula [] ψ ∈ W.carrier) ∧
      liftParamFormula [] φ ∉ W.carrier := by
  exact exists_root_world_saturated_of_notProvable_augmented
    (Base := Base)
    (Const := Const)
    (choose := choose)
    (Δ := Δ)
    (φ := φ)
    (hNotAug := hLiftNotProvableAugmented hNotProv)

/-- Consumer theorem: a root-level saturation bridge yields a saturated root
world for every non-provable original sequent. -/
theorem exists_root_world_saturated_of_bridge
    (B : RootSaturationBridge Base Const)
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const}
    (hNotProv : ¬ ExtDerivation Const Δ φ) :
    ∃ W : PrimeTheory.Saturated Const ([] : Ctx Base),
      (∀ ψ, ψ ∈ Δ → liftParamFormula [] ψ ∈ W.carrier) ∧
      liftParamFormula [] φ ∉ W.carrier := by
  exact exists_root_world_saturated_of_lifted_augmented_notProvable
    (Base := Base)
    (Const := Const)
    (choose := B.choose)
    (hLiftNotProvableAugmented := B.lifted_augmented_notProvable)
    (Δ := Δ)
    (φ := φ)
    hNotProv

/-- Conditional saturated packaging of `exists_root_world`.

If one can saturate any prime theory while preserving omission of a designated
formula, then the root-world construction can be lifted to a saturated root
world at context `[]`. -/
theorem exists_root_world_saturated_of
    (hSaturate :
      ∀ {Γ : Ctx Base} {χ : ClosedFormula (ParamConst Const Γ)},
        (W : PrimeTheory Const Γ) →
        χ ∉ W.carrier →
        ∃ Ws : PrimeTheory.Saturated Const Γ,
          (∀ {ψ : ClosedFormula (ParamConst Const Γ)},
            ψ ∈ W.carrier → ψ ∈ Ws.carrier) ∧
          χ ∉ Ws.carrier)
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const}
    (hNotProv : ¬ ExtDerivation Const Δ φ) :
    ∃ W : PrimeTheory.Saturated Const ([] : Ctx Base),
      (∀ ψ, ψ ∈ Δ → liftParamFormula [] ψ ∈ W.carrier) ∧
      liftParamFormula [] φ ∉ W.carrier := by
  rcases exists_root_world (Const := Const) (Δ := Δ) (φ := φ) hNotProv with
    ⟨W0, hΔ, hOmit⟩
  rcases hSaturate (Γ := ([] : Ctx Base))
      (χ := liftParamFormula [] φ) W0 hOmit with
    ⟨Ws, hMono, hOmitS⟩
  refine ⟨Ws, ?_, hOmitS⟩
  intro ψ hψ
  exact hMono (hΔ ψ hψ)

/-- Consumer theorem: an arbitrary-context saturation bridge already yields a
saturated root world for every non-provable original sequent. -/
theorem exists_root_world_saturated_of_saturationBridge
    (B : PrimeTheory.SaturationBridge Base Const)
    {Δ : List (ClosedFormula Const)} {φ : ClosedFormula Const}
    (hNotProv : ¬ ExtDerivation Const Δ φ) :
    ∃ W : PrimeTheory.Saturated Const ([] : Ctx Base),
      (∀ ψ, ψ ∈ Δ → liftParamFormula [] ψ ∈ W.carrier) ∧
      liftParamFormula [] φ ∉ W.carrier := by
  exact exists_root_world_saturated_of
    (Base := Base)
    (Const := Const)
    (hSaturate := fun W hOmit =>
      PrimeTheory.SaturationBridge.saturate
        (Base := Base)
        (Const := Const)
        B
        (W := W)
        hOmit)
    (Δ := Δ)
    (φ := φ)
    hNotProv

end RootWorld

end Mettapedia.Logic.HOL
