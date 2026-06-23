import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Completeness
import Mettapedia.Logic.HOL.CanonicalTheory
import Mettapedia.Logic.HOL.DerivationExtensionality
import Mettapedia.Logic.HOL.PrimeHenkinExtension

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

open Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

namespace Derivable

/-- Closed native sequent derivations feed directly into the extensional
closed-theory provability layer used by the canonical HOL infrastructure. -/
theorem toClosedTheoryProvable
    {Δ : ClosedTheory Const} {phi : ClosedFormula Const} :
    Derivable (Base := Base) (Const := Const) Δ phi ->
      ClosedTheory.Provable (Const := Const) Δ phi :=
  toExtDerivation

/-- Any native closed derivation from a finite closed context induces finite
provability in an ambient canonical theory-set containing that context. -/
theorem toClosedTheorySetProvable
    {T : ClosedTheorySet Const}
    {Δ : ClosedTheory Const} {phi : ClosedFormula Const}
    (hΔ : ∀ psi, psi ∈ Δ -> psi ∈ T) :
    Derivable (Base := Base) (Const := Const) Δ phi ->
      ClosedTheorySet.Provable (Const := Const) T phi := by
  intro h
  exact ClosedTheorySet.provable_of_closedTheory
    (Const := Const) (T := T) (Δ := Δ)
    (fun {psi} hpsi => hΔ psi hpsi)
    h.toClosedTheoryProvable

/-- Theoremhood in the native archive-free calculus yields canonical
closed-theory provability in every ambient world. -/
theorem theorem_toClosedTheorySetProvable
    {T : ClosedTheorySet Const} {phi : ClosedFormula Const} :
    Derivable.Theorem (Base := Base) (Const := Const) phi ->
      ClosedTheorySet.Provable (Const := Const) T phi := by
  intro h
  exact toClosedTheorySetProvable
    (T := T) (Δ := []) (phi := phi)
    (by
      intro psi hpsi
      cases hpsi)
    h

/-- A canonical world containing all closed antecedents of a native derivation
also contains its succedent. -/
theorem mem_world_of_derivable
    {W : ClosedTheorySet.World Const}
    {Δ : ClosedTheory Const} {phi : ClosedFormula Const}
    (hΔ : ∀ psi, psi ∈ Δ -> psi ∈ W.carrier)
    (h : Derivable (Base := Base) (Const := Const) Δ phi) :
    phi ∈ W.carrier :=
  W.mem_of_provable <|
    h.toClosedTheorySetProvable (T := W.carrier) hΔ

end Derivable

namespace ClosedTheory.Provable

/-- Fresh-constant generalization for finite closed derivations. If a closed
instance `φ[c]` is derivable from hypotheses that do not mention `c`, and the
body `φ` itself does not mention `c`, then the universal formula `∀ φ` is
already derivable from the original hypotheses. This is the finite derivation
core needed for the future archive-free universal counterexample argument. -/
theorem all_of_const_instance
    {Δ : ClosedTheory Const}
    {σ : Ty Base}
    {φ : Formula Const [σ]}
    {c : Const σ}
    (hΔno : ∀ {ψ : ClosedFormula Const}, ψ ∈ Δ -> NoConstOccurrence c ψ)
    (hφno : NoConstOccurrence c φ)
    (hInst : ClosedTheory.Provable (Const := Const) Δ
      (instantiate (Base := Base) (.const c) φ)) :
    ClosedTheory.Provable (Const := Const) Δ (.all φ) := by
  have hHypsAux :
      ∀ {Δ : ClosedTheory Const},
        (∀ {ψ : ClosedFormula Const}, ψ ∈ Δ -> NoConstOccurrence c ψ) ->
          Δ.map (fun ψ =>
            abstractConstAt (Base := Base) (Γ := []) (τ := .prop) c [] ψ) =
            weakenHyps (Base := Base) (Const := Const) (σ := σ) Δ := by
    intro Δ hΔno
    induction Δ with
    | nil =>
        simp [weakenHyps]
    | cons ψ Δ ih =>
        simp [weakenHyps]
        refine And.intro ?_ ?_
        simpa [insertRen, weaken] using
          (abstractConstAt_noOccurrence (Base := Base) (Γ := []) (c := c) [] ψ
            (hΔno (by simp)))
        simpa [weakenHyps] using ih (by
          intro χ hχ
          exact hΔno (by simp [hχ]))
  have hHyps :
      Δ.map (fun ψ =>
        abstractConstAt (Base := Base) (Γ := []) (τ := .prop) c [] ψ) =
        weakenHyps (Base := Base) (Const := Const) (σ := σ) Δ :=
    hHypsAux hΔno
  have hConc :
      abstractConstAt (Base := Base) (Γ := []) (τ := .prop) c []
        (instantiate (Base := Base) (.const c) φ) = φ := by
    have hInsertCancel :
        ∀ {τ : Ty Base} (t : Term Const [σ] τ),
          instantiate (Base := Base) (.var (.vz : Var [σ] σ))
            (rename
              (fun {τ : Ty Base} (v : Var [σ] τ) =>
                insertRen (Base := Base) (Γ := []) (σ := σ) [σ] v) t) = t := by
      intro τ t
      unfold instantiate
      calc
        subst
            (Subst.single (Base := Base) (Const := Const)
              (.var (.vz : Var [σ] σ)))
            (rename
              (fun {τ : Ty Base} (v : Var [σ] τ) =>
                insertRen (Base := Base) (Γ := []) (σ := σ) [σ] v) t)
            =
          subst
            (fun {τ : Ty Base} (v : Var [σ] τ) =>
              (Subst.single (Base := Base) (Const := Const)
                (.var (.vz : Var [σ] σ)))
                (insertRen (Base := Base) (Γ := []) (σ := σ) [σ] v)) t := by
              simpa using
                (subst_rename (Base := Base) (Const := Const)
                  (σs := Subst.single (Base := Base) (Const := Const)
                    (.var (.vz : Var [σ] σ)))
                  (ρ := fun {τ : Ty Base} (v : Var [σ] τ) =>
                    insertRen (Base := Base) (Γ := []) (σ := σ) [σ] v)
                  t)
        _ = subst (Subst.id (Base := Base) (Const := Const) (Γ := [σ])) t := by
              apply subst_ext
              intro τ v
              cases v <;> rfl
        _ = t := subst_id (Base := Base) (Const := Const) t
    have hConstSelf :
        abstractConstAt (Base := Base) (Γ := []) c [] (.const c) =
          (.var (.vz : Var [σ] σ)) := by
      simp only [abstractConstAt, varAtDepth]
      split
      · rfl
      · contradiction
    calc
      abstractConstAt (Base := Base) (Γ := []) (τ := .prop) c []
          (instantiate (Base := Base) (.const c) φ)
          =
            instantiate (Base := Base)
              (abstractConstAt (Base := Base) (Γ := []) c [] (.const c))
              (abstractConstAt (Base := Base) (Γ := []) c [σ] φ) := by
              exact
                (abstractConstAt_instantiate (Base := Base) (Γ := []) (c := c) []
                  (.const c) φ)
      _ = instantiate (Base := Base) (.var (.vz : Var [σ] σ))
            (rename
              (fun {τ : Ty Base} (v : Var [σ] τ) =>
                insertRen (Base := Base) (Γ := []) (σ := σ) [σ] v) φ) := by
            rw [hConstSelf]
            rw [abstractConstAt_noOccurrence
              (Base := Base) (Γ := []) (c := c) [σ] φ hφno]
            rfl
      _ = φ := hInsertCancel φ
  have hAbs :=
    ExtDerivation.abstractConstAt_deriv (Base := Base) (Γ := []) (Ξ := []) c hInst
  have hWeaken :
      ExtDerivation Const
        (weakenHyps (Base := Base) (Const := Const) (σ := σ) Δ) φ := by
    exact hConc ▸ hHyps ▸ hAbs
  exact .allI hWeaken

end ClosedTheory.Provable

namespace ClosedTheorySet

/-- If a finite closed derivation of a witness instance is supported inside a
deductively closed theory-set, then the corresponding existential formula also
belongs to that theory-set. This is the direct existential companion to the
fresh-constant universal generalization lemma. -/
theorem mem_ex_of_const_instance
    {U : ClosedTheorySet Const}
    (hclosed : ClosedTheorySet.DeductivelyClosed (Const := Const) U)
    {Γ : ClosedTheory Const}
    {σ : Ty Base}
    {φ : Formula Const [σ]}
    {c : Const σ}
    (hΓ : ∀ {ψ : ClosedFormula Const}, ψ ∈ Γ -> ψ ∈ U)
    (hInst : ClosedTheory.Provable (Const := Const) Γ
      (instantiate (Base := Base) (.const c) φ)) :
    (.ex φ : ClosedFormula Const) ∈ U := by
  apply hclosed
  exact ClosedTheorySet.provable_of_closedTheory
    (Const := Const) (T := U) (Δ := Γ)
    hΓ
    (.exI (.const c) hInst)

/-- If a fresh-constant instance is derivable from finitely many formulas
already contained in a deductively closed theory-set, and the fresh constant
occurs nowhere in those hypotheses or the quantified body, then the universal
formula itself belongs to the theory-set. -/
theorem mem_all_of_const_instance
    {U : ClosedTheorySet Const}
    (hclosed : ClosedTheorySet.DeductivelyClosed (Const := Const) U)
    {Γ : ClosedTheory Const}
    {σ : Ty Base}
    {φ : Formula Const [σ]}
    {c : Const σ}
    (hΓ : ∀ {ψ : ClosedFormula Const}, ψ ∈ Γ -> ψ ∈ U)
    (hΓno : ∀ {ψ : ClosedFormula Const}, ψ ∈ Γ -> NoConstOccurrence c ψ)
    (hφno : NoConstOccurrence c φ)
    (hInst : ClosedTheory.Provable (Const := Const) Γ
      (instantiate (Base := Base) (.const c) φ)) :
    (.all φ : ClosedFormula Const) ∈ U := by
  apply hclosed
  exact ClosedTheorySet.provable_of_closedTheory
    (Const := Const) (T := U) (Δ := Γ)
    hΓ
    (ClosedTheory.Provable.all_of_const_instance
      (Base := Base) (Const := Const)
      hΓno hφno hInst)

end ClosedTheorySet

namespace CompletenessFrontier

/-- Closed-theory-set view of the antecedents of a closed native frontier. -/
abbrev antecedentTheorySet (F : CompletenessFrontier Const []) : ClosedTheorySet Const :=
  fun φ => φ ∈ F.antecedents

/-- A prime deductively closed consistent closed-theory-set extending the
antecedents of a closed frontier while omitting its succedent. This packages the
prime-separation shape that the canonical completeness route wants before the
full quantifier witness obligations of `ClosedTheorySet.World` are added. -/
structure PrimeSeparatingExtension (F : CompletenessFrontier Const [])
    (U : ClosedTheorySet Const) : Prop where
  contains_antecedents : ∀ {φ : ClosedFormula Const}, φ ∈ F.antecedents → φ ∈ U
  closed : ClosedTheorySet.DeductivelyClosed (Const := Const) U
  consistent : ClosedTheorySet.Consistent (Const := Const) U
  prime_or :
    ∀ {φ ψ : ClosedFormula Const}, (.or φ ψ : ClosedFormula Const) ∈ U → φ ∈ U ∨ ψ ∈ U
  omits_succedent : F.succedent ∉ U

namespace PrimeSeparatingExtension

theorem mem_of_setProvable
    {F : CompletenessFrontier Const []}
    {U : ClosedTheorySet Const}
    (hFU : PrimeSeparatingExtension (Const := Const) F U)
    {φ : ClosedFormula Const} :
    ClosedTheorySet.Provable (Const := Const) F.antecedentTheorySet φ → φ ∈ U := by
  intro hφ
  exact hFU.closed <|
    ClosedTheorySet.provable_mono
      (Const := Const)
      (T := F.antecedentTheorySet)
      (U := U)
      (hTU := by
        intro ψ hψ
        exact hFU.contains_antecedents hψ)
      hφ

theorem not_setProvable_succedent
    {F : CompletenessFrontier Const []}
    {U : ClosedTheorySet Const}
    (hFU : PrimeSeparatingExtension (Const := Const) F U) :
    ¬ ClosedTheorySet.Provable (Const := Const) F.antecedentTheorySet F.succedent := by
  intro hProv
  exact hFU.omits_succedent (hFU.mem_of_setProvable hProv)

/-- Once the quantifier witness fields are supplied separately, a prime
separating extension upgrades directly to a canonical closed-theory world. This
isolates the remaining archive-free completeness obligation to the two Henkin
witness properties rather than the whole world package. -/
def toWorld
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
    ClosedTheorySet.World Const where
  carrier := U
  closed := hFU.closed
  consistent := hFU.consistent
  prime_or := hFU.prime_or
  exists_witness := hExistsWitness
  all_counterexample := hAllCounterexample

end PrimeSeparatingExtension

/-- Extensional non-provability version of a closed canonical world
counterexample. This is the exact input consumed by the trusted
prime-extension layer. -/
theorem not_closedTheorySetProvable_of_world_counterexample
    {F : CompletenessFrontier Const []}
    {W : ClosedTheorySet.World Const}
    (hAnte : ∀ phi, phi ∈ F.antecedents -> phi ∈ W.carrier)
    (hSucc : F.succedent ∉ W.carrier) :
    ¬ ClosedTheorySet.Provable (Const := Const) F.antecedentTheorySet F.succedent := by
  intro hProv
  have hProvW : ClosedTheorySet.Provable (Const := Const) W.carrier F.succedent :=
    ClosedTheorySet.provable_mono
      (Const := Const)
      (T := F.antecedentTheorySet)
      (U := W.carrier)
      (hTU := by
        intro φ hφ
        exact hAnte φ hφ)
      hProv
  exact hSucc (W.mem_of_provable hProvW)

/-- Extensional non-provability of the closed succedent from the closed
antecedent theory-set already rules out the three immediate contradictions that
would be injected by adjoining `T ⊤` and `F ⊥` to the initial search state. -/
theorem closedNonconflicting_of_not_closedTheorySetProvable
    {F : CompletenessFrontier Const []}
    (hNot : ¬ ClosedTheorySet.Provable (Const := Const) F.antecedentTheorySet F.succedent) :
    F.ClosedNonconflicting := by
  refine ⟨?_, ?_, ?_⟩
  · intro hBot
    apply hNot
    exact ClosedTheorySet.provable_mp
      (T := F.antecedentTheorySet)
      (φ := (.bot : ClosedFormula Const))
      (ψ := F.succedent)
      (ClosedTheorySet.provable_of_closedTheory
        (Const := Const)
        (T := F.antecedentTheorySet)
        (Δ := [])
        (hΔ := by
          intro ξ hξ
          cases hξ)
        (hφ := ClosedTheory.Provable.bot_imp
          (Δ := []) (Const := Const) (φ := F.succedent)))
      (ClosedTheorySet.provable_of_mem (Const := Const) hBot)
  · intro hTop
    apply hNot
    simpa [hTop] using
      (ClosedTheorySet.provable_top (Const := Const) F.antecedentTheorySet)
  · intro hSuccMem
    apply hNot
    exact ClosedTheorySet.provable_of_mem (Const := Const) hSuccMem

/-- The prime-extension layer produces a paper-facing separating closed theory
set for any closed frontier whose succedent is not set-provable from its
antecedents in the extensional HOL layer. -/
theorem exists_primeSeparatingExtension_of_not_closedTheorySetProvable
    {F : CompletenessFrontier Const []}
    (hNot : ¬ ClosedTheorySet.Provable (Const := Const) F.antecedentTheorySet F.succedent) :
    ∃ U : ClosedTheorySet Const, PrimeSeparatingExtension (Const := Const) F U := by
  rcases ClosedTheorySet.exists_prime_extension_separating
      (Const := Const) (T := F.antecedentTheorySet) (φ := F.succedent) hNot with
    ⟨U, hExt, hClosed, hCons, hPrime, hOmit⟩
  exact ⟨U, ⟨by
      intro φ hφ
      exact hExt hφ,
    hClosed, hCons, hPrime, hOmit⟩⟩

/-- Any closed canonical world counterexample yields a prime separating closed
theory-set extension of the frontier antecedents. This is a direct bridge from
the current world witness route to the trusted prime-extension layer. -/
theorem exists_primeSeparatingExtension_of_world_counterexample
    {F : CompletenessFrontier Const []}
    {W : ClosedTheorySet.World Const}
    (hAnte : ∀ phi, phi ∈ F.antecedents -> phi ∈ W.carrier)
    (hSucc : F.succedent ∉ W.carrier) :
    ∃ U : ClosedTheorySet Const, PrimeSeparatingExtension (Const := Const) F U :=
  exists_primeSeparatingExtension_of_not_closedTheorySetProvable
    (F := F)
    (not_closedTheorySetProvable_of_world_counterexample
      (F := F) (W := W) hAnte hSucc)

/-- Any prime separating extension already certifies that the original closed
frontier avoids the initial closed-hull conflicts. -/
theorem closedNonconflicting_of_primeSeparatingExtension
    {F : CompletenessFrontier Const []}
    {U : ClosedTheorySet Const}
    (hFU : PrimeSeparatingExtension (Const := Const) F U) :
    F.ClosedNonconflicting :=
  closedNonconflicting_of_not_closedTheorySetProvable
    (F := F) hFU.not_setProvable_succedent

/-- A canonical-world counterexample to a closed frontier excludes the three
immediate initial contradictions tracked by `ClosedNonconflicting`. -/
theorem closedNonconflicting_of_world_counterexample
    {F : CompletenessFrontier Const []}
    {W : ClosedTheorySet.World Const}
    (hAnte : ∀ phi, phi ∈ F.antecedents -> phi ∈ W.carrier)
    (hSucc : F.succedent ∉ W.carrier) :
    F.ClosedNonconflicting :=
  closedNonconflicting_of_not_closedTheorySetProvable
    (F := F)
    (not_closedTheorySetProvable_of_world_counterexample
      (F := F) (W := W) hAnte hSucc)

/-- A canonical-world counterexample to the succedent of a closed frontier
already refutes native derivability of that frontier. -/
theorem not_derivable_of_world_counterexample
    {F : CompletenessFrontier Const []}
    {W : ClosedTheorySet.World Const}
    (hAnte : ∀ phi, phi ∈ F.antecedents -> phi ∈ W.carrier)
    (hSucc : F.succedent ∉ W.carrier) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  intro hDer
  exact hSucc <| Derivable.mem_world_of_derivable (W := W) hAnte hDer

end CompletenessFrontier

namespace SaturationSearchState.HeadPrioritySearchDerivation

/-- A closed canonical-world counterexample keeps every compatible head-priority
search derivation noncontradictory at the closed Hintikka hull. -/
theorem closed_noncontradictory_of_world_counterexample
    {F : CompletenessFrontier Const []}
    {S : SaturationSearchState Const []}
    (D : HeadPrioritySearchDerivation F S)
    {W : ClosedTheorySet.World Const}
    (hAnte : ∀ phi, phi ∈ F.antecedents -> phi ∈ W.carrier)
    (hSucc : F.succedent ∉ W.carrier)
    (hCompat : D.Compatible) :
    S.hintikka.close.Noncontradictory :=
  D.closed_noncontradictory_of_closedNonconflicting
    (CompletenessFrontier.closedNonconflicting_of_world_counterexample
      (F := F) (W := W) hAnte hSucc)
    hCompat

end SaturationSearchState.HeadPrioritySearchDerivation

namespace SaturationSearchState.HeadPriorityCompletion

/-- A closed canonical-world counterexample keeps the closed hull of a
compatible head-priority completion noncontradictory. -/
theorem closed_noncontradictory_of_world_counterexample
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    {W : ClosedTheorySet.World Const}
    (hAnte : ∀ phi, phi ∈ F.antecedents -> phi ∈ W.carrier)
    (hSucc : F.succedent ∉ W.carrier)
    (hCompat : C.derivation.Compatible) :
    C.state.hintikka.close.Noncontradictory :=
  C.closed_noncontradictory_of_closedNonconflicting
    (CompletenessFrontier.closedNonconflicting_of_world_counterexample
      (F := F) (W := W) hAnte hSucc)
    hCompat

/-- A closed compatible head-priority completion can be certified directly from
extensional non-provability of its succedent from its antecedent theory-set. -/
def toCertifiedOfNotClosedTheorySetProvable
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
          F.antecedentTheorySet F.succedent) :
    CertifiedHeadPriorityCompletion Const [] F :=
  C.toCertified
    (Const := Const)
    (Γ := [])
    (CompletenessFrontier.closedNonconflicting_of_not_closedTheorySetProvable
      (F := F) hNot)
    hCompat

/-- Prime separating extensions likewise certify closed compatible terminal
head-priority completions. -/
def toCertifiedOfPrimeSeparatingExtension
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) F U) :
    CertifiedHeadPriorityCompletion Const [] F :=
  C.toCertified
    (Const := Const)
    (Γ := [])
    (CompletenessFrontier.closedNonconflicting_of_primeSeparatingExtension
      (F := F) hFU)
    hCompat

/-- Closed extensional non-provability now feeds directly into the paper-facing
closed Hintikka certificate endpoint for compatible terminal completions. -/
def toClosedLocalHintikkaCertificateOfNotClosedTheorySetProvable
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
          F.antecedentTheorySet F.succedent) :
    LocalHintikkaCertificate F :=
  (C.toCertifiedOfNotClosedTheorySetProvable hCompat hNot).toClosedLocalHintikkaCertificate

/-- Prime separating extensions likewise feed directly into the paper-facing
closed Hintikka certificate endpoint for compatible terminal completions. -/
def toClosedLocalHintikkaCertificateOfPrimeSeparatingExtension
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) F U) :
    LocalHintikkaCertificate F :=
  (C.toCertifiedOfPrimeSeparatingExtension hCompat hFU).toClosedLocalHintikkaCertificate

/-- The existing closed semantic countermodel route can now be driven directly
from extensional non-provability, without separately threading
`ClosedNonconflicting`. -/
theorem exists_closedLocalAgreementWitness_of_exists_semantics_of_not_closedTheorySetProvable
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
          F.antecedentTheorySet F.succedent)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M []),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const []},
            (Sign.trueE, φ) ∈ C.state.hintikka.close.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const []},
            (Sign.falseE, φ) ∈ C.state.hintikka.close.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ∃ (M : SemilocalModel.{u, v, w, w'} Base Const)
      (W : LocalAgreementWitness M F),
      W.certificate =
        (C.toCertifiedOfNotClosedTheorySetProvable hCompat hNot).toClosedLocalHintikkaCertificate ∧
      SemilocalModel.SupportsUniformRelativization M := by
  rcases hSem with ⟨M, env, global, true_top, false_ne_top, hM⟩
  refine ⟨M,
    (C.toCertifiedOfNotClosedTheorySetProvable hCompat hNot).toClosedLocalAgreementWitness
      (M := M) env global ?_ ?_,
    ?_, hM⟩
  · intro φ hφ
    exact true_top <| by
      simpa [SaturationSearchState.HeadPriorityCompletion.toCertifiedOfNotClosedTheorySetProvable,
        SaturationSearchState.HeadPriorityCompletion.toCertified,
        CertifiedHeadPriorityCompletion.state,
        CertifiedHeadPriorityCompletion.hintikka,
        CertifiedHeadPriorityCompletion.closedHintikka] using hφ
  · intro φ hφ
    exact false_ne_top <| by
      simpa [SaturationSearchState.HeadPriorityCompletion.toCertifiedOfNotClosedTheorySetProvable,
        SaturationSearchState.HeadPriorityCompletion.toCertified,
        CertifiedHeadPriorityCompletion.state,
        CertifiedHeadPriorityCompletion.hintikka,
        CertifiedHeadPriorityCompletion.closedHintikka] using hφ
  · rfl

theorem exists_candidateClosedHintikkaSemantics_of_exists_closedLocalAgreementWitness_of_not_closedTheorySetProvable
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
          F.antecedentTheorySet F.succedent)
    (hW :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const)
        (W : LocalAgreementWitness M F),
        W.certificate =
          (C.toCertifiedOfNotClosedTheorySetProvable hCompat hNot).toClosedLocalHintikkaCertificate ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M []),
      SemilocalModel.IsGlobalEnv M env ∧
      Nonempty
        (CertifiedHeadPriorityCompletion.CandidateClosedHintikkaSemantics
          (C.toCertifiedOfNotClosedTheorySetProvable hCompat hNot) env) ∧
      SemilocalModel.SupportsUniformRelativization M := by
  rcases hW with ⟨M, W, hCert, hM⟩
  refine ⟨M, W.env, W.global, ?_, hM⟩
  exact ⟨CertifiedHeadPriorityCompletion.toCandidateClosedHintikkaSemanticsOfClosedLocalAgreementWitness
    (C := C.toCertifiedOfNotClosedTheorySetProvable hCompat hNot)
    (M := M) W hCert⟩

theorem exists_candidateClosedHintikkaSemantics_of_exists_semantics_of_not_closedTheorySetProvable
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
          F.antecedentTheorySet F.succedent)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M []),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const []},
            (Sign.trueE, φ) ∈ C.state.hintikka.close.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const []},
            (Sign.falseE, φ) ∈ C.state.hintikka.close.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M []),
      SemilocalModel.IsGlobalEnv M env ∧
      Nonempty
        (CertifiedHeadPriorityCompletion.CandidateClosedHintikkaSemantics
          (C.toCertifiedOfNotClosedTheorySetProvable hCompat hNot) env) ∧
      SemilocalModel.SupportsUniformRelativization M := by
  exact
    exists_candidateClosedHintikkaSemantics_of_exists_closedLocalAgreementWitness_of_not_closedTheorySetProvable
      (C := C) (hCompat := hCompat) (hNot := hNot)
      (exists_closedLocalAgreementWitness_of_exists_semantics_of_not_closedTheorySetProvable
        (C := C) (hCompat := hCompat) (hNot := hNot) hSem)

theorem not_derivable_of_exists_semantics_of_not_closedTheorySetProvable
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
          F.antecedentTheorySet F.succedent)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M []),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const []},
            (Sign.trueE, φ) ∈ C.state.hintikka.close.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const []},
            (Sign.falseE, φ) ∈ C.state.hintikka.close.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  exact CertifiedHeadPriorityCompletion.not_derivable_of_exists_candidateClosedHintikkaSemantics
    (C := C.toCertifiedOfNotClosedTheorySetProvable hCompat hNot)
    (exists_candidateClosedHintikkaSemantics_of_exists_semantics_of_not_closedTheorySetProvable
      (C := C) (hCompat := hCompat) (hNot := hNot) hSem)

/-- The same closed semantic endpoint can be driven directly from a prime
separating extension. -/
theorem exists_closedLocalAgreementWitness_of_exists_semantics_of_primeSeparatingExtension
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) F U)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M []),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const []},
            (Sign.trueE, φ) ∈ C.state.hintikka.close.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const []},
            (Sign.falseE, φ) ∈ C.state.hintikka.close.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ∃ (M : SemilocalModel.{u, v, w, w'} Base Const)
      (W : LocalAgreementWitness M F),
      W.certificate =
        (C.toCertifiedOfPrimeSeparatingExtension hCompat hFU).toClosedLocalHintikkaCertificate ∧
      SemilocalModel.SupportsUniformRelativization M := by
  rcases hSem with ⟨M, env, global, true_top, false_ne_top, hM⟩
  refine ⟨M,
    (C.toCertifiedOfPrimeSeparatingExtension hCompat hFU).toClosedLocalAgreementWitness
      (M := M) env global ?_ ?_,
    ?_, hM⟩
  · intro φ hφ
    exact true_top <| by
      simpa [SaturationSearchState.HeadPriorityCompletion.toCertifiedOfPrimeSeparatingExtension,
        SaturationSearchState.HeadPriorityCompletion.toCertified,
        CertifiedHeadPriorityCompletion.state,
        CertifiedHeadPriorityCompletion.hintikka,
        CertifiedHeadPriorityCompletion.closedHintikka] using hφ
  · intro φ hφ
    exact false_ne_top <| by
      simpa [SaturationSearchState.HeadPriorityCompletion.toCertifiedOfPrimeSeparatingExtension,
        SaturationSearchState.HeadPriorityCompletion.toCertified,
        CertifiedHeadPriorityCompletion.state,
        CertifiedHeadPriorityCompletion.hintikka,
        CertifiedHeadPriorityCompletion.closedHintikka] using hφ
  · rfl

theorem exists_candidateClosedHintikkaSemantics_of_exists_closedLocalAgreementWitness_of_primeSeparatingExtension
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) F U)
    (hW :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const)
        (W : LocalAgreementWitness M F),
        W.certificate =
          (C.toCertifiedOfPrimeSeparatingExtension hCompat hFU).toClosedLocalHintikkaCertificate ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M []),
      SemilocalModel.IsGlobalEnv M env ∧
      Nonempty
        (CertifiedHeadPriorityCompletion.CandidateClosedHintikkaSemantics
          (C.toCertifiedOfPrimeSeparatingExtension hCompat hFU) env) ∧
      SemilocalModel.SupportsUniformRelativization M := by
  rcases hW with ⟨M, W, hCert, hM⟩
  refine ⟨M, W.env, W.global, ?_, hM⟩
  exact ⟨CertifiedHeadPriorityCompletion.toCandidateClosedHintikkaSemanticsOfClosedLocalAgreementWitness
    (C := C.toCertifiedOfPrimeSeparatingExtension hCompat hFU)
    (M := M) W hCert⟩

theorem exists_candidateClosedHintikkaSemantics_of_exists_semantics_of_primeSeparatingExtension
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) F U)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M []),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const []},
            (Sign.trueE, φ) ∈ C.state.hintikka.close.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const []},
            (Sign.falseE, φ) ∈ C.state.hintikka.close.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M []),
      SemilocalModel.IsGlobalEnv M env ∧
      Nonempty
        (CertifiedHeadPriorityCompletion.CandidateClosedHintikkaSemantics
          (C.toCertifiedOfPrimeSeparatingExtension hCompat hFU) env) ∧
      SemilocalModel.SupportsUniformRelativization M := by
  exact
    exists_candidateClosedHintikkaSemantics_of_exists_closedLocalAgreementWitness_of_primeSeparatingExtension
      (C := C) (hCompat := hCompat) (hFU := hFU)
      (exists_closedLocalAgreementWitness_of_exists_semantics_of_primeSeparatingExtension
        (C := C) (hCompat := hCompat) (hFU := hFU) hSem)

theorem not_derivable_of_exists_semantics_of_primeSeparatingExtension
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) F U)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M []),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const []},
            (Sign.trueE, φ) ∈ C.state.hintikka.close.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const []},
            (Sign.falseE, φ) ∈ C.state.hintikka.close.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  exact CertifiedHeadPriorityCompletion.not_derivable_of_exists_candidateClosedHintikkaSemantics
    (C := C.toCertifiedOfPrimeSeparatingExtension hCompat hFU)
    (exists_candidateClosedHintikkaSemantics_of_exists_semantics_of_primeSeparatingExtension
      (C := C) (hCompat := hCompat) (hFU := hFU) hSem)

/-- The same bridge can be driven by the packaged closed-Hintikka semantics
object rather than raw truth-assignment hypotheses. -/
theorem not_derivable_of_exists_candidateClosedHintikkaSemantics_of_not_closedTheorySetProvable
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
          F.antecedentTheorySet F.succedent)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M []),
        SemilocalModel.IsGlobalEnv M env ∧
        Nonempty
          (CertifiedHeadPriorityCompletion.CandidateClosedHintikkaSemantics
            (C.toCertifiedOfNotClosedTheorySetProvable hCompat hNot) env) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent :=
  CertifiedHeadPriorityCompletion.not_derivable_of_exists_candidateClosedHintikkaSemantics
    (C := C.toCertifiedOfNotClosedTheorySetProvable hCompat hNot) hSem

theorem not_derivable_of_exists_closedLocalAgreementWitness_of_not_closedTheorySetProvable
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
          F.antecedentTheorySet F.succedent)
    (hW :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const)
        (W : LocalAgreementWitness M F),
        W.certificate =
          (C.toCertifiedOfNotClosedTheorySetProvable hCompat hNot).toClosedLocalHintikkaCertificate ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  exact
    not_derivable_of_exists_candidateClosedHintikkaSemantics_of_not_closedTheorySetProvable
      (C := C) (hCompat := hCompat) (hNot := hNot)
      (exists_candidateClosedHintikkaSemantics_of_exists_closedLocalAgreementWitness_of_not_closedTheorySetProvable
        (C := C) (hCompat := hCompat) (hNot := hNot) hW)

/-- Prime separating extensions likewise feed directly into the packaged
closed-Hintikka semantics interface. -/
theorem not_derivable_of_exists_candidateClosedHintikkaSemantics_of_primeSeparatingExtension
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) F U)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M []),
        SemilocalModel.IsGlobalEnv M env ∧
        Nonempty
          (CertifiedHeadPriorityCompletion.CandidateClosedHintikkaSemantics
            (C.toCertifiedOfPrimeSeparatingExtension hCompat hFU) env) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent :=
  CertifiedHeadPriorityCompletion.not_derivable_of_exists_candidateClosedHintikkaSemantics
    (C := C.toCertifiedOfPrimeSeparatingExtension hCompat hFU) hSem

theorem not_derivable_of_exists_closedLocalAgreementWitness_of_primeSeparatingExtension
    {F : CompletenessFrontier Const []}
    (C : HeadPriorityCompletion F)
    (hCompat : C.derivation.Compatible)
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) F U)
    (hW :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const)
        (W : LocalAgreementWitness M F),
        W.certificate =
          (C.toCertifiedOfPrimeSeparatingExtension hCompat hFU).toClosedLocalHintikkaCertificate ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := Base) (Const := Const) F.antecedents F.succedent := by
  exact
    not_derivable_of_exists_candidateClosedHintikkaSemantics_of_primeSeparatingExtension
      (C := C) (hCompat := hCompat) (hFU := hFU)
      (exists_candidateClosedHintikkaSemantics_of_exists_closedLocalAgreementWitness_of_primeSeparatingExtension
        (C := C) (hCompat := hCompat) (hFU := hFU) hW)

end SaturationSearchState.HeadPriorityCompletion

namespace CertifiedHeadPriorityDerivation

/-- A closed certified derivation inherits closed-hull noncontradiction from any
canonical world extending its frontier antecedents while omitting the succedent. -/
theorem closedHintikka_noncontradictory_of_world_counterexample
    {F : CompletenessFrontier Const []}
    (D : CertifiedHeadPriorityDerivation Const [] F)
    {W : ClosedTheorySet.World Const}
    (hAnte : ∀ phi, phi ∈ F.antecedents -> phi ∈ W.carrier)
    (hSucc : F.succedent ∉ W.carrier) :
    D.closedHintikka.Noncontradictory :=
  D.derivation.closed_noncontradictory_of_world_counterexample hAnte hSucc D.compatible

end CertifiedHeadPriorityDerivation

namespace CountermodelCandidate

/-- A closed terminal search candidate becomes a local Hintikka certificate as
soon as a canonical world counterexample supplies closed-hull noncontradiction. -/
def toClosedLocalHintikkaCertificateOfWorldCounterexample
    (C : CountermodelCandidate Const [])
    {W : ClosedTheorySet.World Const}
    (hAnte : ∀ phi, phi ∈ C.frontier.antecedents -> phi ∈ W.carrier)
    (hSucc : C.frontier.succedent ∉ W.carrier)
    (hCompat : C.completion.derivation.Compatible) :
    LocalHintikkaCertificate C.frontier :=
  C.toClosedLocalHintikkaCertificate <|
    C.completion.closed_noncontradictory_of_world_counterexample hAnte hSucc hCompat

/-- Closed extensional non-provability is already enough to feed a compatible
terminal search candidate into the closed local Hintikka certificate layer. -/
def toClosedLocalHintikkaCertificateOfNotClosedTheorySetProvable
    (C : CountermodelCandidate Const [])
    (hCompat : C.completion.derivation.Compatible)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
          C.frontier.antecedentTheorySet C.frontier.succedent) :
    LocalHintikkaCertificate C.frontier :=
  C.toClosedLocalHintikkaCertificateOfClosedNonconflicting
    (CompletenessFrontier.closedNonconflicting_of_not_closedTheorySetProvable
      (F := C.frontier) hNot)
    hCompat

/-- A prime separating extension can therefore be consumed directly into the
closed local Hintikka certificate layer for any compatible terminal candidate. -/
def toClosedLocalHintikkaCertificateOfPrimeSeparatingExtension
    (C : CountermodelCandidate Const [])
    (hCompat : C.completion.derivation.Compatible)
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) C.frontier U) :
    LocalHintikkaCertificate C.frontier :=
  C.toClosedLocalHintikkaCertificateOfNotClosedTheorySetProvable
    hCompat hFU.not_setProvable_succedent

end CountermodelCandidate

namespace CertifiedCountermodelCandidate

/-- A closed certified countermodel candidate inherits closed-hull
noncontradiction from a canonical world counterexample. -/
theorem closedHintikka_noncontradictory_of_world_counterexample
    (C : CertifiedCountermodelCandidate Const [])
    {W : ClosedTheorySet.World Const}
    (hAnte : ∀ phi, phi ∈ C.frontier.antecedents -> phi ∈ W.carrier)
    (hSucc : C.frontier.succedent ∉ W.carrier) :
    C.closedHintikka.Noncontradictory :=
  C.candidate.completion.closed_noncontradictory_of_world_counterexample hAnte hSucc C.compatible

/-- Closed certified countermodel candidates can now consume canonical world
counterexamples directly into paper-facing Hintikka certificates. -/
def toClosedLocalHintikkaCertificateOfWorldCounterexample
    (C : CertifiedCountermodelCandidate Const [])
    {W : ClosedTheorySet.World Const}
    (hAnte : ∀ phi, phi ∈ C.frontier.antecedents -> phi ∈ W.carrier)
    (hSucc : C.frontier.succedent ∉ W.carrier) :
    LocalHintikkaCertificate C.frontier :=
  C.candidate.toClosedLocalHintikkaCertificateOfWorldCounterexample hAnte hSucc C.compatible

/-- Closed certified countermodel candidates can also consume extensional
closed-theory-set non-provability directly into paper-facing Hintikka
certificates. -/
def toClosedLocalHintikkaCertificateOfNotClosedTheorySetProvable
    (C : CertifiedCountermodelCandidate Const [])
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
          C.frontier.antecedentTheorySet C.frontier.succedent) :
    LocalHintikkaCertificate C.frontier :=
  C.candidate.toClosedLocalHintikkaCertificateOfNotClosedTheorySetProvable
    C.compatible hNot

/-- Prime separating extensions can therefore be consumed directly at the
certified candidate layer as well. -/
def toClosedLocalHintikkaCertificateOfPrimeSeparatingExtension
    (C : CertifiedCountermodelCandidate Const [])
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) C.frontier U) :
    LocalHintikkaCertificate C.frontier :=
  C.candidate.toClosedLocalHintikkaCertificateOfPrimeSeparatingExtension
    C.compatible hFU

@[simp] theorem toClosedLocalHintikkaCertificateOfNotClosedTheorySetProvable_eq
    (C : CertifiedCountermodelCandidate Const [])
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
          C.frontier.antecedentTheorySet C.frontier.succedent) :
    C.toClosedLocalHintikkaCertificateOfNotClosedTheorySetProvable hNot =
      C.toClosedLocalHintikkaCertificate := by
  cases C
  rfl

@[simp] theorem toClosedLocalHintikkaCertificateOfPrimeSeparatingExtension_eq
    (C : CertifiedCountermodelCandidate Const [])
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) C.frontier U) :
    C.toClosedLocalHintikkaCertificateOfPrimeSeparatingExtension hFU =
      C.toClosedLocalHintikkaCertificate := by
  cases C
  rfl

theorem exists_closedLocalAgreementWitness_of_exists_semantics_of_not_closedTheorySetProvable
    (C : CertifiedCountermodelCandidate Const [])
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
          C.frontier.antecedentTheorySet C.frontier.succedent)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M []),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const []},
            (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const []},
            (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ∃ (M : SemilocalModel.{u, v, w, w'} Base Const)
      (W : LocalAgreementWitness M C.frontier),
      W.certificate =
        C.toClosedLocalHintikkaCertificateOfNotClosedTheorySetProvable hNot ∧
      SemilocalModel.SupportsUniformRelativization M := by
  rcases hSem with ⟨M, env, global, true_top, false_ne_top, hM⟩
  refine ⟨M, C.toClosedLocalAgreementWitness (M := M) env global true_top false_ne_top, ?_, hM⟩
  simp [CertifiedCountermodelCandidate.toClosedLocalAgreementWitness,
    CertifiedCountermodelCandidate.toClosedLocalHintikkaCertificate,
    CountermodelCandidate.toClosedLocalAgreementWitnessOfClosedNonconflicting,
    CountermodelCandidate.toClosedLocalHintikkaCertificateOfClosedNonconflicting,
    CountermodelCandidate.toClosedLocalAgreementWitnessOfNoncontradictory,
    CountermodelCandidate.toClosedLocalHintikkaCertificate]

theorem exists_candidateClosedHintikkaSemantics_of_exists_closedLocalAgreementWitness_of_not_closedTheorySetProvable
    (C : CertifiedCountermodelCandidate Const [])
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
          C.frontier.antecedentTheorySet C.frontier.succedent)
    (hW :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const)
        (W : LocalAgreementWitness M C.frontier),
        W.certificate =
          C.toClosedLocalHintikkaCertificateOfNotClosedTheorySetProvable hNot ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M []),
      SemilocalModel.IsGlobalEnv M env ∧
      Nonempty
        (CertifiedCountermodelCandidate.CandidateClosedHintikkaSemantics C env) ∧
      SemilocalModel.SupportsUniformRelativization M := by
  rcases hW with ⟨M, W, hCert, hM⟩
  refine ⟨M, W.env, W.global, ?_, hM⟩
  exact ⟨C.toCandidateClosedHintikkaSemanticsOfClosedLocalAgreementWitness
    (M := M) W (by simpa using hCert)⟩

theorem exists_candidateClosedHintikkaSemantics_of_exists_semantics_of_not_closedTheorySetProvable
    (C : CertifiedCountermodelCandidate Const [])
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
          C.frontier.antecedentTheorySet C.frontier.succedent)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M []),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const []},
            (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const []},
            (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M []),
      SemilocalModel.IsGlobalEnv M env ∧
      Nonempty
        (CertifiedCountermodelCandidate.CandidateClosedHintikkaSemantics C env) ∧
      SemilocalModel.SupportsUniformRelativization M := by
  exact
    exists_candidateClosedHintikkaSemantics_of_exists_closedLocalAgreementWitness_of_not_closedTheorySetProvable
      (C := C) (hNot := hNot)
      (exists_closedLocalAgreementWitness_of_exists_semantics_of_not_closedTheorySetProvable
        (C := C) (hNot := hNot) hSem)

theorem not_derivable_of_exists_semantics_of_not_closedTheorySetProvable
    (C : CertifiedCountermodelCandidate Const [])
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
          C.frontier.antecedentTheorySet C.frontier.succedent)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M []),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const []},
            (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const []},
            (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := Base) (Const := Const) C.frontier.antecedents C.frontier.succedent := by
  exact C.not_derivable_of_exists_candidateClosedHintikkaSemantics
    (exists_candidateClosedHintikkaSemantics_of_exists_semantics_of_not_closedTheorySetProvable
      (C := C) (hNot := hNot) hSem)

theorem not_derivable_of_exists_candidateClosedHintikkaSemantics_of_not_closedTheorySetProvable
    (C : CertifiedCountermodelCandidate Const [])
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
          C.frontier.antecedentTheorySet C.frontier.succedent)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M []),
        SemilocalModel.IsGlobalEnv M env ∧
        Nonempty
          (CertifiedCountermodelCandidate.CandidateClosedHintikkaSemantics C env) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := Base) (Const := Const) C.frontier.antecedents C.frontier.succedent :=
  by
    let _ := hNot
    exact C.not_derivable_of_exists_candidateClosedHintikkaSemantics hSem

theorem not_derivable_of_exists_closedLocalAgreementWitness_of_not_closedTheorySetProvable
    (C : CertifiedCountermodelCandidate Const [])
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
          C.frontier.antecedentTheorySet C.frontier.succedent)
    (hW :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const)
        (W : LocalAgreementWitness M C.frontier),
        W.certificate =
          C.toClosedLocalHintikkaCertificateOfNotClosedTheorySetProvable hNot ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := Base) (Const := Const) C.frontier.antecedents C.frontier.succedent := by
  exact
    not_derivable_of_exists_candidateClosedHintikkaSemantics_of_not_closedTheorySetProvable
      (C := C) (hNot := hNot)
      (exists_candidateClosedHintikkaSemantics_of_exists_closedLocalAgreementWitness_of_not_closedTheorySetProvable
        (C := C) (hNot := hNot) hW)

theorem exists_closedLocalAgreementWitness_of_exists_semantics_of_primeSeparatingExtension
    (C : CertifiedCountermodelCandidate Const [])
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) C.frontier U)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M []),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const []},
            (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const []},
            (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ∃ (M : SemilocalModel.{u, v, w, w'} Base Const)
      (W : LocalAgreementWitness M C.frontier),
      W.certificate =
        C.toClosedLocalHintikkaCertificateOfPrimeSeparatingExtension hFU ∧
      SemilocalModel.SupportsUniformRelativization M := by
  rcases hSem with ⟨M, env, global, true_top, false_ne_top, hM⟩
  refine ⟨M, C.toClosedLocalAgreementWitness (M := M) env global true_top false_ne_top, ?_, hM⟩
  simp [CertifiedCountermodelCandidate.toClosedLocalAgreementWitness,
    CertifiedCountermodelCandidate.toClosedLocalHintikkaCertificate,
    CountermodelCandidate.toClosedLocalAgreementWitnessOfClosedNonconflicting,
    CountermodelCandidate.toClosedLocalHintikkaCertificateOfClosedNonconflicting,
    CountermodelCandidate.toClosedLocalAgreementWitnessOfNoncontradictory,
    CountermodelCandidate.toClosedLocalHintikkaCertificate]

theorem exists_candidateClosedHintikkaSemantics_of_exists_closedLocalAgreementWitness_of_primeSeparatingExtension
    (C : CertifiedCountermodelCandidate Const [])
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) C.frontier U)
    (hW :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const)
        (W : LocalAgreementWitness M C.frontier),
        W.certificate =
          C.toClosedLocalHintikkaCertificateOfPrimeSeparatingExtension hFU ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M []),
      SemilocalModel.IsGlobalEnv M env ∧
      Nonempty
        (CertifiedCountermodelCandidate.CandidateClosedHintikkaSemantics C env) ∧
      SemilocalModel.SupportsUniformRelativization M := by
  rcases hW with ⟨M, W, hCert, hM⟩
  refine ⟨M, W.env, W.global, ?_, hM⟩
  exact ⟨C.toCandidateClosedHintikkaSemanticsOfClosedLocalAgreementWitness
    (M := M) W (by simpa using hCert)⟩

theorem exists_candidateClosedHintikkaSemantics_of_exists_semantics_of_primeSeparatingExtension
    (C : CertifiedCountermodelCandidate Const [])
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) C.frontier U)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M []),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const []},
            (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const []},
            (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M []),
      SemilocalModel.IsGlobalEnv M env ∧
      Nonempty
        (CertifiedCountermodelCandidate.CandidateClosedHintikkaSemantics C env) ∧
      SemilocalModel.SupportsUniformRelativization M := by
  exact
    exists_candidateClosedHintikkaSemantics_of_exists_closedLocalAgreementWitness_of_primeSeparatingExtension
      (C := C) (hFU := hFU)
      (exists_closedLocalAgreementWitness_of_exists_semantics_of_primeSeparatingExtension
        (C := C) (hFU := hFU) hSem)

theorem not_derivable_of_exists_semantics_of_primeSeparatingExtension
    (C : CertifiedCountermodelCandidate Const [])
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) C.frontier U)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M []),
        SemilocalModel.IsGlobalEnv M env ∧
        (∀ {φ : Formula Const []},
            (Sign.trueE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ = ⊤) ∧
        (∀ {φ : Formula Const []},
            (Sign.falseE, φ) ∈ C.closedHintikka.formulas →
              SemilocalModel.formulaTruth M env φ ≠ ⊤) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := Base) (Const := Const) C.frontier.antecedents C.frontier.succedent := by
  exact C.not_derivable_of_exists_candidateClosedHintikkaSemantics
    (exists_candidateClosedHintikkaSemantics_of_exists_semantics_of_primeSeparatingExtension
      (C := C) (hFU := hFU) hSem)

theorem not_derivable_of_exists_candidateClosedHintikkaSemantics_of_primeSeparatingExtension
    (C : CertifiedCountermodelCandidate Const [])
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) C.frontier U)
    (hSem :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const) (env : SemilocalModel.Env M []),
        SemilocalModel.IsGlobalEnv M env ∧
        Nonempty
          (CertifiedCountermodelCandidate.CandidateClosedHintikkaSemantics C env) ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := Base) (Const := Const) C.frontier.antecedents C.frontier.succedent :=
  by
    let _ := hFU
    exact C.not_derivable_of_exists_candidateClosedHintikkaSemantics hSem

theorem not_derivable_of_exists_closedLocalAgreementWitness_of_primeSeparatingExtension
    (C : CertifiedCountermodelCandidate Const [])
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) C.frontier U)
    (hW :
      ∃ (M : SemilocalModel.{u, v, w, w'} Base Const)
        (W : LocalAgreementWitness M C.frontier),
        W.certificate =
          C.toClosedLocalHintikkaCertificateOfPrimeSeparatingExtension hFU ∧
        SemilocalModel.SupportsUniformRelativization M) :
    ¬ Derivable (Base := Base) (Const := Const) C.frontier.antecedents C.frontier.succedent := by
  exact
    not_derivable_of_exists_candidateClosedHintikkaSemantics_of_primeSeparatingExtension
      (C := C) (hFU := hFU)
      (exists_candidateClosedHintikkaSemantics_of_exists_closedLocalAgreementWitness_of_primeSeparatingExtension
        (C := C) (hFU := hFU) hW)

end CertifiedCountermodelCandidate

namespace CertifiedHeadPriorityCompletion

/-- Closed certified completions can consume canonical world counterexamples
directly into closed Hintikka certificates via the certified candidate bridge. -/
def toClosedLocalHintikkaCertificateOfWorldCounterexample
    {F : CompletenessFrontier Const []}
    (C : CertifiedHeadPriorityCompletion Const [] F)
    {W : ClosedTheorySet.World Const}
    (hAnte : ∀ phi, phi ∈ F.antecedents -> phi ∈ W.carrier)
    (hSucc : F.succedent ∉ W.carrier) :
    LocalHintikkaCertificate F :=
  C.toCertifiedCountermodelCandidate.toClosedLocalHintikkaCertificateOfWorldCounterexample
    hAnte hSucc

/-- Closed certified completions can also consume extensional closed-theory-set
non-provability directly into closed Hintikka certificates. -/
def toClosedLocalHintikkaCertificateOfNotClosedTheorySetProvable
    {F : CompletenessFrontier Const []}
    (C : CertifiedHeadPriorityCompletion Const [] F)
    (hNot :
      ¬ ClosedTheorySet.Provable (Const := Const)
          F.antecedentTheorySet F.succedent) :
    LocalHintikkaCertificate F :=
  C.toCertifiedCountermodelCandidate.toClosedLocalHintikkaCertificateOfNotClosedTheorySetProvable
    hNot

/-- Prime separating extensions can be consumed directly at the certified
completion layer without unpacking the certified countermodel candidate. -/
def toClosedLocalHintikkaCertificateOfPrimeSeparatingExtension
    {F : CompletenessFrontier Const []}
    (C : CertifiedHeadPriorityCompletion Const [] F)
    {U : ClosedTheorySet Const}
    (hFU : CompletenessFrontier.PrimeSeparatingExtension
      (Const := Const) F U) :
    LocalHintikkaCertificate F :=
  C.toCertifiedCountermodelCandidate.toClosedLocalHintikkaCertificateOfPrimeSeparatingExtension
    hFU

end CertifiedHeadPriorityCompletion

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
