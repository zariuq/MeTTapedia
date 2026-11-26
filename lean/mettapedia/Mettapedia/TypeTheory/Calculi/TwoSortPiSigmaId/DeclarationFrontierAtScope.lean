import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSemantics

namespace Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSemantics

open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Context
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationEnv
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Reduction

private abbrev declReductionReadoutAt (E : DeclEnv) (n : Nat) (tail : Prop) : Prop :=
  (∀ {Γ : Ctx n} {t u A : ScopedTerm n},
      HasTypeDecl E Γ t A → RedStarDecl E t u → HasTypeDecl E Γ u A) ∧
  (∀ {s t₁ t₂ : ScopedTerm n}, RedStarDecl E s t₁ → RedStarDecl E s t₂ →
      ∃ u, RedStarDecl E t₁ u ∧ RedStarDecl E t₂ u) ∧
  (∀ {s t : ScopedTerm n}, ConvDecl E s t → ∃ u, RedStarDecl E s u ∧ RedStarDecl E t u) ∧
  (∀ {A A' : ScopedTerm n} {B B' : ScopedTerm (n + 1)},
      ConvDecl E (.pi A B) (.pi A' B') → ConvDecl E A A' ∧ ConvDecl E B B') ∧ tail

private abbrev declSigmaInjectivityAt (E : DeclEnv) (n : Nat) : Prop :=
  ∀ {A A' : ScopedTerm n} {B B' : ScopedTerm (n + 1)},
    ConvDecl E (.sigma A B) (.sigma A' B') → ConvDecl E A A' ∧ ConvDecl E B B'

/-- Preservation, confluence, joinability and binder injectivity at one
declaration scope. The bodies of Π and Σ retain their extra binder. -/
abbrev DeclChurchRosserReadoutAt (E : DeclEnv) (n : Nat) : Prop :=
  declReductionReadoutAt E n (declSigmaInjectivityAt E n)

/-- The same scope readout with soundness of a returned normalization witness
and soundness of checker success when only nonemptiness was observed. -/
abbrev DeclNoValuesReadoutAt
    (E : DeclEnv) (hNone : ∀ c : DeclName, valueOf? E c = none) (n : Nat) : Prop :=
  declReductionReadoutAt E n
    (declSigmaInjectivityAt E n ∧
      (∀ {A B : ScopedTerm n} {w : DefEqDeclWitness E A B},
        defEqByNormalizationDeclOfNoValues? E hNone A B = some w → ConvDecl E A B) ∧
      (∀ {A B : ScopedTerm n},
        defEqByNormalizationDeclOfNoValues? E hNone A B ≠ none → ConvDecl E A B))

theorem DeclChurchRosserFrontierPackage.atScope {E : DeclEnv}
    (laws : DeclChurchRosserFrontierPackage E) (n : Nat) : DeclChurchRosserReadoutAt E n := by
  obtain ⟨_, preservation, confluence, joins, pi, sigma⟩ := laws
  exact ⟨preservation (n := n), confluence (n := n), joins (k := n),
    pi (n := n), sigma (n := n)⟩

theorem DeclNoValuesFrontierPackage.atScope {E : DeclEnv}
    {hNone : ∀ c : DeclName, valueOf? E c = none}
    (laws : DeclNoValuesFrontierPackage E hNone) (n : Nat) : DeclNoValuesReadoutAt E hNone n := by
  obtain ⟨preservation, confluence, joins, pi, sigma⟩ := laws.1.atScope n
  obtain ⟨witness, success⟩ := laws.2
  exact ⟨preservation, confluence, joins, pi, sigma, witness (n := n), success (n := n)⟩

theorem declChurchRosserFrontier_iff_atScopes (E : DeclEnv) :
    DeclChurchRosserFrontierPackage E ↔ DeclEnvWellFormed E ∧ ∀ n, DeclChurchRosserReadoutAt E n := by
  constructor
  · intro laws
    exact ⟨laws.1, laws.atScope⟩
  · rintro ⟨wellFormed, laws⟩
    refine ⟨wellFormed, ?_, ?_, ?_, ?_, ?_⟩
    · intro n
      exact (laws n).1
    · intro n
      exact (laws n).2.1
    · intro n
      exact (laws n).2.2.1
    · intro n
      exact (laws n).2.2.2.1
    · intro n
      exact (laws n).2.2.2.2

theorem DeclNoValuesReadoutAt.asChurchRosser {E : DeclEnv} {n : Nat}
    {hNone : ∀ c : DeclName, valueOf? E c = none}
    (laws : DeclNoValuesReadoutAt E hNone n) : DeclChurchRosserReadoutAt E n := by
  obtain ⟨preservation, confluence, joins, pi, sigma, _, _⟩ := laws
  exact ⟨preservation, confluence, joins, pi, sigma⟩

theorem declNoValuesFrontier_iff_atScopes
    (E : DeclEnv) (hNone : ∀ c : DeclName, valueOf? E c = none) :
    DeclNoValuesFrontierPackage E hNone ↔
      DeclEnvWellFormed E ∧ ∀ n, DeclNoValuesReadoutAt E hNone n := by
  constructor
  · intro laws
    exact ⟨laws.1.1, laws.atScope⟩
  · rintro ⟨wellFormed, byScope⟩
    refine ⟨(declChurchRosserFrontier_iff_atScopes E).mpr
      ⟨wellFormed, fun n => (byScope n).asChurchRosser⟩, ?_, ?_⟩
    · intro n
      exact (byScope n).2.2.2.2.2.1
    · intro n
      exact (byScope n).2.2.2.2.2.2

end Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSemantics
