import Mettapedia.Languages.Agda.Structural.AdministrativeStablePi
import Mettapedia.Languages.Agda.Structural.AdministrativeCompatiblePreservation

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics.StablePreservation

open Mettapedia.OSLF.Binding
open Preservation
open Statics (RawTm RawTy RawContext)

theorem nilArgs_eq {Γ : Ctx sig} (args : Args sig [] Γ) : args = .nil :=
  match args with | .nil => rfl

def singleArg {Γ : Ctx sig} {bs : List sig.Srt} {s : sig.Srt} (args : Args sig [(bs, s)] Γ) :
    {term : Term sig (bs ++ Γ) s // args = .cons term .nil} :=
  match args with | .cons term .nil => ⟨term, rfl⟩

noncomputable def compatibleBounded (beta : BetaCases) : (fuel : Nat) → ∀ {n : Nat} {s : Srt}
    {source target : Term sig (scope n) s} (step : Step source target),
    CompatibleDerivations.height step < fuel → StableAction source target
  | 0, _, _, _, _, _, small => False.elim (Nat.not_lt_zero _ small)
  | fuel + 1, _, _, _, _, step, small => by
      cases step with
      | root root => exact stableRoot beta root
      | congr op arguments =>
        cases op with
        | lam =>
            cases arguments with
            | head tail child =>
                have empty := nilArgs_eq tail
                cases empty
                intro σ
                exact (lambdaBind (termAt child (compatibleBounded beta fuel child (by
                    change CompatibleDerivations.height child + 1 < fuel + 1 at small
                    exact Nat.lt_of_succ_lt_succ small)) (Telescope.lift σ))).equality
            | tail head children => cases children
        | lamNoAbs =>
            cases arguments with
            | head tail child =>
                have empty := nilArgs_eq tail
                cases empty
                intro σ
                exact (stableNonbinding (stableTermAt child (compatibleBounded beta fuel child (by
                    change CompatibleDerivations.height child + 1 < fuel + 1 at small
                    exact Nat.lt_of_succ_lt_succ small)) σ)).equality
            | tail head children => cases children
        | pi =>
            cases arguments with
            | head tail child =>
                obtain ⟨codomain, rfl⟩ := singleArg tail
                intro σ
                exact piDomainAction codomain child (compatibleBounded beta fuel child (by
                    change CompatibleDerivations.height child + 1 < fuel + 1 at small
                    exact Nat.lt_of_succ_lt_succ small)) σ
            | tail domain children =>
                cases children with
                | head tail child =>
                    have empty := nilArgs_eq tail
                    cases empty
                    intro σ
                    exact piCodomainAction domain child (compatibleBounded beta fuel child (by
                    change CompatibleDerivations.height child + 1 < fuel + 1 at small
                    exact Nat.lt_of_succ_lt_succ small)) σ
                | tail head children => cases children
        | piNoAbs =>
            cases arguments with
            | head tail child =>
                obtain ⟨codomain, rfl⟩ := singleArg tail
                intro σ
                exact piNoAbsDomainAction codomain child (compatibleBounded beta fuel child (by
                    change CompatibleDerivations.height child + 1 < fuel + 1 at small
                    exact Nat.lt_of_succ_lt_succ small)) σ
            | tail domain children =>
                cases children with
                | head tail child =>
                    have empty := nilArgs_eq tail
                    cases empty
                    intro σ
                    exact piNoAbsCodomainAction domain child (compatibleBounded beta fuel child (by
                    change CompatibleDerivations.height child + 1 < fuel + 1 at small
                    exact Nat.lt_of_succ_lt_succ small)) σ
                | tail head children => cases children
        | eliminate =>
            cases arguments with
            | head tail child =>
                obtain ⟨spine, rfl⟩ := singleArg tail
                intro σ
                exact ((termAt child (compatibleBounded beta fuel child (by
                    change CompatibleDerivations.height child + 1 < fuel + 1 at small
                    exact Nat.lt_of_succ_lt_succ small)) σ).eliminateHead (bind σ spine)).equality
            | tail head children =>
                cases children with
                | head tail child =>
                    have empty := nilArgs_eq tail
                    cases empty
                    intro σ
                    exact ((spineAt child (compatibleBounded beta fuel child (by
                    change CompatibleDerivations.height child + 1 < fuel + 1 at small
                    exact Nat.lt_of_succ_lt_succ small)) σ).eliminateSpine (bind σ head)).equality
                | tail head children => cases children
        | sortTerm =>
            cases arguments with
            | head tail child =>
                have empty := nilArgs_eq tail
                cases empty
                intro σ Γ A tree
                obtain ⟨k, boundary⟩ := (CoreDerivation.constructorView tree).sort _ rfl
                exact (sortAction child σ k boundary).elim
            | tail head children => cases children
        | levelTerm =>
            cases arguments with
            | head tail child =>
                have empty := nilArgs_eq tail
                cases empty
                intro σ Γ A tree
                exact False.elim ((CoreDerivation.constructorView tree).level _ rfl)
            | tail head children => cases children
        | el =>
            cases arguments with
            | head tail child =>
                obtain ⟨code, rfl⟩ := singleArg tail
                intro σ Γ tree
                let view := tree.formationView
                have same := (el_injective view.boundary).1
                exact (sortAction child σ view.parameter.level same).elim
            | tail sort children =>
                cases children with
                | head tail child =>
                    have empty := nilArgs_eq tail
                    cases empty
                    intro σ
                    exact (elTerm (termAt child (compatibleBounded beta fuel child (by
                    change CompatibleDerivations.height child + 1 < fuel + 1 at small
                    exact Nat.lt_of_succ_lt_succ small)) σ) (bind σ sort)).equality
                | tail head children => cases children
        | set => exact sortAction (CompatibleDerivations.Step.congr (R := Root) Op.set arguments)
        | prop => exact sortAction (CompatibleDerivations.Step.congr (R := Root) Op.prop arguments)
        | levelSuc => exact levelAction (CompatibleDerivations.Step.congr (R := Root) Op.levelSuc arguments)
        | levelMax => exact levelAction (CompatibleDerivations.Step.congr (R := Root) Op.levelMax arguments)
        | levelNeutral => exact levelAction (CompatibleDerivations.Step.congr (R := Root) Op.levelNeutral arguments)
        | apply =>
            cases arguments with
            | head tail child =>
                have empty := nilArgs_eq tail
                cases empty
                intro σ Γ A B rest tree
                exact ((termAt child (compatibleBounded beta fuel child (by
                    change CompatibleDerivations.height child + 1 < fuel + 1 at small
                    exact Nat.lt_of_succ_lt_succ small)) σ).argument rest).equality Γ A B tree
            | tail head children => cases children
        | cons =>
            cases arguments with
            | head tail child =>
                obtain ⟨rest, rfl⟩ := singleArg tail
                intro σ Γ A B tree
                exact compatibleBounded beta fuel child (by
                    change CompatibleDerivations.height child + 1 < fuel + 1 at small
                    exact Nat.lt_of_succ_lt_succ small) σ Γ A B (bind σ rest) tree
            | tail head children =>
                cases children with
                | head tail child =>
                    have empty := nilArgs_eq tail
                    cases empty
                    intro σ
                    exact ((spineAt child (compatibleBounded beta fuel child (by
                    change CompatibleDerivations.height child + 1 < fuel + 1 at small
                    exact Nat.lt_of_succ_lt_succ small)) σ).consTail (bind σ head)).equality
                | tail head children => cases children
        | append =>
            cases arguments with
            | head tail child =>
                obtain ⟨rest, rfl⟩ := singleArg tail
                intro σ
                exact ((spineAt child (compatibleBounded beta fuel child (by
                    change CompatibleDerivations.height child + 1 < fuel + 1 at small
                    exact Nat.lt_of_succ_lt_succ small)) σ).appendFirst (bind σ rest)).equality
            | tail head children =>
                cases children with
                | head tail child =>
                    have empty := nilArgs_eq tail
                    cases empty
                    intro σ
                    exact ((spineAt child (compatibleBounded beta fuel child (by
                    change CompatibleDerivations.height child + 1 < fuel + 1 at small
                    exact Nat.lt_of_succ_lt_succ small)) σ).appendSecond (bind σ head)).equality
                | tail head children => cases children
        | defined | constructor | natLiteral | setOmega | levelClosed | proj | nil => cases arguments
termination_by structural fuel _ _ _ _ _ _ => fuel

noncomputable def compatible (beta : BetaCases) {n : Nat} {s : Srt}
    {source target : Term sig (scope n) s} (step : Step source target) : StableAction source target :=
  compatibleBounded beta (CompatibleDerivations.height step + 1) step (Nat.lt_succ_self _)

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics.StablePreservation
