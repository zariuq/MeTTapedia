import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSweepWitnessesSort

/-!
# An unknown of a pair type, equated at a pair type with a raised component

Over `A : U0, p : Σ (_ : U0). U0`, at the annotation `Σ (_ : U0). U1`, whose second component is one universe above
the declaration of `p`. Both stores are in the dynamic pattern fragment, and the top family (`sortTower`) is stuck
on them wherever its compiled run reads `stuck`.

**`pairRaisedStore`**: `p ≐ ⟨A, A⟩`. It is solvable, by `p := ⟨A, A⟩` (`pairRaised_solvable`). The reading at the
least annotation lowers the universe at the end of a telescope of Π types; it does not lower a component of a Σ
type, so this store is not read at `Σ (_ : U0). U0`, where the families below commit.

**`pairSortStore`**: `p ≐ ⟨A, U0⟩`. It has no solution (`pairSort_unsolvable`): the second component of `p` is a
type of `U0`, and `U0` is not equal to a type of `U0`. The refutation of a universe reads an equation of types; it
does not read the components of a pair.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentSweep.Witnesses

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment
open ContextualDependentPatternFiring.Controls ContextualDependentAcceptance4
open ContextualDependentEtaDepth ContextualDependentEtaDepth.Controls ContextualDependentEtaDepth.ArgControls
open ContextualDependentEtaDepth.BaseControls ContextualDependentUniverseInjective

/-- `Σ (_ : U0). U0`, over `A`. -/
def pairFamily : TypeOver ctxA :=
  formIn ctxA (.sigma (.head (.sort Tower.zero)) (.head (.sort Tower.zero))) (by decide +kernel)

/-- `A : U0, p : Σ (_ : U0). U0`. -/
abbrev ctxAp := extend ctxA pairFamily

/-- `Σ (_ : U0). U1`, over `A p`. -/
def pairRaisedType : TypeOver ctxAp :=
  formIn ctxAp (.sigma (.head (.sort Tower.zero)) (.head (.sort (.succ Tower.zero)))) (by decide +kernel)

/-- `p ≐ ⟨A, A⟩` at `Σ (_ : U0). U1`. -/
def pairRaisedEquation : Equation (TotalTerm ctxAp) :=
  (termIn ctxAp pairRaisedType (.var 0) (by decide +kernel),
    termIn ctxAp pairRaisedType (.pair (.var 1) (.var 1)) (by decide +kernel))

def pairRaisedStore : EquationStore (TotalTerm ctxAp) := [pairRaisedEquation]

/-- The raw problem of the sweep. -/
def pairRaisedProblem : Problem :=
  { unknowns := [.u0, .sigma .u0 .u0], equations := [(.sigma .u0 .u1, .var 0, .pair (.var 1) (.var 1))] }

theorem pairRaised_in_fragment : InFragmentStore pairRaisedStore := storeInside_sound (by decide +kernel)

/-- `p := ⟨A, A⟩`. -/
def pairRaisedAnswer : ctxA ⟶ ctxAp :=
  Elimination.instantiate ctxA (termIn ctxA pairFamily (.pair (.var 0) (.var 0)) (by decide +kernel)).2

/-- **The store is solvable**, by `p := ⟨A, A⟩`. -/
theorem pairRaised_solvable : (frames setting.levels).Solvable pairRaisedStore :=
  solvable_by pairRaisedAnswer pairRaisedEquation.1.2 pairRaisedEquation.2.2 (by decide +kernel)

/-- **A solvable store of the fragment on which the top family is stuck** wherever its compiled run reads `stuck`:
the reading at the least annotation does not lower a component of a Σ type. -/
theorem pairRaised_gap_of_ending {fuel rounds : Nat}
    (read : endingSort fuel rounds ctxAp pairRaisedStore = .stuck) :
    InFragmentStore pairRaisedStore ∧ (frames setting.levels).Solvable pairRaisedStore ∧
      isStuck (run (sortTower.solver fuel) pairRaisedStore rounds) = true :=
  ⟨pairRaised_in_fragment, pairRaised_solvable, stuck_of_endingSort read⟩

/-- `p ≐ ⟨A, U0⟩` at `Σ (_ : U0). U1`. -/
def pairSortEquation : Equation (TotalTerm ctxAp) :=
  (termIn ctxAp pairRaisedType (.var 0) (by decide +kernel),
    termIn ctxAp pairRaisedType (.pair (.var 1) (.head (.sort Tower.zero))) (by decide +kernel))

def pairSortStore : EquationStore (TotalTerm ctxAp) := [pairSortEquation]

/-- The raw problem of the sweep. -/
def pairSortProblem : Problem :=
  { unknowns := [.u0, .sigma .u0 .u0], equations := [(.sigma .u0 .u1, .var 0, .pair (.var 1) .u0)] }

theorem pairSort_in_fragment : InFragmentStore pairSortStore := storeInside_sound (by decide +kernel)

/-- **The store has no solution**: under a solution `p := q`, the second component of `q` is a type of `U0` equal
to `U0`. -/
theorem pairSort_unsolvable : ¬ (frames setting.levels).Solvable pairSortStore := by
  rintro ⟨Δ, σ, solved⟩
  have held := solved pairSortEquation List.mem_cons_self
  obtain ⟨_, equal⟩ := (ContextualDependentRigidFormers.solves_raw (S := setting) σ pairSortEquation).mp held
  have typeCode : pairSortEquation.1.1.code =
      .sigma (.head (.sort Tower.zero)) (.head (.sort (.succ Tower.zero))) := formIn_code _ _ _
  rw [typeCode] at equal
  have small : setting.R.isUniverse (.sort Tower.zero) := by decide +kernel
  have large : setting.R.isUniverse (.sort (.succ Tower.zero)) := by decide +kernel
  have familyCode : pairFamily.code = .sigma (.head (.sort Tower.zero)) (.head (.sort Tower.zero)) :=
    formIn_code _ _ _
  have declared := σ.typed (⟨0, Nat.zero_lt_succ 1⟩ : Fin 2)
  change Typed setting.R Δ.raw (σ.substitution (⟨0, Nat.zero_lt_succ 1⟩ : Fin 2))
    (subst σ.substitution (Presentation.rename wk pairFamily.code)) at declared
  rw [familyCode] at declared
  have second : Typed setting.R Δ.raw (.snd (σ.substitution (⟨0, Nat.zero_lt_succ 1⟩ : Fin 2)))
      (.head (.sort Tower.zero)) := Derivable.sndElim declared
  obtain ⟨_, typedPair⟩ := Equal.typed equal Δ.formed
  obtain ⟨u, hu, tSigma⟩ := Typed.isType typedPair Δ.formed
  have tFirst : Typed setting.R Δ.raw (σ.substitution (⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩ : Fin 2))
      (.head (.sort Tower.zero)) := σ.typed (⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩ : Fin 2)
  have tSecond : Typed setting.R Δ.raw (.head (.sort Tower.zero)) (.head (.sort (.succ Tower.zero))) :=
    Derivable.headType (.sort _)
  have seconds : Equal setting.R Δ.raw (.snd (σ.substitution (⟨0, Nat.zero_lt_succ 1⟩ : Fin 2)))
      (.snd (.pair (σ.substitution (⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩ : Fin 2))
        (.head (.sort Tower.zero)))) (.head (.sort (.succ Tower.zero))) := Derivable.sndCong equal
  have beta : Equal setting.R Δ.raw
      (.snd (.pair (σ.substitution (⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩ : Fin 2))
        (.head (.sort Tower.zero)))) (.head (.sort Tower.zero)) (.head (.sort (.succ Tower.zero))) :=
    Derivable.betaSnd tSigma hu tFirst tSecond
  have joined : TypeEq setting.R Δ.raw (.snd (σ.substitution (⟨0, Nat.zero_lt_succ 1⟩ : Fin 2)))
      (.head (.sort Tower.zero)) := ⟨_, large, .trans seconds beta⟩
  refine sort_not_small (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentPiSpine.Controls.rigid TowerModel.complete Δ.formed small ?_ second joined
  intro above typing c
  cases typing
  exact absurd c (by decide +kernel)

/-- **A store of the fragment without solution on which the top family is stuck** wherever its compiled run reads
`stuck`: the refutation of a universe does not read the components of a pair. -/
theorem pairSort_gap_of_ending {fuel rounds : Nat} (read : endingSort fuel rounds ctxAp pairSortStore = .stuck) :
    InFragmentStore pairSortStore ∧ ¬ (frames setting.levels).Solvable pairSortStore ∧
      isStuck (run (sortTower.solver fuel) pairSortStore rounds) = true :=
  ⟨pairSort_in_fragment, pairSort_unsolvable, stuck_of_endingSort read⟩

end ContextualDependentSweep.Witnesses
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
