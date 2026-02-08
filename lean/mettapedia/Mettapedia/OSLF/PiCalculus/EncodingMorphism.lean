import Mettapedia.OSLF.PiCalculus.WeakBisim
import Mettapedia.OSLF.Framework.LanguageMorphism

/-!
# Encoding Morphism: π → ρ (Forward Direction)

Organizes the Lybech (2022) encoding correctness proof as a structured
morphism, following the LanguageMorphism framework.

## What Is Sorry-Free

1. **The encoding function** (`encode : Process → String → String → Pattern`)
   in `RhoEncoding.lean` — the π→ρ translation itself has no sorries.

2. **The Encoded grammar** (`Encoded n v P`) — a syntactic characterization of
   the image of `encode`, with a proven `encode_is_Encoded` theorem.

3. **The OSLF framework** (`LanguageMorphism`, `piCalc : LanguageDef`,
   `forward_multi_strong`, `preserves_diamond`) — generic simulation theory.

4. **Bisimilarity infrastructure** (`WeakRestrictedBisim` with refl/symm/trans/
   mono/of_SC/empty, `RhoBisimilar` with refl/symm/trans) — all proven.

## Forward Direction (WIP)

The forward simulation (`prop4_forward`) wraps existing infrastructure:
- `forward_comm_simple` for COMM (simple + Barendregt) — proven
- par_left/par_right from `forward_single_step` — proven
- `forward_multi_step` for multi-step composition — proven modulo single-step

Three cases in `forward_single_step` remain sorry:
- **COMM** (general): needs Prop 1 (parameter independence n_L → n)
- **RES**: needs COMM-first approach (reduction under ν-encoding)
- **STRUCT**: needs EncEquiv bridge (SC-to-reduction composition)

## Backward Direction (TODO)

Not attempted here. The backward direction (showing every ρ-reduction of an
encoded term corresponds to a π-reduction) requires SC inversion, which is
hard due to the EQUIV rule allowing arbitrary SC rearrangement.

## References

- Lybech (2022), Section 6, pages 104-107
- Gorla (2010), "Towards a Unified Approach to Encodability and Separation Results"
-/

namespace Mettapedia.OSLF.PiCalculus.EncodingMorphism

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.PiCalculus
open Mettapedia.OSLF.RhoCalculus
open Mettapedia.OSLF.Framework.LangMorphism

/-! ## The "Encoded" Predicate

Describes the grammar of patterns that `encode P n v` can produce for any
Process P. This constrains the image of the encoding and is the foundation
for any future backward-direction work.

Key property: `encode_is_Encoded` (proven) shows every encoded process
satisfies this grammar. -/

/-- Patterns in the image of the encoding function `encode P n v`.

    Each constructor mirrors one case of `encode`:
    - `nil`: encode(.nil) = rhoNil (empty bag)
    - `par`: encode(P|Q) = rhoPar(encode P n_L v)(encode Q n_R v)
    - `input`: encode(x(y).P) = rhoInput(.fvar x, y, encode P)
    - `output`: encode(x<z>) = rhoOutput(.fvar x, rhoDrop(.fvar z))
    - `nu`: encode(νx.P) = rhoPar(v<n>)(n(x).encode P ns v)
    - `replicate`: encode(!x(y).P) = rhoReplicate(rhoInput(.fvar x, y, encode P)) -/
inductive Encoded : String → String → Pattern → Prop where
  | nil (n v : String) : Encoded n v rhoNil
  | par {n v : String} {P Q : Pattern} :
      Encoded (n ++ "_L") v P → Encoded (n ++ "_R") v Q →
      Encoded n v (rhoPar P Q)
  | input {n v : String} {x y : String} {body : Pattern} :
      Encoded n v body →
      Encoded n v (rhoInput (.fvar x) y body)
  | output {n v : String} (x z : String) :
      Encoded n v (rhoOutput (.fvar x) (rhoDrop (.fvar z)))
  | nu {n v : String} {x : String} {body : Pattern} :
      Encoded (n ++ "_" ++ n) v body →
      Encoded n v (rhoPar (rhoOutput (.fvar v) (.fvar n))
                          (rhoInput (.fvar n) x body))
  | replicate {n v : String} {x y : String} {body : Pattern} :
      Encoded (n ++ "_rep") v body →
      Encoded n v (rhoReplicate (rhoInput (.fvar x) y body))

/-- The encoding function produces Encoded patterns. -/
theorem encode_is_Encoded (P : Process) (n v : String) :
    Encoded n v (encode P n v) := by
  induction P generalizing n with
  | nil => exact .nil n v
  | par P Q ihP ihQ => exact .par (ihP (n ++ "_L")) (ihQ (n ++ "_R"))
  | input x y P ihP => exact .input (ihP n)
  | output x z => exact .output x z
  | nu x P ihP => exact .nu (ihP (n ++ "_" ++ n))
  | replicate x y P ihP => exact .replicate (ihP (n ++ "_rep"))

/-! ## Forward Direction

Wraps existing proven infrastructure to state the forward simulation theorem:
if P →* P' in the π-calculus, then encode(P) →* T in the ρ-calculus where
T is weakly bisimilar to encode(P'). -/

/-- Forward simulation for single π-step, using WeakRestrictedBisim.

    Lifts from `forward_single_step` (which uses SC) to bisim (which is weaker).
    The 3 sorries in `forward_single_step` (comm, res, struct) propagate here. -/
theorem forward_single_step_bisim {N : Finset String} {P P' : Process}
    (h : Reduces P P') (n v : String) :
    ∃ T, Nonempty (ReducesStar (encode P n v) T) ∧ T ≈{N} (encode P' n v) := by
  obtain ⟨T, h_star, h_sc⟩ := forward_single_step h n v
  exact ⟨T, h_star, WeakRestrictedBisim.of_SC h_sc⟩

/-- Multi-step forward simulation, using WeakRestrictedBisim.

    Lifts from `forward_multi_step` (0 local sorries) to bisim.
    Depends on `forward_single_step` sorries propagating through. -/
theorem forward_multi_step_bisim {N : Finset String} {P P' : Process}
    (h : MultiStep P P') (n v : String) :
    ∃ T, Nonempty (ReducesStar (encode P n v) T) ∧ T ≈{N} (encode P' n v) := by
  obtain ⟨T, h_star, h_sc⟩ := forward_multi_step h n v
  exact ⟨T, h_star, WeakRestrictedBisim.of_SC h_sc⟩

/-! ## Main Theorem: Forward Operational Correspondence (Prop 4, Forward)

The π→ρ encoding gives forward operational correspondence up to weak
bisimilarity. This is the MAIN theorem. -/

/-- Proposition 4 (Forward): π multi-step → ρ multi-step + bisim.

    If P →* P' in the π-calculus, then encode(P) →* T in the ρ-calculus
    where T is weakly bisimilar to encode(P').

    **Sorry count**: Inherits 3 sorries from `forward_single_step`
    (comm, res, struct). The composition (`forward_multi_step`) is proven. -/
theorem prop4_forward {N : Finset String} {P P' : Process}
    (h : MultiStep P P') (n v : String) :
    ∃ T, Nonempty (ReducesStar (encode P n v) T) ∧ T ≈{N} (encode P' n v) :=
  forward_multi_step_bisim h n v

/-! ## Sorry Inventory (Forward Direction)

### `forward_single_step` (3 sorries, in `WeakBisim.lean` stub):

1. **COMM** (general case): After ρ-COMM fires, the result lives in namespace
   `n_L` but the target uses `n`. Chain exists but not composed:
   - `encode_comm_SC`: COMM fires (proven in original)
   - `encoding_substitution_barendregt`: substitution bridge (proven)
   - `encode_independent_of_n` / `applySubst_nsEnv_encode`: namespace bridge
   - **Gap**: general case requires Prop 1 (parameter independence)
   - **Workaround**: `forward_comm_simple` proves this for simple+Barendregt

2. **RES**: `encode(νx.P)` puts the body behind an input guard.
   Standard ρ-calculus has no reduction under input.
   - **Solution**: COMM-first approach (fire name server COMM, then reduce)
   - **Status**: Not implemented

3. **STRUCT**: π-SC changes namespace assignment to sub-processes.
   - **Solution**: EncEquiv (SC + renaming) via `encode_preserves_pi_SC_enc`
   - **Gap**: composing EncEquiv with reduction chain

### Backward direction (TODO, not attempted):

4. **BACKWARD**: Inversion of ρ-reduction on encoded terms.
   - **Blocked by**: EQUIV rule (arbitrary SC rearrangement) makes inversion hard
   - **Infrastructure available**: `Encoded` grammar + `encode_is_Encoded` (proven)
-/

end Mettapedia.OSLF.PiCalculus.EncodingMorphism
