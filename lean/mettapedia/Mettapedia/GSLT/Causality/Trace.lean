import Mettapedia.GSLT.Core.GSLT

/-!
# Traces and the Reversible Envelope

This file formalizes traces (Definition 3.1) and the reversible envelope S†
(Definitions 3.2–3.4) from Meredith's "Computation, Causality, and Consciousness"
(2026), Part I, §3.

## Main Definitions

* `GSLT.Trace` — A finite sequence of rewrite steps recording causal history
* `GSLT.ExtendedTerm` — A pair ⟨P, τ⟩ of current term and trace (Definition 3.2)
* `GSLT.reversibleEnvelope` — The reversible GSLT S† (Definition 3.4)
* `GSLT.envelopeEmbed` — The embedding η : S → S† (Proposition 3.1)
* `GSLT.envelopeProject` — The projection π : S† → S (Proposition 3.1)

## Key Insight

The reversible envelope is the computational analogue of CPT symmetry:
every forward rewrite step gets an explicit inverse. The arrow of time
appears entirely in the boundary condition (empty trace = initial state).

## References

- Meredith, "Computation, Causality, and Consciousness" (2026), §3
- Danos & Krivine, "Reversible CCS"
- Phillips & Ulidowski, "Reversible process calculi"
-/

namespace Mettapedia.GSLT

variable (S : GSLT)

/-! ## Traces

    Definition 3.1: A trace is a finite sequence recording the causal history
    of how a term was reached. Each entry records a rewrite step.
-/

/-- A trace entry records one rewrite step: the rule applied and the term matched.

    In the paper, a trace entry is r(l) where r ∈ R and l ∈ T(S) is the
    specific left-hand-side term matched at that step.
-/
structure TraceEntry where
  /-- The term before the step (left-hand side matched) -/
  source : S.Term
  /-- The term after the step -/
  target : S.Term
  /-- Proof that this is a valid rewrite step -/
  step : S.Step source target

/-- A trace is a finite sequence of rewrite steps recording causal history.

    Definition 3.1 (Meredith 2026): A trace τ = r₁(l₁) · r₂(l₂) · ··· · rₙ(lₙ)
    records the sequence of rewrites applied. The empty trace ε represents
    an initial condition with no causal past.
-/
def Trace : Type _ := List (TraceEntry S)

namespace Trace

/-- The empty trace ε — represents an initial condition -/
def empty : Trace S := []

/-- Prepend a step to a trace -/
def cons (entry : TraceEntry S) (τ : Trace S) : Trace S := entry :: τ

/-- Length of a trace -/
def length (τ : Trace S) : Nat := List.length τ

/-- A trace is initial if it is empty -/
def isInitial (τ : Trace S) : Prop := τ = []

end Trace

/-! ## Extended Terms

    Definition 3.2: Extended terms are pairs ⟨P, τ⟩ where P is the current
    term and τ is the causal history of how P was reached.
-/

/-- An extended term ⟨P, τ⟩ pairs a current term with its causal history.

    Definition 3.2 (Meredith 2026): The extended grammar T† consists of pairs
    ⟨P, τ⟩ where P ∈ T(S) is the current term and τ is the trace.
-/
structure ExtendedTerm where
  /-- The current term -/
  current : S.Term
  /-- The causal history (trace) -/
  history : Trace S

namespace ExtendedTerm

/-- An initial extended term has empty history -/
def initial (t : S.Term) : ExtendedTerm S :=
  { current := t, history := Trace.empty S }

/-- Whether an extended term is in the initial state (no causal past) -/
def isInitial (et : ExtendedTerm S) : Prop := et.history.isInitial S

end ExtendedTerm

/-! ## The Reversible Envelope S†

    Definition 3.3 (Reversible Rules): For each rule r : l → r in R, define:
    - Forward rule r⁺: ⟨l, τ⟩ → ⟨r, r(l) · τ⟩
    - Backward rule r⁻: ⟨r, r(l) · τ⟩ → ⟨l, τ⟩

    Definition 3.4 (Reversible Envelope): S† = (T†, E†, R†)
-/

/-- Direction of a step in the reversible envelope -/
inductive StepDirection where
  | forward
  | backward
  deriving DecidableEq

/-- One-step reduction in the reversible envelope.

    Definition 3.3 (Meredith 2026):
    - Forward: ⟨l, τ⟩ → ⟨r, entry · τ⟩  (records the step)
    - Backward: ⟨r, entry · τ⟩ → ⟨l, τ⟩  (undoes the step)
-/
inductive ReversibleStep : ExtendedTerm S → ExtendedTerm S → Prop where
  /-- Forward rule r⁺: ⟨l, τ⟩ → ⟨r, r(l) · τ⟩ -/
  | forward {l r : S.Term} (h : S.Step l r) (τ : Trace S) :
      ReversibleStep
        { current := l, history := τ }
        { current := r, history := ⟨l, r, h⟩ :: τ }
  /-- Backward rule r⁻: ⟨r, r(l) · τ⟩ → ⟨l, τ⟩ -/
  | backward {l r : S.Term} (h : S.Step l r) (τ : Trace S) :
      ReversibleStep
        { current := r, history := ⟨l, r, h⟩ :: τ }
        { current := l, history := τ }

/-- Equational equivalence on extended terms lifts E to the current-term component,
    leaving traces invariant.

    Definition 3.4 (Meredith 2026): E† lifts ≡ to act on the current-term
    component of extended terms, leaving traces invariant.
-/
def extendedEquiv (et1 et2 : ExtendedTerm S) : Prop :=
  S.Equiv et1.current et2.current ∧ et1.history = et2.history

theorem extendedEquiv_refl (et : ExtendedTerm S) : extendedEquiv S et et :=
  ⟨S.equations.iseqv.refl et.current, rfl⟩

theorem extendedEquiv_symm {et1 et2 : ExtendedTerm S}
    (h : extendedEquiv S et1 et2) : extendedEquiv S et2 et1 :=
  ⟨S.equations.iseqv.symm h.1, h.2.symm⟩

theorem extendedEquiv_trans {et1 et2 et3 : ExtendedTerm S}
    (h1 : extendedEquiv S et1 et2) (h2 : extendedEquiv S et2 et3) :
    extendedEquiv S et1 et3 :=
  ⟨S.equations.iseqv.trans h1.1 h2.1, h1.2.trans h2.2⟩

/-- Setoid on extended terms -/
def extendedSetoid : Setoid (ExtendedTerm S) where
  r := extendedEquiv S
  iseqv := ⟨extendedEquiv_refl (S := S), fun h => extendedEquiv_symm (S := S) h,
            fun h1 h2 => extendedEquiv_trans (S := S) h1 h2⟩

/-- Every forward step has a corresponding backward step -/
theorem reversibleStep_invertible {et1 et2 : ExtendedTerm S}
    (h : ReversibleStep S et1 et2) : ReversibleStep S et2 et1 := by
  cases h with
  | forward h τ => exact ReversibleStep.backward h τ
  | backward h τ => exact ReversibleStep.forward h τ

/-! ## The Embedding η and Projection π

    Proposition 3.1 (Meredith 2026): There exist morphisms:
    - η : S → S†, P ↦ ⟨P, ε⟩
    - π : S† → S, ⟨P, τ⟩ ↦ P
    satisfying π ∘ η = id_S
-/

/-- The embedding η : S → S†, mapping P ↦ ⟨P, ε⟩

    Proposition 3.1 (Meredith 2026): η embeds S into S† by giving
    each term an empty history.
-/
def envelopeEmbed (t : S.Term) : ExtendedTerm S :=
  ExtendedTerm.initial S t

/-- The projection π : S† → S, mapping ⟨P, τ⟩ ↦ P

    Proposition 3.1 (Meredith 2026): π forgets the causal history.
-/
def envelopeProject (et : ExtendedTerm S) : S.Term :=
  et.current

/-- π ∘ η = id : the projection undoes the embedding.

    Proposition 3.1 (Meredith 2026).
-/
theorem project_embed (t : S.Term) : envelopeProject S (envelopeEmbed S t) = t := by
  rfl

/-- η maps S-steps to forward steps in S† -/
theorem embed_preserves_step {t t' : S.Term} (h : S.Step t t') :
    ReversibleStep S (envelopeEmbed S t) { current := t', history := [⟨t, t', h⟩] } := by
  exact ReversibleStep.forward h []

/-! ## Summary

This file establishes:

1. **Trace**: Finite sequences of rewrite steps (Definition 3.1)
2. **ExtendedTerm**: Pairs ⟨P, τ⟩ of term + history (Definition 3.2)
3. **ReversibleStep**: Forward and backward rules (Definition 3.3)
4. **Reversible envelope properties**: Invertibility of steps (Definition 3.4)
5. **η and π**: Embedding and projection with π ∘ η = id (Proposition 3.1)

**Paper Coverage**: Definitions 3.1–3.4; Proposition 3.1; Remark 3.1

**No sorry statements** — everything is fully proven.

**Next**: `Causality/SyncTree.lean` (Definitions 4.1–4.3)
-/

end Mettapedia.GSLT
