import Mettapedia.GSLT.Meredith.Modal.RewriteModality

/-!
# Empty-Context Possibility ♢: §5.5 of "Generating Hypercubes of Type Systems"

Formalization of the empty-context possibility operator `♢`, which provides a
rewrite-stable, weakened form of the conversion principle.

## Main Definitions

* `DiamondType` — the ♢B type former: "p can step to some reduct of type B"
* `DiamondIntro` — introduction from a concrete step and typing (♢-Intro)
* `DiamondElim` — existential elimination (♢-Elim)
* `LaxConversion` — the derived M-Elim⇝,♢ rule combining M-Step + ♢-Intro

## Key Insight (§5.5)

Rewrite-generated modalities do NOT support full conversion (unlike equation
modalities that yield Π). The ♢ operator provides a weakened substitute:

  `p :: ♢B` iff `∃ q. (p ⇝ q) ∧ (q :: B)`

This is "rely-possibly" without a specific context — just bare one-step reachability
to a well-typed reduct.

## The Derived Lax Conversion (§5.5.4)

Combining M-Step and ♢-Intro yields:
```
  Γ Δ ⊢ t :: ⟨K_j⟩_{x̄::Ā} B    Γ Δ ⊢ u_k :: A_k
  ────────────────────────────────────────────────────
  Γ Δ ⊢ K_j[t][ū/x̄] :: ♢(B[ū/x̄])
```

This is the promised weakened conversion: the redex-in-context is typed at
`♢(B[ū/x̄])`, reflecting that it *can* take one step to a term of type B[ū/x̄].

## References

- Stay, Meredith & Wells, "Generating Hypercubes of Type Systems" (2026), §5.5
-/

namespace Mettapedia.GSLT.Meredith.Modal

open Mettapedia.GSLT.Meredith
open Mettapedia.OSLF.Framework.ModalHypercube

/-! ## ♢ Type Former (§5.5) -/

/-- The empty-context possibility type ♢B at carrier Pr.

    §5.5: "p :: ♢B asserts that p can take one step to some reduct of type B."

    Semantically (§5.5, when ∃ is available):
      `p :: ♢B ≡ ∃ q : Pr. (p ⇝ q) ∧ (q :: B)`

    We represent ♢B abstractly as a type former parameterized by a
    "postcondition" (type predicate B) at carrier Pr.
-/
structure DiamondType (T : LambdaTheory) where
  /-- The postcondition predicate B on Pr terms.
      In the full system this would be a type former at carrier Pr. -/
  postcondition : (∀ {Γ : T.Obj}, (Γ ⟶ T.Pr) → Prop)

/-! ## ♢-Form (§5.5.1)

    ```
    Γ Δ ⊢ B :: s^Pr
    ─────────────────
    Γ Δ ⊢ ♢B :: s^Pr
    ```

    The current `DiamondType` encoding records only the postcondition on
    reducts. It does not yet internalize the surrounding sort judgment, so the
    paper's sort-preservation rule is intentionally not packaged here as a
    theorem with a misleading vacuous statement.
-/

/-! ## ♢-Intro (§5.5.2)

    ```
    Γ Δ ⊢ p ⇝ q    Γ Δ ⊢ q :: B
    ──────────────────────────────
    Γ Δ ⊢ p :: ♢B
    ```
-/

/-- A witness for ♢-introduction: a concrete reduct and its typing. -/
structure DiamondIntroWitness (T : LambdaTheory) (d : DiamondType T)
    {Γ : T.Obj} (p : Γ ⟶ T.Pr) where
  /-- The concrete reduct q with p ⇝ q. -/
  reduct : Γ ⟶ T.Pr
  /-- The operational step: p ⇝ q. -/
  steps : T.rewriteRel p reduct
  /-- The reduct satisfies the postcondition: q :: B. -/
  typed : d.postcondition reduct

/-- ♢-Intro: from a step and typing, conclude membership in ♢B.

    §5.5.2: "If p ⇝ q and q :: B, then p :: ♢B."
-/
def diamondIntro (T : LambdaTheory) (d : DiamondType T)
    {Γ : T.Obj} {p : Γ ⟶ T.Pr}
    (w : DiamondIntroWitness T d p) : DiamondIntroWitness T d p := w

/-! ## ♢-Elim (§5.5.3)

    ```
    Γ Δ ⊢ p :: ♢B    Γ, q : Pr  Δ, (p ⇝ q), (q :: B) ⊢ φ
    ─────────────────────────────────────────────────────────
    Γ Δ ⊢ φ                                      (q ∉ FV(φ))
    ```

    This is existential elimination: given that p has a one-step reduct
    of type B, and given that any such reduct implies φ, conclude φ.
-/

/-- ♢-Elim: existential elimination for ♢.

    §5.5.3: From `p :: ♢B` and a proof that any witness implies `φ`,
    conclude `φ`. The bound variable `q` must not appear free in `φ`.
-/
theorem diamondElim (T : LambdaTheory) (d : DiamondType T)
    {Γ : T.Obj} {p : Γ ⟶ T.Pr} {φ : Prop}
    (w : DiamondIntroWitness T d p)
    (elim : ∀ (q : Γ ⟶ T.Pr), T.rewriteRel p q → d.postcondition q → φ) : φ :=
  elim w.reduct w.steps w.typed

/-! ## Derived Lax Conversion (§5.5.4)

    Combining M-Step (§5.4.3) and ♢-Intro (§5.5.2) yields the key rule:

    ```
    Γ Δ ⊢ t :: ⟨K_j⟩_{x̄::Ā} B    Γ Δ ⊢ u_k :: A_k
    ────────────────────────────────────────────────────
    Γ Δ ⊢ K_j[t][ū/x̄] :: ♢(B[ū/x̄])
    ```

    This is the promised **weakened conversion principle**: the redex-in-context
    is typed at ♢(B[ū/x̄]), reflecting that it can take one step to a term of
    type B[ū/x̄].
-/

/-- Lax conversion: from a modal type and rely instances, derive ♢-membership.

    §5.5.4 (M-Elim⇝,♢): The redex-in-context K_j[t][ū/x̄] has type ♢(B[ū/x̄]).

    This is the composition: M-Step gives the operational step, then ♢-Intro
    packages it with the typing from M-Elim⇝.
-/
def laxConversion (T : LambdaTheory) (br : BaseRewrite T)
    (pos : RedexPosition T br)
    (postcond : ∀ {Γ : T.Obj}, (Γ ⟶ T.Pr) → Prop)
    (rhs_typed : postcond br.rhs) :
    DiamondIntroWitness T ⟨postcond⟩ (pos.fillContext pos.subterm) where
  reduct := br.rhs
  steps := pos.fills ▸ br.fires
  typed := rhs_typed

/-! ## Modal Cut Elimination (§5.9)

    "Normalizing an introduction-followed-by-elimination detour corresponds
    precisely to firing the underlying rewrite at the chosen redex position."

    A modal cut redex is: M-Intro followed by M-Elim⇝,♢ followed by ♢-Elim.
    Cut elimination inlines the concrete reduct, which operationally fires the
    one-step rewrite.

    For the ρ-calculus: reduction is nondeterministic (parallel composition
    introduces races), so modal cut elimination is NOT confluent (§5.9).
-/

/-- Modal cut elimination: intro followed by elim reduces to the direct step.

    §5.9: "normalizing an introduction-followed-by-elimination detour
    corresponds precisely to firing the underlying rewrite."
-/
theorem modalCutElim (T : LambdaTheory) (br : BaseRewrite T)
    (pos : RedexPosition T br)
    (postcond : ∀ {Γ : T.Obj}, (Γ ⟶ T.Pr) → Prop)
    (rhs_typed : postcond br.rhs)
    {φ : Prop}
    (use : ∀ (q : br.ctx ⟶ T.Pr), T.rewriteRel (pos.fillContext pos.subterm) q →
           postcond q → φ) : φ :=
  let w := laxConversion T br pos postcond rhs_typed
  diamondElim T ⟨postcond⟩ w use

end Mettapedia.GSLT.Meredith.Modal
