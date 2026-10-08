import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
import Mettapedia.GSLT.Core.LambdaTheoryCategory

/-!
# Lambda Theories: Definition 4.1

Paper-aligned formalization of Definition 4.1 from Stay, Meredith & Wells,
"Generating Hypercubes of Type Systems" (2026).

## Main Definitions

* `LambdaTheory` — CCC + finite limits + object-indexed predicate fibers,
  a distinguished `Pr` object, and a substitution-stable rewrite family.
  Representing that family by a subobject of `Pr × Pr` requires separate data.
* `BaseRewrite` — a base rewrite rule `Γ | ∅ ⊢ L(x̄) ⇝ R(x̄)` (§4.1 ⇝_B)
* `RewriteOp` — a congruence rule `Γ | (∧ pᵢ ⇝ qᵢ) ⊢ f(p̄) ⇝ f(q̄)` (§4.1 ⇝_O)
* `RelyCtx` — a rely context Δ of assumed reductions (§5.2)
* `RewriteJudgment` — the judgment form `Γ | Δ ⊢ p ⇝ q` (§5.2)

## References

- Stay, Meredith & Wells, "Generating Hypercubes of Type Systems" (2026), §4.1, §5.2
-/

namespace Mettapedia.GSLT.Meredith

open _root_.CategoryTheory
open Mettapedia.GSLT.Core

/-! ## Lambda Theory (Definition 4.1) -/

-- Object, hom and predicate universes are inherited independently. Their
-- maximum in the record's sort does not identify the three parameters.
set_option linter.checkUnivs false in

/-- A lambda theory.

    Definition 4.1 (Stay, Meredith & Wells 2026): A lambda theory consists of:
    - A category T with finite limits and a chosen cartesian closed structure;
    - Its subobject fibration π : Sub(T) → T (the ambient logic);
    - A distinguished object Pr ∈ T of programs/processes;
    - A distinguished subobject (⇝) ↪ Pr × Pr: in the internal language,
        `p : Pr, q : Pr ⊢ (p ⇝ q) prop`;
    - A specified family of entailments (base rewrites + rewrite operations).

    This record retains the broader operational interface: `rewriteRel` is a
    relation on morphisms `Γ ⟶ Pr`, stable under precomposition. Stability
    alone does not imply the source's subobject claim. Consumers needing an
    internal reduction predicate must supply a representing mono and prove
    its factorization equivalence separately.
-/
structure LambdaTheory extends LambdaTheoryWithEquality where
  /-- The distinguished object of programs/processes.
      Paper: "a distinguished object Pr ∈ T of programs/processes". -/
  Pr : Obj
  /-- The one-step rewrite relation on generalized process terms.
      A representing subobject is additional structure. -/
  rewriteRel : {Γ : Obj} → (Γ ⟶ Pr) → (Γ ⟶ Pr) → Prop
  /-- Stability of the rewrite relation under substitution.
      If `p ⇝ q` in context Γ and σ : Δ ⟶ Γ, then `σ ≫ p ⇝ σ ≫ q` in Δ.
      This one-way condition is not a subobject representation or a full
      Beck–Chevalley law. -/
  rewriteRel_nat : ∀ {Γ Δ : Obj} (σ : Δ ⟶ Γ) (p q : Γ ⟶ Pr),
      rewriteRel p q → rewriteRel (σ ≫ p) (σ ≫ q)

/-! ## Base Rewrites (§4.1, ⇝_B) -/

/-- A base rewrite in a lambda theory.

    Paper §4.1 (base rewrites ⇝_B): A base rewrite has the schematic form
        x₁ : X₁, ..., xₙ : Xₙ | ∅ ⊢ L(x̄) ⇝ R(x̄)
    with Γ ⊢ L(x̄) : Pr and Γ ⊢ R(x̄) : Pr.

    Categorically: a pair of morphisms `lhs, rhs : ctx ⟶ Pr` in T together
    with a proof that the rewrite fires: `rewriteRel lhs rhs`.
-/
structure BaseRewrite (T : LambdaTheory) where
  /-- The variable context Γ = X₁ × ⋯ × Xₙ -/
  ctx : T.Obj
  /-- The left-hand side L(x̄) -/
  lhs : ctx ⟶ T.Pr
  /-- The right-hand side R(x̄) -/
  rhs : ctx ⟶ T.Pr
  /-- The base rewrite fires: ctx | ∅ ⊢ L(x̄) ⇝ R(x̄) -/
  fires : T.rewriteRel lhs rhs

/-! ## Rewrite Operations (§4.1, ⇝_O) -/

/-- A rewrite operation in a lambda theory.

    Paper §4.1 (rewrite operations ⇝_O): A rewrite operation has the schematic form
        Γ | (∧ᵢ∈I pᵢ ⇝ qᵢ) ⊢ f(p̄) ⇝ f(q̄)
    where f ranges over operations in the presentation, and I ⊆ {1,...,n} is a
    designated set of "active" argument positions.

    We abstract over the arity: `op` is a natural map on morphism-vectors into Pr.
    Congruence and naturality are required.
-/
structure RewriteOp (T : LambdaTheory) (n : ℕ) where
  /-- The n-ary operation: maps n process terms in context Γ to one process term.
      Naturality (over Γ) is expressed by `op_nat`. -/
  op : {Γ : T.Obj} → (Fin n → (Γ ⟶ T.Pr)) → (Γ ⟶ T.Pr)
  /-- The active argument positions: positions where congruence rewriting fires. -/
  activePos : Finset (Fin n)
  /-- Congruence: if pᵢ ⇝ qᵢ for all active i, then op(p̄) ⇝ op(q̄).
      Paper: "Γ | (∧ᵢ pᵢ ⇝ qᵢ) ⊢ f(p̄) ⇝ f(q̄)". -/
  congruence : ∀ {Γ : T.Obj} (ps qs : Fin n → (Γ ⟶ T.Pr)),
      (∀ i ∈ activePos, T.rewriteRel (ps i) (qs i)) →
      T.rewriteRel (op ps) (op qs)
  /-- Naturality: the operation commutes with precomposition. -/
  op_nat : ∀ {Γ Δ : T.Obj} (σ : Δ ⟶ Γ) (ps : Fin n → (Γ ⟶ T.Pr)),
      op (fun i => σ ≫ ps i) = σ ≫ op ps

/-! ## Rely Context (§5.2) -/

/-- A rely context Δ in context Γ: a list of assumed reductions pᵢ ⇝ qᵢ.

    Paper §5.2: "Γ | Δ ⊢ ψ, where Δ lists assumed propositions (including
    typing assumptions t :: A and reduction assumptions p ⇝ q)."

    Here we specialize to reduction assumptions only.
    Each element (p, q) of `assumptions` asserts `p ⇝ q` as a hypothesis.
-/
structure RelyCtx (T : LambdaTheory) (Γ : T.Obj) where
  /-- The list of assumed reductions: (pᵢ, qᵢ) means "pᵢ ⇝ qᵢ is assumed". -/
  assumptions : List ((Γ ⟶ T.Pr) × (Γ ⟶ T.Pr))

/-- The empty rely context. -/
def RelyCtx.empty (T : LambdaTheory) (Γ : T.Obj) : RelyCtx T Γ where
  assumptions := []

/-! ## The Judgment Form (§5.2) -/

/-- The rewrite judgment `Γ | Δ ⊢ p ⇝ q`.

    Paper §5.2: "We work with judgments Γ | Δ ⊢ ψ, where Γ declares variables
    and their carriers, Δ lists assumed propositions, and ψ is the conclusion."
    Here ψ = (p ⇝ q), specialized to one-step rewrite conclusions.

    The judgment is defined inductively, closed under:
    - **Base**: fires a base rewrite in any rely context;
    - **Rely**: uses an assumption from Δ directly;
    - **Subst**: stable under precomposition (substitution into context).
-/
inductive RewriteJudgment (T : LambdaTheory) :
    (Γ : T.Obj) → RelyCtx T Γ → (Γ ⟶ T.Pr) → (Γ ⟶ T.Pr) → Prop where
  /-- A base rewrite fires in any context under any rely context.
      Paper §4.1 ⇝_B: "x₁:X₁,...,xₙ:Xₙ | ∅ ⊢ L(x̄) ⇝ R(x̄)". -/
  | base (br : BaseRewrite T) (Δ : RelyCtx T br.ctx) :
      RewriteJudgment T br.ctx Δ br.lhs br.rhs
  /-- A reduction assumed in Δ is immediately derivable.
      Paper §5.2: Δ lists assumed reductions that may be used freely. -/
  | rely {Γ : T.Obj} {Δ : RelyCtx T Γ} {p q : Γ ⟶ T.Pr}
      (hmem : (p, q) ∈ Δ.assumptions) :
      RewriteJudgment T Γ Δ p q
  /-- Stability under substitution (precomposition).
      Paper §4.1: rewrite operations express congruence / closure under term formers. -/
  | subst {Γ Δ' : T.Obj} {Δ : RelyCtx T Γ} {p q : Γ ⟶ T.Pr}
      (σ : Δ' ⟶ Γ)
      (hpq : RewriteJudgment T Γ Δ p q) :
      RewriteJudgment T Δ' (RelyCtx.empty T Δ') (σ ≫ p) (σ ≫ q)

end Mettapedia.GSLT.Meredith
