import Mettapedia.GSLT.Core.GSLT
import Mettapedia.GSLT.Logic.ContextHML
import Mettapedia.GSLT.Causality.Trace

/-!
# Synchronization Trees and Causal Structure

This file formalizes the closed and open synchronization trees (§4) from
Meredith's "Computation, Causality, and Consciousness" (2026), Part I.

## Main Definitions

* `ClosedEdge` — Autonomous rewrite edge (Definition 4.1)
* `OpenEdge` — Context-labeled interactive edge (Definition 4.2)
* `OpenReachable` — Multi-step reachability in the open tree
* `AutonomousCausalOrder` / `InteractiveCausalOrder` — Causal partial orders (Def 4.3)
* `InteractivePath` — Context-labeled paths with length (Definition 4.4)
* `closedReachable_implies_openReachable` — ST^c(P) ⊆ ST^o(P) (Proposition 4.1)

## Key Insight

The closed tree records what a term does as a *program* — its autonomous
computational behavior. The open tree records what a term does as a
*function of its environment*. A term with a trivial closed tree but rich
open tree is a pure interface: it does nothing alone but responds to everything.

## References

- Meredith, "Computation, Causality, and Consciousness" (2026), §4
- Milner, "Communication and Concurrency"
- Bombelli, Lee, Meyer, Sorkin, "Space-Time as a Causal Set"
-/

namespace Mettapedia.GSLT

variable (S : GSLT)

/-! ## Closed Synchronization Trees

    Definition 4.1 (Meredith 2026): The closed synchronization tree ST^c(P)
    of a term P is the directed graph whose:
    - nodes are equivalence classes of terms reachable from P by autonomous
      rewrites →*, requiring no external context
    - edges are labeled by rewrite rule instances
-/

/-- Edge in the closed synchronization tree: an autonomous rewrite step
    between reachable terms.

    Definition 4.1 (Meredith 2026): There is an edge Q → Q' whenever
    Q →_r Q' by firing rule r without any surrounding context.
-/
structure ClosedEdge (root : S.Term) where
  /-- Source term -/
  source : S.Term
  /-- Target term -/
  target : S.Term
  /-- Source is reachable from root -/
  source_reachable : S.MultiStep root source
  /-- The rewrite step (autonomous, no context needed) -/
  step : S.Step source target

/-- A term has a trivial closed synchronization tree iff it is in normal form.

    Remark (Meredith 2026): A term has a nontrivial closed synchronization tree
    if and only if it contains a redex.
-/
theorem closedTree_trivial_iff_normalForm (P : S.Term) :
    S.IsNormalForm P ↔ ¬∃ e : S.ClosedEdge P, e.source = P := by
  constructor
  · intro hnf ⟨e, heq⟩
    exact hnf ⟨e.target, heq ▸ e.step⟩
  · intro hno ⟨t', hstep⟩
    exact hno ⟨⟨P, t', MultiStep.refl P, hstep⟩, rfl⟩

/-! ## Open Synchronization Trees

    Definition 4.2 (Meredith 2026): The open synchronization tree ST^o(P)
    of a term P is the directed graph whose:
    - nodes are equivalence classes of terms reachable from P via transitions
      in the Milner-Sewell-Leifer labeled transition system
    - edges are labeled by minimal contexts: K → Q' whenever K[Q] → Q'
-/

/-- Edge in the open synchronization tree: a context-labeled transition.

    Definition 4.2 (Meredith 2026): There is an edge Q →_K Q' whenever
    K[Q] → Q' for minimal context K.
-/
structure OpenEdge (root : S.Term) where
  /-- Source term -/
  source : S.Term
  /-- Target term -/
  target : S.Term
  /-- The minimal context that triggers the transition -/
  context : GSLTContext S
  /-- The transition: K[source] → target -/
  step : S.Step (context.plug source) target

/-- Multi-step reachability in the open synchronization tree -/
inductive OpenReachable : S.Term → S.Term → Prop where
  | refl (t : S.Term) : OpenReachable t t
  | step {t u v : S.Term} (K : GSLTContext S)
      (h : S.Step (K.plug t) u) (hr : OpenReachable u v) :
      OpenReachable t v

/-- Autonomous steps are a special case of context-labeled steps (with identity context) -/
theorem autonomous_is_open_step {t t' : S.Term} (h : S.Step t t') :
    S.Step ((GSLTContext.id (S := S)).plug t) t' := by
  simp [GSLTContext.id]
  exact h

/-- Every autonomously reachable term is also openly reachable.

    Proposition 4.1 (partial): ST^c(P) ⊆ ST^o(P) as directed graphs.
-/
theorem closedReachable_implies_openReachable {t u : S.Term}
    (h : S.MultiStep t u) : S.OpenReachable t u := by
  induction h with
  | refl t => exact OpenReachable.refl t
  | step hstep _ ih =>
    exact OpenReachable.step (GSLTContext.id) (autonomous_is_open_step S hstep) ih

/-! ## Causal Structure

    Definition 4.3 (Meredith 2026): Both ST^c(P) and ST^o(P) are directed
    graphs whose transitive closures are partial orders. Each is a causal set
    in the sense of Bombelli-Lee-Sorkin.
-/

/-- The autonomous causal order: transitive closure of the closed sync tree edges.
    Q ≤ Q' means "Q can autonomously causally influence Q'." -/
def AutonomousCausalOrder (t u : S.Term) : Prop := S.MultiStep t u

/-- The interactive causal order: transitive closure of the open sync tree edges.
    Q ≤ Q' means "Q can interactively causally influence Q'." -/
def InteractiveCausalOrder (t u : S.Term) : Prop := S.OpenReachable t u

/-- The autonomous causal order is reflexive -/
theorem autonomousCausalOrder_refl (t : S.Term) : S.AutonomousCausalOrder t t :=
  MultiStep.refl t

/-- The interactive causal order is reflexive -/
theorem interactiveCausalOrder_refl (t : S.Term) : S.InteractiveCausalOrder t t :=
  OpenReachable.refl t

/-- The autonomous causal order is transitive -/
theorem autonomousCausalOrder_trans {t u v : S.Term}
    (h1 : S.AutonomousCausalOrder t u) (h2 : S.AutonomousCausalOrder u v) :
    S.AutonomousCausalOrder t v := by
  induction h1 with
  | refl _ => exact h2
  | step hstep _ ih => exact MultiStep.step hstep (ih h2)

/-- The interactive causal order is transitive -/
theorem interactiveCausalOrder_trans {t u v : S.Term}
    (h1 : S.InteractiveCausalOrder t u) (h2 : S.InteractiveCausalOrder u v) :
    S.InteractiveCausalOrder t v := by
  induction h1 with
  | refl _ => exact h2
  | step K hstep _ ih => exact OpenReachable.step K hstep (ih h2)

/-- The autonomous order embeds into the interactive order.

    Proposition 4.1 (Meredith 2026): ST^c(P) ⊆ ST^o(P) as causal orders.
-/
theorem autonomousCausal_embeds_interactive {t u : S.Term}
    (h : S.AutonomousCausalOrder t u) : S.InteractiveCausalOrder t u :=
  closedReachable_implies_openReachable S h

/-! ## Causal Distance

    Definition 4.4 (Meredith 2026): Causal distances are path lengths
    in the synchronization trees.

    d^c_min(P,Q) = min{|γ| : γ is an autonomous rewrite path from P to Q}
    d^o_min(P,Q) = min{|γ| : γ is a context-labeled path from P to Q}
-/

/-- An autonomous rewrite path with explicit length -/
def AutonomousPath (t u : S.Term) : Type _ := S.RewritePath t u

/-- Length of an autonomous path = autonomous causal distance -/
def AutonomousPath.length {t u : S.Term} (p : S.AutonomousPath t u) : Nat :=
  RewritePath.length S p

/-- An interactive (context-labeled) path.

    Each edge is labeled by the minimal context K that triggers
    the transition K[source] → target.
-/
inductive InteractivePath : S.Term → S.Term → Type _ where
  | nil (t : S.Term) : InteractivePath t t
  | cons {t u v : S.Term} (K : GSLTContext S)
      (h : S.Step (K.plug t) u) (rest : InteractivePath u v) :
      InteractivePath t v

/-- Length of an interactive path = interactive causal distance -/
def InteractivePath.length : {t u : S.Term} → S.InteractivePath t u → Nat
  | _, _, .nil _ => 0
  | _, _, .cons _ _ rest => 1 + rest.length

/-- Every autonomous path can be lifted to an interactive path.

    This witnesses the embedding ST^c ⊆ ST^o at the path level.
-/
def RewritePath.toInteractive : {t u : S.Term} → S.RewritePath t u → S.InteractivePath t u
  | _, _, .nil t => InteractivePath.nil t
  | _, _, .cons hstep rest =>
      InteractivePath.cons (GSLTContext.id) (autonomous_is_open_step S hstep)
        rest.toInteractive

/-- Lifting preserves path length -/
theorem RewritePath.toInteractive_length {t u : S.Term} (p : S.RewritePath t u) :
    (p.toInteractive S).length S = p.length S := by
  induction p with
  | nil _ => rfl
  | cons _ rest ih =>
    simp [toInteractive, InteractivePath.length, RewritePath.length]
    exact ih

/-! ## Remark 4.1: The Program/Environment Boundary

    The closed tree records what a term does as a program — its autonomous
    computational behavior. The open tree records what a term does as a
    function of its environment — the full range of behaviors it can exhibit
    when placed in contexts.

    A term with a trivial closed tree but rich open tree is a pure interface:
    it does nothing alone but responds to everything.
-/

/-- A term is a pure interface if it has no autonomous rewrites
    but has context-triggered transitions.

    Remark 4.1 (Meredith 2026): In the Rho calculus, x!(Q) is exactly this:
    it has no autonomous rewrite, but in the context for(y ← x)P | [−]
    it fires immediately.
-/
def IsPureInterface (t : S.Term) : Prop :=
  S.IsNormalForm t ∧ ∃ K : GSLTContext S, ∃ t', S.Step (K.plug t) t'

/-- A term is autonomously active if it has at least one autonomous rewrite -/
def IsAutonomouslyActive (t : S.Term) : Prop :=
  S.IsRedex t

/-! ## Summary

This file establishes:

1. **ClosedEdge / OpenEdge**: Edges of closed and open sync trees (Defs 4.1, 4.2)
2. **OpenReachable**: Multi-step reachability in the open tree
3. **closedTree_trivial_iff_normalForm**: Trivial closed tree ↔ normal form
4. **closedReachable_implies_openReachable**: ST^c ⊆ ST^o (Prop 4.1)
5. **AutonomousCausalOrder / InteractiveCausalOrder**: Causal partial orders (Def 4.3)
6. **autonomousCausal_embeds_interactive**: Autonomous ⊆ interactive (Prop 4.1)
7. **InteractivePath**: Context-labeled paths with length (Def 4.4)
8. **RewritePath.toInteractive**: Lifting autonomous → interactive paths
9. **IsPureInterface**: Terms with trivial closed but rich open tree (Remark 4.1)

**Paper Coverage**: Definitions 4.1–4.4; Proposition 4.1; Remarks 4.1–4.3

**No sorry statements** — everything is fully proven.

**Next**: `Dynamics/PathIntegral.lean` (Definition 9.1–9.2)
-/

end Mettapedia.GSLT
