/-!
# WorldModel: The Minimal General Interface and Hierarchy

The world-model class hierarchy, from most general to most specialized.

## Hierarchy

```
WorldModel (no laws)
  → MonoidalWorldModel (revision is a monoid)
    → AdditiveWorldModel (in PLNWorldModelGeneric.lean)
    → OverlapWorldModel (explicit overlap correction)
    → TrustGatedWorldModel (source-trust-weighted merge)
    → CoalitionWorldModel (semitopological consensus)
```

See `WorldModelClassWeb.md` for the full design rationale,
probability hypercube connection, and Pearl's SCM mapping.
-/

/-! ## Level 0: Minimal WorldModel (no laws) -/

/-- The minimal world-model interface: three typed operations, no laws.

    The relationship between `extract (revise W₁ W₂) q` and
    the individual extractions is NOT specified — it depends on
    the revision regime (additive, overlap, trust-gated, etc.). -/
class WorldModel (State : Type _) (Query : Type _) (V : Type _) where
  revise : State → State → State
  empty : State
  extract : State → Query → V

/-! ## Level 1: MonoidalWorldModel (revision is a monoid) -/

/-- Revision is associative with a unit (monoid structure). -/
class MonoidalWorldModel (State : Type _) (Query : Type _) (V : Type _)
    extends WorldModel State Query V where
  revise_assoc (a b c : State) : revise (revise a b) c = revise a (revise b c)
  revise_empty_left (a : State) : revise empty a = a
  revise_empty_right (a : State) : revise a empty = a

/-! ## Level 2a: OverlapWorldModel -/

/-- Extraction with explicit overlap/correlation correction.

    `extract(revise(W₁,W₂), q) = combine(extract W₁ q, extract W₂ q, overlap W₁ W₂ q)`

    Probability hypercube vertex: Dempster-Shafer (subadditive). -/
class OverlapWorldModel (State : Type _) (Query : Type _) (V : Type _) (Ov : Type _)
    extends MonoidalWorldModel State Query V where
  overlap : State → State → Query → Ov
  combine : V → V → Ov → V
  extract_revise (W₁ W₂ : State) (q : Query) :
    extract (revise W₁ W₂) q = combine (extract W₁ q) (extract W₂ q) (overlap W₁ W₂ q)

/-! ## Level 2b: TrustGatedWorldModel -/

/-- Revision gated by source trust scores.
    Existing Lean: `FallbackRevision` in the typed realization vocabulary. -/
class TrustGatedWorldModel (State : Type _) (Query : Type _) (V : Type _) (Trust : Type _)
    extends MonoidalWorldModel State Query V where
  trust : State → Trust
  gatedRevise : State → State → State

/-! ## Level 2c: CoalitionWorldModel -/

/-- Revision requiring consensus among coherent coalitions.
    Existing Lean: `Semitopology`, `CoalitionTopology` in PLNSemitopology.lean. -/
class CoalitionWorldModel (State : Type _) (Query : Type _) (V : Type _)
    extends MonoidalWorldModel State Query V where
  actionable : State → State → Prop
  coalitionRevise : (W₁ W₂ : State) → actionable W₁ W₂ → State
