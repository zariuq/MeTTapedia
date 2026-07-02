/-!
# WorldModel readouts: support orders into evidence carriers

The interface separating logical *support* from graded *evidence*: a support
order `Ω` (Heyting-style truth/derivability), an evidence carrier `Q`
(strengths, provenance values, credal intervals, quantale elements), and a
monotone readout `μ : Ω → Q`.  Completeness-style converses are captured by
order reflection, or — more generally — by a *family* of readouts that jointly
separates the support order.

Design constraints on the evidence carrier `Q`, by stage:
* crisp stage: any preordered carrier suffices (e.g. `ℝ≥0∞` with `≤`);
* provenance stage: a commutative semiring evaluated over proof-relevant
  derivation trees (Boolean evaluation = kernel/axiom ledger, evidence
  evaluation = graded readout of the same derivation);
* evidence stage: an ordered evidence structure whose combination respects the
  support order — `Q` is a view target here, never the primitive truth algebra
  of the logic (making a graded algebra the truth algebra changes the logic
  unless its structural laws are separately validated).
-/

namespace Mettapedia.PLN.WorldModel

universe u v w

/-- A monotone readout from a support order into an evidence carrier. -/
structure WMReadout (Ω : Type u) (Q : Type v)
    (leSupport : Ω → Ω → Prop) (leEvidence : Q → Q → Prop) where
  mu : Ω → Q
  monotone : ∀ {a b : Ω}, leSupport a b → leEvidence (mu a) (mu b)

/-- An order-reflecting readout: evidence comparison recovers support order. -/
structure OrderReflectingWMReadout (Ω : Type u) (Q : Type v)
    (leSupport : Ω → Ω → Prop) (leEvidence : Q → Q → Prop)
    extends WMReadout Ω Q leSupport leEvidence where
  reflects : ∀ {a b : Ω}, leEvidence (mu a) (mu b) → leSupport a b

/-- A family of monotone readouts that jointly separates the support order:
if every readout in the family agrees that `a` has no more evidence than `b`,
then `a` is below `b` in support.  Completeness theorems provide instances. -/
structure SeparatingWMReadouts (I : Type w) (Ω : Type u) (Q : Type v)
    (leSupport : Ω → Ω → Prop) (leEvidence : Q → Q → Prop) where
  mu : I → Ω → Q
  monotone : ∀ (i : I) {a b : Ω}, leSupport a b → leEvidence (mu i a) (mu i b)
  separates : ∀ {a b : Ω}, (∀ i : I, leEvidence (mu i a) (mu i b)) → leSupport a b

/-- An order-reflecting readout yields a one-member separating family. -/
def OrderReflectingWMReadout.toSeparating {Ω : Type u} {Q : Type v}
    {leS : Ω → Ω → Prop} {leE : Q → Q → Prop}
    (r : OrderReflectingWMReadout Ω Q leS leE) :
    SeparatingWMReadouts PUnit Ω Q leS leE where
  mu _ := r.mu
  monotone _ := r.monotone
  separates h := r.reflects (h PUnit.unit)

end Mettapedia.PLN.WorldModel
