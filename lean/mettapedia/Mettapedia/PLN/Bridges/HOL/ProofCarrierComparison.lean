import Mettapedia.Logic.HOL.ProofSyntax
import Mettapedia.PLN.Bridges.HOL.ProvenanceSemiringReadout

/-!
# The two proof carriers: `ProofSyntax` dominates, and `DerivationTree` is going

**This module previously argued the opposite, and was wrong.**  It claimed the
two carriers were complementary — that `DerivationTree` supported a context
weakening `ProofSyntax` structurally could not — and used that to refuse a
merge.  The claim was reached by reasoning rather than by searching the tree,
and the tree already refutes it.

`Logic/HOL/ProofSyntaxStructural.lean` defines

```lean
structure OccurrenceMap (source target : List α) where
  index  : Fin source.length → Fin target.length
  get_eq : ∀ i, target.get (index i) = source.get i
```

and with it `ProofSyntax.mono`, together with `prepend`, `castIndices`,
`rename`, `subst`, `mono_erasure`, `rename_erasure`, `mono_nodeCount`,
`rename_nodeCount`, `subst_instantiate` and `subst_weakenHyps`.  So weakening
*is* available on `ProofSyntax`; it simply asks for an occurrence transport
rather than a `Prop`-valued subset, which is the honest hypothesis — a subset
relation does not determine *which* occurrence a repeated formula maps to, and
`OccurrenceMap` says so explicitly.

The earlier impossibility argument was about the unstrengthened hypothesis, and
that much is true.  It was the wrong question.

**And the axiom comparison inverts the old framing.**  Measured:

```
ProofSyntax.mono     → [propext]
DerivationTree.mono  → [propext, Quot.sound]
```

The endpoints of this module are axiom-free only because they are trivial: two
are `rfl` on a `Prop` and one composes existing lemmas.  Every *working*
operation on `DerivationTree` carries strictly more than its `ProofSyntax`
counterpart.  On the metric this module used to cite in `DerivationTree`'s
favour, `DerivationTree` loses.

## What remains here, and for how long

`ProofSyntax.toDerivationTree` below is retained as the **migration bridge**
while the provenance readout is re-derived over `ProofSyntax`.  Once that is
done, `DerivationTree` and this module both go.

`erase_toDerivationTree` is proof irrelevance and was never evidence of
anything; it is kept only to record that the bridge does not disturb erasure.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-! ## The forgetful map -/

namespace ProofSyntax

/-- **Forget which hypothesis was used.**  Every rule other than `hyp` is
carried across unchanged; `hyp` replaces its occurrence index by the membership
fact that index witnesses. -/
def toDerivationTree {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {φ : Formula Const Γ} : ProofSyntax Const Δ φ → DerivationTree Const Δ φ
  | .hyp occurrence => .hyp (List.get_mem _ occurrence)
  | .topI => .topI
  | .botE proof => .botE proof.toDerivationTree
  | .andI left right => .andI left.toDerivationTree right.toDerivationTree
  | .andEL proof => .andEL proof.toDerivationTree
  | .andER proof => .andER proof.toDerivationTree
  | .orIL proof => .orIL proof.toDerivationTree
  | .orIR proof => .orIR proof.toDerivationTree
  | .orE cases left right =>
      .orE cases.toDerivationTree left.toDerivationTree right.toDerivationTree
  | .impI proof => .impI proof.toDerivationTree
  | .impE function argument =>
      .impE function.toDerivationTree argument.toDerivationTree
  | .notI proof => .notI proof.toDerivationTree
  | .notE negative positive =>
      .notE negative.toDerivationTree positive.toDerivationTree
  | .allI proof => .allI proof.toDerivationTree
  | .allE term proof => .allE term proof.toDerivationTree
  | .exI term proof => .exI term proof.toDerivationTree
  | .exE existsProof body =>
      .exE existsProof.toDerivationTree body.toDerivationTree
  | .eqRefl term => .eqRefl term
  | .eqSymm proof => .eqSymm proof.toDerivationTree
  | .eqTrans left right => .eqTrans left.toDerivationTree right.toDerivationTree
  | .eqPropI forward backward =>
      .eqPropI forward.toDerivationTree backward.toDerivationTree
  | .eqPropEL proof => .eqPropEL proof.toDerivationTree
  | .eqPropER proof => .eqPropER proof.toDerivationTree
  | .eqApp term proof => .eqApp term proof.toDerivationTree
  | .eqAppArg function proof => .eqAppArg function proof.toDerivationTree
  | .eqLam proof => .eqLam proof.toDerivationTree
  | .funExt proof => .funExt proof.toDerivationTree
  | .beta term body => .beta term body
  | .eta function => .eta function

/-! ## It commutes with erasure

Both carriers erase into the same `Prop`-valued `ExtDerivation`, and the
triangle commutes.  Since `ExtDerivation` is a `Prop`, this is proof
irrelevance — which is exactly the point: the two carriers disagree only about
data that erasure discards. -/

theorem erase_toDerivationTree {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {φ : Formula Const Γ} (proof : ProofSyntax Const Δ φ) :
    (toDerivationTree proof).erase = proof.erase := rfl

end ProofSyntax

/-! ## They are inhabited on the same judgments -/

/-- **Same theorems, different bookkeeping.**  Each carrier is inhabited
exactly when the underlying derivation exists, so neither proves anything the
other does not. -/
theorem nonempty_proofSyntax_iff_nonempty_derivationTree
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
    Nonempty (ProofSyntax Const Δ φ) ↔ Nonempty (DerivationTree Const Δ φ) :=
  (ProofSyntax.nonempty_iff).trans (DerivationTree.nonempty_iff_extDerivation).symm

/-- And the forgetful map is a direct witness of one direction. -/
theorem nonempty_derivationTree_of_proofSyntax
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (proof : ProofSyntax Const Δ φ) : Nonempty (DerivationTree Const Δ φ) :=
  ⟨ProofSyntax.toDerivationTree proof⟩

/-! ## Controls -/

namespace ProofCarrierComparisonControls

/-- The map does not collapse the calculus: `⊤` is carried to `⊤`. -/
theorem toDerivationTree_topI {Γ : Ctx Base} {Δ : List (Formula Const Γ)} :
    ProofSyntax.toDerivationTree (Const := Const) (Γ := Γ) (Δ := Δ) .topI = .topI := rfl

/-- **The occurrence index really is discarded.**  Two hypothesis proofs that
differ as `ProofSyntax` can become the same `DerivationTree`, because their
membership facts are equal by proof irrelevance.  This is the content of the
asymmetry, not an accident of the definition. -/
theorem hyp_index_forgotten {Γ : Ctx Base} {φ : Formula Const Γ} :
    ProofSyntax.toDerivationTree
        (ProofSyntax.hyp (Const := Const) (Δ := [φ, φ]) ⟨0, by simp⟩)
      = ProofSyntax.toDerivationTree
        (ProofSyntax.hyp (Const := Const) (Δ := [φ, φ]) ⟨1, by simp⟩) := rfl

end ProofCarrierComparisonControls

end Mettapedia.Logic.HOL

#print axioms Mettapedia.Logic.HOL.ProofSyntax.toDerivationTree
#print axioms Mettapedia.Logic.HOL.ProofSyntax.erase_toDerivationTree
#print axioms Mettapedia.Logic.HOL.nonempty_proofSyntax_iff_nonempty_derivationTree
