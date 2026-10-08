import Foundation.Propositional.Kripke.Logic.Int
import Mettapedia.Logic.HostingStyles.Intuitionistic
import Mettapedia.Logic.HostingStyles.Shallow

/-!
# The worked logic, shallowly: two semantic embeddings

Two shallow semantic embeddings of the intuitionistic Hilbert calculus, both
built from semantics that already exist.

## The Kripke embedding

A formula denotes its truth at a world of a Kripke model, in Foundation's
Kripke semantics of intuitionistic propositional logic: implication looks at
all later worlds.

* Every rule preserves truth at each world (`kripke_locallySound`), so the
  calculus maps into the theory of this semantics (`kripkeMap`).
* The embedding is faithful: a formula has a derivation exactly when it is
  true at every world of every model (`kripke_faithful`).  Completeness is
  Foundation's.
* Every entailment of the host comes from a derived rule
  (`kripke_stronglyComplete`), so the map is exhausting
  (`kripkeMap_exhausting`).
* It is hosting for the provability collapse (`kripkeMap_hosting_total`) and
  not when derivations are kept apart (`kripkeMap_not_hosting`): the two
  derivations of `φ ➝ φ` become one host proof.

## The truth-table embedding, and host leakage

A formula denotes its truth value under a valuation of the atoms, with
implication read as the host's own.  The host is classical.

* Every rule preserves truth (`truthTable_locallySound`), so this too is a
  map of theories (`truthTableMap`), and it is hosting for the provability
  collapse (`truthTableMap_hosting_total`).
* It validates Peirce's law (`truthTable_peirce`), which the Kripke embedding
  refutes at a world of a two-world model (`kripke_not_peirce`), so Peirce's
  law has no derivation (`peirce_underivable`).
* The truth-table embedding is therefore not faithful and not exhausting
  (`truthTableMap_not_exhausting`): the host holds a term, the truth of
  Peirce's law, that no derivation reaches.  That is host leakage: the logic
  of the host shows through an embedding that reads an object connective as
  the host's own.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles

open LO LO.Propositional
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.GSLT
open Mettapedia.Logic.ModalCompanion

/-! ## The Kripke embedding -/

/-- A point of evaluation: a world of a Kripke model. -/
abbrev KripkePoint : Type 1 := Σ model : Kripke.Model, model.World

/-- The Kripke embedding: a formula denotes its truth at a world. -/
def kripkeHolds (point : KripkePoint) (φ : IntFormula) : Prop :=
  Formula.Kripke.Satisfies point.1 point.2 φ

/-- **Every rule preserves truth at each world.** -/
theorem kripke_locallySound : LocallySound kripkeHolds intSignature := by
  intro conclusion rule point premises
  cases rule with
  | axm instance' =>
      cases instance' with
      | efq φ => exact Formula.Kripke.ValidOnModel.efq point.2
      | implyK φ ψ => exact Formula.Kripke.ValidOnModel.implyK point.2
      | implyS φ ψ χ => exact Formula.Kripke.ValidOnModel.implyS point.2
      | andElimL φ ψ => exact Formula.Kripke.ValidOnModel.andElim₁ point.2
      | andElimR φ ψ => exact Formula.Kripke.ValidOnModel.andElim₂ point.2
      | andIntro φ ψ => exact Formula.Kripke.ValidOnModel.andInst₃ point.2
      | orIntroL φ ψ => exact Formula.Kripke.ValidOnModel.orInst₁ point.2
      | orIntroR φ ψ => exact Formula.Kripke.ValidOnModel.orInst₂ point.2
      | orElim φ ψ χ => exact Formula.Kripke.ValidOnModel.orElim point.2
  | mdp antecedent =>
      have major : Formula.Kripke.Satisfies point.1 point.2 (antecedent ➝ conclusion) :=
        premises false
      have minor : Formula.Kripke.Satisfies point.1 point.2 antecedent := premises true
      exact major point.1.refl minor

/-- **Completeness**, from Foundation's Kripke completeness of intuitionistic
propositional logic. -/
theorem kripke_complete : Complete kripkeHolds intSignature := by
  intro φ valid
  refine (nonempty_proof_iff_provable φ).mpr ?_
  exact LO.Complete.complete (𝓜 := Kripke.FrameClass.Int)
    (fun frame _ valuation world => valid ⟨⟨frame, valuation⟩, world⟩)

/-- **The Kripke embedding is faithful**: derivable exactly when true at
every world of every model. -/
theorem kripke_faithful (φ : IntFormula) : Nonempty (IntProof φ) ↔ Valid kripkeHolds φ :=
  derivable_iff_valid kripke_locallySound kripke_complete φ

/-! ### Entailments come from derived rules -/

/-- The implication from a list of assumptions to a conclusion. -/
def impliesFrom {arity : Type} (assumptions : arity → IntFormula) :
    List arity → IntFormula → IntFormula
  | [], conclusion => conclusion
  | index :: rest, conclusion => assumptions index ➝ impliesFrom assumptions rest conclusion

/-- If the conclusion is true wherever the listed assumptions are, at and
after a world, the implication from them is true at that world. -/
theorem satisfies_impliesFrom {arity : Type} (assumptions : arity → IntFormula)
    (model : Kripke.Model) (conclusion : IntFormula) :
    ∀ (support : List arity) (world : model.World),
      (∀ later : model.World, world ≺ later →
        (∀ index ∈ support, Formula.Kripke.Satisfies model later (assumptions index)) →
          Formula.Kripke.Satisfies model later conclusion) →
        Formula.Kripke.Satisfies model world (impliesFrom assumptions support conclusion)
  | [], world, follows => follows world model.refl fun _ member => absurd member List.not_mem_nil
  | index :: rest, world, follows => by
      intro reach holds
      rename_i later
      refine satisfies_impliesFrom assumptions model conclusion rest later ?_
      intro latest reach' others
      refine follows latest (model.trans reach reach') ?_
      intro other member
      rcases List.mem_cons.mp member with same | member
      · subst same
        exact Formula.Kripke.Satisfies.formula_hereditary reach' holds
      · exact others other member

/-- Modus ponens on derived rules. -/
def openMdp {arity : Type} {assumptions : arity → IntFormula} {φ ψ : IntFormula}
    (major : intSignature.Open assumptions (φ ➝ ψ)) (minor : intSignature.Open assumptions φ) :
    intSignature.Open assumptions ψ :=
  Free.node intSignature (.mdp φ ψ) fun position =>
    match position with
    | false => major
    | true => minor

/-- A derived rule of the implication from a list of assumptions gives a
derived rule of the conclusion from those assumptions. -/
noncomputable def dischargeAll {arity : Type} (assumptions : arity → IntFormula)
    (conclusion : IntFormula) : (support : List arity) →
    intSignature.Open assumptions (impliesFrom assumptions support conclusion) →
      intSignature.Open assumptions conclusion
  | [], context => context
  | index :: rest, context =>
      dischargeAll assumptions conclusion rest (openMdp context (intSignature.assume index))

/-- **Every entailment of the Kripke embedding comes from a derived rule.** -/
theorem kripke_stronglyComplete : StronglyComplete kripkeHolds intSignature := by
  intro arity assumptions conclusion entails
  obtain ⟨support, follows⟩ := entails
  have valid : Valid kripkeHolds (impliesFrom assumptions support conclusion) := fun point =>
    satisfies_impliesFrom assumptions point.1 conclusion support point.2
      fun later _ holds => follows ⟨point.1, later⟩ holds
  obtain ⟨proof⟩ := kripke_complete _ valid
  exact ⟨dischargeAll assumptions conclusion support (intSignature.close proof)⟩

/-- **The Kripke embedding, as a map of theories.** -/
noncomputable def kripkeMap (congruence : intSignature.ProofCongruence) :
    ContextMap (intSignature.proofTheory congruence) (shallowTheory kripkeHolds) :=
  shallowMap kripke_locallySound intFinitary congruence

/-- The Kripke embedding is exhausting: the host adds no entailment. -/
theorem kripkeMap_exhausting (congruence : intSignature.ProofCongruence) :
    (kripkeMap congruence).Exhausting :=
  (shallowMap_exhausting_iff kripke_locallySound intFinitary congruence).mpr
    kripke_stronglyComplete

/-- The Kripke embedding is hosting for the provability collapse. -/
theorem kripkeMap_hosting_total :
    (kripkeMap (RuleSignature.ProofCongruence.total intSignature)).Hosting :=
  shallowMap_hosting_total kripke_locallySound intFinitary

/-- **The Kripke embedding is not hosting when derivations are kept apart**:
the two derivations of `φ ➝ φ` become one host proof. -/
theorem kripkeMap_not_hosting :
    ¬ (kripkeMap (RuleSignature.ProofCongruence.identity intSignature)).Hosting :=
  shallowMap_not_hosting kripke_locallySound intFinitary _
    (identityProof_ne_detourProof (.atom 0))

/-! ## Peirce's law -/

/-- Peirce's law on the first two atoms. -/
def peirce : IntFormula := Axioms.Peirce (.atom 0) (.atom 1)

/-- The two-world frame: one world before another. -/
def twoWorldFrame : Kripke.Frame where
  World := Bool
  Rel := fun first second => first ≤ second

/-- On the two-world frame, the first atom holds at the later world only and
the second atom nowhere. -/
def twoWorldModel : Kripke.Model where
  toFrame := twoWorldFrame
  Val := ⟨fun atom world => atom = 0 ∧ world = true, by
    rintro first second reach atom ⟨zero, later⟩
    subst later
    exact ⟨zero, top_le_iff.mp reach⟩⟩

/-- **The Kripke embedding refutes Peirce's law** at the earlier world. -/
theorem kripke_not_peirce : ¬ kripkeHolds ⟨twoWorldModel, false⟩ peirce := by
  intro holds
  have antecedent : Formula.Kripke.Satisfies twoWorldModel false
      ((.atom 0 ➝ .atom 1) ➝ .atom 0) := by
    intro world _ implication
    have second : Formula.Kripke.Satisfies twoWorldModel true (.atom 1) :=
      implication (w' := true) (Bool.le_true world) ⟨rfl, rfl⟩
    exact absurd second.1 (by decide)
  have first : Formula.Kripke.Satisfies twoWorldModel false (.atom 0) :=
    holds (w' := false) twoWorldModel.refl antecedent
  exact Bool.false_ne_true first.2

/-- **Peirce's law has no derivation.**  Independence by a countermodel
needs soundness only. -/
theorem peirce_underivable : IsEmpty (IntProof peirce) :=
  isEmpty_proof_of_countermodel kripke_locallySound kripke_not_peirce

/-! ## The truth-table embedding -/

/-- The truth-table embedding: a formula denotes its truth value under a
valuation of the atoms. -/
def truthTableHolds (valuation : ℕ → Bool) (φ : IntFormula) : Prop :=
  ttVal valuation φ = true

/-- Every rule preserves truth values. -/
theorem truthTable_locallySound : LocallySound truthTableHolds intSignature := by
  intro conclusion rule valuation premises
  cases rule with
  | axm instance' =>
      exact PropDeriv.ttVal_sound valuation (fun _ member => absurd member List.not_mem_nil)
        instance'.toDeriv
  | mdp antecedent =>
      have major : ttVal valuation (antecedent ➝ conclusion) = true := premises false
      have minor : ttVal valuation antecedent = true := premises true
      rw [ttVal_imp, minor] at major
      exact major

/-- **The truth-table embedding validates Peirce's law.** -/
theorem truthTable_peirce : Valid truthTableHolds peirce := by
  intro valuation
  change ttVal valuation (((.atom 0 ➝ .atom 1) ➝ .atom 0) ➝ .atom 0) = true
  simp only [ttVal_imp, ttVal_atom]
  cases valuation 0 <;> cases valuation 1 <;> rfl

/-- The truth-table embedding, as a map of theories. -/
noncomputable def truthTableMap (congruence : intSignature.ProofCongruence) :
    ContextMap (intSignature.proofTheory congruence) (shallowTheory truthTableHolds) :=
  shallowMap truthTable_locallySound intFinitary congruence

/-- The truth-table embedding is hosting for the provability collapse. -/
theorem truthTableMap_hosting_total :
    (truthTableMap (RuleSignature.ProofCongruence.total intSignature)).Hosting :=
  shallowMap_hosting_total truthTable_locallySound intFinitary

/-- **Host leakage**: the truth-table embedding is not exhausting.  The
classical host holds the truth of Peirce's law, which no derivation
reaches. -/
theorem truthTableMap_not_exhausting (congruence : intSignature.ProofCongruence) :
    ¬ (truthTableMap congruence).Exhausting :=
  not_exhausting_of_valid_underivable truthTable_locallySound intFinitary congruence
    truthTable_peirce peirce_underivable

/-- The truth-table embedding is sound and not faithful. -/
theorem truthTable_not_faithful :
    Valid truthTableHolds peirce ∧ ¬ Nonempty (IntProof peirce) :=
  ⟨truthTable_peirce, fun ⟨proof⟩ => peirce_underivable.false proof⟩

#print axioms kripke_faithful
#print axioms kripke_stronglyComplete
#print axioms kripkeMap_exhausting
#print axioms kripkeMap_not_hosting
#print axioms kripke_not_peirce
#print axioms peirce_underivable
#print axioms truthTable_peirce
#print axioms truthTableMap_not_exhausting

end Mettapedia.Logic.HostingStyles
