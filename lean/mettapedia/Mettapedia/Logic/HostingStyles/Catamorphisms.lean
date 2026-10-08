import Mettapedia.GSLT.Logic.PrivilegedView
import Mettapedia.Logic.HostingStyles.Observers

/-!
# The three hostings as folds, and what is final

## Folds

The derivations of a rule signature are the initial algebra of the signature
(`Mettapedia.TypeTheory.IndexedPolynomial.Algebra.initial`), and a map out of
them that commutes with the rules is the fold into its target algebra
(`Algebra.hom_eq_fold`, restated as `fold_unique`).  A translation is a fold
under three conditions, each of which is used:

* the source syntax is free: here, the derivations of a rule signature;
* the target algebra is fixed: the operation that each rule becomes;
* if the source is taken up to an equivalence, the target respects it: a fold
  factors through the quotient of derivations by a congruence exactly when it
  identifies congruent derivations (`fold_factors_quotient_iff`), and then in
  exactly one way (`fold_descends_unique`).

A hosting is an algebra of the rule signature.

* **Shallow semantic.**  Truth at every point is an algebra when every rule
  preserves truth at each point (`validityAlgebra`); its fold is soundness
  (`fold_validityAlgebra`).  Validity is then a predicate closed under the
  rules (`valid_ruleClosed`); derivability is the least such predicate
  (`derivable_least`); and the embedding is faithful exactly when validity is
  the least one (`faithful_iff_least`).  Soundness alone does not make
  validity closed under the rules (`gap_sound`, `gap_not_ruleClosed`).
* **Judgments as types.**  The terms of the framework are an algebra
  (`RuleSignature.Finitary.termAlgebra`) and encoding is its fold; adequacy
  says that this fold is a bijection onto canonical forms and a bijection up
  to conversion (`RuleSignature.Finitary.canonicalEquiv`,
  `RuleSignature.Finitary.adequacy`).

**The chain from initiality.**  A fold composed with a homomorphism of
algebras is the fold into the target (`fold_comp_hom`).  Reading framework
terms as truths is a homomorphism from the algebra of terms to the algebra of
validity (`termToValidity`), so soundness is encoding followed by that
reading (`soundness_factors_through_encoding`).

**Three levels.**  Folds out of derivations are classified by the congruence
they respect: every fold respects equality (`fold_factors_identity`); a fold
into a family of propositions respects the total congruence
(`fold_factors_total_of_subsingleton`); the size of a derivation does not
(`size_not_factors_total`).  The quotient by the total congruence is
provability: it is inhabited exactly when the judgment has a derivation and
has at most one element (`total_quotient_nonempty_iff`,
`total_quotient_subsingleton`).

## What is final

The algebra with one element at each judgment receives exactly one
homomorphism from every algebra (`hom_to_unit_unique`) and observes nothing.
Validity is not that algebra unless every judgment is valid
(`not_hom_unit_validity`).

The observer that is characterized by a universal property on the *coarse*
side is found among behaviours, not among algebras.  Let a claim be used by
plugging its derivation into a derived rule with one assumption (`use`).  A
view of claims is stable when claims it identifies stay identified under
every use.  For the purpose of seeing which judgment is claimed, the judgment
itself is the word behaviour of `Mettapedia.GSLT.PrivilegedView`
(`judgment_eq_iff_wordBehaviour`): the coarsest stable view that keeps the
judgment, through which every other such view factors
(`wordBehaviour_factors_stable`).  For the purpose of seeing the derivation,
the word behaviour keeps every claim apart (`wordBehaviour_claim_injective`).
So the native observer is initial, as syntax; the provability observer is
final, as the behaviour for its purpose.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles

open LO
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.GSLT
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.GSLT.PrivilegedView
open Framework

universe v

namespace RuleSignature

variable {J : Type} (P : RuleSignature J)

/-! ## Folds out of derivations -/

/-- **A map out of derivations that commutes with the rules is the fold.** -/
theorem fold_unique {carrier : PUnit.{1} → J → Type} (algebra : P.Algebra carrier)
    (candidate : (j : J) → P.Proof j → carrier PUnit.unit j)
    (commutes : ∀ {j : J} (shape : P.Shape PUnit.unit j)
      (children : (position : P.Position shape) → P.Proof (P.next shape position)),
      candidate j (P.node shape children) =
        algebra.act PUnit.unit j ⟨shape, fun position => candidate _ (children position)⟩)
    {j : J} (proof : P.Proof j) :
    candidate j proof = Fix.fold P algebra.act PUnit.unit j proof :=
  Algebra.hom_eq_fold algebra
    { toFun := fun _ j proof => candidate j proof
      commutes := fun _ _ layer => commutes layer.1 layer.2 } PUnit.unit j proof

/-- **A fold followed by a homomorphism is the fold into the target.** -/
theorem fold_comp_hom {first second : PUnit.{1} → J → Type} (firstAlgebra : P.Algebra first)
    (secondAlgebra : P.Algebra second) (hom : Algebra.Hom firstAlgebra secondAlgebra) {j : J}
    (proof : P.Proof j) :
    hom.toFun PUnit.unit j (Fix.fold P firstAlgebra.act PUnit.unit j proof) =
      Fix.fold P secondAlgebra.act PUnit.unit j proof :=
  P.fold_unique secondAlgebra
    (fun j proof => hom.toFun PUnit.unit j (Fix.fold P firstAlgebra.act PUnit.unit j proof))
    (fun shape children => hom.commutes PUnit.unit _
      ⟨shape, fun position => Fix.fold P firstAlgebra.act PUnit.unit _ (children position)⟩) proof

/-- **A fold factors through the quotient by a congruence exactly when it
identifies congruent derivations.** -/
theorem fold_factors_quotient_iff (congruence : P.ProofCongruence)
    {carrier : PUnit.{1} → J → Type} (algebra : P.Algebra carrier) (j : J) :
    Factors (fun proof : P.Proof j => Quotient.mk (congruence.setoid j) proof)
        (Fix.fold P algebra.act PUnit.unit j) ↔
      ∀ first second : P.Proof j, (congruence.setoid j).r first second →
        Fix.fold P algebra.act PUnit.unit j first = Fix.fold P algebra.act PUnit.unit j second := by
  constructor
  · intro factors first second related
    exact factors.constantOnFibers first second (Quotient.sound related)
  · intro respects
    exact ⟨Quotient.lift (Fix.fold P algebra.act PUnit.unit j) respects, fun _ => rfl⟩

/-- When a fold respects a congruence, it descends to the quotient in exactly
one way. -/
theorem fold_descends_unique (congruence : P.ProofCongruence)
    {carrier : PUnit.{1} → J → Type} (algebra : P.Algebra carrier) (j : J)
    (respects : ∀ first second : P.Proof j, (congruence.setoid j).r first second →
      Fix.fold P algebra.act PUnit.unit j first = Fix.fold P algebra.act PUnit.unit j second) :
    ∃! descended : Quotient (congruence.setoid j) → carrier PUnit.unit j,
      ∀ proof, descended (Quotient.mk _ proof) = Fix.fold P algebra.act PUnit.unit j proof := by
  refine ⟨Quotient.lift (Fix.fold P algebra.act PUnit.unit j) respects, fun _ => rfl, ?_⟩
  intro other agrees
  funext value
  induction value using Quotient.inductionOn with
  | _ proof => exact agrees proof

/-- Every fold respects equality of derivations. -/
theorem fold_factors_identity {carrier : PUnit.{1} → J → Type} (algebra : P.Algebra carrier)
    (j : J) :
    Factors (fun proof : P.Proof j => Quotient.mk ((ProofCongruence.identity P).setoid j) proof)
      (Fix.fold P algebra.act PUnit.unit j) :=
  (P.fold_factors_quotient_iff _ algebra j).mpr fun _ _ same => congrArg _ same

/-- A fold into a family with at most one element at each judgment respects
the total congruence. -/
theorem fold_factors_total_of_subsingleton {carrier : PUnit.{1} → J → Type}
    (algebra : P.Algebra carrier) (j : J) [Subsingleton (carrier PUnit.unit j)] :
    Factors (fun proof : P.Proof j => Quotient.mk ((ProofCongruence.total P).setoid j) proof)
      (Fix.fold P algebra.act PUnit.unit j) :=
  (P.fold_factors_quotient_iff _ algebra j).mpr fun _ _ _ => Subsingleton.elim _ _

/-- The quotient by the total congruence has at most one element. -/
theorem total_quotient_subsingleton (j : J) :
    Subsingleton (Quotient ((ProofCongruence.total P).setoid j)) :=
  ⟨fun first second => by
    induction first using Quotient.inductionOn
    induction second using Quotient.inductionOn
    exact Quotient.sound trivial⟩

/-- **The quotient by the total congruence is provability.** -/
theorem total_quotient_nonempty_iff (j : J) :
    Nonempty (Quotient ((ProofCongruence.total P).setoid j)) ↔ Nonempty (P.Proof j) :=
  ⟨fun ⟨value⟩ => Quotient.inductionOn value fun proof => ⟨proof⟩,
    fun ⟨proof⟩ => ⟨Quotient.mk _ proof⟩⟩

/-! ## Predicates closed under the rules -/

/-- A predicate on judgments is closed under the rules. -/
def RuleClosed (predicate : J → Prop) : Prop :=
  ∀ (j : J) (shape : P.Shape PUnit.unit j),
    (∀ position, predicate (P.next shape position)) → predicate j

/-- Derivability is closed under the rules. -/
theorem derivable_ruleClosed : P.RuleClosed fun j => Nonempty (P.Proof j) :=
  fun _ shape each => ⟨P.node shape fun position => Classical.choice (each position)⟩

variable {P}

/-- **Derivability is the least predicate closed under the rules.** -/
theorem derivable_least {predicate : J → Prop} (closed : P.RuleClosed predicate) {j : J}
    (derivable : Nonempty (P.Proof j)) : predicate j := by
  obtain ⟨proof⟩ := derivable
  induction proof using Proof.induction with
  | node shape children ih => exact closed _ shape ih

/-! ## The shallow hosting as an algebra -/

section Shallow

variable {Point : Type v} {holds : Point → J → Prop}

/-- **Truth at every point, as an algebra of the rule signature.** -/
def validityAlgebra (sound : LocallySound holds P) :
    P.Algebra (fun _ j => PLift (Valid holds j)) where
  act := fun _ _ layer =>
    ⟨fun point => sound layer.1 point fun position => (layer.2 position).down point⟩

/-- **The fold into the algebra of validity is soundness.** -/
theorem fold_validityAlgebra (sound : LocallySound holds P) {j : J} (proof : P.Proof j) :
    Fix.fold P (validityAlgebra sound).act PUnit.unit j proof = ⟨sound.valid proof⟩ :=
  plift_eq _ _

/-- Validity is closed under the rules. -/
theorem valid_ruleClosed (sound : LocallySound holds P) : P.RuleClosed (Valid holds) :=
  fun _ shape each point => sound shape point fun position => each position point

/-- **A sound embedding is faithful exactly when validity is the least
predicate closed under the rules.** -/
theorem faithful_iff_least (sound : LocallySound holds P) :
    (∀ j, Nonempty (P.Proof j) ↔ Valid holds j) ↔
      ∀ predicate : J → Prop, P.RuleClosed predicate → ∀ j, Valid holds j → predicate j := by
  constructor
  · intro faithful predicate closed j valid
    exact derivable_least closed ((faithful j).mpr valid)
  · intro least j
    exact ⟨fun ⟨proof⟩ => sound.valid proof, least _ P.derivable_ruleClosed j⟩

/-- Reading the terms of the framework as truths is a homomorphism from the
algebra of terms to the algebra of validity. -/
noncomputable def termToValidity (finitary : P.Finitary) (sound : LocallySound holds P) :
    Algebra.Hom (finitary.termAlgebra (noHoles (B := J))) (validityAlgebra sound) where
  toFun := fun _ _ term => ⟨sound.valid (finitary.readback term)⟩
  commutes := fun _ _ _ => plift_eq _ _

/-- **Soundness is encoding followed by reading terms as truths.** -/
theorem soundness_factors_through_encoding (finitary : P.Finitary)
    (sound : LocallySound holds P) {j : J} (proof : P.Proof j) :
    (termToValidity finitary sound).toFun PUnit.unit j (finitary.encodeTerm proof) =
      Fix.fold P (validityAlgebra sound).act PUnit.unit j proof :=
  P.fold_comp_hom _ _ (termToValidity finitary sound) proof

end Shallow

/-! ## The final algebra -/

variable (P)

/-- The algebra with one element at each judgment. -/
def unitAlgebra : P.Algebra (fun _ _ => PUnit.{1}) where
  act := fun _ _ _ => PUnit.unit

/-- **Every algebra has exactly one homomorphism into the algebra with one
element.** -/
theorem hom_to_unit_unique {carrier : PUnit.{1} → J → Type} (algebra : P.Algebra carrier)
    (first second : Algebra.Hom algebra P.unitAlgebra) :
    first.toFun = second.toFun := by
  funext base j value
  rfl

/-- The homomorphism into the algebra with one element. -/
def homToUnit {carrier : PUnit.{1} → J → Type} (algebra : P.Algebra carrier) :
    Algebra.Hom algebra P.unitAlgebra where
  toFun := fun _ _ _ => PUnit.unit
  commutes := fun _ _ _ => rfl

variable {P}

/-- **Validity is not the final algebra unless every judgment is valid**:
the algebra with one element maps into it only then. -/
theorem not_hom_unit_validity {Point : Type v} {holds : Point → J → Prop}
    (sound : LocallySound holds P) {j : J} (invalid : ¬ Valid holds j) :
    IsEmpty (Algebra.Hom P.unitAlgebra (validityAlgebra sound)) :=
  ⟨fun hom => invalid (hom.toFun PUnit.unit j PUnit.unit).down⟩

/-! ## The final observer is a behaviour -/

section Behaviour

variable (P) [DecidableEq J]

/-- A use of a derivation: a derived rule with one assumption. -/
abbrev Use : Type := Σ source target : J, P.Open (fun _ : Unit => source) target

/-- Use a claim in a derived rule with one assumption: put its derivation in
the hole when the judgments agree, and otherwise leave it. -/
noncomputable def use (claim : P.Claim) (context : P.Use) : P.Claim :=
  if agrees : context.1 = claim.1 then
    ⟨context.2.1, P.fill context.2.2 fun _ => agrees ▸ claim.2⟩
  else claim

/-- The judgment of a claim is stable under every use. -/
theorem stableUnder_judgment : StableUnder P.use (fun claim : P.Claim => claim.1) := by
  intro first second same context
  by_cases agrees : context.1 = first.1
  · rw [use, use, dif_pos agrees, dif_pos (agrees.trans same)]
  · rw [use, use, dif_neg agrees, dif_neg fun other => agrees (other.trans same.symm)]
    exact same

/-- **For the purpose of seeing which judgment is claimed, the judgment is
the word behaviour**: two claims have the same judgment exactly when no
sequence of uses tells their judgments apart. -/
theorem judgment_eq_iff_wordBehaviour (first second : P.Claim) :
    first.1 = second.1 ↔
      wordBehaviour P.use (fun claim : P.Claim => claim.1) first =
        wordBehaviour P.use (fun claim : P.Claim => claim.1) second :=
  sameFibres_of_coarsest_word P.stableUnder_judgment ⟨id, fun _ => rfl⟩
    factors_wordBehaviour_evaluation first second

/-- **The behaviour is final among the stable views that keep the
judgment**: it factors through every one of them. -/
theorem wordBehaviour_factors_stable {View : Type} (view : P.Claim → View)
    (stable : StableUnder P.use view)
    (keeps : Factors view (fun claim : P.Claim => claim.1)) :
    Factors view (wordBehaviour P.use (fun claim : P.Claim => claim.1)) :=
  factors_wordBehaviour stable keeps

/-- For the purpose of seeing the derivation, the word behaviour keeps every
claim apart. -/
theorem wordBehaviour_claim_injective :
    Function.Injective (wordBehaviour P.use (fun claim : P.Claim => claim)) :=
  fun _ _ same => congrFun same []

end Behaviour

end RuleSignature

/-! ## Soundness without closure -/

/-- A proof system with one rule, from the judgment `true` to the judgment
`false`, and no axiom. -/
def gapSignature : RuleSignature Bool where
  Shape := fun _ j => PLift (j = false)
  Position := fun _ => Unit
  next := fun _ _ => true

/-- It has no derivation. -/
theorem gap_no_proof (j : Bool) : IsEmpty (gapSignature.Proof j) :=
  ⟨fun proof => RuleSignature.Proof.induction (P := gapSignature)
    (motive := fun _ _ => False) (fun _ _ ih => ih ()) proof⟩

/-- A semantics in which `true` holds and `false` does not. -/
def gapHolds (_ : Unit) (j : Bool) : Prop := j = true

/-- Every derivable judgment is valid: there is none. -/
theorem gap_sound (j : Bool) (derivable : Nonempty (gapSignature.Proof j)) : Valid gapHolds j :=
  derivable.elim fun proof => ((gap_no_proof j).false proof).elim

/-- **Soundness does not make validity closed under the rules.** -/
theorem gap_not_ruleClosed : ¬ gapSignature.RuleClosed (Valid gapHolds) := by
  intro closed
  have invalid : Valid gapHolds false := closed false ⟨rfl⟩ fun _ _ => rfl
  exact Bool.false_ne_true (invalid ())

/-! ## The worked logic -/

/-- **The size of a derivation is not a fold that respects the total
congruence.** -/
theorem size_not_factors_total :
    ¬ Factors (fun proof : IntProof ((.atom 0 : IntFormula) ➝ .atom 0) =>
        Quotient.mk ((RuleSignature.ProofCongruence.total intSignature).setoid _) proof)
      (fun proof => RuleSignature.size intFinitary proof) :=
  NonTrivialFiber.not_factors
    { left := identityProof (.atom 0)
      right := detourProof (.atom 0)
      sameShadow := Quotient.sound trivial
      differentValue := by
        rw [size_identityProof, size_detourProof]
        decide }

/-- The algebra of Kripke validity is not final: Peirce's law is not valid. -/
theorem kripke_validity_not_final :
    IsEmpty (Algebra.Hom intSignature.unitAlgebra
      (RuleSignature.validityAlgebra kripke_locallySound)) :=
  RuleSignature.not_hom_unit_validity kripke_locallySound (j := peirce)
    fun valid => kripke_not_peirce (valid _)

#print axioms RuleSignature.fold_unique
#print axioms RuleSignature.fold_comp_hom
#print axioms RuleSignature.fold_descends_unique
#print axioms RuleSignature.faithful_iff_least
#print axioms RuleSignature.soundness_factors_through_encoding
#print axioms RuleSignature.judgment_eq_iff_wordBehaviour
#print axioms RuleSignature.wordBehaviour_factors_stable
#print axioms gap_not_ruleClosed
#print axioms size_not_factors_total
#print axioms kripke_validity_not_final

end Mettapedia.Logic.HostingStyles
