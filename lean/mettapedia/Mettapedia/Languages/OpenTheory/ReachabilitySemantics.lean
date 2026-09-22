import Mettapedia.Languages.OpenTheory.OperationalGSLTAdequacy
import Mettapedia.Languages.OpenTheory.EtaNotDerivable

/-!
# From GSLT reachability to extensional higher-order semantics

The OpenTheory kernel as a GSLT on theorem lists (`openTheoryGSLT`), its least
policy closure, and its interpretation in extensional higher-order logic
compose into single statements about reachable states:

* `reachable_heytingConsequence_of_emptyAxiomPolicy`: every theorem in a state
  reachable from `[]` under the empty axiom policy has a translated conclusion
  that is a Heyting-valued consequence of its translated hypotheses;
  `reachable_models_of_emptyAxiomPolicy` is the same statement for every
  extensional Henkin model (`FunctionsRespectEqv`).
* `reachable_heytingConsequence` and `reachable_models`: the same under any
  axiom policy, relative to background sentences `Θ` that mention no
  free-variable symbol, are closed under the target image of every admitted
  substitution, and prove every axiom tag of the theorem.

The legs are `OperationalGSLT.derives_of_reachable` (reachability gives
derivability) and `derives_heytingConsequence`, `derives_models` (derivability
gives the semantic conclusion).

Controls:

* positive, empty policy: the beta instance `⊢ (λ x. f x) y = f y` is reachable
  and its translation is a Heyting-valued consequence
  (`betaTheorem_reachable_heytingConsequence`);
* positive, axiom policy: the `onlyP` fixture reaches its axiom `p ⊢ p`, whose
  tag is provable from no background sentences
  (`onlyP_axiomP_reachable_heytingConsequence`);
* negative, axiom-tag hypothesis: under a policy admitting `⊢ F`, the axiom
  theorem is reachable but its translation fails in the two-point extensional
  model, so the policy statements need their axiom-tag hypothesis
  (`falsityAxiom_reachable_and_not_twoPointModel`);
* negative, converse: the translated eta sequent is a Heyting-valued
  consequence of no hypotheses, yet no reachable state of the axiom-free
  kernel contains a theorem with the eta sequent
  (`eta_heytingConsequence_and_not_reachable`).

Scope of the converse:

* the axiom-free converse is false: eta separates the kernel from extensional
  higher-order logic (`Eta.eta_not_derivable`);
* `EtaCompleteness` proves the converse for the eta axiom policy and sequents
  with Boolean hypotheses, and `EtaCompletenessHeyting` gives the corresponding
  Heyting-model equivalence. Those results are downstream of this file;
* completeness for OpenTheory theories with further axioms is not proved here.

This relates different calculi by interpretation.  It does not identify the
GSLT carrier with higher-order formulas, and it concerns the OpenTheory kernel,
not HOL Light or HOL4.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory.ReachabilitySemantics

open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.OpenTheory.OperationalGSLT
open Mettapedia.Languages.OpenTheory.TheoryClosureCanary
open Mettapedia.Languages.OpenTheory.AxiomPolicyCanary
open Mettapedia.Languages.OpenTheory.CoreRulesFixtures
open Mettapedia.Logic

/-! ## Composed statements -/

/-- Axiom-free kernel: every theorem in a state reachable from `[]` has a
translated conclusion that is a Heyting-valued consequence of its translated
hypotheses. -/
theorem reachable_heytingConsequence_of_emptyAxiomPolicy {Γ : List Theorem}
    {t : Theorem} (reachable : (openTheoryGSLT emptyAxiomPolicy).MultiStep [] Γ)
    (member : t ∈ Γ) :
    ∃ φ, Translates [] t.sequent.concl.term .prop φ ∧
      HOL.HeytingSem.HeytingConsequence (Base := AtomicTy)
        (translatedHypotheses t.sequent.hyp) φ :=
  derives_heytingConsequence_of_emptyAxiomPolicy
    (derives_of_reachable emptyAxiomPolicy reachable member)

/-- Axiom-free kernel: every theorem in a state reachable from `[]` has a
translated conclusion that holds in every extensional Henkin model satisfying
its translated hypotheses. -/
theorem reachable_models_of_emptyAxiomPolicy {Γ : List Theorem} {t : Theorem}
    (reachable : (openTheoryGSLT emptyAxiomPolicy).MultiStep [] Γ) (member : t ∈ Γ)
    (model : HOL.HenkinModel AtomicTy Symbol) (extensional : model.FunctionsRespectEqv) :
    ∃ φ, Translates [] t.sequent.concl.term .prop φ ∧
      ((∀ ψ ∈ translatedHypotheses t.sequent.hyp, model.models ψ) → model.models φ) := by
  have derivation := derives_of_reachable emptyAxiomPolicy reachable member
  exact derives_models variableFreeSubstitutionClosed_empty derivation
    (fun tagged htagged => by
      rw [axioms_eq_empty_of_emptyAxiomPolicy derivation] at htagged
      exact absurd htagged (Finset.notMem_empty _))
    model extensional (fun _ h => absurd h (Set.notMem_empty _))

/-- Any axiom policy: a theorem in a state reachable from `[]` whose axiom tags
are provable from the background sentences `Θ` has a translated conclusion that
is a Heyting-valued consequence of `Θ` and its translated hypotheses. -/
theorem reachable_heytingConsequence {Θ : HOL.ClosedTheorySet Symbol}
    (background : VariableFreeSubstitutionClosed Θ) {policy : AxiomPolicy}
    {Γ : List Theorem} {t : Theorem}
    (reachable : (openTheoryGSLT policy).MultiStep [] Γ) (member : t ∈ Γ)
    (axiomsProvable : ∀ tagged ∈ t.axioms, TranslatedProvable Θ tagged) :
    ∃ φ, Translates [] t.sequent.concl.term .prop φ ∧
      HOL.HeytingSem.HeytingConsequence (Base := AtomicTy)
        (Θ ∪ translatedHypotheses t.sequent.hyp) φ :=
  derives_heytingConsequence background (derives_of_reachable policy reachable member)
    axiomsProvable

/-- Any axiom policy: a theorem in a state reachable from `[]` whose axiom tags
are provable from the background sentences `Θ` has a translated conclusion that
holds in every extensional Henkin model of `Θ` satisfying its translated
hypotheses. -/
theorem reachable_models {Θ : HOL.ClosedTheorySet Symbol}
    (background : VariableFreeSubstitutionClosed Θ) {policy : AxiomPolicy}
    {Γ : List Theorem} {t : Theorem}
    (reachable : (openTheoryGSLT policy).MultiStep [] Γ) (member : t ∈ Γ)
    (axiomsProvable : ∀ tagged ∈ t.axioms, TranslatedProvable Θ tagged)
    (model : HOL.HenkinModel AtomicTy Symbol) (extensional : model.FunctionsRespectEqv)
    (backgroundHolds : ∀ ψ ∈ Θ, model.models ψ) :
    ∃ φ, Translates [] t.sequent.concl.term .prop φ ∧
      ((∀ ψ ∈ translatedHypotheses t.sequent.hyp, model.models ψ) → model.models φ) :=
  derives_models background (derives_of_reachable policy reachable member) axiomsProvable
    model extensional backgroundHolds

/-! ## Positive controls -/

/-- The beta instance `⊢ (λ x. f x) y = f y` is reachable in the axiom-free
kernel, and its translation `(λ x. f x) y = f y` is a Heyting-valued
consequence of no hypotheses. -/
theorem betaTheorem_reachable_heytingConsequence (name : Name) (domain codomain : Ty)
    (argumentName : Name) :
    (∃ Γ : List Theorem, (openTheoryGSLT emptyAxiomPolicy).MultiStep [] Γ ∧
        Eta.betaTheorem name domain codomain argumentName ∈ Γ) ∧
      HOL.HeytingSem.HeytingConsequence (Base := AtomicTy)
        (translatedHypotheses (Eta.betaTheorem name domain codomain argumentName).sequent.hyp)
        (Eta.betaFormula name domain codomain argumentName) := by
  obtain ⟨Γ, reachable, member⟩ := reachable_of_derives emptyAxiomPolicy
    (Eta.betaTheorem_derives name domain codomain argumentName)
  obtain ⟨φ, hφ, consequence⟩ :=
    reachable_heytingConsequence_of_emptyAxiomPolicy reachable member
  have hφ' : φ = Eta.betaFormula name domain codomain argumentName :=
    hφ.unique_eq (Eta.betaEquationDB_translates name domain codomain argumentName)
  subst hφ'
  exact ⟨⟨Γ, reachable, member⟩, consequence⟩

/-- The tag of `axiomP` is the assume-shaped sequent `p ⊢ p`, which is
provable from no background sentences. -/
theorem axiomP_sequent_translatedProvable :
    TranslatedProvable (∅ : HOL.ClosedTheorySet Symbol) axiomP.sequent :=
  (translatedProvable_iff_compositionallyProvable _ _).mpr
    (compositionallyProvable_assume p_isBool)

/-- Under the `onlyP` policy, `axiomP` is reachable and its axiom tag is
provable from no background sentences, so its translated conclusion is a
Heyting-valued consequence of its translated hypotheses. -/
theorem onlyP_axiomP_reachable_heytingConsequence :
    ∃ φ, Translates [] axiomP.sequent.concl.term .prop φ ∧
      HOL.HeytingSem.HeytingConsequence (Base := AtomicTy)
        (∅ ∪ translatedHypotheses axiomP.sequent.hyp) φ := by
  obtain ⟨Γ, reachable, member⟩ := onlyP_axiomP_reachable
  refine reachable_heytingConsequence variableFreeSubstitutionClosed_empty reachable member ?_
  intro tagged htagged
  have htag : tagged = axiomP.sequent := by
    simpa [axiomP, Theorem.axiomResult] using htagged
  rw [htag]
  exact axiomP_sequent_translatedProvable

/-! ## Negative controls -/

/-- The sequent `⊢ F`. -/
def falsitySequent : Sequent := ⟨∅, falsity⟩

theorem falsitySequent_isBool : falsitySequent.IsBool :=
  ⟨rfl, by simp [falsitySequent]⟩

/-- An object theory admitting exactly the axiom `⊢ F`. -/
def onlyFalsity : AxiomPolicy := fun sequent => sequent = falsitySequent

/-- The axiom theorem `⊢ F`, tagged by its own sequent. -/
def falsityAxiom : Theorem := Theorem.axiomResult falsitySequent falsitySequent_isBool

theorem onlyFalsity_derives_falsityAxiom :
    Derives (PolicyPrimitiveRule onlyFalsity) falsityAxiom :=
  derives_of_nullary_check onlyFalsity (.core (.axiom falsitySequent)) falsityAxiom rfl rfl
    (by
      rw [checkPrimitive, checkCore]
      exact (checkAxiom_eq_some_iff falsitySequent falsityAxiom).mpr
        ⟨falsitySequent_isBool,
          (theorem_axiomResult_eq_iff_hasParts falsitySequent falsitySequent_isBool
            falsityAxiom).mp rfl⟩)

/-- The axiom-tag hypothesis of `reachable_models` cannot be dropped: under the
policy admitting `⊢ F`, the axiom theorem is reachable, it has no hypotheses,
and its translated conclusion fails in the two-point extensional model. -/
theorem falsityAxiom_reachable_and_not_twoPointModel :
    (∃ Γ : List Theorem,
        (openTheoryGSLT onlyFalsity).MultiStep [] Γ ∧ falsityAxiom ∈ Γ) ∧
      falsityAxiom.sequent.hyp = ∅ ∧
      ∀ φ, Translates [] falsityAxiom.sequent.concl.term .prop φ →
        ¬ twoPointModel.models φ := by
  refine ⟨reachable_of_derives onlyFalsity onlyFalsity_derives_falsityAxiom, rfl, ?_⟩
  intro φ hφ
  rw [hφ.unique_eq PrimitiveSentences.falsityDB_translates]
  exact twoPointModel_not_models_falsityFormula

/-- The converse of `reachable_heytingConsequence_of_emptyAxiomPolicy` fails at
eta: the translated eta sequent `⊢ (λ x. f x) = f` is a Heyting-valued
consequence of no hypotheses, but no state reachable from `[]` under the empty
axiom policy contains a theorem with that sequent. -/
theorem eta_heytingConsequence_and_not_reachable (name : Name) (domain codomain : Ty) :
    (∃ φ, Translates [] (Eta.equation name domain codomain).term .prop φ ∧
        HOL.HeytingSem.HeytingConsequence (Base := AtomicTy) (translatedHypotheses ∅) φ) ∧
      ¬ ∃ (Γ : List Theorem) (t : Theorem),
        (openTheoryGSLT emptyAxiomPolicy).MultiStep [] Γ ∧ t ∈ Γ ∧
          t.sequent = ⟨∅, Eta.equation name domain codomain⟩ := by
  refine ⟨?_, ?_⟩
  · obtain ⟨φ, hφ, provable⟩ := Eta.equation_translatedProvable name domain codomain
    rw [Set.empty_union] at provable
    exact ⟨φ, hφ, HOL.HeytingSem.heytingConsequence_of_provable provable⟩
  · rintro ⟨Γ, t, reachable, member, hsequent⟩
    exact Eta.eta_not_derivable name domain codomain
      (derives_of_reachable emptyAxiomPolicy reachable member) hsequent

#print axioms reachable_heytingConsequence_of_emptyAxiomPolicy
#print axioms reachable_models_of_emptyAxiomPolicy
#print axioms reachable_heytingConsequence
#print axioms reachable_models
#print axioms betaTheorem_reachable_heytingConsequence
#print axioms onlyP_axiomP_reachable_heytingConsequence
#print axioms falsityAxiom_reachable_and_not_twoPointModel
#print axioms eta_heytingConsequence_and_not_reachable

end Mettapedia.Languages.OpenTheory.ReachabilitySemantics
