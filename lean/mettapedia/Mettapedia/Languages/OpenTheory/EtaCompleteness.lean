import Mettapedia.Languages.OpenTheory.EtaCompletenessRules
import Mettapedia.Languages.OpenTheory.EtaCompletenessExpansion

/-!
# Completeness of the OpenTheory kernel with eta

The OpenTheory primitive kernel with the eta axiom proves exactly the
sequents whose translations are derivable in extensional intuitionistic
higher-order logic (`HOL.ExtDerivation`), and therefore exactly the sequents
whose translations are Heyting-valued consequences of their translated
hypotheses.

## Main results

* `kernelProvable_of_translatedProvable`: under every axiom policy admitting
  the eta sequent, a sequent with Boolean hypotheses whose translation is
  derivable from the translated hypotheses is kernel-provable.  The derivation
  is reversed at the empty naming (`kernelProvable_reverse_of_extDerivation`),
  which returns every hypothesis and the conclusion with bare equality
  eta-expanded; the kernel proves each expansion equal to the original
  (`KernelProvable.eq_expandBareEquality`), and the expanded hypotheses are
  discharged (`KernelProvable.of_forall_mem_provable`).
* `kernelProvable_etaAxiomPolicy_iff_translatedProvable`: for sequents with
  Boolean hypotheses, kernel provability under `etaAxiomPolicy` is
  derivability of the translation; `derives_etaAxiomPolicy_iff_translatedProvable`
  states it for derivations of the exact sequent.
* `provable_iff_heytingConsequence_withParams`: over any signature with a
  constant at every type, such as the target signature `Symbol` (whose
  variable symbols exist at every type, `paramSymbol`), derivability from any
  closed theory is Heyting-valued consequence over the signature extended by
  parameters (`HOL.WithParams`), the theory and formula embedded by
  `HOL.WithParams.inj`.  Parameters are conservative
  (`provable_iff_provable_withParams`): a derivation over the extended
  signature maps back by sending each parameter to a constant of its type.
* `kernelProvable_etaAxiomPolicy_iff_heytingConsequence_withParams`: for
  sequents with Boolean hypotheses, kernel provability under `etaAxiomPolicy`
  is Heyting-valued consequence of the embedded translations over models of
  the signature with parameters.  `EtaCompletenessHeyting.lean` removes the
  parameters: the same holds over models of `Symbol` itself.

## Controls

* positive: `p ∧ q ⊢ q ∧ p` and the closed extensionality principle
  `∀ f g. (∀ x. f x = g x) ⇒ f = g`, derived in `HOL.ExtDerivation` and
  transported to the kernel;
* negative: the eta axiom is needed (the eta sequent's translation is
  derivable, and it is not kernel-provable under the empty policy); the
  Boolean-hypothesis premise is needed (a non-Boolean hypothesis is invisible
  to the translation and fatal to kernel provability); and `⊤`, derivable in
  the target, is the translation of no OpenTheory term, so the correspondence
  is with the image of the translation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory

open Mettapedia.Logic
open CanonicalTerm (equalityDB)
open ReverseTranslation
open DerivedRules

namespace EtaCompleteness

/-! ## Completeness relative to extensional HOL -/

section Completeness

variable {policy : AxiomPolicy}

/-- A term that translates to a formula is Boolean. -/
theorem isBool_of_translates {term : CanonicalTerm} {φ : HOL.ClosedFormula Symbol}
    (translation : Translates [] term.term .prop φ) : term.IsBool := by
  obtain ⟨φ', hφ'⟩ := translation.exists_compositional
  exact CanonicalTerm.isBool_of_translation hφ'

/-- The reverse at the empty naming of a translated formula is the source term
with bare equality eta-expanded. -/
theorem reverseTerm_empty_of_translates {term : DBTerm} {φ : HOL.ClosedFormula Symbol}
    (translation : Translates [] term .prop φ) :
    reverseTerm Naming.empty φ = expandBareEquality term :=
  (reverseTerm_eq_reverseTermOpen φ).trans (reverseTermOpen_of_translates translation)

/-- A Boolean hypothesis proves its own bare-equality expansion. -/
theorem kernelProvable_expandBareEquality_of_mem (admitted : policy EtaAxiom.sequent)
    {hyp : Finset CanonicalTerm} (hypBool : ∀ term ∈ hyp, term.IsBool)
    {term : CanonicalTerm} (member : term ∈ hyp) :
    KernelProvable policy hyp (expandBareEquality term.term) := by
  have hbool := hypBool term member
  have typed : term.term.inferType [] = some Ty.bool := hbool ▸ term.checked
  exact KernelProvable.weaken
    ((KernelProvable.eqMp (KernelProvable.eq_expandBareEquality admitted typed)
      (KernelProvable.assume term hbool)).congr_hyp (Finset.empty_union _))
    (Finset.singleton_subset_iff.mpr member) hypBool

/-- **Completeness relative to extensional HOL.**  Under every axiom policy
admitting the eta sequent, a sequent with Boolean hypotheses whose
translation is derivable from its translated hypotheses is kernel-provable. -/
theorem kernelProvable_of_translatedProvable (admitted : policy EtaAxiom.sequent)
    {sequent : Sequent} (hypBool : ∀ term ∈ sequent.hyp, term.IsBool)
    (provable : TranslatedProvable ∅ sequent) :
    KernelProvable policy sequent.hyp sequent.concl.term := by
  obtain ⟨φ, translation, premises, hpremises, derivation⟩ := provable
  have hreverse :=
    kernelProvable_reverse_of_extDerivation admitted derivation Naming.empty
  rw [reverseTerm_empty_of_translates translation] at hreverse
  have hexpanded : KernelProvable policy sequent.hyp (expandBareEquality sequent.concl.term) :=
    KernelProvable.of_forall_mem_provable hreverse hypBool fun term member => by
      obtain ⟨ψ, hψ, rfl⟩ := mem_reverseHypotheses.mp member
      rcases hpremises ψ hψ with absurdity | ⟨source, hsource, hψtranslation⟩
      · exact absurd absurdity (Set.notMem_empty ψ)
      · show KernelProvable policy sequent.hyp (reverseTerm Naming.empty ψ)
        rw [reverseTerm_empty_of_translates hψtranslation]
        exact kernelProvable_expandBareEquality_of_mem admitted hypBool hsource
  have typed : sequent.concl.term.inferType [] = some Ty.bool :=
    isBool_of_translates translation ▸ sequent.concl.checked
  exact KernelProvable.convRule
    (KernelProvable.sym (KernelProvable.eq_expandBareEquality admitted typed)) hexpanded

/-- Soundness relative to extensional HOL, for a policy whose admitted
sequents have derivable translations. -/
theorem translatedProvable_of_kernelProvable
    (policyProvable : ∀ sequent, policy sequent → TranslatedProvable ∅ sequent)
    {sequent : Sequent} (h : KernelProvable policy sequent.hyp sequent.concl.term) :
    TranslatedProvable ∅ sequent := by
  obtain ⟨out, derivation, hsequent⟩ := (kernelProvable_iff_derives_sequent sequent.concl).mp h
  have provable :=
    derives_translatedProvable_of_policy variableFreeSubstitutionClosed_empty policyProvable
      derivation
  rw [hsequent] at provable
  exact provable

/-- **The OpenTheory kernel with eta is sound and complete for extensional
HOL.**  For a sequent with Boolean hypotheses, kernel provability under
`etaAxiomPolicy` is derivability of its translation from its translated
hypotheses. -/
theorem kernelProvable_etaAxiomPolicy_iff_translatedProvable {sequent : Sequent}
    (hypBool : ∀ term ∈ sequent.hyp, term.IsBool) :
    KernelProvable etaAxiomPolicy sequent.hyp sequent.concl.term ↔
      TranslatedProvable ∅ sequent :=
  ⟨translatedProvable_of_kernelProvable etaAxiomPolicy_translatedProvable,
    kernelProvable_of_translatedProvable (policy := etaAxiomPolicy) rfl hypBool⟩

/-- The same for derivations of the exact sequent in the policy closure. -/
theorem derives_etaAxiomPolicy_iff_translatedProvable {sequent : Sequent}
    (hypBool : ∀ term ∈ sequent.hyp, term.IsBool) :
    (∃ out : Theorem, Derives (PolicyPrimitiveRule etaAxiomPolicy) out ∧
      out.sequent = sequent) ↔ TranslatedProvable ∅ sequent := by
  rw [← kernelProvable_etaAxiomPolicy_iff_translatedProvable hypBool,
    kernelProvable_iff_derives_sequent]

end Completeness

/-! ## Heyting-valued completeness -/

section Heyting

universe u v

variable {Base : Type u} {Const : HOL.Ty Base → Type v}

/-- The embedding of terms into the signature extended by parameters. -/
abbrev embedParams {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} :
    HOL.Term Const Γ τ → HOL.Term (HOL.WithParams Const) Γ τ :=
  HOL.mapConst (fun {_} constant => HOL.WithParams.inj constant)

/-- Keep the original constants and send every parameter to a chosen constant
of its type. -/
def eraseParams (pick : ∀ σ : HOL.Ty Base, Const σ) :
    ∀ {σ : HOL.Ty Base}, HOL.WithParams Const σ → Const σ
  | _, .inl constant => constant
  | σ, .inr _ => pick σ

theorem mapConst_eraseParams_embedParams (pick : ∀ σ : HOL.Ty Base, Const σ)
    {Γ : HOL.Ctx Base} {τ : HOL.Ty Base} (term : HOL.Term Const Γ τ) :
    HOL.mapConst (eraseParams pick) (embedParams term) = term := by
  rw [embedParams, HOL.mapConst_comp]
  exact HOL.mapConst_id term

/-- **Parameters are conservative.**  Over a signature with a constant at
every type, derivability from a closed theory is derivability of the embedded
theory and formula over the signature with parameters. -/
theorem provable_iff_provable_withParams (pick : ∀ σ : HOL.Ty Base, Const σ)
    {T : HOL.ClosedTheorySet Const} {φ : HOL.ClosedFormula Const} :
    HOL.ClosedTheorySet.Provable T φ ↔
      HOL.ClosedTheorySet.Provable (embedParams '' T) (embedParams φ) := by
  constructor
  · rintro ⟨premises, hpremises, derivation⟩
    refine ⟨premises.map embedParams, fun ψ member => ?_,
      HOL.ExtDerivation.mapConst _ derivation⟩
    obtain ⟨ψ₀, hψ₀, rfl⟩ := List.mem_map.mp member
    exact ⟨ψ₀, hpremises ψ₀ hψ₀, rfl⟩
  · rintro ⟨premises, hpremises, derivation⟩
    refine ⟨premises.map (HOL.mapConst (eraseParams pick)), fun ψ member => ?_, ?_⟩
    · obtain ⟨ψ', hψ', rfl⟩ := List.mem_map.mp member
      obtain ⟨ψ₀, hψ₀, rfl⟩ := hpremises ψ' hψ'
      rw [mapConst_eraseParams_embedParams]
      exact hψ₀
    · have mapped := HOL.ExtDerivation.mapConst (eraseParams pick) derivation
      rwa [mapConst_eraseParams_embedParams] at mapped

/-- **Heyting-valued completeness without parameters in the statement.**  Over
a signature with a constant at every type, derivability from a closed theory is
consequence over all Heyting-valued substitutional models of the signature
with parameters, the theory and the formula embedded by
`HOL.WithParams.inj`. -/
theorem provable_iff_heytingConsequence_withParams (pick : ∀ σ : HOL.Ty Base, Const σ)
    {T : HOL.ClosedTheorySet Const} {φ : HOL.ClosedFormula Const} :
    HOL.ClosedTheorySet.Provable T φ ↔
      HOL.HeytingSem.HeytingConsequence (Base := Base) (embedParams '' T) (embedParams φ) := by
  rw [provable_iff_provable_withParams pick]
  exact HOL.HeytingSem.provable_iff_heytingConsequence_param_free fun ψ member σ index => by
    obtain ⟨ψ₀, -, rfl⟩ := member
    exact HOL.WithParams.noConstOccurrence_param_of_inj index ψ₀

/-- A variable symbol at every target type. -/
def paramSymbol (τ : HOL.Ty AtomicTy) : Symbol τ :=
  .variable ⟨Name.global "param", reverseTy τ⟩ (toHOL_reverseTy τ)

/-- **Heyting-valued completeness of the OpenTheory kernel with eta.**  For a
sequent with Boolean hypotheses and the translation `φ` of its conclusion,
kernel provability under `etaAxiomPolicy` is consequence of the translated
hypotheses over all Heyting-valued substitutional models of the target
signature with parameters. -/
theorem kernelProvable_etaAxiomPolicy_iff_heytingConsequence_withParams {sequent : Sequent}
    (hypBool : ∀ term ∈ sequent.hyp, term.IsBool) {φ : HOL.ClosedFormula Symbol}
    (translation : Translates [] sequent.concl.term .prop φ) :
    KernelProvable etaAxiomPolicy sequent.hyp sequent.concl.term ↔
      HOL.HeytingSem.HeytingConsequence (Base := AtomicTy)
        (embedParams '' translatedHypotheses sequent.hyp) (embedParams φ) := by
  rw [kernelProvable_etaAxiomPolicy_iff_translatedProvable hypBool,
    ← provable_iff_heytingConsequence_withParams paramSymbol]
  constructor
  · intro provable
    have hprovable := provable.provable translation
    rwa [Set.empty_union] at hprovable
  · intro provable
    exact ⟨φ, translation, by rwa [Set.empty_union]⟩

end Heyting

end EtaCompleteness

/-! ## Controls -/

namespace EtaCompletenessExamples

open EtaCompleteness DerivedRulesExamples

/-- The propositional variable symbol `p`. -/
def pFormula : HOL.ClosedFormula Symbol :=
  .const (.variable ⟨Name.global "p", Ty.bool⟩ Ty.toHOL_bool)

/-- The propositional variable symbol `q`. -/
def qFormula : HOL.ClosedFormula Symbol :=
  .const (.variable ⟨Name.global "q", Ty.bool⟩ Ty.toHOL_bool)

theorem and_comm_extDerivation :
    HOL.ExtDerivation Symbol [.and pFormula qFormula] (.and qFormula pFormula) :=
  .andI (.andER (.hyp List.mem_cons_self)) (.andEL (.hyp List.mem_cons_self))

/-- **Positive control.**  `p ∧ q ⊢ q ∧ p`, derived in extensional HOL and
transported to the kernel, with its hypothesis set `{p ∧ q}`. -/
theorem and_comm_kernelProvable :
    KernelProvable etaAxiomPolicy {pAndQ} (andAppDB qTerm.term pTerm.term) := by
  have h := kernelProvable_reverse_of_extDerivation (policy := etaAxiomPolicy) rfl
    and_comm_extDerivation Naming.empty
  rw [reverseHypotheses_cons, reverseHypotheses_nil,
    show reverseCanonical Naming.empty (.and pFormula qFormula) = pAndQ from
      CanonicalTerm.ext_term rfl] at h
  exact h

/-- The function type `ind → ind`. -/
abbrev indToInd : HOL.Ty AtomicTy := .arr Examples.ind Examples.ind

/-- `∀ f g : ind → ind. (∀ x. f x = g x) ⇒ f = g`. -/
def extensionalityFormula : HOL.ClosedFormula Symbol :=
  .all (σ := indToInd) (.all (σ := indToInd)
    (.imp (.all (.eq (.app (HOL.weaken (.var (.vs .vz))) (.var .vz))
        (.app (HOL.weaken (.var .vz)) (.var .vz))))
      (.eq (.var (.vs .vz)) (.var .vz))))

theorem extensionalityFormula_extDerivation :
    HOL.ExtDerivation Symbol ([] : List (HOL.ClosedFormula Symbol)) extensionalityFormula :=
  .allI (.allI (.impI (.funExt (.hyp List.mem_cons_self))))

/-- The kernel term `∀ f g. (∀ x. f x = g x) ⇒ f = g` over `ind → ind`, with
the defined connectives inlined. -/
def extensionalityDB : DBTerm :=
  let A := OpenTheory.Examples.individual
  forallAppDB (.function A A) (.abs (.function A A)
    (forallAppDB (.function A A) (.abs (.function A A)
      (ExcludedMiddle.impAppDB
        (forallAppDB A (.abs A
          (equalityDB A (.app (.bound 2) (.bound 0)) (.app (.bound 1) (.bound 0)))))
        (equalityDB (.function A A) (.bound 1) (.bound 0))))))

theorem reverseTerm_extensionalityFormula :
    reverseTerm Naming.empty extensionalityFormula = extensionalityDB :=
  rfl

/-- **Positive control.**  The closed extensionality principle, transported to
the kernel: GEN twice, DISCH, and EXT (hence the eta axiom). -/
theorem extensionality_kernelProvable : KernelProvable etaAxiomPolicy ∅ extensionalityDB :=
  reverseTerm_extensionalityFormula ▸
    kernelProvable_reverse_of_extDerivation (policy := etaAxiomPolicy) rfl
      extensionalityFormula_extDerivation Naming.empty

/-- **Negative control: the eta axiom is needed.**  The eta sequent
`⊢ (λx. f x) = f` is Boolean and its translation is derivable, yet it is not
kernel-provable under the empty policy; completeness fails without eta. -/
theorem exists_translatedProvable_not_kernelProvable_emptyAxiomPolicy :
    ∃ sequent : Sequent, sequent.IsBool ∧ TranslatedProvable ∅ sequent ∧
      ¬ KernelProvable emptyAxiomPolicy sequent.hyp sequent.concl.term :=
  ⟨⟨∅, Eta.equation (Name.global "f") OpenTheory.Examples.individual Ty.bool⟩,
    ⟨rfl, fun _ member => absurd member (Finset.notMem_empty _)⟩,
    Eta.equation_translatedProvable _ _ _,
    DerivedRulesEtaExamples.etaVariable_not_provable_without_axiom⟩

/-- **Negative control: Boolean hypotheses are needed.**  The sequent
`x ⊢ T`, with `x` an individual variable, has a derivable translation (its
hypothesis does not translate to a formula), and it is not kernel-provable,
since kernel hypotheses are Boolean. -/
theorem nonBoolHypothesis_translatedProvable_and_not_kernelProvable :
    ¬ BindingExamples.freeX.IsBool ∧
      TranslatedProvable ∅ ⟨{BindingExamples.freeX}, truthTerm⟩ ∧
      ¬ KernelProvable etaAxiomPolicy {BindingExamples.freeX} truthTerm.term := by
  have notBool : ¬ BindingExamples.freeX.IsBool := by
    simp [CanonicalTerm.IsBool, BindingExamples.freeX, OpenTheory.Examples.individual, Ty.bool,
      TypeOp.bool, Name.global]
  refine ⟨notBool, ⟨PrimitiveSentences.truthFormula, PrimitiveSentences.truthDB_translates [],
    [], fun _ member => absurd member List.not_mem_nil, .eqRefl _⟩, fun h => ?_⟩
  exact notBool (h.hyp_isBool _ (Finset.mem_singleton_self _))

/-- **Negative control: the correspondence is with the image of the
translation.**  `⊤` is derivable in extensional HOL, and no OpenTheory term
translates to it: its reverse `T` translates to the defined truth instead. -/
theorem extDerivation_top_and_not_translates_top :
    HOL.ExtDerivation Symbol ([] : List (HOL.ClosedFormula Symbol)) .top ∧
      ∀ term : DBTerm, ¬ Translates [] term .prop .top :=
  ⟨.topI, ReverseTranslation.Examples.not_translates_top []⟩

end EtaCompletenessExamples

end Mettapedia.Languages.OpenTheory
