import Mettapedia.Logic.HOL.Embedding.ZFSetHOLProofDecoderBoundary
import Mettapedia.Logic.HOL.Embedding.ZFSetContextualInterpretation

/-!
# Weak decoding of HOL truth fibres into actual graph products

Implication and universal quantification admit explicit carrier equivalences
with the existing set-coded products. Their introduction/application laws
and substitution squares are proved using actual graph decoding. They are
not strict equalities of the underlying set codes: the closed implication
counterexample remains valid.

All uniqueness used here is derived for these extensional semantic truth
fibres and their total graphs. It does not identify native identity proofs
or retained source proof trees, and does not by itself interpret arbitrary
native conversion, identity elimination, or induction.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetHOLWeakProofDecoding

open ZFSetHOLProofInterpretation ZFSetHOLTermInterpretation ZFSetHOLTypeInterpretation
open ZFSetDependentProducts ZFSetUniverseInterpretation ZFSetUniverseClosure

universe u

theorem fibre_subsingleton (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    (p : Formula UniverseSymbol Γ) (ρ : Valuation Γ) :
    Subsingleton (Elements (truthFibre h p ρ)) := by
  constructor
  intro left right
  apply Subtype.ext
  exact ((mem_truthFibre h p ρ left.1).mp left.2).1.trans
    ((mem_truthFibre h p ρ right.1).mp right.2).1.symm

/-! ## Implication: a truth fibre and a total graph carrier -/

noncomputable def implicationSections (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    (p q : Formula UniverseSymbol Γ) (ρ : Valuation Γ) :
    Elements (truthFibre h (.imp p q) ρ) ≃
      (Elements (truthFibre h p ρ) → Elements (truthFibre h q ρ)) where
  toFun proof argument := ⟨∅, (mem_truthFibre h q ρ ∅).mpr ⟨rfl, by
    have implication := ((mem_truthFibre h (.imp p q) ρ proof.1).mp proof.2).2
    have premise := ((mem_truthFibre h p ρ argument.1).mp argument.2).2
    exact (holds_truth _).mp implication premise⟩⟩
  invFun function := ⟨∅, (mem_truthFibre h (.imp p q) ρ ∅).mpr ⟨rfl, by
    apply (holds_truth _).mpr
    intro premise
    let argument : Elements (truthFibre h p ρ) :=
      ⟨∅, (mem_truthFibre h p ρ ∅).mpr ⟨rfl, premise⟩⟩
    exact ((mem_truthFibre h q ρ (function argument).1).mp (function argument).2).2⟩⟩
  left_inv proof := (fibre_subsingleton h (.imp p q) ρ).allEq _ proof
  right_inv function := by
    funext argument
    exact (fibre_subsingleton h q ρ).allEq _ (function argument)

noncomputable def implicationGraphCode (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    (p q : Formula UniverseSymbol Γ) (ρ : Valuation Γ) : ZFSet.{u + 1} :=
  piSet (truthFibre h p ρ) (fun _ => truthFibre h q ρ)

noncomputable def implicationEquiv (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    (p q : Formula UniverseSymbol Γ) (ρ : Valuation Γ) :
    Elements (truthFibre h (.imp p q) ρ) ≃ Elements (implicationGraphCode h p q ρ) :=
  (implicationSections h p q ρ).trans
    (piEquiv (truthFibre h p ρ) (fun _ => truthFibre h q ρ)).symm

noncomputable def implicationIntro (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    {p q : Formula UniverseSymbol Γ} {ρ : Valuation Γ}
    (body : Elements (truthFibre h p ρ) → Elements (truthFibre h q ρ)) :
    Elements (truthFibre h (.imp p q) ρ) := (implicationSections h p q ρ).symm body

noncomputable def implicationApp (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    {p q : Formula UniverseSymbol Γ} {ρ : Valuation Γ}
    (proof : Elements (truthFibre h (.imp p q) ρ))
    (argument : Elements (truthFibre h p ρ)) : Elements (truthFibre h q ρ) :=
  graphValue (a := truthFibre h p ρ) (b := fun _ => truthFibre h q ρ)
    (implicationEquiv h p q ρ proof) argument

theorem implication_intro_graph (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    {p q : Formula UniverseSymbol Γ} {ρ : Valuation Γ}
    (body : Elements (truthFibre h p ρ) → Elements (truthFibre h q ρ)) :
    implicationEquiv h p q ρ (implicationIntro h body) =
      encodeFunction (a := truthFibre h p ρ) (b := fun _ => truthFibre h q ρ) body := by
  change (piEquiv (truthFibre h p ρ) (fun _ => truthFibre h q ρ)).symm ((implicationSections h p q ρ)
    ((implicationSections h p q ρ).symm body)) = _
  rw [Equiv.apply_symm_apply]
  rfl

theorem implication_app_sections (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    {p q : Formula UniverseSymbol Γ} {ρ : Valuation Γ}
    (proof : Elements (truthFibre h (.imp p q) ρ)) (argument : Elements (truthFibre h p ρ)) :
    implicationApp h proof argument = implicationSections h p q ρ proof argument :=
  congrFun (decode_encode_function (a := truthFibre h p ρ)
    (b := fun _ => truthFibre h q ρ) (implicationSections h p q ρ proof)) argument

theorem implication_beta (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    {p q : Formula UniverseSymbol Γ} {ρ : Valuation Γ}
    (body : Elements (truthFibre h p ρ) → Elements (truthFibre h q ρ))
    (argument : Elements (truthFibre h p ρ)) :
    implicationApp h (implicationIntro h body) argument = body argument := by
  rw [implication_app_sections]
  exact congrFun ((implicationSections h p q ρ).apply_symm_apply body) argument

theorem implication_eta (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    {p q : Formula UniverseSymbol Γ} {ρ : Valuation Γ}
    (proof : Elements (truthFibre h (.imp p q) ρ)) :
    implicationIntro h (fun argument => implicationApp h proof argument) = proof := by
  apply (implicationSections h p q ρ).injective
  change (implicationSections h p q ρ) ((implicationSections h p q ρ).symm _) = _
  rw [Equiv.apply_symm_apply]
  funext argument
  exact implication_app_sections h proof argument

/-- The same implication graph code is the existing contextual product;
the outside-domain extension does not alter the bounded graph set. -/
theorem implicationGraphCode_cwf (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    (p q : Formula UniverseSymbol Γ) (ρ : Valuation Γ) :
    implicationGraphCode h p q ρ =
      ZFSetContextualInterpretation.piFamily
        (fun ν : Valuation Γ => truthFibre h p ν)
        (fun point => truthFibre h q point.1) ρ := by
  apply piSet_congr
  intro x member
  exact (ZFSetContextualInterpretation.totalFamily_at (truthFibre h p ρ)
    (fun _ => truthFibre h q ρ) ⟨x, member⟩).symm

/-! ## Universal quantification: the original carrier and dependent fibres -/

noncomputable def quantifierDomain (Γ : Ctx Unit) (A : Ty Unit) :
    ZFSetContextualInterpretation.SetFamily (Valuation.{u} Γ) := fun _ => typeCode A

noncomputable def quantifierBody (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} (p : Formula UniverseSymbol (A :: Γ)) :
    ZFSetContextualInterpretation.SetFamily
      (ZFSetContextualInterpretation.Extension (quantifierDomain Γ A)) :=
  fun point => truthFibre h p (extend point.1 point.2)

noncomputable def universalGraphCode (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} (p : Formula UniverseSymbol (A :: Γ))
    (ρ : Valuation Γ) : ZFSet.{u + 1} :=
  ZFSetContextualInterpretation.piFamily (quantifierDomain Γ A) (quantifierBody h p) ρ

noncomputable def universalSections (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} (p : Formula UniverseSymbol (A :: Γ))
    (ρ : Valuation Γ) : Elements (truthFibre h (.all p) ρ) ≃
      ((x : Value A) → Elements (truthFibre h p (extend ρ x))) where
  toFun proof x := ⟨∅, (mem_truthFibre h p (extend ρ x) ∅).mpr ⟨rfl, by
    have universal := ((mem_truthFibre h (.all p) ρ proof.1).mp proof.2).2
    exact (holds_truth _).mp universal x⟩⟩
  invFun sectionValue := ⟨∅, (mem_truthFibre h (.all p) ρ ∅).mpr ⟨rfl, by
    apply (holds_truth _).mpr
    intro x
    exact ((mem_truthFibre h p (extend ρ x) (sectionValue x).1).mp (sectionValue x).2).2⟩⟩
  left_inv proof := (fibre_subsingleton h (.all p) ρ).allEq _ proof
  right_inv sectionValue := by
    funext x
    exact (fibre_subsingleton h p (extend ρ x)).allEq _ (sectionValue x)

noncomputable def universalEquiv (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} (p : Formula UniverseSymbol (A :: Γ))
    (ρ : Valuation Γ) : Elements (truthFibre h (.all p) ρ) ≃
      Elements (universalGraphCode h p ρ) :=
  (universalSections h p ρ).trans
    (ZFSetContextualInterpretation.piDecode (quantifierDomain Γ A) (quantifierBody h p) ρ).symm

noncomputable def universalIntro (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} {p : Formula UniverseSymbol (A :: Γ)} {ρ : Valuation Γ}
    (body : (x : Value A) → Elements (truthFibre h p (extend ρ x))) :
    Elements (truthFibre h (.all p) ρ) := (universalSections h p ρ).symm body

noncomputable def universalApp (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} {p : Formula UniverseSymbol (A :: Γ)} {ρ : Valuation Γ}
    (proof : Elements (truthFibre h (.all p) ρ)) (x : Value A) :
    Elements (truthFibre h p (extend ρ x)) :=
  ZFSetContextualInterpretation.piDecode (quantifierDomain Γ A) (quantifierBody h p) ρ
    (universalEquiv h p ρ proof) x

theorem universal_intro_graph (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} {p : Formula UniverseSymbol (A :: Γ)} {ρ : Valuation Γ}
    (body : (x : Value A) → Elements (truthFibre h p (extend ρ x))) :
    universalEquiv h p ρ (universalIntro h body) =
      (ZFSetContextualInterpretation.piDecode (quantifierDomain Γ A) (quantifierBody h p) ρ).symm
        body := by
  change (ZFSetContextualInterpretation.piDecode (quantifierDomain Γ A) (quantifierBody h p) ρ).symm
    ((universalSections h p ρ) ((universalSections h p ρ).symm body)) = _
  rw [Equiv.apply_symm_apply]

theorem universal_app_sections (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} {p : Formula UniverseSymbol (A :: Γ)} {ρ : Valuation Γ}
    (proof : Elements (truthFibre h (.all p) ρ)) (x : Value A) :
    universalApp h proof x = universalSections h p ρ proof x :=
  congrFun (Equiv.apply_symm_apply
    (ZFSetContextualInterpretation.piDecode (quantifierDomain Γ A) (quantifierBody h p) ρ)
    (universalSections h p ρ proof)) x

theorem universal_beta (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} {p : Formula UniverseSymbol (A :: Γ)} {ρ : Valuation Γ}
    (body : (x : Value A) → Elements (truthFibre h p (extend ρ x))) (x : Value A) :
    universalApp h (universalIntro h body) x = body x := by
  rw [universal_app_sections]
  exact congrFun ((universalSections h p ρ).apply_symm_apply body) x

theorem universal_eta (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} {p : Formula UniverseSymbol (A :: Γ)} {ρ : Valuation Γ}
    (proof : Elements (truthFibre h (.all p) ρ)) :
    universalIntro h (fun x => universalApp h proof x) = proof := by
  apply (universalSections h p ρ).injective
  change (universalSections h p ρ) ((universalSections h p ρ).symm _) = _
  rw [Equiv.apply_symm_apply]
  funext x
  exact universal_app_sections h proof x

/-! ## Naturality over original HOL substitutions -/

theorem implication_graph_subsingleton (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    (p q : Formula UniverseSymbol Γ) (ρ : Valuation Γ) :
    Subsingleton (Elements (implicationGraphCode h p q ρ)) := by
  constructor
  intro left right
  apply (piEquiv (truthFibre h p ρ) (fun _ => truthFibre h q ρ)).injective
  funext argument
  exact (fibre_subsingleton h q ρ).allEq _ _

theorem universal_graph_subsingleton (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} (p : Formula UniverseSymbol (A :: Γ))
    (ρ : Valuation Γ) : Subsingleton (Elements (universalGraphCode h p ρ)) := by
  constructor
  intro left right
  apply (ZFSetContextualInterpretation.piDecode (quantifierDomain Γ A) (quantifierBody h p) ρ).injective
  funext x
  exact (fibre_subsingleton h p (extend ρ x)).allEq _ _

theorem implicationGraphCode_substitution (h : CofinalInaccessibles.{u})
    {Γ Δ : Ctx Unit} (p q : Formula UniverseSymbol Γ) (θ : Subst UniverseSymbol Γ Δ)
    (ρ : Valuation Δ) :
    implicationGraphCode h (HOL.subst θ p) (HOL.subst θ q) ρ =
      implicationGraphCode h p q (substValuation (universeConstants h) θ ρ) := by
  unfold implicationGraphCode
  rw [truthFibre_substitution, truthFibre_substitution]

theorem quantifierFibre_substitution (h : CofinalInaccessibles.{u})
    {Γ Δ : Ctx Unit} {A : Ty Unit} (p : Formula UniverseSymbol (A :: Γ))
    (θ : Subst UniverseSymbol Γ Δ) (ρ : Valuation Δ) (x : Value A) :
    truthFibre h (HOL.subst (Subst.lift θ) p) (extend ρ x) =
      truthFibre h p (extend (substValuation (universeConstants h) θ ρ) x) :=
  (truthFibre_substitution h p (Subst.lift θ) (extend ρ x)).trans
    (congrArg (fun ν : Valuation (A :: Γ) => truthFibre h p ν)
      (universe_substValuation_lift h θ ρ x))

theorem universalGraphCode_substitution (h : CofinalInaccessibles.{u})
    {Γ Δ : Ctx Unit} {A : Ty Unit} (p : Formula UniverseSymbol (A :: Γ))
    (θ : Subst UniverseSymbol Γ Δ) (ρ : Valuation Δ) :
    universalGraphCode h (HOL.subst (Subst.lift θ) p) ρ =
      universalGraphCode h p (substValuation (universeConstants h) θ ρ) := by
  apply piSet_congr
  intro x member
  have left := ZFSetContextualInterpretation.totalFamily_at (typeCode A)
    (fun x : Value A => truthFibre h (HOL.subst (Subst.lift θ) p) (extend ρ x)) ⟨x, member⟩
  have right := ZFSetContextualInterpretation.totalFamily_at (typeCode A)
    (fun x : Value A => truthFibre h p (extend (substValuation (universeConstants h) θ ρ) x))
    ⟨x, member⟩
  exact left.trans ((quantifierFibre_substitution h p θ ρ ⟨x, member⟩).trans right.symm)

/-- Naturality is equality of actual graph values after the proved code
reindexing. Graph uniqueness follows from their actual singleton fibres;
it is not an assumed native proof-irrelevance principle. -/
theorem implicationEquiv_substitution (h : CofinalInaccessibles.{u})
    {Γ Δ : Ctx Unit} (p q : Formula UniverseSymbol Γ) (θ : Subst UniverseSymbol Γ Δ)
    (ρ : Valuation Δ) (proof : Elements (truthFibre h (HOL.subst θ (.imp p q)) ρ)) :
    elementsEq (implicationGraphCode_substitution h p q θ ρ)
        (implicationEquiv h (HOL.subst θ p) (HOL.subst θ q) ρ proof) =
      implicationEquiv h p q (substValuation (universeConstants h) θ ρ)
        (elementsEq (truthFibre_substitution h (.imp p q) θ ρ) proof) :=
  (implication_graph_subsingleton h p q (substValuation (universeConstants h) θ ρ)).allEq _ _

theorem universalEquiv_substitution (h : CofinalInaccessibles.{u})
    {Γ Δ : Ctx Unit} {A : Ty Unit} (p : Formula UniverseSymbol (A :: Γ))
    (θ : Subst UniverseSymbol Γ Δ) (ρ : Valuation Δ)
    (proof : Elements (truthFibre h (HOL.subst θ (.all p)) ρ)) :
    elementsEq (universalGraphCode_substitution h p θ ρ)
        (universalEquiv h (HOL.subst (Subst.lift θ) p) ρ proof) =
      universalEquiv h p (substValuation (universeConstants h) θ ρ)
        (elementsEq (truthFibre_substitution h (.all p) θ ρ) proof) :=
  (universal_graph_subsingleton h p (substValuation (universeConstants h) θ ρ)).allEq _ _

theorem implicationApp_substitution (h : CofinalInaccessibles.{u})
    {Γ Δ : Ctx Unit} (p q : Formula UniverseSymbol Γ) (θ : Subst UniverseSymbol Γ Δ)
    (ρ : Valuation Δ) (proof : Elements (truthFibre h (HOL.subst θ (.imp p q)) ρ))
    (argument : Elements (truthFibre h (HOL.subst θ p) ρ)) :
    elementsEq (truthFibre_substitution h q θ ρ) (implicationApp h proof argument) =
      implicationApp h (elementsEq (truthFibre_substitution h (.imp p q) θ ρ) proof)
        (elementsEq (truthFibre_substitution h p θ ρ) argument) :=
  (fibre_subsingleton h q (substValuation (universeConstants h) θ ρ)).allEq _ _

theorem universalApp_substitution (h : CofinalInaccessibles.{u})
    {Γ Δ : Ctx Unit} {A : Ty Unit} (p : Formula UniverseSymbol (A :: Γ))
    (θ : Subst UniverseSymbol Γ Δ) (ρ : Valuation Δ)
    (proof : Elements (truthFibre h (HOL.subst θ (.all p)) ρ)) (x : Value A) :
    elementsEq (quantifierFibre_substitution h p θ ρ x) (universalApp h proof x) =
      universalApp h (elementsEq (truthFibre_substitution h (.all p) θ ρ) proof) x :=
  (fibre_subsingleton h p (extend (substValuation (universeConstants h) θ ρ) x)).allEq _ _

theorem implicationIntro_substitution (h : CofinalInaccessibles.{u})
    {Γ Δ : Ctx Unit} (p q : Formula UniverseSymbol Γ) (θ : Subst UniverseSymbol Γ Δ)
    (ρ : Valuation Δ)
    (body : Elements (truthFibre h (HOL.subst θ p) ρ) → Elements (truthFibre h (HOL.subst θ q) ρ)) :
    elementsEq (truthFibre_substitution h (.imp p q) θ ρ) (implicationIntro h body) =
      implicationIntro h (fun x => elementsEq (truthFibre_substitution h q θ ρ)
        (body ((elementsEq (truthFibre_substitution h p θ ρ)).symm x))) :=
  (fibre_subsingleton h (.imp p q) (substValuation (universeConstants h) θ ρ)).allEq _ _

theorem universalIntro_substitution (h : CofinalInaccessibles.{u})
    {Γ Δ : Ctx Unit} {A : Ty Unit} (p : Formula UniverseSymbol (A :: Γ))
    (θ : Subst UniverseSymbol Γ Δ) (ρ : Valuation Δ)
    (body : (x : Value A) → Elements (truthFibre h (HOL.subst (Subst.lift θ) p) (extend ρ x))) :
    elementsEq (truthFibre_substitution h (.all p) θ ρ) (universalIntro h body) =
      universalIntro h (fun x => elementsEq (quantifierFibre_substitution h p θ ρ x) (body x)) :=
  (fibre_subsingleton h (.all p) (substValuation (universeConstants h) θ ρ)).allEq _ _

/-! ## The weak interpretation retains the strict counterexample -/

theorem weak_is_not_strict (h : CofinalInaccessibles.{u}) :
    truthFibre h (.imp .top .top : ClosedFormula UniverseSymbol) emptyValuation ≠
      implicationGraphCode h .top .top emptyValuation :=
  ZFSetHOLProofDecoderBoundary.strict_implication_decoder_fails h

noncomputable def topValue (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    (ρ : Valuation Γ) : Elements (truthFibre h (.top : Formula UniverseSymbol Γ) ρ) :=
  ⟨∅, (mem_truthFibre h .top ρ ∅).mpr ⟨rfl, (holds_truth True).mpr trivial⟩⟩

noncomputable def topIdentityGraph (h : CofinalInaccessibles.{u}) :
    Elements (implicationGraphCode h (.top : ClosedFormula UniverseSymbol) .top emptyValuation) :=
  implicationEquiv h .top .top emptyValuation
    (implicationIntro h (fun x : Elements (truthFibre h .top emptyValuation) => x))

theorem topIdentityGraph_nonempty (h : CofinalInaccessibles.{u}) :
    (topIdentityGraph h).1 ≠ ∅ := by
  intro emptyGraph
  have functional := (mem_piSet.mp (topIdentityGraph h).2).1
  obtain ⟨value, member, _⟩ := functional.2 ∅ (topValue h emptyValuation).2
  rw [emptyGraph] at member
  exact ZFSet.notMem_empty _ member

theorem fibre_empty_of_false (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    (p : Formula UniverseSymbol Γ) (ρ : Valuation Γ)
    (falsehood : ¬ holds (interpret (universeConstants h) p ρ)) : truthFibre h p ρ = ∅ := by
  apply ZFSet.ext
  intro x
  simp only [mem_truthFibre, falsehood, and_false, ZFSet.notMem_empty]

theorem false_fibre (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit} (ρ : Valuation Γ) :
    truthFibre h (.bot : Formula UniverseSymbol Γ) ρ = ∅ :=
  fibre_empty_of_false h .bot ρ (by simp only [interpret, holds_truth, not_false_eq_true])

noncomputable def vacuousGraph (h : CofinalInaccessibles.{u}) :
    Elements (implicationGraphCode h (.bot : ClosedFormula UniverseSymbol) .bot emptyValuation) :=
  implicationEquiv h .bot .bot emptyValuation
    (implicationIntro h (fun x : Elements (truthFibre h .bot emptyValuation) => x))

theorem vacuousGraph_empty (h : CofinalInaccessibles.{u}) : (vacuousGraph h).1 = ∅ := by
  unfold vacuousGraph
  rw [implication_intro_graph]
  apply ZFSet.ext
  intro x
  change x ∈ graph (truthFibre h .bot emptyValuation) _ ↔ x ∈ ∅
  rw [mem_graph, false_fibre]
  simp only [ZFSet.notMem_empty, exists_false, false_and]

def reflexivePredicate : Formula UniverseSymbol [ZFSetHenkinInterpretation.set] :=
  .eq (.var .vz) (.var .vz)

def reflexivityProof : ProofSyntax UniverseSymbol [] (.all reflexivePredicate) :=
  .allI (.eqRefl (.var .vz))

noncomputable def reflexivityGraph (h : CofinalInaccessibles.{u}) :
    Elements (universalGraphCode h reflexivePredicate emptyValuation) :=
  universalEquiv h reflexivePredicate emptyValuation
    (proofValue h reflexivityProof (noHypotheses h emptyValuation))

theorem reflexivityGraph_nonempty (h : CofinalInaccessibles.{u}) :
    (reflexivityGraph h).1 ≠ ∅ := by
  intro emptyGraph
  have graphMember := (reflexivityGraph h).2
  change (reflexivityGraph h).1 ∈ piSet (typeCode ZFSetHenkinInterpretation.set)
    (ZFSetContextualInterpretation.totalFamily (typeCode ZFSetHenkinInterpretation.set)
      (fun x => truthFibre h reflexivePredicate (extend emptyValuation x))) at graphMember
  have functional := (mem_piSet.mp graphMember).1
  obtain ⟨value, member, _⟩ := functional.2 ∅ ZFSetUniverseLift.carrierEmpty.2
  rw [emptyGraph] at member
  exact ZFSet.notMem_empty _ member

def functionEtaBody : Formula UniverseSymbol [ZFSetHenkinInterpretation.mapping] :=
  .eq (.lam (.app (.var (.vs .vz)) (.var .vz))) (.var .vz)

/-- The already retained higher-order eta proof becomes a total graph whose
arguments are themselves set-function graphs. -/
noncomputable def higherOrderEtaGraph (h : CofinalInaccessibles.{u}) :
    Elements (universalGraphCode h functionEtaBody emptyValuation) :=
  universalEquiv h functionEtaBody emptyValuation
    (proofValue h functionEtaProof (noHypotheses h emptyValuation))

theorem higherOrderEtaGraph_nonempty (h : CofinalInaccessibles.{u}) :
    (higherOrderEtaGraph h).1 ≠ ∅ := by
  intro emptyGraph
  let argument : Value.{u} ZFSetHenkinInterpretation.mapping := constants .power
  have graphMember := (higherOrderEtaGraph h).2
  change (higherOrderEtaGraph h).1 ∈ piSet (typeCode ZFSetHenkinInterpretation.mapping)
    (ZFSetContextualInterpretation.totalFamily (typeCode ZFSetHenkinInterpretation.mapping)
      (fun x => truthFibre h functionEtaBody (extend emptyValuation x))) at graphMember
  have functional := (mem_piSet.mp graphMember).1
  obtain ⟨value, member, _⟩ := functional.2 argument.1 argument.2
  rw [emptyGraph] at member
  exact ZFSet.notMem_empty _ member

/-- This predicate has an inhabited fibre at the empty set and an empty
fibre at its powerset. The whole universal graph product is therefore empty. -/
theorem nonconstant_universal_graph_empty (h : CofinalInaccessibles.{u}) :
    universalGraphCode h equalsParameter emptyParameter = ∅ := by
  let point : Value.{u} ZFSetHenkinInterpretation.set :=
    ZFSetUniverseLift.carrierPower ZFSetUniverseLift.carrierEmpty
  apply piSet_empty_of_empty_fibre point
  have atPoint := ZFSetContextualInterpretation.totalFamily_at
    (typeCode ZFSetHenkinInterpretation.set)
    (fun x => truthFibre h equalsParameter (extend emptyParameter x)) point
  refine atPoint.trans (fibre_empty_of_false h equalsParameter (extend emptyParameter point) ?_)
  intro proof
  simp only [equalsParameter, interpret, extend, emptyParameter, holds_truth] at proof
  have valueEqual := congrArg Subtype.val proof
  change ZFSet.powerset (∅ : ZFSet.{u + 1}) = ∅ at valueEqual
  have member : (∅ : ZFSet.{u + 1}) ∈ ZFSet.powerset ∅ :=
    ZFSet.mem_powerset.mpr (ZFSet.empty_subset _)
  rw [valueEqual] at member
  exact ZFSet.mem_irrefl _ member

theorem nonconstant_predicate_has_inhabited_fibre (h : CofinalInaccessibles.{u}) :
    Nonempty (Elements (truthFibre h equalsParameter
      (extend emptyParameter ZFSetUniverseLift.carrierEmpty))) := by
  refine ⟨⟨∅, (mem_truthFibre h _ _ ∅).mpr ⟨rfl, ?_⟩⟩⟩
  simp only [equalsParameter, interpret, extend, emptyParameter, holds_truth]

#print axioms implicationEquiv
#print axioms implication_intro_graph
#print axioms implication_beta
#print axioms implication_eta
#print axioms implicationGraphCode_cwf
#print axioms universalEquiv
#print axioms universal_intro_graph
#print axioms universal_beta
#print axioms universal_eta
#print axioms implicationGraphCode_substitution
#print axioms quantifierFibre_substitution
#print axioms universalGraphCode_substitution
#print axioms implicationEquiv_substitution
#print axioms universalEquiv_substitution
#print axioms implicationApp_substitution
#print axioms universalApp_substitution
#print axioms implicationIntro_substitution
#print axioms universalIntro_substitution
#print axioms weak_is_not_strict
#print axioms topIdentityGraph_nonempty
#print axioms vacuousGraph_empty
#print axioms reflexivityGraph_nonempty
#print axioms higherOrderEtaGraph_nonempty
#print axioms nonconstant_universal_graph_empty
#print axioms nonconstant_predicate_has_inhabited_fibre

end Mettapedia.Logic.HOL.Embedding.ZFSetHOLWeakProofDecoding
