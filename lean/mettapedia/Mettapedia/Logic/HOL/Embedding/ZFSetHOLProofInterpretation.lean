import Mettapedia.Logic.HOL.Embedding.ZFSetHOLTermInterpretation

/-!
# Retained HOL proofs consumed by actual set-coded families

The original proof trees produce elements of actual truth fibres and maps
between separated type codes. These constructions commute with the earlier
Henkin dependent-family interpretation and with simultaneous substitution.
The interpretation is extensional; the supplied `ProofSyntax` tree remains
the source proof and is not reconstructed from its truth-value image.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetHOLProofInterpretation

open ZFSetHOLTypeInterpretation ZFSetHOLTermInterpretation ZFSetDependentProducts
open ZFSetHenkinInterpretation ZFSetUniverseInterpretation ZFSetUniverseClosure
open HenkinDependentFamilyInterpretation HenkinPredicateFamilyInterpretation

universe u

theorem formula_agreement (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    (φ : Formula UniverseSymbol Γ) (ρ : Valuation.{u} Γ) :
    holds (interpret (universeConstants h) φ ρ) ↔
      ((universeModel h).denote φ (decodeValuation ρ)).down :=
  iff_of_eq (congrArg ULift.down (universe_term_agreement h φ ρ))

noncomputable def decodeContext (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} (ρ : Valuation.{u} Γ) : AdmissibleContext (universeModel h) Γ :=
  ⟨decodeValuation ρ, fun _ => trivial⟩

theorem decodeContext_substitution (h : CofinalInaccessibles.{u})
    {Γ Δ : Ctx Unit} (θ : Subst UniverseSymbol Γ Δ) (ρ : Valuation Δ) :
    decodeContext h (substValuation (universeConstants h) θ ρ) =
      interpretSubstitution (universeModel h) θ (decodeContext h ρ) := by
  apply Subtype.ext
  exact decode_substValuation (constant h) (universeConstants h) (decode_universeConstants h) θ ρ

abbrev CodedSatisfied (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    (hypotheses : List (Formula UniverseSymbol Γ)) :=
  {ρ : Valuation.{u} Γ // ∀ φ ∈ hypotheses, holds (interpret (universeConstants h) φ ρ)}

noncomputable def decodeSatisfied (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    {hypotheses : List (Formula UniverseSymbol Γ)} (ρ : CodedSatisfied h hypotheses) :
    SatisfiedContext (universeModel h) hypotheses :=
  ⟨decodeContext h ρ.1, fun φ member => (formula_agreement h φ ρ.1).mp (ρ.2 φ member)⟩

/-! ## Actual truth fibres and retained proof sections -/

noncomputable def truthFibre (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    (φ : Formula UniverseSymbol Γ) (ρ : Valuation Γ) : ZFSet.{u + 1} :=
  ZFSet.sep (fun _ => holds (interpret (universeConstants h) φ ρ)) {∅}

theorem mem_truthFibre (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    (φ : Formula UniverseSymbol Γ) (ρ : Valuation Γ) (x : ZFSet.{u + 1}) :
    x ∈ truthFibre h φ ρ ↔ x = ∅ ∧ holds (interpret (universeConstants h) φ ρ) := by
  simp only [truthFibre, ZFSet.mem_sep, ZFSet.mem_singleton]

noncomputable def truthFibreEquiv (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    (φ : Formula UniverseSymbol Γ) (ρ : Valuation Γ) :
    Elements (truthFibre h φ ρ) ≃ truthFamily (universeModel h) φ (decodeContext h ρ) where
  toFun point := ⟨⟨(formula_agreement h φ ρ).mp ((mem_truthFibre h φ ρ point.1).mp point.2).2⟩⟩
  invFun point := ⟨∅, (mem_truthFibre h φ ρ ∅).mpr
    ⟨rfl, (formula_agreement h φ ρ).mpr point.down.down⟩⟩
  left_inv point := Subtype.ext ((mem_truthFibre h φ ρ point.1).mp point.2).1.symm
  right_inv point := by cases point; rfl

noncomputable def proofValue (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    {hypotheses : List (Formula UniverseSymbol Γ)} {φ : Formula UniverseSymbol Γ}
    (proof : ProofSyntax UniverseSymbol hypotheses φ) (ρ : CodedSatisfied h hypotheses) :
    Elements (truthFibre h φ ρ.1) :=
  ⟨∅, (mem_truthFibre h φ ρ.1 ∅).mpr ⟨rfl, (formula_agreement h φ ρ.1).mpr
    (proofSection (universeModel h) (universeFunctionsRespectEqv h) proof
      (decodeSatisfied h ρ)).down.down⟩⟩

theorem proofValue_agreement (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    {hypotheses : List (Formula UniverseSymbol Γ)} {φ : Formula UniverseSymbol Γ}
    (proof : ProofSyntax UniverseSymbol hypotheses φ) (ρ : CodedSatisfied h hypotheses) :
    truthFibreEquiv h φ ρ.1 (proofValue h proof ρ) =
      proofSection (universeModel h) (universeFunctionsRespectEqv h) proof
        (decodeSatisfied h ρ) := rfl

theorem truthFibre_substitution (h : CofinalInaccessibles.{u}) {Γ Δ : Ctx Unit}
    (φ : Formula UniverseSymbol Γ) (θ : Subst UniverseSymbol Γ Δ) (ρ : Valuation Δ) :
    truthFibre h (HOL.subst θ φ) ρ =
      truthFibre h φ (substValuation (universeConstants h) θ ρ) := by
  unfold truthFibre
  rw [universe_substitution]

/-! ## All simple carriers have actual separated refinement codes -/

noncomputable def refinementCode (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} (φ : Formula UniverseSymbol (A :: Γ))
    (ρ : Valuation Γ) : ZFSet.{u + 1} :=
  ZFSet.sep (fun x => ∃ member : x ∈ typeCode A,
    holds (interpret (universeConstants h) φ (extend ρ ⟨x, member⟩))) (typeCode A)

theorem mem_refinementCode (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} (φ : Formula UniverseSymbol (A :: Γ))
    (ρ : Valuation Γ) (x : ZFSet.{u + 1}) :
    x ∈ refinementCode h φ ρ ↔ ∃ member : x ∈ typeCode A,
      holds (interpret (universeConstants h) φ (extend ρ ⟨x, member⟩)) := by
  rw [refinementCode, ZFSet.mem_sep]
  exact ⟨fun h => h.2, fun ⟨member, hp⟩ => ⟨member, member, hp⟩⟩

noncomputable def refinementCodeEquiv (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} (φ : Formula UniverseSymbol (A :: Γ))
    (ρ : Valuation Γ) : Elements (refinementCode h φ ρ) ≃
      {x : Value A // holds (interpret (universeConstants h) φ (extend ρ x))} where
  toFun point :=
    let membership := (mem_refinementCode h φ ρ point.1).mp point.2
    ⟨⟨point.1, membership.choose⟩, membership.choose_spec⟩
  invFun point := ⟨point.1.1, (mem_refinementCode h φ ρ point.1.1).mpr ⟨point.1.2, point.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def decodeAdmissible (h : CofinalInaccessibles.{u}) (A : Ty Unit) :
    Value.{u} A ≃ AdmissibleValue (universeModel h) A :=
  (decode A).trans (fullDomainsValueEquiv (universeModel h) (universeFullDomains h) A).symm

theorem predicate_agreement (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} (φ : Formula UniverseSymbol (A :: Γ))
    (ρ : Valuation Γ) (x : Value A) :
    holds (interpret (universeConstants h) φ (extend ρ x)) ↔
      ((universeModel h).denote φ ((universeModel h).extend (decodeValuation ρ)
        (decode A x))).down :=
  (formula_agreement h φ (extend ρ x)).trans
    (iff_of_eq (congrArg (fun ν : RawValuation (A :: Γ) => ((universeModel h).denote φ ν).down)
      (decode_extend (constant h) ρ x)))

noncomputable def refinementEquiv (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} (φ : Formula UniverseSymbol (A :: Γ))
    (ρ : Valuation Γ) : Elements (refinementCode h φ ρ) ≃
      refinementFamily (universeModel h) φ (decodeContext h ρ) :=
  (refinementCodeEquiv h φ ρ).trans
    (((decodeAdmissible h A).subtypeEquiv (predicate_agreement h φ ρ)).trans
      (refinementEquivSubtype (universeModel h) φ (decodeContext h ρ)).symm)

theorem refinementEquiv_value (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} (φ : Formula UniverseSymbol (A :: Γ))
    (ρ : Valuation Γ) (point : Elements (refinementCode h φ ρ)) :
    (refinementEquiv h φ ρ point).1.1 =
      decode A (refinementCodeEquiv h φ ρ point).1 := rfl

/-- The proof's original universal implication supplies membership in the
target separated set, without replacing its underlying graph or set code. -/
noncomputable def refinementMap (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} {hypotheses : List (Formula UniverseSymbol Γ)}
    {φ ψ : Formula UniverseSymbol (A :: Γ)}
    (proof : ProofSyntax UniverseSymbol hypotheses (.all (.imp φ ψ)))
    (ρ : CodedSatisfied h hypotheses) (point : Elements (refinementCode h φ ρ.1)) :
    Elements (refinementCode h ψ ρ.1) := by
  let source := refinementCodeEquiv h φ ρ.1 point
  have proofHolds := (mem_truthFibre h (.all (.imp φ ψ)) ρ.1 ∅).mp
    (proofValue h proof ρ).2
  have maps : ∀ x : Value A,
      holds (interpret (universeConstants h) φ (extend ρ.1 x)) →
        holds (interpret (universeConstants h) ψ (extend ρ.1 x)) := by
    simpa only [interpret, holds_truth] using proofHolds.2
  exact ⟨point.1, (mem_refinementCode h ψ ρ.1 point.1).mpr
    ⟨source.1.2, maps source.1 source.2⟩⟩

theorem refinementMap_square (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} {hypotheses : List (Formula UniverseSymbol Γ)}
    {φ ψ : Formula UniverseSymbol (A :: Γ)}
    (proof : ProofSyntax UniverseSymbol hypotheses (.all (.imp φ ψ)))
    (ρ : CodedSatisfied h hypotheses) (point : Elements (refinementCode h φ ρ.1)) :
    refinementEquiv h ψ ρ.1 (refinementMap h proof ρ point) =
      refinementMapOfProof (universeModel h) (universeFunctionsRespectEqv h)
        proof (decodeSatisfied h ρ) (refinementEquiv h φ ρ.1 point) := rfl

theorem refinementCode_mem (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} (φ : Formula UniverseSymbol (A :: Γ))
    (ρ : Valuation Γ) {U : ZFSet.{u + 1}} (closed : Closed U)
    (carrier_mem : ZFSetUniverseLift.carrierCode.{u} ∈ U) : refinementCode h φ ρ ∈ U :=
  closed.separation_mem (typeCode_mem closed carrier_mem A) _

/-! ## The previously constructed bounded separated set, not a new set model -/

def boundedPredicate {Γ : Ctx Unit} (bound : UniverseExpr Γ set)
    (φ : Formula UniverseSymbol (set :: Γ)) : Formula UniverseSymbol (set :: Γ) :=
  .and (inSet (.var .vz) (weaken bound)) φ

theorem bounded_predicate_agreement (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} (bound : UniverseExpr Γ set) (φ : Formula UniverseSymbol (set :: Γ))
    (ρ : Valuation Γ) (x : Value set) :
    holds (interpret (universeConstants h) (boundedPredicate bound φ) (extend ρ x)) ↔
      ZFSetUniverseLift.carrierEquiv x ∈ universePredicateSet h bound φ (decodeContext h ρ) := by
  refine (predicate_agreement h (boundedPredicate bound φ) ρ x).trans ?_
  change (ZFSetUniverseLift.carrierEquiv x ∈
    (show ZFSet.{u} from (universeModel h).denote (weaken bound)
      ((universeModel h).extend (σ := set) (decodeValuation ρ) (ZFSetUniverseLift.carrierEquiv x))) ∧ _) ↔
    ZFSetUniverseLift.carrierEquiv x ∈ ZFSet.sep _ _
  erw [Soundness.denote_weaken, ZFSet.mem_sep]
  rfl

/-- Refining the lifted full carrier by the bounded predicate produces
exactly the lift of the original bounded separated set. -/
theorem bounded_refinementCode_eq_lift (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} (bound : UniverseExpr Γ set) (φ : Formula UniverseSymbol (set :: Γ))
    (ρ : Valuation Γ) :
    refinementCode h (boundedPredicate bound φ) ρ =
      ZFSetUniverseLift.lift (universePredicateSet h bound φ (decodeContext h ρ)) := by
  apply ZFSet.ext
  intro x
  rw [mem_refinementCode, ZFSetUniverseLift.mem_lift]
  constructor
  · rintro ⟨member, hp⟩
    exact ⟨ZFSetUniverseLift.carrierEquiv ⟨x, member⟩,
      (bounded_predicate_agreement h bound φ ρ ⟨x, member⟩).mp hp,
      ZFSetUniverseLift.lift_decode ⟨x, member⟩⟩
  · rintro ⟨y, member, rfl⟩
    refine ⟨(ZFSetUniverseLift.encode y).2,
      (bounded_predicate_agreement h bound φ ρ (ZFSetUniverseLift.encode y)).mpr ?_⟩
    exact Eq.mpr (congrArg (fun z => z ∈ universePredicateSet h bound φ (decodeContext h ρ))
      (ZFSetUniverseLift.decode_encode y)) member

/-! ## Retained proof and dependent-refinement substitution -/

noncomputable def pullCodedSatisfied (h : CofinalInaccessibles.{u})
    {Γ Δ : Ctx Unit} {hypotheses : List (Formula UniverseSymbol Γ)}
    (θ : Subst UniverseSymbol Γ Δ)
    (ρ : CodedSatisfied h (hypotheses.map (HOL.subst θ))) : CodedSatisfied h hypotheses :=
  ⟨substValuation (universeConstants h) θ ρ.1, by
    intro φ member
    have observed := ρ.2 (HOL.subst θ φ) (List.mem_map.mpr ⟨φ, member, rfl⟩)
    rw [universe_substitution] at observed
    exact observed⟩

def elementsEq {a b : ZFSet.{u}} (equal : a = b) : Elements a ≃ Elements b where
  toFun point := ⟨point.1, equal ▸ point.2⟩
  invFun point := ⟨point.1, equal.symm ▸ point.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem proofValue_substitution (h : CofinalInaccessibles.{u})
    {Γ Δ : Ctx Unit} {hypotheses : List (Formula UniverseSymbol Γ)}
    {φ : Formula UniverseSymbol Γ} (proof : ProofSyntax UniverseSymbol hypotheses φ)
    (θ : Subst UniverseSymbol Γ Δ)
    (ρ : CodedSatisfied h (hypotheses.map (HOL.subst θ))) :
    elementsEq (truthFibre_substitution h φ θ ρ.1)
        (proofValue h (ProofSyntax.subst θ proof) ρ) =
      proofValue h proof (pullCodedSatisfied h θ ρ) := by
  apply Subtype.ext
  rfl

theorem refinementCode_substitution (h : CofinalInaccessibles.{u})
    {Γ Δ : Ctx Unit} {A : Ty Unit} (φ : Formula UniverseSymbol (A :: Γ))
    (θ : Subst UniverseSymbol Γ Δ) (ρ : Valuation Δ) :
    refinementCode h (HOL.subst (Subst.lift θ) φ) ρ =
      refinementCode h φ (substValuation (universeConstants h) θ ρ) := by
  apply ZFSet.ext
  intro x
  simp only [mem_refinementCode, universe_substitution, universe_substValuation_lift]

theorem refinementMap_substitution (h : CofinalInaccessibles.{u})
    {Γ Δ : Ctx Unit} {A : Ty Unit} {hypotheses : List (Formula UniverseSymbol Γ)}
    {φ ψ : Formula UniverseSymbol (A :: Γ)}
    (proof : ProofSyntax UniverseSymbol hypotheses (.all (.imp φ ψ)))
    (θ : Subst UniverseSymbol Γ Δ)
    (ρ : CodedSatisfied h (hypotheses.map (HOL.subst θ)))
    (point : Elements (refinementCode h (HOL.subst (Subst.lift θ) φ) ρ.1)) :
    elementsEq (refinementCode_substitution h ψ θ ρ.1)
        (refinementMap h (ProofSyntax.subst θ proof) ρ point) =
      refinementMap h proof (pullCodedSatisfied h θ ρ)
        (elementsEq (refinementCode_substitution h φ θ ρ.1) point) := by
  apply Subtype.ext
  rfl

/-! ## Higher-order proof consumption and changed-predicate controls -/

def functionEta : ClosedFormula UniverseSymbol :=
  .all (.eq (.lam (.app (.var (.vs .vz)) (.var .vz)))
    (.var .vz : UniverseExpr [mapping] mapping))

def functionEtaProof : ProofSyntax UniverseSymbol [] functionEta :=
  .allI (.eta (.var .vz))

noncomputable def noHypotheses (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    (ρ : Valuation Γ) : CodedSatisfied h ([] : List (Formula UniverseSymbol Γ)) :=
  ⟨ρ, by intro φ member; cases member⟩

noncomputable def functionEtaValue (h : CofinalInaccessibles.{u}) :
    Elements (truthFibre h functionEta emptyValuation) :=
  proofValue h functionEtaProof (noHypotheses h emptyValuation)

theorem functionEtaValue_agreement (h : CofinalInaccessibles.{u}) :
    truthFibreEquiv h functionEta emptyValuation (functionEtaValue h) =
      proofSection (universeModel h) (universeFunctionsRespectEqv h)
        functionEtaProof (decodeSatisfied h (noHypotheses h emptyValuation)) :=
  proofValue_agreement h functionEtaProof (noHypotheses h emptyValuation)

def equalsParameter : Formula UniverseSymbol [set, set] :=
  .eq (.var .vz) (.var (.vs .vz))

def discardTrue : ProofSyntax UniverseSymbol []
    (.all (.imp (.and equalsParameter .top) equalsParameter)) :=
  .allI (.impI (.andEL (.hyp ⟨0, by simp⟩)))

noncomputable def emptyParameter : Valuation.{u} [set] :=
  extend emptyValuation ZFSetUniverseLift.carrierEmpty

noncomputable def equalPoint (h : CofinalInaccessibles.{u}) :
    Elements (refinementCode h (.and equalsParameter .top) emptyParameter) := by
  refine ⟨∅, (mem_refinementCode h _ _ ∅).mpr ⟨ZFSetUniverseLift.carrierEmpty.2, ?_⟩⟩
  simp only [equalsParameter, interpret, extend, emptyParameter, holds_truth]
  exact ⟨rfl, trivial⟩

noncomputable def transportedEqualPoint (h : CofinalInaccessibles.{u}) :
    Elements (refinementCode h equalsParameter emptyParameter) :=
  refinementMap h discardTrue (noHypotheses h emptyParameter) (equalPoint h)

theorem transportedEqualPoint_value (h : CofinalInaccessibles.{u}) :
    (transportedEqualPoint h).1 = ∅ := rfl

theorem transportedEqualPoint_square (h : CofinalInaccessibles.{u}) :
    refinementEquiv h equalsParameter emptyParameter (transportedEqualPoint h) =
      refinementMapOfProof (universeModel h) (universeFunctionsRespectEqv h)
        discardTrue (decodeSatisfied h (noHypotheses h emptyParameter))
        (refinementEquiv h (.and equalsParameter .top) emptyParameter (equalPoint h)) :=
  refinementMap_square h discardTrue (noHypotheses h emptyParameter) (equalPoint h)

noncomputable def changedParameter : Valuation.{u} [set] :=
  extend emptyValuation (ZFSetUniverseLift.carrierPower ZFSetUniverseLift.carrierEmpty)

theorem changed_parameter_rejects_point (h : CofinalInaccessibles.{u}) :
    (∅ : ZFSet.{u + 1}) ∉ refinementCode h equalsParameter changedParameter := by
  intro member
  obtain ⟨hm, hp⟩ := (mem_refinementCode h _ _ ∅).mp member
  simp only [equalsParameter, interpret, extend, changedParameter, holds_truth] at hp
  have equality := congrArg Subtype.val hp
  change (∅ : ZFSet.{u + 1}) = ZFSet.powerset ∅ at equality
  have emptyMember : (∅ : ZFSet.{u + 1}) ∈ ZFSet.powerset ∅ :=
    ZFSet.mem_powerset.mpr (ZFSet.empty_subset _)
  rw [← equality] at emptyMember
  exact ZFSet.mem_irrefl _ emptyMember

theorem false_predicate_has_no_point (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    {A : Ty Unit} (ρ : Valuation Γ) :
    refinementCode h (.bot : Formula UniverseSymbol (A :: Γ)) ρ = ∅ := by
  apply ZFSet.ext
  intro x
  simp only [mem_refinementCode, interpret, holds_truth, ZFSet.notMem_empty, exists_false]

theorem false_claim_has_no_proof (h : CofinalInaccessibles.{u}) :
    ¬ Nonempty (ProofSyntax UniverseSymbol universeTheory .bot) := by
  rintro ⟨proof⟩
  exact (universeTheoremSection h proof).down.down

#print axioms formula_agreement
#print axioms decodeContext_substitution
#print axioms truthFibreEquiv
#print axioms proofValue
#print axioms proofValue_agreement
#print axioms truthFibre_substitution
#print axioms refinementCodeEquiv
#print axioms refinementEquiv
#print axioms refinementMap
#print axioms refinementMap_square
#print axioms refinementCode_mem
#print axioms bounded_refinementCode_eq_lift
#print axioms proofValue_substitution
#print axioms refinementCode_substitution
#print axioms refinementMap_substitution
#print axioms functionEtaValue
#print axioms functionEtaValue_agreement
#print axioms transportedEqualPoint_square
#print axioms changed_parameter_rejects_point
#print axioms false_predicate_has_no_point
#print axioms false_claim_has_no_proof

end Mettapedia.Logic.HOL.Embedding.ZFSetHOLProofInterpretation
