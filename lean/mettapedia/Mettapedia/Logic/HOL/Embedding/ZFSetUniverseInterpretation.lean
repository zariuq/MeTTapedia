import Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure
import Mettapedia.Logic.HOL.ConstantSubstitutionSemantics
import Mettapedia.Logic.HOL.ImpredicativeConnectives

/-!
# A universe-operation extension of the same set/HOL model

The new constant denotes the least internal closed universe constructed in
`ZFSetUniverseClosure`. The original set signature is retained through an
actual constant-to-term interpretation whose model reduct equals the prior
ZFSet Henkin model. All four universe-operation laws are actual HOL formulas.

The construction is relative to cofinally many inaccessible cardinals in the
fixed set level. This is a sufficient explicit model assumption, not a new
Lean axiom and not a theorem asserting that such a cofinal family exists.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.Embedding.ZFSetUniverseInterpretation

open ZFSetHenkinInterpretation ZFSetUniverseClosure
open HenkinDependentFamilyInterpretation HenkinPredicateFamilyInterpretation

universe u

/-- Conservative signature extension by one typed set operation. Whether
adding its mathematical assumptions is conservative is a separate claim. -/
inductive UniverseSymbol : Ty Unit → Type where
  | core {A : Ty Unit} : Symbol A → UniverseSymbol A
  | universe : UniverseSymbol mapping

abbrev UniverseExpr (Γ : Ctx Unit) (A : Ty Unit) := Term UniverseSymbol Γ A

noncomputable def constant (h : CofinalInaccessibles.{u}) :
    {A : Ty Unit} → UniverseSymbol A → Ty.denote.{0, u + 1} carrier.{u} A
  | _, .core c => denoteSymbol c
  | _, .universe => univOf h

noncomputable def universeModel (h : CofinalInaccessibles.{u}) :
    HenkinModel.{0, 0, u + 1} Unit UniverseSymbol :=
  HenkinModel.standard carrier (constant h)

def coreDefinition {A : Ty Unit} (c : Symbol A) : ClosedTerm UniverseSymbol A :=
  .const (.core c)

/-- The old model is exactly the constant-substitution reduct. Its
mathematical carriers and set operations have not been replaced. -/
theorem core_reduct (h : CofinalInaccessibles.{u}) :
    HenkinModel.constantSubstitutionReduct coreDefinition (universeModel h) =
      model.{u} := rfl

def embed {Γ : Ctx Unit} {A : Ty Unit} (t : Expr Γ A) : UniverseExpr Γ A :=
  substConst coreDefinition t

theorem denote_embed (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} {A : Ty Unit} (t : Expr Γ A)
    (valuation : (universeModel h).Valuation Γ) :
    (universeModel h).denote (embed t) valuation = model.denote t valuation := by
  exact HenkinModel.denote_substConst coreDefinition (universeModel h) t valuation

theorem models_embed (h : CofinalInaccessibles.{u}) (φ : ClosedFormula Symbol) :
    (universeModel h).models (embed φ) ↔ model.{u}.models φ := by
  exact HenkinModel.models_substConst coreDefinition (universeModel h) φ

def inSet {Γ : Ctx Unit} (x a : UniverseExpr Γ set) : Formula UniverseSymbol Γ :=
  .app (.app (.const (.core .member)) x) a

def universeOf {Γ : Ctx Unit} (a : UniverseExpr Γ set) : UniverseExpr Γ set :=
  .app (.const .universe) a

def subsetFormula {Γ : Ctx Unit} (a b : UniverseExpr Γ set) :
    Formula UniverseSymbol Γ :=
  .all (.imp (inSet (.var .vz) (weaken a)) (inSet (.var .vz) (weaken b)))

def transitiveFormula {Γ : Ctx Unit} (U : UniverseExpr Γ set) :
    Formula UniverseSymbol Γ :=
  .all (.imp (inSet (.var .vz) (weaken U))
    (subsetFormula (.var .vz) (weaken U)))

def unionClosedFormula {Γ : Ctx Unit} (U : UniverseExpr Γ set) :
    Formula UniverseSymbol Γ :=
  .all (.imp (inSet (.var .vz) (weaken U))
    (inSet (.app (.const (.core .union)) (.var .vz)) (weaken U)))

def powerClosedFormula {Γ : Ctx Unit} (U : UniverseExpr Γ set) :
    Formula UniverseSymbol Γ :=
  .all (.imp (inSet (.var .vz) (weaken U))
    (inSet (.app (.const (.core .power)) (.var .vz)) (weaken U)))

def replacementClosedFormula {Γ : Ctx Unit} (U : UniverseExpr Γ set) :
    Formula UniverseSymbol Γ :=
  .all (.imp (inSet (.var .vz) (weaken U))
    (.all (.imp
      (.all (.imp (inSet (.var .vz) (.var (.vs (.vs .vz))))
        (inSet (.app (.var (.vs .vz)) (.var .vz)) (weaken (weaken (weaken U))))))
      (inSet (.app (.app (.const (.core .replace)) (.var (.vs .vz))) (.var .vz))
        (weaken (weaken U))))))

def closureFormula {Γ : Ctx Unit} (U : UniverseExpr Γ set) :
    Formula UniverseSymbol Γ :=
  .and (unionClosedFormula U)
    (.and (powerClosedFormula U) (replacementClosedFormula U))

theorem denote_inSet (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    (x a : UniverseExpr Γ set) (ρ : (universeModel h).Valuation Γ) :
    ((universeModel h).denote (inSet x a) ρ).down ↔
      (show ZFSet.{u} from (universeModel h).denote x ρ) ∈
        (show ZFSet.{u} from (universeModel h).denote a ρ) := Iff.rfl

theorem denote_subsetFormula (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    (a b : UniverseExpr Γ set) (ρ : (universeModel h).Valuation Γ) :
    ((universeModel h).denote (subsetFormula a b) ρ).down ↔
      (show ZFSet.{u} from (universeModel h).denote a ρ) ⊆
        (show ZFSet.{u} from (universeModel h).denote b ρ) := by
  constructor
  · intro holds x hx
    have q := holds x trivial
    change _ → _ at q
    erw [denote_inSet, Soundness.denote_weaken] at q
    erw [denote_inSet, Soundness.denote_weaken] at q
    exact q hx
  · intro hab x _ hx
    erw [denote_inSet, Soundness.denote_weaken] at hx
    erw [denote_inSet, Soundness.denote_weaken]
    exact hab hx

theorem denote_transitiveFormula (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    (U : UniverseExpr Γ set) (ρ : (universeModel h).Valuation Γ) :
    ((universeModel h).denote (transitiveFormula U) ρ).down ↔
      ZFSet.IsTransitive ((universeModel h).denote U ρ) := by
  constructor
  · intro holds x hx
    have q := holds x trivial
    change _ → _ at q
    erw [denote_inSet, Soundness.denote_weaken] at q
    have hs := q hx
    erw [denote_subsetFormula, Soundness.denote_weaken] at hs
    exact hs
  · intro hu x _ hx
    erw [denote_inSet, Soundness.denote_weaken] at hx
    erw [denote_subsetFormula, Soundness.denote_weaken]
    exact hu x hx

theorem denote_unionClosedFormula (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    (U : UniverseExpr Γ set) (ρ : (universeModel h).Valuation Γ) :
    ((universeModel h).denote (unionClosedFormula U) ρ).down ↔
      ∀ a : ZFSet.{u}, a ∈ (show ZFSet.{u} from (universeModel h).denote U ρ) →
        ZFSet.sUnion a ∈ (show ZFSet.{u} from (universeModel h).denote U ρ) := by
  constructor
  · intro holds a ha
    have q := holds a trivial
    change _ → _ at q
    erw [denote_inSet, Soundness.denote_weaken] at q
    have hs := q ha
    erw [denote_inSet, Soundness.denote_weaken] at hs
    exact hs
  · intro hu a _ ha
    erw [denote_inSet, Soundness.denote_weaken] at ha
    erw [denote_inSet, Soundness.denote_weaken]
    exact hu a ha

theorem denote_powerClosedFormula (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    (U : UniverseExpr Γ set) (ρ : (universeModel h).Valuation Γ) :
    ((universeModel h).denote (powerClosedFormula U) ρ).down ↔
      ∀ a : ZFSet.{u}, a ∈ (show ZFSet.{u} from (universeModel h).denote U ρ) →
        ZFSet.powerset a ∈ (show ZFSet.{u} from (universeModel h).denote U ρ) := by
  constructor
  · intro holds a ha
    have q := holds a trivial
    change _ → _ at q
    erw [denote_inSet, Soundness.denote_weaken] at q
    have hs := q ha
    erw [denote_inSet, Soundness.denote_weaken] at hs
    exact hs
  · intro hu a _ ha
    erw [denote_inSet, Soundness.denote_weaken] at ha
    erw [denote_inSet, Soundness.denote_weaken]
    exact hu a ha

theorem denote_replacementClosedFormula (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    (U : UniverseExpr Γ set) (ρ : (universeModel h).Valuation Γ) :
    ((universeModel h).denote (replacementClosedFormula U) ρ).down ↔
      ∀ a : ZFSet.{u}, a ∈ (show ZFSet.{u} from (universeModel h).denote U ρ) →
        ∀ f : ZFSet.{u} → ZFSet.{u},
          (∀ x ∈ a, f x ∈ (show ZFSet.{u} from (universeModel h).denote U ρ)) →
          replacement a f ∈ (show ZFSet.{u} from (universeModel h).denote U ρ) := by
  constructor
  · intro holds a ha f hf
    have q := holds a trivial
    change _ → _ at q
    erw [denote_inSet, Soundness.denote_weaken] at q
    have qr := q ha f trivial
    change _ → _ at qr
    have hf' : ∀ x : ZFSet.{u}, True →
        ((universeModel h).denote
          (.imp (inSet (.var .vz) (.var (.vs (.vs .vz))))
            (inSet (.app (.var (.vs .vz)) (.var .vz))
              (weaken (weaken (weaken U)))))
          ((universeModel h).extend (σ := set)
            ((universeModel h).extend (σ := mapping)
              ((universeModel h).extend (σ := set) ρ a) f) x)).down := by
      intro x _ hx
      erw [denote_inSet] at hx
      erw [denote_inSet, Soundness.denote_weaken,
        Soundness.denote_weaken, Soundness.denote_weaken]
      exact hf x hx
    have hr := qr hf'
    erw [denote_inSet, Soundness.denote_weaken, Soundness.denote_weaken] at hr
    exact hr
  · intro hu a _ ha f _ hf
    erw [denote_inSet, Soundness.denote_weaken] at ha
    erw [denote_inSet, Soundness.denote_weaken, Soundness.denote_weaken]
    apply hu a ha f
    intro x hx
    have q := hf x trivial
    change _ → _ at q
    erw [denote_inSet] at q
    have hr := q hx
    erw [denote_inSet, Soundness.denote_weaken,
      Soundness.denote_weaken, Soundness.denote_weaken] at hr
    exact hr

theorem denote_closed (h : CofinalInaccessibles.{u}) {Γ : Ctx Unit}
    (U : UniverseExpr Γ set) (ρ : (universeModel h).Valuation Γ) :
    (((universeModel h).denote (transitiveFormula U) ρ).down ∧
      ((universeModel h).denote (closureFormula U) ρ).down) ↔
      Closed ((universeModel h).denote U ρ) := by
  change (_ ∧ _ ∧ _ ∧ _) ↔ _
  rw [denote_transitiveFormula, denote_unionClosedFormula,
    denote_powerClosedFormula, denote_replacementClosedFormula]
  constructor
  · rintro ⟨ht, hu, hp, hr⟩
    exact ⟨ht, fun ha => hu _ ha, fun ha => hp _ ha, fun ha => hr _ ha⟩
  · intro hc
    exact ⟨hc.transitive, fun _ ha => hc.union_mem ha,
      fun _ ha => hc.power_mem ha, fun _ ha => hc.replacement_mem ha⟩

def universeIn : ClosedFormula UniverseSymbol :=
  .all (inSet (.var .vz) (universeOf (.var .vz)))

def universeTransitive : ClosedFormula UniverseSymbol :=
  .all (transitiveFormula (universeOf (.var .vz)))

def universeClosed : ClosedFormula UniverseSymbol :=
  .all (closureFormula (universeOf (.var .vz)))

def universeMinimal : ClosedFormula UniverseSymbol :=
  .all (.all (.imp (inSet (.var (.vs .vz)) (.var .vz))
    (.imp (transitiveFormula (.var .vz))
      (.imp (closureFormula (.var .vz))
        (subsetFormula (universeOf (.var (.vs .vz))) (.var .vz))))))

theorem universeIn_valid (h : CofinalInaccessibles.{u}) :
    (universeModel h).models universeIn := by
  intro N _
  exact mem_univOf h N

theorem universeTransitive_valid (h : CofinalInaccessibles.{u}) :
    (universeModel h).models universeTransitive := by
  intro N _
  apply (denote_transitiveFormula h _ _).mpr
  exact (univOf_closed h N).transitive

theorem universeClosed_valid (h : CofinalInaccessibles.{u}) :
    (universeModel h).models universeClosed := by
  intro N _
  exact ((denote_closed h (Γ := [set]) (universeOf (.var .vz))
    ((universeModel h).extend (σ := set)
      (fun {A} (v : Var [] A) => nomatch v) N)).mpr
      (univOf_closed h N)).2

theorem universeMinimal_valid (h : CofinalInaccessibles.{u}) :
    (universeModel h).models universeMinimal := by
  intro N _ U _ hN ht hc
  apply (denote_subsetFormula h _ _ _).mpr
  exact univOf_minimal h hN ((denote_closed h _ _).mp ⟨ht, hc⟩)

/-! ## The validated theory and dependent consumption -/

/-- The seven set formulas already interpreted, followed by exactly the
four universe-operation laws. This is not an imported source preamble. -/
def universeTheory : List (ClosedFormula UniverseSymbol) :=
  ZFSetHenkinInterpretation.theory.map embed ++
    [universeIn, universeTransitive, universeClosed, universeMinimal]

theorem universeTheory_valid (h : CofinalInaccessibles.{u})
    (φ : ClosedFormula UniverseSymbol) (hφ : φ ∈ universeTheory) :
    (universeModel h).models φ := by
  rcases List.mem_append.mp hφ with hcore | huniverse
  · obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp hcore
    exact (models_embed h ψ).mpr (ZFSetHenkinInterpretation.theory_valid ψ hψ)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at huniverse
    rcases huniverse with rfl | rfl | rfl | rfl
    · exact universeIn_valid h
    · exact universeTransitive_valid h
    · exact universeClosed_valid h
    · exact universeMinimal_valid h

/-- The same eleven set/universe laws survive elimination of every derived
logical connective. The explicit inaccessible-cardinal assumption is retained;
logical expansion neither establishes nor strengthens the source axioms. -/
theorem expanded_universeTheory_valid (h : CofinalInaccessibles.{u})
    (φ : ClosedFormula UniverseSymbol)
    (member : φ ∈ universeTheory.map ImpredicativeConnectives.expand) :
    (universeModel h).models φ := by
  obtain ⟨source, source_mem, rfl⟩ := List.mem_map.mp member
  exact (ImpredicativeConnectives.models_expand _ _).mpr
    (universeTheory_valid h source source_mem)

theorem universeFullDomains (h : CofinalInaccessibles.{u}) :
    (universeModel h).FullDomains :=
  HenkinModel.fullDomains_standard carrier (constant h)

theorem universeFunctionsRespectEqv (h : CofinalInaccessibles.{u}) :
    (universeModel h).FunctionsRespectEqv :=
  (universeModel h).functionsRespectEqv_of_fullDomains (universeFullDomains h)

noncomputable def universeEmptyContext (h : CofinalInaccessibles.{u}) :
    AdmissibleContext (universeModel h) [] :=
  ⟨(fun v => nomatch v), by intro A v; nomatch v⟩

/-- Actual satisfaction of the combined hypotheses, not an adequacy field
required of a prospective interpretation. -/
noncomputable def satisfiedUniverseTheory (h : CofinalInaccessibles.{u}) :
    SatisfiedContext (universeModel h) universeTheory :=
  ⟨universeEmptyContext h, by
    intro φ hφ
    refine Eq.mp ?_ (universeTheory_valid h φ hφ)
    unfold HenkinModel.models PreModel.models
    congr 2
    funext A v
    nomatch v⟩

/-- A retained proof using both set and universe laws gives a dependent
section in the very same Henkin interpretation. -/
noncomputable def universeTheoremSection (h : CofinalInaccessibles.{u})
    {φ : ClosedFormula UniverseSymbol}
    (proof : ProofSyntax UniverseSymbol universeTheory φ) :
    truthFamily (universeModel h) φ (universeEmptyContext h) :=
  proofSection (universeModel h) (universeFunctionsRespectEqv h)
    proof (satisfiedUniverseTheory h)

/-- Separation permits arbitrary formulas of the extended language,
including formulas that themselves mention the universe operation. -/
noncomputable def universePredicateSet (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} (bound : UniverseExpr Γ set)
    (φ : Formula UniverseSymbol (set :: Γ))
    (valuation : AdmissibleContext (universeModel h) Γ) : ZFSet.{u} :=
  ZFSet.sep (fun x => ((universeModel h).denote φ
    ((universeModel h).extend (σ := set) valuation.1 x)).down)
      ((universeModel h).denote bound valuation.1)

theorem universePredicateSet_mem (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} (bound : UniverseExpr Γ set)
    (φ : Formula UniverseSymbol (set :: Γ))
    (valuation : AdmissibleContext (universeModel h) Γ) :
    universePredicateSet h bound φ valuation ∈
      univOf h ((universeModel h).denote bound valuation.1) :=
  (univOf_closed h _).separation_mem (mem_univOf h _) _

/-- Extending the signature does not alter an existing separated set. -/
theorem universePredicateSet_embed (h : CofinalInaccessibles.{u})
    {Γ : Ctx Unit} (bound : Expr Γ set) (φ : Formula Symbol (set :: Γ))
    (valuation : AdmissibleContext model.{u} Γ) :
    universePredicateSet h (embed bound) (embed φ) valuation =
      predicateSet bound φ valuation := by
  unfold universePredicateSet predicateSet
  rw [denote_embed]
  congr 1
  funext x
  rw [denote_embed]
  rfl

/-! ## Boundary controls -/

def universeIdempotent : ClosedFormula UniverseSymbol :=
  .all (.eq (universeOf (universeOf (.var .vz))) (universeOf (.var .vz)))

/-- Containment of a parameter is membership, not mere subset closure.
Consequently the universe operation cannot be idempotent. -/
theorem universeIdempotent_false (h : CofinalInaccessibles.{u}) :
    ¬ (universeModel h).models universeIdempotent := by
  intro holds
  exact univOf_not_idempotent h ∅ (holds (∅ : ZFSet.{u}) trivial)

theorem embedded_universalSet_false (h : CofinalInaccessibles.{u}) :
    ¬ (universeModel h).models (embed universalSet) :=
  fun holds => universalSet_false ((models_embed h universalSet).mp holds)

/-- The interpreted universe assumptions cannot derive a universal set. -/
theorem universeTheory_no_universal_set (h : CofinalInaccessibles.{u}) :
    ¬ Nonempty (ProofSyntax UniverseSymbol universeTheory (embed universalSet)) := by
  rintro ⟨proof⟩
  exact embedded_universalSet_false h (universeTheoremSection h proof).down.down

#print axioms core_reduct
#print axioms universeIn_valid
#print axioms universeTransitive_valid
#print axioms universeClosed_valid
#print axioms universeMinimal_valid
#print axioms universeTheory_valid
#print axioms expanded_universeTheory_valid
#print axioms universeTheoremSection
#print axioms universePredicateSet_mem
#print axioms universePredicateSet_embed
#print axioms universeIdempotent_false
#print axioms embedded_universalSet_false
#print axioms universeTheory_no_universal_set

end Mettapedia.Logic.HOL.Embedding.ZFSetUniverseInterpretation
