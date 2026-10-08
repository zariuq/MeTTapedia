import Mettapedia.GSLT.Topos.PresheafPredicateHeyting
import Mettapedia.GSLT.Topos.PresheafPredicateUniversalQuantifier

/-!
# Predicate assumptions and quantified entailment

A predicate assumption changes the context to its satisfying subfunctor.
Truth after that inclusion is precisely entailment from the assumed
predicate. The resulting implication, disjunction and existential laws retain
that context restriction. Quantifier introduction and elimination use actual
sections or actual image coverage, rather than merely present inhabitants.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.PresheafPredicateAssumptionLogic

open _root_.CategoryTheory

universe u v w
variable {C : Type u} [Category.{v} C] {P Q : C ⥤ Type w}

theorem inclusion_top_iff (assumption consequent : Subfunctor P) :
    consequent.preimage assumption.ι = ⊤ ↔ assumption ≤ consequent := by
  constructor
  · intro restricted world value member
    have holds : (⟨value, member⟩ : assumption.toFunctor.obj world) ∈
        (consequent.preimage assumption.ι).obj world := restricted.symm ▸ trivial
    exact holds
  · intro below
    ext world value
    constructor
    · intro _
      trivial
    · intro _
      exact below world value.property

theorem assumption_holds (assumption : Subfunctor P) :
    assumption.preimage assumption.ι = ⊤ :=
  (inclusion_top_iff assumption assumption).mpr le_rfl

theorem implication_top (assumption consequent : Subfunctor P)
    (restricted : consequent.preimage assumption.ι = ⊤) :
    himpPointwise assumption consequent = ⊤ := by
  rw [himpPointwise_eq_himp, himp_eq_top_iff]
  exact (inclusion_top_iff assumption consequent).mp restricted

theorem predicate_equal (first second : Subfunctor P)
    (firstAssumed : second.preimage first.ι = ⊤)
    (secondAssumed : first.preimage second.ι = ⊤) : first = second :=
  le_antisymm ((inclusion_top_iff first second).mp firstAssumed)
    ((inclusion_top_iff second first).mp secondAssumed)

theorem disjunction_elimination (first second consequent : Subfunctor P)
    (covered : first ⊔ second = ⊤)
    (firstAssumed : consequent.preimage first.ι = ⊤)
    (secondAssumed : consequent.preimage second.ι = ⊤) : consequent = ⊤ := by
  apply le_antisymm le_top
  rw [← covered]
  exact sup_le ((inclusion_top_iff first consequent).mp firstAssumed)
    ((inclusion_top_iff second consequent).mp secondAssumed)

theorem universal_top_iff (arrow : P ⟶ Q) (predicate : Subfunctor P) :
    forallAlong arrow predicate = ⊤ ↔ predicate = ⊤ := by
  constructor
  · intro universal
    apply le_antisymm le_top
    have above : (⊤ : Subfunctor Q) ≤ forallAlong arrow predicate := universal.symm ▸ le_rfl
    have below := (preimage_le_iff_le_forallAlong arrow predicate ⊤).mpr above
    simpa only [preimage_top'] using below
  · intro predicateTop
    rw [predicateTop, forallAlong_top]

theorem universal_section (arrow : P ⟶ Q) (predicate : Subfunctor P)
    (universal : forallAlong arrow predicate = ⊤) (supplied : Q ⟶ P) :
    predicate.preimage supplied = ⊤ := by
  rw [(universal_top_iff arrow predicate).mp universal, preimage_top']

theorem existential_section (arrow : P ⟶ Q) (predicate : Subfunctor P)
    (supplied : Q ⟶ P) (projects : supplied ≫ arrow = 𝟙 Q)
    (holds : predicate.preimage supplied = ⊤) : predicate.image arrow = ⊤ := by
  ext world value
  constructor
  · intro _
    trivial
  · intro _
    have member : supplied.app world value ∈ predicate.obj world := by
      have selected : value ∈ (predicate.preimage supplied).obj world := holds.symm ▸ trivial
      exact selected
    refine ⟨supplied.app world value, member, ?_⟩
    exact ConcreteCategory.congr_hom (NatTrans.congr_app projects world) value

theorem existential_elimination (arrow : P ⟶ Q) (predicate : Subfunctor P)
    (consequent : Subfunctor Q) (covered : predicate.image arrow = ⊤)
    (restricted : (consequent.preimage arrow).preimage predicate.ι = ⊤) : consequent = ⊤ := by
  apply le_antisymm le_top
  rw [← covered]
  exact (Subfunctor.image_le_iff predicate arrow consequent).mpr
    ((inclusion_top_iff predicate (consequent.preimage arrow)).mp restricted)

theorem image_cover_cancel (arrow : P ⟶ Q) (consequent : Subfunctor Q)
    (covered : Subfunctor.range arrow = ⊤)
    (restricted : consequent.preimage arrow = ⊤) : consequent = ⊤ := by
  apply le_antisymm le_top
  rw [← covered, ← Subfunctor.image_top]
  exact (Subfunctor.image_le_iff ⊤ arrow consequent).mpr (restricted.symm ▸ le_rfl)

end Mettapedia.GSLT.Topos.PresheafPredicateAssumptionLogic
