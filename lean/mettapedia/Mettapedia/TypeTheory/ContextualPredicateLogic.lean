import Mettapedia.TypeTheory.ContextualPredicateAssumptions

/-!
# Logical introduction and elimination from local predicate capabilities

Assumed contexts express conditional consequence through their actual
inclusions. Display quantifiers use the two local adjunctions. Existential
elimination needs its coverage premise, and introduction uses an independently
supplied section; no data witness is selected from existential truth.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualPredicateLogic

open Mettapedia.GSLT.Core.ContextualLadder
open ContextualPredicateCapabilities ContextualPredicateAssumptions
open ContextualProductComparison (selfExtend)
open ContextualTypeOperations (wk_selfExtend)

universe c s t m p

variable {C : Cwf.{c, s, t, m}}
variable {doctrine : PredicateDoctrine.{c, s, t, m, p} C}

theorem implication_top (assumptions : AssumptionOperations doctrine)
    {context : C.Ctx} (antecedent consequent : doctrine.Predicate context)
    (branch : doctrine.reindex (assumptions.inclusion antecedent) consequent = ⊤) :
    antecedent ⇨ consequent = ⊤ :=
  himp_eq_top_iff.mpr ((assumptions.consequence antecedent consequent).mp branch)

theorem predicate_equal (assumptions : AssumptionOperations doctrine)
    {context : C.Ctx} (first second : doctrine.Predicate context)
    (forward : doctrine.reindex (assumptions.inclusion first) second = ⊤)
    (reverse : doctrine.reindex (assumptions.inclusion second) first = ⊤) :
    first = second :=
  le_antisymm ((assumptions.consequence first second).mp forward)
    ((assumptions.consequence second first).mp reverse)

theorem disjunction_elimination (assumptions : AssumptionOperations doctrine)
    {context : C.Ctx} (first second consequent : doctrine.Predicate context)
    (covered : first ⊔ second = ⊤)
    (firstBranch : doctrine.reindex (assumptions.inclusion first) consequent = ⊤)
    (secondBranch : doctrine.reindex (assumptions.inclusion second) consequent = ⊤) :
    consequent = ⊤ := by
  apply top_le_iff.mp
  rw [← covered]
  exact sup_le ((assumptions.consequence first consequent).mp firstBranch)
    ((assumptions.consequence second consequent).mp secondBranch)

theorem universal_top (doctrine : PredicateDoctrine.{c, s, t, m, p} C)
    {context : C.Ctx} (type : C.Ty context) : doctrine.all type ⊤ = ⊤ :=
  (universal_truth_iff type ⊤).mpr rfl

theorem universal_section (doctrine : PredicateDoctrine.{c, s, t, m, p} C)
    {context : C.Ctx} (type : C.Ty context)
    (predicate : doctrine.Predicate (C.ext context type)) (supplied : C.Tm context type)
    (covered : doctrine.all type predicate = ⊤) :
    doctrine.reindex (selfExtend C supplied) predicate = ⊤ := by
  rw [(universal_truth_iff type predicate).mp covered]
  exact map_top (doctrine.reindex (selfExtend C supplied))

theorem existential_section (doctrine : PredicateDoctrine.{c, s, t, m, p} C)
    {context : C.Ctx} (type : C.Ty context)
    (predicate : doctrine.Predicate (C.ext context type)) (supplied : C.Tm context type)
    (guard : doctrine.reindex (selfExtend C supplied) predicate = ⊤) :
    doctrine.some type predicate = ⊤ := by
  have unit : predicate ≤ doctrine.reindex (C.wk type) (doctrine.some type predicate) :=
    (doctrine.some_adjunction type predicate (doctrine.some type predicate)).mp le_rfl
  have transported := OrderHomClass.mono (doctrine.reindex (selfExtend C supplied)) unit
  rw [guard, ← doctrine.reindex_comp, wk_selfExtend, doctrine.reindex_id] at transported
  exact top_le_iff.mp transported

theorem existential_elimination (assumptions : AssumptionOperations doctrine)
    {context : C.Ctx} (type : C.Ty context)
    (predicate : doctrine.Predicate (C.ext context type)) (consequent : doctrine.Predicate context)
    (covered : doctrine.some type predicate = ⊤)
    (branch : doctrine.reindex (assumptions.inclusion predicate)
      (doctrine.reindex (C.wk type) consequent) = ⊤) :
    consequent = ⊤ := by
  have body : predicate ≤ doctrine.reindex (C.wk type) consequent :=
    (assumptions.consequence predicate (doctrine.reindex (C.wk type) consequent)).mp branch
  have below : doctrine.some type predicate ≤ consequent :=
    (doctrine.some_adjunction type predicate consequent).mpr body
  rw [covered] at below
  exact top_le_iff.mp below

theorem image_cover_cancel (doctrine : PredicateDoctrine.{c, s, t, m, p} C)
    {context : C.Ctx} (type : C.Ty context) (consequent : doctrine.Predicate context)
    (covered : doctrine.some type ⊤ = ⊤)
    (restricted : doctrine.reindex (C.wk type) consequent = ⊤) :
    consequent = ⊤ := by
  have body : (⊤ : doctrine.Predicate (C.ext context type)) ≤
      doctrine.reindex (C.wk type) consequent := le_of_eq restricted.symm
  have below := (doctrine.some_adjunction type ⊤ consequent).mpr body
  rw [covered] at below
  exact top_le_iff.mp below

theorem image_section (doctrine : PredicateDoctrine.{c, s, t, m, p} C)
    {context : C.Ctx} (type : C.Ty context) (supplied : C.Tm context type) :
    doctrine.some type ⊤ = ⊤ :=
  existential_section doctrine type ⊤ supplied (map_top _)

end Mettapedia.TypeTheory.ContextualPredicateLogic
