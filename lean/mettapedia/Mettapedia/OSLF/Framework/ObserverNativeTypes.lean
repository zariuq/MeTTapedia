import Mettapedia.GSLT.Logic.ObserverPresheafControls
import Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes
import Mettapedia.OSLF.PresheafNativeType.InternalLanguage

/-!
# Native types relative to an observer, and over the observer site

For an admissible class `D`, the **observed GSLT** `observedGSLT obs D` has the
terms and reductions of `S` and the `D`-relative equivalence as its equations.
Its generated OSLF is the OSLF that the observers of `D` can use.

* **Native predicates are stage predicates.**  The native predicates of the
  observed GSLT are exactly the predicates on the stage of `D` in the observer
  presheaf (`nativeStageOrderIso`, an instance of `equationPredicatesOrderIso`).
  Agreement on all of them is exactly the `D`-relative equivalence
  (`observedNativeTypes_equivalent_iff`), and every Hennessy–Milner formula of the
  saturated system of `D` is one of them (`formulaObservedPredicate`).
* **OSLF change of base along forgetting is the hyperdoctrine of the observer
  presheaf.**  For `A ≤ B` the identity on terms is an equation-respecting map from
  the `B`-observed to the `A`-observed GSLT (`forgetMap`).  Its OSLF pullback,
  direct image and universal image are reindexing, existential image and universal
  image along forgetting (`nativeStage_pullback`, `nativeStage_directImage`,
  `nativeStage_universalImage`), so OSLF's own adjunctions
  `directImage_pullback_galois` and `pullback_universalImage_galois` are the
  hyperdoctrine adjunctions of the observer presheaf.
* **The step modalities over the site.**  Pullback along forgetting commutes with
  the OSLF step-future `◇` (`forget_pullback_diamond`) and only laxly with the
  step-past `□` (`forget_pullback_box_le`); the oracle tower shows the lax
  inequality can be strict (`box_not_natural`).
* **Native types over the observer site.**  In the presheaf topos over the
  observer lattice, a predicate on the observer presheaf is a subfunctor.  The
  subfunctors are order-isomorphic to the families of stage predicates closed
  under forgetting (`subfunctorOrderIso`): what holds at a finer stage holds at
  every coarser one.  The Williams–Stay indexed adjoints and Beck–Chevalley
  condition apply over this site (`observerSite_indexedAdjoints`,
  `observerSite_beckChevalley`); unlike the stagewise Beck–Chevalley condition
  along forgetting, which is amalgamation and can fail, they hold unconditionally.
* **Carving is restriction to a sub-site.**  Restricting forgetting-closed
  families to a set of observer classes has a left adjoint, the smallest
  extension, and a right adjoint, the largest extension, and restricting either
  extension gives the family back (`smallestExtension_subset_iff`,
  `subset_largestExtension_iff`, `restrict_smallestExtension`,
  `restrict_largestExtension`).  The two extensions disagree outside the sub-site
  in general (`extensions_differ`): a carve loses the stages it drops.
* **Controls.**  Images of a term predicate form a forgetting-closed family for
  every predicate (`imageFamily_forgettingClosed`); interiors do not
  (`interiorFamily_not_forgettingClosed`, on the oracle tower).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.ObserverNativeTypes

open _root_.CategoryTheory Opposite
open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.GSLT.AdmissibleContextCongruence.AdmissibleClass
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.OSLF.Framework.DerivedModalities

universe uS uContext uRule uAtom

variable {S : GSLT.{uS}} {rules : ContextualRules.{uContext, uRule} S}
variable (observations : ContextualRules.Observations.{uAtom} S)

/-! ## The observed GSLT -/

/-- **The GSLT seen by the observers of `D`**: the terms and reductions of `S`,
with the `D`-relative equivalence as equations and reductions closed under
it. -/
def observedGSLT (D : AdmissibleClass rules) : GSLT.{uS} where
  Term := S.Term
  equations := (D.saturated observations).behavioralSetoid
  rewrites source target :=
    ∃ target', S.Step source target' ∧ D.RelEquiv observations target' target
  rewrites_resp_left := by
    rintro source source' target related ⟨target', step, targetRelated⟩
    obtain ⟨target'', step', related'⟩ :=
      (D.isReductionBisimulation_relEquiv observations).1.1 related step
    exact ⟨target, ⟨target'', step',
      D.relEquiv_trans observations (D.relEquiv_symm observations related') targetRelated⟩,
      D.relEquiv_refl observations target⟩
  rewrites_resp_right := by
    rintro source target target'' ⟨target', step, targetRelated⟩ related
    exact ⟨target', step, D.relEquiv_trans observations targetRelated related⟩

variable {observations}

theorem observedGSLT_equiv_iff {D : AdmissibleClass rules} {left right : S.Term} :
    (observedGSLT observations D).Equiv left right ↔ D.RelEquiv observations left right :=
  Iff.rfl

theorem observedGSLT_step_iff {D : AdmissibleClass rules} {source target : S.Term} :
    (observedGSLT observations D).Step source target ↔
      ∃ target', S.Step source target' ∧ D.RelEquiv observations target' target :=
  Iff.rfl

variable (observations)

/-- **The native predicates of the observed GSLT are the stage predicates.** -/
def nativeStageOrderIso (D : AdmissibleClass rules) :
    EquationPredicate (observedGSLT observations D) ≃o (Stage observations D → Prop) :=
  equationPredicatesOrderIso (observedGSLT observations D)

theorem nativeStageOrderIso_stageClass (D : AdmissibleClass rules)
    (φ : EquationPredicate (observedGSLT observations D)) (term : S.Term) :
    nativeStageOrderIso observations D φ (stageClass observations D term) ↔ φ.1 term :=
  Iff.rfl

/-- **Agreement on every native predicate of the observed GSLT is exactly the
relative equivalence.** -/
theorem observedPredicates_equivalent_iff (D : AdmissibleClass rules) (left right : S.Term) :
    (∀ φ : EquationPredicate (observedGSLT observations D), φ.1 left ↔ φ.1 right) ↔
      D.RelEquiv observations left right := by
  constructor
  · intro agree
    let classOf : EquationPredicate (observedGSLT observations D) :=
      ⟨fun term => D.RelEquiv observations term left, fun first second related =>
        ⟨fun firstLeft => D.relEquiv_trans observations (D.relEquiv_symm observations related) firstLeft,
          fun secondLeft => D.relEquiv_trans observations related secondLeft⟩⟩
    exact D.relEquiv_symm observations ((agree classOf).mp (D.relEquiv_refl observations left))
  · intro related φ
    exact φ.2 related

/-- The same statement through the generated OSLF of the observed GSLT
(`HennessyMilnerNativeTypes.allNativeTypes_equivalent_iff_equiv`). -/
theorem observedNativeTypes_equivalent_iff (D : AdmissibleClass rules) (left right : S.Term) :
    (∀ nativeType : GSLTNativeType (observedGSLT observations D),
      ((gsltOSLF (observedGSLT observations D)).satisfies (S := ()) left nativeType.pred ↔
       (gsltOSLF (observedGSLT observations D)).satisfies (S := ()) right nativeType.pred)) ↔
      D.RelEquiv observations left right :=
  HennessyMilnerNativeTypes.allNativeTypes_equivalent_iff_equiv (S := observedGSLT observations D)
    left right

/-- A Hennessy–Milner formula of the saturated system of `D` denotes a native
predicate of the `D`-observed GSLT. -/
def formulaObservedPredicate (D : AdmissibleClass rules)
    (formula : Formula (D.saturated observations).Atom (D.saturated observations).Label) :
    EquationPredicate (observedGSLT observations D) :=
  invariantPredicate (observedGSLT observations D) ((D.saturated observations).sat formula)
    fun _ _ related => (D.saturated observations).logicallyEquivalent_of_bisimilar related formula

/-- Its satisfaction is Hennessy–Milner satisfaction, and it is the generated native
type of the same formula over `S` (`HennessyMilnerNativeTypes.formulaNativeType`). -/
theorem formulaObservedPredicate_apply (D : AdmissibleClass rules)
    (formula : Formula (D.saturated observations).Atom (D.saturated observations).Label)
    (term : S.Term) :
    (formulaObservedPredicate observations D formula).1 term ↔
      (gsltOSLF S).satisfies (S := ()) term
        (HennessyMilnerNativeTypes.formulaNativeType (D.saturated observations) formula).pred :=
  Iff.rfl

/-! ## Forgetting as an equation-respecting map -/

/-- For `A ≤ B`, the identity on terms respects the equations from the
`B`-observed GSLT to the `A`-observed GSLT. -/
def forgetMap {A B : AdmissibleClass rules} (le : A ≤ B) :
    EquationRespectingMap (observedGSLT observations B) (observedGSLT observations A) where
  toFun := id
  map_equiv := fun related => AdmissibleClass.relEquiv_antitone observations le related

/-- On classes, the forgetting map is the restriction of the observer presheaf. -/
theorem forgetMap_onClasses {A B : AdmissibleClass rules} (le : A ≤ B) :
    (forgetMap observations le).onClasses = restrict observations le :=
  rfl

/-- **OSLF pullback along forgetting is reindexing.** -/
theorem nativeStage_pullback {A B : AdmissibleClass rules} (le : A ≤ B)
    (φ : EquationPredicate (observedGSLT observations A)) :
    (nativeStageOrderIso observations B ((forgetMap observations le).pullback φ) :
        Set (Stage observations B)) =
      reindex observations le (nativeStageOrderIso observations A φ) := by
  funext x
  induction x using Quotient.inductionOn with
  | _ term => rfl

/-- **OSLF direct image along forgetting is existential image.** -/
theorem nativeStage_directImage {A B : AdmissibleClass rules} (le : A ≤ B)
    (ψ : EquationPredicate (observedGSLT observations B)) :
    (nativeStageOrderIso observations A ((forgetMap observations le).directImage ψ) :
        Set (Stage observations A)) =
      existsAlong observations le (nativeStageOrderIso observations B ψ) := by
  funext x
  induction x using Quotient.inductionOn with
  | _ term =>
    apply propext
    change (∃ fine, restrict observations le fine = stageClass observations A term ∧
        nativeStageOrderIso observations B ψ fine) ↔
      ∃ fine, nativeStageOrderIso observations B ψ fine ∧
        restrict observations le fine = stageClass observations A term
    exact exists_congr fun _ => and_comm

/-- **OSLF universal image along forgetting is universal image.** -/
theorem nativeStage_universalImage {A B : AdmissibleClass rules} (le : A ≤ B)
    (ψ : EquationPredicate (observedGSLT observations B)) :
    (nativeStageOrderIso observations A ((forgetMap observations le).universalImage ψ) :
        Set (Stage observations A)) =
      forallAlong observations le (nativeStageOrderIso observations B ψ) := by
  funext x
  induction x using Quotient.inductionOn with
  | _ term => rfl

/-- **The OSLF adjunctions along forgetting are the hyperdoctrine adjunctions of the
observer presheaf**: direct image, pullback and universal image of OSLF's
change of base along `forgetMap`. -/
theorem forget_adjunctions {A B : AdmissibleClass rules} (le : A ≤ B) :
    GaloisConnection (forgetMap observations le).directImage (forgetMap observations le).pullback ∧
      GaloisConnection (forgetMap observations le).pullback
        (forgetMap observations le).universalImage :=
  ⟨(forgetMap observations le).directImage_pullback_galois,
    (forgetMap observations le).pullback_universalImage_galois⟩

/-- Pullback along forgetting keeps a predicate's reading on terms. -/
theorem forget_pullback_apply {A B : AdmissibleClass rules} (le : A ≤ B)
    (φ : EquationPredicate (observedGSLT observations A)) (term : S.Term) :
    ((forgetMap observations le).pullback φ).1 term ↔ φ.1 term :=
  Iff.rfl

/-! ## The step modalities along forgetting -/

theorem observed_diamond_apply (D : AdmissibleClass rules)
    (φ : EquationPredicate (observedGSLT observations D)) (source : S.Term) :
    (semanticDiamond (observedGSLT observations D) φ).1 source ↔
      ∃ target, S.Step source target ∧ φ.1 target := by
  refine (gsltDiamond_spec (observedGSLT observations D) φ.1 source).trans ?_
  constructor
  · rintro ⟨target, ⟨target', step, related⟩, holds⟩
    exact ⟨target', step, (φ.2 related).mpr holds⟩
  · rintro ⟨target, step, holds⟩
    exact ⟨target, ⟨target, step, D.relEquiv_refl observations target⟩, holds⟩

theorem observed_box_apply (D : AdmissibleClass rules)
    (φ : EquationPredicate (observedGSLT observations D)) (target : S.Term) :
    (semanticBox (observedGSLT observations D) φ).1 target ↔
      ∀ source target', S.Step source target' → D.RelEquiv observations target' target →
        φ.1 source := by
  refine (gsltBox_spec (observedGSLT observations D) φ.1 target).trans ?_
  constructor
  · intro holds source target' step related
    exact holds source ⟨target', step, related⟩
  · rintro holds source ⟨target', step, related⟩
    exact holds source target' step related

/-- **Pullback along forgetting commutes with the step-future.** -/
theorem forget_pullback_diamond {A B : AdmissibleClass rules} (le : A ≤ B)
    (φ : EquationPredicate (observedGSLT observations A)) (term : S.Term) :
    ((forgetMap observations le).pullback (semanticDiamond (observedGSLT observations A) φ)).1 term ↔
      (semanticDiamond (observedGSLT observations B)
        ((forgetMap observations le).pullback φ)).1 term := by
  rw [forget_pullback_apply, observed_diamond_apply, observed_diamond_apply]
  rfl

/-- **Pullback along forgetting commutes with the step-past only laxly.** -/
theorem forget_pullback_box_le {A B : AdmissibleClass rules} (le : A ≤ B)
    (φ : EquationPredicate (observedGSLT observations A)) (term : S.Term)
    (holds : ((forgetMap observations le).pullback
      (semanticBox (observedGSLT observations A) φ)).1 term) :
    (semanticBox (observedGSLT observations B) ((forgetMap observations le).pullback φ)).1 term := by
  rw [forget_pullback_apply, observed_box_apply] at holds
  rw [observed_box_apply]
  intro source target' step related
  exact holds source target' step (AdmissibleClass.relEquiv_antitone observations le related)

section BoxControl

open ObserverPresheafControls.OracleTower

theorem opened_terminal (target : Tm) : ¬ Opens .opened target := by
  intro step
  cases step

theorem leaf_terminal (level : ℕ) (live : Bool) (target : Tm) :
    ¬ Opens (.leaf level live) target := by
  intro step
  cases step

/-- Stage `0` of the tower admits only the empty context. -/
theorem stage_zero_admissible {levels : List ℕ} (admissible : (stage 0).Admissible levels) :
    levels = [] := by
  cases levels with
  | nil => rfl
  | cons level rest =>
    exact absurd (stage_le_below 0 _ admissible level (List.Mem.head rest)) (Nat.not_lt_zero level)

/-- At stage `0`, terms with no step are equivalent. -/
theorem stage_zero_relEquiv_of_terminal {left right : Tm} (leftTerminal : ∀ t, ¬ Opens left t)
    (rightTerminal : ∀ t, ¬ Opens right t) : (stage 0).RelEquiv silent left right := by
  refine ⟨fun first second => (∀ t, ¬ Opens first t) ∧ ∀ t, ¬ Opens second t,
    ⟨?_, ?_, ?_⟩, leftTerminal, rightTerminal⟩
  · rintro first _ ⟨firstTerminal, _⟩ label target step
    have empty := stage_zero_admissible label.2
    change Opens (plugProbes label.1 first) target at step
    rw [empty] at step
    exact (firstTerminal target step).elim
  · rintro _ second ⟨_, secondTerminal⟩ label target step
    have empty := stage_zero_admissible label.2
    change Opens (plugProbes label.1 second) target at step
    rw [empty] at step
    exact (secondTerminal target step).elim
  · intro _ _ _ atom
    exact atom.1.elim

/-- At stage `1`, the opened residue and the live leaf of level `0` are
separated. -/
theorem not_stage_one_relEquiv_opened_leaf :
    ¬ (stage 1).RelEquiv silent .opened (.leaf 0 true) := by
  intro related
  obtain ⟨_, step, _⟩ := AdmissibleContextCongruence.bisimilar_backward related
    ⟨[0], probe_admissible (by decide)⟩ (Opens.fire 0)
  change Opens (Tm.probe 0 .opened) _ at step
  cases step

/-- **Negative control: the step-past is not natural along forgetting.**  On the
oracle tower, with `φ` the predicate "not equivalent at stage `0` to the probe of
the live leaf of level `0`", the stage-`1` step-past of the pulled-back `φ` holds
of the live leaf of level `0`, but the pullback of the stage-`0` step-past does
not. -/
theorem box_not_natural :
    ¬ ∀ (φ : EquationPredicate (observedGSLT silent (stage 0))) (term : Tm),
      (semanticBox (observedGSLT silent (stage 1))
          ((forgetMap silent (stage_monotone (Nat.zero_le 1))).pullback φ)).1 term →
        ((forgetMap silent (stage_monotone (Nat.zero_le 1))).pullback
          (semanticBox (observedGSLT silent (stage 0)) φ)).1 term := by
  intro natural
  let source : Tm := .probe 0 (.leaf 0 true)
  let φ : EquationPredicate (observedGSLT silent (stage 0)) :=
    ⟨fun term => ¬ (stage 0).RelEquiv silent term source, fun left right related =>
      ⟨fun notLeft relatedRight => notLeft ((stage 0).relEquiv_trans silent related relatedRight),
        fun notRight relatedLeft => notRight
          ((stage 0).relEquiv_trans silent ((stage 0).relEquiv_symm silent related) relatedLeft)⟩⟩
  have fine : (semanticBox (observedGSLT silent (stage 1))
      ((forgetMap silent (stage_monotone (Nat.zero_le 1))).pullback φ)).1 (.leaf 0 true) := by
    refine (observed_box_apply silent (stage 1) _ _).mpr ?_
    intro _ _ step related
    cases step
    exact (not_stage_one_relEquiv_opened_leaf related).elim
  have coarse := (observed_box_apply silent (stage 0) φ _).mp (natural φ (.leaf 0 true) fine)
  exact coarse source .opened (Opens.fire 0)
    (stage_zero_relEquiv_of_terminal (opened_terminal) (leaf_terminal 0 true))
    ((stage 0).relEquiv_refl silent source)

end BoxControl

/-! ## Native types over the observer site -/

/-- A family of stage predicates is **closed under forgetting** when what holds at
a finer stage holds at every coarser stage. -/
def ForgettingClosed (φ : ∀ D : AdmissibleClass rules, Set (Stage observations D)) : Prop :=
  ∀ ⦃A B : AdmissibleClass rules⦄ (le : A ≤ B), existsAlong observations le (φ B) ⊆ φ A

theorem forgettingClosed_iff (φ : ∀ D : AdmissibleClass rules, Set (Stage observations D)) :
    ForgettingClosed observations φ ↔
      ∀ ⦃A B : AdmissibleClass rules⦄ (le : A ≤ B), φ B ⊆ reindex observations le (φ A) :=
  forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun le => existsAlong_subset_iff le

/-- **Subfunctors of the observer presheaf are the forgetting-closed families of
stage predicates.** -/
def subfunctorOrderIso :
    Subfunctor (observerPresheaf (rules := rules) observations) ≃o
      {φ : ∀ D : AdmissibleClass rules, Set (Stage observations D) //
        ForgettingClosed observations φ} where
  toFun G := ⟨fun D => G.obj (op D), fun _ _ le =>
    (existsAlong_subset_iff le).mpr (G.map (homOfLE le).op)⟩
  invFun φ :=
    { obj := fun U => φ.1 U.unop
      map := fun {U V} i => (existsAlong_subset_iff (leOfHom i.unop)).mp
        (φ.2 (leOfHom i.unop)) }
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' {G G'} := by
    constructor
    · intro le U
      exact le U.unop
    · intro le D
      exact le (op D)

/-- **The Williams–Stay indexed adjoints over the observer site.**  Over any
presheaf mapped into the observer presheaf, native predicates have direct and
universal images adjoint to pullback. -/
theorem observerSite_indexedAdjoints {X : (AdmissibleClass rules)ᵒᵖ ⥤ Type uS}
    (f : X ⟶ observerPresheaf observations) :
    GaloisConnection
        ((Mettapedia.GSLT.Topos.presheafChangeOfBase (AdmissibleClass rules)).directImage f)
        ((Mettapedia.GSLT.Topos.presheafChangeOfBase (AdmissibleClass rules)).pullback f) ∧
      GaloisConnection
        ((Mettapedia.GSLT.Topos.presheafChangeOfBase (AdmissibleClass rules)).pullback f)
        ((Mettapedia.GSLT.Topos.presheafChangeOfBase (AdmissibleClass rules)).universalImage f) :=
  Mettapedia.OSLF.PresheafNativeType.prop12_indexedAdjoints (AdmissibleClass rules) f

/-- **The Williams–Stay Beck–Chevalley condition over the observer site**, for
pullback squares of presheaves. -/
theorem observerSite_beckChevalley :
    Mettapedia.GSLT.Topos.BeckChevalleyCondition
      (Mettapedia.GSLT.Topos.presheafPredicateFib.{uContext, uS, uContext} (AdmissibleClass rules))
      (Mettapedia.GSLT.Topos.presheafChangeOfBase.{uContext, uS, uContext} (AdmissibleClass rules)) :=
  Mettapedia.OSLF.PresheafNativeType.prop12_beckChevalley (AdmissibleClass rules)

/-! ## Carving: restriction to a sub-site -/

section SubSite

variable (Q : Set (AdmissibleClass rules))

/-- Families of stage predicates on a sub-site that are closed under forgetting
within it. -/
def ForgettingClosedOn (φ : ∀ q : Q, Set (Stage observations q.1)) : Prop :=
  ∀ ⦃q q' : Q⦄ (le : q.1 ≤ q'.1), existsAlong observations le (φ q') ⊆ φ q

/-- Restricting a family to a sub-site. -/
def restrictFamily (φ : ∀ D : AdmissibleClass rules, Set (Stage observations D)) :
    ∀ q : Q, Set (Stage observations q.1) :=
  fun q => φ q.1

theorem restrictFamily_closed {φ : ∀ D : AdmissibleClass rules, Set (Stage observations D)}
    (closed : ForgettingClosed observations φ) :
    ForgettingClosedOn observations Q (restrictFamily observations Q φ) :=
  fun _ _ le => closed le

/-- **The smallest extension** of a family on a sub-site: what forgetting generates
from it. -/
def smallestExtension (φ : ∀ q : Q, Set (Stage observations q.1)) (D : AdmissibleClass rules) :
    Set (Stage observations D) :=
  {y | ∃ (q : Q) (le : D ≤ q.1), y ∈ existsAlong observations le (φ q)}

/-- **The largest extension** of a family on a sub-site: what restricts into it at
every stage of the sub-site below. -/
def largestExtension (φ : ∀ q : Q, Set (Stage observations q.1)) (D : AdmissibleClass rules) :
    Set (Stage observations D) :=
  {x | ∀ (q : Q) (le : q.1 ≤ D), restrict observations le x ∈ φ q}

theorem smallestExtension_closed (φ : ∀ q : Q, Set (Stage observations q.1)) :
    ForgettingClosed observations (smallestExtension observations Q φ) := by
  rintro A B le _ ⟨_, ⟨q, qLe, x, member, rfl⟩, rfl⟩
  exact ⟨q, le_trans le qLe, x, member, restrict_trans observations le qLe x⟩

theorem largestExtension_closed (φ : ∀ q : Q, Set (Stage observations q.1)) :
    ForgettingClosed observations (largestExtension observations Q φ) := by
  rintro A B le _ ⟨x, member, rfl⟩ q qLe
  rw [← restrict_trans]
  exact member q (le_trans qLe le)

/-- Restricting the smallest extension gives the family back. -/
theorem restrict_smallestExtension {φ : ∀ q : Q, Set (Stage observations q.1)}
    (closed : ForgettingClosedOn observations Q φ) (q : Q) :
    smallestExtension observations Q φ q.1 = φ q := by
  apply Set.Subset.antisymm
  · rintro _ ⟨q', le, x, member, rfl⟩
    exact closed le ⟨x, member, rfl⟩
  · intro x member
    exact ⟨q, le_refl q.1, x, member, restrict_refl observations q.1 x⟩

/-- Restricting the largest extension gives the family back. -/
theorem restrict_largestExtension {φ : ∀ q : Q, Set (Stage observations q.1)}
    (closed : ForgettingClosedOn observations Q φ) (q : Q) :
    largestExtension observations Q φ q.1 = φ q := by
  apply Set.Subset.antisymm
  · intro x member
    have atSelf := member q (le_refl q.1)
    rwa [restrict_refl] at atSelf
  · intro x member q' le
    exact closed le ⟨x, member, rfl⟩

/-- **The smallest extension is left adjoint to restriction.** -/
theorem smallestExtension_subset_iff {φ : ∀ q : Q, Set (Stage observations q.1)}
    {ψ : ∀ D : AdmissibleClass rules, Set (Stage observations D)}
    (closed : ForgettingClosed observations ψ) :
    (∀ D, smallestExtension observations Q φ D ⊆ ψ D) ↔
      ∀ q, φ q ⊆ restrictFamily observations Q ψ q := by
  constructor
  · intro below q x member
    exact below q.1 ⟨q, le_refl q.1, x, member, restrict_refl observations q.1 x⟩
  · rintro below D _ ⟨q, le, x, member, rfl⟩
    exact closed le ⟨x, below q member, rfl⟩

/-- **The largest extension is right adjoint to restriction.** -/
theorem subset_largestExtension_iff {φ : ∀ q : Q, Set (Stage observations q.1)}
    {ψ : ∀ D : AdmissibleClass rules, Set (Stage observations D)}
    (closed : ForgettingClosed observations ψ) :
    (∀ D, ψ D ⊆ largestExtension observations Q φ D) ↔
      ∀ q, restrictFamily observations Q ψ q ⊆ φ q := by
  constructor
  · intro below q x member
    have atSelf := below q.1 member q (le_refl q.1)
    rwa [restrict_refl] at atSelf
  · intro below D x member q le
    exact below q (closed le ⟨x, member, rfl⟩)

end SubSite

open ObserverPresheafControls.OracleTower in
/-- **Negative control: carving loses the stages outside the sub-site.**  On the
oracle tower carved to the single stage `1`, the smallest and the largest
extension of "the class of the live leaf of level `0`" disagree at stage `2`. -/
theorem extensions_differ :
    smallestExtension silent {stage 1}
        (fun q => {stageClass silent q.1 (.leaf 0 true)}) (stage 2) ≠
      largestExtension silent {stage 1}
        (fun q => {stageClass silent q.1 (.leaf 0 true)}) (stage 2) := by
  intro equal
  have inLargest : stageClass silent (stage 2) (.leaf 0 true) ∈
      largestExtension silent {stage 1}
        (fun q => {stageClass silent q.1 (.leaf 0 true)}) (stage 2) :=
    fun _ _ => rfl
  rw [← equal] at inLargest
  obtain ⟨q, le, _⟩ := inLargest
  have atOne : q.1 = stage 1 := q.2
  rw [atOne] at le
  exact absurd le (not_le_of_gt (stage_lt_succ 1))

/-! ## Controls: images are native over the site, interiors are not -/

/-- The classes of the terms satisfying `ψ`, at every stage. -/
def imageFamily (ψ : Set S.Term) (D : AdmissibleClass rules) : Set (Stage observations D) :=
  stageClass observations D '' ψ

/-- The classes lying entirely inside `ψ`, at every stage. -/
def interiorFamily (ψ : Set S.Term) (D : AdmissibleClass rules) : Set (Stage observations D) :=
  universalImage (stageClass observations D) ψ

/-- **Positive control**: the images of any term predicate form a
forgetting-closed family, hence a native predicate over the observer site. -/
theorem imageFamily_forgettingClosed (ψ : Set S.Term) :
    ForgettingClosed observations (imageFamily (rules := rules) observations ψ) := by
  rintro A B le _ ⟨_, ⟨term, member, rfl⟩, rfl⟩
  exact ⟨term, member, rfl⟩

/-- The native predicate over the observer site given by the images of `ψ`. -/
def imageSubfunctor (ψ : Set S.Term) : Subfunctor (observerPresheaf (rules := rules) observations) where
  obj U := imageFamily observations ψ U.unop
  map {_ _} _ := by
    rintro _ ⟨term, member, rfl⟩
    exact ⟨term, member, rfl⟩

theorem subfunctorOrderIso_imageSubfunctor (ψ : Set S.Term) :
    subfunctorOrderIso observations (imageSubfunctor (rules := rules) observations ψ) =
      ⟨imageFamily observations ψ, imageFamily_forgettingClosed observations ψ⟩ :=
  rfl

open ObserverPresheafControls.OracleTower in
/-- **Negative control**: interiors are not closed under forgetting.  At stage `1`
of the oracle tower the class of the live leaf of level `0` is a singleton inside
`{leaf 0 true}`; at stage `0` it also contains the dead leaf. -/
theorem interiorFamily_not_forgettingClosed :
    ¬ ForgettingClosed silent (interiorFamily (rules := towerRules) silent {.leaf 0 true}) := by
  intro closed
  have fine : stageClass silent (stage 1) (.leaf 0 true) ∈
      interiorFamily silent {.leaf 0 true} (stage 1) := by
    intro term equal
    have related := (stageClass_eq_iff silent (stage 1) term (.leaf 0 true)).mp equal
    obtain ⟨_, step, _⟩ := AdmissibleContextCongruence.bisimilar_backward related
      ⟨[0], probe_admissible (by decide)⟩ (Opens.fire 0)
    change Opens (Tm.probe 0 term) _ at step
    cases step
    rfl
  have coarse := closed (stage_monotone (Nat.zero_le 1)) ⟨_, fine, rfl⟩
  have dead := coarse (.leaf 0 false)
    ((stageClass_eq_iff silent (stage 0) _ _).mpr
      ((stage 0).relEquiv_symm silent (stage_relEquiv_leaves le_rfl)))
  exact Bool.false_ne_true (Tm.leaf.inj dead).2

end Mettapedia.OSLF.Framework.ObserverNativeTypes
