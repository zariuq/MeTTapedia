import Mettapedia.GSLT.Causality.Identifiability

/-!
# Context operators at the top: presentations, composition, impact, authority

An intervention is a context (`Causality.Hierarchy`): a term of a GSLT is a
causal model, the contexts of an admissible class are the interventions one
may make, and the three rungs of Pearl's ladder are three equivalences
relative to that class.  This module states, for an arbitrary GSLT and an
arbitrary presentation of its contexts, what the context operators do.

* **The ladder sees only the plug maps** (`Covers`, `agree_of_covers`,
  `agree_iff_of_covers`).  Two presentations of contexts over one GSLT, with
  their classes, agree at every rung and in every distance
  (`interventionalDistance_eq_of_covers`, `counterfactualDistance_eq_of_covers`)
  as soon as each admissible context of one has an admissible context of the
  other with the same plug up to the equations.  Whether an intervention is
  written as one operator or derived from other context formers is invisible
  to every observer of the ladder unless the plug maps differ.
* **Composition up to the plug** (`PlugEquiv`).  Contexts form a monoid up to
  plug equivalence (`plugEquiv_identity_left`, `plugEquiv_identity_right`,
  `plugEquiv_assoc`), and plug-equivalent contexts send a model to terms that
  agree at every rung (`agree_plug_of_plugEquiv`).  A set of contexts is the
  admissible set of a class exactly when it contains the identity and is
  closed under composition (`exists_class_iff`).
* **Suprema of pullbacks** (`supPullback`).  A bounded pseudometric pulled
  back along a family of maps and maximised over it is a pseudometric
  (`supPullback_symm`, `supPullback_triangle`), monotone in the family
  (`supPullback_le_of_cover`), and nonexpansive under every map of the family
  when the family is closed under composition (`supPullback_act_le`).  The
  interventional distance of the ladder is such a supremum
  (`interventionalDistance_eq_supPullback`).
* **Impact** (`impact`): how much a context changes a model's behaviour, read
  through one further admissible intervention.  Impact grows with the class
  that measures it (`impact_mono`), vanishes on the identity
  (`impact_identity`), is bounded by the counterfactual distance
  (`impact_le_counterfactual`), and is subadditive under composition when the
  outer context belongs to the measuring class (`impact_compose_le`): this is
  nonexpansiveness, that is, closure of the class under composition.  Measured
  by the bottom class, which runs no experiment, impact is the passive
  distance between the model and the intervened model (`impact_bot`).
* **Authority by unwinding** (`agree_of_unwinding`).  A relation preserved by
  every context of a class and that is a reduction bisimulation with the base
  observations relates only terms the class cannot tell apart, at every rung:
  the noninterference reading of the coarsest bisimulation congruence
  (`AdmissibleClass.relEquiv_of_isReductionBisimulation`).  A smaller class
  separates less (`agree_antitone`, `interventionalDistance_mono`,
  `saturatedGraded_logicalDistance_mono`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ContextOperators

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.GSLT.Distinction
open Mettapedia.GSLT.Causality.Hierarchy
open Mettapedia.GSLT.Causality.Identifiability

universe uS uContext uRule uContext' uRule' uAtom uObs uX uI uJ

/-! ## Suprema of pullbacks -/

section Pullbacks

variable {X : Type uX} {I : Type uI} {J : Type uJ}

/-- The supremum over a family of maps of a function of two points read after
the map. -/
noncomputable def supPullback (act : I → X → X) (d : X → X → ℝ) (x y : X) : ℝ :=
  ⨆ index, d (act index x) (act index y)

variable (act : I → X → X) (d : X → X → ℝ) {bound : ℝ} (le_bound : ∀ x y, d x y ≤ bound)
include le_bound

theorem bddAbove_pullback (x y : X) : BddAbove (Set.range fun index => d (act index x) (act index y)) :=
  ⟨bound, by
    rintro _ ⟨index, rfl⟩
    exact le_bound _ _⟩

theorem le_supPullback (index : I) (x y : X) :
    d (act index x) (act index y) ≤ supPullback act d x y :=
  le_ciSup (bddAbove_pullback act d le_bound x y) index

omit le_bound in
theorem supPullback_le [Nonempty I] {x y : X} {value : ℝ}
    (each : ∀ index, d (act index x) (act index y) ≤ value) : supPullback act d x y ≤ value :=
  ciSup_le each

omit le_bound in
theorem supPullback_symm (symm : ∀ x y, d x y = d y x) (x y : X) :
    supPullback act d x y = supPullback act d y x := by
  unfold supPullback
  congr 1
  funext index
  exact symm _ _

theorem supPullback_triangle [Nonempty I] (triangle : ∀ x y z, d x z ≤ d x y + d y z) (x y z : X) :
    supPullback act d x z ≤ supPullback act d x y + supPullback act d y z :=
  supPullback_le act d fun index => (triangle _ (act index y) _).trans
    (add_le_add (le_supPullback act d le_bound index x y) (le_supPullback act d le_bound index y z))

omit le_bound in
theorem supPullback_nonneg [Nonempty I] (nonneg : ∀ x y, 0 ≤ d x y) (le_bound : ∀ x y, d x y ≤ bound)
    (x y : X) : 0 ≤ supPullback act d x y := by
  obtain ⟨index⟩ := ‹Nonempty I›
  exact (nonneg _ _).trans (le_supPullback act d le_bound index x y)

omit le_bound in
/-- **A family that is covered by another gives a smaller supremum.** -/
theorem supPullback_le_of_cover [Nonempty I] {act' : J → X → X} (le_bound : ∀ x y, d x y ≤ bound)
    (cover : ∀ index, ∃ index', ∀ x y, d (act index x) (act index y) = d (act' index' x) (act' index' y))
    (x y : X) : supPullback act d x y ≤ supPullback act' d x y := by
  refine supPullback_le act d fun index => ?_
  obtain ⟨index', same⟩ := cover index
  rw [same]
  exact le_supPullback act' d le_bound index' x y

/-- **Nonexpansiveness.**  When the family is closed under composition, as read
by `d`, every map of the family is nonexpansive for the supremum. -/
theorem supPullback_act_le [Nonempty I]
    (closed : ∀ inner outer, ∃ composite, ∀ x y,
      d (act outer (act inner x)) (act outer (act inner y)) = d (act composite x) (act composite y))
    (index : I) (x y : X) :
    supPullback act d (act index x) (act index y) ≤ supPullback act d x y := by
  refine supPullback_le act d fun outer => ?_
  obtain ⟨composite, same⟩ := closed index outer
  rw [same]
  exact le_supPullback act d le_bound composite x y

/-- **Subadditivity of the displacement.**  For a family closed under
composition, displacing by one map and then another moves a point by at most
the sum of the two displacements. -/
theorem supPullback_displacement_le [Nonempty I] (triangle : ∀ x y z, d x z ≤ d x y + d y z)
    (closed : ∀ inner outer, ∃ composite, ∀ x y,
      d (act outer (act inner x)) (act outer (act inner y)) = d (act composite x) (act composite y))
    (inner outer : I) (x : X) :
    supPullback act d x (act outer (act inner x)) ≤
      supPullback act d x (act inner x) + supPullback act d x (act outer x) := by
  calc supPullback act d x (act outer (act inner x))
      ≤ supPullback act d x (act outer x) +
          supPullback act d (act outer x) (act outer (act inner x)) :=
        supPullback_triangle act d le_bound triangle _ _ _
    _ ≤ supPullback act d x (act outer x) + supPullback act d x (act inner x) :=
        add_le_add le_rfl (supPullback_act_le act d le_bound closed outer x (act inner x))
    _ = supPullback act d x (act inner x) + supPullback act d x (act outer x) := add_comm _ _

end Pullbacks

/-! ## The ladder sees only the plug maps -/

section Presentations

variable {S : GSLT.{uS}} {rules : ContextualRules.{uContext, uRule} S}
  {rules' : ContextualRules.{uContext', uRule'} S}

/-- **One class covers another** when every admissible context of the first has
an admissible context of the second with the same plug, up to the equations.
The two classes may belong to different presentations of the contexts of one
GSLT. -/
def Covers (A : AdmissibleClass rules) (A' : AdmissibleClass rules') : Prop :=
  ∀ ⦃context : rules.Context⦄, A.Admissible context →
    ∃ context', A'.Admissible context' ∧
      ∀ term, S.Equiv (rules'.plug context' term) (rules.plug context term)

theorem covers_refl (A : AdmissibleClass rules) : Covers A A :=
  fun context admissible => ⟨context, admissible, fun _ => S.equations.iseqv.refl _⟩

theorem covers_of_le {A B : AdmissibleClass rules} (le : A ≤ B) : Covers A B :=
  fun context admissible => ⟨context, le context admissible, fun _ => S.equations.iseqv.refl _⟩

variable {A : AdmissibleClass rules} {A' : AdmissibleClass rules'}
  (observations : ContextualRules.Observations.{uAtom} S)

theorem contextualEquiv_of_covers (cover : Covers A A') {left right : S.Term}
    (related : A'.ContextualEquiv observations left right) :
    A.ContextualEquiv observations left right := by
  intro context admissible
  obtain ⟨context', admissible', same⟩ := cover admissible
  exact reductionBisimilar_respectsEquations observations (same left) (same right)
    (related admissible')

theorem relEquiv_of_covers (cover : Covers A A') {left right : S.Term}
    (related : A'.RelEquiv observations left right) : A.RelEquiv observations left right := by
  refine A.relEquiv_of_isReductionBisimulation observations
    (A'.isReductionBisimulation_relEquiv observations) ?_ related
  intro context first second admissible held
  obtain ⟨context', admissible', same⟩ := cover admissible
  exact A'.relEquiv_of_equiv_of_equiv observations (same first) (same second)
    (A'.relEquiv_closedUnder observations admissible' held)

/-- **A covering class separates at least as much, at every rung.** -/
theorem agree_of_covers (cover : Covers A A') :
    ∀ (rung : Rung) {left right : S.Term},
      Agree A' observations rung left right → Agree A observations rung left right
  | .association, _, _, related => related
  | .intervention, _, _, related => contextualEquiv_of_covers observations cover related
  | .counterfactual, _, _, related => relEquiv_of_covers observations cover related

/-- **Two presentations with the same admissible plug maps have the same
ladder.** -/
theorem agree_iff_of_covers (cover : Covers A A') (cover' : Covers A' A) (rung : Rung)
    (left right : S.Term) :
    Agree A observations rung left right ↔ Agree A' observations rung left right :=
  ⟨agree_of_covers observations cover' rung, agree_of_covers observations cover rung⟩

/-! ### Distances -/

variable (base : GradedObservations.{uS, uObs} S) (discount : ℝ) (discount_nonneg : 0 ≤ discount)
  (discount_le_one : discount ≤ 1)

theorem passiveDistance_resp {left left' right right' : S.Term} (leftEquivalent : S.Equiv left left')
    (rightEquivalent : S.Equiv right right') :
    passiveDistance base discount discount_nonneg discount_le_one left right =
      passiveDistance base discount discount_nonneg discount_le_one left' right' := by
  unfold passiveDistance
  rw [GradedSystem.logicalDistance_resp_left _ leftEquivalent,
    GradedSystem.logicalDistance_resp_right _ _ rightEquivalent]

/-- **The interventional distance is a supremum of pullbacks** of the passive
distance along the admissible plugs. -/
theorem interventionalDistance_eq_supPullback (left right : S.Term) :
    interventionalDistance A base discount discount_nonneg discount_le_one left right =
      supPullback (fun context : {context : rules.Context // A.Admissible context} =>
          rules.plug context.1)
        (passiveDistance base discount discount_nonneg discount_le_one) left right :=
  rfl

theorem interventionalDistance_le_of_covers (cover : Covers A A') (left right : S.Term) :
    interventionalDistance A base discount discount_nonneg discount_le_one left right ≤
      interventionalDistance A' base discount discount_nonneg discount_le_one left right := by
  have : Nonempty {context : rules.Context // A.Admissible context} :=
    ⟨⟨rules.identity, A.identity_mem⟩⟩
  refine ciSup_le fun context => ?_
  obtain ⟨context', admissible', same⟩ := cover context.2
  rw [passiveDistance_resp base discount discount_nonneg discount_le_one
    (S.equations.iseqv.symm (same left)) (S.equations.iseqv.symm (same right))]
  exact passiveDistance_plug_le_interventional A' base discount discount_nonneg discount_le_one
    admissible' left right

/-- The covering context chosen for an admissible context. -/
noncomputable def coverContext (cover : Covers A A')
    (context : {context : rules.Context // A.Admissible context}) :
    {context' : rules'.Context // A'.Admissible context'} :=
  ⟨Classical.choose (cover context.2), (Classical.choose_spec (cover context.2)).1⟩

theorem coverContext_plug (cover : Covers A A')
    (context : {context : rules.Context // A.Admissible context}) (term : S.Term) :
    S.Equiv (rules'.plug (coverContext cover context).1 term) (rules.plug context.1 term) :=
  (Classical.choose_spec (cover context.2)).2 term

/-- The identity is an observation-preserving functional bisimulation from the
saturated system of a class to that of a covering class. -/
noncomputable def coverEmbedding (cover : Covers A A') :
    ObservationBisimulation (saturatedGraded A base discount discount_nonneg discount_le_one)
      (saturatedGraded A' base discount discount_nonneg discount_le_one) where
  mapTerm := id
  mapEquiv := fun equivalent => equivalent
  atom observation := (observation.1, coverContext cover observation.2)
  label context := coverContext cover context
  discount_eq := rfl
  value_map observation term :=
    base.value_resp observation.1 (coverContext_plug cover observation.2 term)
  mapAct context term target step := by
    obtain ⟨target', step', equivalent⟩ := S.rewrites_resp_left
      (S.equations.iseqv.symm (coverContext_plug cover context term)) step
    exact S.rewrites_resp_right step' (S.equations.iseqv.symm equivalent)
  liftAct context term target' step := by
    obtain ⟨target, step', equivalent⟩ := S.rewrites_resp_left
      (coverContext_plug cover context term) step
    exact ⟨target, step', S.equations.iseqv.symm equivalent⟩

theorem counterfactualDistance_le_of_covers (cover : Covers A A') (left right : S.Term) :
    counterfactualDistance A base discount discount_nonneg discount_le_one left right ≤
      counterfactualDistance A' base discount discount_nonneg discount_le_one left right :=
  (coverEmbedding base discount discount_nonneg discount_le_one cover).logicalDistance_le_map
    left right

theorem interventionalDistance_eq_of_covers (cover : Covers A A') (cover' : Covers A' A)
    (left right : S.Term) :
    interventionalDistance A base discount discount_nonneg discount_le_one left right =
      interventionalDistance A' base discount discount_nonneg discount_le_one left right :=
  le_antisymm (interventionalDistance_le_of_covers base discount discount_nonneg discount_le_one
      cover left right)
    (interventionalDistance_le_of_covers base discount discount_nonneg discount_le_one
      cover' left right)

theorem counterfactualDistance_eq_of_covers (cover : Covers A A') (cover' : Covers A' A)
    (left right : S.Term) :
    counterfactualDistance A base discount discount_nonneg discount_le_one left right =
      counterfactualDistance A' base discount discount_nonneg discount_le_one left right :=
  le_antisymm (counterfactualDistance_le_of_covers base discount discount_nonneg discount_le_one
      cover left right)
    (counterfactualDistance_le_of_covers base discount discount_nonneg discount_le_one
      cover' left right)

end Presentations

/-! ## Composition up to the plug -/

section Composition

variable {S : GSLT.{uS}} {rules : ContextualRules.{uContext, uRule} S}

/-- Two contexts are **plug-equivalent** when they plug every term to equated
terms. -/
def PlugEquiv (first second : rules.Context) : Prop :=
  ∀ term, S.Equiv (rules.plug first term) (rules.plug second term)

theorem plugEquiv_refl (context : rules.Context) : PlugEquiv context context :=
  fun _ => S.equations.iseqv.refl _

theorem plugEquiv_symm {first second : rules.Context} (same : PlugEquiv first second) :
    PlugEquiv second first :=
  fun term => S.equations.iseqv.symm (same term)

theorem plugEquiv_trans {first second third : rules.Context} (firstSecond : PlugEquiv first second)
    (secondThird : PlugEquiv second third) : PlugEquiv first third :=
  fun term => S.equations.iseqv.trans (firstSecond term) (secondThird term)

/-- Plugging a composite is plugging its parts in turn. -/
theorem plug_compose_equiv (outer inner : rules.Context) (term : S.Term) :
    S.Equiv (rules.plug (rules.compose outer inner) term) (rules.plug outer (rules.plug inner term)) :=
  rules.plug_compose outer inner term

theorem plugEquiv_compose {outer outer' inner inner' : rules.Context}
    (outerSame : PlugEquiv outer outer') (innerSame : PlugEquiv inner inner') :
    PlugEquiv (rules.compose outer inner) (rules.compose outer' inner') := fun term =>
  S.equations.iseqv.trans (rules.plug_compose outer inner term)
    (S.equations.iseqv.trans (rules.plug_resp outer (innerSame term))
      (S.equations.iseqv.trans (outerSame _)
        (S.equations.iseqv.symm (rules.plug_compose outer' inner' term))))

/-- **Identity on the left.** -/
theorem plugEquiv_identity_left (context : rules.Context) :
    PlugEquiv (rules.compose rules.identity context) context := fun term =>
  S.equations.iseqv.trans (rules.plug_compose _ _ term) (rules.plug_identity _)

/-- **Identity on the right.** -/
theorem plugEquiv_identity_right (context : rules.Context) :
    PlugEquiv (rules.compose context rules.identity) context := fun term =>
  S.equations.iseqv.trans (rules.plug_compose _ _ term) (rules.plug_resp _ (rules.plug_identity _))

/-- **Associativity.** -/
theorem plugEquiv_assoc (first second third : rules.Context) :
    PlugEquiv (rules.compose (rules.compose first second) third)
      (rules.compose first (rules.compose second third)) := fun term =>
  S.equations.iseqv.trans (rules.plug_compose _ _ term)
    (S.equations.iseqv.trans (rules.plug_compose _ _ _)
      (S.equations.iseqv.trans (rules.plug_resp _ (S.equations.iseqv.symm
          (rules.plug_compose _ _ term)))
        (S.equations.iseqv.symm (rules.plug_compose _ _ term))))

/-- Two contexts **commute** when composing them in either order gives
plug-equivalent contexts. -/
def Commute (first second : rules.Context) : Prop :=
  PlugEquiv (rules.compose first second) (rules.compose second first)

variable (observations : ContextualRules.Observations.{uAtom} S)

/-- **Plug-equivalent contexts are indistinguishable at every rung**: the
models they produce agree, whatever class is used to watch them. -/
theorem agree_plug_of_plugEquiv (A : AdmissibleClass rules) {first second : rules.Context}
    (same : PlugEquiv first second) (rung : Rung) (term : S.Term) :
    Agree A observations rung (rules.plug first term) (rules.plug second term) := by
  have equal : Agree A observations rung (rules.plug second term) (rules.plug second term) :=
    (agree_equivalence A observations rung).refl _
  exact agree_respectsEquations observations A rung
    (S.equations.iseqv.symm (same term)) (S.equations.iseqv.refl _) equal

/-- **A set of contexts is the admissible set of a class exactly when it holds
the identity and is closed under composition.** -/
theorem exists_class_iff (admissible : rules.Context → Prop) :
    (∃ A : AdmissibleClass rules, A.Admissible = admissible) ↔
      admissible rules.identity ∧
        ∀ ⦃outer inner⦄, admissible outer → admissible inner →
          admissible (rules.compose outer inner) := by
  constructor
  · rintro ⟨A, rfl⟩
    exact ⟨A.identity_mem, fun _ _ outer inner => A.compose_mem outer inner⟩
  · rintro ⟨identity, compose⟩
    exact ⟨⟨admissible, identity, fun outer inner => compose outer inner⟩, rfl⟩

end Composition

/-! ## Impact -/

section Impact

variable {S : GSLT.{uS}} {rules : ContextualRules.{uContext, uRule} S}
  (A : AdmissibleClass rules) (base : GradedObservations.{uS, uObs} S) (discount : ℝ)
  (discount_nonneg : 0 ≤ discount) (discount_le_one : discount ≤ 1)

theorem passiveDistance_triangle (first second third : S.Term) :
    passiveDistance base discount discount_nonneg discount_le_one first third ≤
      passiveDistance base discount discount_nonneg discount_le_one first second +
        passiveDistance base discount discount_nonneg discount_le_one second third :=
  GradedSystem.logicalDistance_triangle _ _ _ _

theorem passiveDistance_symm (left right : S.Term) :
    passiveDistance base discount discount_nonneg discount_le_one left right =
      passiveDistance base discount discount_nonneg discount_le_one right left :=
  GradedSystem.logicalDistance_symm _ _ _

theorem passiveDistance_le_one (left right : S.Term) :
    passiveDistance base discount discount_nonneg discount_le_one left right ≤ 1 :=
  GradedSystem.logicalDistance_le_one _ _ _

theorem interventionalDistance_symm (left right : S.Term) :
    interventionalDistance A base discount discount_nonneg discount_le_one left right =
      interventionalDistance A base discount discount_nonneg discount_le_one right left := by
  rw [interventionalDistance_eq_supPullback, interventionalDistance_eq_supPullback]
  exact supPullback_symm _ _ (passiveDistance_symm base discount discount_nonneg discount_le_one) _ _

theorem interventionalDistance_triangle (first second third : S.Term) :
    interventionalDistance A base discount discount_nonneg discount_le_one first third ≤
      interventionalDistance A base discount discount_nonneg discount_le_one first second +
        interventionalDistance A base discount discount_nonneg discount_le_one second third := by
  have : Nonempty {context : rules.Context // A.Admissible context} :=
    ⟨⟨rules.identity, A.identity_mem⟩⟩
  rw [interventionalDistance_eq_supPullback, interventionalDistance_eq_supPullback,
    interventionalDistance_eq_supPullback]
  exact supPullback_triangle _ _ (passiveDistance_le_one base discount discount_nonneg discount_le_one)
    (passiveDistance_triangle base discount discount_nonneg discount_le_one) _ _ _

theorem interventionalDistance_resp {left left' right right' : S.Term}
    (leftEquivalent : S.Equiv left left') (rightEquivalent : S.Equiv right right') :
    interventionalDistance A base discount discount_nonneg discount_le_one left right =
      interventionalDistance A base discount discount_nonneg discount_le_one left' right' := by
  unfold interventionalDistance
  congr 1
  funext context
  exact passiveDistance_resp base discount discount_nonneg discount_le_one
    (rules.plug_resp _ leftEquivalent) (rules.plug_resp _ rightEquivalent)

/-- The admissible plugs are closed under composition, as read by the passive
distance. -/
theorem plug_closed (inner outer : {context : rules.Context // A.Admissible context}) :
    ∃ composite : {context : rules.Context // A.Admissible context}, ∀ left right,
      passiveDistance base discount discount_nonneg discount_le_one
          (rules.plug outer.1 (rules.plug inner.1 left)) (rules.plug outer.1 (rules.plug inner.1 right)) =
        passiveDistance base discount discount_nonneg discount_le_one
          (rules.plug composite.1 left) (rules.plug composite.1 right) :=
  ⟨⟨rules.compose outer.1 inner.1, A.compose_mem outer.2 inner.2⟩, fun left right =>
    passiveDistance_resp base discount discount_nonneg discount_le_one
      (S.equations.iseqv.symm (rules.plug_compose _ _ left))
      (S.equations.iseqv.symm (rules.plug_compose _ _ right))⟩

/-- **Every admissible context is nonexpansive for the interventional
distance.** -/
theorem interventionalDistance_plug_le {context : rules.Context} (admissible : A.Admissible context)
    (left right : S.Term) :
    interventionalDistance A base discount discount_nonneg discount_le_one
        (rules.plug context left) (rules.plug context right) ≤
      interventionalDistance A base discount discount_nonneg discount_le_one left right := by
  have : Nonempty {context : rules.Context // A.Admissible context} :=
    ⟨⟨rules.identity, A.identity_mem⟩⟩
  rw [interventionalDistance_eq_supPullback, interventionalDistance_eq_supPullback]
  exact supPullback_act_le (fun context : {context : rules.Context // A.Admissible context} =>
      rules.plug context.1) _ (passiveDistance_le_one base discount discount_nonneg discount_le_one)
    (plug_closed A base discount discount_nonneg discount_le_one) ⟨context, admissible⟩ left right

/-- **A larger class separates more**: the interventional distance is monotone
in the class. -/
theorem interventionalDistance_mono {B : AdmissibleClass rules} (le : A ≤ B) (left right : S.Term) :
    interventionalDistance A base discount discount_nonneg discount_le_one left right ≤
      interventionalDistance B base discount discount_nonneg discount_le_one left right :=
  interventionalDistance_le_of_covers base discount discount_nonneg discount_le_one
    (covers_of_le le) left right

/-- **The impact of a context on a model**: how far the intervened model is
from the model, as seen by one further admissible intervention. -/
noncomputable def impact (context : rules.Context) (term : S.Term) : ℝ :=
  interventionalDistance A base discount discount_nonneg discount_le_one term
    (rules.plug context term)

theorem impact_nonneg (context : rules.Context) (term : S.Term) :
    0 ≤ impact A base discount discount_nonneg discount_le_one context term :=
  (passiveDistance_nonneg base discount discount_nonneg discount_le_one _ _).trans
    (passiveDistance_le_interventional A base discount discount_nonneg discount_le_one _ _)

/-- **Impact grows with the class that measures it.** -/
theorem impact_mono {B : AdmissibleClass rules} (le : A ≤ B) (context : rules.Context)
    (term : S.Term) :
    impact A base discount discount_nonneg discount_le_one context term ≤
      impact B base discount discount_nonneg discount_le_one context term :=
  interventionalDistance_mono A base discount discount_nonneg discount_le_one le _ _

/-- The identity context has no impact. -/
theorem impact_identity (term : S.Term) :
    impact A base discount discount_nonneg discount_le_one rules.identity term = 0 := by
  unfold impact
  rw [interventionalDistance_resp A base discount discount_nonneg discount_le_one
    (S.equations.iseqv.refl term) (rules.plug_identity term)]
  apply le_antisymm _ ((passiveDistance_nonneg base discount discount_nonneg discount_le_one _ _).trans
    (passiveDistance_le_interventional A base discount discount_nonneg discount_le_one term term))
  have : Nonempty {context : rules.Context // A.Admissible context} :=
    ⟨⟨rules.identity, A.identity_mem⟩⟩
  exact ciSup_le fun _ => by
    simp [passiveDistance]

/-- **Impact is bounded by the counterfactual distance.** -/
theorem impact_le_counterfactual (context : rules.Context) (term : S.Term) :
    impact A base discount discount_nonneg discount_le_one context term ≤
      counterfactualDistance A base discount discount_nonneg discount_le_one term
        (rules.plug context term) :=
  interventional_le_counterfactual A base discount discount_nonneg discount_le_one _ _

/-- The zero kernel of impact: no admissible intervention tells the model and
the intervened model apart passively. -/
theorem impact_eq_zero_iff (context : rules.Context) (term : S.Term) :
    impact A base discount discount_nonneg discount_le_one context term = 0 ↔
      ∀ ⦃other : rules.Context⦄, A.Admissible other →
        passiveDistance base discount discount_nonneg discount_le_one
          (rules.plug other term) (rules.plug other (rules.plug context term)) = 0 :=
  interventionalDistance_eq_zero_iff A base discount discount_nonneg discount_le_one _ _

/-- **With no experiment the interventional distance is the passive one**:
every context of the bottom class acts as the identity. -/
theorem interventionalDistance_bot (left right : S.Term) :
    interventionalDistance (⊥ : AdmissibleClass rules) base discount discount_nonneg discount_le_one
        left right =
      passiveDistance base discount discount_nonneg discount_le_one left right := by
  have : Nonempty {context : rules.Context // (⊥ : AdmissibleClass rules).Admissible context} :=
    ⟨⟨rules.identity, (⊥ : AdmissibleClass rules).identity_mem⟩⟩
  refine le_antisymm (ciSup_le fun context => ?_)
    (passiveDistance_le_interventional _ base discount discount_nonneg discount_le_one left right)
  rw [passiveDistance_resp base discount discount_nonneg discount_le_one
    (plug_equiv_of_bot context.2 left) (plug_equiv_of_bot context.2 right)]

/-- **Impact measured by the bottom class is passive impact.** -/
theorem impact_bot (context : rules.Context) (term : S.Term) :
    impact (⊥ : AdmissibleClass rules) base discount discount_nonneg discount_le_one context term =
      passiveDistance base discount discount_nonneg discount_le_one term (rules.plug context term) :=
  interventionalDistance_bot base discount discount_nonneg discount_le_one _ _

/-- **Subadditivity of impact under composition.**  When the outer context
belongs to the measuring class, the impact of the composite is at most the
sum of the impacts.  The hypothesis is used only through nonexpansiveness,
that is, through closure of the class under composition. -/
theorem impact_compose_le {outer : rules.Context} (admissible : A.Admissible outer)
    (inner : rules.Context) (term : S.Term) :
    impact A base discount discount_nonneg discount_le_one (rules.compose outer inner) term ≤
      impact A base discount discount_nonneg discount_le_one inner term +
        impact A base discount discount_nonneg discount_le_one outer term := by
  unfold impact
  rw [interventionalDistance_resp A base discount discount_nonneg discount_le_one
    (S.equations.iseqv.refl term) (rules.plug_compose outer inner term)]
  calc interventionalDistance A base discount discount_nonneg discount_le_one term
        (rules.plug outer (rules.plug inner term))
      ≤ interventionalDistance A base discount discount_nonneg discount_le_one term
            (rules.plug outer term) +
          interventionalDistance A base discount discount_nonneg discount_le_one
            (rules.plug outer term) (rules.plug outer (rules.plug inner term)) :=
        interventionalDistance_triangle A base discount discount_nonneg discount_le_one _ _ _
    _ ≤ interventionalDistance A base discount discount_nonneg discount_le_one term
            (rules.plug outer term) +
          interventionalDistance A base discount discount_nonneg discount_le_one term
            (rules.plug inner term) :=
        add_le_add le_rfl (interventionalDistance_plug_le A base discount discount_nonneg
          discount_le_one admissible _ _)
    _ = _ := add_comm _ _

end Impact

/-! ## Authority -/

section Authority

variable {S : GSLT.{uS}} {rules : ContextualRules.{uContext, uRule} S}
  (A : AdmissibleClass rules) (observations : ContextualRules.Observations.{uAtom} S)

/-- **Noninterference by unwinding.**  A relation that every context of a class
preserves, and that is a reduction bisimulation with the base observations,
relates only models that the class cannot tell apart, at every rung. -/
theorem agree_of_unwinding {relation : S.Term → S.Term → Prop}
    (bisimulation : IsReductionBisimulation observations relation)
    (closed : A.ClosedUnder relation) {left right : S.Term} (related : relation left right)
    (rung : Rung) : Agree A observations rung left right :=
  agree_of_le (lower := rung) (upper := .counterfactual) A observations
    (show rung.height ≤ 2 by cases rung <;> decide)
    (A.relEquiv_of_isReductionBisimulation observations bisimulation closed related)

end Authority

end Mettapedia.GSLT.Causality.ContextOperators
