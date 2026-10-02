import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedGenericRule
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalLawTransfer

/-!
# Firing trees factor through the generic objects

Every leaf of a firing tree is a bare event variable used through the
environment it records. Substituting a tree factors through the generic
substitution, and a rule node factors through the rule's generic occurrence:
the arrow of the substituted tree, or of the node, is an arrow into the
generic object followed by the generic arrow.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalJudgmentCategory
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalEventOrbit
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFiniteContext (Context seeds exactHole Hom)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFibres
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFree (Tree Holes interpret freeModel substitute)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedBaseChange (pushTree)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCoherence
  (pushTree_substitute orbit_heq_of_environment)
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalSubstitutionModel (substJudgment_congr)
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
  (substJudgment mapJudgment_substJudgment heq_transport)

variable {S : Signature} (R : List (LocalRule S))
variable {M : List (MetaArity S)} (equations : List (EqAxiom S M))

/-! ## Leaves -/

section Leaves

variable {A : BindingCloneAlgebra.Algebra.{0} S}

/-- Bare uses of a listed variable at equal judgments agree. -/
theorem exactHole_heq (Γ : Context R A) (position : Fin Γ.listed.length) {J J' : Judgment A}
    (same : Γ.listed.label position = J) (same' : Γ.listed.label position = J') :
    HEq (exactHole R A Γ ⟨position, ⟨same⟩⟩) (exactHole R A Γ ⟨position, ⟨same'⟩⟩) := by
  subst same
  subst same'
  rfl

/-- Leaves at equal judgments with equal holes agree. -/
theorem pure_heq {Seed : (sort : S.Srt) → State A sort → Type} {J J' : Judgment A} (same : J = J')
    {hole : Holes A Seed J} {hole' : Holes A Seed J'} (sameHole : HEq hole hole') :
    HEq (Mettapedia.TypeTheory.IndexedPolynomial.Free.pure (rules R A) hole : Tree R A Seed J)
      (Mettapedia.TypeTheory.IndexedPolynomial.Free.pure (rules R A) hole' : Tree R A Seed J') := by
  subst same
  cases sameHole
  rfl

/-- **Every leaf is a bare event variable used through the environment it
records.** -/
theorem pure_heq_substitute (Γ : Context R A) (J : Judgment A)
    (hole : Holes A (seeds R A Γ) J) :
    HEq (Mettapedia.TypeTheory.IndexedPolynomial.Free.pure (rules R A) hole :
        Tree R A (seeds R A Γ) J)
      (substitute R A (seeds R A Γ) (hole.original.asJudgment A)
        (Mettapedia.TypeTheory.IndexedPolynomial.Free.pure (rules R A)
          (exactHole R A Γ ⟨hole.seed.1, ⟨hole.seed.2.down⟩⟩))
        hole.arrow.environment J (Map.as_substitution A hole.arrow)) := by
  obtain ⟨⟨context, source, target⟩, ⟨position, ⟨same⟩⟩, arrow⟩ := hole
  refine HEq.trans ?_ (heq_of_eq (IntrinsicScopedLocalActedFree.substitute_pure R A _ _ _ _ _ _)).symm
  refine HEq.trans ?_ (heq_transport _ _).symm
  have states : ofJudgment A J = ofJudgment A (substJudgment
      (State.asJudgment A ⟨context, source, target⟩) arrow.environment) :=
    congrArg₂ (fun one two => (⟨J.1, one, two⟩ : State A J.2.1)) arrow.sourceEq.symm
      arrow.targetEq.symm
  have leaves := orbit_heq_of_environment (Seed := seeds R A Γ) ⟨position, ⟨same⟩⟩ states arrow
    (𝟙 _ ≫ substitutionArrow A (State.asJudgment A ⟨context, source, target⟩) arrow.environment :
      (⟨context, source, target⟩ : State A J.2.1) ⟶ _)
    (heq_of_eq (funext fun _ => funext fun v =>
      (A.substitution.substitute_var arrow.environment v).symm))
  exact pure_heq R (congrArg (State.asJudgment A) states) leaves

/-- Maps out of the free model agree at equal judgments on equal trees. -/
theorem freeHom_heq {Γ : Context R A} {model : IntrinsicScopedLocalSubstitutionModel.SubstitutionModel R A}
    (hom : IntrinsicScopedLocalSubstitutionModel.SubstitutionModel.Hom R A
      (freeModel R A (seeds R A Γ)) model)
    {J J' : Judgment A} (same : J = J') {tree : Tree R A (seeds R A Γ) J}
    {tree' : Tree R A (seeds R A Γ) J'} (sameTree : HEq tree tree') :
    HEq (hom.evidence.toFun () J tree) (hom.evidence.toFun () J' tree') := by
  subst same
  cases sameTree
  rfl

/-- **Maps out of the free model over a finite context are determined by the
bare variables.** -/
theorem hom_ext_on_variables (Γ : Context R A)
    (model : IntrinsicScopedLocalSubstitutionModel.SubstitutionModel R A)
    (first second : IntrinsicScopedLocalSubstitutionModel.SubstitutionModel.Hom R A
      (freeModel R A (seeds R A Γ)) model)
    (same : ∀ position : Fin Γ.listed.length,
      first.evidence.toFun () _ (leaf R Γ position) =
        second.evidence.toFun () _ (leaf R Γ position)) :
    first = second := by
  refine IntrinsicScopedLocalActedFree.hom_ext_on_leaves R A _ model first second (fun J hole => ?_)
  have atVariable : ∀ hom : IntrinsicScopedLocalSubstitutionModel.SubstitutionModel.Hom R A
      (freeModel R A (seeds R A Γ)) model,
      HEq (hom.evidence.toFun () J (Mettapedia.TypeTheory.IndexedPolynomial.Free.pure (rules R A) hole))
        (model.act (hole.original.asJudgment A)
          (hom.evidence.toFun () _ (Mettapedia.TypeTheory.IndexedPolynomial.Free.pure (rules R A)
            (exactHole R A Γ ⟨hole.seed.1, ⟨hole.seed.2.down⟩⟩)))
          hole.arrow.environment J (Map.as_substitution A hole.arrow)) :=
    fun hom => (freeHom_heq R hom rfl (pure_heq_substitute R Γ J hole)).trans
      (heq_of_eq (hom.preserves (hole.original.asJudgment A)
        (Mettapedia.TypeTheory.IndexedPolynomial.Free.pure (rules R A)
          (exactHole R A Γ ⟨hole.seed.1, ⟨hole.seed.2.down⟩⟩))
        hole.arrow.environment J (Map.as_substitution A hole.arrow)))
  have atLeaf : ∀ hom : IntrinsicScopedLocalSubstitutionModel.SubstitutionModel.Hom R A
      (freeModel R A (seeds R A Γ)) model,
      HEq (hom.evidence.toFun () _ (Mettapedia.TypeTheory.IndexedPolynomial.Free.pure (rules R A)
          (exactHole R A Γ ⟨hole.seed.1, ⟨hole.seed.2.down⟩⟩)))
        (hom.evidence.toFun () _ (leaf R Γ hole.seed.1)) :=
    fun hom => freeHom_heq R hom hole.seed.2.down.symm
      (pure_heq R hole.seed.2.down.symm (exactHole_heq R Γ hole.seed.1 _ rfl))
  refine eq_of_heq ((atVariable first).trans (HEq.trans ?_ (atVariable second).symm))
  exact model.toAction.act_heq rfl ((atLeaf first).trans ((heq_of_eq (same hole.seed.1)).trans
    (atLeaf second).symm)) HEq.rfl rfl _ _

/-- **Interpreting a firing tree is the unique map commuting with both actions
that agrees at the bare variables.** -/
theorem interpret_eq_of_variables (Γ : Context R A)
    (model : IntrinsicScopedLocalSubstitutionModel.SubstitutionModel R A)
    (assigned : IntrinsicScopedLocalActedFree.NaturalAssignment R A (seeds R A Γ) model)
    (image : ∀ J : Judgment A, Tree R A (seeds R A Γ) J → model.carrier J)
    (isHom : IntrinsicScopedLocalSubstitutionModel.SubstitutionModel.IsHom R A
      (freeModel R A (seeds R A Γ)) model image)
    (same : ∀ position : Fin Γ.listed.length,
      interpret R A (seeds R A Γ) model assigned _ (leaf R Γ position) = image _ (leaf R Γ position))
    (J : Judgment A) (tree : Tree R A (seeds R A Γ) J) :
    interpret R A (seeds R A Γ) model assigned J tree = image J tree :=
  congrArg (fun hom => hom.evidence.toFun () J tree)
    (hom_ext_on_variables R Γ model (IntrinsicScopedLocalActedFree.foldHom R A _ model assigned)
      (IntrinsicScopedLocalSubstitutionModel.SubstitutionModel.Hom.ofIsHom R A image isHom) same)

end Leaves

/-! ## Reading the variable of a one-variable object -/

/-- Reading the one variable of an object through an arrow into it returns
the arrow's tree. -/
theorem singleArrow_comp_rep_leaf {a : Classifier R equations} {Y : Base equations}
    (u : a.base ⟶ Y) (j : Judgment (modelAt equations Y))
    (tree : Tree R _ (seeds R _ (events R equations a)) (mapJudgment (modelMap equations u) j)) :
    singleArrow R equations u j tree ≫
        rep R equations (a := object R equations Y ((Context.empty R _).cons R _ j)) j
          (leaf R ((Context.empty R _).cons R _ j) (first R j (Context.empty R _))) =
      rep R equations (mapJudgment (modelMap equations u) j) tree := by
  refine (comp_rep R equations (singleArrow R equations u j tree) j
    (leaf R ((Context.empty R _).cons R _ j) (first R j (Context.empty R _)))).trans
    (congrArg (rep R equations _) ?_)
  refine (congrArg (interpret R _ _ _ _ _)
    (pushTree_leaf R (modelMap equations u) ((Context.empty R _).cons R _ j)
      (first R j (Context.empty R _)))).trans ?_
  exact (interpret_leaf R _ _).trans (atSlot_singleArrow R equations u j tree)

/-! ## Substitution through the generic substitution -/

/-- Reindexing the generic substitution tree and substituting an arrow's trees
uses the arrow's tree at the variable through the reindexed environment. -/
theorem interpret_pushTree_substitutionTree {B : BindingCloneAlgebra.Algebra.{0} S}
    (Γ Δ : Ctx S) (s : S.Srt)
    (h : FreeBindingClone.Hom (modelAt equations (substitutionBase equations Γ Δ s)) B)
    {Θ : Context R B}
    (φ : Hom R B Θ (pushContext R h ((Context.empty R _).cons R _
      (substitutionJudgment equations Γ Δ s)))) :
    interpret R B (seeds R B (pushContext R h ((Context.empty R _).cons R _
          (substitutionJudgment equations Γ Δ s))))
        (freeModel R B (seeds R B Θ)) φ
        (mapJudgment h (substJudgment (substitutionJudgment equations Γ Δ s)
          (substitutionEnv equations Γ Δ s)))
        (pushTree R h (pushSeed R h ((Context.empty R _).cons R _
          (substitutionJudgment equations Γ Δ s)))
          (substJudgment (substitutionJudgment equations Γ Δ s) (substitutionEnv equations Γ Δ s))
          (substitutionTree R equations Γ Δ s)) =
      substitute R B (seeds R B Θ) (mapJudgment h (substitutionJudgment equations Γ Δ s))
        (atSlot R B φ (first R (substitutionJudgment equations Γ Δ s) (Context.empty R _)))
        (fun t v => h.raw.map (substitutionEnv equations Γ Δ s t v))
        (mapJudgment h (substJudgment (substitutionJudgment equations Γ Δ s)
          (substitutionEnv equations Γ Δ s)))
        (mapJudgment_substJudgment h (substitutionJudgment equations Γ Δ s)
          (substitutionEnv equations Γ Δ s)).symm := by
  let variable_ := (Context.empty R (modelAt equations (substitutionBase equations Γ Δ s))).cons R _
    (substitutionJudgment equations Γ Δ s)
  have pushed := pushTree_substitute R h (pushSeed R h variable_)
    (substitutionJudgment equations Γ Δ s) (leaf R variable_ (first R _ (Context.empty R _)))
    (substitutionEnv equations Γ Δ s)
    (substJudgment (substitutionJudgment equations Γ Δ s) (substitutionEnv equations Γ Δ s)) rfl
  have atVariable : interpret R B (seeds R B (pushContext R h variable_))
      (freeModel R B (seeds R B Θ)) φ (mapJudgment h (substitutionJudgment equations Γ Δ s))
      (pushTree R h (pushSeed R h variable_) (substitutionJudgment equations Γ Δ s)
        (leaf R variable_ (first R _ (Context.empty R _)))) =
        atSlot R B φ (first R _ (Context.empty R _)) :=
    (congrArg (interpret R B _ _ φ _)
      (pushTree_leaf R h variable_ (first R _ (Context.empty R _)))).trans (interpret_leaf R φ _)
  refine (congrArg (interpret R B (seeds R B (pushContext R h variable_))
    (freeModel R B (seeds R B Θ)) φ _) pushed).trans ?_
  refine (IntrinsicScopedLocalActedFree.interpret_substitute R B _ _ φ _ _ _ _ _).trans ?_
  exact congrArg (fun tree => substitute R B (seeds R B Θ) _ tree _ _ _) atVariable

/-- **Substituting a tree factors through the generic substitution.** -/
theorem singleArrow_comp_substitutionRep {a : Classifier R equations}
    (j : Judgment (modelAt equations a.base)) {Δ : Ctx S}
    (env : BindingSubstitutionAlgebra.Environment S
      (modelAt equations a.base).substitution.Carrier j.1 Δ)
    (tree : Tree R _ (seeds R _ (events R equations a)) j) :
    singleArrow R equations (substitutionBaseOf equations j env)
        (substitutionJudgment equations j.1 Δ j.2.1)
        (cast (congrArg (Tree R _ (seeds R _ (events R equations a)))
          (mapJudgment_substitutionBaseOf equations j env).symm) tree) ≫
      substitutionRep R equations j.1 Δ j.2.1 =
    rep R equations (substJudgment j env) (substitute R _ _ j tree env _ rfl) := by
  let u := substitutionBaseOf equations j env
  let w := singleArrow R equations u (substitutionJudgment equations j.1 Δ j.2.1)
    (cast (congrArg (Tree R _ (seeds R _ (events R equations a)))
      (mapJudgment_substitutionBaseOf equations j env).symm) tree)
  have environment : HEq (fun t v => (modelMap equations u).raw.map
      (substitutionEnv equations j.1 Δ j.2.1 t v)) env :=
    heq_of_eq (funext fun _ => funext fun v => substitutionBaseOf_env equations j env v)
  have judgmentEq : mapJudgment (modelMap equations u)
      (substJudgment (substitutionJudgment equations j.1 Δ j.2.1)
        (substitutionEnv equations j.1 Δ j.2.1)) = substJudgment j env :=
    (mapJudgment_substJudgment _ _ _).trans
      (substJudgment_congr (mapJudgment_substitutionBaseOf equations j env) environment)
  refine (comp_rep R equations w _ (substitutionTree R equations j.1 Δ j.2.1)).trans
    (eq_of_heq ?_)
  refine rep_heq R equations (X := a.base) (Γ := events R equations a)
    (Γ' := events R equations a) rfl judgmentEq ?_
  refine (heq_of_eq (interpret_pushTree_substitutionTree R equations j.1 Δ j.2.1
    (modelMap equations u) w.fiber)).trans ?_
  refine IntrinsicScopedLocalActedFree.substitute_heq R _ _
    (mapJudgment_substitutionBaseOf equations j env) ?_ environment judgmentEq _ _
  exact (heq_of_eq (atSlot_singleArrow R equations _ _ _)).trans (cast_heq _ _)

/-! ## Rule nodes through the generic occurrence -/

/-- The trees at the premises of an occurrence, at the reindexed premises of
the generic occurrence. -/
def ruleSlots {a : Classifier R equations} (occurrence : Instance R (modelAt equations a.base))
    (children : ∀ position : Fin (R.get occurrence.index).2.premises.length,
      Tree R _ (seeds R _ (events R equations a)) (childJudgment R _ occurrence position))
    (position : Fin (R.get occurrence.index).2.premises.length) :
    Tree R _ (seeds R _ (events R equations a))
      ((pushContext R (modelMap equations (ruleBaseOf R equations occurrence))
        (events R equations (ruleObject R equations occurrence.index occurrence.ambient))).listed.label
          position) :=
  cast (congrArg (Tree R _ (seeds R _ (events R equations a)))
    (((childJudgment_congr R (mapInstance_ruleBaseOf R equations occurrence) position position
      HEq.rfl).symm.trans (mapInstance_child R (modelMap equations (ruleBaseOf R equations occurrence))
        (ruleInstance R equations occurrence.index occurrence.ambient) position)))) (children position)

/-- The trees of the arrow of an occurrence. -/
def ruleArrowTrees {a : Classifier R equations} (occurrence : Instance R (modelAt equations a.base))
    (children : ∀ position : Fin (R.get occurrence.index).2.premises.length,
      Tree R _ (seeds R _ (events R equations a)) (childJudgment R _ occurrence position)) :
    Hom R (modelAt equations a.base) (events R equations a)
      (pushContext R (modelMap equations (ruleBaseOf R equations occurrence))
        (events R equations (ruleObject R equations occurrence.index occurrence.ambient))) :=
  ofSlots R _ (ruleSlots R equations occurrence children)

/-- An arrow into the generic object of a rule: the map of an occurrence of
the rule, with a tree at each premise. -/
def ruleArrow {a : Classifier R equations} (occurrence : Instance R (modelAt equations a.base))
    (children : ∀ position : Fin (R.get occurrence.index).2.premises.length,
      Tree R _ (seeds R _ (events R equations a)) (childJudgment R _ occurrence position)) :
    a ⟶ ruleObject R equations occurrence.index occurrence.ambient :=
  arrow R equations (ruleBaseOf R equations occurrence) (ruleArrowTrees R equations occurrence children)

/-- The arrow of an occurrence carries each premise's tree. -/
theorem atSlot_ruleArrow {a : Classifier R equations}
    (occurrence : Instance R (modelAt equations a.base))
    (children : ∀ position : Fin (R.get occurrence.index).2.premises.length,
      Tree R _ (seeds R _ (events R equations a)) (childJudgment R _ occurrence position))
    (position : Fin (R.get occurrence.index).2.premises.length) :
    HEq (atSlot R _ (ruleArrowTrees R equations occurrence children) position) (children position) :=
  (heq_of_eq (atSlot_ofSlots R _ (Γ := events R equations a)
    (Δ := pushContext R (modelMap equations (ruleBaseOf R equations occurrence))
      (events R equations (ruleObject R equations occurrence.index occurrence.ambient)))
    (ruleSlots R equations occurrence children) position)).trans (cast_heq _ _)

/-- Reading a premise of the generic occurrence through the arrow of an
occurrence returns its tree. -/
theorem ruleArrow_comp_rep_leaf {a : Classifier R equations}
    (occurrence : Instance R (modelAt equations a.base))
    (children : ∀ position : Fin (R.get occurrence.index).2.premises.length,
      Tree R _ (seeds R _ (events R equations a)) (childJudgment R _ occurrence position))
    (position : Fin (R.get occurrence.index).2.premises.length) :
    HEq (ruleArrow R equations occurrence children ≫
        rep R equations (a := ruleObject R equations occurrence.index occurrence.ambient)
          (childJudgment R _ (ruleInstance R equations occurrence.index occurrence.ambient) position)
          (leaf R (events R equations (ruleObject R equations occurrence.index occurrence.ambient))
            position))
      (rep R equations (a := a) (childJudgment R _ occurrence position) (children position)) := by
  refine (heq_of_eq (comp_rep R equations (ruleArrow R equations occurrence children)
    (childJudgment R _ (ruleInstance R equations occurrence.index occurrence.ambient) position)
    (leaf R (events R equations (ruleObject R equations occurrence.index occurrence.ambient))
      position))).trans ?_
  refine rep_heq R equations (X := a.base) (Γ := events R equations a)
    (Γ' := events R equations a) rfl
    (((mapInstance_child R (modelMap equations (ruleBaseOf R equations occurrence))
      (ruleInstance R equations occurrence.index occurrence.ambient) position).symm.trans
      (childJudgment_congr R
      (mapInstance_ruleBaseOf R equations occurrence) position position HEq.rfl))) ?_
  refine (heq_of_eq ((congrArg (interpret R _ _ _ (ruleArrowTrees R equations occurrence children) _)
    (pushTree_leaf R (modelMap equations (ruleBaseOf R equations occurrence))
      (events R equations (ruleObject R equations occurrence.index occurrence.ambient)) position)).trans
    (interpret_leaf R (ruleArrowTrees R equations occurrence children) position))).trans ?_
  exact atSlot_ruleArrow R equations occurrence children position

/-- Free rule nodes at equal judgments agree for equal occurrences and
children. -/
theorem node_heq {A : BindingCloneAlgebra.Algebra.{0} S}
    {Seed : (sort : S.Srt) → State A sort → Type} {target target' : Judgment A}
    (sameTarget : target = target') {first second : Instance R A} (same : first = second)
    (firstConclusion : conclusionJudgment R A first = target)
    (secondConclusion : conclusionJudgment R A second = target')
    (firstChildren : ∀ position : Fin (R.get first.index).2.premises.length,
      Tree R A Seed (childJudgment R A first position))
    (secondChildren : ∀ position : Fin (R.get second.index).2.premises.length,
      Tree R A Seed (childJudgment R A second position))
    (children : ∀ firstPosition secondPosition, HEq firstPosition secondPosition →
      HEq (firstChildren firstPosition) (secondChildren secondPosition)) :
    HEq (Mettapedia.TypeTheory.IndexedPolynomial.Free.node (rules R A)
        (⟨first, firstConclusion⟩ : Shape R A target) firstChildren : Tree R A Seed target)
      (Mettapedia.TypeTheory.IndexedPolynomial.Free.node (rules R A)
        (⟨second, secondConclusion⟩ : Shape R A target') secondChildren : Tree R A Seed target') := by
  subst sameTarget
  exact heq_of_eq (IntrinsicScopedLocalActedFree.node_congr_instance R A Seed same _ _ _ _ children)

/-- Reindexing the generic rule tree and substituting an arrow's trees applies
the reindexed occurrence to the arrow's trees at the premises. -/
theorem interpret_pushTree_ruleTree {B : BindingCloneAlgebra.Algebra.{0} S}
    (index : Fin R.length) (Γ : Ctx S)
    (h : FreeBindingClone.Hom (modelAt equations (ruleBase R equations index Γ)) B)
    {Θ : Context R B}
    (φ : Hom R B Θ (pushContext R h (events R equations (ruleObject R equations index Γ)))) :
    interpret R B (seeds R B (pushContext R h (events R equations (ruleObject R equations index Γ))))
        (freeModel R B (seeds R B Θ)) φ
        (mapJudgment h (conclusionJudgment R _ (ruleInstance R equations index Γ)))
        (pushTree R h (pushSeed R h (events R equations (ruleObject R equations index Γ)))
          (conclusionJudgment R _ (ruleInstance R equations index Γ)) (ruleTree R equations index Γ)) =
      Mettapedia.TypeTheory.IndexedPolynomial.Free.node (rules R B)
        (mapShape R h ⟨ruleInstance R equations index Γ, rfl⟩)
        (fun position => cast (congrArg (Tree R B (seeds R B Θ))
          (mapInstance_child R h (ruleInstance R equations index Γ) position).symm)
          (atSlot R B φ position)) := by
  let premises := events R equations (ruleObject R equations index Γ)
  have pushed := IntrinsicScopedLocalActedBaseChange.pushTree_node R h (pushSeed R h premises)
    (⟨ruleInstance R equations index Γ, rfl⟩ :
      Shape R _ (conclusionJudgment R _ (ruleInstance R equations index Γ)))
    (fun position => leaf R premises position)
  refine (congrArg (interpret R B (seeds R B (pushContext R h premises))
    (freeModel R B (seeds R B Θ)) φ _) pushed).trans ?_
  refine (IntrinsicScopedLocalActedFree.interpret_node R B _ _ φ _ _).trans ?_
  refine congrArg (Mettapedia.TypeTheory.IndexedPolynomial.Free.node (rules R B)
    (holes := fun _ j => Holes B (seeds R B Θ) j) (base := ())
    (mapShape R h ⟨ruleInstance R equations index Γ, rfl⟩))
    (funext fun position => eq_of_heq ?_)
  refine (IntrinsicScopedLocalActedFibres.interpret_heq R _ φ
    (mapInstance_child R h (ruleInstance R equations index Γ) position) (heq_transport _ _)).trans ?_
  refine (heq_of_eq ((congrArg (interpret R B _ _ φ _) (pushTree_leaf R h premises position)).trans
    (interpret_leaf R φ position))).trans ?_
  exact (cast_heq _ _).symm

/-- **A rule node factors through the rule's generic occurrence.** -/
theorem ruleArrow_comp_ruleRep {a : Classifier R equations}
    (occurrence : Instance R (modelAt equations a.base))
    (children : ∀ position : Fin (R.get occurrence.index).2.premises.length,
      Tree R _ (seeds R _ (events R equations a)) (childJudgment R _ occurrence position)) :
    HEq (ruleArrow R equations occurrence children ≫
        ruleRep R equations occurrence.index occurrence.ambient)
      (rep R equations (a := a) (conclusionJudgment R _ occurrence)
        (Mettapedia.TypeTheory.IndexedPolynomial.Free.node (rules R _) ⟨occurrence, rfl⟩ children)) := by
  let u := ruleBaseOf R equations occurrence
  let w := ruleArrow R equations occurrence children
  have instanceEq := mapInstance_ruleBaseOf R equations occurrence
  have judgmentEq : mapJudgment (modelMap equations u)
      (conclusionJudgment R _ (ruleInstance R equations occurrence.index occurrence.ambient)) =
        conclusionJudgment R _ occurrence :=
    (mapInstance_conclusion R _ _).symm.trans (congrArg (conclusionJudgment R _) instanceEq)
  unfold ruleRep
  refine (heq_of_eq ((comp_rep R equations w _ (ruleTree R equations occurrence.index
    occurrence.ambient)).trans (congrArg (rep R equations _)
      (interpret_pushTree_ruleTree R equations occurrence.index occurrence.ambient
        (modelMap equations u) w.fiber)))).trans ?_
  refine rep_heq R equations (X := a.base) (Γ := events R equations a)
    (Γ' := events R equations a) rfl judgmentEq ?_
  refine node_heq R judgmentEq instanceEq _ _ _ _ ?_
  intro position position' same
  cases same
  exact (cast_heq _ _).trans (atSlot_ruleArrow R equations occurrence children position)

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier

end
