import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedClassifier
import Mettapedia.OSLF.Syntax.SecondOrderEquationClassArrows
import Mettapedia.CategoryTheory.PullbackCast

/-!
# The generic event object of the classifier

For a context and sort, the generic event object has two metavariables of
that arity and one event variable from the first to the second. The endpoints
of any judgment form a map into the pair context. A firing tree at a judgment
is therefore an arrow into the generic event object, and composition acts on
these trees by reindexing and substitution.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier

open _root_.CategoryTheory
open _root_.CategoryTheory.Pseudofunctor
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFiniteContext (Context seeds exactHole Hom)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFibres
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFree (Tree interpret freeModel)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedBaseChange (pushTree)
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)

variable {S : Signature} (R : List (LocalRule S))
variable {M : List (MetaArity S)} (equations : List (EqAxiom S M))

/-! ## The pair context and the generic judgment -/

/-- Two metavariables of one arity. -/
abbrev pairContext (Γ : Ctx S) (s : S.Srt) : Object S := ⟨[(Γ, s), (Γ, s)]⟩

/-- The equation context with two metavariables of one arity. -/
abbrev pairBase (Γ : Ctx S) (s : S.Srt) : Base equations := ⟨pairContext Γ s⟩

/-- The generic judgment: the first metavariable to the second. -/
def pairJudgment (Γ : Ctx S) (s : S.Srt) : Judgment (modelAt equations (pairBase equations Γ s)) :=
  ⟨Γ, s, termClass equations (metaVar (M := (pairContext Γ s).arities) ⟨0, by simp⟩),
    termClass equations (metaVar (M := (pairContext Γ s).arities) ⟨1, by simp⟩)⟩

/-- **The generic event object**: one event variable between the two
metavariables of a pair context. -/
noncomputable abbrev eventObject (Γ : Ctx S) (s : S.Srt) : Classifier R equations :=
  object R equations (pairBase equations Γ s)
    ((Context.empty R _).cons R _ (pairJudgment equations Γ s))

/-- The classes of a pair of endpoints, at the pair context. -/
def pairClasses {X : Object S} {Γ : Ctx S} {s : S.Srt}
    (first second : EquationTermClass (authoredEquationPresentation S equations) X Γ s) :
    ∀ i : Fin (pairContext Γ s).arities.length,
      EquationTermClass (authoredEquationPresentation S equations) X
        ((pairContext Γ s).arities.get i).1 ((pairContext Γ s).arities.get i).2
  | ⟨0, _⟩ => first
  | ⟨1, _⟩ => second
  | ⟨_ + 2, bound⟩ => absurd bound (by simp)

/-- The endpoints of a judgment, as a map into the pair context. -/
noncomputable def judgmentBase {X : Base equations} (J : Judgment (modelAt equations X)) :
    X ⟶ pairBase equations J.1 J.2.1 :=
  ofClasses equations (pairContext J.1 J.2.1).arities (pairClasses equations J.2.2.1 J.2.2.2)

/-- **The generic judgment read along the endpoints of a judgment is that
judgment.** -/
theorem mapJudgment_judgmentBase {X : Base equations} (J : Judgment (modelAt equations X)) :
    mapJudgment (modelMap equations (judgmentBase equations J))
      (pairJudgment equations J.1 J.2.1) = J := by
  obtain ⟨Γ, s, first, second⟩ := J
  exact congrArg₂ (fun one two => (⟨Γ, s, one, two⟩ : Judgment (modelAt equations X)))
    (ofClasses_metaVar equations (pairContext Γ s).arities (pairClasses equations first second)
      ⟨0, by simp⟩)
    (ofClasses_metaVar equations (pairContext Γ s).arities (pairClasses equations first second)
      ⟨1, by simp⟩)

/-- Precomposing the endpoints of a judgment gives the endpoints of the
reindexed judgment. -/
theorem comp_judgmentBase {X Y : Base equations} (u : Y ⟶ X) (J : Judgment (modelAt equations X)) :
    u ≫ judgmentBase equations J =
      judgmentBase equations (mapJudgment (modelMap equations u) J) := by
  obtain ⟨Γ, s, first, second⟩ := J
  refine (comp_ofClasses equations u _ _).trans (congrArg (ofClasses equations _) ?_)
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨_ + 2, bound⟩ => exact absurd bound (by simp)

/-! ## Arrows into objects with one event variable -/

/-- An arrow into an object with one event variable: a map of equation
contexts with a tree at the reindexed judgment. -/
noncomputable def singleArrow {a : Classifier R equations} {Y : Base equations} (u : a.base ⟶ Y)
    (j : Judgment (modelAt equations Y))
    (tree : Tree R _ (seeds R _ (events R equations a)) (mapJudgment (modelMap equations u) j)) :
    a ⟶ object R equations Y ((Context.empty R _).cons R _ j) :=
  arrow R equations u (ofSlots R _ fun position =>
    Fin.cases (motive := fun position => Tree R _ (seeds R _ (events R equations a))
      ((pushContext R (modelMap equations u) ((Context.empty R _).cons R _ j)).listed.label position))
      tree (fun i => i.elim0) position)

/-- An arrow into an object with one event variable carries its tree at the
variable. -/
theorem atSlot_singleArrow {a : Classifier R equations} {Y : Base equations} (u : a.base ⟶ Y)
    (j : Judgment (modelAt equations Y))
    (tree : Tree R _ (seeds R _ (events R equations a)) (mapJudgment (modelMap equations u) j)) :
    atSlot R _ (singleArrow R equations u j tree).fiber (first R j (Context.empty R _)) = tree :=
  atSlot_ofSlots R _ _ _

/-- Arrows into an object with one event variable agree when their
assignments and their trees agree. -/
theorem single_hom_ext {a : Classifier R equations} {Y : Base equations}
    {j : Judgment (modelAt equations Y)}
    {x y : a ⟶ object R equations Y ((Context.empty R _).cons R _ j)} (base : x.base = y.base)
    (slot : HEq (atSlot R _ x.fiber (first R j (Context.empty R _)))
      (atSlot R _ y.fiber (first R j (Context.empty R _)))) :
    x = y :=
  hom_ext_heq R equations base fun position =>
    Fin.cases (motive := fun position =>
      HEq (atSlot R _ x.fiber position) (atSlot R _ y.fiber position)) slot
      (fun i => i.elim0) position

/-! ## Trees are arrows into the generic event object -/

/-- **The arrow of a firing tree**: the endpoints of its judgment, with the
tree at the event variable. -/
noncomputable def rep {a : Classifier R equations} (J : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) J) :
    a ⟶ eventObject R equations J.1 J.2.1 :=
  singleArrow R equations (judgmentBase equations J) (pairJudgment equations J.1 J.2.1)
    (cast (congrArg (Tree R _ (seeds R _ (events R equations a)))
      (mapJudgment_judgmentBase equations J).symm) tree)

theorem rep_base {a : Classifier R equations} (J : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) J) :
    (rep R equations J tree).base = judgmentBase equations J :=
  rfl

/-- The arrow of a tree carries the tree at the event variable. -/
theorem atSlot_rep {a : Classifier R equations} (J : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) J) :
    HEq (atSlot R _ (rep R equations J tree).fiber
        (first R (pairJudgment equations J.1 J.2.1) (Context.empty R _))) tree :=
  (heq_of_eq (atSlot_singleArrow R equations _ _ _)).trans (cast_heq _ _)

/-- Arrows into the generic event object agree when their assignments and
their trees agree. -/
theorem eventObject_hom_ext {a : Classifier R equations} {Γ : Ctx S} {s : S.Srt}
    {x y : a ⟶ eventObject R equations Γ s} (base : x.base = y.base)
    (slot : HEq (atSlot R _ x.fiber (first R (pairJudgment equations Γ s) (Context.empty R _)))
      (atSlot R _ y.fiber (first R (pairJudgment equations Γ s) (Context.empty R _)))) :
    x = y :=
  single_hom_ext R equations base slot

/-- **Composition acts on the tree of an arrow into the generic event**:
reindex the tree along the first assignment and substitute the first arrow's
trees for its variables. -/
theorem comp_rep {a b : Classifier R equations} (w : a ⟶ b)
    (J : Judgment (modelAt equations b.base))
    (tree : Tree R _ (seeds R _ (events R equations b)) J) :
    w ≫ rep R equations J tree =
      rep R equations (mapJudgment (modelMap equations w.base) J)
        (interpret R _ _ (freeModel R _ (seeds R _ (events R equations a))) w.fiber _
          (pushTree R (modelMap equations w.base)
            (pushSeed R (modelMap equations w.base) (events R equations b)) J tree)) := by
  apply eventObject_hom_ext R equations
  · exact comp_judgmentBase equations w.base J
  · refine (atSlot_comp R equations w (rep R equations J tree) _).trans ?_
    refine HEq.trans ?_ (atSlot_rep R equations _ _).symm
    exact interpret_heq R _ w.fiber
      (congrArg (mapJudgment (modelMap equations w.base)) (mapJudgment_judgmentBase equations J))
      (pushTree_heq R (modelMap equations w.base)
        (pushSeed R (modelMap equations w.base) (events R equations b))
        (mapJudgment_judgmentBase equations J) (atSlot_rep R equations J tree))

/-- Reading a listed variable through an arrow reads the arrow's tree at that
variable. -/
theorem comp_rep_leaf {a b : Classifier R equations} (w : a ⟶ b)
    (position : Fin (events R equations b).listed.length) :
    w ≫ rep R equations _ (leaf R (events R equations b) position) =
      rep R equations (a := a)
        (mapJudgment (modelMap equations w.base) ((events R equations b).listed.label position))
        (atSlot R _ w.fiber position) :=
  (comp_rep R equations w _ _).trans (congrArg (rep R equations _)
    ((congrArg (interpret R _ _ _ w.fiber _) (pushTree_leaf R _ _ position)).trans
      (interpret_leaf R w.fiber position)))

/-- The arrow of the tree at the event variable of the generic event object
is the identity. -/
theorem rep_leaf_eventObject (Γ : Ctx S) (s : S.Srt) :
    rep R equations (a := eventObject R equations Γ s) (pairJudgment equations Γ s)
        (leaf R ((Context.empty R _).cons R _ (pairJudgment equations Γ s))
          (first R (pairJudgment equations Γ s) (Context.empty R _))) =
      𝟙 (eventObject R equations Γ s) := by
  apply eventObject_hom_ext R equations
  · have idBase : CoGrothendieck.Hom.base (𝟙 (eventObject R equations Γ s)) =
        𝟙 (pairBase equations Γ s) := rfl
    have repBase : (rep R equations (a := eventObject R equations Γ s) (pairJudgment equations Γ s)
        (leaf R ((Context.empty R _).cons R _ (pairJudgment equations Γ s))
          (first R (pairJudgment equations Γ s) (Context.empty R _)))).base =
        ofClasses equations (pairContext Γ s).arities
          (pairClasses equations (pairJudgment equations Γ s).2.2.1
            (pairJudgment equations Γ s).2.2.2) := rfl
    refine repBase.trans (Eq.trans ?_ idBase.symm)
    refine Eq.trans (congrArg (ofClasses equations (pairContext Γ s).arities) ?_)
      (ofClasses_metaVar_id equations (pairContext Γ s).arities)
    funext i
    match i with
    | ⟨0, _⟩ => rfl
    | ⟨1, _⟩ => rfl
    | ⟨_ + 2, bound⟩ => exact absurd bound (by simp)
  · exact (atSlot_rep R equations _ _).trans
      (atSlot_id_heq R equations (eventObject R equations Γ s) _).symm

/-- An arrow of event contexts over one equation context substitutes its trees
into the tree of an arrow into the generic event. -/
theorem inclusion_comp_rep {X : Base equations} {Γ Δ : Context R (modelAt equations X)}
    (φ : Γ ⟶ Δ) (J : Judgment (modelAt equations X))
    (tree : Tree R _ (seeds R _ Δ) J) :
    (inclusion R equations X).map φ ≫ rep R equations (a := object R equations X Δ) J tree =
      rep R equations (a := object R equations X Γ) J
        (interpret R _ _ (freeModel R _ (seeds R _ Γ)) φ J tree) := by
  have judgmentEq : mapJudgment (modelMap equations (𝟙 X)) J = J :=
    (congrArg (fun h => mapJudgment h J) (modelMap_id equations X)).trans
      (AuthoredPositionedRulePolynomial.mapJudgment_id _ _)
  apply eventObject_hom_ext R equations
  · exact Category.id_comp _
  · refine (atSlot_comp R equations (a := object R equations X Γ) (b := object R equations X Δ)
      ((inclusion R equations X).map φ)
      (rep R equations (a := object R equations X Δ) J tree) _).trans ?_
    refine HEq.trans ?_ (atSlot_rep R equations (a := object R equations X Γ) _ _).symm
    erw [Mettapedia.CategoryTheory.StrictCoGrothendieck.ι_map_fiber]
    refine interpret_comp_eqToHom R φ _
      ((congrArg (mapJudgment (modelMap equations (𝟙 X)))
        (mapJudgment_judgmentBase equations J)).trans judgmentEq) ?_
    exact (pushTree_heq_of_eq_id R (modelMap_id equations X) Δ
      (mapJudgment (modelMap equations (judgmentBase equations J))
        (pairJudgment equations J.1 J.2.1)) _).trans
      (atSlot_rep R equations (a := object R equations X Δ) J tree)

/-- A cast of event contexts leaves the tree of an arrow into the generic
event unchanged. -/
theorem eqToHom_comp_rep {X : Base equations} {Γ Γ' : Context R (modelAt equations X)}
    (same : Γ = Γ') (J : Judgment (modelAt equations X))
    {tree : Tree R _ (seeds R _ Γ) J} {tree' : Tree R _ (seeds R _ Γ') J}
    (sameTree : HEq tree tree') :
    eqToHom (congrArg (object R equations X) same) ≫
        rep R equations (a := object R equations X Γ') J tree' =
      rep R equations (a := object R equations X Γ) J tree := by
  subst same
  cases sameTree
  rw [eqToHom_refl, Category.id_comp]

/-- A cast of event contexts has the identity assignment. -/
theorem eqToHom_object_base {X : Base equations} {Γ Γ' : Context R (modelAt equations X)}
    (same : Γ = Γ') :
    (eqToHom (congrArg (object R equations X) same)).base = 𝟙 X := by
  subst same
  rfl

/-- The use of a variable in equal contexts. -/
theorem leaf_heq {A : BindingCloneAlgebra.Algebra.{0} S} {Γ Γ' : Context R A} (same : Γ = Γ')
    {position : Fin Γ.listed.length} {position' : Fin Γ'.listed.length}
    (samePosition : HEq position position') :
    HEq (leaf R Γ position) (leaf R Γ' position') := by
  subst same
  cases samePosition
  rfl

/-! ## Forgetting the event variables -/

/-- Forget every event variable. -/
noncomputable def toProgram (a : Classifier R equations) :
    a ⟶ (programSection R equations).obj a.base :=
  arrow R equations (𝟙 a.base) (toEmpty R _ _ rfl)

/-- Arrows into an event-free object agree when their assignments agree. -/
theorem programSection_hom_ext {a : Classifier R equations} {X : Base equations}
    {x y : a ⟶ (programSection R equations).obj X} (base : x.base = y.base) : x = y :=
  hom_ext_heq R equations base fun position => position.elim0

theorem comp_toProgram {a b : Classifier R equations} (w : a ⟶ b) :
    w ≫ toProgram R equations b = toProgram R equations a ≫ (programSection R equations).map w.base :=
  programSection_hom_ext R equations ((Category.comp_id w.base).trans (Category.id_comp w.base).symm)

/-- The arrow of a tree forgets its event variables into the endpoints of its
judgment. -/
theorem rep_toProgram {a : Classifier R equations} (J : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) J) :
    rep R equations J tree ≫ toProgram R equations (eventObject R equations J.1 J.2.1) =
      toProgram R equations a ≫ (programSection R equations).map (judgmentBase equations J) :=
  programSection_hom_ext R equations
    ((Category.comp_id _).trans (Category.id_comp _).symm)

/-- Forgetting the event variables of the generic event is its projection. -/
theorem projection_eq_toProgram (X : Base equations) (J : Judgment (modelAt equations X)) :
    projection R equations ((programSection R equations).obj X) J =
      toProgram R equations (object R equations X ((Context.empty R _).cons R _ J)) :=
  programSection_hom_ext R equations rfl

/-! ## The first variable of an event context -/

/-- The endpoints of the generic judgment are the identity. -/
theorem judgmentBase_pairJudgment (Γ : Ctx S) (s : S.Srt) :
    judgmentBase equations (pairJudgment equations Γ s) = 𝟙 (pairBase equations Γ s) := by
  refine Eq.trans (congrArg (ofClasses equations (pairContext Γ s).arities) ?_)
    (ofClasses_metaVar_id equations (pairContext Γ s).arities)
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨_ + 2, bound⟩ => exact absurd bound (by simp)

/-- Arrows of trees over equal contexts at equal judgments with equal trees
agree. -/
theorem rep_heq {X : Base equations} {Γ Γ' : Context R (modelAt equations X)}
    (sameContext : Γ = Γ') {J J' : Judgment (modelAt equations X)} (same : J = J')
    {tree : Tree R _ (seeds R _ Γ) J} {tree' : Tree R _ (seeds R _ Γ') J'}
    (sameTree : HEq tree tree') :
    HEq (rep R equations (a := object R equations X Γ) J tree)
      (rep R equations (a := object R equations X Γ') J' tree') := by
  subst sameContext
  subst same
  cases sameTree
  rfl

/-- **Reindexing the generic event along an arrow is the arrow of the new
variable's bare use.** -/
theorem reindex_eventObject {b : Classifier R equations} {Γ : Ctx S} {s : S.Srt}
    (f : b ⟶ (programSection R equations).obj (pairBase equations Γ s)) :
    reindex R equations f (pairJudgment equations Γ s) =
      rep R equations (a := object R equations b.base ((events R equations b).cons R _
          (mapJudgment (modelMap equations f.base) (pairJudgment equations Γ s))))
        (mapJudgment (modelMap equations f.base) (pairJudgment equations Γ s))
        (leaf R ((events R equations b).cons R _
          (mapJudgment (modelMap equations f.base) (pairJudgment equations Γ s)))
          (first R _ (events R equations b))) := by
  apply eventObject_hom_ext R equations
  · exact (Category.comp_id f.base).symm.trans
      ((congrArg (f.base ≫ ·) (judgmentBase_pairJudgment equations Γ s)).symm.trans
        (comp_judgmentBase equations f.base _))
  · refine (heq_of_eq (atSlot_reindexEvents_first R equations f _)).trans ?_
    exact (atSlot_rep R equations (a := object R equations b.base ((events R equations b).cons R _
      (mapJudgment (modelMap equations f.base) (pairJudgment equations Γ s)))) _ _).symm

/-- Projections at equal judgments agree. -/
theorem projection_heq (a : Classifier R equations) {j j' : Judgment (modelAt equations a.base)}
    (same : j = j') : HEq (projection R equations a j) (projection R equations a j') := by
  subst same
  rfl

/-- A context is its first variable in front of the rest. -/
theorem cons_self_tail {A : BindingCloneAlgebra.Algebra.{0} S} (n : ℕ)
    (label : Fin (n + 1) → Judgment A) :
    (⟨⟨n + 1, label⟩⟩ : Context R A) = Context.cons R A (label 0) ⟨⟨n, Fin.tail label⟩⟩ :=
  congrArg (fun label => (⟨⟨n + 1, label⟩⟩ : Context R A)) (Fin.cons_self_tail label).symm

/-- Forget the first event variable. -/
noncomputable def dropFirst (X : Base equations) (n : ℕ)
    (label : Fin (n + 1) → Judgment (modelAt equations X)) :
    object R equations X ⟨⟨n + 1, label⟩⟩ ⟶ object R equations X ⟨⟨n, Fin.tail label⟩⟩ :=
  eqToHom (congrArg (object R equations X) (cons_self_tail R n label)) ≫
    projection R equations (object R equations X ⟨⟨n, Fin.tail label⟩⟩) (label 0)

/-- Forgetting the first variable is the projection away from it. -/
theorem dropFirst_heq (X : Base equations) (n : ℕ)
    (label : Fin (n + 1) → Judgment (modelAt equations X)) :
    HEq (dropFirst R equations X n label)
      (projection R equations (object R equations X ⟨⟨n, Fin.tail label⟩⟩) (label 0)) :=
  Mettapedia.CategoryTheory.eqToHom_comp_heq _ _

/-- Forgetting the first variable keeps the others. -/
theorem dropFirst_comp_rep (X : Base equations) (n : ℕ)
    (label : Fin (n + 1) → Judgment (modelAt equations X)) (position : Fin n) :
    dropFirst R equations X n label ≫
        rep R equations (a := object R equations X ⟨⟨n, Fin.tail label⟩⟩) (label position.succ)
          (leaf R ⟨⟨n, Fin.tail label⟩⟩ position) =
      rep R equations (a := object R equations X ⟨⟨n + 1, label⟩⟩) (label position.succ)
        (leaf R ⟨⟨n + 1, label⟩⟩ position.succ) := by
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (inclusion_comp_rep R equations
    (IntrinsicScopedLocalActedFibres.weaken R (label 0) ⟨⟨n, Fin.tail label⟩⟩) _ _)).trans ?_
  refine eqToHom_comp_rep R equations (cons_self_tail R n label) _ ?_
  exact (leaf_heq R (cons_self_tail R n label) HEq.rfl).trans
    (heq_of_eq ((interpret_leaf R
      (IntrinsicScopedLocalActedFibres.weaken R (label 0) ⟨⟨n, Fin.tail label⟩⟩) position).trans
      (atSlot_weaken R (label 0) ⟨⟨n, Fin.tail label⟩⟩ position))).symm

theorem dropFirst_toProgram (X : Base equations) (n : ℕ)
    (label : Fin (n + 1) → Judgment (modelAt equations X)) :
    dropFirst R equations X n label ≫
        toProgram R equations (object R equations X ⟨⟨n, Fin.tail label⟩⟩) =
      toProgram R equations (object R equations X ⟨⟨n + 1, label⟩⟩) := by
  apply programSection_hom_ext R equations
  exact (congrArg (· ≫ 𝟙 X) ((congrArg (· ≫ 𝟙 X)
    (eqToHom_object_base R equations (cons_self_tail R n label))).trans
      (Category.id_comp _))).trans (Category.id_comp _)

/-- An event context without variables is the event-free object. -/
noncomputable def fromProgram (X : Base equations)
    (label : Fin 0 → Judgment (modelAt equations X)) :
    (programSection R equations).obj X ⟶ object R equations X ⟨⟨0, label⟩⟩ :=
  arrow R equations (𝟙 X) (toEmpty R _ _ rfl)

instance isIso_toProgram_zero (X : Base equations)
    (label : Fin 0 → Judgment (modelAt equations X)) :
    IsIso (toProgram R equations (object R equations X ⟨⟨0, label⟩⟩)) :=
  ⟨⟨fromProgram R equations X label,
    hom_ext_heq R equations (Category.id_comp _) fun position => position.elim0,
    programSection_hom_ext R equations (Category.id_comp _)⟩⟩

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier
