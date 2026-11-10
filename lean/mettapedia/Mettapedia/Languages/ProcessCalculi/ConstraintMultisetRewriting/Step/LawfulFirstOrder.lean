import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.LawfulTransport
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.FirstOrderIndependence

/-!
# The one-frame transport is lawful, for faithful substitution actions

* **Guards** (`firstOrderGuards`): a first-order firing's guards are its checks and predicate queries,
  read at any present occurrences (`firstOrderGuard`). Its region at a solution is the occurrences
  whose labels its absence and count checks match there, and those its queries' regions hold there
  (`firstOrderRegion`); the guards read nothing else (`firstOrderGuard_inside`).
* **The frame equivalence.** Checks respect it for every action (`check_holds_respects`). A query's
  region is an arbitrary function of the substitution, so `Holds` respects the equivalence for every
  firing exactly when the action is faithful: substitutions that act alike are equal. A non-faithful
  action admits a query that tells apart two substitutions acting alike (`LawfulControls.holds_not_respecting`).
* **Lawful** (`firstOrderLawful`): for a faithful action, the residual is the firing itself carried
  along the identity, settlement is the identity, and results of isomorphic firings have the same
  solutions and occurrences. The first-order action is faithful (`firstOrder_faithful`).

## Controls

* **An unlawful residual changes independence** (`LawfulControls.unlawful_changes_independence`). The
  residual that keeps a firing's selection, guards and queries but drops its tells (`dropTells`) is a
  transport (`noTells`). The tells `X = 1` and `Y = 2` are independent for the lawful transport and
  not for it: dropping the tells leaves the two composite results with different solutions. By the
  content theorem it is therefore not lawful (`LawfulControls.noTells_not_lawful`).
* **Settlement that chooses a solution** (`settledBy`, `LawfulControls.settledBy_not_conservative`): the
  one-frame step whose result keeps the information instantiated by a fixed substitution satisfies
  every law of the interface, and is not conservative; its result asks `X = 1`, which its information
  does not (`LawfulControls.settledBy_asks_more`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open Interface (Frames Transport)
open MeTTaCalculus.OccurrenceCommits (regionOf fire)
open GuardFreeProcessOrders (SameUpTo)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

section Laws

variable (A : SubstitutionAction T S) (label : O → T)

/-- The occurrences a check reads at a solution: those whose label its pattern matches there. -/
def checkReads (σ : S) : Check T → O → Prop
  | .equal _ _, _ => False
  | .absent pattern, o => A.E (A.apply σ pattern) (A.apply σ (label o))
  | .count pattern _, o => A.E (A.apply σ pattern) (A.apply σ (label o))

/-- **The guards of a first-order firing**, read at any present occurrences. -/
def firstOrderGuard (f : Firing T S O) (σ : S) (W : Finset O) : Prop :=
  (∀ check ∈ f.rule.checks, check.Holds A σ label W) ∧
    ∀ query ∈ f.queries, (query.atSolution σ).Holds label W

/-- **The region of a first-order firing at a solution**: the occurrences its absence and count
checks match there, and the occurrences its queries' regions hold there. -/
def firstOrderRegion (f : Firing T S O) (σ : S) : Set O :=
  {o | (∃ check ∈ f.rule.checks, checkReads A label σ check o) ∨
    ∃ query ∈ f.queries, query.region σ (label o) = true}

omit [DecidableEq O] in
/-- A check reads present occurrences only where its pattern matches. -/
theorem check_holds_inside (σ : S) (check : Check T) {W W' : Finset O}
    (same : ∀ o, checkReads A label σ check o → (o ∈ W ↔ o ∈ W')) :
    check.Holds A σ label W ↔ check.Holds A σ label W' := by
  cases check with
  | equal _ _ => exact Iff.rfl
  | absent pattern =>
      show (∀ o ∈ W, ¬ A.E (A.apply σ pattern) (A.apply σ (label o))) ↔
        (∀ o ∈ W', ¬ A.E (A.apply σ pattern) (A.apply σ (label o)))
      constructor
      · intro absent o member matched
        exact absent o ((same o matched).mpr member) matched
      · intro absent o member matched
        exact absent o ((same o matched).mp member) matched
  | count pattern number =>
      show (Check.«matches» A σ label W pattern).card = number ↔
        (Check.«matches» A σ label W' pattern).card = number
      have equal : Check.«matches» A σ label W pattern = Check.«matches» A σ label W' pattern := by
        ext o
        simp only [Check.«matches», Finset.mem_filter]
        constructor
        · rintro ⟨member, matched⟩
          exact ⟨(same o matched).mp member, matched⟩
        · rintro ⟨member, matched⟩
          exact ⟨(same o matched).mpr member, matched⟩
      rw [equal]

omit [DecidableEq O] in
/-- **The guards read nothing outside the region.** -/
theorem firstOrderGuard_inside (f : Firing T S O) (σ : S) {W W' : Finset O}
    (same : ∀ o ∈ firstOrderRegion A label f σ, (o ∈ W ↔ o ∈ W')) :
    firstOrderGuard A label f σ W ↔ firstOrderGuard A label f σ W' := by
  refine and_congr (forall_congr' fun check => imp_congr_right fun member => ?_)
    (forall_congr' fun query => imp_congr_right fun member => ?_)
  · exact check_holds_inside A label σ check fun o reads => same o (Or.inl ⟨check, member, reads⟩)
  · show regionOf label W (query.region σ) = query.seen ↔ regionOf label W' (query.region σ) = query.seen
    have equal : regionOf label W (query.region σ) = regionOf label W' (query.region σ) := by
      ext o
      simp only [regionOf, Finset.mem_filter]
      constructor
      · rintro ⟨present, inRegion⟩
        exact ⟨(same o (Or.inr ⟨query, member, inRegion⟩)).mp present, inRegion⟩
      · rintro ⟨present, inRegion⟩
        exact ⟨(same o (Or.inr ⟨query, member, inRegion⟩)).mpr present, inRegion⟩
    rw [equal]

omit [DecidableEq O] in
/-- **Checks respect the frame equivalence for every action.** -/
theorem check_holds_respects {σ τ : S} (same : ∀ t, A.E (A.apply σ t) (A.apply τ t))
    (check : Check T) (W : Finset O) : check.Holds A σ label W ↔ check.Holds A τ label W := by
  have congrE : ∀ s t : T, A.E (A.apply σ s) (A.apply σ t) ↔ A.E (A.apply τ s) (A.apply τ t) :=
    fun s t => ⟨fun h => A.equivalence.trans (A.equivalence.symm (same s)) (A.equivalence.trans h (same t)),
      fun h => A.equivalence.trans (same s) (A.equivalence.trans h (A.equivalence.symm (same t)))⟩
  cases check with
  | equal left right => exact congrE left right
  | absent pattern =>
      show (∀ o ∈ W, ¬ A.E (A.apply σ pattern) (A.apply σ (label o))) ↔
        (∀ o ∈ W, ¬ A.E (A.apply τ pattern) (A.apply τ (label o)))
      exact forall_congr' fun o => imp_congr_right fun _ => not_congr (congrE _ _)
  | count pattern number =>
      show (Check.«matches» A σ label W pattern).card = number ↔
        (Check.«matches» A τ label W pattern).card = number
      have equal : Check.«matches» A σ label W pattern = Check.«matches» A τ label W pattern := by
        ext o
        simp only [Check.«matches», Finset.mem_filter]
        exact and_congr Iff.rfl (congrE _ _)
      rw [equal]

/-- **A faithful action**: substitutions that act alike are equal. -/
def Faithful : Prop := ∀ σ τ : S, (∀ t, A.E (A.apply σ t) (A.apply τ t)) → σ = τ

variable {A} in
/-- **Locality of the one-frame guards**, for a faithful action. -/
def firstOrderGuards (faithful : Faithful A) : (firstOrder A label).Guards where
  Guard f _ σ W := firstOrderGuard A label f σ W
  region f _ σ := firstOrderRegion A label f σ
  holds_iff _ _ _ := Iff.rfl
  respects _ _ σ τ same _ := by
    obtain rfl := faithful σ τ same
    exact Iff.rfl
  inside f _ σ _ _ same := firstOrderGuard_inside A label f σ same

/-- One-frame stores carried along the identity are themselves. -/
theorem applyStore_identity (store : EquationStore T) :
    (Frames.ofSubstitution A).applyStore (a := PUnit.unit) (b := PUnit.unit) A.identity store = store :=
  Frames.applyStore_id (X := Frames.ofSubstitution A) store

/-- One-frame morphisms agree when they act alike. -/
theorem agree_iff {σ τ : S} :
    (Frames.ofSubstitution A).Agree (a := PUnit.unit) (b := PUnit.unit) σ τ ↔
      ∀ t, A.E (A.apply σ t) (A.apply τ t) :=
  Iff.rfl

/-- The identity carried after the identity is the identity. -/
theorem agree_comp_identity (σ : S) :
    (Frames.ofSubstitution A).Agree (a := PUnit.unit) (b := PUnit.unit) (A.compose σ A.identity) σ :=
  fun t => by
    show A.E (A.apply (A.compose σ A.identity) t) (A.apply σ t)
    rw [A.apply_compose, A.apply_identity]
    exact A.equivalence.refl _

variable {A} in
/-- **Residual coherence in the one-frame instance.** -/
def firstOrderCoherent (faithful : Faithful A) :
    (firstOrderTransport A label).Coherent (firstOrderGuards label faithful) where
  carry _ _ _ := A.identity
  square _ _ _ := fun t => by
    show A.E (A.apply (A.compose A.identity A.identity) t)
      (A.apply (A.compose A.identity (A.compose A.identity A.identity)) t)
    simp only [A.apply_compose, A.apply_identity]
    exact A.equivalence.refl _
  amalgamate _ _ _ _ σ τ agree := by
    refine ⟨σ, agree_comp_identity A σ, fun t => ?_⟩
    have at_t : A.E (A.apply (A.compose σ A.identity) t)
        (A.apply (A.compose τ (A.compose A.identity A.identity)) t) := agree t
    simp only [A.apply_compose, A.apply_identity] at at_t
    show A.E (A.apply (A.compose σ A.identity) t) (A.apply τ t)
    rw [A.apply_compose, A.apply_identity]
    exact at_t
  separated _ _ _ _ ρ ρ' throughCarry _ :=
    (agree_comp_identity A ρ).symm.trans (throughCarry.trans (agree_comp_identity A ρ'))
  information {C} g _ f := by
    show (Frames.ofSubstitution A).Equivalent (f.selection.problem label f.rule (g.result label C))
      ((Frames.ofSubstitution A).applyStore A.identity (f.selection.problem label f.rule C) ++
        (Frames.ofSubstitution A).applyStore A.identity (g.selection.problem label g.rule C))
    rw [applyStore_identity, applyStore_identity]
    apply Frames.equivalent_of_mem_iff
    intro e
    simp only [Selection.problem, Firing.result, Selection.result, List.mem_append]
    tauto
  shapes _ _ _ := Iff.rfl
  guard _ _ f _ ρ W := by
    show firstOrderGuard A label f ρ W ↔ firstOrderGuard A label f (A.compose ρ A.identity) W
    rw [faithful _ _ (agree_comp_identity A ρ)]

variable {A} in
/-- **The one-frame transport is lawful** for a faithful action. -/
def firstOrderLawful (faithful : Faithful A) :
    (firstOrderTransport A label).Lawful (firstOrderGuards label faithful) where
  coherent := firstOrderCoherent label faithful
  conservative _ _ _ σ _ := ⟨σ, (agree_comp_identity A σ).symm⟩
  canonical {C} {f₁ f₂} i _ _ := by
    have identity : (Frames.ofSubstitution A).Agree (a := PUnit.unit) (b := PUnit.unit)
        i.frame.hom A.identity :=
      (agree_comp_identity A i.frame.hom).symm.trans i.extension
    have carried := identity.equivalent (f₁.selection.problem label f₁.rule C)
    rw [applyStore_identity] at carried
    have same : (Frames.ofSubstitution A).Equivalent (f₁.selection.problem label f₁.rule C)
        (f₂.selection.problem label f₂.rule C) :=
      (Frames.Equivalent.symm carried).trans i.information
    have selection : f₁.selection = f₂.selection := i.selection
    refine ⟨⟨⟨fun σ => same PUnit.unit σ, ?_⟩⟩⟩
    show fire C.present (f₁.selection.commit (T := T)) = fire C.present (f₂.selection.commit (T := T))
    rw [selection]

/-- **The first-order action is faithful.** -/
theorem firstOrder_faithful (signature : Mettapedia.Logic.LP.LPSignature) :
    Faithful (FirstOrder.action signature) :=
  fun _ _ same => funext fun v => same (.var v)

/-- The residual that keeps a firing's selection, guards and queries and drops its tells. -/
def dropTells (f : Firing T S O) : Firing T S O :=
  ⟨{ f.rule with tell := [] }, f.queries, f.selection⟩

/-- **The one-frame transport with the residual that drops tells.** -/
def noTells : Transport (firstOrder A label).toStep :=
  (firstOrderTransport A label).withResidual (fun _ _ f => dropTells f) (fun _ _ _ => rfl)
    (fun _ _ _ _ => rfl)

/-- **The one-frame step whose settlement instantiates the information by a fixed substitution.**
Every law of the interface holds. -/
def settledBy (u : S) :
    Interface.Step.Standard (Frames.ofSubstitution A) O (Configuration T O) (fun _ => Firing T S O) :=
  { firstOrder A label with
    preparedResult := fun {C} f _ => ⟨(Frames.ofSubstitution A).applyStore u (f.selection.problem label f.rule C),
      fire C.present (f.selection.commit (T := Unit))⟩
    present_preparedResult := fun _ _ => rfl
    preparedSettle := fun _ _ => u
    knowledge_preparedResult := fun _ _ => rfl
    result_refines := fun {_C} _ _ {_b} σ solved =>
      (Frames.models_applyStore (X := Frames.ofSubstitution A) u σ _).mp solved }

end Laws

namespace LawfulControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (label Run)
open RoundControls (tellOne tellTwo empty)

/-- `X = 1` and `Y` left free. -/
def xOne : Subst signature := fun n => if n = 0 then .const 1 else .var n

/-- `X = 1` and `Y = 2`. -/
def both : Subst signature := fun n => if n = 0 then .const 1 else .const 2

theorem tellOne_valid : tellOne.Valid A label empty := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨both, ?_⟩, by simp [tellOne]⟩,
    by simp [tellOne]⟩
  intro equation member
  have same : equation = (.var 0, .const 1) := by
    simpa [Selection.problem, Selection.equations, empty, tellOne] using member
  subst same
  rfl

theorem tellTwo_valid : tellTwo.Valid A label empty := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨both, ?_⟩, by simp [tellTwo]⟩,
    by simp [tellTwo]⟩
  intro equation member
  have same : equation = (.var 1, .const 2) := by
    simpa [Selection.problem, Selection.equations, empty, tellTwo] using member
  subst same
  rfl

theorem tellTwo_valid_after : tellTwo.Valid A label (tellOne.result label empty) := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨both, ?_⟩, by simp [tellTwo]⟩,
    by simp [tellTwo]⟩
  intro equation member
  have cases : equation = (.var 0, .const 1) ∨ equation = (.var 1, .const 2) := by
    simpa [Selection.problem, Selection.equations, Selection.result, Firing.result, empty, tellOne,
      tellTwo] using member
  rcases cases with rfl | rfl <;> rfl

theorem tellOne_valid_after : tellOne.Valid A label (tellTwo.result label empty) := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨both, ?_⟩, by simp [tellOne]⟩,
    by simp [tellOne]⟩
  intro equation member
  have cases : equation = (.var 1, .const 2) ∨ equation = (.var 0, .const 1) := by
    simpa [Selection.problem, Selection.equations, Selection.result, Firing.result, empty, tellOne,
      tellTwo] using member
  rcases cases with rfl | rfl <;> rfl

/-- **The lawful transport makes the two tells independent.** -/
theorem lawful_independent : (firstOrderTransport A label).Independent empty tellOne tellTwo :=
  (firstOrder_independent_iff A label).mpr
    ⟨tellOne_valid, tellTwo_valid, tellTwo_valid_after, tellOne_valid_after⟩

/-- **The residual that drops tells breaks the diamond**: after it, the two composite results have
different solutions. -/
theorem noTells_not_independent : ¬ (noTells A label).Independent empty tellOne tellTwo := by
  rintro ⟨_, _, _, _, ⟨⟨same⟩⟩⟩
  have one : A.Models xOne [(.var 0, .const 1)] := by
    intro equation member
    obtain rfl := List.mem_singleton.mp member
    rfl
  have two : A.Models xOne [(.var 1, .const 2)] := (same.1 xOne).mp one
  have told := two (.var 1, .const 2) (List.mem_singleton_self _)
  change xOne 1 = .const 2 at told
  simp [xOne] at told

/-- **An unlawful residual changes independence.** -/
theorem unlawful_changes_independence :
    (firstOrderTransport A label).Independent empty tellOne tellTwo ∧
      ¬ (noTells A label).Independent empty tellOne tellTwo :=
  ⟨lawful_independent, noTells_not_independent⟩

/-- **The residual that drops tells is not lawful**, by the content theorem. -/
theorem noTells_not_lawful :
    IsEmpty ((noTells A label).Lawful (firstOrderGuards label (firstOrder_faithful signature))) :=
  ⟨fun lawful => noTells_not_independent
    ((Transport.Lawful.independent_iff (firstOrderLawful label (firstOrder_faithful signature)) lawful
      fun _ _ => Iff.rfl).mp lawful_independent)⟩

/-- Neither takes, reads, tells, guards nor makes. -/
def idle : Run := ⟨⟨[], [], [], [], []⟩, [], ⟨[], [], []⟩⟩

theorem idle_valid : idle.Valid A label empty := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨Subst.id signature, ?_⟩, by simp [idle]⟩,
    by simp [idle]⟩
  intro equation member
  simp [Selection.problem, Selection.equations, empty, idle] at member

/-- `X` to `1`. -/
def toOne : Subst signature := Subst.single 0 (.const 1)

/-- **Settlement by a ground substitution is not conservative**: the identity solves the idle
firing's information and does not factor through `X ↦ 1`. -/
theorem settledBy_not_conservative : ¬ (settledBy A label toOne).ConservativeSettlement := by
  intro conservative
  obtain ⟨ρ, agree⟩ := conservative (s := empty) idle idle_valid PUnit.unit (Subst.id signature)
    (Interface.Frames.models_nil _)
  have at_X := agree (.var 0)
  change Subst.applyTerm (Subst.id signature) (.var 0) =
    Subst.applyTerm (Subst.comp ρ toOne) (.var 0) at at_X
  simp [Subst.id, Subst.comp, toOne, Subst.single, Subst.applyTerm] at at_X

/-- **The result asks more than the information**: after settling by `X ↦ 1`, every solution of the
result makes `X` equal to `1`; the information has a solution that does not. -/
theorem settledBy_asks_more :
    (Frames.ofSubstitution A).Entails (a := PUnit.unit)
        ((settledBy A label toOne).knowledge ((settledBy A label toOne).result (s := empty) idle idle_valid))
        (fun _ ρ => A.Models (Subst.comp ρ toOne) [(.var 0, .const 1)]) ∧
      ¬ (Frames.ofSubstitution A).Entails (a := PUnit.unit)
        ((settledBy A label toOne).information (s := empty) idle)
        (fun _ σ => A.Models σ [(.var 0, .const 1)]) := by
  refine ⟨fun _ ρ _ => ?_, fun asked => ?_⟩
  · intro equation member
    obtain rfl := List.mem_singleton.mp member
    show Subst.applyTerm (Subst.comp ρ toOne) (.var 0) = Subst.applyTerm (Subst.comp ρ toOne) (.const 1)
    simp [Subst.comp, toOne, Subst.single, Subst.applyTerm]
  · have holds := asked PUnit.unit (Subst.id signature) (by
      intro equation member
      simp [settledBy, firstOrder, Selection.problem, Selection.equations, empty, idle] at member)
    have at_X := holds (.var 0, .const 1) (List.mem_singleton_self _)
    change Subst.applyTerm (Subst.id signature) (.var 0) = Subst.applyTerm (Subst.id signature) (.const 1)
      at at_X
    simp [Subst.id, Subst.applyTerm] at at_X

/-! ### Without faithfulness, `Holds` does not respect the frame equivalence -/

/-- An action of two substitutions that both act as the identity. -/
def blind : SubstitutionAction Unit Bool where
  E := Eq
  equivalence := ⟨Eq.refl, Eq.symm, Eq.trans⟩
  apply _ t := t
  identity := true
  compose _ _ := true
  apply_identity _ := rfl
  apply_compose _ _ _ := rfl
  preserves _ _ _ same := same

/-- A query whose region holds every occurrence at `true` and none at `false`. -/
def split : PredicateQueryAdmission.Query Unit Bool Nat := ⟨fun σ _ => σ, ∅⟩

/-- Queries `split` and nothing else. -/
def splitter : Firing Unit Bool Nat := ⟨⟨[], [], [], [], []⟩, [split], ⟨[], [], []⟩⟩

/-- One present occurrence. -/
def one : Configuration Unit Nat := ⟨[], {0}⟩

/-- **A query tells apart two substitutions that act alike**, so no guards structure exists for this
action: `Holds` does not respect the frame equivalence. -/
theorem holds_not_respecting :
    (Frames.ofSubstitution blind).Agree (a := PUnit.unit) (b := PUnit.unit) true false ∧
      ¬ ((firstOrder blind (fun _ : Nat => ())).Holds (s := one) splitter PUnit.unit true ↔
        (firstOrder blind (fun _ : Nat => ())).Holds (s := one) splitter PUnit.unit false) := by
  refine ⟨fun _ => rfl, fun same => ?_⟩
  have atFalse : (firstOrder blind (fun _ : Nat => ())).Holds (s := one) splitter PUnit.unit false := by
    refine ⟨fun check member => by simp [splitter] at member, fun query member => ?_⟩
    obtain rfl := List.mem_singleton.mp member
    show regionOf (fun _ : Nat => ()) one.present (fun _ => false) = (∅ : Finset Nat)
    decide
  obtain ⟨-, queries⟩ := same.mpr atFalse
  have atTrue := queries split (List.mem_singleton_self _)
  change regionOf (fun _ : Nat => ()) one.present (fun _ => true) = (∅ : Finset Nat) at atTrue
  revert atTrue
  decide

/-- **Without faithfulness the one-frame step has no local guards.** -/
theorem blind_no_guards : IsEmpty (firstOrder blind (fun _ : Nat => ())).Guards :=
  ⟨fun G => holds_not_respecting.2 (G.holds_respects (s := one) splitter PUnit.unit
    holds_not_respecting.1)⟩

end LawfulControls

#print axioms check_holds_inside
#print axioms firstOrderGuard_inside
#print axioms check_holds_respects
#print axioms firstOrderGuards
#print axioms firstOrderCoherent
#print axioms firstOrderLawful
#print axioms firstOrder_faithful
#print axioms LawfulControls.lawful_independent
#print axioms LawfulControls.noTells_not_independent
#print axioms LawfulControls.unlawful_changes_independence
#print axioms LawfulControls.noTells_not_lawful
#print axioms LawfulControls.settledBy_not_conservative
#print axioms LawfulControls.settledBy_asks_more
#print axioms LawfulControls.holds_not_respecting
#print axioms LawfulControls.blind_no_guards

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
