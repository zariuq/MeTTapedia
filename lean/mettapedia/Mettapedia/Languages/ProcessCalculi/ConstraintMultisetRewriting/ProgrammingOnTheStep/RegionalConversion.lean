import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RegionalEquality
import Mettapedia.TypeTheory.BubbleConversion

/-!
# Bubble-local type checks on an actual firing

Use the comparison core's existing arithmetic conversion and its open
vector typing. A rule checks the inferred type against a requested one
in a specified bubble and publishes the requested type. The same open
operands can admit in one bubble and refuse in another, even though
all bubbles use exactly the same substitutions.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.RegionalConversion

open Interface RuleSyntax
open Mettapedia.TypeTheory.BubbleConversion Mettapedia.TypeTheory.BubbleConversion.Arith
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Expr

inductive Bubble where
  | weak | arith | arithPlus

/-- The three existing type-checking choices on the same expressions. -/
def equations : Bubble → AExpr → AExpr → Prop
  | .weak => fun _ _ => False
  | .arith => bubbleRules false
  | .arithPlus => bubbleRules true

private theorem stable (bubble : Bubble) : SubstitutionStable (equations bubble) := by
  cases bubble with
  | weak => intro left right rule; exact False.elim rule
  | arith => exact bubbleRules_stable false
  | arithPlus => exact bubbleRules_stable true

/-- Explicit substitution words acting on the comparison syntax. An
empty word is identity. A nonempty word may instantiate open terms. -/
abbrev Substitution := List (Nat × AExpr)

def substitute (word : Substitution) (term : AExpr) : AExpr :=
  word.foldl (fun term edit => substAt edit.1 edit.2 term) term

private theorem substitute_preserves (bubble : Bubble) (word : Substitution)
    {left right : AExpr} (converted : Convertible (equations bubble) left right) :
    Convertible (equations bubble) (substitute word left) (substitute word right) := by
  induction word generalizing left right with
  | nil => exact converted
  | cons edit rest ih =>
    exact ih (convertible_substAt (stable bubble) converted edit.1 edit.2)

def base : Frames (fun _ : Unit => AExpr) (fun _ _ => Substitution) where
  E := Eq
  equivalence _ := eq_equivalence
  act := substitute
  id _ := []
  comp later earlier := earlier ++ later
  act_id _ := rfl
  act_comp g f t := List.foldl_append (l := f) (l' := g)
  preserves := by
    intro a b σ left right same
    exact congrArg (substitute σ) same

def views : RegionalEquality base Bubble where
  conversion bubble _ :=
    ⟨Convertible (equations bubble),
      ⟨Relation.EqvGen.refl, fun h => Relation.EqvGen.symm _ _ h,
        fun h k => Relation.EqvGen.trans _ _ _ h k⟩⟩
  preserves := by
    intro bubble a b σ left right converted
    exact substitute_preserves bubble σ converted

abbrev LocatedExpr (_ : Unit) := Bubble × AExpr
abbrev TypeSelection := State LocatedExpr Nat

def initial : TypeSelection :=
  ⟨(), [], ∅, fun _ => (.weak, natType)⟩

def inferred : AExpr := vec (bvar 1)

def request (bubble : Bubble) (expected : AExpr) : Rule LocatedExpr :=
  ⟨(), ⟨[], [], [], [.equal (bubble, inferred) (bubble, expected)],
    [(bubble, expected)]⟩, []⟩

abbrev extension : Extensions.{0, 0, 0} (fun _ _ : Unit => Substitution) :=
  Extensions.identity views.frames

abbrev program (bubble : Bubble) (expected : AExpr) : Program LocatedExpr :=
  {request bubble expected}

def candidate (bubble : Bubble) (expected : AExpr) :
    Firing Nat extension (program bubble expected) initial.frame :=
  ⟨request bubble expected, rfl, PUnit.unit, [], ⟨[], [], [0]⟩, []⟩

private theorem shapes (bubble : Bubble) (expected : AExpr) :
    (candidate bubble expected).Shapes views.frames initial := by
  refine ⟨?_, List.nodup_nil, List.nodup_singleton 0, rfl, rfl, rfl, rfl⟩
  intro b g h
  refine ⟨h, ?_, ?_⟩
  · intro t mentioned
    simp [State.Mentions, initial] at mentioned
  · intro t _
    exact (views.frames.equivalence b).refl _

private theorem holds_iff (bubble : Bubble) (expected : AExpr) {b : Unit} (σ : Substitution) :
    (candidate bubble expected).Holds views.frames initial (b := b) σ ↔
      Convertible (equations bubble) (substitute σ inferred) (substitute σ expected) := by
  simp [Firing.Holds, Firing.opened, Firing.collectOpened, initial,
    candidate, request, RuleInstance.map, Check.map, checkHolds, RegionalEquality.frames,
    base, substitute]
  rfl

/-- The actual rule admits precisely the existing bubble conversion.
The reverse direction uses preservation under every substitution word. -/
theorem admits_iff_conversion (bubble : Bubble) (expected : AExpr) :
    (step views.frames Nat extension (program bubble expected)).Admits
      (s := initial) (candidate bubble expected) ↔ Convertible (equations bubble) inferred expected := by
  constructor
  · intro admitted
    exact (holds_iff bubble expected (b := ()) []).mp (admitted.2.2.2 () []
      (by simp [Frames.Models, Firing.information, Firing.matching, Firing.opened, candidate,
        request, RuleInstance.map, initial, Frames.applyStore]))
  · intro converted
    refine ⟨shapes bubble expected, ?_, ⟨(), [], ?_⟩, ?_⟩
    · change Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Enabled
        (fun _ : Nat => ()) ∅ ((⟨[], [], [0]⟩ : Selection Nat).commit (T := Unit))
      decide
    · simp [Frames.Models, Firing.information, Firing.matching, Firing.opened, candidate,
        request, RuleInstance.map, initial, Frames.applyStore]
    · intro b σ _
      exact (holds_iff bubble expected (b := b) σ).mpr (substitute_preserves bubble σ converted)

/-- The source type judgment on the open vector is exactly the
admission of this request, in each of the three bubbles. -/
theorem admits_iff_vector_typing (bubble : Bubble) (expected : AExpr) :
    (step views.frames Nat extension (program bubble expected)).Admits
      (s := initial) (candidate bubble expected) ↔
        HasTypeIn (equations bubble) vecContext (bvar 0) expected := by
  rw [admits_iff_conversion, hasTypeIn_iff]
  constructor
  · intro converted
    exact ⟨inferred, vecVariable_typed, converted⟩
  · rintro ⟨ty, typing, converted⟩
    rw [vecVariable_type_unique typing] at converted
    exact converted

def rightUnit : AExpr := vec (addE (bvar 1) zeroE)
def leftUnit : AExpr := vec (addE zeroE (bvar 1))
def longer : AExpr := vec (succE (bvar 1))

abbrev Accepted (bubble : Bubble) (expected : AExpr) : Prop :=
  (step views.frames Nat extension (program bubble expected)).Admits
    (s := initial) (candidate bubble expected)

theorem rightUnit_arith : Accepted .arith rightUnit :=
  (admits_iff_vector_typing .arith rightUnit).mpr (vec_addZero_inside false)

theorem rightUnit_weak_refused : ¬ Accepted .weak rightUnit := by
  intro accepted
  exact vec_addZero_not_global (hasTypeIn_none_iff.mp
    ((admits_iff_vector_typing .weak rightUnit).mp accepted))

theorem leftUnit_arithPlus : Accepted .arithPlus leftUnit :=
  (admits_iff_vector_typing .arithPlus leftUnit).mpr vec_zeroAdd_plus

theorem leftUnit_arith_refused : ¬ Accepted .arith leftUnit :=
  fun accepted => vec_zeroAdd_not_arith ((admits_iff_vector_typing .arith leftUnit).mp accepted)

theorem longer_arithPlus_refused : ¬ Accepted .arithPlus longer :=
  fun accepted => vec_succ_not_inside true ((admits_iff_vector_typing .arithPlus longer).mp accepted)

/-- Admission of a numeric vector index in either arithmetic bubble is
sound at every natural-number valuation of the open context. -/
theorem arithmetic_admission_preserves_length (plus : Bool) {index : AExpr}
    (numeric : IsNumeral index)
    (admitted : Accepted (if plus then .arithPlus else .arith) (vec index))
    (valuation : Nat → Nat) :
    value valuation (bvar 1) = value valuation index := by
  have converted := (admits_iff_conversion _ _).mp admitted
  have same : equations (if plus then .arithPlus else .arith) = bubbleRules plus := by
    cases plus <;> rfl
  rw [same] at converted
  exact vec_conv_sound plus (.var 1) numeric converted valuation

/-- The successful conversion publishes one occurrence at the requested
type and leaves the original equation store empty. -/
theorem result_of_request {bubble : Bubble} {expected : AExpr} (admitted : Accepted bubble expected) :
    let after := (step views.frames Nat extension (program bubble expected)).result
      (s := initial) (candidate bubble expected) admitted
    after.present = {0} ∧ after.label 0 = (bubble, expected) ∧ after.knowledge = [] := by
  simp [result_eq, Firing.result, Firing.information, Firing.row, Firing.opened, Firing.matching,
    relabel, initial, candidate, request, RuleInstance.map, RegionalEquality.frames, base,
    substitute, Frames.applyStore, Selection.commit,
    Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.fire]

/-- A decision on the two operands alone cannot agree with the actual
admission in every bubble. -/
theorem untagged_decision_impossible (accept : AExpr → AExpr → Prop)
    (agrees : ∀ bubble expected, Accepted bubble expected ↔ accept inferred expected) : False :=
  rightUnit_weak_refused ((agrees .weak rightUnit).mpr ((agrees .arith rightUnit).mp rightUnit_arith))

namespace SharedIndex

def unknown : AExpr := bvar 0
def index : AExpr := bvar 1

/-- The equality left by reading a vector through the arithmetic view.
Both indices still live in the common frame. -/
def residual : EquationStore (LocatedExpr ()) :=
  [((.arith, vec unknown), (.arith, vec index))]

def bindHome (term : AExpr) : EquationStore (LocatedExpr ()) :=
  [((.weak, unknown), (.weak, term))]

private theorem residual_models (σ : Substitution) :
    views.frames.Models (a := ()) (b := ()) σ residual ↔
      Convertible (bubbleRules false) (substitute σ (vec unknown)) (substitute σ (vec index)) := by
  rw [views.models_iff]
  constructor
  · intro h
    exact (h ((.arith, vec unknown), (.arith, vec index)) (List.mem_singleton_self _)).2
  · intro h e mem
    obtain rfl := List.mem_singleton.mp mem
    exact ⟨rfl, h⟩

private theorem home_models (term : AExpr) (σ : Substitution) :
    views.frames.Models (a := ()) (b := ()) σ (bindHome term) ↔
      substitute σ unknown = substitute σ term := by
  rw [views.models_iff]
  constructor
  · intro h
    exact convertible_none_iff.mp (h ((.weak, unknown), (.weak, term)) (List.mem_singleton_self _)).2
  · intro h e mem
    obtain rfl := List.mem_singleton.mp mem
    exact ⟨rfl, convertible_none_iff.mpr h⟩

private def plain : Substitution := [(0, bvar 0)]
private def plusZero : Substitution := [(0, addE (bvar 0) zeroE)]

private theorem plain_solves : views.frames.Models (a := ()) (b := ()) plain residual :=
  (residual_models _).mpr (Relation.EqvGen.refl _)

private theorem plusZero_solves : views.frames.Models (a := ()) (b := ()) plusZero residual :=
  (residual_models _).mpr ((conv_iff_norm false).mpr rfl)

/-- Eagerly binding the home unknown to the index loses a solution of
the arithmetic read. -/
theorem eager_home_binding_loses_solution :
    ¬ views.frames.Equivalent (a := ()) residual (residual ++ bindHome index) := by
  intro same
  have solved := (same () plusZero).mp plusZero_solves
  have home := (views.frames.models_append _ _ _).mp solved |>.2
  have equal := (home_models _ _).mp home
  change addE (bvar 0) zeroE = bvar 0 at equal
  cases equal

/-- The open residual allows both a core-equal and a core-apart solution.
In particular, existence of an apart witness cannot admit an apart ask. -/
theorem neither_equality_nor_apart_is_certain :
    (¬ views.frames.Entails (a := ()) residual (fun _ σ => substitute σ unknown = substitute σ index)) ∧
    (¬ views.frames.Entails (a := ()) residual (fun _ σ => substitute σ unknown ≠ substitute σ index)) := by
  constructor
  · intro certain
    have equal := certain () plusZero plusZero_solves
    change addE (bvar 0) zeroE = bvar 0 at equal
    cases equal
  · intro certain
    exact (certain () plain plain_solves) rfl

private theorem substitute_form (form : AExpr → AExpr)
    (commutes : ∀ depth replacement term,
      substAt depth replacement (form term) = form (substAt depth replacement term))
    (σ : Substitution) (term : AExpr) :
    substitute σ (form term) = form (substitute σ term) := by
  induction σ generalizing term with
  | nil => rfl
  | cons edit rest ih =>
    change substitute rest (substAt edit.1 edit.2 (form term)) =
      form (substitute rest (substAt edit.1 edit.2 term))
    rw [commutes, ih]

theorem right_unit_binding_survives :
    views.frames.Solvable (a := ()) (residual ++ bindHome (addE index zeroE)) ∧
    views.frames.Entails (a := ()) (residual ++ bindHome (addE index zeroE))
      (fun _ σ => substitute σ unknown ≠ substitute σ index) := by
  constructor
  · refine ⟨(), plusZero, (views.frames.models_append _ _ _).mpr
      ⟨plusZero_solves, (home_models _ _).mpr rfl⟩⟩
  · rintro ⟨⟩ σ solved equal
    have home := (views.frames.models_append _ _ _).mp solved |>.2
    have binding := (home_models _ _).mp home
    rw [substitute_form (fun term => addE term zeroE) (fun _ _ _ => rfl), equal] at binding
    have sizes := congrArg sizeOf binding
    simp [addE] at sizes
    omega

/-- A core successor binding makes the watched arithmetic equation
inconsistent at every later assignment. -/
theorem successor_binding_refutes :
    ¬ views.frames.Solvable (a := ()) (residual ++ bindHome (succE index)) := by
  rintro ⟨⟨⟩, σ, solved⟩
  obtain ⟨read, bound⟩ := (views.frames.models_append _ _ _).mp solved
  have converted := (residual_models _).mp read
  have equal := (home_models _ _).mp bound
  rw [substitute_form succE (fun _ _ _ => rfl)] at equal
  rw [substitute_form vec (fun _ _ _ => rfl) σ unknown,
    substitute_form vec (fun _ _ _ => rfl) σ index, equal] at converted
  have normalized := (conv_iff_norm false).mp converted
  rw [norm_vec, norm_vec, norm_succE] at normalized
  have same := (Expr.app.inj normalized).2
  have sizes := congrArg sizeOf same
  simp [succE] at sizes

/-- Two physical occurrences may have convertible labels. -/
def rows : Bool → LocatedExpr () :=
  fun second => (.arith, if second then vec index else vec (addE index zeroE))

/-- The retained equation entails the whole read even with an open index. -/
theorem collect_two (σ : Substitution) (solved : views.frames.Models (a := ()) (b := ()) σ residual) :
    matchesAt views.frames (a := ()) (b := ()) σ rows Finset.univ (.arith, vec unknown) = Finset.univ := by
  have first := (residual_models σ).mp solved
  have other := substitute_preserves .arith σ
    ((conv_iff_norm false (e := vec index) (e' := vec (addE index zeroE))).mpr rfl)
  ext occurrence
  rw [views.mem_matchesAt]
  constructor
  · exact fun found => found.1
  · intro present
    refine ⟨present, rfl, ?_⟩
    cases occurrence
    · exact Relation.EqvGen.trans _ _ _ first other
    · exact first

theorem count_two :
    views.frames.Entails (a := ()) residual
      (fun b σ => checkHolds views.frames (a := ()) (b := b) σ rows Finset.univ (.count (.arith, vec unknown) 2)) := by
  rintro ⟨⟩ σ solved
  show (matchesAt views.frames (a := ()) (b := ()) σ rows Finset.univ (.arith, vec unknown)).card = 2
  rw [collect_two σ solved]
  decide

end SharedIndex

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgrammingOnTheStep.RegionalConversion
