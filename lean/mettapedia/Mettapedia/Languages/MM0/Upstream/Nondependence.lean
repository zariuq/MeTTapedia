import Mettapedia.Languages.MM0.Kernel.Support
import Mettapedia.GSLT.Core.NonFactorization

/-!
# MM0 support is a bound on dependence

A bound variable contributes its own index. A regular variable contributes the
bound variables named in its declaration. A term symbol contributes nothing,
and an application contributes the union. That computation is already the
kernel support judgment. This module reads it.

Sorts are predicates on one carrier. A term symbol denotes a value of its
sort. Application is a binary operation on the carrier; a preterm does not
record a term declaration, so the reading does not invent one. A bound
variable denotes the value assigned to its index. A regular variable denotes
a function of the whole assignment. The dependency law says that function is
allowed to consult only the declared indices: assignments that agree on the
declaration give the same value. The function may ignore part of the
declaration. Nothing else is assumed. In particular the law does not say that
a declared index is actually read, and an empty support is a successful
answer rather than a refusal.

Forgetting an index means changing the value stored there and leaving every
other coordinate fixed. When the support misses that index, the denotation is
unchanged, so it factors through the one-point shadow that keeps nothing
about the forgotten value.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Upstream.Nondependence

open Mettapedia.Languages.MM0.Kernel
open Preterm
open Mettapedia.GSLT.Core.NonFactorization

variable {V : Type}

/-- A reading of sorts, term symbols, application and regular variables. -/
structure Interpretation (V : Type) where
  /-- Values that inhabit a sort. -/
  inSort : Nat → V → Prop
  /-- The value of a term symbol. Its support is empty. -/
  termDenote : Nat → V
  /-- The sort declared for a term symbol. -/
  termSort : Nat → Nat
  /-- The symbol's value lies in its declared sort. -/
  termInSort : ∀ symbol, inSort (termSort symbol) (termDenote symbol)
  /-- Application of two values. -/
  apply : V → V → V
  /-- A regular variable, as a function of a bound-variable assignment. -/
  regular : Nat → (Nat → V) → V

/-- Assignments that agree on the declared dependencies give the same regular value.
The function may ignore some declared indices. It may not consult any other index. -/
structure DependencyLaw (context : Context) (reading : Interpretation V) : Prop where
  regularAgrees :
    ∀ index sort dependencies (left right : Nat → V),
      context[index]? = some (.regular sort dependencies) →
      (∀ coordinate, coordinate ∈ dependencies → left coordinate = right coordinate) →
      reading.regular index left = reading.regular index right

/-- Bound values and regular results lie in the sort written on their binder. -/
structure SortLaw (context : Context) (reading : Interpretation V) (assignment : Nat → V) : Prop where
  boundInSort :
    ∀ index sort, context[index]? = some (.bound sort) →
      reading.inSort sort (assignment index)
  regularInSort :
    ∀ index sort dependencies, context[index]? = some (.regular sort dependencies) →
      reading.inSort sort (reading.regular index assignment)

/-- Replace the value stored at one index. -/
def withBound (assignment : Nat → V) (index : Nat) (value : V) : Nat → V :=
  fun coordinate => if coordinate = index then value else assignment coordinate

theorem withBound_self (assignment : Nat → V) (index : Nat) (value : V) :
    withBound assignment index value index = value := by
  unfold withBound
  rw [if_pos rfl]

theorem withBound_ne (assignment : Nat → V) (index coordinate : Nat) (value : V)
    (different : coordinate ≠ index) :
    withBound assignment index value coordinate = assignment coordinate := by
  unfold withBound
  rw [if_neg different]

/-- Denotation of a preterm. An undefined variable has no support derivation;
the clause below is only the total extension and is not used by the theorems. -/
def denote (reading : Interpretation V) (context : Context) (assignment : Nat → V) :
    Preterm → V
  | .var index =>
      match context[index]? with
      | some (.bound _) => assignment index
      | some (.regular _ _) => reading.regular index assignment
      | none => assignment index
  | .term symbol => reading.termDenote symbol
  | .app function argument =>
      reading.apply (denote reading context assignment function)
        (denote reading context assignment argument)

theorem denote_bound (reading : Interpretation V) (context : Context) (assignment : Nat → V)
    {index sort : Nat} (lookup : context[index]? = some (.bound sort)) :
    denote reading context assignment (.var index) = assignment index := by
  unfold denote
  rw [lookup]

theorem denote_regular (reading : Interpretation V) (context : Context) (assignment : Nat → V)
    {index sort : Nat} {dependencies : Finset Nat}
    (lookup : context[index]? = some (.regular sort dependencies)) :
    denote reading context assignment (.var index) = reading.regular index assignment := by
  unfold denote
  rw [lookup]

theorem denote_term (reading : Interpretation V) (context : Context) (assignment : Nat → V)
    (symbol : Nat) :
    denote reading context assignment (.term symbol) = reading.termDenote symbol := rfl

theorem denote_app (reading : Interpretation V) (context : Context) (assignment : Nat → V)
    (function argument : Preterm) :
    denote reading context assignment (.app function argument) =
      reading.apply (denote reading context assignment function)
        (denote reading context assignment argument) := rfl

/-- Changing a missed index does not change the denotation. -/
theorem denote_independent_of_missed {reading : Interpretation V} {context : Context}
    (law : DependencyLaw context reading)
    {source : Preterm} {support : Finset Nat}
    (derivation : Supports context source support) {forgotten : Nat}
    (assignment : Nat → V) (value : V) :
    forgotten ∉ support →
      denote reading context (withBound assignment forgotten value) source =
        denote reading context assignment source := by
  induction derivation with
  | @bound index _sort lookup =>
      intro misses
      have different : index ≠ forgotten := by
        intro same
        apply misses
        rw [← same]
        exact Finset.mem_singleton_self index
      rw [denote_bound reading context (withBound assignment forgotten value) lookup,
        denote_bound reading context assignment lookup]
      exact withBound_ne assignment forgotten index value different
  | @regular index sort dependencies lookup =>
      intro misses
      rw [denote_regular reading context (withBound assignment forgotten value) lookup,
        denote_regular reading context assignment lookup]
      apply law.regularAgrees index sort dependencies
      · exact lookup
      · intro coordinate member
        apply withBound_ne
        intro same
        apply misses
        rw [← same]
        exact member
  | term _ =>
      intro _
      rfl
  | @app _function _argument left right _functionDerivation _argumentDerivation
      ihFunction ihArgument =>
      intro misses
      rw [denote_app, denote_app]
      have functionMiss : forgotten ∉ left := fun member =>
        misses (Finset.mem_union_left right member)
      have argumentMiss : forgotten ∉ right := fun member =>
        misses (Finset.mem_union_right left member)
      rw [ihFunction functionMiss, ihArgument argumentMiss]

/-- A term whose support misses an index factors through forgetting that index. -/
theorem support_misses_factors {reading : Interpretation V} {context : Context}
    (law : DependencyLaw context reading)
    {source : Preterm} {support : Finset Nat}
    (derivation : Supports context source support) {index : Nat}
    (misses : index ∉ support) (assignment : Nat → V) :
    Factors (fun _ : V => ())
      (fun value => denote reading context (withBound assignment index value) source) :=
  ⟨fun _ => denote reading context assignment source,
    fun value => (denote_independent_of_missed law derivation assignment value misses).symm⟩

/-- The same denotation is constant while that index changes and the rest stays fixed. -/
theorem support_misses_constant {reading : Interpretation V} {context : Context}
    (law : DependencyLaw context reading)
    {source : Preterm} {support : Finset Nat}
    (derivation : Supports context source support) {index : Nat}
    (misses : index ∉ support) (assignment : Nat → V) (value other : V) :
    denote reading context (withBound assignment index value) source =
      denote reading context (withBound assignment index other) source :=
  (support_misses_factors law derivation misses assignment).constantOnFibers value other rfl

/-- Side condition for substitution. Every variable that occurs in the source,
at its own index, is replaced by a supported term whose support misses `index`.
Occurrence is the right test: a regular variable is replaced at its own index,
while its support is the declared dependency set. Support of each image is
read in the same context. This substitution does not extend the context, and
the condition does not ask the image support to sit inside the declaration. -/
def ImagesMiss (context : Context) (substitution : Substitution) (source : Preterm)
    (index : Nat) : Prop :=
  ∀ sourceIndex, Occurs sourceIndex source →
    ∃ image imageSupport,
      substitution sourceIndex = some image ∧
      Supports context image imageSupport ∧
      index ∉ imageSupport

/-- Under that side condition the result still misses the index. -/
theorem substitution_result_misses {context : Context} {substitution : Substitution}
    {source result : Preterm} {index : Nat}
    (step : Substitutes substitution source result) :
    ImagesMiss context substitution source index →
      ∃ resultSupport, Supports context result resultSupport ∧ index ∉ resultSupport := by
  induction step with
  | @var index value lookup =>
      intro side
      obtain ⟨image, imageSupport, imageLookup, imageSupported, imageMisses⟩ :=
        side index Occurs.var
      have imageEq : image = value := Option.some.inj (imageLookup.symm.trans lookup)
      subst imageEq
      exact ⟨imageSupport, imageSupported, imageMisses⟩
  | term symbol =>
      intro _
      exact ⟨∅, Supports.term symbol, Finset.notMem_empty index⟩
  | @app function argument _function' _argument' _stepFunction _stepArgument
      ihFunction ihArgument =>
      intro side
      have functionSide : ImagesMiss context substitution function index :=
        fun sourceIndex occurs => side sourceIndex (Occurs.function occurs)
      have argumentSide : ImagesMiss context substitution argument index :=
        fun sourceIndex occurs => side sourceIndex (Occurs.argument occurs)
      obtain ⟨leftSupport, leftDerivation, leftMisses⟩ := ihFunction functionSide
      obtain ⟨rightSupport, rightDerivation, rightMisses⟩ := ihArgument argumentSide
      refine ⟨leftSupport ∪ rightSupport, Supports.app leftDerivation rightDerivation, ?_⟩
      intro member
      rcases Finset.mem_union.mp member with belongs | belongs
      · exact leftMisses belongs
      · exact rightMisses belongs

/-- Substitution preserves factorization through forgetting the index when every
substituted image misses that index. -/
theorem substitution_preserves_factors {reading : Interpretation V} {context : Context}
    (law : DependencyLaw context reading) {substitution : Substitution}
    {source result : Preterm} {index : Nat}
    (step : Substitutes substitution source result)
    (side : ImagesMiss context substitution source index) (assignment : Nat → V) :
    Factors (fun _ : V => ())
      (fun value => denote reading context (withBound assignment index value) result) := by
  obtain ⟨resultSupport, resultDerivation, resultMisses⟩ := substitution_result_misses step side
  exact support_misses_factors law resultDerivation resultMisses assignment

/-! ## A two-element reading, and the freshness failure of ax-5 -/

/-- Every Boolean value inhabits every sort. The dependency examples below do
not need a narrower sort. -/
def booleanReading : Interpretation Bool where
  inSort := fun _ _ => True
  termDenote := fun _ => false
  termSort := fun _ => 0
  termInSort := fun _ => trivial
  apply := fun _ _ => false
  regular := fun _ _ => false

theorem boolean_law (context : Context) : DependencyLaw context booleanReading :=
  ⟨fun _index _sort _dependencies _left _right _lookup _agree => rfl⟩

theorem boolean_sorts (context : Context) (assignment : Nat → Bool) :
    SortLaw context booleanReading assignment :=
  ⟨fun _index _sort _lookup => trivial,
    fun _index _sort _dependencies _lookup => trivial⟩

/-- `x = y → ∀ x, x = y`, with `x` the first coordinate and `y` held fixed. -/
def ax5 (x y : Bool) : Prop :=
  x = y → ∀ x', x' = y

/-- At a two-element domain the instance is false when `x` and `y` are equal:
the antecedent holds and the other element breaks the consequent. -/
theorem ax5_false_when_equal (y : Bool) : ¬ ax5 y y := by
  intro holds
  have other : (!y) = y := holds rfl (!y)
  cases y <;> cases other

/-- The ax-5 instance is not constant once `x` is forgotten and `y` stays fixed.
The two assignments share the empty shadow, and the instance holds for the
value different from `y` while it fails for the value equal to `y`. -/
def ax5_fiber (y : Bool) :
    NonTrivialFiber (fun _ : Bool => ()) (fun x => ax5 x y) :=
  NonTrivialFiber.ofProp (a := !y) (b := y) rfl
    (by
      intro antecedent
      cases y <;> cases antecedent)
    (ax5_false_when_equal y)

/-! ## Substitution can introduce a dependence the source did not have -/

def twoBoundContext : Context := [.bound 0, .bound 0]

def sourceVar : Preterm := .var 0

def introducedVar : Preterm := .var 1

/-- Replace variable 0 by variable 1. -/
def exposingSubstitution : Substitution :=
  fun index => if index = 0 then some introducedVar else none

theorem exposing_substitutes : Substitutes exposingSubstitution sourceVar introducedVar := by
  apply Substitutes.var
  simp [exposingSubstitution, introducedVar]

theorem source_support : Supports twoBoundContext sourceVar {0} :=
  Supports.bound rfl

theorem introduced_support : Supports twoBoundContext introducedVar {1} :=
  Supports.bound rfl

theorem source_misses_introduced_index : (1 : Nat) ∉ ({0} : Finset Nat) := by
  intro member
  have : (1 : Nat) = 0 := Finset.mem_singleton.mp member
  cases this

/-- The image of the only occurring variable has 1 in its support, so the side
condition fails for this substitution. -/
theorem exposing_violates_side :
    ¬ ImagesMiss twoBoundContext exposingSubstitution sourceVar 1 := by
  intro side
  obtain ⟨image, imageSupport, imageLookup, imageSupported, imageMisses⟩ := side 0 Occurs.var
  have imageEq : image = introducedVar := by
    have lookupImage : exposingSubstitution 0 = some introducedVar := by
      simp [exposingSubstitution, introducedVar]
    exact Option.some.inj (imageLookup.symm.trans lookupImage)
  subst imageEq
  have supportEq : imageSupport = {1} :=
    Supports.deterministic imageSupported introduced_support
  rw [supportEq] at imageMisses
  exact imageMisses (Finset.mem_singleton_self 1)

/-- Forgetting index 1, the source still factors. -/
theorem source_forgets_introduced (assignment : Nat → Bool) :
    Factors (fun _ : Bool => ())
      (fun value =>
        denote booleanReading twoBoundContext (withBound assignment 1 value) sourceVar) :=
  support_misses_factors (boolean_law twoBoundContext) source_support
    source_misses_introduced_index assignment

/-- The substituted variable does not factor through forgetting index 1.
Its denotation is that coordinate, true at one value and false at the other. -/
def introduced_depends (assignment : Nat → Bool) :
    NonTrivialFiber (fun _ : Bool => ())
      (fun value =>
        denote booleanReading twoBoundContext (withBound assignment 1 value) introducedVar =
          true) :=
  NonTrivialFiber.ofProp (a := true) (b := false) rfl
    (by
      unfold introducedVar
      rw [denote_bound booleanReading twoBoundContext (withBound assignment 1 true) rfl]
      exact withBound_self assignment 1 true)
    (by
      intro holds
      unfold introducedVar at holds
      rw [denote_bound booleanReading twoBoundContext (withBound assignment 1 false) rfl,
        withBound_self] at holds
      cases holds)

/-- The side condition holds when variable 0 is replaced by a term symbol. -/
def erasingSubstitution : Substitution :=
  fun index => if index = 0 then some (.term 0) else none

theorem erasing_substitutes : Substitutes erasingSubstitution sourceVar (.term 0) := by
  apply Substitutes.var
  simp [erasingSubstitution]

theorem erasing_side : ImagesMiss twoBoundContext erasingSubstitution sourceVar 1 := by
  intro sourceIndex occurs
  cases occurs
  refine ⟨.term 0, ∅, ?_, Supports.term 0, Finset.notMem_empty 1⟩
  simp [erasingSubstitution]

theorem erasing_factors (assignment : Nat → Bool) :
    Factors (fun _ : Bool => ())
      (fun value =>
        denote booleanReading twoBoundContext (withBound assignment 1 value) (.term 0)) :=
  substitution_preserves_factors (boolean_law twoBoundContext) erasing_substitutes erasing_side
    assignment

/-! ## Support can name an index the denotation ignores -/

/-- `x = x` and `x = y`, coded with one equality symbol.
A bit is sort 0, the symbol is sort 1, and a symbol applied to one bit is sort 2. -/
inductive EqualityCarrier where
  | bit (value : Bool)
  | symbol
  | waiting (left : Bool)
  deriving DecidableEq

def equalityInSort : Nat → EqualityCarrier → Prop
  | 0, .bit _ => True
  | 1, .symbol => True
  | 2, .waiting _ => True
  | _, _ => False

def equalityApply : EqualityCarrier → EqualityCarrier → EqualityCarrier
  | .symbol, .bit left => .waiting left
  | .waiting left, .bit right => .bit (left == right)
  | _, _ => .bit true

def equalityInterpretation : Interpretation EqualityCarrier where
  inSort := equalityInSort
  termDenote := fun _ => .symbol
  termSort := fun _ => 1
  termInSort := fun _ => trivial
  apply := equalityApply
  regular := fun _ _ => .bit true

theorem equality_law (context : Context) : DependencyLaw context equalityInterpretation :=
  ⟨fun _index _sort _dependencies _left _right _lookup _agree => rfl⟩

theorem equalityApply_same (value : EqualityCarrier) :
    equalityApply (equalityApply .symbol value) value = .bit true := by
  cases value with
  | bit value =>
      simp only [equalityApply]
      rw [beq_self_eq_true']
  | symbol => rfl
  | waiting _ => rfl

def reflexiveContext : Context := [.bound 0]

/-- The term `x = x`, with `x` bound at index 0. -/
def reflexiveTerm : Preterm := .app (.app (.term 0) (.var 0)) (.var 0)

theorem reflexive_denotation (assignment : Nat → EqualityCarrier) (value : EqualityCarrier) :
    denote equalityInterpretation reflexiveContext (withBound assignment 0 value) reflexiveTerm =
      .bit true := by
  have lookup : reflexiveContext[0]? = some (.bound 0) := rfl
  unfold reflexiveTerm
  rw [denote_app, denote_app, denote_term,
    denote_bound equalityInterpretation reflexiveContext (withBound assignment 0 value) lookup,
    withBound_self]
  change equalityApply (equalityApply .symbol value) value = .bit true
  exact equalityApply_same value

/-- The support of `x = x` contains `x`. -/
theorem reflexive_support :
    ∃ support, Supports reflexiveContext reflexiveTerm support ∧ 0 ∈ support := by
  refine ⟨(∅ ∪ {0}) ∪ {0}, ?_, ?_⟩
  · exact Supports.app
      (Supports.app (Supports.term 0) (Supports.bound rfl))
      (Supports.bound rfl)
  · exact Finset.mem_union_right _ (Finset.mem_singleton_self 0)

/-- The denotation is constantly true, so it still factors through forgetting `x`.
Syntactic support is therefore only an upper bound. An index inside the support
need not be read, and an omitted disjointness condition need not have a countermodel. -/
theorem reflexive_factors (assignment : Nat → EqualityCarrier) :
    Factors (fun _ : EqualityCarrier => ())
      (fun value =>
        denote equalityInterpretation reflexiveContext (withBound assignment 0 value)
          reflexiveTerm) :=
  ⟨fun _ => .bit true, fun value => (reflexive_denotation assignment value).symm⟩

def comparisonContext : Context := [.bound 0, .bound 0]

/-- The term `x = y`, with `x` at index 0 and `y` at index 1. -/
def comparisonTerm : Preterm := .app (.app (.term 0) (.var 0)) (.var 1)

theorem comparison_denotation (assignment : Nat → EqualityCarrier) (x y : Bool) :
    denote equalityInterpretation comparisonContext
        (withBound (withBound assignment 1 (.bit y)) 0 (.bit x)) comparisonTerm =
      .bit (x == y) := by
  have lookup0 : comparisonContext[0]? = some (.bound 0) := rfl
  have lookup1 : comparisonContext[1]? = some (.bound 0) := rfl
  have at0 :
      denote equalityInterpretation comparisonContext
          (withBound (withBound assignment 1 (.bit y)) 0 (.bit x)) (.var 0) =
        .bit x := by
    rw [denote_bound equalityInterpretation _ _ lookup0, withBound_self]
  have at1 :
      denote equalityInterpretation comparisonContext
          (withBound (withBound assignment 1 (.bit y)) 0 (.bit x)) (.var 1) =
        .bit y := by
    rw [denote_bound equalityInterpretation comparisonContext
        (withBound (withBound assignment 1 (.bit y)) 0 (.bit x)) lookup1,
      withBound_ne (withBound assignment 1 (.bit y)) 0 1 (.bit x) (Nat.succ_ne_zero 0),
      withBound_self]
  unfold comparisonTerm
  rw [denote_app, denote_app, denote_term, at0, at1]
  simp [equalityInterpretation, equalityApply]

/-- Truth of the term `x = y` has a non-trivial fibre over forgetting `x`.
This is the dependence that the freshness condition of ax-5 is there to exclude. -/
def comparison_fiber (assignment : Nat → EqualityCarrier) (y : Bool) :
    NonTrivialFiber (fun _ : Bool => ())
      (fun x : Bool =>
        denote equalityInterpretation comparisonContext
            (withBound (withBound assignment 1 (.bit y)) 0 (.bit x)) comparisonTerm =
          .bit true) :=
  NonTrivialFiber.ofProp (a := y) (b := !y) rfl
    (by rw [comparison_denotation, beq_self_eq_true'])
    (by
      rw [comparison_denotation]
      intro same
      have bits : ((!y) == y) = true := by
        injection same with bits
      cases y <;> cases bits)

/-- A regular variable may be declared to depend on index 0 and still denote a constant. -/
def declaredContext : Context := [.bound 0, .regular 0 {0}]

def declaredTerm : Preterm := .var 1

theorem declared_support : Supports declaredContext declaredTerm {0} :=
  Supports.regular rfl

theorem declared_factors (assignment : Nat → Bool) :
    Factors (fun _ : Bool => ())
      (fun value =>
        denote booleanReading declaredContext (withBound assignment 0 value) declaredTerm) :=
  ⟨fun _ => false, fun _ => rfl⟩

end Mettapedia.Languages.MM0.Upstream.Nondependence
