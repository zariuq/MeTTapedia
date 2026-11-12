import Mettapedia.Logic.Relation.ObservationTransport
import Mettapedia.Logic.Relation.NormalFormDecision

/-!
# Types that mention only values

A type may be indexed by a term. If the term is a computation still to be run, and computations
may branch or diverge, the type inherits the branching and the divergence. This module states the
discipline that prevents it, on a first-order syntax with quotation, and proves what it buys.

**Syntax** (`Term`). Symbols are of two kinds: *pure* ones (constructors, type formers and the
operations a bubble computes definitionally) and *user* operations (whose rules are arbitrary:
they may branch and need not terminate). Terms are variables, symbols, applications and
quotations. A term is **value-like** (`ValueLike`) when no user operation occurs in it outside a
quotation; a variable is value-like, because variables stand for values. Steps (`Step`) apply a
set of root rules at every position that is not inside a quotation. Instantiation (`subst`)
replaces variables, also inside quotations.

**Hypotheses.** The user's rules are rules *on computations*: no left-hand side is value-like
(`OnComputations`). The bubble's rules keep value-like terms value-like (`PreservesValues`).

**Theorems**, for a value-like term and the union of both rule sets (`both`):
* every step is a step of the bubble, to a value-like term (`step_of_valueLike`);
* its reducts are its reducts under the bubble alone (`reduces_iff`), its normal forms are the
  bubble's (`normalForm_iff`), and it is strongly normalizing exactly when it is under the bubble
  (`acc_iff`);
* if the bubble's conversion is decided by normal forms on a set of value-like terms, then
  normalizing with every rule, the user's included, decides the same conversion with the same
  normal forms (`conversion_decided_with_all_rules`);
* value-like terms embed exactly (`valueEmbedding`), so every may- and must-observation of
  `ObservationTransport` is conserved;
* instantiating the variables of a value-like type by value-like terms gives a value-like type
  (`valueLike_subst`), so every instance of a dependent type at values is protected
  (`instance_reduces_iff`).

The user's rules are arbitrary in all of this: no confluence and no termination is asked of them.

## Controls (`Controls`)

* **Two runs, two types** (`two_runs_two_types`): `Vec choose`, indexed by a branching computation,
  has the normal forms `Vec a` and `Vec b`.
* **A diverging index** (`loop_not_terminating`): `Vec loop` is not strongly normalizing.
* **Why the user's rules are in no bubble** (`conversion_not_conserved`): `Vec a` and `Vec b`
  are value-like and become convertible through `Vec choose` once the user's steps are read as
  conversions; under the bubble they are not. Reduction of value-like types is protected; the
  symmetric closure of all steps is not.
* **Quotation** (`quoted_valueLike`, `quoted_type_normal`, `quoted_choice_one_type`,
  `quote_keeps_code`, `force_runs`): `Vec (quote choose)` is value-like and normal, and it is its
  only normal form; different codes give different types; forcing the code runs it, at a
  computation position.
* **Definitional computation still happens in types** (`value_type_still_computes`):
  `Vec (a + 0)` steps to `Vec a` by the bubble's rule.
* **The decision theorem at work** (`twoTypes_decided`, `twoTypes_decided_with_all_rules`): the
  bubble decides its conversion on `Vec a` and `Vec b`, and normalizing with every rule decides
  the same.
* **Dependency.** The type `Vec x` with a variable: at a value it is normal
  (`value_instance_normal`); at the branching computation it is the type with two normal forms and
  is no longer value-like (`computation_instance_branches`); `Vec (quote x)` is value-like at every
  instance (`quoted_variable_absorbs`).
* **Both hypotheses are needed.** A user rule on a value steps a value-like type outside the
  bubble (`meddling_breaks_protection`); a bubble rule that produces a computation lets a
  value-like type reach two normal forms (`leaking_bubble_breaks_protection`).

Scope: a first-order syntax with free variables and no binders. A bubble rule that substitutes,
as β does, keeps value-like terms value-like when what it substitutes is value-like
(`valueLike_subst`); a calculus with binders has to ask that of its β rule.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ValueDependency

open _root_.Relation
open Mettapedia.Logic.Relation (IsNormal IsNormalFormOf DecidedOn)
open Mettapedia.Logic.Relation.ObservationTransport (ExactEmbedding)

/-- First-order terms over variables, pure symbols and user operations, with quotation. -/
inductive Term (Pure User : Type) : Type where
  | var : Nat → Term Pure User
  | pure : Pure → Term Pure User
  | user : User → Term Pure User
  | app : Term Pure User → Term Pure User → Term Pure User
  | quote : Term Pure User → Term Pure User
  deriving DecidableEq

variable {Pure User : Type}

/-- A term is value-like when no user operation occurs in it outside a quotation. A variable is
value-like: variables stand for values. -/
def ValueLike : Term Pure User → Prop
  | .var _ => True
  | .pure _ => True
  | .user _ => False
  | .app function argument => ValueLike function ∧ ValueLike argument
  | .quote _ => True

/-- Instantiation of the variables of a term, also inside quotations. -/
def subst (instantiation : Nat → Term Pure User) : Term Pure User → Term Pure User
  | .var name => instantiation name
  | .pure symbol => .pure symbol
  | .user operation => .user operation
  | .app function argument => .app (subst instantiation function) (subst instantiation argument)
  | .quote code => .quote (subst instantiation code)

/-- **Instantiating variables by values keeps a type value-like.** -/
theorem valueLike_subst {instantiation : Nat → Term Pure User}
    (values : ∀ name, ValueLike (instantiation name)) :
    ∀ {term : Term Pure User}, ValueLike term → ValueLike (subst instantiation term)
  | .var name, _ => values name
  | .pure _, _ => trivial
  | .user _, value => value
  | .app _ _, value =>
      ⟨valueLike_subst values (show _ ∧ _ from value).1,
        valueLike_subst values (show _ ∧ _ from value).2⟩
  | .quote _, _ => trivial

/-- One step of a set of root rules, at any position that is not inside a quotation. -/
inductive Step (rules : Term Pure User → Term Pure User → Prop) :
    Term Pure User → Term Pure User → Prop where
  | root {left right : Term Pure User} : rules left right → Step rules left right
  | appFunction {function function' argument : Term Pure User} :
      Step rules function function' → Step rules (.app function argument) (.app function' argument)
  | appArgument {function argument argument' : Term Pure User} :
      Step rules argument argument' → Step rules (.app function argument) (.app function argument')

/-- Steps of a rule set that instantiation keeps are kept by instantiation. -/
theorem Step.subst {rules : Term Pure User → Term Pure User → Prop}
    (instantiation : Nat → Term Pure User)
    (stable : ∀ left right, rules left right →
      rules (subst instantiation left) (subst instantiation right))
    {source target : Term Pure User} (step : Step rules source target) :
    Step rules (subst instantiation source) (subst instantiation target) := by
  induction step with
  | root rule => exact .root (stable _ _ rule)
  | appFunction _ ih => exact .appFunction ih
  | appArgument _ ih => exact .appArgument ih

theorem Step.mono {small large : Term Pure User → Term Pure User → Prop}
    (included : ∀ left right, small left right → large left right) {source target : Term Pure User}
    (step : Step small source target) : Step large source target := by
  induction step with
  | root rule => exact .root (included _ _ rule)
  | appFunction _ ih => exact .appFunction ih
  | appArgument _ ih => exact .appArgument ih

/-- The rules of a bubble together with the user's rules. -/
def both (bubble user : Term Pure User → Term Pure User → Prop) :
    Term Pure User → Term Pure User → Prop :=
  fun left right => bubble left right ∨ user left right

/-- The user's rules are rules on computations: no left-hand side is value-like. -/
def OnComputations (user : Term Pure User → Term Pure User → Prop) : Prop :=
  ∀ left right, user left right → ¬ ValueLike left

/-- The bubble's rules keep value-like terms value-like. -/
def PreservesValues (bubble : Term Pure User → Term Pure User → Prop) : Prop :=
  ∀ left right, bubble left right → ValueLike left → ValueLike right

section Protection

variable {bubble user : Term Pure User → Term Pure User → Prop}

/-- **From a value-like term, every step is a step of the bubble, to a value-like term.** -/
theorem step_of_valueLike (preserves : PreservesValues bubble) (onComputations : OnComputations user)
    {source target : Term Pure User} (step : Step (both bubble user) source target) :
    ValueLike source → Step bubble source target ∧ ValueLike target := by
  induction step with
  | root rule =>
      intro value
      rcases rule with definitional | computed
      · exact ⟨.root definitional, preserves _ _ definitional value⟩
      · exact absurd value (onComputations _ _ computed)
  | @appFunction function function' argument _ ih =>
      intro value
      have parts : ValueLike function ∧ ValueLike argument := value
      exact ⟨.appFunction (ih parts.1).1,
        show ValueLike function' ∧ ValueLike argument from ⟨(ih parts.1).2, parts.2⟩⟩
  | @appArgument function argument argument' _ ih =>
      intro value
      have parts : ValueLike function ∧ ValueLike argument := value
      exact ⟨.appArgument (ih parts.2).1,
        show ValueLike function ∧ ValueLike argument' from ⟨parts.1, (ih parts.2).2⟩⟩

theorem reduces_of_valueLike (preserves : PreservesValues bubble)
    (onComputations : OnComputations user) {source target : Term Pure User}
    (steps : ReflTransGen (Step (both bubble user)) source target) (value : ValueLike source) :
    ReflTransGen (Step bubble) source target ∧ ValueLike target := by
  induction steps with
  | refl => exact ⟨.refl, value⟩
  | tail _ step ih =>
      obtain ⟨bubbleStep, next⟩ := step_of_valueLike preserves onComputations step ih.2
      exact ⟨ih.1.tail bubbleStep, next⟩

/-- **The reducts of a value-like term are its reducts under the bubble alone.** -/
theorem reduces_iff (preserves : PreservesValues bubble) (onComputations : OnComputations user)
    {source target : Term Pure User} (value : ValueLike source) :
    ReflTransGen (Step (both bubble user)) source target ↔
      ReflTransGen (Step bubble) source target :=
  ⟨fun steps => (reduces_of_valueLike preserves onComputations steps value).1,
    fun steps => by
      induction steps with
      | refl => exact .refl
      | tail _ step ih => exact ih.tail (Step.mono (fun _ _ rule => Or.inl rule) step)⟩

theorem isNormal_iff (preserves : PreservesValues bubble) (onComputations : OnComputations user)
    {source : Term Pure User} (value : ValueLike source) :
    IsNormal (Step (both bubble user)) source ↔ IsNormal (Step bubble) source :=
  ⟨fun normal target step => normal target (Step.mono (fun _ _ rule => Or.inl rule) step),
    fun normal target step => normal target (step_of_valueLike preserves onComputations step value).1⟩

/-- **The normal forms of a value-like term are the bubble's.** -/
theorem normalForm_iff (preserves : PreservesValues bubble) (onComputations : OnComputations user)
    {source normal : Term Pure User} (value : ValueLike source) :
    IsNormalFormOf (Step (both bubble user)) source normal ↔
      IsNormalFormOf (Step bubble) source normal := by
  constructor
  · rintro ⟨steps, stuck⟩
    obtain ⟨bubbleSteps, normalValue⟩ := reduces_of_valueLike preserves onComputations steps value
    exact ⟨bubbleSteps, (isNormal_iff preserves onComputations normalValue).mp stuck⟩
  · rintro ⟨steps, stuck⟩
    have allSteps := (reduces_iff preserves onComputations value).mpr steps
    exact ⟨allSteps, (isNormal_iff preserves onComputations
      (reduces_of_valueLike preserves onComputations allSteps value).2).mpr stuck⟩

/-- **A value-like term is strongly normalizing with every rule exactly when it is under the
bubble.** The user's rules cannot make a value-like type diverge. -/
theorem acc_iff (preserves : PreservesValues bubble) (onComputations : OnComputations user)
    {source : Term Pure User} (value : ValueLike source) :
    Acc (fun later earlier => Step (both bubble user) earlier later) source ↔
      Acc (fun later earlier => Step bubble earlier later) source := by
  constructor
  · intro accessible
    exact Subrelation.accessible
      (fun {_ _} step => Step.mono (fun _ _ rule => Or.inl rule) step) accessible
  · intro accessible
    revert value
    induction accessible with
    | intro source _ ih =>
        intro value
        exact Acc.intro source fun next step =>
          ih next (step_of_valueLike preserves onComputations step value).1
            (step_of_valueLike preserves onComputations step value).2

/-- **Type conversion stays decided.** If the bubble's conversion is decided by normal forms on a
set of value-like terms, then normalizing with every rule, the user's included, finds a normal
form for each of them and decides the bubble's conversion by comparing those normal forms. -/
theorem conversion_decided_with_all_rules (preserves : PreservesValues bubble)
    (onComputations : OnComputations user) {S : Set (Term Pure User)}
    (values : ∀ term ∈ S, ValueLike term) (decided : DecidedOn (Step bubble) S) :
    (∀ term ∈ S, ∃ normal, IsNormalFormOf (Step (both bubble user)) term normal) ∧
      ∀ first ∈ S, ∀ second ∈ S, ∀ firstNormal secondNormal,
        IsNormalFormOf (Step (both bubble user)) first firstNormal →
        IsNormalFormOf (Step (both bubble user)) second secondNormal →
          (EqvGen (Step bubble) first second ↔ firstNormal = secondNormal) := by
  refine ⟨fun term member => ?_, fun first firstMember second secondMember _ _ firstForm secondForm => ?_⟩
  · obtain ⟨normal, form⟩ := decided.1 term member
    exact ⟨normal, (normalForm_iff preserves onComputations (values term member)).mpr form⟩
  · exact decided.2 first firstMember second secondMember _ _
      ((normalForm_iff preserves onComputations (values first firstMember)).mp firstForm)
      ((normalForm_iff preserves onComputations (values second secondMember)).mp secondForm)

/-- **A dependent type instantiated by values is protected.** For an open value-like type and an
instantiation of its variables by value-like terms, the reducts of the instance under every rule
are its reducts under the bubble alone. -/
theorem instance_reduces_iff (preserves : PreservesValues bubble)
    (onComputations : OnComputations user) {instantiation : Nat → Term Pure User}
    (values : ∀ name, ValueLike (instantiation name)) {type target : Term Pure User}
    (value : ValueLike type) :
    ReflTransGen (Step (both bubble user)) (subst instantiation type) target ↔
      ReflTransGen (Step bubble) (subst instantiation type) target :=
  reduces_iff preserves onComputations (valueLike_subst values value)

/-- The value-like terms. -/
abbrev Value (Pure User : Type) : Type := {term : Term Pure User // ValueLike term}

/-- **Value-like terms embed exactly**: the steps of a value-like term under every rule are
exactly the bubble's steps between value-like terms. -/
def valueEmbedding (preserves : PreservesValues bubble) (onComputations : OnComputations user) :
    ExactEmbedding (fun source target : Value Pure User => Step bubble source.val target.val)
      (Step (both bubble user)) where
  embed := Subtype.val
  injective := Subtype.val_injective
  exact := by
    intro term next'
    constructor
    · intro step
      obtain ⟨bubbleStep, value⟩ := step_of_valueLike preserves onComputations step term.property
      exact ⟨⟨next', value⟩, bubbleStep, rfl⟩
    · rintro ⟨next, step, rfl⟩
      exact Step.mono (fun _ _ rule => Or.inl rule) step

end Protection

/-- An element that steps to itself is not accessible. -/
theorem not_acc_of_self {α : Type} {r : α → α → Prop} {x : α} (loop : r x x) : ¬ Acc r x := by
  intro accessible
  revert loop
  induction accessible with
  | intro y _ ih => exact fun loop => ih y loop loop

/-! ## Controls -/

namespace Controls

/-- Pure symbols: a type former, two values, zero and addition. -/
inductive Sym where
  | vec | a | b | zero | add
  deriving DecidableEq

/-- User operations: a choice, a loop, and forcing a quotation. -/
inductive Op where
  | choose | loop | force
  deriving DecidableEq

abbrev T := Term Sym Op

/-- The type indexed by a term. -/
def vecOf (index : T) : T := .app (.pure .vec) index

/-- The bubble: addition of zero on the right. -/
inductive Definitional : T → T → Prop where
  | addZero (x : T) : Definitional (.app (.app (.pure .add) x) (.pure .zero)) x

/-- The user's rules: a choice with two answers, a loop, and forcing. -/
inductive Computes : T → T → Prop where
  | left : Computes (.user .choose) (.pure .a)
  | right : Computes (.user .choose) (.pure .b)
  | loop : Computes (.user .loop) (.user .loop)
  | force (code : T) : Computes (.app (.user .force) (.quote code)) code

theorem definitional_preserves : PreservesValues Definitional := by
  intro left right rule value
  cases rule
  exact (show (True ∧ ValueLike right) ∧ True from value).1.2

theorem computes_onComputations : OnComputations Computes := by
  intro left right rule value
  cases rule with
  | left => exact value
  | right => exact value
  | loop => exact value
  | force code => exact (show False ∧ True from value).1

/-- Every rule. -/
abbrev allRules : T → T → Prop := both Definitional Computes

theorem pure_normal (symbol : Sym) : IsNormal (Step Definitional) (.pure symbol : T) := by
  intro target step
  cases step with
  | root rule => cases rule

theorem vecOf_pure_normal (symbol : Sym) : IsNormal (Step allRules) (vecOf (.pure symbol)) := by
  refine (isNormal_iff definitional_preserves computes_onComputations
    (show ValueLike (vecOf (.pure symbol)) from ⟨trivial, trivial⟩)).mpr ?_
  intro target step
  cases step with
  | root rule => cases rule
  | appFunction inner => exact pure_normal _ _ inner
  | appArgument inner => exact pure_normal _ _ inner

/-- **Two runs, two types.** The type indexed by the branching computation has two normal
forms. -/
theorem two_runs_two_types :
    IsNormalFormOf (Step allRules) (vecOf (.user .choose)) (vecOf (.pure .a)) ∧
      IsNormalFormOf (Step allRules) (vecOf (.user .choose)) (vecOf (.pure .b)) ∧
      vecOf (.pure .a) ≠ vecOf (.pure .b) :=
  ⟨⟨ReflTransGen.single (.appArgument (.root (Or.inr .left))), vecOf_pure_normal .a⟩,
    ⟨ReflTransGen.single (.appArgument (.root (Or.inr .right))), vecOf_pure_normal .b⟩,
    by decide⟩

/-- **A diverging index.** The type indexed by the looping computation is not strongly
normalizing. -/
theorem loop_not_terminating :
    ¬ Acc (fun later earlier => Step allRules earlier later) (vecOf (.user .loop)) :=
  not_acc_of_self (.appArgument (.root (Or.inr .loop)))

/-- Whether the value `a` occurs. -/
def mentionsA : T → Bool
  | .var _ => false
  | .pure .a => true
  | .pure _ => false
  | .user _ => false
  | .app function argument => mentionsA function || mentionsA argument
  | .quote code => mentionsA code

theorem mentionsA_step {source target : T} (step : Step Definitional source target) :
    mentionsA source = mentionsA target := by
  induction step with
  | root rule =>
      cases rule with
      | addZero x => simp [mentionsA]
  | appFunction _ ih => simp only [mentionsA, ih]
  | appArgument _ ih => simp only [mentionsA, ih]

theorem mentionsA_conv {source target : T} (converted : EqvGen (Step Definitional) source target) :
    mentionsA source = mentionsA target := by
  induction converted with
  | rel _ _ step => exact mentionsA_step step
  | refl _ => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ihFirst ihSecond => exact ihFirst.trans ihSecond

/-- **The user's rules belong to no bubble.** Read as conversions, the user's steps identify the
two value-like types through the unevaluated one; the bubble's conversion keeps them apart. -/
theorem conversion_not_conserved :
    EqvGen (Step allRules) (vecOf (.pure .a)) (vecOf (.pure .b)) ∧
      ¬ EqvGen (Step Definitional) (vecOf (.pure .a)) (vecOf (.pure .b)) :=
  ⟨EqvGen.trans _ (vecOf (.user .choose)) _
      (EqvGen.symm _ _ (EqvGen.rel _ _ (.appArgument (.root (Or.inr .left)))))
      (EqvGen.rel _ _ (.appArgument (.root (Or.inr .right)))),
    fun converted => absurd (mentionsA_conv converted) (by decide)⟩

/-- A type indexed by a quotation is value-like, whatever is quoted. -/
theorem quoted_valueLike (code : T) : ValueLike (vecOf (.quote code)) := ⟨trivial, trivial⟩

/-- **A type indexed by a quotation is normal**: no rule, of the bubble or of the user, applies to
it. -/
theorem quoted_type_normal (code : T) : IsNormal (Step allRules) (vecOf (.quote code)) := by
  refine (isNormal_iff definitional_preserves computes_onComputations (quoted_valueLike code)).mpr ?_
  intro target step
  cases step with
  | root rule => cases rule
  | appFunction inner => exact pure_normal _ _ inner
  | appArgument inner =>
      cases inner with
      | root rule => cases rule

/-- **The type indexed by the quoted branching computation has one normal form**, itself. -/
theorem quoted_choice_one_type (normal : T)
    (form : IsNormalFormOf (Step allRules) (vecOf (.quote (.user .choose))) normal) :
    normal = vecOf (.quote (.user .choose)) :=
  (quoted_type_normal _).reflTransGen_eq form.1

/-- Different codes give different types: the quotation keeps the computation. -/
theorem quote_keeps_code : Function.Injective fun code : T => vecOf (.quote code) := by
  intro first second same
  cases same
  rfl

/-- **Forcing runs the code**, at a computation position. -/
theorem force_runs (code : T) : Step allRules (.app (.user .force) (.quote code)) code :=
  .root (Or.inr (.force code))

/-- The forced choice still has both answers. -/
theorem forced_choice_branches :
    ReflTransGen (Step allRules) (.app (.user .force) (.quote (.user .choose))) (.pure .a) ∧
      ReflTransGen (Step allRules) (.app (.user .force) (.quote (.user .choose))) (.pure .b) :=
  ⟨(ReflTransGen.single (force_runs _)).tail (.root (Or.inr .left)),
    (ReflTransGen.single (force_runs _)).tail (.root (Or.inr .right))⟩

/-- **Definitional computation still happens in types.** -/
theorem value_type_still_computes :
    Step allRules (vecOf (.app (.app (.pure .add) (.pure .a)) (.pure .zero))) (vecOf (.pure .a)) :=
  .appArgument (.root (Or.inl (.addZero _)))

/-! ### The decision theorem at work -/

/-- The two value-like types `Vec a` and `Vec b`. -/
def twoTypes : Set T := {term | term = vecOf (.pure .a) ∨ term = vecOf (.pure .b)}

theorem twoTypes_values : ∀ term ∈ twoTypes, ValueLike term := by
  rintro _ (rfl | rfl) <;> exact ⟨trivial, trivial⟩

theorem definitional_vec_normal (symbol : Sym) :
    IsNormal (Step Definitional) (vecOf (.pure symbol)) :=
  (isNormal_iff definitional_preserves computes_onComputations
    (show ValueLike (vecOf (.pure symbol)) from ⟨trivial, trivial⟩)).mp (vecOf_pure_normal symbol)

/-- The bubble decides its conversion by normal forms on the two types. -/
theorem twoTypes_decided : DecidedOn (Step Definitional) twoTypes := by
  refine ⟨?_, ?_⟩
  · rintro _ (rfl | rfl)
    · exact ⟨_, .refl, definitional_vec_normal .a⟩
    · exact ⟨_, .refl, definitional_vec_normal .b⟩
  · intro first firstMember second secondMember firstNormal secondNormal firstForm secondForm
    rcases firstMember with rfl | rfl <;> rcases secondMember with rfl | rfl
    · have atFirst := (definitional_vec_normal .a).reflTransGen_eq firstForm.1
      have atSecond := (definitional_vec_normal .a).reflTransGen_eq secondForm.1
      subst atFirst
      subst atSecond
      exact ⟨fun _ => rfl, fun _ => EqvGen.refl _⟩
    · have atFirst := (definitional_vec_normal .a).reflTransGen_eq firstForm.1
      have atSecond := (definitional_vec_normal .b).reflTransGen_eq secondForm.1
      subst atFirst
      subst atSecond
      exact ⟨fun converted => absurd (mentionsA_conv converted) (by decide),
        fun same => absurd same (by decide)⟩
    · have atFirst := (definitional_vec_normal .b).reflTransGen_eq firstForm.1
      have atSecond := (definitional_vec_normal .a).reflTransGen_eq secondForm.1
      subst atFirst
      subst atSecond
      exact ⟨fun converted => absurd (mentionsA_conv converted) (by decide),
        fun same => absurd same (by decide)⟩
    · have atFirst := (definitional_vec_normal .b).reflTransGen_eq firstForm.1
      have atSecond := (definitional_vec_normal .b).reflTransGen_eq secondForm.1
      subst atFirst
      subst atSecond
      exact ⟨fun _ => rfl, fun _ => EqvGen.refl _⟩

/-- **The decision survives the user's rules**: normalizing `Vec a` and `Vec b` with every rule,
the branching and looping ones included, decides the bubble's conversion between them. -/
theorem twoTypes_decided_with_all_rules :
    (∀ term ∈ twoTypes, ∃ normal, IsNormalFormOf (Step allRules) term normal) ∧
      ∀ first ∈ twoTypes, ∀ second ∈ twoTypes, ∀ firstNormal secondNormal,
        IsNormalFormOf (Step allRules) first firstNormal →
        IsNormalFormOf (Step allRules) second secondNormal →
          (EqvGen (Step Definitional) first second ↔ firstNormal = secondNormal) :=
  conversion_decided_with_all_rules definitional_preserves computes_onComputations twoTypes_values
    twoTypes_decided

/-! ### Dependency: a type with a variable, and what may be put for it -/

/-- The dependent type `Vec x`. -/
def vecOfVariable : T := vecOf (.var 0)

/-- **Putting a value for the variable keeps the type protected**: `Vec x` at `x := a` is normal
under every rule. -/
theorem value_instance_normal :
    IsNormal (Step allRules) (subst (fun _ => (.pure .a : T)) vecOfVariable) :=
  vecOf_pure_normal .a

/-- **Putting a computation for the variable does not**: `Vec x` at `x := choose` is the type with
two normal forms. -/
theorem computation_instance_branches :
    subst (fun _ => (.user .choose : T)) vecOfVariable = vecOf (.user .choose) ∧
      ¬ ValueLike (subst (fun _ => (.user .choose : T)) vecOfVariable) :=
  ⟨rfl, fun value => (show True ∧ False from value).2⟩

/-- **A quoted variable absorbs every instantiation**: `Vec (quote x)` is value-like at every
instance, a computation included. -/
theorem quoted_variable_absorbs (instantiation : Nat → T) :
    ValueLike (subst instantiation (vecOf (.quote (.var 0)))) :=
  ⟨trivial, trivial⟩

/-! ### Both hypotheses are needed -/

/-- A user rule that rewrites a value: not a rule on computations. -/
inductive Meddles : T → T → Prop where
  | swap : Meddles (.pure .a) (.pure .b)

theorem meddles_not_onComputations : ¬ OnComputations Meddles :=
  fun onComputations => onComputations _ _ .swap trivial

/-- **A user rule on a value breaks the protection**: the value-like type `Vec a` steps to `Vec b`
by a rule that is not the bubble's. -/
theorem meddling_breaks_protection :
    ValueLike (vecOf (.pure .a)) ∧
      Step (both Definitional Meddles) (vecOf (.pure .a)) (vecOf (.pure .b)) ∧
      ¬ Step Definitional (vecOf (.pure .a)) (vecOf (.pure .b)) :=
  ⟨⟨trivial, trivial⟩, .appArgument (.root (Or.inr .swap)),
    (isNormal_iff definitional_preserves computes_onComputations
      (show ValueLike (vecOf (.pure .a)) from ⟨trivial, trivial⟩)).mp (vecOf_pure_normal .a) _⟩

/-- A bubble rule that produces a computation. -/
inductive Leaks : T → T → Prop where
  | toChoice : Leaks (.pure .zero) (.user .choose)

theorem leaks_not_preserving : ¬ PreservesValues Leaks :=
  fun preserves => preserves _ _ .toChoice trivial

/-- **A bubble rule that produces a computation breaks the protection**: the value-like type
`Vec 0` reduces to `Vec a` and to `Vec b`. -/
theorem leaking_bubble_breaks_protection :
    ValueLike (vecOf (.pure .zero)) ∧
      ReflTransGen (Step (both Leaks Computes)) (vecOf (.pure .zero)) (vecOf (.pure .a)) ∧
      ReflTransGen (Step (both Leaks Computes)) (vecOf (.pure .zero)) (vecOf (.pure .b)) :=
  ⟨⟨trivial, trivial⟩,
    (ReflTransGen.single (.appArgument (.root (Or.inl .toChoice)))).tail
      (.appArgument (.root (Or.inr .left))),
    (ReflTransGen.single (.appArgument (.root (Or.inl .toChoice)))).tail
      (.appArgument (.root (Or.inr .right)))⟩

end Controls

/-! ## Axiom audit -/

#print axioms step_of_valueLike
#print axioms reduces_iff
#print axioms normalForm_iff
#print axioms acc_iff
#print axioms conversion_decided_with_all_rules
#print axioms valueEmbedding
#print axioms valueLike_subst
#print axioms instance_reduces_iff
#print axioms Step.subst
#print axioms Controls.twoTypes_decided_with_all_rules
#print axioms Controls.value_instance_normal
#print axioms Controls.computation_instance_branches
#print axioms Controls.quoted_variable_absorbs
#print axioms Controls.two_runs_two_types
#print axioms Controls.loop_not_terminating
#print axioms Controls.conversion_not_conserved
#print axioms Controls.quoted_type_normal
#print axioms Controls.quoted_choice_one_type
#print axioms Controls.quote_keeps_code
#print axioms Controls.force_runs
#print axioms Controls.forced_choice_branches
#print axioms Controls.value_type_still_computes
#print axioms Controls.meddling_breaks_protection
#print axioms Controls.leaking_bubble_breaks_protection

end Mettapedia.TypeTheory.ValueDependency
