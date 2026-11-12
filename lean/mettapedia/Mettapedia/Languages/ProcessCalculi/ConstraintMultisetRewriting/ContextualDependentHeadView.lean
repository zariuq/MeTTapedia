import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNormalChecking

/-!
# A view of normal codes, and the classification of a pair of sides as a total function

**Eliminations** (`Elimination`, `eliminate`, `unwind`). A code is a head under a list of eliminations, applications
and projections in any order, innermost first. `unwind` reads the head and the list of any code, and `eliminate`
puts them back (`eliminate_unwind`, `unwind_eliminate`).

**The view** (`View`, `view?`). A view is an introduction (an abstraction, a pair, reflexivity, one of the three
type formers, a universe) or a neutral: a variable or a constant under eliminations. `view?` is total on codes; it
presents the code (`view?_code`, `view?_presents`), and it fails exactly on an introduction under an elimination
(`view?_isSome_iff`).

**Canonical forms** (`view_of_typed_normal`). Every typed normal code has a view: a normal code is not a β-redex,
and typing excludes every other introduction under an elimination, because a function type, a pair type, an
identity type and a universe are pairwise not equal types.

**The rows** (`Row`, `classify`). The classification of two sides is a function defined by pattern matching on the
two views and on the marking of the variables as unknowns or bound locals. Lean's coverage check is the proof that no
pair of shapes is missed. The only tests are the ones the meaning needs: whether a neutral's head is an unknown,
whether two heads are the same, whether two universes are the same, and whether two lists of eliminations have the
same shape.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentHeadView

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization
open ContextualDependentNormalChecking

variable {Head : Type}

/-! ## Eliminations -/

/-- **One elimination**: an application to an argument, or a projection. -/
inductive Elimination (Head : Type) (n : Nat) where
  | app (argument : Tm Head n)
  | fst
  | snd

/-- The shape of an elimination, without its argument. -/
inductive ElimShape where
  | app
  | fst
  | snd
  deriving DecidableEq, Repr

namespace Elimination

/-- One elimination of a code. -/
def apply {n : Nat} : Elimination Head n → Tm Head n → Tm Head n
  | .app argument, head => .app head argument
  | .fst, head => .fst head
  | .snd, head => .snd head

/-- The shape of an elimination. -/
def shape {n : Nat} : Elimination Head n → ElimShape
  | .app _ => .app
  | .fst => .fst
  | .snd => .snd

end Elimination

/-- **A head under eliminations**, innermost first. -/
def eliminate {n : Nat} (head : Tm Head n) : List (Elimination Head n) → Tm Head n
  | [] => head
  | elimination :: rest => eliminate (elimination.apply head) rest

theorem eliminate_append {n : Nat} (head : Tm Head n) (first second : List (Elimination Head n)) :
    eliminate head (first ++ second) = eliminate (eliminate head first) second := by
  induction first generalizing head with
  | nil => rfl
  | cons elimination rest ih => exact ih _

theorem eliminate_snoc {n : Nat} (head : Tm Head n) (eliminations : List (Elimination Head n))
    (last : Elimination Head n) :
    eliminate head (eliminations ++ [last]) = last.apply (eliminate head eliminations) := by
  rw [eliminate_append]
  rfl

/-- **The head of a code under its eliminations, and the eliminations**, innermost first. -/
def unwind {n : Nat} : Tm Head n → Tm Head n × List (Elimination Head n)
  | .app function argument => ((unwind function).1, (unwind function).2 ++ [.app argument])
  | .fst inner => ((unwind inner).1, (unwind inner).2 ++ [.fst])
  | .snd inner => ((unwind inner).1, (unwind inner).2 ++ [.snd])
  | .var index => (.var index, [])
  | .const name => (.const name, [])
  | .head head => (.head head, [])
  | .pi domain codomain => (.pi domain codomain, [])
  | .sigma first second => (.sigma first second, [])
  | .id type left right => (.id type left right, [])
  | .lam body => (.lam body, [])
  | .pair first second => (.pair first second, [])
  | .refl point => (.refl point, [])

/-- **A code is its head under its eliminations.** -/
theorem eliminate_unwind {n : Nat} : ∀ code : Tm Head n, eliminate (unwind code).1 (unwind code).2 = code
  | .app function argument => by
      rw [unwind, eliminate_snoc, eliminate_unwind function]
      rfl
  | .fst inner => by
      rw [unwind, eliminate_snoc, eliminate_unwind inner]
      rfl
  | .snd inner => by
      rw [unwind, eliminate_snoc, eliminate_unwind inner]
      rfl
  | .var _ | .const _ | .head _ | .pi _ _ | .sigma _ _ | .id _ _ _ | .lam _ | .pair _ _ | .refl _ => rfl

theorem unwind_apply {n : Nat} (elimination : Elimination Head n) (code : Tm Head n) :
    unwind (elimination.apply code) = ((unwind code).1, (unwind code).2 ++ [elimination]) := by
  cases elimination <;> rfl

/-- **The head and the eliminations of a head under eliminations.** -/
theorem unwind_eliminate {n : Nat} (head : Tm Head n) (eliminations : List (Elimination Head n)) :
    unwind (eliminate head eliminations) = ((unwind head).1, (unwind head).2 ++ eliminations) := by
  induction eliminations generalizing head with
  | nil => simp [eliminate]
  | cons elimination rest ih =>
      rw [eliminate, ih, unwind_apply]
      simp

/-! ## The view -/

/-- **The view of a normal code**: an introduction, or a neutral, a variable or a constant under eliminations. -/
inductive View (Head : Type) (n : Nat) where
  | lam (body : Tm Head (n + 1))
  | pair (first second : Tm Head n)
  | refl (point : Tm Head n)
  | pi (domain : Tm Head n) (codomain : Tm Head (n + 1))
  | sigma (first : Tm Head n) (second : Tm Head (n + 1))
  | id (type left right : Tm Head n)
  | sort (head : Head)
  | neutral (index : Fin n) (eliminations : List (Elimination Head n))
  | constant (name : DeclName) (eliminations : List (Elimination Head n))

/-- The code a view presents. -/
def View.code {n : Nat} : View Head n → Tm Head n
  | .lam body => .lam body
  | .pair first second => .pair first second
  | .refl point => .refl point
  | .pi domain codomain => .pi domain codomain
  | .sigma first second => .sigma first second
  | .id type left right => .id type left right
  | .sort head => .head head
  | .neutral index eliminations => eliminate (.var index) eliminations
  | .constant name eliminations => eliminate (.const name) eliminations

/-- An introduction: an abstraction, a pair, reflexivity, a type former or a universe. -/
def isIntroduction {n : Nat} : Tm Head n → Bool
  | .lam _ | .pair _ _ | .refl _ | .pi _ _ | .sigma _ _ | .id _ _ _ | .head _ => true
  | .var _ | .const _ | .app _ _ | .fst _ | .snd _ => false

/-- The view of a head under eliminations: an introduction under no elimination, or a variable or a constant. -/
def viewOf {n : Nat} : Tm Head n → List (Elimination Head n) → Option (View Head n)
  | .var index, eliminations => some (.neutral index eliminations)
  | .const name, eliminations => some (.constant name eliminations)
  | .lam body, [] => some (.lam body)
  | .pair first second, [] => some (.pair first second)
  | .refl point, [] => some (.refl point)
  | .pi domain codomain, [] => some (.pi domain codomain)
  | .sigma first second, [] => some (.sigma first second)
  | .id type left right, [] => some (.id type left right)
  | .head head, [] => some (.sort head)
  | .lam _, _ :: _ | .pair _ _, _ :: _ | .refl _, _ :: _ | .pi _ _, _ :: _ | .sigma _ _, _ :: _
  | .id _ _ _, _ :: _ | .head _, _ :: _ => none
  | .app _ _, _ | .fst _, _ | .snd _, _ => none

/-- **The view of a code.** -/
def view? {n : Nat} (code : Tm Head n) : Option (View Head n) :=
  viewOf (unwind code).1 (unwind code).2

theorem viewOf_code {n : Nat} {head : Tm Head n} {eliminations : List (Elimination Head n)} {view : View Head n}
    (found : viewOf head eliminations = some view) : view.code = eliminate head eliminations := by
  cases head <;> cases eliminations <;> simp only [viewOf, Option.some.injEq, reduceCtorEq] at found <;>
    subst found <;> rfl

/-- **A view presents its code.** -/
theorem view?_code {n : Nat} {code : Tm Head n} {view : View Head n} (found : view? code = some view) :
    view.code = code := by
  rw [viewOf_code found, eliminate_unwind]

/-- **Every view is the view of the code it presents.** -/
theorem view?_presents {n : Nat} (view : View Head n) : view? view.code = some view := by
  cases view with
  | neutral index eliminations =>
      unfold view? View.code
      rw [unwind_eliminate]
      simp [unwind, viewOf]
  | constant name eliminations =>
      unfold view? View.code
      rw [unwind_eliminate]
      simp [unwind, viewOf]
  | lam _ | pair _ _ | refl _ | pi _ _ | sigma _ _ | id _ _ _ | sort _ => rfl

/-- An elimination: an application or a projection. -/
def isElimination {n : Nat} : Tm Head n → Bool
  | .app _ _ | .fst _ | .snd _ => true
  | .var _ | .const _ | .head _ | .pi _ _ | .sigma _ _ | .id _ _ _ | .lam _ | .pair _ _ | .refl _ => false

/-- The head of a code under its eliminations is never an elimination. -/
theorem unwind_head {n : Nat} : ∀ code : Tm Head n, isElimination (unwind code).1 = false
  | .app function _ => unwind_head function
  | .fst inner => unwind_head inner
  | .snd inner => unwind_head inner
  | .var _ | .const _ | .head _ | .pi _ _ | .sigma _ _ | .id _ _ _ | .lam _ | .pair _ _ | .refl _ => rfl

/-- **A code has a view exactly when it is not an introduction under an elimination.** -/
theorem view?_isSome_iff {n : Nat} (code : Tm Head n) :
    (view? code).isSome ↔ (isIntroduction (unwind code).1 = true → (unwind code).2 = []) := by
  have notElimination := unwind_head code
  unfold view?
  generalize (unwind code).1 = head at notElimination ⊢
  generalize (unwind code).2 = eliminations
  cases head with
  | app _ _ | fst _ | snd _ => cases notElimination
  | var _ | const _ => simp [viewOf, isIntroduction]
  | lam _ | pair _ _ | refl _ | pi _ _ | sigma _ _ | id _ _ _ | head _ =>
      cases eliminations <;> simp [viewOf, isIntroduction]

/-! ## Canonical forms -/

section Canonical

variable {L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- The code under one elimination of a normal code is normal. -/
theorem normal_of_apply {n : Nat} {elimination : Elimination Head n} {code : Tm Head n}
    (normal : Normal (S := S) (elimination.apply code)) : Normal (S := S) code := by
  cases elimination with
  | app argument =>
      have normal : Normal (S := S) (.app code argument) := normal
      exact fun _ step => normal _ (.congAppFun step)
  | fst =>
      have normal : Normal (S := S) (.fst code) := normal
      exact fun _ step => normal _ (.congFst step)
  | snd =>
      have normal : Normal (S := S) (.snd code) := normal
      exact fun _ step => normal _ (.congSnd step)

/-- The head of a normal code under eliminations, and every code on the way, is normal. -/
theorem normal_of_eliminate {n : Nat} : ∀ (eliminations : List (Elimination Head n)) {head : Tm Head n},
    Normal (S := S) (eliminate head eliminations) → Normal (S := S) head
  | [], _, normal => normal
  | _ :: rest, _, normal => normal_of_apply (normal_of_eliminate rest normal)

/-- The code under one elimination of a typed code is typed. -/
theorem typed_of_apply {n : Nat} {Γ : Ctx Head n} {elimination : Elimination Head n} {code type : Tm Head n}
    (typed : Typed S.R Γ (elimination.apply code) type) : ∃ inner, Typed S.R Γ code inner := by
  cases elimination with
  | app argument =>
      have typed : Typed S.R Γ (.app code argument) type := typed
      obtain ⟨domain, codomain, function, _, _⟩ := typed.generation
      exact ⟨_, function⟩
  | fst =>
      have typed : Typed S.R Γ (.fst code) type := typed
      obtain ⟨first, second, value, _⟩ := typed.generation
      exact ⟨_, value⟩
  | snd =>
      have typed : Typed S.R Γ (.snd code) type := typed
      obtain ⟨first, second, value, _⟩ := typed.generation
      exact ⟨_, value⟩

/-- The head of a typed code under eliminations, and every code on the way, is typed. -/
theorem typed_of_eliminate {n : Nat} {Γ : Ctx Head n} : ∀ (eliminations : List (Elimination Head n))
    {head type : Tm Head n}, Typed S.R Γ (eliminate head eliminations) type → ∃ inner, Typed S.R Γ head inner
  | [], _, _, typed => ⟨_, typed⟩
  | _ :: rest, _, _, typed => by
      obtain ⟨_, inner⟩ := typed_of_eliminate rest typed
      exact typed_of_apply inner

variable (facts : FormFacts S.R S.roles)
include facts

/-- A type former or a universe is not typed at a function type. -/
theorem universe_not_pi {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {level : Head}
    {domain : Tm Head n} {codomain : Tm Head (n + 1)}
    (isPi : IsType S.R Γ (.pi domain codomain)) (le : TypeLe S.R Γ (.head level) (.pi domain codomain)) : False := by
  obtain ⟨_, _, same, _, _⟩ := Below.pi_inv facts (TypeLe.toBelow le isPi) formed (IsType.refl isPi)
  exact TypeEq.pi_ne_head facts formed same.symm

/-- A type former or a universe is not typed at a pair type. -/
theorem universe_not_sigma {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {level : Head}
    {first : Tm Head n} {second : Tm Head (n + 1)}
    (isSigma : IsType S.R Γ (.sigma first second)) (le : TypeLe S.R Γ (.head level) (.sigma first second)) :
    False := by
  obtain ⟨_, _, same, _, _⟩ := Below.sigma_inv facts (TypeLe.toBelow le isSigma) formed (IsType.refl isSigma)
  exact TypeEq.sigma_ne_head facts formed same.symm

/-- **No typed normal code is an elimination of an introduction.** -/
theorem not_introduction_of_apply {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ)
    {elimination : Elimination Head n} {code type : Tm Head n}
    (typed : Typed S.R Γ (elimination.apply code) type) (normal : Normal (S := S) (elimination.apply code)) :
    isIntroduction code = false := by
  cases elimination with
  | app argument =>
      have typed : Typed S.R Γ (.app code argument) type := typed
      have normal : Normal (S := S) (.app code argument) := normal
      obtain ⟨domain, codomain, function, _, _⟩ := typed.generation
      have isPi := Typed.isType function formed
      cases code with
      | var _ | const _ | app _ _ | fst _ | snd _ => rfl
      | lam body => exact (normal _ (.betaPi body argument)).elim
      | pair _ _ =>
          obtain ⟨_, _, same⟩ := pair_type facts formed function
          exact absurd same (TypeEq.pi_ne_sigma facts formed)
      | refl _ =>
          obtain ⟨_, same⟩ := refl_type facts formed function
          exact absurd same (TypeEq.pi_ne_id facts formed)
      | pi _ _ =>
          obtain ⟨_, _, _, _, _, _, _, _, le⟩ := function.generation
          exact (universe_not_pi facts formed isPi le).elim
      | sigma _ _ =>
          obtain ⟨_, _, _, _, _, _, _, _, le⟩ := function.generation
          exact (universe_not_pi facts formed isPi le).elim
      | id _ _ _ =>
          obtain ⟨_, _, _, _, _, le⟩ := function.generation
          exact (universe_not_pi facts formed isPi le).elim
      | head _ =>
          obtain ⟨_, _, le⟩ := function.generation
          exact (universe_not_pi facts formed isPi le).elim
  | fst =>
      have typed : Typed S.R Γ (.fst code) type := typed
      have normal : Normal (S := S) (.fst code) := normal
      obtain ⟨first, second, value, _⟩ := typed.generation
      have isSigma := Typed.isType value formed
      cases code with
      | var _ | const _ | app _ _ | fst _ | snd _ => rfl
      | pair left right => exact (normal _ (.betaSigmaFst left right)).elim
      | lam _ =>
          obtain ⟨_, _, same⟩ := lambda_type facts formed value
          exact absurd same.symm (TypeEq.pi_ne_sigma facts formed)
      | refl _ =>
          obtain ⟨_, same⟩ := refl_type facts formed value
          exact absurd same (TypeEq.sigma_ne_id facts formed)
      | pi _ _ =>
          obtain ⟨_, _, _, _, _, _, _, _, le⟩ := value.generation
          exact (universe_not_sigma facts formed isSigma le).elim
      | sigma _ _ =>
          obtain ⟨_, _, _, _, _, _, _, _, le⟩ := value.generation
          exact (universe_not_sigma facts formed isSigma le).elim
      | id _ _ _ =>
          obtain ⟨_, _, _, _, _, le⟩ := value.generation
          exact (universe_not_sigma facts formed isSigma le).elim
      | head _ =>
          obtain ⟨_, _, le⟩ := value.generation
          exact (universe_not_sigma facts formed isSigma le).elim
  | snd =>
      have typed : Typed S.R Γ (.snd code) type := typed
      have normal : Normal (S := S) (.snd code) := normal
      obtain ⟨first, second, value, _⟩ := typed.generation
      have isSigma := Typed.isType value formed
      cases code with
      | var _ | const _ | app _ _ | fst _ | snd _ => rfl
      | pair left right => exact (normal _ (.betaSigmaSnd left right)).elim
      | lam _ =>
          obtain ⟨_, _, same⟩ := lambda_type facts formed value
          exact absurd same.symm (TypeEq.pi_ne_sigma facts formed)
      | refl _ =>
          obtain ⟨_, same⟩ := refl_type facts formed value
          exact absurd same (TypeEq.sigma_ne_id facts formed)
      | pi _ _ =>
          obtain ⟨_, _, _, _, _, _, _, _, le⟩ := value.generation
          exact (universe_not_sigma facts formed isSigma le).elim
      | sigma _ _ =>
          obtain ⟨_, _, _, _, _, _, _, _, le⟩ := value.generation
          exact (universe_not_sigma facts formed isSigma le).elim
      | id _ _ _ =>
          obtain ⟨_, _, _, _, _, le⟩ := value.generation
          exact (universe_not_sigma facts formed isSigma le).elim
      | head _ =>
          obtain ⟨_, _, le⟩ := value.generation
          exact (universe_not_sigma facts formed isSigma le).elim

/-- **Canonical forms: every typed normal code has a view.** -/
theorem view_of_typed_normal {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {code type : Tm Head n}
    (typed : Typed S.R Γ code type) (normal : Normal (S := S) code) : ∃ view, view? code = some view := by
  refine Option.isSome_iff_exists.mp ((view?_isSome_iff code).mpr fun introduction => ?_)
  have same := eliminate_unwind code
  cases eliminations : (unwind code).2 with
  | nil => rfl
  | cons elimination rest =>
      rw [eliminations, eliminate] at same
      rw [← same] at typed normal
      obtain ⟨_, inner⟩ := typed_of_eliminate rest typed
      have blocked := not_introduction_of_apply facts formed inner (normal_of_eliminate rest normal)
      rw [introduction] at blocked
      cases blocked

end Canonical

/-! ## The rows -/

/-- **The rows of a pair of sides.** -/
inductive Row where
  /-- Two abstractions: the bodies under the binder. -/
  | abstractions
  /-- Two pairs: the components. -/
  | pairs
  /-- Two reflexivities: the points. -/
  | reflexivities
  /-- Two function types, two pair types or two identity types: the components. -/
  | formers
  /-- The same universe on both sides. -/
  | universes
  /-- Two different type formers or universes: no solution. -/
  | formerClash
  /-- Two introductions of different types (an abstraction, a pair, reflexivity, a type): not typed at one type. -/
  | illTyped
  /-- An abstraction against a neutral: η-expansion of the neutral. -/
  | etaFunction
  /-- A pair against a neutral with a rigid head: η-expansion of the neutral at its Σ type. -/
  | etaPair
  /-- Reflexivity, a type former or a universe against a neutral with a rigid head: no solution. -/
  | introductionRigid
  /-- Two neutrals with the same rigid head and eliminations of the same shape: the arguments, pairwise. -/
  | sameRigid
  /-- Two neutrals with the same rigid head and eliminations of different shapes: no solution. -/
  | shapeClash
  /-- Two neutrals with different rigid heads: no solution. -/
  | headClash
  /-- An unknown under eliminations against an introduction or a rigid neutral: the pattern rules, left. -/
  | patternLeft
  /-- An introduction or a rigid neutral against an unknown under eliminations: the pattern rules, right. -/
  | patternRight
  /-- The same unknown under eliminations on both sides: intersection. -/
  | sameUnknown
  /-- Two different unknowns under eliminations. -/
  | twoUnknowns
  deriving DecidableEq, Repr

/-- The shapes of a list of eliminations. -/
def shapes {n : Nat} (eliminations : List (Elimination Head n)) : List ElimShape :=
  eliminations.map Elimination.shape

/-- The row of two neutrals with rigid heads. -/
def rigidRow {n : Nat} (sameHead : Bool) (left right : List (Elimination Head n)) : Row :=
  if sameHead then (if shapes left = shapes right then .sameRigid else .shapeClash) else .headClash

/-- **The classification of a pair of sides**, by pattern matching on their two views and on the marking of the
variables that are unknowns. -/
def classify [DecidableEq Head] {n : Nat} (flexible : Fin n → Bool) : View Head n → View Head n → Row
  -- two neutrals
  | .neutral index left, .neutral other right =>
      if flexible index then
        (if flexible other then (if index = other then .sameUnknown else .twoUnknowns) else .patternLeft)
      else if flexible other then .patternRight
      else rigidRow (decide (index = other)) left right
  | .neutral index _, .constant _ _ => if flexible index then .patternLeft else .headClash
  | .constant _ _, .neutral other _ => if flexible other then .patternRight else .headClash
  | .neutral index _, .lam _ => if flexible index then .patternLeft else .etaFunction
  | .lam _, .neutral other _ => if flexible other then .patternRight else .etaFunction
  | .neutral index _, .pair _ _ => if flexible index then .patternLeft else .etaPair
  | .pair _ _, .neutral other _ => if flexible other then .patternRight else .etaPair
  | .neutral index _, .refl _ | .neutral index _, .pi _ _ | .neutral index _, .sigma _ _
  | .neutral index _, .id _ _ _ | .neutral index _, .sort _ =>
      if flexible index then .patternLeft else .introductionRigid
  | .refl _, .neutral other _ | .pi _ _, .neutral other _ | .sigma _ _, .neutral other _
  | .id _ _ _, .neutral other _ | .sort _, .neutral other _ =>
      if flexible other then .patternRight else .introductionRigid
  -- constants are rigid
  | .constant name left, .constant other right => rigidRow (decide (name = other)) left right
  | .constant _ _, .lam _ | .lam _, .constant _ _ => .etaFunction
  | .constant _ _, .pair _ _ | .pair _ _, .constant _ _ => .etaPair
  | .constant _ _, .refl _ | .constant _ _, .pi _ _ | .constant _ _, .sigma _ _ | .constant _ _, .id _ _ _
  | .constant _ _, .sort _ | .refl _, .constant _ _ | .pi _ _, .constant _ _ | .sigma _ _, .constant _ _
  | .id _ _ _, .constant _ _ | .sort _, .constant _ _ => .introductionRigid
  -- two introductions
  | .lam _, .lam _ => .abstractions
  | .pair _ _, .pair _ _ => .pairs
  | .refl _, .refl _ => .reflexivities
  | .pi _ _, .pi _ _ | .sigma _ _, .sigma _ _ | .id _ _ _, .id _ _ _ => .formers
  | .sort head, .sort other => if head = other then .universes else .formerClash
  | .pi _ _, .sigma _ _ | .pi _ _, .id _ _ _ | .pi _ _, .sort _ | .sigma _ _, .pi _ _ | .sigma _ _, .id _ _ _
  | .sigma _ _, .sort _ | .id _ _ _, .pi _ _ | .id _ _ _, .sigma _ _ | .id _ _ _, .sort _
  | .sort _, .pi _ _ | .sort _, .sigma _ _ | .sort _, .id _ _ _ => .formerClash
  | .lam _, .pair _ _ | .lam _, .refl _ | .lam _, .pi _ _ | .lam _, .sigma _ _ | .lam _, .id _ _ _
  | .lam _, .sort _ | .pair _ _, .lam _ | .pair _ _, .refl _ | .pair _ _, .pi _ _ | .pair _ _, .sigma _ _
  | .pair _ _, .id _ _ _ | .pair _ _, .sort _ | .refl _, .lam _ | .refl _, .pair _ _ | .refl _, .pi _ _
  | .refl _, .sigma _ _ | .refl _, .id _ _ _ | .refl _, .sort _ | .pi _ _, .lam _ | .pi _ _, .pair _ _
  | .pi _ _, .refl _ | .sigma _ _, .lam _ | .sigma _ _, .pair _ _ | .sigma _ _, .refl _ | .id _ _ _, .lam _
  | .id _ _ _, .pair _ _ | .id _ _ _, .refl _ | .sort _, .lam _ | .sort _, .pair _ _
  | .sort _, .refl _ => .illTyped

end ContextualDependentHeadView
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
