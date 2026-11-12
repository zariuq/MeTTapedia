import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSortClash
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentUniverseApartPairs

/-!
# The refutation of a universe in a component of a pair

An equation at a pair type whose right side is a pair that holds, in a component, a universe, and whose left side
is a term of the pair type with that component at a universe `u` that does not hold it, has no solution: the
projection of the left side is a type of `u` (`ContextualDependentUniverseInjective.pair_second_apart`,
`pair_first_apart`). The same under the abstractions of a telescope of Π types.

* `PairClash`: the relation between the lowered pair type, the annotation and the right side; it is kept by
  substitution (`PairClash.subst`) and no term of the lowered type is equal to the right side at the annotation
  (`PairClash.apart`).
* `PairSortClash`: such a reading of an equation; `PairSortClash.unsolved`.
* `pairCodes`, `pairClashAt`, `pairClashFirst`, `pairClashOne`, `pairClashStore`: the executable search, and the
  rule: refute the store at the first equation with such a reading, read from either side. Both components are
  tried at every candidate universe: the code of one component can have the reading while the left side is a term
  of the type lowered at the other only. It is eventually constant in the budget (`pairClashStore_const`).

The rule reads a pair written as a pair, with the universe written in the component. A nested pair, or a universe
under a former inside the component, is not read.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaDepth

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternSolver ContextualDependentDecisiveFragment ContextualDependentFragment
open ContextualDependentRank ContextualDependentConversionBudget ContextualDependentDynamicFragment
open ContextualDependentMillerClosure ContextualDependentOpenedNormal
open ContextualDependentAcceptance4 ContextualDependentTwinsUnder
open ContextualDependentConstantHeads ContextualDependentCumulativeClosure ContextualDependentShortClosure
open ContextualDependentIntersectionGeneral ContextualDependentCoverageReadersHalf
open ContextualDependentRigidFormers ContextualDependentClosure ContextualDependentEtaLong
open ContextualDependentUniverseInjective
open ContextualDependentCumulative (checkAt checkAt_const)
open ContextualDependentEtaExpansion (swap solves_swap)

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **A pair that holds, in a component, a universe that the lowered pair type's component does not hold**, under
the abstractions of a telescope: the lowered type, the annotation and the right side. -/
inductive PairClash (R : Rules Head) (u : Head) : {n : Nat} → Tm Head n → Tm Head n → Tm Head n → Prop where
  | second {n : Nat} {A a : Tm Head n} {w k : Head} : R.isUniverse u → R.isUniverse w →
      (∀ above, R.headTyping k above → ¬ R.cumulative above u) →
      PairClash R u (.sigma A (.head u)) (.sigma A (.head w)) (.pair a (.head k))
  | first {n : Nat} {B : Tm Head (n + 1)} {b : Tm Head n} {w k : Head} : R.isUniverse u → R.isUniverse w →
      (∀ above, R.headTyping k above → ¬ R.cumulative above u) →
      PairClash R u (.sigma (.head u) B) (.sigma (.head w) B) (.pair (.head k) b)
  | pi {n : Nat} {A : Tm Head n} {small large body : Tm Head (n + 1)} :
      PairClash R u small large body → PairClash R u (.pi A small) (.pi A large) (.lam body)

/-- The relation is kept by substitution. -/
theorem PairClash.subst {R : Rules Head} {u : Head} {n : Nat} {small large right : Tm Head n}
    (clash : PairClash R u small large right) :
    ∀ {m : Nat} (σ : Sub Head n m),
      PairClash R u (Presentation.subst σ small) (Presentation.subst σ large) (Presentation.subst σ right) := by
  induction clash with
  | second hu hw apart => intro m σ; exact .second hu hw apart
  | first hu hw apart => intro m σ; exact .first hu hw apart
  | pi _ ih => intro m σ; exact .pi (ih (liftSub σ))

/-- **A reading of an equation whose right side is, under the abstractions of the annotation, a pair that holds in
a component a universe**: a formed type that lowers that component to a universe `level` that does not hold it,
and the left side as a term of that type. -/
structure PairSortClash {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) where
  level : Head
  small : TypeOver Θ
  clash : PairClash S.R level small.code equation.1.1.code equation.2.2.code
  left : Term Θ small
  leftCode : left.code = equation.1.2.code

section Semantics

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **No term of the lowered type is equal to the right side at the annotation.** -/
theorem PairClash.apart {u : Head} {n : Nat} {small large right : Tm Head n}
    (clash : PairClash S.R u small large right) : ∀ {Γ : Ctx Head n}, Apart S.R Γ small large right := by
  induction clash with
  | second hu hw apart =>
      intro Γ formed q typedTerm equal
      obtain ⟨_, typedPair⟩ := Equal.typed equal formed
      obtain ⟨x, hx, typedSigma⟩ := Typed.isType typedPair formed
      obtain ⟨typedFirst, typedSecond⟩ := Typed.pair_inv facts typedPair formed
      exact pair_second_apart facts roots heads algebra rigid complete formed hu hw hx apart typedTerm typedSigma
        typedFirst typedSecond equal
  | first hu hw apart =>
      intro Γ formed q typedTerm equal
      obtain ⟨_, typedPair⟩ := Equal.typed equal formed
      obtain ⟨x, hx, typedSigma⟩ := Typed.isType typedPair formed
      obtain ⟨typedFirst, typedSecond⟩ := Typed.pair_inv facts typedPair formed
      exact pair_first_apart facts roots heads algebra rigid complete formed hu hw hx apart typedTerm typedSigma
        typedFirst typedSecond equal
  | pi _ ih => intro Γ; exact Apart.pi facts ih

include facts roots heads algebra rigid complete in
/-- **An equation with such a reading has no solution.** -/
theorem PairSortClash.unsolved {Θ Δ : Context S.R} (σ : Δ ⟶ Θ) {equation : Equation (TotalTerm Θ)}
    (clash : PairSortClash equation) : ¬ (frames S.levels).Solves σ equation := by
  rw [solves_raw]
  rintro ⟨_, held⟩
  have typedLeft : Typed S.R Δ.raw (subst σ.substitution equation.1.2.code)
      (subst σ.substitution clash.small.code) := by
    rw [← clash.leftCode]
    exact clash.left.typed.substitute σ.typed
  exact (clash.clash.subst σ.substitution).apart facts roots heads algebra rigid complete Δ.formed typedLeft held

/-- The certificate of an equation from a reading of it or of the equation read from its right side. -/
def pairClashOr {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    Option (PairSortClash equation) × Option (PairSortClash (swap equation)) →
      Option (PLift (∀ {Δ : Context S.R} (σ : Δ ⟶ Θ), ¬ (frames S.levels).Solves σ equation))
  | (some clash, _) => some ⟨fun σ => clash.unsolved facts roots heads algebra rigid complete σ⟩
  | (none, some clash) => some ⟨fun σ solved =>
      clash.unsolved facts roots heads algebra rigid complete σ ((solves_swap σ equation).mpr solved)⟩
  | (none, none) => none

end Semantics

/-! ## The executable search -/

section Search

variable [DecidableEq Head] [∀ head, Decidable (S.R.isUniverse head)] [DecidableRel S.R.headEq]
  [DecidableRel S.R.cumulative]
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles) (declared : DeclaredTypesFormed S.R)
  (choices : ExecutableChecking.HeadChoices S.R) (reducer : ExecutableReduction.Reducer S.R)
  (headTypingUnique : ∀ {head first second : Head},
    S.R.headTyping head first → S.R.headTyping head second → first = second)

/-- The pair type with its second component lowered to `u`, when the pair holds there a universe that `u` does not
hold. -/
def pairSecond (u : Head) {n : Nat} (A a : Tm Head n) :
    (B : Tm Head (n + 1)) → (b : Tm Head n) →
      Option {small : Tm Head n // PairClash S.R u small (.sigma A B) (.pair a b)}
  | .head w, .head k =>
      match choices.typing k with
      | some above =>
          if allowed : S.R.isUniverse u ∧ S.R.isUniverse w ∧ ¬ S.R.cumulative above.1 u then
            some ⟨.sigma A (.head u), .second allowed.1 allowed.2.1
              fun _ typing c => allowed.2.2 (headTypingUnique typing above.2 ▸ c)⟩
          else none
      | none => none
  | _, _ => none

/-- The pair type with its first component lowered to `u`, when the pair holds there a universe that `u` does not
hold. -/
def pairFirst (u : Head) {n : Nat} (B : Tm Head (n + 1)) (b : Tm Head n) :
    (A a : Tm Head n) → Option {small : Tm Head n // PairClash S.R u small (.sigma A B) (.pair a b)}
  | .head w, .head k =>
      match choices.typing k with
      | some above =>
          if allowed : S.R.isUniverse u ∧ S.R.isUniverse w ∧ ¬ S.R.cumulative above.1 u then
            some ⟨.sigma (.head u) B, .first allowed.1 allowed.2.1
              fun _ typing c => allowed.2.2 (headTypingUnique typing above.2 ▸ c)⟩
          else none
      | none => none
  | _, _ => none

/-- **The annotation with a component of its pair type lowered to `u`, in every way**, when the other code is,
under its abstractions, a pair that holds there a universe `u` does not hold: the second component, then the
first. -/
def pairCodes (u : Head) : {n : Nat} → (large right : Tm Head n) →
    List {small : Tm Head n // PairClash S.R u small large right}
  | _, .sigma A B, .pair a b =>
      (pairSecond (S := S) choices headTypingUnique u A a B b).toList ++
        (pairFirst (S := S) choices headTypingUnique u B b A a).toList
  | _, .pi A B, .lam body => (pairCodes u B body).map fun small => ⟨.pi A small.1, .pi small.2⟩
  | _, _, _ => []

/-- **An equation read at one lowered annotation**, when the lowered type is formed and the left side checks
against it. -/
def pairClashWith (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (u : Head)
    (small : {small : Tm Head Θ.arity // PairClash S.R u small equation.1.1.code equation.2.2.code}) :
    Option (PairSortClash equation) :=
  match ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Θ small.1 with
  | none => none
  | some type =>
      match checkAt facts roots heads algebra declared choices reducer fuel type.1 equation.1.2.code with
      | some left => some ⟨u, type.1, by rw [type.2]; exact small.2, left.1, left.2⟩
      | none => none

/-- The first of a list of lowered annotations at which the equation has such a reading. -/
def pairClashAmong (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (u : Head) :
    List {small : Tm Head Θ.arity // PairClash S.R u small equation.1.1.code equation.2.2.code} →
      Option (PairSortClash equation)
  | [] => none
  | small :: rest =>
      (pairClashWith facts roots heads algebra declared choices reducer fuel equation u small).orElse fun _ =>
        pairClashAmong fuel equation u rest

/-- **An equation read with a component of its annotation lowered to `u`**: the first component at which the
lowered type is formed and the left side checks against it. -/
def pairClashAt (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (u : Head) :
    Option (PairSortClash equation) :=
  pairClashAmong facts roots heads algebra declared choices reducer fuel equation u
    (pairCodes (S := S) choices headTypingUnique u equation.1.1.code equation.2.2.code)

/-- The first candidate universe at which the equation has such a reading. -/
def pairClashFirst (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    List Head → Option (PairSortClash equation)
  | [] => none
  | u :: rest =>
      (pairClashAt facts roots heads algebra declared choices reducer headTypingUnique fuel equation u).orElse
        fun _ => pairClashFirst fuel equation rest

/-- **The certificate of one equation**, read from its left side or from its right side. -/
def pairClashOne (candidates : List Head) (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    Option (PLift (∀ {Δ : Context S.R} (σ : Δ ⟶ Θ), ¬ (frames S.levels).Solves σ equation)) :=
  pairClashOr facts roots heads algebra rigid complete equation
    (pairClashFirst facts roots heads algebra declared choices reducer headTypingUnique fuel equation candidates,
      pairClashFirst facts roots heads algebra declared choices reducer headTypingUnique fuel (swap equation)
        candidates)

/-- **The rule**: refute the store at the first equation with such a reading. -/
def pairClashStore (candidates : List Head) (fuel : Nat) {Θ : Context S.R} :
    (problem : EquationStore (TotalTerm Θ)) → Option (PLift (¬ (frames S.levels).Solvable problem))
  | [] => none
  | equation :: rest =>
      clashCons equation rest
        (pairClashOne facts roots heads algebra rigid complete declared choices reducer headTypingUnique candidates
          fuel equation, pairClashStore candidates fuel rest)

/-! ## Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
/-- Reading at one lowered annotation is eventually constant: type formation and checking keep their results. -/
theorem pairClashWith_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (u : Head)
    (small : {small : Tm Head Θ.arity // PairClash S.R u small equation.1.1.code equation.2.2.code}) :
    EventuallyConst fun fuel =>
      pairClashWith facts roots heads algebra declared choices reducer fuel equation u small := by
  have forming : ∀ (Γ : Context S.R) (code : Tm Head Γ.arity), ∃ threshold, ∀ fuel, threshold ≤ fuel →
      ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Γ code =
        ContextualDependentPruning.formType facts roots heads algebra declared choices reducer threshold Γ code :=
    fun _ code => (formType_const facts roots heads algebra declared choices reducer stable code).spec
  have checking : ∀ (C : Context S.R) (type : TypeOver C) (code : Tm Head C.arity), ∃ threshold, ∀ fuel,
      threshold ≤ fuel →
        checkAt facts roots heads algebra declared choices reducer fuel type code =
          checkAt facts roots heads algebra declared choices reducer threshold type code :=
    fun _ type code => (checkAt_const facts roots heads algebra declared choices reducer stable type code).spec
  choose formAt formSame using forming
  choose checkThreshold checkSame using checking
  unfold pairClashWith
  refine EventuallyConst.of_eventually_eq _ (fun fuel enough => by rw [formSame _ _ fuel enough]) ?_
  split <;> try exact EventuallyConst.const _
  refine EventuallyConst.of_eventually_eq (checkThreshold _ _ _) (fun fuel enough => by
    rw [checkSame _ _ _ fuel enough]) ?_
  exact EventuallyConst.const _

include stable in
theorem pairClashAmong_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (u : Head) :
    ∀ smalls : List {small : Tm Head Θ.arity // PairClash S.R u small equation.1.1.code equation.2.2.code},
      EventuallyConst fun fuel =>
        pairClashAmong facts roots heads algebra declared choices reducer fuel equation u smalls
  | [] => EventuallyConst.const _
  | small :: rest =>
      EventuallyConst.of_eq (fun _ => rfl)
        (EventuallyConst.comp (fun pair : Option (PairSortClash equation) × Option (PairSortClash equation) =>
            pair.1.orElse fun _ => pair.2)
          (EventuallyConst.pair
            (pairClashWith_const facts roots heads algebra declared choices reducer stable equation u small)
            (pairClashAmong_const equation u rest)))

include stable in
/-- Reading at one candidate universe is eventually constant. -/
theorem pairClashAt_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (u : Head) :
    EventuallyConst fun fuel =>
      pairClashAt facts roots heads algebra declared choices reducer headTypingUnique fuel equation u :=
  pairClashAmong_const facts roots heads algebra declared choices reducer stable equation u
    (pairCodes (S := S) choices headTypingUnique u equation.1.1.code equation.2.2.code)

include stable in
theorem pairClashFirst_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    ∀ candidates : List Head, EventuallyConst fun fuel =>
      pairClashFirst facts roots heads algebra declared choices reducer headTypingUnique fuel equation candidates
  | [] => EventuallyConst.const _
  | u :: rest =>
      EventuallyConst.of_eq (fun _ => rfl)
        (EventuallyConst.comp (fun pair : Option (PairSortClash equation) × Option (PairSortClash equation) =>
            pair.1.orElse fun _ => pair.2)
          (EventuallyConst.pair
            (pairClashAt_const facts roots heads algebra declared choices reducer headTypingUnique stable equation
              u)
            (pairClashFirst_const equation rest)))

include stable in
theorem pairClashOne_const (candidates : List Head) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      pairClashOne facts roots heads algebra rigid complete declared choices reducer headTypingUnique candidates
        fuel equation :=
  EventuallyConst.comp (pairClashOr facts roots heads algebra rigid complete equation)
    (EventuallyConst.pair
      (pairClashFirst_const facts roots heads algebra declared choices reducer headTypingUnique stable equation
        candidates)
      (pairClashFirst_const facts roots heads algebra declared choices reducer headTypingUnique stable
        (swap equation) candidates))

include stable in
/-- **The rule is eventually constant** on every store. -/
theorem pairClashStore_const (candidates : List Head) {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ), EventuallyConst fun fuel =>
      pairClashStore facts roots heads algebra rigid complete declared choices reducer headTypingUnique candidates
        fuel problem
  | [] => EventuallyConst.const _
  | equation :: rest =>
      EventuallyConst.of_eq (fun _ => rfl)
        (EventuallyConst.comp (clashCons equation rest)
          (EventuallyConst.pair
            (pairClashOne_const facts roots heads algebra rigid complete declared choices reducer headTypingUnique
              stable candidates equation)
            (pairClashStore_const candidates rest)))

end Search

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
