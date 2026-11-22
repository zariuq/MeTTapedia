import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentUniverseApart
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentLeastFamily

/-!
# The refutation of a type that holds a universe against a type of a universe that does not hold it

An equation one of whose sides, under the abstractions of its annotation, holds a universe `K` at a type position
under formers, and whose other side is a term of the annotation's telescope ending in a universe `U` that does not
hold `K`, has no solution (`SortClash.unsolved`): under every instantiation the other side is still a term of `U`,
the first side still holds `K`, and no type of `U` is equal to such a type
(`ContextualDependentUniverseInjective.AboveUnder.apart`). The same holds when, in place of `K`, the side holds a
variable bound by the annotation's telescope at a universe that does not lie below `U`.

* `SortClash`: the reading of an equation whose right side holds the universe;
* `above?`, `sortCode`, `clashAt`, `clashFirst`, `clashOne`, `clashStore`: the executable search. For each candidate
  universe the telescope ending in it is formed and the other side is checked against it; the universe of `K` is
  read from the package's head typing, which is unique. Both orientations are read;
* the search is eventually constant in the budget (`clashStore_const`).

**The naive version is unsound.** "The other side cannot be checked at the universe of the unknown" is not a
refutation when the other side holds an unknown of a larger universe: the store `A ≐ Π (y : Y). Y` with `A : U0`,
`Y : U1` is solvable. The rule reads the side that is checked, and asks the other side for a universe at a rigid
position, which no instantiation changes. The control is in `ContextualDependentSweepWitnessesSort`.
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

/-! ## An equation whose right side holds a universe -/

/-- **A reading of an equation whose right side, under the abstractions of the annotation, holds at a type position
under formers a universe, or a variable of the telescope bound at a universe**: a formed telescope ending in a
universe `level` that does not hold it, and the left side as a term of that telescope. -/
structure SortClash {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) where
  level : Head
  small : TypeOver Θ
  under : AboveUnder S.R level (fun _ => false) small.code equation.1.1.code equation.2.2.code
  left : Term Θ small
  leftCode : left.code = equation.1.2.code

section Semantics

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **An equation with such a reading has no solution.** -/
theorem SortClash.unsolved {Θ Δ : Context S.R} (σ : Δ ⟶ Θ) {equation : Equation (TotalTerm Θ)}
    (clash : SortClash equation) : ¬ (frames S.levels).Solves σ equation := by
  rw [solves_raw]
  rintro ⟨_, held⟩
  have typedLeft : Typed S.R Δ.raw (subst σ.substitution equation.1.2.code)
      (subst σ.substitution clash.small.code) := by
    rw [← clash.leftCode]
    exact clash.left.typed.substitute σ.typed
  exact ((clash.under.subst σ.substitution (MarkedSub.none _ _)).apart facts roots heads algebra rigid complete
    (Marked.none S.R clash.level Δ.raw)) Δ.formed typedLeft held

/-- The certificate of an equation from a reading of it or of the equation read from its right side. -/
def clashOr {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    Option (SortClash equation) × Option (SortClash (swap equation)) →
      Option (PLift (∀ {Δ : Context S.R} (σ : Δ ⟶ Θ), ¬ (frames S.levels).Solves σ equation))
  | (some clash, _) => some ⟨fun σ => clash.unsolved facts roots heads algebra rigid complete σ⟩
  | (none, some clash) => some ⟨fun σ solved =>
      clash.unsolved facts roots heads algebra rigid complete σ ((solves_swap σ equation).mpr solved)⟩
  | (none, none) => none

/-- The certificate of a store from the certificate of its first equation or of the rest. -/
def clashCons {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (rest : EquationStore (TotalTerm Θ)) :
    Option (PLift (∀ {Δ : Context S.R} (σ : Δ ⟶ Θ), ¬ (frames S.levels).Solves σ equation)) ×
        Option (PLift (¬ (frames S.levels).Solvable rest)) →
      Option (PLift (¬ (frames S.levels).Solvable (equation :: rest)))
  | (some absent, _) => some ⟨fun ⟨_, σ, solved⟩ => absent.down σ (solved equation List.mem_cons_self)⟩
  | (none, some absent) => some ⟨fun ⟨Δ, σ, solved⟩ =>
      absent.down ⟨Δ, σ, fun other member => solved other (List.mem_cons_of_mem _ member)⟩⟩
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

/-- **A certificate that a code holds, at a type position under formers, a universe that `u` does not hold or a
marked variable.** The universe of a universe is read from the head typing of the package, which is unique. The
first position found is taken: the domain or first component before the codomain or second component. -/
def above? (u : Head) : {n : Nat} → (mark : Fin n → Bool) → (t : Tm Head n) → Option (PLift (Above S.R u mark t))
  | _, _, .head k =>
      match choices.typing k with
      | some above =>
          if apart : ¬ S.R.cumulative above.1 u then
            some ⟨.sort fun _ typing c => apart (headTypingUnique typing above.2 ▸ c)⟩
          else none
      | none => none
  | _, mark, .var i => if held : mark i = true then some ⟨.var held⟩ else none
  | _, mark, .pi A B =>
      match above? u mark A with
      | some found => some ⟨.piDomain found.down⟩
      | none =>
          match above? u (liftMark mark false) B with
          | some found => some ⟨.piCodomain found.down⟩
          | none => none
  | _, mark, .sigma A B =>
      match above? u mark A with
      | some found => some ⟨.sigmaFirst found.down⟩
      | none =>
          match above? u (liftMark mark false) B with
          | some found => some ⟨.sigmaSecond found.down⟩
          | none => none
  | _, mark, .id A _ _ =>
      match above? u mark A with
      | some found => some ⟨.id found.down⟩
      | none => none
  | _, _, _ => none

/-- **The telescope ending in `u`, when the other code is, under its abstractions, a type that holds what `u` does
not hold.** A variable of the telescope bound at a universe that does not lie below `u` is marked. -/
def sortCode (u : Head) : {n : Nat} → (mark : Fin n → Bool) → (large t : Tm Head n) →
    Option {small : Tm Head n // AboveUnder S.R u mark small large t}
  | _, mark, .head v, t =>
      match above? (S := S) choices headTypingUnique u mark t with
      | some found =>
          if allowed : S.R.isUniverse u ∧ S.R.isUniverse v then
            some ⟨.head u, .base allowed.1 allowed.2 found.down⟩
          else none
      | none => none
  | _, mark, .pi (.head w) B, .lam body =>
      if allowed : S.R.isUniverse w ∧ ¬ S.R.cumulative w u then
        match sortCode u (liftMark mark true) B body with
        | some small => some ⟨.pi (.head w) small.1, .bound allowed.1 allowed.2 small.2⟩
        | none => none
      else
        match sortCode u (liftMark mark false) B body with
        | some small => some ⟨.pi (.head w) small.1, .pi small.2⟩
        | none => none
  | _, mark, .pi A B, .lam body =>
      match sortCode u (liftMark mark false) B body with
      | some small => some ⟨.pi A small.1, .pi small.2⟩
      | none => none
  | _, _, _, _ => none

/-- **An equation read with the universe `u` at the end of its annotation and its right side a universe that `u`
does not hold**, when the telescope is formed and the left side checks against it. -/
def clashAt (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (u : Head) :
    Option (SortClash equation) :=
  match sortCode (S := S) choices headTypingUnique u (fun _ => false) equation.1.1.code equation.2.2.code with
  | none => none
  | some small =>
      match ContextualDependentPruning.formType facts roots heads algebra declared choices reducer fuel Θ small.1 with
      | none => none
      | some type =>
          match checkAt facts roots heads algebra declared choices reducer fuel type.1 equation.1.2.code with
          | some left => some ⟨u, type.1, by rw [type.2]; exact small.2, left.1, left.2⟩
          | none => none

/-- The first candidate universe at which the equation has such a reading. -/
def clashFirst (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    List Head → Option (SortClash equation)
  | [] => none
  | u :: rest =>
      (clashAt facts roots heads algebra declared choices reducer headTypingUnique fuel equation u).orElse fun _ =>
        clashFirst fuel equation rest

/-- **The certificate of one equation**, read from its left side or from its right side. -/
def clashOne (candidates : List Head) (fuel : Nat) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    Option (PLift (∀ {Δ : Context S.R} (σ : Δ ⟶ Θ), ¬ (frames S.levels).Solves σ equation)) :=
  clashOr facts roots heads algebra rigid complete equation
    (clashFirst facts roots heads algebra declared choices reducer headTypingUnique fuel equation candidates,
      clashFirst facts roots heads algebra declared choices reducer headTypingUnique fuel (swap equation) candidates)

/-- **The rule**: refute the store at the first equation with such a reading. -/
def clashStore (candidates : List Head) (fuel : Nat) {Θ : Context S.R} :
    (problem : EquationStore (TotalTerm Θ)) → Option (PLift (¬ (frames S.levels).Solvable problem))
  | [] => none
  | equation :: rest =>
      clashCons equation rest
        (clashOne facts roots heads algebra rigid complete declared choices reducer headTypingUnique candidates fuel
          equation, clashStore candidates fuel rest)

/-! ## Eventual constancy -/

variable (stable : ∀ {n : Nat} (fuel : Nat) (term : Tm Head n),
  Keeps (reducer fuel term) (reducer (fuel + 1) term))

include stable in
/-- Reading at one candidate universe is eventually constant: type formation and checking keep their results. -/
theorem clashAt_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) (u : Head) :
    EventuallyConst fun fuel =>
      clashAt facts roots heads algebra declared choices reducer headTypingUnique fuel equation u := by
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
  unfold clashAt
  split <;> try exact EventuallyConst.const _
  refine EventuallyConst.of_eventually_eq _ (fun fuel enough => by rw [formSame _ _ fuel enough]) ?_
  split <;> try exact EventuallyConst.const _
  refine EventuallyConst.of_eventually_eq (checkThreshold _ _ _) (fun fuel enough => by
    rw [checkSame _ _ _ fuel enough]) ?_
  exact EventuallyConst.const _

include stable in
theorem clashFirst_const {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    ∀ candidates : List Head, EventuallyConst fun fuel =>
      clashFirst facts roots heads algebra declared choices reducer headTypingUnique fuel equation candidates
  | [] => EventuallyConst.const _
  | u :: rest =>
      EventuallyConst.of_eq (fun _ => rfl)
        (EventuallyConst.comp (fun pair : Option (SortClash equation) × Option (SortClash equation) =>
            pair.1.orElse fun _ => pair.2)
          (EventuallyConst.pair
            (clashAt_const facts roots heads algebra declared choices reducer headTypingUnique stable equation u)
            (clashFirst_const equation rest)))

include stable in
theorem clashOne_const (candidates : List Head) {Θ : Context S.R} (equation : Equation (TotalTerm Θ)) :
    EventuallyConst fun fuel =>
      clashOne facts roots heads algebra rigid complete declared choices reducer headTypingUnique candidates fuel
        equation :=
  EventuallyConst.comp (clashOr facts roots heads algebra rigid complete equation)
    (EventuallyConst.pair
      (clashFirst_const facts roots heads algebra declared choices reducer headTypingUnique stable equation
        candidates)
      (clashFirst_const facts roots heads algebra declared choices reducer headTypingUnique stable (swap equation)
        candidates))

include stable in
/-- **The rule is eventually constant** on every store. -/
theorem clashStore_const (candidates : List Head) {Θ : Context S.R} :
    ∀ problem : EquationStore (TotalTerm Θ), EventuallyConst fun fuel =>
      clashStore facts roots heads algebra rigid complete declared choices reducer headTypingUnique candidates fuel
        problem
  | [] => EventuallyConst.const _
  | equation :: rest =>
      EventuallyConst.of_eq (fun _ => rfl)
        (EventuallyConst.comp (clashCons equation rest)
          (EventuallyConst.pair
            (clashOne_const facts roots heads algebra rigid complete declared choices reducer headTypingUnique
              stable candidates equation)
            (clashStore_const candidates rest)))

end Search

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
