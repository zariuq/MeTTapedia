import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentNarrowContext

/-!
# Narrowing one universe declaration at any position, at an equation that forces it

`ContextualDependentEtaDepth.narrowingUpdate` reads a store over a narrowed context wherever every solution is
equal to a substitution into that context. Here that hypothesis is proved from the shape of one equation, for a
declaration at any position of the context.

* `LowersAt`: a narrowing that lowers one declaration, at a position, from a universe to a smaller one.
* **`LowersAt.forced`**: a solution whose value at that position is equal to a type of the smaller universe is
  equal, as a typed substitution, to a substitution into the narrowed context. The declarations after the lowered
  one may depend on it; their types at the two substitutions are equal by functionality.
* `holds_forced_at`: an equation annotated at a universe whose left side is a type of the smaller universe and
  whose right side holds the unknown at a type position gives such a value in every solution.
* **`narrowingAt`**: the update. With `narrowingUpdate_rank` and `narrowingUpdate_keeps` it is a reading of the
  store that keeps the weight rank and the permuted Miller class.
* `holds_forced_at_left`, `narrowingAtLeft`: the same with the two sides of the equation exchanged.

Not covered: an equation whose sides are abstractions (the unknown held under a binder), and the declarations of
applied unknowns, which are not universes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentEtaDepth

open CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist ContextualDependentRank
open ContextualDependentEtaLong ContextualDependentCumulative ContextualDependentUniverseInjective
open ContextualDependentMillerClosure ContextualDependentCumulativeClosure ContextualDependentShortClosure

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}

/-- **A narrowing that lowers one declaration**, at a position, from the universe `v` to the universe `u`. -/
structure LowersAt {Γ : Context S.R} (narrowing : Narrowing Γ) (position : Fin Γ.arity) (u v : Head) : Prop where
  wide : Ctx.lookup Γ.raw position = .head v
  small : Ctx.lookup narrowing.raw position = .head u
  elsewhere : ∀ index, index ≠ position → Ctx.lookup narrowing.raw index = Ctx.lookup Γ.raw index
  lower : S.R.cumulative u v
  large : S.R.isUniverse v

section Position

variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **A solution whose value at the lowered declaration is equal to a type of the smaller universe is equal to a
substitution into the narrowed context.** The declarations after the lowered one may depend on it: their types at
the two substitutions are equal, by functionality. -/
theorem LowersAt.forced {Γ : Context S.R} {narrowing : Narrowing Γ} {position : Fin Γ.arity} {u v : Head}
    (lowered : LowersAt narrowing position u v) {Δ : Context S.R} (σ : Δ ⟶ Γ) {value : Tm Head Δ.arity}
    (tValue : Typed S.R Δ.raw value (.head u))
    (eValue : TypeEq S.R Δ.raw value (σ.substitution position)) :
    ∃ τ : Δ ⟶ narrowing.context, homTypedEquality S.R σ (τ ≫ narrowing.hom) := by
  classical
  let τ : Sub Head Γ.arity Δ.arity := fun index => if index = position then value else σ.substitution index
  have here : τ position = value := if_pos rfl
  have same : SubstEq S.R Γ.raw Δ.raw σ.substitution τ := by
    refine ⟨σ.typed, fun index => ?_⟩
    by_cases at_ : index = position
    · rw [at_, here]
      have declared := σ.typed position
      rw [lowered.wide] at declared ⊢
      obtain ⟨x, hx, equal⟩ := eValue
      exact .symm (universe_injective facts roots heads algebra rigid complete Δ.formed lowered.large hx
        (Derivable.cumul tValue lowered.lower) declared equal)
    · have other : τ index = σ.substitution index := if_neg at_
      rw [other]
      exact .refl (σ.typed index)
  have typed : SubstMor S.R narrowing.raw Δ.raw τ := by
    intro index
    by_cases at_ : index = position
    · rw [at_, here, lowered.small]
      exact tValue
    · have other : τ index = σ.substitution index := if_neg at_
      rw [other, lowered.elsewhere index at_]
      obtain ⟨w, hw, tType⟩ := Γ.formed.lookup index
      exact Derivable.conv (σ.typed index) (Typed.functional tType same) hw
  exact ⟨⟨τ, typed⟩, same⟩

include facts roots heads algebra rigid complete in
/-- **Where the reading applies, at any position.** An equation of the store, annotated at a universe, whose left
side is a type of the smaller universe and whose right side holds the unknown at a type position: in every
solution the value of the unknown is equal to a type of the smaller universe. -/
theorem holds_forced_at {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)} {position : Fin Γ.arity}
    {u a : Head} (hu : S.R.isUniverse u) (ha : S.R.isUniverse a)
    {equation : Equation (TotalTerm Γ)} (member : equation ∈ problem)
    (annotated : equation.1.1.code = .head a)
    (small : Typed S.R Γ.raw equation.1.2.code (.head u))
    (holds : HoldsVar (Head := Head) position equation.2.2.code)
    (Δ : Context S.R) (σ : Δ ⟶ Γ) (solved : (frames S.levels).Models σ problem) :
    ∃ value, Typed S.R Δ.raw value (.head u) ∧ TypeEq S.R Δ.raw value (σ.substitution position) := by
  obtain ⟨_, equal⟩ :=
    (ContextualDependentRigidFormers.solves_raw (S := S) σ equation).mp (solved equation member)
  rw [annotated] at equal
  exact HoldsVar.small facts roots heads algebra rigid complete holds Δ.formed hu σ.substitution
    (small.substitute σ.typed) ⟨a, ha, equal⟩

/-- **Narrowing one declaration, at any position, at an equation that forces it**: the declaration is a universe,
a smaller universe lies below it, and an equation of the store, annotated at a universe, has a left side that is a
type of the smaller universe and a right side that holds the unknown at a type position. -/
def narrowingAt {Γ : Context S.R} (narrowing : Narrowing Γ) {position : Fin Γ.arity} {u v a : Head}
    (lowered : LowersAt narrowing position u v) (hu : S.R.isUniverse u) (ha : S.R.isUniverse a)
    (problem : EquationStore (TotalTerm Γ)) {equation : Equation (TotalTerm Γ)} (member : equation ∈ problem)
    (annotated : equation.1.1.code = .head a) (typed : Typed S.R Γ.raw equation.1.2.code (.head u))
    (holds : HoldsVar (Head := Head) position equation.2.2.code) : Update S.levels problem :=
  narrowingUpdate narrowing problem fun Δ σ solved => by
    obtain ⟨value, tValue, eValue⟩ :=
      holds_forced_at facts roots heads algebra rigid complete hu ha member annotated typed holds Δ σ solved
    exact lowered.forced facts roots heads algebra rigid complete σ tValue eValue

include facts roots heads algebra rigid complete in
/-- **The same with the sides exchanged**: the right side is a type of the smaller universe and the left side holds
the unknown at a type position. -/
theorem holds_forced_at_left {Γ : Context S.R} {problem : EquationStore (TotalTerm Γ)} {position : Fin Γ.arity}
    {u a : Head} (hu : S.R.isUniverse u) (ha : S.R.isUniverse a)
    {equation : Equation (TotalTerm Γ)} (member : equation ∈ problem)
    (annotated : equation.1.1.code = .head a)
    (small : Typed S.R Γ.raw equation.2.2.code (.head u))
    (holds : HoldsVar (Head := Head) position equation.1.2.code)
    (Δ : Context S.R) (σ : Δ ⟶ Γ) (solved : (frames S.levels).Models σ problem) :
    ∃ value, Typed S.R Δ.raw value (.head u) ∧ TypeEq S.R Δ.raw value (σ.substitution position) := by
  obtain ⟨_, equal⟩ :=
    (ContextualDependentRigidFormers.solves_raw (S := S) σ equation).mp (solved equation member)
  rw [annotated] at equal
  exact HoldsVar.small facts roots heads algebra rigid complete holds Δ.formed hu σ.substitution
    (small.substitute σ.typed) ⟨a, ha, .symm equal⟩

/-- **Narrowing one declaration, at any position, at an equation that forces it from its left side**: the right
side is a type of the smaller universe and the left side holds the unknown at a type position. -/
def narrowingAtLeft {Γ : Context S.R} (narrowing : Narrowing Γ) {position : Fin Γ.arity} {u v a : Head}
    (lowered : LowersAt narrowing position u v) (hu : S.R.isUniverse u) (ha : S.R.isUniverse a)
    (problem : EquationStore (TotalTerm Γ)) {equation : Equation (TotalTerm Γ)} (member : equation ∈ problem)
    (annotated : equation.1.1.code = .head a) (typed : Typed S.R Γ.raw equation.2.2.code (.head u))
    (holds : HoldsVar (Head := Head) position equation.1.2.code) : Update S.levels problem :=
  narrowingUpdate narrowing problem fun Δ σ solved => by
    obtain ⟨value, tValue, eValue⟩ :=
      holds_forced_at_left facts roots heads algebra rigid complete hu ha member annotated typed holds Δ σ solved
    exact lowered.forced facts roots heads algebra rigid complete σ tValue eValue

end Position

end ContextualDependentEtaDepth
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
