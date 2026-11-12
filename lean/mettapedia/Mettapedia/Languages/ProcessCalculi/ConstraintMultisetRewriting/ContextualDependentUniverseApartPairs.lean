import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentUniverseApart

/-!
# A universe in a component of a pair

A term of a pair type whose component is declared at a universe `u` is not equal, at a pair type whose component
is a universe, to a pair that holds in that component a universe `u` does not hold: the projection of the term is a
type of `u`, and a universe that `u` does not hold is not equal to a type of `u`
(`ContextualDependentUniverseInjective.sort_not_small`).

* `pair_second_apart`: the second component.
* `pair_first_apart`: the first component.

These are the statements behind a refutation through the components of a pair. The refutation itself, which reads
the equations of a store, is not built here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentUniverseInjective

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEtaLong ContextualDependentCumulative ContextualDependentRank

variable {Head L : Type} [UniverseLevel.LevelOrder L] {S : Setting Head L}
variable (facts : FormFacts S.R S.roles) (roots : RootPreserving S.R) (heads : HeadPreserving S.R)
  (algebra : CumulativeAlgebra S.R) (rigid : ∀ name, S.roles name = .rigid)
  (complete : AlgorithmicComplete S.R S.roles)

include facts roots heads algebra rigid complete in
/-- **A universe in the second component.** A term of `Σ (_ : A). u` is not equal, at `Σ (_ : A'). w`, to a pair
whose second component is a universe that `u` does not hold. -/
theorem pair_second_apart {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {u k w x : Head}
    (hu : S.R.isUniverse u) (hw : S.R.isUniverse w) (hx : S.R.isUniverse x)
    (apart : ∀ above, S.R.headTyping k above → ¬ S.R.cumulative above u) {q a A A' : Tm Head n}
    (typedTerm : Typed S.R Γ q (.sigma A (.head u)))
    (typedSigma : Typed S.R Γ (.sigma A' (.head w)) (.head x)) (typedFirst : Typed S.R Γ a A')
    (typedSecond : Typed S.R Γ (.head k) (.head w)) :
    ¬ Equal S.R Γ q (.pair a (.head k)) (.sigma A' (.head w)) := by
  intro equal
  have second : Typed S.R Γ (.snd q) (.head u) := Derivable.sndElim typedTerm
  have seconds : Equal S.R Γ (.snd q) (.snd (.pair a (.head k))) (.head w) := Derivable.sndCong equal
  have beta : Equal S.R Γ (.snd (.pair a (.head k))) (.head k) (.head w) :=
    Derivable.betaSnd typedSigma hx typedFirst typedSecond
  exact sort_not_small facts roots heads algebra rigid complete formed hu apart second
    ⟨w, hw, .trans seconds beta⟩

include facts roots heads algebra rigid complete in
/-- **A universe in the first component.** A term of `Σ (_ : u). B` is not equal, at `Σ (_ : w). B'`, to a pair
whose first component is a universe that `u` does not hold. -/
theorem pair_first_apart {n : Nat} {Γ : Ctx Head n} (formed : CtxFormed S.R Γ) {u k w x : Head}
    (hu : S.R.isUniverse u) (hw : S.R.isUniverse w) (hx : S.R.isUniverse x)
    (apart : ∀ above, S.R.headTyping k above → ¬ S.R.cumulative above u) {q b : Tm Head n}
    {B B' : Tm Head (n + 1)}
    (typedTerm : Typed S.R Γ q (.sigma (.head u) B))
    (typedSigma : Typed S.R Γ (.sigma (.head w) B') (.head x)) (typedFirst : Typed S.R Γ (.head k) (.head w))
    (typedSecond : Typed S.R Γ b (inst0 (.head k) B')) :
    ¬ Equal S.R Γ q (.pair (.head k) b) (.sigma (.head w) B') := by
  intro equal
  have first : Typed S.R Γ (.fst q) (.head u) := Derivable.fstElim typedTerm
  have firsts : Equal S.R Γ (.fst q) (.fst (.pair (.head k) b)) (.head w) := Derivable.fstCong equal
  have beta : Equal S.R Γ (.fst (.pair (.head k) b)) (.head k) (.head w) :=
    Derivable.betaFst typedSigma hx typedFirst typedSecond
  exact sort_not_small facts roots heads algebra rigid complete formed hu apart first
    ⟨w, hw, .trans firsts beta⟩

end ContextualDependentUniverseInjective
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
