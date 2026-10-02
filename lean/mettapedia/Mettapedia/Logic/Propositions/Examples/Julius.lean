import Mettapedia.Logic.Propositions.Comparison

/-!
# Julius and the zip

Evans's example of the contingent a priori ("Reference and Contingency", *The
Monist* 62, 1979).  'Julius' is introduced as a name for whoever invented the
zip.  'Julius invented the zip' can then be known without investigation, yet
the person so named might not have invented it.  Evans calls the sentence
superficially contingent and deeply necessary; in two-dimensional terms its
secondary intension is contingent and its primary intension is necessary.

The example is the negative control for descent along the Fregean leg.

* 'Julius invented the zip' is a priori and not necessary
  (`invented_aPriori`, `invented_not_necessary`).
* 'Julius is the actual inventor of the zip' is a priori and necessary
  (`actual_aPriori`, `actual_necessary`).
* The two sentences express one Fregean proposition (`fregean_eq`) and two
  Russellian propositions (`russellian_ne`).
* So being necessary is not a feature of Fregean propositions, nor of primary
  intensions (`necessaryFiber`, `not_factors_fregean_necessary`,
  `not_factors_primary_necessary`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Propositions.Julius

open Mettapedia.GSLT.Core.NonFactorization

/-- How history might have gone: which of two people invented the zip. -/
inductive History
  | judsonDid
  | sundbackDid
  deriving DecidableEq

inductive Person
  | judson
  | sundback
  deriving DecidableEq

inductive Name
  | julius
  deriving DecidableEq

inductive Predicate
  | inventedTheZip
  | isTheActualInventor
  deriving DecidableEq

/-- The inventor of the zip in a history. -/
def inventor : History → Person
  | .judsonDid => .judson
  | .sundbackDid => .sundback

/-- 'Julius' names the inventor in the scenario taken as actual.  'Invented the
zip' is had, in each world, by that world's inventor.  'Is the actual inventor'
is had in every world by the inventor of the scenario taken as actual. -/
def interpretation : Interpretation History History Person Name Predicate where
  world := id
  referent := fun _ scenario => inventor scenario
  property
    | .inventedTheZip, _, world => {inventor world}
    | .isTheActualInventor, scenario, _ => {inventor scenario}

/-- 'Julius invented the zip'. -/
def invented : Sentence Name Predicate :=
  .pred .inventedTheZip .julius

/-- 'Julius is the actual inventor of the zip'. -/
def actualInventor : Sentence Name Predicate :=
  .pred .isTheActualInventor .julius

theorem invented_aPriori : interpretation.APriori invented :=
  fun _ => rfl

theorem invented_not_necessary : ¬ interpretation.Necessary .judsonDid invented :=
  fun necessary => Person.noConfusion (necessary .sundbackDid)

theorem actual_aPriori : interpretation.APriori actualInventor :=
  fun _ => rfl

theorem actual_necessary : interpretation.Necessary .judsonDid actualInventor :=
  fun _ => rfl

/-- **One Fregean proposition**: the two predicates have the same extension in
every scenario taken as actual. -/
theorem fregean_eq : interpretation.fregean invented = interpretation.fregean actualInventor :=
  rfl

/-- **Two Russellian propositions**: the properties differ in the world where
the other person invented the zip. -/
theorem russellian_ne :
    interpretation.russellian .judsonDid invented ≠
      interpretation.russellian .judsonDid actualInventor := by
  intro same
  have properties := (Form.pred.inj same).1
  have extensions := congrFun properties .sundbackDid
  have member : Person.judson ∈ ({Person.sundback} : Set Person) := by
    rw [show ({Person.sundback} : Set Person) = {Person.judson} from extensions]
    rfl
  exact Person.noConfusion member

/-- The witness: one Fregean proposition, expressed by a necessary sentence and
by a sentence that is not necessary. -/
def necessaryFiber :
    NonTrivialFiber interpretation.fregean (interpretation.Necessary .judsonDid) :=
  .ofProp fregean_eq.symm actual_necessary invented_not_necessary

/-- **Being necessary is not a feature of Fregean propositions.** -/
theorem not_factors_fregean_necessary :
    ¬ Factors interpretation.fregean (interpretation.Necessary .judsonDid) :=
  necessaryFiber.not_factors

/-- **Being necessary is not a feature of primary intensions**: the obstruction
passes to the coarser view. -/
theorem not_factors_primary_necessary :
    ¬ Factors interpretation.primary (interpretation.Necessary .judsonDid) :=
  not_factors_of_coarsening (fine := interpretation.fregean)
    (coarsen := FregeanProposition.scenarios)
    (fun sentence => (interpretation.scenarios_fregean sentence).symm)
    not_factors_fregean_necessary

end Mettapedia.Logic.Propositions.Julius
