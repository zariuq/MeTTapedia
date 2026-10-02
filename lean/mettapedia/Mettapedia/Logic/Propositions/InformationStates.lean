import Mettapedia.Logic.Propositions.Scrutability
import Mettapedia.Logic.WorldModel.Basic

/-!
# Information states as a world model

A reasoner's information can be represented by the scenarios it leaves open
(Stalnaker, *Inquiry*, 1984; Veltman, "Defaults in Update Semantics", 1996).
Such states form a world model in the sense of
`Mettapedia.Logic.WorldModel`: revising by further information intersects the
open scenarios, the state with no information leaves every scenario open, and a
query returns whether the state settles a sentence.

* `Verdict`: what a state says about a sentence, as the pair of "settled true"
  and "settled false".
* `Interpretation.informationWorldModel`: the monoidal world model of
  information states.
* `Interpretation.stateOf base`: the state of a reasoner who has accepted the
  sentences of `base`.  Accepting more sentences is revision (`stateOf_union`).
* **Scrutability is a query to the world model**: the state of a base settles a
  sentence true exactly when the sentence is scrutable from the base
  (`settledTrue_stateOf_iff`), and settles it false exactly when its negation
  is (`settledFalse_stateOf_iff`).  The state with no information settles
  exactly the a priori truths (`settledTrue_empty_iff`).
* More information settles more (`settledTrue_mono`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Propositions

universe uS uW uD uN uP

/-- What an information state says about a sentence. -/
@[ext]
structure Verdict where
  /-- Every open scenario verifies the sentence. -/
  settledTrue : Prop
  /-- No open scenario verifies the sentence. -/
  settledFalse : Prop

namespace Interpretation

variable {S : Type uS} {W : Type uW} {D : Type uD} {N : Type uN} {P : Type uP}
variable (I : Interpretation S W D N P)

/-- Information states: sets of open scenarios, revised by intersection and
queried for what they settle. -/
@[instance_reducible]
def informationWorldModel : MonoidalWorldModel (Set S) (Sentence N P) Verdict where
  revise := fun first second => first ∩ second
  empty := Set.univ
  extract := fun state sentence =>
    { settledTrue := state ⊆ I.primary sentence
      settledFalse := state ⊆ (I.primary sentence)ᶜ }
  revise_assoc := Set.inter_assoc
  revise_empty_left := Set.univ_inter
  revise_empty_right := Set.inter_univ

/-- The state of a reasoner who has accepted the sentences of a base: the
scenarios that verify all of them. -/
def stateOf (base : Set (Sentence N P)) : Set S :=
  {scenario | ∀ member ∈ base, scenario ∈ I.primary member}

/-- **Accepting more sentences is revision.** -/
theorem stateOf_union (first second : Set (Sentence N P)) :
    I.stateOf (first ∪ second) = I.informationWorldModel.revise (I.stateOf first) (I.stateOf second) := by
  ext scenario
  constructor
  · intro verifies
    exact ⟨fun member inFirst => verifies member (Or.inl inFirst),
      fun member inSecond => verifies member (Or.inr inSecond)⟩
  · rintro ⟨verifiesFirst, verifiesSecond⟩ member (inFirst | inSecond)
    · exact verifiesFirst member inFirst
    · exact verifiesSecond member inSecond

theorem stateOf_empty : I.stateOf ∅ = I.informationWorldModel.empty :=
  Set.eq_univ_of_forall fun _ _ member => member.elim

/-- **Scrutability is what the state of the base settles.** -/
theorem settledTrue_stateOf_iff (base : Set (Sentence N P)) (sentence : Sentence N P) :
    (I.informationWorldModel.extract (I.stateOf base) sentence).settledTrue ↔
      I.ScrutableFrom base sentence :=
  ⟨fun settled => I.scrutableFrom_iff.mpr fun _ verifies => settled verifies,
    fun scrutable scenario verifies => I.scrutableFrom_iff.mp scrutable scenario verifies⟩

theorem settledFalse_stateOf_iff (base : Set (Sentence N P)) (sentence : Sentence N P) :
    (I.informationWorldModel.extract (I.stateOf base) sentence).settledFalse ↔
      I.ScrutableFrom base (.neg sentence) :=
  I.settledTrue_stateOf_iff base (.neg sentence)

/-- The state with no information settles exactly the a priori truths. -/
theorem settledTrue_empty_iff (sentence : Sentence N P) :
    (I.informationWorldModel.extract I.informationWorldModel.empty sentence).settledTrue ↔
      I.APriori sentence :=
  ⟨fun settled scenario => settled (Set.mem_univ scenario), fun aPriori scenario _ => aPriori scenario⟩

/-- More information settles more. -/
theorem settledTrue_mono {smaller larger : Set S} (included : smaller ⊆ larger)
    {sentence : Sentence N P}
    (settled : (I.informationWorldModel.extract larger sentence).settledTrue) :
    (I.informationWorldModel.extract smaller sentence).settledTrue :=
  fun _ member => settled (included member)

end Interpretation

end Mettapedia.Logic.Propositions
