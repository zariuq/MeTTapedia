import Mettapedia.Logic.Propositions.LogicalForm
import Mathlib.Data.Set.Basic

/-!
# Two-dimensional interpretations

A sentence can be evaluated in two ways.  Taking a *scenario* as actual asks
what the sentence says if things turn out that way; this is the epistemic
evaluation.  Holding the actual scenario fixed and moving to another *world*
asks what would have been the case; this is the modal evaluation.  The first
gives the primary intension and the second the secondary intension of
two-dimensional semantics (Chalmers, "The Foundations of Two-Dimensional
Semantics", 2006; *Constructing the World*, 2012, ch. 5 and the tenth
excursus).  Kaplan's character and content are the same two steps for
indexicals ("Demonstratives", 1989), and Evans's deep and superficial necessity
are the two notions of necessity that result ("Reference and Contingency",
*The Monist* 62, 1979).

* `Interpretation S W D N P` interprets names `N` and predicates `P` over
  scenarios `S`, worlds `W` and things `D`.  A name stands for a thing once a
  scenario is taken as actual, and rigidly so across worlds.  A predicate
  expresses a property once a scenario is taken as actual, and the property has
  an extension in each world.
* `Interpretation.TrueAt` is the two-dimensional truth value of a sentence: at
  a world, with a scenario taken as actual.
* `Interpretation.primary` is the diagonal (the scenario's own world), and
  `Interpretation.secondary` is the row of the actual scenario
  (`mem_primary_iff`).
* A sentence is a priori when it is true at every scenario (`APriori`) and
  necessary, relative to the actual scenario, when it is true at every world
  (`Necessary`).  Either implies truth (`APriori.trueIn`, `Necessary.trueIn`).
* Both intensions turn negation into complement and conjunction into
  intersection (`primary_neg`, `primary_conj`, `secondary_neg`,
  `secondary_conj`).
* A self-identity is a priori and necessary (`aPriori_ident_self`,
  `necessary_ident_self`).  An identity between names is necessary exactly when
  it is true (`necessary_ident_iff`): names are rigid.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Propositions

universe uS uW uD uN uP

/-- A two-dimensional interpretation of names `N` and predicates `P` over
scenarios `S`, worlds `W` and things `D`. -/
structure Interpretation (S : Type uS) (W : Type uW) (D : Type uD) (N : Type uN)
    (P : Type uP) where
  /-- The world that a scenario presents as actual. -/
  world : S → W
  /-- What a name stands for if the scenario is actual. -/
  referent : N → S → D
  /-- The property a predicate expresses if the scenario is actual, given by the
  things that have it in each world. -/
  property : P → S → W → Set D

/-- A sentence: a logical form whose leaves are the names and predicates. -/
abbrev Sentence (N : Type uN) (P : Type uP) : Type (max uN uP) := Form N P

namespace Interpretation

variable {S : Type uS} {W : Type uW} {D : Type uD} {N : Type uN} {P : Type uP}
variable (I : Interpretation S W D N P)

/-- Truth of a sentence at a world, with a scenario taken as actual. -/
def TrueAt (scenario : S) (world : W) : Sentence N P → Prop :=
  Form.Holds
    (fun predicate subject => I.referent subject scenario ∈ I.property predicate scenario world)
    (fun left right => I.referent left scenario = I.referent right scenario)

/-- The primary intension: the scenarios at which the sentence is true when the
scenario itself is taken as actual. -/
def primary (sentence : Sentence N P) : Set S :=
  {scenario | I.TrueAt scenario (I.world scenario) sentence}

/-- The secondary intension relative to an actual scenario: the worlds at which
the sentence is true. -/
def secondary (actual : S) (sentence : Sentence N P) : Set W :=
  {world | I.TrueAt actual world sentence}

/-- The primary intension is the diagonal of the two-dimensional truth value. -/
theorem mem_primary_iff (scenario : S) (sentence : Sentence N P) :
    scenario ∈ I.primary sentence ↔ I.world scenario ∈ I.secondary scenario sentence :=
  Iff.rfl

/-- True in every scenario taken as actual. -/
def APriori (sentence : Sentence N P) : Prop :=
  ∀ scenario, scenario ∈ I.primary sentence

/-- True at every world, with the actual scenario held fixed. -/
def Necessary (actual : S) (sentence : Sentence N P) : Prop :=
  ∀ world, world ∈ I.secondary actual sentence

/-- True at the actual scenario. -/
def TrueIn (actual : S) (sentence : Sentence N P) : Prop :=
  actual ∈ I.primary sentence

theorem APriori.trueIn {sentence : Sentence N P} (aPriori : I.APriori sentence) (actual : S) :
    I.TrueIn actual sentence :=
  aPriori actual

theorem Necessary.trueIn {actual : S} {sentence : Sentence N P}
    (necessary : I.Necessary actual sentence) : I.TrueIn actual sentence :=
  necessary (I.world actual)

@[simp]
theorem primary_neg (sentence : Sentence N P) :
    I.primary (.neg sentence) = (I.primary sentence)ᶜ :=
  rfl

@[simp]
theorem primary_conj (left right : Sentence N P) :
    I.primary (.conj left right) = I.primary left ∩ I.primary right :=
  rfl

@[simp]
theorem secondary_neg (actual : S) (sentence : Sentence N P) :
    I.secondary actual (.neg sentence) = (I.secondary actual sentence)ᶜ :=
  rfl

@[simp]
theorem secondary_conj (actual : S) (left right : Sentence N P) :
    I.secondary actual (.conj left right) = I.secondary actual left ∩ I.secondary actual right :=
  rfl

theorem aPriori_ident_self (name : N) : I.APriori (.ident name name) :=
  fun _ => rfl

theorem necessary_ident_self (actual : S) (name : N) : I.Necessary actual (.ident name name) :=
  fun _ => rfl

/-- **Names are rigid**: an identity between names is necessary exactly when it
is true. -/
theorem necessary_ident_iff (actual : S) (left right : N) :
    I.Necessary actual (.ident left right) ↔ I.TrueIn actual (.ident left right) :=
  ⟨fun necessary => necessary.trueIn, fun trueIn _ => trueIn⟩

end Interpretation

end Mettapedia.Logic.Propositions
