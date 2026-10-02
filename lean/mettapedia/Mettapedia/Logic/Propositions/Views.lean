import Mettapedia.Logic.Propositions.TwoDimensional

/-!
# Views of what a sentence expresses

Chalmers lists four views of the proposition a sentence expresses
(*Constructing the World*, 2012, ch. 2 §2):

* on the **possible-worlds view** it is "the set of possible worlds where the
  sentence is true";
* on the **Russellian view** it is "a structure involving those objects and
  properties that are the extensions of parts of the sentence";
* on the **Fregean view** it is "a structure of senses expressed by parts of a
  sentence";
* on the **eliminative view** "there are only sentences and utterances".

His own account adds a fifth object above the Russellian and the Fregean one:
the *enriched proposition*, whose leaves pair a sense with an extension
("Propositions and Attitude Ascriptions", 2011, §2).  From it "one can
straightforwardly recover a structured primary intension and a Russellian
proposition", and from those the two unstructured intensions.

This module defines the carriers and the maps, and proves that the diagram

```
sentence ──▶ enriched ──▶ Russellian ──▶ worlds
                 │
                 ▼
              Fregean ──▶ scenarios
```

commutes.

* `FregeanProposition`, `RussellianProposition`, `EnrichedProposition`: logical
  forms with senses, with objects and properties, and with pairs of both at the
  leaves.  Senses are taken to be primary intensions, as in the cited paper.
* `Interpretation.fregean`, `Interpretation.russellian`,
  `Interpretation.enriched`: the proposition a sentence expresses on each view.
  The Russellian and the enriched proposition depend on which scenario is
  actual; the Fregean one does not.
* The enriched proposition projects to the other two (`fregean_enriched`,
  `russellian_enriched`).
* The Fregean proposition composes to the primary intension
  (`scenarios_fregean`), and the Russellian proposition evaluates to the
  secondary intension (`worlds_russellian`).
* The two legs give the same truth value at the actual scenario
  (`actual_mem_scenarios_iff`).
* The projections of an enriched proposition determine it
  (`EnrichedProposition.fregean_russellian_injective`): an enriched proposition
  is a Russellian proposition together with a guise.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Propositions

universe uS uW uD uN uP

/-- A Fregean proposition: a logical form whose leaves are senses.  The sense
of a name gives a thing in each scenario, and the sense of a predicate gives an
extension in each scenario. -/
abbrev FregeanProposition (S : Type uS) (D : Type uD) : Type (max uS uD) :=
  Form (S → D) (S → Set D)

/-- A Russellian proposition: a logical form whose leaves are things and
properties, a property being given by its extension in each world. -/
abbrev RussellianProposition (W : Type uW) (D : Type uD) : Type (max uW uD) :=
  Form D (W → Set D)

/-- An enriched proposition: a logical form whose leaves pair a sense with what
it picks out. -/
abbrev EnrichedProposition (S : Type uS) (W : Type uW) (D : Type uD) : Type (max uS uW uD) :=
  Form ((S → D) × D) ((S → Set D) × (W → Set D))

namespace FregeanProposition

variable {S : Type uS} {D : Type uD}

/-- Truth of a Fregean proposition at a scenario. -/
def TrueAt (scenario : S) : FregeanProposition S D → Prop :=
  Form.Holds (fun predicate subject => subject scenario ∈ predicate scenario)
    (fun left right => left scenario = right scenario)

/-- The scenarios at which a Fregean proposition is true. -/
def scenarios (proposition : FregeanProposition S D) : Set S :=
  {scenario | TrueAt scenario proposition}

end FregeanProposition

namespace RussellianProposition

variable {W : Type uW} {D : Type uD}

/-- Truth of a Russellian proposition at a world. -/
def TrueAt (world : W) : RussellianProposition W D → Prop :=
  Form.Holds (fun property object => object ∈ property world) (fun left right => left = right)

/-- The worlds at which a Russellian proposition is true. -/
def worlds (proposition : RussellianProposition W D) : Set W :=
  {world | TrueAt world proposition}

end RussellianProposition

namespace EnrichedProposition

variable {S : Type uS} {W : Type uW} {D : Type uD}

/-- The Fregean proposition inside an enriched proposition: keep the senses. -/
def fregean : EnrichedProposition S W D → FregeanProposition S D :=
  Form.map Prod.fst Prod.fst

/-- The Russellian proposition inside an enriched proposition: keep what the
senses pick out. -/
def russellian : EnrichedProposition S W D → RussellianProposition W D :=
  Form.map Prod.snd Prod.snd

/-- **An enriched proposition is a Russellian proposition with a guise**: its
two projections determine it. -/
theorem fregean_russellian_injective :
    Function.Injective fun proposition : EnrichedProposition S W D =>
      (proposition.fregean, proposition.russellian) :=
  Form.unzip_injective

end EnrichedProposition

namespace Interpretation

variable {S : Type uS} {W : Type uW} {D : Type uD} {N : Type uN} {P : Type uP}
variable (I : Interpretation S W D N P)

/-- The sense of a name: what it stands for in each scenario taken as actual. -/
def nameSense (name : N) : S → D :=
  I.referent name

/-- The sense of a predicate: its extension in each scenario taken as actual. -/
def predicateSense (predicate : P) : S → Set D :=
  fun scenario => I.property predicate scenario (I.world scenario)

/-- The Fregean proposition a sentence expresses. -/
def fregean : Sentence N P → FregeanProposition S D :=
  Form.map I.nameSense I.predicateSense

/-- The Russellian proposition a sentence expresses, given the actual
scenario. -/
def russellian (actual : S) : Sentence N P → RussellianProposition W D :=
  Form.map (fun name => I.referent name actual) (fun predicate => I.property predicate actual)

/-- The enriched proposition a sentence expresses, given the actual scenario. -/
def enriched (actual : S) : Sentence N P → EnrichedProposition S W D :=
  Form.map (fun name => (I.nameSense name, I.referent name actual))
    (fun predicate => (I.predicateSense predicate, I.property predicate actual))

/-- Dropping the extensions of the enriched proposition gives the Fregean
proposition. -/
theorem fregean_enriched (actual : S) (sentence : Sentence N P) :
    (I.enriched actual sentence).fregean = I.fregean sentence :=
  Form.map_map _ _ _ _ sentence

/-- Dropping the senses of the enriched proposition gives the Russellian
proposition. -/
theorem russellian_enriched (actual : S) (sentence : Sentence N P) :
    (I.enriched actual sentence).russellian = I.russellian actual sentence :=
  Form.map_map _ _ _ _ sentence

theorem trueAt_fregean (scenario : S) (sentence : Sentence N P) :
    (I.fregean sentence).TrueAt scenario ↔ I.TrueAt scenario (I.world scenario) sentence :=
  Form.holds_map _ _ _ _ sentence

theorem trueAt_russellian (actual : S) (world : W) (sentence : Sentence N P) :
    (I.russellian actual sentence).TrueAt world ↔ I.TrueAt actual world sentence :=
  Form.holds_map _ _ _ _ sentence

/-- **The Fregean proposition composes to the primary intension.** -/
theorem scenarios_fregean (sentence : Sentence N P) :
    (I.fregean sentence).scenarios = I.primary sentence :=
  Set.ext fun scenario => I.trueAt_fregean scenario sentence

/-- **The Russellian proposition evaluates to the secondary intension.** -/
theorem worlds_russellian (actual : S) (sentence : Sentence N P) :
    (I.russellian actual sentence).worlds = I.secondary actual sentence :=
  Set.ext fun world => I.trueAt_russellian actual world sentence

/-- **The two legs agree on actual truth**: the Fregean proposition is true at
the actual scenario exactly when the Russellian proposition is true at its
world. -/
theorem actual_mem_scenarios_iff (actual : S) (sentence : Sentence N P) :
    actual ∈ (I.fregean sentence).scenarios ↔
      I.world actual ∈ (I.russellian actual sentence).worlds := by
  rw [I.scenarios_fregean, I.worlds_russellian]
  exact I.mem_primary_iff actual sentence

end Interpretation

end Mettapedia.Logic.Propositions
