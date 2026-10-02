import Mettapedia.Logic.Propositions.Comparison
import Mettapedia.Logic.TheoryModel.Basic

/-!
# Scrutability

A sentence is a priori scrutable from a class of sentences when the class
settles it a priori: every scenario that verifies the class verifies the
sentence.  Chalmers's thesis is that all truths are scrutable from a compact
class of truths (*Constructing the World*, 2012, ch. 1–2), and he states it for
sentences because its content for propositions depends on the view of
propositions (ch. 2 §2 and the third excursus).

Scrutability is semantic consequence for the relation "the scenario verifies
the sentence", so the Galois connection between theories and model classes of
`Mettapedia.Logic.TheoryModel` applies to it as it stands.

* `Interpretation.ScrutableFrom`: a priori scrutability of a sentence from a
  class of sentences.  From the empty class it is being a priori
  (`scrutableFrom_empty_iff`); it is reflexive, monotone and transitive
  (`scrutableFrom_of_mem`, `ScrutableFrom.mono`, `ScrutableFrom.trans`).
* **Fregean view**: "a sentence S will be scrutable from a class C of
  sentences iff the proposition expressed by S is scrutable from the class of
  propositions expressed by sentences in C" (third excursus).  This is
  `scrutableFrom_iff_fregean`.
* **Proposition and guise**: "one might bring propositional scrutability theses
  into a closer alignment ... by replacing propositions in the scrutability
  thesis by proposition/guise pairs" (third excursus).  An enriched proposition
  is such a pair, and scrutability under the guise agrees with scrutability of
  the sentence (`scrutableFrom_iff_enriched`).
* **Bases**: a class of truths is a scrutability base exactly when every
  scenario that verifies it verifies the same sentences as the actual scenario
  (`scrutabilityBase_iff`).  For the truths of a class of sentences closed
  under negation, this says that scenarios agreeing with the actual one on that
  class agree with it on every sentence (`scrutabilityBase_truthsIn_iff`): the
  class discerns as much as the whole language does.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Propositions

open Mettapedia.Logic.TheoryModel

universe uS uW uD uN uP

namespace FregeanProposition

variable {S : Type uS} {D : Type uD}

/-- Scrutability of a Fregean proposition from a class of Fregean
propositions: every scenario at which the class is true makes it true. -/
def ScrutableFrom (base : Set (FregeanProposition S D)) (proposition : FregeanProposition S D) :
    Prop :=
  Entails (fun scenario candidate => TrueAt scenario candidate) base proposition

end FregeanProposition

namespace EnrichedProposition

variable {S : Type uS} {W : Type uW} {D : Type uD}

/-- Scrutability of a Russellian proposition under a guise, from a class of
such: scrutability of the guises. -/
def ScrutableFrom (base : Set (EnrichedProposition S W D))
    (proposition : EnrichedProposition S W D) : Prop :=
  FregeanProposition.ScrutableFrom (fregean '' base) proposition.fregean

end EnrichedProposition

namespace Interpretation

variable {S : Type uS} {W : Type uW} {D : Type uD} {N : Type uN} {P : Type uP}
variable (I : Interpretation S W D N P)

/-- The scenario verifies the sentence: the sentence is true if the scenario is
actual. -/
def Verifies (scenario : S) (sentence : Sentence N P) : Prop :=
  scenario ∈ I.primary sentence

/-- A priori scrutability: every scenario that verifies the class verifies the
sentence. -/
def ScrutableFrom (base : Set (Sentence N P)) (sentence : Sentence N P) : Prop :=
  Entails I.Verifies base sentence

theorem scrutableFrom_iff {base : Set (Sentence N P)} {sentence : Sentence N P} :
    I.ScrutableFrom base sentence ↔
      ∀ scenario, (∀ member ∈ base, scenario ∈ I.primary member) → scenario ∈ I.primary sentence :=
  ⟨fun scrutable _ verifies => scrutable fun _ member => verifies _ member,
    fun scrutable scenario verifies => scrutable scenario fun _ member => verifies member⟩

/-- Scrutable from nothing is a priori. -/
theorem scrutableFrom_empty_iff {sentence : Sentence N P} :
    I.ScrutableFrom ∅ sentence ↔ I.APriori sentence :=
  ⟨fun scrutable _ => scrutable fun _ member => member.elim,
    fun aPriori scenario _ => aPriori scenario⟩

theorem scrutableFrom_of_mem {base : Set (Sentence N P)} {sentence : Sentence N P}
    (member : sentence ∈ base) : I.ScrutableFrom base sentence :=
  fun _ verifies => verifies member

theorem ScrutableFrom.mono {base larger : Set (Sentence N P)} {sentence : Sentence N P}
    (scrutable : I.ScrutableFrom base sentence) (included : base ⊆ larger) :
    I.ScrutableFrom larger sentence :=
  fun _ verifies => scrutable fun _ member => verifies (included member)

theorem ScrutableFrom.trans {base middle : Set (Sentence N P)} {sentence : Sentence N P}
    (first : ∀ member ∈ middle, I.ScrutableFrom base member)
    (second : I.ScrutableFrom middle sentence) : I.ScrutableFrom base sentence :=
  fun _ verifies => second fun member inMiddle => first member inMiddle verifies

/-- An a priori sentence is scrutable from every class. -/
theorem APriori.scrutableFrom {sentence : Sentence N P} (aPriori : I.APriori sentence)
    (base : Set (Sentence N P)) : I.ScrutableFrom base sentence :=
  fun scenario _ => aPriori scenario

/-! ## Sentences and propositions -/

/-- **On the Fregean view, sentential and propositional scrutability
coincide.** -/
theorem scrutableFrom_iff_fregean {base : Set (Sentence N P)} {sentence : Sentence N P} :
    I.ScrutableFrom base sentence ↔
      FregeanProposition.ScrutableFrom (I.fregean '' base) (I.fregean sentence) := by
  have translate : ∀ scenario (candidate : Sentence N P),
      I.Verifies scenario candidate ↔ (I.fregean candidate).TrueAt (id scenario) :=
    fun scenario candidate => (I.trueAt_fregean scenario candidate).symm
  unfold ScrutableFrom FregeanProposition.ScrutableFrom Entails
  rw [models_eq_preimage id I.fregean translate base]
  exact ⟨fun scrutable scenario member => (translate scenario sentence).mp (scrutable member),
    fun scrutable scenario member => (translate scenario sentence).mpr (scrutable member)⟩

/-- **Scrutability under guises agrees with scrutability of sentences.** -/
theorem scrutableFrom_iff_enriched (actual : S) {base : Set (Sentence N P)}
    {sentence : Sentence N P} :
    I.ScrutableFrom base sentence ↔
      EnrichedProposition.ScrutableFrom (I.enriched actual '' base) (I.enriched actual sentence) := by
  unfold EnrichedProposition.ScrutableFrom
  rw [Set.image_image, I.fregean_enriched actual sentence]
  simp only [I.fregean_enriched]
  exact I.scrutableFrom_iff_fregean

/-! ## Scrutability bases -/

/-- A scrutability base at the actual scenario: a class of truths from which
every truth is scrutable. -/
def ScrutabilityBase (actual : S) (base : Set (Sentence N P)) : Prop :=
  (∀ member ∈ base, I.TrueIn actual member) ∧
    ∀ sentence, I.TrueIn actual sentence → I.ScrutableFrom base sentence

/-- Two scenarios verify the same sentences. -/
def Indiscernible (first second : S) : Prop :=
  ∀ sentence : Sentence N P, first ∈ I.primary sentence ↔ second ∈ I.primary sentence

/-- **A class of truths is a scrutability base exactly when it pins the actual
scenario down** as far as sentences can tell: every scenario that verifies the
class verifies the same sentences as the actual one. -/
theorem scrutabilityBase_iff (actual : S) (base : Set (Sentence N P)) :
    I.ScrutabilityBase actual base ↔
      (∀ member ∈ base, I.TrueIn actual member) ∧
        ∀ scenario, (∀ member ∈ base, scenario ∈ I.primary member) →
          I.Indiscernible actual scenario := by
  refine and_congr_right fun _ => ⟨fun scrutable scenario verifies sentence => ?_, ?_⟩
  · refine ⟨fun trueIn => I.scrutableFrom_iff.mp (scrutable sentence trueIn) scenario verifies,
      fun holds => ?_⟩
    by_contra notTrue
    exact I.scrutableFrom_iff.mp (scrutable (.neg sentence) notTrue) scenario verifies holds
  · intro pins sentence trueIn
    exact I.scrutableFrom_iff.mpr fun scenario verifies => (pins scenario verifies sentence).mp trueIn

/-- The truths, at the actual scenario, among a class of sentences. -/
def truthsIn (actual : S) (candidates : Set (Sentence N P)) : Set (Sentence N P) :=
  {sentence | sentence ∈ candidates ∧ I.TrueIn actual sentence}

/-- **Scrutability from a class of sentences closed under negation**: its
truths form a scrutability base exactly when every scenario agreeing with the
actual one on that class agrees with it on every sentence. -/
theorem scrutabilityBase_truthsIn_iff (actual : S) {candidates : Set (Sentence N P)}
    (closed : ∀ sentence ∈ candidates, Form.neg sentence ∈ candidates) :
    I.ScrutabilityBase actual (I.truthsIn actual candidates) ↔
      ∀ scenario,
        (∀ sentence ∈ candidates, actual ∈ I.primary sentence ↔ scenario ∈ I.primary sentence) →
          I.Indiscernible actual scenario := by
  rw [I.scrutabilityBase_iff]
  constructor
  · rintro ⟨-, pins⟩ scenario agrees
    exact pins scenario fun member ⟨inCandidates, trueIn⟩ => (agrees member inCandidates).mp trueIn
  · intro pins
    refine ⟨fun _ member => member.2, fun scenario verifies => pins scenario ?_⟩
    intro sentence inCandidates
    refine ⟨fun trueIn => verifies sentence ⟨inCandidates, trueIn⟩, fun holds => ?_⟩
    by_contra notTrue
    exact verifies (.neg sentence) ⟨closed sentence inCandidates, notTrue⟩ holds

end Interpretation

end Mettapedia.Logic.Propositions
