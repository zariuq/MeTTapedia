import Mettapedia.Logic.Propositions.Scrutability

/-!
# Positive bases and the that's-all truth

"Bases consisting of ordinary positive truths ... do not suffice" for negative
truths such as 'There are no ghosts'; Chalmers therefore adds to his base a
totality sentence, "a 'that's-all' truth, or a 'stop clause': it says that the
world contains no more than it needs to" (*Constructing the World*, 2012, sixth
excursus).  This module separates what a positive base settles by itself from
what the that's-all truth adds.

A class of sentences is taken as the positive ones, and one scenario extends
another when it verifies every positive sentence the other verifies.  This is
the second of Chalmers's two formulations, in which "one can take the notion of
a positive sentence as basic, and define outstripping in terms of it".

* `Extends`: the extension preorder on scenarios (`Extends.refl`,
  `Extends.trans`).
* **Without the that's-all truth**: what the positive truths settle is what
  holds in every extension of the actual scenario
  (`scrutableFrom_positiveTruths_iff`).  A truth that some extension falsifies
  is not settled (`not_scrutableFrom_positiveTruths`), and a sentence preserved
  under extension is settled exactly when it is true
  (`scrutableFrom_positiveTruths_iff_trueIn`).
* **With it**: the positive truths form a scrutability base exactly when the
  actual scenario has no extension that sentences can tell from it
  (`scrutabilityBase_positiveTruths_iff`).
* **In an open space of scenarios**, where every scenario has an extension that
  some sentence tells from it, no scenario's positive truths form a
  scrutability base (`not_scrutabilityBase_of_open`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Propositions

universe uS uW uD uN uP

namespace Interpretation

variable {S : Type uS} {W : Type uW} {D : Type uD} {N : Type uN} {P : Type uP}
variable (I : Interpretation S W D N P) (positive : Set (Sentence N P))

/-- `later` extends `earlier`: it verifies every positive sentence that
`earlier` verifies. -/
def Extends (later earlier : S) : Prop :=
  ∀ sentence ∈ positive, earlier ∈ I.primary sentence → later ∈ I.primary sentence

theorem Extends.refl (scenario : S) : I.Extends positive scenario scenario :=
  fun _ _ verifies => verifies

theorem Extends.trans {first second third : S} (later : I.Extends positive third second)
    (earlier : I.Extends positive second first) : I.Extends positive third first :=
  fun sentence member verifies => later sentence member (earlier sentence member verifies)

/-- A scenario verifies the positive truths exactly when it extends the actual
scenario. -/
theorem verifies_positiveTruths_iff (actual scenario : S) :
    (∀ member ∈ I.truthsIn actual positive, scenario ∈ I.primary member) ↔
      I.Extends positive scenario actual :=
  ⟨fun verifies sentence member trueIn => verifies sentence ⟨member, trueIn⟩,
    fun extension sentence member => extension sentence member.1 member.2⟩

/-- **What the positive truths settle** is what holds in every extension of the
actual scenario. -/
theorem scrutableFrom_positiveTruths_iff (actual : S) (sentence : Sentence N P) :
    I.ScrutableFrom (I.truthsIn actual positive) sentence ↔
      ∀ scenario, I.Extends positive scenario actual → scenario ∈ I.primary sentence := by
  rw [I.scrutableFrom_iff]
  exact forall_congr' fun scenario => imp_congr_left (I.verifies_positiveTruths_iff positive actual scenario)

/-- **A truth that an extension falsifies is not settled by the positive
truths.** -/
theorem not_scrutableFrom_positiveTruths {actual scenario : S} {sentence : Sentence N P}
    (extension : I.Extends positive scenario actual) (falsified : scenario ∉ I.primary sentence) :
    ¬ I.ScrutableFrom (I.truthsIn actual positive) sentence :=
  fun scrutable =>
    falsified ((I.scrutableFrom_positiveTruths_iff positive actual sentence).mp scrutable scenario
      extension)

/-- A sentence is preserved under extension. -/
def Persistent (sentence : Sentence N P) : Prop :=
  ∀ earlier later, I.Extends positive later earlier → earlier ∈ I.primary sentence →
    later ∈ I.primary sentence

theorem persistent_of_mem {sentence : Sentence N P} (member : sentence ∈ positive) :
    I.Persistent positive sentence :=
  fun _ _ extension verifies => extension sentence member verifies

theorem Persistent.conj {left right : Sentence N P} (leftPersistent : I.Persistent positive left)
    (rightPersistent : I.Persistent positive right) : I.Persistent positive (.conj left right) :=
  fun earlier later extension verifies =>
    ⟨leftPersistent earlier later extension verifies.1,
      rightPersistent earlier later extension verifies.2⟩

/-- **A persistent sentence is settled by the positive truths exactly when it is
true.** -/
theorem scrutableFrom_positiveTruths_iff_trueIn {sentence : Sentence N P}
    (persistent : I.Persistent positive sentence) (actual : S) :
    I.ScrutableFrom (I.truthsIn actual positive) sentence ↔ I.TrueIn actual sentence := by
  rw [I.scrutableFrom_positiveTruths_iff]
  exact ⟨fun settled => settled actual (Extends.refl I positive actual),
    fun trueIn scenario extension => persistent actual scenario extension trueIn⟩

/-- That's all: no extension of the actual scenario can be told from it by a
sentence. -/
def ThatsAll (actual : S) : Prop :=
  ∀ scenario, I.Extends positive scenario actual → I.Indiscernible actual scenario

/-- **The positive truths form a scrutability base exactly when that's all.** -/
theorem scrutabilityBase_positiveTruths_iff (actual : S) :
    I.ScrutabilityBase actual (I.truthsIn actual positive) ↔ I.ThatsAll positive actual := by
  rw [I.scrutabilityBase_iff]
  constructor
  · rintro ⟨-, pins⟩ scenario extension
    exact pins scenario ((I.verifies_positiveTruths_iff positive actual scenario).mpr extension)
  · intro thatsAll
    exact ⟨fun _ member => member.2, fun scenario verifies =>
      thatsAll scenario ((I.verifies_positiveTruths_iff positive actual scenario).mp verifies)⟩

/-- An open space of scenarios: every scenario has an extension that some
sentence tells from it. -/
def OpenEnded : Prop :=
  ∀ scenario, ∃ extension, I.Extends positive extension scenario ∧ ¬ I.Indiscernible scenario extension

/-- **In an open space of scenarios no scenario's positive truths settle every
truth.** -/
theorem not_scrutabilityBase_of_open (openEnded : I.OpenEnded positive) (actual : S) :
    ¬ I.ScrutabilityBase actual (I.truthsIn actual positive) := by
  rw [I.scrutabilityBase_positiveTruths_iff]
  intro thatsAll
  obtain ⟨extension, extends_, discernible⟩ := openEnded actual
  exact discernible (thatsAll extension extends_)

end Interpretation

end Mettapedia.Logic.Propositions
