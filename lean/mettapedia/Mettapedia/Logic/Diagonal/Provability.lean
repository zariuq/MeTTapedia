import Mettapedia.Logic.Diagonal.Lawvere

/-!
# Provability stages and the diagonal: Löb's theorem and the second incompleteness theorem

A **provability stage** has sentences, a provability predicate closed under
modus ponens, the Hilbert axioms K and S for implication, falsum, and an
internal provability operator `box` satisfying the Hilbert–Bernays–Löb
derivability conditions: necessitation, distribution over implication, and
`box a → box (box a)`.

Its codes are its sentences, and `run code argument` is the sentence obtained
by applying the formula `code` to the code of `argument`.  The stage is
**diagonalizable** when, for every sentence `c`, the predicate
`x ↦ box (run x x) → c` is represented by a code up to provable equivalence.
This is the relative point-surjectivity hypothesis of
`Mettapedia.Logic.Diagonal.Lawvere`, restricted to the predicates the argument
uses, and its diagonal step produces a sentence `L` with `L ↔ (box L → c)`.

**Theorems.**
* `loeb`: in a diagonalizable stage, if `box c → c` is provable then `c` is
  provable.
* `goedel_second`: a diagonalizable stage that proves its consistency
  statement `box ⊥ → ⊥` proves `⊥`.
* `not_proves_of_implies_consistency`: a consistent diagonalizable stage
  proves no sentence from which it proves its own consistency statement.  In
  particular it does not prove the consistency statement of any stronger
  stage whose consistency it can show implies its own.

**The stratified escape.**  `Model.consistent`: a model of a stage, given one
level up, proves that stage consistent.  The stage itself cannot prove it
when it is diagonalizable.

**Controls.**
* `truthStage`: the Boolean stage whose `box` is truth itself.  It is
  consistent and proves its own consistency statement, so it is not
  diagonalizable: with no diagonal the conclusion fails.
* `saturatedStage`: the Boolean stage whose `box` holds of every sentence.  It
  is consistent, diagonalizable, and does not prove its consistency
  statement.
* `trivialStage`: the stage proving everything.  It is diagonalizable, proves
  its consistency statement, and proves `⊥`, as the theorem requires.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Diagonal

universe u

/-- A provability stage: Hilbert implication, falsum, and an internal
provability operator with the Hilbert–Bernays–Löb derivability conditions. -/
structure ProvabilityStage (Sentence : Type u) where
  Proves : Sentence → Prop
  imp : Sentence → Sentence → Sentence
  falsum : Sentence
  box : Sentence → Sentence
  modusPonens : ∀ {a b : Sentence}, Proves (imp a b) → Proves a → Proves b
  axiomK : ∀ a b : Sentence, Proves (imp a (imp b a))
  axiomS : ∀ a b c : Sentence,
    Proves (imp (imp a (imp b c)) (imp (imp a b) (imp a c)))
  necessitation : ∀ {a : Sentence}, Proves a → Proves (box a)
  boxDistribution : ∀ a b : Sentence, Proves (imp (box (imp a b)) (imp (box a) (box b)))
  boxBox : ∀ a : Sentence, Proves (imp (box a) (box (box a)))

namespace ProvabilityStage

variable {Sentence : Type u} (stage : ProvabilityStage Sentence)

/-- Provable equivalence. -/
def Equivalent (first second : Sentence) : Prop :=
  stage.Proves (stage.imp first second) ∧ stage.Proves (stage.imp second first)

/-- The consistency statement `box ⊥ → ⊥`. -/
def consistency : Sentence := stage.imp (stage.box stage.falsum) stage.falsum

/-- The stage does not prove `⊥`. -/
def Consistent : Prop := ¬ stage.Proves stage.falsum

/-- The codes of the stage represent its predicates `x ↦ box (run x x) → c`
up to provable equivalence. -/
def Diagonalizable (run : Sentence → Sentence → Sentence) : Prop :=
  ∀ c : Sentence,
    Representable run stage.Equivalent
      (diagonalComposite run fun value => stage.imp (stage.box value) c)

variable {stage}

/-- Hypothetical syllogism from K and S. -/
theorem compose {a b c : Sentence} (first : stage.Proves (stage.imp a b))
    (second : stage.Proves (stage.imp b c)) : stage.Proves (stage.imp a c) :=
  stage.modusPonens
    (stage.modusPonens (stage.axiomS a b c)
      (stage.modusPonens (stage.axiomK (stage.imp b c) a) second))
    first

/-- Provable implication lifts through `box`. -/
theorem boxMonotone {a b : Sentence} (implication : stage.Proves (stage.imp a b)) :
    stage.Proves (stage.imp (stage.box a) (stage.box b)) :=
  stage.modusPonens (stage.boxDistribution a b) (stage.necessitation implication)

/-- **The diagonal sentence.**  A diagonalizable stage has, for every `c`, a
sentence provably equivalent to `box L → c`. -/
theorem exists_diagonal {run : Sentence → Sentence → Sentence}
    (diagonal : stage.Diagonalizable run) (c : Sentence) :
    ∃ sentence, stage.Equivalent sentence (stage.imp (stage.box sentence) c) :=
  exists_fixedPoint run stage.Equivalent _ (diagonal c)

/-- **Löb's theorem.** -/
theorem loeb {run : Sentence → Sentence → Sentence} (diagonal : stage.Diagonalizable run)
    {c : Sentence} (reflection : stage.Proves (stage.imp (stage.box c) c)) :
    stage.Proves c := by
  obtain ⟨sentence, forward, backward⟩ := exists_diagonal diagonal c
  have boxForward := boxMonotone forward
  have unfolded :
      stage.Proves (stage.imp (stage.box sentence)
        (stage.imp (stage.box (stage.box sentence)) (stage.box c))) :=
    compose boxForward (stage.boxDistribution (stage.box sentence) c)
  have toBoxC : stage.Proves (stage.imp (stage.box sentence) (stage.box c)) :=
    stage.modusPonens (stage.modusPonens (stage.axiomS _ _ _) unfolded) (stage.boxBox sentence)
  have toC : stage.Proves (stage.imp (stage.box sentence) c) := compose toBoxC reflection
  have proved : stage.Proves sentence := stage.modusPonens backward toC
  exact stage.modusPonens toC (stage.necessitation proved)

/-- **The second incompleteness theorem.**  A diagonalizable stage that
proves its consistency statement proves `⊥`. -/
theorem goedel_second {run : Sentence → Sentence → Sentence}
    (diagonal : stage.Diagonalizable run)
    (provesConsistency : stage.Proves stage.consistency) : stage.Proves stage.falsum :=
  loeb diagonal provesConsistency

/-- A consistent diagonalizable stage does not prove its consistency
statement. -/
theorem not_proves_consistency {run : Sentence → Sentence → Sentence}
    (diagonal : stage.Diagonalizable run) (consistent : stage.Consistent) :
    ¬ stage.Proves stage.consistency :=
  fun provesConsistency => consistent (goedel_second diagonal provesConsistency)

/-- **The relative form.**  A consistent diagonalizable stage proves no
sentence from which it proves its own consistency statement: for instance
the consistency statement of any theory that the stage shows would
certify its own consistency. -/
theorem not_proves_of_implies_consistency {run : Sentence → Sentence → Sentence}
    (diagonal : stage.Diagonalizable run) (consistent : stage.Consistent)
    {statement : Sentence} (implies : stage.Proves (stage.imp statement stage.consistency)) :
    ¬ stage.Proves statement :=
  fun proved => not_proves_consistency diagonal consistent (stage.modusPonens implies proved)

/-! ## The stratified escape -/

/-- A model of a stage, given one level up: an interpretation in which every
provable sentence holds and `⊥` fails. -/
structure Model (stage : ProvabilityStage Sentence) where
  Holds : Sentence → Prop
  sound : ∀ {sentence : Sentence}, stage.Proves sentence → Holds sentence
  falsum_fails : ¬ Holds stage.falsum

/-- A model one level up proves the stage consistent. -/
theorem Model.consistent (model : Model stage) : stage.Consistent :=
  fun proved => model.falsum_fails (model.sound proved)

/-- **Stratification.**  A diagonalizable stage with a model is consistent,
and its consistency statement is not provable inside it: the consistency
lives one level up. -/
theorem stratified {run : Sentence → Sentence → Sentence}
    (diagonal : stage.Diagonalizable run) (model : Model stage) :
    stage.Consistent ∧ ¬ stage.Proves stage.consistency :=
  ⟨model.consistent, not_proves_consistency diagonal model.consistent⟩

end ProvabilityStage

/-! ## Controls -/

namespace ProvabilityStage

/-- Boolean implication. -/
def boolImp (a b : Bool) : Bool := !a || b

/-- A Boolean stage with a chosen provability operator: a sentence is provable
when it is `true`. -/
def booleanStage (box : Bool → Bool) (necessitation : ∀ {a : Bool}, a = true → box a = true)
    (distribution : ∀ a b : Bool, boolImp (box (boolImp a b)) (boolImp (box a) (box b)) = true)
    (boxBox : ∀ a : Bool, boolImp (box a) (box (box a)) = true) :
    ProvabilityStage Bool where
  Proves := fun sentence => sentence = true
  imp := boolImp
  falsum := false
  box := box
  modusPonens := by
    intro a b implication proved
    subst proved
    simpa [boolImp] using implication
  axiomK := by intro a b; cases a <;> cases b <;> rfl
  axiomS := by intro a b c; cases a <;> cases b <;> cases c <;> rfl
  necessitation := necessitation
  boxDistribution := distribution
  boxBox := boxBox

/-- `box` is truth itself. -/
def truthStage : ProvabilityStage Bool :=
  booleanStage id (fun proved => proved) (by intro a b; cases a <;> cases b <;> rfl)
    (by intro a; cases a <;> rfl)

/-- The truth stage is consistent. -/
theorem truthStage_consistent : truthStage.Consistent := Bool.false_ne_true

/-- The truth stage proves its own consistency statement. -/
theorem truthStage_proves_consistency : truthStage.Proves truthStage.consistency := rfl

/-- **Control.**  Without the diagonal the conclusion fails: the truth stage
is consistent and proves its consistency, and it is diagonalizable for no
code map, because Boolean negation has no fixed point. -/
theorem truthStage_not_diagonalizable (run : Bool → Bool → Bool) :
    ¬ truthStage.Diagonalizable run := by
  intro diagonal
  obtain ⟨sentence, forward, backward⟩ := exists_diagonal diagonal false
  cases sentence
  · exact Bool.false_ne_true backward
  · exact Bool.false_ne_true forward

/-- `box` holds of every sentence. -/
def saturatedStage : ProvabilityStage Bool :=
  booleanStage (fun _ => true) (fun _ => rfl) (by intro a b; rfl) (by intro a; rfl)

/-- The saturated stage is consistent. -/
theorem saturatedStage_consistent : saturatedStage.Consistent := Bool.false_ne_true

/-- The saturated stage is diagonalizable: codes run as constants, and every
predicate `x ↦ box x → c` is the constant `c`. -/
theorem saturatedStage_diagonalizable :
    saturatedStage.Diagonalizable (fun code _ => code) := by
  intro c
  refine ⟨c, fun _ => ?_⟩
  cases c <;> exact ⟨rfl, rfl⟩

/-- **Positive control.**  A consistent diagonalizable stage exists, and it
does not prove its consistency statement. -/
theorem saturatedStage_not_proves_consistency :
    ¬ saturatedStage.Proves saturatedStage.consistency :=
  not_proves_consistency saturatedStage_diagonalizable saturatedStage_consistent

/-- Its consistency is proved one level up, from a model. -/
def saturatedStage_model : Model saturatedStage where
  Holds := fun sentence => sentence = true
  sound := fun proved => proved
  falsum_fails := Bool.false_ne_true

/-- The stage that proves everything. -/
def trivialStage : ProvabilityStage Bool where
  Proves := fun _ => True
  imp := boolImp
  falsum := false
  box := id
  modusPonens := fun _ _ => trivial
  axiomK := fun _ _ => trivial
  axiomS := fun _ _ _ => trivial
  necessitation := fun _ => trivial
  boxDistribution := fun _ _ => trivial
  boxBox := fun _ => trivial

theorem trivialStage_diagonalizable (run : Bool → Bool → Bool) :
    trivialStage.Diagonalizable run :=
  fun _ => ⟨false, fun _ => ⟨trivial, trivial⟩⟩

/-- **Positive control.**  The trivial stage proves its consistency statement
and, as the theorem requires, proves `⊥`. -/
theorem trivialStage_proves_falsum : trivialStage.Proves trivialStage.falsum :=
  goedel_second (trivialStage_diagonalizable fun code _ => code) trivial

end ProvabilityStage

end Mettapedia.Logic.Diagonal
