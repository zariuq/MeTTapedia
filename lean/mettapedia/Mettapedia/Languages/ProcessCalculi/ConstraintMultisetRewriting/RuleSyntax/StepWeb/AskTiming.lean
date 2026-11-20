import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Spaces
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.StepSpan

/-!
# When a firing's guards are asked: one law for every guarded step

A step is named by five choices: its store, its commit, its guards, its rules and its knowledge. This
module varies the guards alone. Its input is any guarded step (`Interface.Step.Guarded`: a firing is
admitted when it is prepared and its guards hold at every solution of its information), with any
store, commit, rules and knowledge; the output keeps those four choices and asks the guards at another
time.

* **Guards after the firing's own tells** (the input): at every solution of the information.
* **Guards before them** (`beforeTells`): at every solution of an **ask part** of the information.

The ask part is data. An `AskSplit` of a step gives, for each firing, an ask part and its tells such
that at every solution the information is solved exactly when both are (`Splits`). The parts need not
be a prefix and a suffix of the information: only their solutions matter.

## The law

* **The before-tells step is a restriction** (`beforeTells`, by `Spaces.restrict`) to the firings
  whose guards hold at every solution of the ask part. It is exactly the admission that asks the guards
  there and keeps everything else (`beforeTells_admits_iff`): the shapes, the enabling of the
  selection, and solvability of the whole information, tells included. Results and their knowledge are
  those of the step (`result_beforeTells`); the before-tells form of a standard step is standard
  (`beforeTellsStandard`).
* **Inclusion** (`admits_of_beforeTells`, `succ_of_beforeTells`, `reaches_of_beforeTells`): a firing
  admitted before its tells is admitted after them, with the same result.
* **Equality where the ask part entails the tells** (`beforeTells_admits_iff_of_entailed`,
  `succ_beforeTells_iff_of_entailed`, `reaches_beforeTells_iff_of_entailed`); in particular for a
  firing that tells nothing (`beforeTells_admits_iff_of_no_tells`), and for a firing whose guards hold
  at every solution (`beforeTells_admits_iff_of_unguarded`).
* **Where they differ** (`refused_before_iff`): a firing admitted after its tells is refused before
  them exactly when a solution of its ask part that does not solve its tells fails a guard.
* **The law commutes with restriction** (`beforeTells_restrict_admits_iff`): the before-tells form of
  a restriction of a step is the restriction of its before-tells form. A commit presented as a
  restriction of a guarded step therefore has its before-tells form by this law.
* **The timing depends on the split** (`beforeTells_whole_admits_iff`): the split whose ask part is the
  whole information gives back the step.

Underneath is a statement about stores (`entails_of_splits`, `entails_iff_of_splits`): what every
solution of the ask part satisfies, every solution of the whole store satisfies, and conversely where
the ask part entails the tells. An ask part followed by tells is split into them (`splits_append`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb

open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface (Frames)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.StepSpan
  (Succ)

universe uO uT uH uOcc uS uF

/-! ## Splitting a store -/

section Stores

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} (X : Frames Tm Hom) {a : Obj}

/-- **A store split into an ask part and tells**: at every solution, the store is solved exactly when
both parts are. -/
def Splits (whole ask tells : EquationStore (Tm a)) : Prop :=
  ∀ (b : Obj) (σ : Hom a b), X.Models σ whole ↔ X.Models σ ask ∧ X.Models σ tells

/-- An ask part followed by tells is split into them. -/
theorem splits_append (ask tells : EquationStore (Tm a)) : Splits X (ask ++ tells) ask tells :=
  fun _ σ => Frames.models_append σ ask tells

/-- A store is split into itself and no tells. -/
theorem splits_nil (whole : EquationStore (Tm a)) : Splits X whole whole [] :=
  fun _ σ => ⟨fun solved => ⟨solved, Frames.models_nil σ⟩, And.left⟩

variable {X} {whole ask tells : EquationStore (Tm a)}

/-- **What every solution of the ask part satisfies, every solution of the whole store satisfies.** -/
theorem entails_of_splits (split : Splits X whole ask tells)
    {observation : (b : Obj) → Hom a b → Prop} (asked : X.Entails ask observation) :
    X.Entails whole observation :=
  fun b σ solved => asked b σ ((split b σ).mp solved).1

/-- **Where the ask part entails the tells, the ask part and the whole store entail the same.** -/
theorem entails_iff_of_splits (split : Splits X whole ask tells)
    (entailed : X.Entails ask fun _ σ => X.Models σ tells) {observation : (b : Obj) → Hom a b → Prop} :
    X.Entails ask observation ↔ X.Entails whole observation :=
  ⟨entails_of_splits split, fun asked b σ solved =>
    asked b σ ((split b σ).mpr ⟨solved, entailed b σ solved⟩)⟩

/-- A solvable store has a solvable ask part. -/
theorem solvable_of_splits (split : Splits X whole ask tells) (solvable : X.Solvable whole) :
    X.Solvable ask := by
  obtain ⟨b, σ, solved⟩ := solvable
  exact ⟨b, σ, ((split b σ).mp solved).1⟩

end Stores

/-! ## The law -/

section Law

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}

/-- **A split of a step's information**: for each firing, an ask part and its tells, the information
being solved exactly when both are. -/
structure AskSplit (P : Interface.Step X O State Firing) where
  ask : {s : State} → (f : Firing s) → EquationStore (Tm (P.target f))
  tells : {s : State} → (f : Firing s) → EquationStore (Tm (P.target f))
  splits : ∀ {s : State} (f : Firing s), Splits X (P.information f) (ask f) (tells f)

namespace AskSplit

variable {P : Interface.Step X O State Firing}

/-- **The ask part of a firing entails its tells**: every solution of the ask part solves them. -/
def Entailed (S : AskSplit P) {s : State} (f : Firing s) : Prop :=
  X.Entails (S.ask f) fun _ σ => X.Models σ (S.tells f)

/-- A firing that tells nothing has its tells entailed. -/
theorem entailed_of_no_tells (S : AskSplit P) {s : State} {f : Firing s} (silent : S.tells f = []) :
    S.Entailed f := by
  intro b σ _
  rw [silent]
  exact Frames.models_nil σ

/-- **The split whose ask part is the whole information.** -/
def whole (P : Interface.Step X O State Firing) : AskSplit P where
  ask f := P.information f
  tells _ := []
  splits f := splits_nil X (P.information f)

/-- **The split of a restriction**: the same parts. -/
def restrict (S : AskSplit P) (allowed : ∀ {s : State}, Firing s → Prop) :
    AskSplit (Spaces.restrict P allowed) where
  ask f := S.ask f
  tells f := S.tells f
  splits f := S.splits f

end AskSplit

variable (P : Interface.Step X O State Firing) [P.Guarded] (S : AskSplit P)

/-- **The guards of a firing asked before its own tells**: they hold at every solution of its ask
part. -/
def AsksBeforeTells {s : State} (f : Firing s) : Prop :=
  X.Entails (S.ask f) (P.Holds f)

/-- **The step whose guards are asked before the firing's own tells**: the restriction of the step to
the firings whose guards hold at every solution of their ask part. -/
def beforeTells : Interface.Step X O State Firing :=
  Spaces.restrict P fun {_} f => AsksBeforeTells P S f

instance beforeTells_guarded : (beforeTells P S).Guarded :=
  Spaces.restrict_guarded P fun {_} f => AsksBeforeTells P S f

instance beforeTells_literalInformation [P.LiteralInformation] :
    (beforeTells P S).LiteralInformation :=
  Spaces.restrict_literalInformation P fun {_} f => AsksBeforeTells P S f

instance beforeTells_literalKnowledge [P.LiteralKnowledge] : (beforeTells P S).LiteralKnowledge :=
  Spaces.restrict_literalKnowledge P fun {_} f => AsksBeforeTells P S f

theorem beforeTells_admits {s : State} (f : Firing s) :
    (beforeTells P S).Admits f ↔ P.Admits f ∧ AsksBeforeTells P S f :=
  Iff.rfl

/-- **The before-tells step asks the guards at the ask part and keeps everything else**: a firing is
admitted before its tells exactly when it is prepared (shapes, enabling, solvable information, tells
included) and its guards hold at every solution of its ask part. -/
theorem beforeTells_admits_iff {s : State} (f : Firing s) :
    (beforeTells P S).Admits f ↔ P.Prepares f ∧ X.Entails (S.ask f) (P.Holds f) := by
  constructor
  · intro admitted
    exact ⟨P.prepares admitted.1, admitted.2⟩
  · intro prepared
    exact ⟨(P.admits_iff_prepares f).mpr ⟨prepared.1, entails_of_splits (S.splits f) prepared.2⟩,
      prepared.2⟩

/-- **Inclusion**: a firing admitted before its tells is admitted after them. -/
theorem admits_of_beforeTells {s : State} {f : Firing s} (admitted : (beforeTells P S).Admits f) :
    P.Admits f :=
  admitted.1

/-- **The same result.** -/
theorem result_beforeTells {s : State} {f : Firing s} (admitted : (beforeTells P S).Admits f) :
    (beforeTells P S).result f admitted = P.result f (admits_of_beforeTells P S admitted) :=
  rfl

/-- **Equality where the ask part entails the tells.** -/
theorem beforeTells_admits_iff_of_entailed {s : State} {f : Firing s} (entailed : S.Entailed f) :
    (beforeTells P S).Admits f ↔ P.Admits f :=
  ⟨admits_of_beforeTells P S, fun admitted =>
    ⟨admitted, (entails_iff_of_splits (S.splits f) entailed).mpr
      ((P.admits_iff_prepares f).mp admitted).2⟩⟩

/-- **Equality for a firing that tells nothing.** -/
theorem beforeTells_admits_iff_of_no_tells {s : State} {f : Firing s} (silent : S.tells f = []) :
    (beforeTells P S).Admits f ↔ P.Admits f :=
  beforeTells_admits_iff_of_entailed P S (S.entailed_of_no_tells silent)

/-- **Equality for a firing whose guards hold at every solution.** -/
theorem beforeTells_admits_iff_of_unguarded {s : State} {f : Firing s}
    (unguarded : ∀ (b : Obj) (σ : Hom (P.target f) b), P.Holds f b σ) :
    (beforeTells P S).Admits f ↔ P.Admits f :=
  ⟨admits_of_beforeTells P S, fun admitted => ⟨admitted, fun b σ _ => unguarded b σ⟩⟩

/-- **Where the two timings differ**: a firing admitted after its tells is refused before them exactly
when some solution of its ask part, which then does not solve its tells, fails a guard. -/
theorem refused_before_iff {s : State} {f : Firing s} (admitted : P.Admits f) :
    ¬ (beforeTells P S).Admits f ↔
      ∃ (b : Obj) (σ : Hom (P.target f) b),
        X.Models σ (S.ask f) ∧ ¬ X.Models σ (S.tells f) ∧ ¬ P.Holds f b σ := by
  constructor
  · intro refused
    by_contra none
    apply refused
    refine ⟨admitted, fun b σ asked => ?_⟩
    by_contra fails
    by_cases told : X.Models σ (S.tells f)
    · exact fails (((P.admits_iff_prepares f).mp admitted).2 b σ ((S.splits f b σ).mpr ⟨asked, told⟩))
    · exact none ⟨b, σ, asked, told, fails⟩
  · rintro ⟨b, σ, asked, -, fails⟩ before
    exact fails (before.2 b σ asked)

/-! ## Transitions -/

/-- **Inclusion of transitions.** -/
theorem succ_of_beforeTells {s t : State} (stepped : Succ (beforeTells P S) s t) : Succ P s t := by
  obtain ⟨f, admitted, reached⟩ := stepped
  exact ⟨f, admitted.1, reached⟩

/-- **Equality of transitions** from a state whose firings have their tells entailed. -/
theorem succ_beforeTells_iff_of_entailed {s t : State} (entailed : ∀ f : Firing s, S.Entailed f) :
    Succ (beforeTells P S) s t ↔ Succ P s t := by
  refine ⟨succ_of_beforeTells P S, ?_⟩
  rintro ⟨f, admitted, reached⟩
  exact ⟨f, (beforeTells_admits_iff_of_entailed P S (entailed f)).mpr admitted, reached⟩

/-- **Inclusion of reachability.** -/
theorem reaches_of_beforeTells {s t : State}
    (run : Relation.ReflTransGen (Succ (beforeTells P S)) s t) : Relation.ReflTransGen (Succ P) s t := by
  induction run with
  | refl => exact .refl
  | tail _ last earlier => exact earlier.tail (succ_of_beforeTells P S last)

/-- **Equality of reachability** where every firing has its tells entailed. -/
theorem reaches_beforeTells_iff_of_entailed (entailed : ∀ {s : State} (f : Firing s), S.Entailed f)
    {s t : State} :
    Relation.ReflTransGen (Succ (beforeTells P S)) s t ↔ Relation.ReflTransGen (Succ P) s t := by
  refine ⟨reaches_of_beforeTells P S, fun run => ?_⟩
  induction run with
  | refl => exact .refl
  | tail _ last earlier =>
      exact earlier.tail ((succ_beforeTells_iff_of_entailed P S fun f => entailed f).mpr last)

/-! ## Restrictions and splits -/

/-- **The law commutes with restriction**: asking the guards of a restriction before the tells is
restricting the step whose guards are asked before the tells. -/
theorem beforeTells_restrict_admits_iff (allowed : ∀ {s : State}, Firing s → Prop) {s : State}
    (f : Firing s) :
    (beforeTells (Spaces.restrict P allowed) (S.restrict allowed)).Admits f ↔
      (Spaces.restrict (beforeTells P S) allowed).Admits f := by
  constructor
  · rintro ⟨⟨admitted, permitted⟩, asked⟩
    exact ⟨⟨admitted, fun b σ solved => (asked b σ solved).1⟩, permitted⟩
  · rintro ⟨⟨admitted, asked⟩, permitted⟩
    exact ⟨⟨admitted, permitted⟩, fun b σ solved => ⟨asked b σ solved, permitted⟩⟩

/-- **With the whole information as the ask part, the before-tells step is the step.** -/
theorem beforeTells_whole_admits_iff {s : State} (f : Firing s) :
    (beforeTells P (AskSplit.whole P)).Admits f ↔ P.Admits f :=
  beforeTells_admits_iff_of_no_tells P (AskSplit.whole P) rfl

end Law

/-! ## Standard steps -/

section Standard

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}

/-- **The before-tells form of a standard step is standard**: guarded, with literal information and
knowledge, so the theory stated for standard steps applies to it. -/
def beforeTellsStandard (Q : Interface.Step.Standard X O State Firing) (S : AskSplit Q.toStep) :
    Interface.Step.Standard X O State Firing :=
  Interface.Step.Standard.ofCertified (beforeTells Q.toStep S)

theorem beforeTellsStandard_admits_iff (Q : Interface.Step.Standard X O State Firing)
    (S : AskSplit Q.toStep) {s : State} (f : Firing s) :
    (beforeTellsStandard Q S).Admits f ↔ (beforeTells Q.toStep S).Admits f :=
  Iff.rfl

end Standard

#print axioms splits_append
#print axioms entails_of_splits
#print axioms entails_iff_of_splits
#print axioms beforeTells_admits_iff
#print axioms admits_of_beforeTells
#print axioms result_beforeTells
#print axioms beforeTells_admits_iff_of_entailed
#print axioms beforeTells_admits_iff_of_no_tells
#print axioms beforeTells_admits_iff_of_unguarded
#print axioms refused_before_iff
#print axioms succ_of_beforeTells
#print axioms succ_beforeTells_iff_of_entailed
#print axioms reaches_of_beforeTells
#print axioms reaches_beforeTells_iff_of_entailed
#print axioms beforeTells_restrict_admits_iff
#print axioms beforeTells_whole_admits_iff
#print axioms beforeTellsStandard

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.StepWeb
