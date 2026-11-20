import Mettapedia.Logic.ModalMuCalculusSimulation
import Mettapedia.Logic.ModalQuantaleSemantics
import Mettapedia.GSLT.LanguageDef.CertificateGSLTMuCalculusBoundary
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.StepConcepts

/-!
# Fixed-point formulas over the step's systems, and exactly when they denote types

The tree's modal μ-calculus (`Mettapedia.Logic.ModalMuCalculus`) reads a least fixed point as the
intersection of the pre-fixed sets of its body and a greatest one as the union of the post-fixed
sets, for every body. This module reads it over the step's systems and settles when its formulas
denote types.

* **Zigzag maps** (`IsZigzag`, `satisfies_pull`): a map that carries every transition, and every
  transition of whose images comes from one, pulls the meaning of every formula whose fixed points
  have positive bodies back to its meaning (`fixedPointsPositive`, the tree's admission condition for
  fixed-point checking). A least fixed point needs the monotonicity of the source's body, and only
  in one direction; a greatest one the same, in the other direction.
* **Bisimulations** (`satisfies_iff_of_bisimulation`): a relation that is a simulation both ways
  (`IsSimulation`) is the image of its own span (`spanLTS`), whose two projections are zigzag maps.
  So related states satisfy the same formulas with positive fixed points, for environments that the
  relation respects.
* **Positivity is needed** (`Controls.nonpositive_splits`): on four states, `a → d` and `b → d`,
  `b → e`, the states `a` and `b` are bisimilar, and the least fixed point of
  `◇⊤ ∧ ¬(◇X ∧ ◇¬X)` holds at `a` and fails at `b`. Without positivity the impredicative reading of
  a least fixed point is not invariant.
* **Over a system with observations** (`ltsOf`, `FixFormula`): the labelled steps form a transition
  system, and an atom is a free variable read as the states where it is observed (`atomEnv`), the
  tree's own convention for observations in fixed-point formulas. A fixed-point formula over the
  system is a formula with positive fixed points and finitely many named atoms.
* **The types they denote** (`FixFormula.bisimClosed`, `FixFormula.isConcept_iformulas`,
  `FixFormula.iformula`): every fixed-point formula denotes a class closed under bisimilarity, so a
  type of the infinitary formulas, denoted by one of them.
* **Every finitary formula is a fixed-point formula** (`ofFinitary`, `ofFinitary_holds`): its atom
  occurrences become free variables, in order.

So, on every system: finitary types ⊆ fixed-point types ⊆ bisimulation-closed classes = infinitary
types (`ladder_inclusions`). Where each inclusion is strict is in `Ladder`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.WhenTypesApply.FixpointTypes

open Set
open Mettapedia.Logic.ModalMuCalculus
open Mettapedia.Logic.ModalQuantaleSemantics.Boolean (bodyOrderHom)
open Mettapedia.GSLT.LanguageDef.CertificateGSLT.MuCalculusBoundary (fixedPointsPositive)

universe u v w

section Zigzag

variable {S : Type u} {T : Type v} {Act : Type w}

/-- **A zigzag map**: it carries every transition, and every transition from an image comes from a
transition of the source. -/
structure IsZigzag (source : LTS S Act) (target : LTS T Act) (map : S → T) : Prop where
  forth : ∀ state action next, source.trans state action next →
    target.trans (map state) action (map next)
  back : ∀ state action image, target.trans (map state) action image →
    ∃ next, source.trans state action next ∧ map next = image

/-- The pullback of an environment along a map. -/
def pullEnv {n : ℕ} (map : S → T) (ρ : Env T n) : Env S n := fun index => map ⁻¹' ρ index

theorem mem_pullEnv_extend {n : ℕ} (map : S → T) (ρ : Env T n) (Y : Set T) (index : Fin (n + 1))
    (state : S) :
    state ∈ pullEnv map (ρ.extend Y) index ↔ state ∈ (pullEnv map ρ).extend (map ⁻¹' Y) index := by
  unfold pullEnv Env.extend
  split <;> exact Iff.rfl

/-- **A zigzag map pulls meanings back**: for every formula whose fixed points have positive bodies,
a state satisfies it at the pulled-back environment exactly when its image satisfies it. -/
theorem satisfies_pull {source : LTS S Act} {target : LTS T Act} {map : S → T}
    (zigzag : IsZigzag source target map) :
    ∀ {n : ℕ} (formula : Formula Act n), fixedPointsPositive formula = true →
      ∀ (ρ : Env T n) (state : S),
        satisfies source (pullEnv map ρ) formula state ↔ satisfies target ρ formula (map state)
  | _, .tt, _, _, _ => Iff.rfl
  | _, .ff, _, _, _ => Iff.rfl
  | _, .neg inner, positive, ρ, state => not_congr (satisfies_pull zigzag inner positive ρ state)
  | _, .conj first second, positive, ρ, state => by
      simp only [fixedPointsPositive, Bool.and_eq_true] at positive
      exact and_congr (satisfies_pull zigzag first positive.1 ρ state)
        (satisfies_pull zigzag second positive.2 ρ state)
  | _, .disj first second, positive, ρ, state => by
      simp only [fixedPointsPositive, Bool.and_eq_true] at positive
      exact or_congr (satisfies_pull zigzag first positive.1 ρ state)
        (satisfies_pull zigzag second positive.2 ρ state)
  | _, .diamond action body, positive, ρ, state => by
      constructor
      · rintro ⟨next, step, holds⟩
        exact ⟨map next, zigzag.forth state action next step,
          (satisfies_pull zigzag body positive ρ next).mp holds⟩
      · rintro ⟨image, step, holds⟩
        obtain ⟨next, step', rfl⟩ := zigzag.back state action image step
        exact ⟨next, step', (satisfies_pull zigzag body positive ρ next).mpr holds⟩
  | _, .box action body, positive, ρ, state => by
      constructor
      · intro all image step
        obtain ⟨next, step', rfl⟩ := zigzag.back state action image step
        exact (satisfies_pull zigzag body positive ρ next).mp (all next step')
      · intro all next step
        exact (satisfies_pull zigzag body positive ρ next).mpr
          (all (map next) (zigzag.forth state action next step))
  | _, .var _, _, _, _ => Iff.rfl
  | _, .mu body, positive, ρ, state => by
      simp only [fixedPointsPositive, Bool.and_eq_true] at positive
      have pulled : ∀ (Y : Set T) (s : S),
          satisfies source ((pullEnv map ρ).extend (map ⁻¹' Y)) body s ↔
            satisfies target (ρ.extend Y) body (map s) := fun Y s =>
        (satisfies_congr (fun _ _ _ => Iff.rfl)
          (fun index s' => (mem_pullEnv_extend map ρ Y index s').symm) body s).trans
          (satisfies_pull zigzag body positive.2 (ρ.extend Y) s)
      constructor
      · intro least Y closed
        exact least (map ⁻¹' Y) fun s holds => closed (map s) ((pulled Y s).mp holds)
      · intro least X closed
        have inside : map ⁻¹' {t | ∀ s, map s = t → s ∈ X} ⊆ X := fun s member => member s rfl
        have closedY : ∀ t, satisfies target (ρ.extend {t | ∀ s, map s = t → s ∈ X}) body t →
            t ∈ {t | ∀ s, map s = t → s ∈ X} := by
          rintro t holds s rfl
          exact closed s ((bodyOrderHom source (pullEnv map ρ) body positive.1).monotone inside
            ((pulled _ s).mpr holds))
        exact least _ closedY state rfl
  | _, .nu body, positive, ρ, state => by
      simp only [fixedPointsPositive, Bool.and_eq_true] at positive
      have pulled : ∀ (Y : Set T) (s : S),
          satisfies source ((pullEnv map ρ).extend (map ⁻¹' Y)) body s ↔
            satisfies target (ρ.extend Y) body (map s) := fun Y s =>
        (satisfies_congr (fun _ _ _ => Iff.rfl)
          (fun index s' => (mem_pullEnv_extend map ρ Y index s').symm) body s).trans
          (satisfies_pull zigzag body positive.2 (ρ.extend Y) s)
      constructor
      · rintro ⟨X, member, post⟩
        refine ⟨map '' X, ⟨state, member, rfl⟩, ?_⟩
        rintro _ ⟨s, inX, rfl⟩
        exact (pulled (map '' X) s).mp
          ((bodyOrderHom source (pullEnv map ρ) body positive.1).monotone
            (Set.subset_preimage_image map X) (post s inX))
      · rintro ⟨Y, member, post⟩
        exact ⟨map ⁻¹' Y, member, fun s inY => (pulled Y s).mpr (post (map s) inY)⟩

/-! ## Bisimulations, through their spans -/

/-- The pairs a relation relates. -/
abbrev Related (relation : S → T → Prop) := {p : S × T // relation p.1 p.2}

/-- **The span of a relation**: a related pair steps when both components step, to a related
pair. -/
def spanLTS (source : LTS S Act) (target : LTS T Act) (relation : S → T → Prop) :
    LTS (Related relation) Act where
  trans p action q := source.trans p.1.1 action q.1.1 ∧ target.trans p.1.2 action q.1.2

theorem fst_isZigzag {source : LTS S Act} {target : LTS T Act} {relation : S → T → Prop}
    (forth : IsSimulation source target relation) :
    IsZigzag (spanLTS source target relation) source fun p => p.1.1 where
  forth _ _ _ step := step.1
  back p action next step := by
    obtain ⟨image, step', related⟩ := forth p.1.1 p.1.2 p.2 action next step
    exact ⟨⟨(next, image), related⟩, ⟨step, step'⟩, rfl⟩

theorem snd_isZigzag {source : LTS S Act} {target : LTS T Act} {relation : S → T → Prop}
    (back : IsSimulation target source fun t s => relation s t) :
    IsZigzag (spanLTS source target relation) target fun p => p.1.2 where
  forth _ _ _ step := step.2
  back p action image step := by
    obtain ⟨next, step', related⟩ := back p.1.2 p.1.1 p.2 action image step
    exact ⟨⟨(next, image), related⟩, ⟨step', step⟩, rfl⟩

/-- **Bisimilar states satisfy the same formulas with positive fixed points**, for environments the
relation respects: a relation that is a simulation both ways relates states that agree on every
such formula. -/
theorem satisfies_iff_of_bisimulation {source : LTS S Act} {target : LTS T Act}
    {relation : S → T → Prop} (forth : IsSimulation source target relation)
    (back : IsSimulation target source fun t s => relation s t)
    {n : ℕ} (formula : Formula Act n) (positive : fixedPointsPositive formula = true)
    {sourceEnv : Env S n} {targetEnv : Env T n}
    (related : ∀ index s t, relation s t → (s ∈ sourceEnv index ↔ t ∈ targetEnv index))
    {s : S} {t : T} (relates : relation s t) :
    satisfies source sourceEnv formula s ↔ satisfies target targetEnv formula t := by
  have first := satisfies_pull (fst_isZigzag forth) formula positive sourceEnv ⟨(s, t), relates⟩
  have second := satisfies_pull (snd_isZigzag back) formula positive targetEnv ⟨(s, t), relates⟩
  have same := satisfies_congr (lts := spanLTS source target relation)
    (ρ := pullEnv (fun p : Related relation => p.1.1) sourceEnv)
    (ρ' := pullEnv (fun p : Related relation => p.1.2) targetEnv) (fun _ _ _ => Iff.rfl)
    (fun index p => related index p.1.1 p.1.2 p.2) formula ⟨(s, t), relates⟩
  exact first.symm.trans (same.trans second)

end Zigzag

/-! ## Control: without positivity, bisimilar states are split -/

namespace Controls

/-- Four states. -/
inductive Four where
  | a
  | b
  | d
  | e
  deriving DecidableEq

/-- `a → d`, `b → d`, `b → e`. -/
inductive FourStep : Four → Unit → Four → Prop where
  | ad : FourStep .a () .d
  | bd : FourStep .b () .d
  | be : FourStep .b () .e

/-- The four-state system. -/
def four : LTS Four Unit where
  trans := FourStep

/-- The body `◇⊤ ∧ ¬(◇X ∧ ◇¬X)`: some step, and no two steps that `X` tells apart. -/
def splitterBody : Formula Unit 1 :=
  .conj (.diamond () .tt) (.neg (.conj (.diamond () (.var 0)) (.diamond () (.neg (.var 0)))))

/-- Its least fixed point. -/
def splitter : Formula Unit 0 := .mu splitterBody

theorem splitter_not_positive : fixedPointsPositive splitter = false := by rfl

/-- `a` and `b` are related by a simulation both ways. -/
def relates : Four → Four → Prop := fun x y => (x = .a ∧ y = .b) ∨ (x = .d ∧ (y = .d ∨ y = .e))

theorem relates_forth : IsSimulation four four relates := by
  rintro x y (⟨rfl, rfl⟩ | ⟨rfl, _⟩) action next step
  · cases step
    exact ⟨.d, FourStep.bd, Or.inr ⟨rfl, Or.inl rfl⟩⟩
  · cases step

theorem relates_back : IsSimulation four four fun y x => relates x y := by
  rintro y x (⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩) action next step
  · cases step with
    | bd => exact ⟨.d, FourStep.ad, Or.inr ⟨rfl, Or.inl rfl⟩⟩
    | be => exact ⟨.d, FourStep.ad, Or.inr ⟨rfl, Or.inr rfl⟩⟩
  · cases step
  · cases step

theorem splitter_a : satisfies four Env.empty splitter .a := by
  intro X closed
  apply closed .a
  refine ⟨⟨.d, FourStep.ad, trivial⟩, ?_⟩
  rintro ⟨⟨t, step, inX⟩, ⟨t', step', notInX⟩⟩
  cases step
  cases step'
  exact notInX inX

theorem splitter_not_b : ¬ satisfies four Env.empty splitter .b := by
  intro holds
  have closed : ∀ t, satisfies four (Env.empty.extend {Four.a, Four.d}) splitterBody t →
      t ∈ ({Four.a, Four.d} : Set Four) := by
    rintro t ⟨⟨u, step, -⟩, notSplit⟩
    cases step with
    | ad => exact Or.inl rfl
    | bd =>
        exfalso
        apply notSplit
        refine ⟨⟨.d, FourStep.bd, ?_⟩, ⟨.e, FourStep.be, ?_⟩⟩
        · show Four.d ∈ ({Four.a, Four.d} : Set Four)
          exact Or.inr rfl
        · show Four.e ∉ ({Four.a, Four.d} : Set Four)
          rintro (same | same) <;> cases same
    | be =>
        exfalso
        apply notSplit
        refine ⟨⟨.d, FourStep.bd, ?_⟩, ⟨.e, FourStep.be, ?_⟩⟩
        · show Four.d ∈ ({Four.a, Four.d} : Set Four)
          exact Or.inr rfl
        · show Four.e ∉ ({Four.a, Four.d} : Set Four)
          rintro (same | same) <;> cases same
  rcases holds _ closed with same | same <;> cases same

/-- **Control: without positivity, bisimilar states are split.** `a` and `b` are related by a
simulation both ways, and the least fixed point of a body that is not positive holds at `a` and
fails at `b`. -/
theorem nonpositive_splits :
    fixedPointsPositive splitter = false ∧ IsSimulation four four relates ∧
      IsSimulation four four (fun y x => relates x y) ∧ relates .a .b ∧
      satisfies four Env.empty splitter .a ∧ ¬ satisfies four Env.empty splitter .b :=
  ⟨splitter_not_positive, relates_forth, relates_back, Or.inl ⟨rfl, rfl⟩, splitter_a, splitter_not_b⟩

end Controls

/-! ## Over the step's systems: atoms as free variables -/

section Systems

open Mettapedia.GSLT
open Mettapedia.Cybernetics.DistinctionCalculus.Exclusion
open Distinctions.ObserverConcepts Distinctions.StepConcepts InfinitaryAdequacy

universe uG uA uL

variable {G : GSLT.{uG}} (M : HennessyMilner.System.{uA, uL} G)

/-- **The transition system of a system**: its labelled steps. -/
def ltsOf : LTS G.Term M.Label where
  trans s label s' := M.act label s s'

/-- **Atoms as free variables**: the `i`-th variable is read as the states where the `i`-th atom is
observed. -/
def atomEnv {n : ℕ} (atoms : Fin n → M.Atom) : Env G.Term n :=
  fun index => {s | M.observes (atoms index) s}

/-- **A fixed-point formula over a system**: a μ-calculus formula over its labels whose free variables
name atoms, every fixed point with a positive body. -/
structure FixFormula where
  arity : ℕ
  body : Formula M.Label arity
  atoms : Fin arity → M.Atom
  positive : fixedPointsPositive body = true

variable {M}

/-- Where a fixed-point formula holds. -/
def FixFormula.Holds (φ : FixFormula M) (s : G.Term) : Prop :=
  satisfies (ltsOf M) (atomEnv M φ.atoms) φ.body s

/-- **Every fixed-point formula denotes a class closed under bisimilarity.** -/
theorem FixFormula.bisimClosed (φ : FixFormula M) : BisimClosed M {s | φ.Holds s} := by
  rintro x holds y ⟨R, bisimulation, related⟩
  have forth : IsSimulation (ltsOf M) (ltsOf M) R := fun _ _ r a _ step => bisimulation.1 r a step
  have back : IsSimulation (ltsOf M) (ltsOf M) (fun t s => R s t) :=
    fun _ _ r a _ step => bisimulation.2.1 r a step
  have atoms : ∀ (index : Fin φ.arity) (s t : G.Term), R s t →
      (s ∈ atomEnv M φ.atoms index ↔ t ∈ atomEnv M φ.atoms index) :=
    fun index _ _ r => bisimulation.2.2 r (φ.atoms index)
  exact (satisfies_iff_of_bisimulation forth back φ.body φ.positive atoms related).mp holds

/-- **Every fixed-point formula denotes a type of the infinitary formulas.** -/
theorem FixFormula.isConcept_iformulas (φ : FixFormula M) :
    IsConcept (Apart (iformulas M)) {s | φ.Holds s} :=
  (isConcept_iformulas_iff M _).mpr φ.bisimClosed

/-- **Every fixed-point formula is equivalent to an infinitary formula.** -/
theorem FixFormula.iformula (φ : FixFormula M) :
    ∃ ψ : IFormula.{uG, uA, uL} M.Atom M.Label, ∀ s, isat M ψ s ↔ φ.Holds s :=
  exists_iformula_of_bisimClosed M φ.bisimClosed

/-! ## Every finitary formula is a fixed-point formula -/

/-- The atoms of a finitary formula, in order of occurrence. -/
def atomsOf {Atom : Type uA} {Label : Type uL} : HennessyMilner.Formula Atom Label → List Atom
  | .top => []
  | .atom a => [a]
  | .conj left right => atomsOf left ++ atomsOf right
  | .neg inner => atomsOf inner
  | .dia _ inner => atomsOf inner

/-- **The finitary formula as a fixed-point formula**: the `k`-th atom occurrence becomes the
variable `offset + k`. -/
def toMu {Atom : Type uA} {Label : Type uL} {total : ℕ} :
    (φ : HennessyMilner.Formula Atom Label) → (offset : ℕ) →
      offset + (atomsOf φ).length ≤ total → Formula Label total
  | .top, _, _ => .tt
  | .atom _, offset, fits => .var ⟨offset, by simp only [atomsOf, List.length_singleton] at fits; omega⟩
  | .conj left right, offset, fits =>
      .conj (toMu left offset (by simp only [atomsOf, List.length_append] at fits; omega))
        (toMu right (offset + (atomsOf left).length)
          (by simp only [atomsOf, List.length_append] at fits; omega))
  | .neg inner, offset, fits => .neg (toMu inner offset fits)
  | .dia label inner, offset, fits => .diamond label (toMu inner offset fits)

theorem toMu_positive {Atom : Type uA} {Label : Type uL} {total : ℕ} :
    ∀ (φ : HennessyMilner.Formula Atom Label) (offset : ℕ)
      (fits : offset + (atomsOf φ).length ≤ total), fixedPointsPositive (toMu φ offset fits) = true
  | .top, _, _ => rfl
  | .atom _, _, _ => rfl
  | .conj left right, offset, fits => by
      show (fixedPointsPositive (toMu left _ _) && fixedPointsPositive (toMu right _ _)) = true
      rw [toMu_positive left, toMu_positive right]
      rfl
  | .neg inner, offset, fits => toMu_positive inner offset fits
  | .dia _ inner, offset, fits => toMu_positive inner offset fits

theorem satisfies_toMu {total : ℕ} (E : ℕ → Set G.Term) :
    ∀ (φ : HennessyMilner.Formula M.Atom M.Label) (offset : ℕ)
      (fits : offset + (atomsOf φ).length ≤ total),
      (∀ (k : ℕ) (inside : k < (atomsOf φ).length) (s : G.Term),
        s ∈ E (offset + k) ↔ M.observes ((atomsOf φ)[k]) s) →
      ∀ s, satisfies (ltsOf M) (fun index : Fin total => E index) (toMu φ offset fits) s ↔ M.sat φ s
  | .top, _, _, _, _ => Iff.rfl
  | .atom a, offset, _, named, s => named 0 (by simp [atomsOf]) s
  | .conj left right, offset, fits, named, s => by
      have leftFits : offset + (atomsOf left).length ≤ total := by
        simp only [atomsOf, List.length_append] at fits; omega
      have rightFits : offset + (atomsOf left).length + (atomsOf right).length ≤ total := by
        simp only [atomsOf, List.length_append] at fits; omega
      have leftNamed : ∀ (k : ℕ) (inside : k < (atomsOf left).length) (s' : G.Term),
          s' ∈ E (offset + k) ↔ M.observes ((atomsOf left)[k]) s' := by
        intro k inside s'
        rw [named k (by simp only [atomsOf, List.length_append]; omega) s']
        simp [atomsOf, inside]
      have rightNamed : ∀ (k : ℕ) (inside : k < (atomsOf right).length) (s' : G.Term),
          s' ∈ E (offset + (atomsOf left).length + k) ↔ M.observes ((atomsOf right)[k]) s' := by
        intro k inside s'
        rw [Nat.add_assoc, named ((atomsOf left).length + k)
          (by simp only [atomsOf, List.length_append]; omega) s']
        simp [atomsOf]
      exact and_congr (satisfies_toMu E left offset leftFits leftNamed s)
        (satisfies_toMu E right _ rightFits rightNamed s)
  | .neg inner, offset, fits, named, s => not_congr (satisfies_toMu E inner offset fits named s)
  | .dia label inner, offset, fits, named, s => by
      constructor
      · rintro ⟨next, step, holds⟩
        exact ⟨next, step, (satisfies_toMu E inner offset fits named next).mp holds⟩
      · rintro ⟨next, step, holds⟩
        exact ⟨next, step, (satisfies_toMu E inner offset fits named next).mpr holds⟩

variable (M) in
/-- **Every finitary formula is a fixed-point formula**, with its atom occurrences as variables. -/
def ofFinitary (φ : HennessyMilner.Formula M.Atom M.Label) : FixFormula M where
  arity := (atomsOf φ).length
  body := toMu φ 0 (by simp)
  atoms index := (atomsOf φ)[index]
  positive := toMu_positive φ 0 _

theorem ofFinitary_holds (φ : HennessyMilner.Formula M.Atom M.Label) (s : G.Term) :
    (ofFinitary M φ).Holds s ↔ M.sat φ s := by
  have translated := satisfies_toMu (M := M) (total := (atomsOf φ).length)
    (fun k => {s | ∃ a, (atomsOf φ)[k]? = some a ∧ M.observes a s}) φ 0 (by simp)
    (fun k inside s' => by simp [List.getElem?_eq_getElem inside]) s
  refine (satisfies_congr (fun _ _ _ => Iff.rfl) (fun index s' => ?_) _ s).trans translated
  show M.observes ((atomsOf φ)[index]) s' ↔ ∃ a, (atomsOf φ)[(index : ℕ)]? = some a ∧ M.observes a s'
  have inside : (index : ℕ) < (atomsOf φ).length := index.isLt
  rw [List.getElem?_eq_getElem inside]
  constructor
  · intro holds
    exact ⟨_, rfl, holds⟩
  · rintro ⟨a, same, holds⟩
    cases Option.some.inj same
    exact holds

/-- **The ladder of inclusions, on every system**: every finitary formula is a fixed-point formula,
every fixed-point formula denotes a class closed under bisimilarity, and every such class is denoted
by an infinitary formula. -/
theorem ladder_inclusions :
    (∀ φ : HennessyMilner.Formula M.Atom M.Label, ∃ ψ : FixFormula M, ∀ s, ψ.Holds s ↔ M.sat φ s) ∧
      (∀ ψ : FixFormula M, BisimClosed M {s | ψ.Holds s}) ∧
      ∀ A : Set G.Term, BisimClosed M A →
        ∃ χ : IFormula.{uG, uA, uL} M.Atom M.Label, ∀ s, isat M χ s ↔ s ∈ A :=
  ⟨fun φ => ⟨ofFinitary M φ, ofFinitary_holds φ⟩, fun ψ => ψ.bisimClosed,
    fun _ closed => exists_iformula_of_bisimClosed M closed⟩

end Systems

#print axioms satisfies_pull
#print axioms satisfies_iff_of_bisimulation
#print axioms Controls.nonpositive_splits
#print axioms FixFormula.bisimClosed
#print axioms FixFormula.isConcept_iformulas
#print axioms FixFormula.iformula
#print axioms ofFinitary_holds
#print axioms ladder_inclusions

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.WhenTypesApply.FixpointTypes
