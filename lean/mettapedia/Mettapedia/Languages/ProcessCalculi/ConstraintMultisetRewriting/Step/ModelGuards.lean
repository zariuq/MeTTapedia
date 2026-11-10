import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

/-!
# Guards as syntax: a guard logic over a frame's terms

The interface leaves a firing's guards opaque (`Step.Holds` is any predicate of a solution). This
module gives them a syntax, as a fibre: opaque guards stay the general case, and a step whose guards
are written in the syntax (`Step.GuardedBy`) has the existing semantics.

* **Guard formulas** (`GuardFormula T O`): equations, absence and count of a pattern among the labels
  of a finite region of occurrences, `⊤`, `⊥`, `¬`, `∧`, `∨`, `→`. A formula is read at one solution.
  Its truth depends only on which equations hold there: `GuardFormula.Sat R` reads it relative to any
  relation `R` on terms (`sat_congr`), and carrying the terms along a map is reading the relation back
  (`sat_map`).
* **At a solution** (`Frames.Satisfies`): the relation is the solution's kernel, the equations it makes
  hold up to the frame equivalence (`Frames.kernel`). Agreeing solutions satisfy the same guards
  (`satisfies_congr`); a guard carried along a morphism is the guard read at the composite
  (`satisfies_carry`). **Positive** guards (equations, `⊤`, `⊥`, `∧`, `∨`) persist along later
  instantiation (`Satisfies.persist`); absence and count do not.
* **Asks** (`Ask`, `Frames.Asks`): quantifiers over the solutions of a store: at every solution, at some
  solution, and the same over closed solutions into a designated frame. Solvability is the ask
  `some ⊤` (`solvable_iff_some_top`).
* **The fibre** (`Step.GuardedBy`, `Step.admits_iff_asks`): when a step's guards are written in the
  syntax, admission is its shapes, the enabling of its selection, and two asks of its information.
* **The first-order run layer is in the fibre for its checks** (`AnnotatedRuns.firstOrder_guardedBy`):
  a query-free first-order firing's `Holds` is the conjunction of its checks read as guard formulas
  (`checkGuard_sat`), so its admission is `firstOrder_valid_iff_asks`. Predicate queries, whose region
  is an arbitrary function of the solution, stay opaque.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)

universe uO uT uH uOcc uU uS uF

/-- **Guard formulas** over terms `T`: equations, absence and count of a pattern among the labels of a
finite region of occurrences, and the propositional connectives. A formula is read at one solution. -/
inductive GuardFormula (T : Type uT) (O : Type uOcc) : Type (max uT uOcc)
  | top
  | bot
  | eq (left right : T)
  | absent (pattern : T) (region : Finset O) (label : O → T)
  | count (pattern : T) (region : Finset O) (label : O → T) (number : Nat)
  | not (φ : GuardFormula T O)
  | and (φ ψ : GuardFormula T O)
  | or (φ ψ : GuardFormula T O)
  | imp (φ ψ : GuardFormula T O)

namespace GuardFormula

variable {T : Type uT} {O : Type uOcc}

/-- The occurrences of a region whose label the relation relates to the pattern. -/
noncomputable def matching (R : T → T → Prop) (pattern : T) (region : Finset O) (label : O → T) :
    Finset O := by
  classical
  exact region.filter fun o => R pattern (label o)

theorem mem_matching {R : T → T → Prop} {pattern : T} {region : Finset O} {label : O → T} {o : O} :
    o ∈ matching R pattern region label ↔ o ∈ region ∧ R pattern (label o) := by
  classical
  simp only [matching, Finset.mem_filter]

/-- **Satisfaction relative to a relation on terms**: the relation says which equations hold. -/
def Sat (R : T → T → Prop) : GuardFormula T O → Prop
  | .top => True
  | .bot => False
  | .eq s t => R s t
  | .absent p W label => ∀ o ∈ W, ¬ R p (label o)
  | .count p W label n => (matching R p W label).card = n
  | .not φ => ¬ Sat R φ
  | .and φ ψ => Sat R φ ∧ Sat R ψ
  | .or φ ψ => Sat R φ ∨ Sat R ψ
  | .imp φ ψ => Sat R φ → Sat R ψ

theorem matching_congr {R R' : T → T → Prop} (same : ∀ s t, R s t ↔ R' s t) (pattern : T)
    (region : Finset O) (label : O → T) :
    matching R pattern region label = matching R' pattern region label := by
  ext o
  rw [mem_matching, mem_matching, same]

/-- **A guard's truth depends only on which equations hold.** -/
theorem sat_congr {R R' : T → T → Prop} (same : ∀ s t, R s t ↔ R' s t) :
    ∀ φ : GuardFormula T O, φ.Sat R ↔ φ.Sat R'
  | .top => Iff.rfl
  | .bot => Iff.rfl
  | .eq s t => same s t
  | .absent p _ label => forall₂_congr fun o _ => not_congr (same p (label o))
  | .count p W label n => by
      show (matching R p W label).card = n ↔ (matching R' p W label).card = n
      rw [matching_congr same]
  | .not φ => not_congr (sat_congr same φ)
  | .and φ ψ => and_congr (sat_congr same φ) (sat_congr same ψ)
  | .or φ ψ => or_congr (sat_congr same φ) (sat_congr same ψ)
  | .imp φ ψ => imp_congr (sat_congr same φ) (sat_congr same ψ)

/-- Carry every term of a guard along a map. -/
def map {U : Type uU} (g : T → U) : GuardFormula T O → GuardFormula U O
  | .top => .top
  | .bot => .bot
  | .eq s t => .eq (g s) (g t)
  | .absent p W label => .absent (g p) W (g ∘ label)
  | .count p W label n => .count (g p) W (g ∘ label) n
  | .not φ => .not (map g φ)
  | .and φ ψ => .and (map g φ) (map g ψ)
  | .or φ ψ => .or (map g φ) (map g ψ)
  | .imp φ ψ => .imp (map g φ) (map g ψ)

/-- **A carried guard is the guard read through the map.** -/
theorem sat_map {U : Type uU} (g : T → U) (R : U → U → Prop) :
    ∀ φ : GuardFormula T O, (φ.map g).Sat R ↔ φ.Sat (fun s t => R (g s) (g t))
  | .top => Iff.rfl
  | .bot => Iff.rfl
  | .eq _ _ => Iff.rfl
  | .absent _ _ _ => Iff.rfl
  | .count p W label n => by
      show (matching R (g p) W (g ∘ label)).card = n ↔
        (matching (fun s t => R (g s) (g t)) p W label).card = n
      have same : matching R (g p) W (g ∘ label) = matching (fun s t => R (g s) (g t)) p W label := by
        ext o
        rw [mem_matching, mem_matching]
        rfl
      rw [same]
  | .not φ => not_congr (sat_map g R φ)
  | .and φ ψ => and_congr (sat_map g R φ) (sat_map g R ψ)
  | .or φ ψ => or_congr (sat_map g R φ) (sat_map g R ψ)
  | .imp φ ψ => imp_congr (sat_map g R φ) (sat_map g R ψ)

/-- **Positive guards**: equations, `⊤` and `⊥` under `∧` and `∨`. -/
inductive Positive : GuardFormula T O → Prop
  | top : Positive .top
  | bot : Positive .bot
  | eq (s t : T) : Positive (.eq s t)
  | and {φ ψ : GuardFormula T O} : Positive φ → Positive ψ → Positive (.and φ ψ)
  | or {φ ψ : GuardFormula T O} : Positive φ → Positive ψ → Positive (.or φ ψ)

/-- **Positive guards only grow with the relation.** -/
theorem Positive.mono {R R' : T → T → Prop} (le : ∀ s t, R s t → R' s t) :
    ∀ {φ : GuardFormula T O}, φ.Positive → φ.Sat R → φ.Sat R'
  | _, .top, holds => holds
  | _, .bot, holds => holds
  | _, .eq s t, holds => le s t holds
  | _, .and one two, holds => ⟨one.mono le holds.1, two.mono le holds.2⟩
  | _, .or one two, holds => holds.elim (fun h => Or.inl (one.mono le h)) (fun h => Or.inr (two.mono le h))

end GuardFormula

/-- **Asks**: quantifiers over the solutions of a store. `every` and `some` range over every solution
into every later frame; `closedEvery` and `closedSome` over the closed solutions, into a designated
frame. -/
inductive Ask (T : Type uT) (O : Type uOcc) : Type (max uT uOcc)
  | every (φ : GuardFormula T O)
  | some (φ : GuardFormula T O)
  | closedEvery (φ : GuardFormula T O)
  | closedSome (φ : GuardFormula T O)

namespace Frames

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} (X : Frames Tm Hom)
  {O : Type uOcc}

/-- **The kernel of a solution**: the equations of its frame it makes hold. -/
def kernel {a b : Obj} (f : Hom a b) (s t : Tm a) : Prop := X.E (X.act f s) (X.act f t)

/-- **A guard read at a solution.** -/
def Satisfies {a b : Obj} (f : Hom a b) (φ : GuardFormula (Tm a) O) : Prop := φ.Sat (X.kernel f)

/-- A guard carried along a morphism. -/
def carryGuard {a b : Obj} (f : Hom a b) (φ : GuardFormula (Tm a) O) : GuardFormula (Tm b) O :=
  φ.map (X.act f)

/-- **Asks of a store**, with closed asks over the solutions into `point`. -/
def Asks (point : Obj) {a : Obj} (store : EquationStore (Tm a)) : Ask (Tm a) O → Prop
  | .every φ => X.Entails store fun _ f => X.Satisfies f φ
  | .some φ => ∃ (b : Obj) (f : Hom a b), X.Models f store ∧ X.Satisfies f φ
  | .closedEvery φ => ∀ f : Hom a point, X.Models f store → X.Satisfies f φ
  | .closedSome φ => ∃ f : Hom a point, X.Models f store ∧ X.Satisfies f φ

variable {X}

theorem models_iff_kernel {a b : Obj} (f : Hom a b) (store : EquationStore (Tm a)) :
    X.Models f store ↔ ∀ e ∈ store, X.kernel f e.1 e.2 :=
  Iff.rfl

/-- Agreeing solutions have the same kernel. -/
theorem kernel_congr {a b : Obj} {f g : Hom a b} (same : ∀ t, X.E (X.act f t) (X.act g t))
    (s t : Tm a) : X.kernel f s t ↔ X.kernel g s t := by
  have eqv := X.equivalence b
  exact ⟨fun h => eqv.trans (eqv.symm (same s)) (eqv.trans h (same t)),
    fun h => eqv.trans (same s) (eqv.trans h (eqv.symm (same t)))⟩

/-- **Agreeing solutions satisfy the same guards.** -/
theorem satisfies_congr {a b : Obj} {f g : Hom a b} (same : ∀ t, X.E (X.act f t) (X.act g t))
    (φ : GuardFormula (Tm a) O) : X.Satisfies f φ ↔ X.Satisfies g φ :=
  GuardFormula.sat_congr (kernel_congr same) φ

/-- The kernel of a composite. -/
theorem kernel_comp {a b c : Obj} (g : Hom b c) (f : Hom a b) (s t : Tm a) :
    X.kernel (X.comp g f) s t ↔ X.kernel g (X.act f s) (X.act f t) := by
  simp only [kernel, X.act_comp]

/-- **A carried guard is the guard read at the composite.** -/
theorem satisfies_carry {a b c : Obj} (f : Hom a b) (g : Hom b c) (φ : GuardFormula (Tm a) O) :
    X.Satisfies g (X.carryGuard f φ) ↔ X.Satisfies (X.comp g f) φ :=
  (GuardFormula.sat_map _ _ φ).trans
    (GuardFormula.sat_congr (fun s t => (kernel_comp g f s t).symm) φ)

/-- An equation a solution makes hold, every later instantiation keeps. -/
theorem kernel_persist {a b c : Obj} {f : Hom a b} {s t : Tm a} (held : X.kernel f s t)
    (g : Hom b c) : X.kernel (X.comp g f) s t :=
  (kernel_comp g f s t).mpr (X.preserves g held)

/-- **Positive guards persist** along later instantiation. -/
theorem Satisfies.persist {a b c : Obj} {f : Hom a b} {φ : GuardFormula (Tm a) O}
    (positive : φ.Positive) (held : X.Satisfies f φ) (g : Hom b c) : X.Satisfies (X.comp g f) φ :=
  positive.mono (fun _ _ h => kernel_persist h g) held

/-- **Solvability is the ask `some ⊤`.** -/
theorem solvable_iff_some_top (point : Obj) {a : Obj} (store : EquationStore (Tm a)) :
    X.Solvable store ↔ X.Asks (O := O) point store (.some .top) := by
  constructor
  · rintro ⟨b, f, solved⟩
    exact ⟨b, f, solved, trivial⟩
  · rintro ⟨b, f, solved, _⟩
    exact ⟨b, f, solved⟩

theorem asks_every_iff (point : Obj) {a : Obj} (store : EquationStore (Tm a))
    (φ : GuardFormula (Tm a) O) :
    X.Asks point store (.every φ) ↔ X.Entails store fun _ f => X.Satisfies f φ :=
  Iff.rfl

/-- An ask at every solution is an ask at every closed solution. -/
theorem asks_closedEvery_of_every (point : Obj) {a : Obj} {store : EquationStore (Tm a)}
    {φ : GuardFormula (Tm a) O} (asked : X.Asks point store (.every φ)) :
    X.Asks point store (.closedEvery φ) :=
  fun f solved => asked point f solved

/-- A closed instance of an ask at some closed solution is an instance at some solution. -/
theorem asks_some_of_closedSome (point : Obj) {a : Obj} {store : EquationStore (Tm a)}
    {φ : GuardFormula (Tm a) O} (asked : X.Asks point store (.closedSome φ)) :
    X.Asks point store (.some φ) := by
  obtain ⟨f, solved, holds⟩ := asked
  exact ⟨point, f, solved, holds⟩

end Frames

namespace Step

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  (P : Step X O State Firing)
  [P.Guarded]

/-- **A step whose guards are written in the guard syntax**: each firing's `Holds` is its guard formula
read at the solution. -/
def GuardedBy (guard : ∀ {s : State} (f : Firing s), GuardFormula (Tm (P.target f)) O) : Prop :=
  ∀ {s : State} (f : Firing s) (b : Obj) (σ : Hom (P.target f) b), P.Holds f b σ ↔ X.Satisfies σ (guard f)

/-- **Admission in the fibre**: its shapes, the enabling of its selection, and two asks of its
information, `some ⊤` (solvability) and `every` of its guard. -/
theorem admits_iff_asks {guard : ∀ {s : State} (f : Firing s), GuardFormula (Tm (P.target f)) O}
    (guarded : P.GuardedBy guard) (point : Obj) {s : State} (f : Firing s) :
    P.Admits f ↔ P.Shapes f ∧ Enabled (fun _ : O => ()) (P.present s) ((P.selection f).commit (T := Unit)) ∧
      X.Asks point (P.information f) (Ask.some (O := O) .top) ∧ X.Asks point (P.information f) (.every (guard f)) := by
  rw [P.admits_iff f, Frames.solvable_iff_some_top (O := O) point, Frames.asks_every_iff]
  exact and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
    (forall_congr' fun b => forall_congr' fun σ => imp_congr_right fun _ => guarded f b σ)))

end Step

/-! ## The first-order run layer: its checks are guard formulas -/

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open Interface (Frames GuardFormula)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO}

/-- A check as a guard formula over a labelled region. -/
def checkGuard (label : O → T) (W : Finset O) : Check T → GuardFormula T O
  | .equal left right => .eq left right
  | .absent pattern => .absent pattern W label
  | .count pattern number => .count pattern W label number

/-- A list of checks as the conjunction of their guard formulas. -/
def checksGuard (label : O → T) (W : Finset O) : List (Check T) → GuardFormula T O
  | [] => .top
  | check :: rest => .and (checkGuard label W check) (checksGuard label W rest)

/-- **A check means its guard formula** at every substitution. -/
theorem checkGuard_sat (A : SubstitutionAction T S) (σ : S) (label : O → T) (W : Finset O)
    (check : Check T) :
    (checkGuard label W check).Sat (fun s t => A.E (A.apply σ s) (A.apply σ t)) ↔
      check.Holds A σ label W := by
  cases check with
  | equal left right => exact Iff.rfl
  | absent pattern => exact Iff.rfl
  | count pattern number =>
      show (GuardFormula.matching _ pattern W label).card = number ↔
        (Check.«matches» A σ label W pattern).card = number
      have same : GuardFormula.matching (fun s t => A.E (A.apply σ s) (A.apply σ t)) pattern W label =
          Check.«matches» A σ label W pattern := by
        classical
        ext o
        rw [GuardFormula.mem_matching]
        simp only [Check.«matches», Finset.mem_filter]
      rw [same]

theorem checksGuard_sat (A : SubstitutionAction T S) (σ : S) (label : O → T) (W : Finset O) :
    ∀ checks : List (Check T),
      (checksGuard label W checks).Sat (fun s t => A.E (A.apply σ s) (A.apply σ t)) ↔
        ∀ check ∈ checks, check.Holds A σ label W
  | [] => by simp [checksGuard, GuardFormula.Sat]
  | check :: rest => by
      rw [List.forall_mem_cons, ← checkGuard_sat A σ label W check, ← checksGuard_sat A σ label W rest]
      exact Iff.rfl

variable [DecidableEq O] (A : SubstitutionAction T S) (label : O → T)

/-- The guard of a first-order firing at a configuration: the conjunction of its checks over the
present occurrences. -/
def firingGuard (C : Configuration T O) (f : Firing T S O) : GuardFormula T O :=
  checksGuard label C.present f.rule.checks

/-- **The first-order run layer is in the guard fibre for its query-free firings.** -/
theorem firstOrder_holds_iff_guard {C : Configuration T O} {f : Firing T S O} (noQueries : f.queries = [])
    (b : PUnit) (σ : S) :
    (firstOrder A label).Holds (s := C) f b σ ↔
      (Frames.ofSubstitution A).Satisfies (a := PUnit.unit) (b := b) σ (firingGuard label C f) := by
  show ((∀ check ∈ f.rule.checks, check.Holds A σ label C.present) ∧
      ∀ query ∈ f.queries, (query.atSolution σ).Holds label C.present) ↔ _
  constructor
  · rintro ⟨checks, _⟩
    exact (checksGuard_sat A σ label C.present f.rule.checks).mpr checks
  · intro holds
    refine ⟨(checksGuard_sat A σ label C.present f.rule.checks).mp holds, fun query member => ?_⟩
    rw [noQueries] at member
    cases member

/-- **Query-free first-order admission is two asks**: solvability and the ask of its checks. -/
theorem firstOrder_valid_iff_asks {C : Configuration T O} {f : Firing T S O}
    (noQueries : f.queries = []) :
    f.Valid A label C ↔ (firstOrder A label).Shapes (s := C) f ∧
      Enabled (fun _ : O => ()) C.present (f.selection.commit (T := Unit)) ∧
      (Frames.ofSubstitution A).Asks PUnit.unit (a := PUnit.unit) (f.selection.problem label f.rule C)
        (Interface.Ask.some (O := O) .top) ∧
      (Frames.ofSubstitution A).Asks PUnit.unit (a := PUnit.unit) (f.selection.problem label f.rule C)
        (.every (firingGuard label C f)) := by
  rw [firstOrder_admits_iff, Frames.solvable_iff_some_top (O := O) PUnit.unit, Frames.asks_every_iff]
  exact and_congr Iff.rfl (and_congr Iff.rfl (and_congr Iff.rfl
    (forall_congr' fun b => forall_congr' fun σ => imp_congr_right fun _ =>
      firstOrder_holds_iff_guard A label noQueries b σ)))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting

#print axioms Interface.GuardFormula.sat_congr
#print axioms Interface.GuardFormula.sat_map
#print axioms Interface.GuardFormula.Positive.mono
#print axioms Interface.Frames.satisfies_congr
#print axioms Interface.Frames.satisfies_carry
#print axioms Interface.Frames.Satisfies.persist
#print axioms Interface.Frames.solvable_iff_some_top
#print axioms Interface.Step.admits_iff_asks
#print axioms AnnotatedRuns.checkGuard_sat
#print axioms AnnotatedRuns.checksGuard_sat
#print axioms AnnotatedRuns.firstOrder_holds_iff_guard
#print axioms AnnotatedRuns.firstOrder_valid_iff_asks

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
