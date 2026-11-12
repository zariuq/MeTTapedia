import Mettapedia.TypeTheory.BubbleTypingRuns

/-!
# A conversion store on the dependent comparison core: lookups as guards

A store of proved conversions, for one bubble of the comparison core, as a guarded step of the
step interface (`Interface.Step.guarded`) over the frames of strict models
(`KnowledgeFramesCore.congruenceFrames`).

* **States** (`Store`): the expression reached, the ledger of told equations, one occurrence.
* **Moves** (`Move`): a rewrite step of the bubble, forwards or backwards, which tells the equation
  between its two expressions; or a **lookup**, which tells nothing.
* **The guard** (`Move.Guard`): a lookup asks that the knowledge entail the equation between the
  expression reached and its target. A rewrite step asks nothing.
* **A lookup is admitted exactly when the ledger's congruence closure converts**
  (`admits_lookup_iff`): the ask ranges over strict models, which are congruences, so one told
  equation serves under every context (`lookup_admitted_under`).
* **Sound** (`store_run_sound`): from a ledger of conversions of the bubble, every run leads to an
  expression the bubble converts with the first, and to a ledger of conversions.
* **Only growing** (`ledger_grows`); the refinement law of the interface is
  `Step.Run.models_start` at this step.
* **Complete inside the bubble** (`store_complete`, `store_reaches_iff`): the expressions reachable
  from the empty ledger are exactly those the bubble converts. Lookups change the length of runs
  and not what is reachable.

## Controls (`Controls`)

With the recursion equations of addition, at the store that has learnt `n + 0 ≐ n`:
* the lookup from `Vec (n + 0)` to `Vec n` is admitted (`lookup_admitted`), and so is the lookup
  from `Π (_ : Vec (n + 0)). nat` to `Π (_ : Vec n). nat`, two formers deep (`deep_lookup_admitted`);
* with nothing learnt the lookup is refused (`lookup_refused_unlearned`);
* the lookup from `Vec (0 + n)` to `Vec n` is refused (`wrong_lookup_refused`).

Scope: the comparison core of `SimpleSliceOfDependent`; one bubble; the ledger is a list and its
closure is the conversion of the bubble whose root rules are the ledger's equations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ConversionStoreCore

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire)
open Mettapedia.Logic.TheoryModel
open Mettapedia.TypeTheory.BubbleConversion
open Mettapedia.TypeTheory.BubbleWeakness
open Mettapedia.TypeTheory.ConversionRuns
open Mettapedia.TypeTheory.KnowledgeFramesCore
open Mettapedia.TypeTheory.BubbleTypingRuns
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.Embedding.SimpleSliceOfDependent
open Expr

universe u v

section Core

variable {Base : Type u} {Const : Ty Base → Type v}

/-- A conversion store at work: the expression reached, the told equations, one occurrence. -/
structure Store (Base : Type u) (Const : Ty Base → Type v) where
  cursor : Expr Base Const
  ledger : EquationStore (Expr Base Const)
  clock : Nat

/-- A move of the store: a rewrite step of the bubble, forwards or backwards, or a lookup. -/
inductive Move (rules : Expr Base Const → Expr Base Const → Prop) (source : Expr Base Const) :
    Type (max u v) where
  | forward (target : Expr Base Const) (step : Rewrite rules source target) : Move rules source
  | backward (target : Expr Base Const) (step : Rewrite rules target source) : Move rules source
  | lookup (target : Expr Base Const) : Move rules source

namespace Move

variable {rules : Expr Base Const → Expr Base Const → Prop} {source : Expr Base Const}

/-- The expression a move leads to. -/
def target : Move rules source → Expr Base Const
  | forward target _ => target
  | backward target _ => target
  | lookup target => target

/-- The knowledge after a move: a rewrite step tells its equation; a lookup tells nothing. -/
def information (ledger : EquationStore (Expr Base Const)) :
    Move rules source → EquationStore (Expr Base Const)
  | forward target _ => ledger ++ [(source, target)]
  | backward target _ => ledger ++ [(source, target)]
  | lookup _ => ledger

/-- What a move asks of a strict model: a lookup asks for its equation; a rewrite step asks
nothing. -/
def Guard : Move rules source → Congruence Base Const → Prop
  | forward _ _, _ => True
  | backward _ _, _ => True
  | lookup target, θ => θ.rel source target

theorem ledger_subset_information (ledger : EquationStore (Expr Base Const))
    (move : Move rules source) : ∀ e ∈ ledger, e ∈ move.information ledger := by
  intro e member
  cases move with
  | forward target step => exact List.mem_append_left _ member
  | backward target step => exact List.mem_append_left _ member
  | lookup target => exact member

end Move

/-- The effect of a move, before any permission. -/
def core (rules : Expr Base Const → Expr Base Const → Prop) :
    EffectCore (congruenceFrames Base Const) Nat (Store Base Const)
      (fun store => Move rules store.cursor) where
  frame := fun _ => syntactic
  knowledge := fun store => store.ledger
  present := fun store => {store.clock}
  selection := fun {store} _ => ⟨[store.clock], [], [store.clock + 1]⟩
  target := fun _ => syntactic
  extension := fun _ => ⟨fun _ _ related => related⟩
  information := fun {store} move => move.information store.ledger
  information_refines := by
    intro store move model coarsening solved e member
    exact solved e (Move.ledger_subset_information store.ledger move e member)
  Shapes := fun _ => True
  preparedResult := fun {store} move _ =>
    ⟨move.target, move.information store.ledger, store.clock + 1⟩
  present_preparedResult := by
    intro store move _
    ext occurrence
    simp [fire, Selection.commit]
  preparedSettle := fun _ _ => ⟨fun _ _ related => related⟩
  result_refines := by
    intro store move _ model coarsening solved
    exact solved

/-- **The conversion store of a bubble**: its moves, guarded by their asks of the knowledge. -/
def storeStep (rules : Expr Base Const → Expr Base Const → Prop) :
    Step (congruenceFrames Base Const) Nat (Store Base Const)
      (fun store => Move rules store.cursor) :=
  Step.guarded (core rules) (fun {_} move θ _ => move.Guard θ)

variable {rules : Expr Base Const → Expr Base Const → Prop}

/-- Every move is prepared. -/
theorem prepared {store : Store Base Const} (move : Move rules store.cursor) :
    (core rules).Prepares move := by
  refine ⟨trivial, ⟨?_, ?_, ?_, ?_, ?_⟩, total, ⟨fun _ _ _ => trivial⟩, fun _ _ => trivial⟩
  all_goals simp [core, Selection.commit]

/-- **A lookup is admitted exactly when the congruence closure of the ledger converts.** -/
theorem admits_lookup_iff {store : Store Base Const} (target : Expr Base Const) :
    (storeStep rules).Admits (Move.lookup target : Move rules store.cursor) ↔
      Convertible (assumed store.ledger) store.cursor target := by
  constructor
  · rintro ⟨_, entailed⟩
    exact (entails_iff_convertible store.ledger store.cursor target).mp entailed
  · intro converted
    exact ⟨prepared _, (entails_iff_convertible store.ledger store.cursor target).mpr converted⟩

/-- A rewrite step of the bubble is always admitted. -/
theorem admits_forward {store : Store Base Const} (target : Expr Base Const)
    (step : Rewrite rules store.cursor target) :
    (storeStep rules).Admits (Move.forward target step : Move rules store.cursor) :=
  ⟨prepared _, fun _ _ _ => trivial⟩

theorem admits_backward {store : Store Base Const} (target : Expr Base Const)
    (step : Rewrite rules target store.cursor) :
    (storeStep rules).Admits (Move.backward target step : Move rules store.cursor) :=
  ⟨prepared _, fun _ _ _ => trivial⟩

/-- **Sharing.** If the ledger's closure converts `a` with `b`, the lookup from `family a` to
`family b` is admitted, for every one-hole context of the core. -/
theorem lookup_admitted_under {ledger : EquationStore (Expr Base Const)}
    (family : Expr Base Const → Expr Base Const)
    (crosses : ∀ {x x' : Expr Base Const},
      Rewrite (assumed ledger) x x' → Rewrite (assumed ledger) (family x) (family x'))
    {a b : Expr Base Const} (known : Convertible (assumed ledger) a b) (clock : Nat) :
    (storeStep rules).Admits
      (Move.lookup (family b) : Move rules (Store.mk (family a) ledger clock).cursor) :=
  (admits_lookup_iff (store := Store.mk (family a) ledger clock) (family b)).mpr
    (convertible_context family crosses known)

/-- A store is sound for a bubble when every told equation is a conversion of the bubble. -/
def Sound (rules : Expr Base Const → Expr Base Const → Prop) (store : Store Base Const) : Prop :=
  ∀ e ∈ store.ledger, Convertible rules e.1 e.2

/-- The closure of a ledger of conversions of a bubble is contained in the bubble's conversion. -/
theorem convertible_of_assumed {ledger : EquationStore (Expr Base Const)}
    (sound : ∀ e ∈ ledger, Convertible rules e.1 e.2) {e e' : Expr Base Const}
    (converted : Convertible (assumed ledger) e e') : Convertible rules e e' :=
  rel_of_convertible (θ := conversionModel rules) (mem_models_assumed.mpr sound) converted

/-- An admitted move from a sound store leads to an expression the bubble converts with the one
reached, and to a sound ledger. -/
theorem move_sound {store : Store Base Const} (move : Move rules store.cursor)
    (admitted : (storeStep rules).Admits move) (sound : Sound rules store) :
    Convertible rules store.cursor move.target ∧
      ∀ e ∈ move.information store.ledger, Convertible rules e.1 e.2 := by
  cases move with
  | forward target step =>
      refine ⟨Relation.EqvGen.rel _ _ step, fun e member => ?_⟩
      have split : e ∈ store.ledger ++ [(store.cursor, target)] := member
      rcases List.mem_append.mp split with old | told
      · exact sound e old
      · obtain rfl := List.mem_singleton.mp told
        exact Relation.EqvGen.rel _ _ step
  | backward target step =>
      refine ⟨Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ step), fun e member => ?_⟩
      have split : e ∈ store.ledger ++ [(store.cursor, target)] := member
      rcases List.mem_append.mp split with old | told
      · exact sound e old
      · obtain rfl := List.mem_singleton.mp told
        exact Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ step)
  | lookup target =>
      exact ⟨convertible_of_assumed sound ((admits_lookup_iff target).mp admitted), sound⟩

/-- **Soundness of the store.** From a sound store, every run leads to an expression the bubble
converts with the first, and to a sound store. -/
theorem store_run_sound : ∀ {store : Store Base Const} (run : (storeStep rules).Run store),
    Sound rules store → Convertible rules store.cursor run.last.cursor ∧ Sound rules run.last
  | _, .nil _, sound => ⟨Relation.EqvGen.refl _, sound⟩
  | _, .cons move admitted rest, sound =>
      have here := move_sound move admitted sound
      have later := store_run_sound rest here.2
      ⟨Relation.EqvGen.trans _ _ _ here.1 later.1, later.2⟩

/-- **The ledger only grows.** -/
theorem ledger_grows : ∀ {store : Store Base Const} (run : (storeStep rules).Run store),
    ∀ e ∈ store.ledger, e ∈ run.last.ledger
  | _, .nil _, _, member => member
  | store, .cons move _ rest, e, member =>
      ledger_grows rest e (Move.ledger_subset_information store.ledger move e member)

/-- Every zigzag of the bubble is followed by a run of the store, by rewrite steps. -/
theorem store_run_of_zigzag : ∀ {a b : Expr Base Const},
    Zigzag (bubbles Base Const) rules (index := ()) a b →
      ∀ (ledger : EquationStore (Expr Base Const)) (clock : Nat),
        ∃ run : (storeStep rules).Run ⟨a, ledger, clock⟩, run.last.cursor = b
  | a, _, .nil _, ledger, clock =>
      ⟨Step.Run.nil (P := storeStep rules) (Store.mk a ledger clock), rfl⟩
  | a, _, .forward (middle := middle) step rest, ledger, clock =>
      (store_run_of_zigzag rest
        (ledger ++ [((a, middle) : Expr Base Const × Expr Base Const)]) (clock + 1)).elim
        fun run ends =>
        ⟨Step.Run.cons (P := storeStep rules) (s := Store.mk a ledger clock)
          (Move.forward middle (PLift.down step))
          (admits_forward (store := Store.mk a ledger clock) middle (PLift.down step)) run, ends⟩
  | a, _, .backward (middle := middle) step rest, ledger, clock =>
      (store_run_of_zigzag rest
        (ledger ++ [((a, middle) : Expr Base Const × Expr Base Const)]) (clock + 1)).elim
        fun run ends =>
        ⟨Step.Run.cons (P := storeStep rules) (s := Store.mk a ledger clock)
          (Move.backward middle (PLift.down step))
          (admits_backward (store := Store.mk a ledger clock) middle (PLift.down step)) run, ends⟩

/-- **Completeness inside the bubble.** Every conversion of the bubble is reached by a run of the
store, from any ledger. -/
theorem store_complete {a b : Expr Base Const} (converted : Convertible rules a b)
    (ledger : EquationStore (Expr Base Const)) (clock : Nat) :
    ∃ run : (storeStep rules).Run ⟨a, ledger, clock⟩, run.last.cursor = b :=
  (convertible_iff_conv.mp converted).elim fun path =>
    store_run_of_zigzag (Zigzag.ofConv path) ledger clock

/-- **The store reaches exactly the bubble's conversion.** With lookups admitted, the expressions
reachable from the empty ledger are those the bubble converts. -/
theorem store_reaches_iff {a b : Expr Base Const} :
    (∃ run : (storeStep rules).Run ⟨a, [], 0⟩, run.last.cursor = b) ↔ Convertible rules a b := by
  constructor
  · rintro ⟨run, ends⟩
    subst ends
    exact (store_run_sound run (fun _ member => absurd member List.not_mem_nil)).1
  · exact fun converted => store_complete converted [] 0

end Core

/-! ## Controls -/

namespace Controls

open Mettapedia.TypeTheory.BubbleConversion.Arith

/-- The store at `Vec (n + 0)` that has learnt `n + 0 ≐ n`. -/
def learned : Store Unit ArithConst :=
  ⟨vec (addE (bvar 1) zeroE), [(addE (bvar 1) zeroE, bvar 1)], 1⟩

theorem learned_knows :
    Convertible (assumed learned.ledger) (addE (bvar 1) zeroE) (bvar 1) :=
  Relation.EqvGen.rel _ _
    (Rewrite.root (show assumed learned.ledger (addE (bvar 1) zeroE) (bvar 1) from
      List.mem_singleton_self _))

/-- **The lookup from `Vec (n + 0)` to `Vec n` is admitted.** -/
theorem lookup_admitted :
    (storeStep Rule).Admits (Move.lookup (vec (bvar 1)) : Move Rule learned.cursor) :=
  lookup_admitted_under (fun x => vec x) (fun step => Rewrite.appArgument step) learned_knows 1

/-- **Two formers deep, by the same told equation**: the lookup from `Π (_ : Vec (n + 0)). nat` to
`Π (_ : Vec n). nat` is admitted. -/
theorem deep_lookup_admitted :
    (storeStep Rule).Admits
      (Move.lookup (Expr.pi (vec (bvar 1)) natType) :
        Move Rule (Store.mk (Expr.pi (vec (addE (bvar 1) zeroE)) natType) learned.ledger 1).cursor) :=
  lookup_admitted_under (fun x => Expr.pi (vec x) natType)
    (fun step => Rewrite.piDomain (Rewrite.appArgument step)) learned_knows 1

/-- **With nothing learnt the lookup is refused.** -/
theorem lookup_refused_unlearned :
    ¬ (storeStep Rule).Admits
      (Move.lookup (vec (bvar 1)) : Move Rule (Store.mk (vec (addE (bvar 1) zeroE)) [] 0).cursor) := by
  intro admitted
  have converted :=
    (admits_lookup_iff (store := Store.mk (vec (addE (bvar 1) zeroE)) [] 0) (vec (bvar 1))).mp
      admitted
  have same : vec (addE (bvar 1) zeroE) = vec (bvar 1) :=
    convertible_none_iff.mp
      (convertible_mono (fun _ _ member => absurd member List.not_mem_nil) converted)
  simp [vec, addE] at same

/-- **A lookup the knowledge does not entail is refused**: `Vec (0 + n)` to `Vec n`, with
`n + 0 ≐ n` known. -/
theorem wrong_lookup_refused :
    ¬ (storeStep Rule).Admits
      (Move.lookup (vec (bvar 1)) :
        Move Rule (Store.mk (vec (addE zeroE (bvar 1))) learned.ledger 1).cursor) := by
  intro admitted
  have converted :=
    (admits_lookup_iff (store := Store.mk (vec (addE zeroE (bvar 1))) learned.ledger 1)
      (vec (bvar 1))).mp admitted
  have same : Arith.norm false (vec (addE zeroE (bvar 1))) = Arith.norm false (vec (bvar 1)) :=
    rel_of_convertible (θ := ArithControl.normModel false)
      (mem_models_assumed.mpr (by
        intro e member
        have single : e ∈ [((addE (bvar 1) zeroE, bvar 1) : AExpr × AExpr)] := member
        obtain rfl := List.mem_singleton.mp single
        rfl))
      converted
  simp [Arith.norm, appNorm, addNorm, vec, addE, zeroE] at same

end Controls

/-! ## Axiom audit -/

#print axioms storeStep
#print axioms admits_lookup_iff
#print axioms lookup_admitted_under
#print axioms store_run_sound
#print axioms ledger_grows
#print axioms store_complete
#print axioms store_reaches_iff
#print axioms Controls.lookup_admitted
#print axioms Controls.deep_lookup_admitted
#print axioms Controls.lookup_refused_unlearned
#print axioms Controls.wrong_lookup_refused

end Mettapedia.TypeTheory.ConversionStoreCore
