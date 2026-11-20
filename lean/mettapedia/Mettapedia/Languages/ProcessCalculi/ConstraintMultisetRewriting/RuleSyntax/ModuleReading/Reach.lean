import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading.Runs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading.Functional
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading.Print

/-!
# Control: reachability over a cyclic relation

The module `tests/tcalc/modules/reach.module` of CeTTa:

    reach-edge. edge(x, y)                 |- n:reach(x) ~> y
    reach-step. edge(x, y), n:reach(y) ~> z |- n:reach(x) ~> z

with the rows `a -> b`, `b -> c`, `c -> d`, `d -> b` and the call `reach(a)`.

* Faithfulness: the Lean reading has the six rules the library prints, rule by rule
  (`reading_rules`), and prints to the library's text exactly (`reading_text`, by `decide`).
* The closure holds the values `b`, `c`, `d` of `reach(a)` and no other (`reach_a_values`), and the
  demands `reach(a) .. reach(d)` and no other: the cycle `d -> b` asks `reach(b)` again, one row
  (`demand_rows`). Disciplined runs end, with those values (`reach_runs`).
* The module is range-restricted (`rangeRestricted`), so T0 and T1 apply. It is not exclusive
  (`not_exclusive`: both rules hold at `reach(a)`), and a query binds a new variable
  (`not_queriesBound`): T2's licence fails twice, and `reach(a)` has three values.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading.Reach

open Mettapedia.Logic.LP (LPSignature Term Atom Subst)
open SetStoreSyntax (consequence Discipline DisciplinedStep TerminalWith)

/-! ## The module -/

/-- The constructors `n:a`, `n:b`, `n:c`, `n:d`, `n:reach`. -/
inductive Con where
  | a | b | c | d | reach
  deriving DecidableEq

def Con.arity : Con → ℕ
  | .reach => 1
  | _ => 0

/-- The relation `edge`. -/
inductive RelSym where
  | edge
  deriving DecidableEq

def RelSym.arity : RelSym → ℕ
  | .edge => 2

/-- The rules `reach-edge` and `reach-step`. -/
inductive Label where
  | edge | step
  deriving DecidableEq

instance : Fintype Label := ⟨{.edge, .step}, fun l => by cases l <;> simp⟩

/-- No constants (the module's nodes are constructors of arity zero), variables numbered. -/
abbrev σ : LPSignature.{0, 0, 0, 0} := ⟨Empty, ℕ, RelSym, RelSym.arity, Con, Con.arity⟩

abbrev T := Term (readingSignature σ Label)

def a : T := .app (Head.con Con.a) ![]
def b : T := .app (Head.con Con.b) ![]
def c : T := .app (Head.con Con.c) ![]
def d : T := .app (Head.con Con.d) ![]
def reach (t : T) : T := .app (Head.con Con.reach) ![t]
def edge (s t : T) : Atom (readingSignature σ Label) := ⟨RelSym.edge, ![s, t]⟩
def x : T := .var 0
def y : T := .var 1
def z : T := .var 2

/-- The module. -/
def module : Label → ModuleRule (readingSignature σ Label)
  | .edge => ⟨reach x, [.query (edge x y)], y⟩
  | .step => ⟨reach x, [.query (edge x y), .call (reach y) z], z⟩

/-- The rows `a -> b`, `b -> c`, `c -> d`, `d -> b`. -/
def rows : Finset (Atom (readingSignature σ Label)) := {edge a b, edge b c, edge c d, edge d b}

/-! ## Faithfulness to the library -/

/-- The library's names. -/
def names : Names σ Label where
  con := fun | .a => "n:a" | .b => "n:b" | .c => "n:c" | .d => "n:d" | .reach => "n:reach"
  rel := fun | .edge => "edge"
  const := fun e => nomatch e
  var := fun | 0 => "x" | 1 => "y" | 2 => "z" | n => "v" ++ toString n
  label := fun | .edge => "reach-edge" | .step => "reach-step"

/-- **The reading, rule by rule**: `reach-edge/1`, `reach-edge`, `reach-step/1`, `reach-step/2.ask`,
`reach-step/2`, `reach-step`. -/
theorem reading_rules : (readingList module [.edge, .step]).map Prod.snd =
    [makeRule [demandRow (reach x), atomRow (edge x y)] [stageRow .edge (reach x) [atomRow (edge x y)]],
     makeRule [stageRow .edge (reach x) [atomRow (edge x y)]] [valueRow (reach x) y],
     makeRule [demandRow (reach x), atomRow (edge x y)] [stageRow .step (reach x) [atomRow (edge x y)]],
     makeRule [stageRow .step (reach x) [atomRow (edge x y)]] [demandRow (reach y)],
     makeRule [stageRow .step (reach x) [atomRow (edge x y)], valueRow (reach y) z]
       [stageRow .step (reach x) [atomRow (edge x y), z]],
     makeRule [stageRow .step (reach x) [atomRow (edge x y), z]] [valueRow (reach x) z]] := rfl

#eval IO.print (readingText names module [.edge, .step])

/-- **The reading prints as the library's** `tcalc:module-text` of `reach.module` (its rule lines). -/
theorem reading_text : readingText names module [.edge, .step] =
    "(rule reach-edge/1 (read (demand (n:reach $x)) (edge $x $y)) (make (reach-edge/1 (n:reach $x) (edge $x $y))))\n" ++
    "(rule reach-edge (read (reach-edge/1 (n:reach $x) (edge $x $y))) (make (value (n:reach $x) $y)))\n" ++
    "(rule reach-step/1 (read (demand (n:reach $x)) (edge $x $y)) (make (reach-step/1 (n:reach $x) (edge $x $y))))\n" ++
    "(rule reach-step/2.ask (read (reach-step/1 (n:reach $x) (edge $x $y))) (make (demand (n:reach $y))))\n" ++
    "(rule reach-step/2 (read (reach-step/1 (n:reach $x) (edge $x $y)) (value (n:reach $y) $z)) (make (reach-step/2 (n:reach $x) (edge $x $y) $z)))\n" ++
    "(rule reach-step (read (reach-step/2 (n:reach $x) (edge $x $y) $z)) (make (value (n:reach $x) $z)))\n" := by
  decide +kernel

/-! ## Terms under substitution -/

/-- Three values for `x`, `y`, `z`. -/
def sub (p q r : T) : Subst (readingSignature σ Label) := fun
  | 0 => p
  | 1 => q
  | _ => r

theorem app_nullary {n : Con} (zero : Con.arity n = 0) (args args' : Fin (Con.arity n) → T) :
    Term.app (σ := readingSignature σ Label) (Head.con n) args = Term.app (Head.con n) args' := by
  congr 1
  funext i
  exact absurd i.2 (by omega)

theorem apply_a (θ : Subst (readingSignature σ Label)) : θ.applyTerm a = a := app_nullary rfl _ _
theorem apply_b (θ : Subst (readingSignature σ Label)) : θ.applyTerm b = b := app_nullary rfl _ _
theorem apply_c (θ : Subst (readingSignature σ Label)) : θ.applyTerm c = c := app_nullary rfl _ _
theorem apply_d (θ : Subst (readingSignature σ Label)) : θ.applyTerm d = d := app_nullary rfl _ _

theorem apply_reach (θ : Subst (readingSignature σ Label)) (t : T) :
    θ.applyTerm (reach t) = reach (θ.applyTerm t) := by
  show Term.app (σ := readingSignature σ Label) (Head.con Con.reach) (fun i : Fin 1 => θ.applyTerm (![t] i)) =
    Term.app (Head.con Con.reach) ![θ.applyTerm t]
  congr 1
  funext i
  obtain ⟨k, bound⟩ := i
  obtain rfl : k = 0 := by omega
  rfl

theorem applyAtom_edge (θ : Subst (readingSignature σ Label)) (s t : T) :
    θ.applyAtom (edge s t) = edge (θ.applyTerm s) (θ.applyTerm t) := by
  show (⟨RelSym.edge, fun i : Fin 2 => θ.applyTerm (![s, t] i)⟩ : Atom (readingSignature σ Label)) =
    ⟨RelSym.edge, ![θ.applyTerm s, θ.applyTerm t]⟩
  congr 1
  funext i
  obtain ⟨k, bound⟩ := i
  rcases k with _ | _ | k
  · rfl
  · rfl
  · omega

theorem edge_inj {s t s' t' : T} : edge s t = edge s' t' ↔ s = s' ∧ t = t' := by
  constructor
  · intro same
    have args := eq_of_heq (Atom.mk.inj same).2
    exact ⟨congrFun args 0, congrFun args 1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem reach_inj {t t' : T} (same : reach t = reach t') : t = t' :=
  congrFun (eq_of_heq (Term.app.inj same).2) 0

theorem b_ne_c : b ≠ c := fun same => by
  have heads := Head.con.inj (Term.app.inj same).1
  cases heads

theorem mem_rows {s t : T} :
    edge s t ∈ rows ↔ (s = a ∧ t = b) ∨ (s = b ∧ t = c) ∨ (s = c ∧ t = d) ∨ (s = d ∧ t = b) := by
  simp only [rows, Finset.mem_insert, Finset.mem_singleton, edge_inj]

theorem freeVars_reach (t : T) : (reach t).freeVars = t.freeVars := by
  change (Finset.univ : Finset (Fin 1)).biUnion (fun i => (![t] i).freeVars) = t.freeVars
  simp

theorem freeVars_edge (s t : T) : (edge s t).freeVars = s.freeVars ∪ t.freeVars := by
  change (Finset.univ : Finset (Fin 2)).biUnion (fun i => (![s, t] i).freeVars) = s.freeVars ∪ t.freeVars
  ext v
  simp [Fin.exists_fin_two]

theorem node_ground {n : Con} (zero : Con.arity n = 0) (args : Fin (Con.arity n) → T) :
    (Term.app (σ := readingSignature σ Label) (Head.con n) args).isGround :=
  fun i => absurd i.2 (by change ¬ (i : ℕ) < Con.arity n; omega)

theorem reach_ground {t : T} (ground : t.isGround) : (reach t).isGround := by
  intro i
  obtain ⟨k, bound⟩ := i
  obtain rfl : k = 0 := by change k < 1 at bound; omega
  exact ground

theorem edge_ground {s t : T} (groundS : s.isGround) (groundT : t.isGround) : (edge s t).isGround := by
  intro i
  obtain ⟨k, bound⟩ := i
  rcases k with _ | _ | k
  · exact groundS
  · exact groundT
  · change k + 2 < 2 at bound
    omega

theorem ground : (reach a).isGround := reach_ground (node_ground rfl _)

theorem rows_ground : ∀ e ∈ rows, e.isGround := by
  intro e inside
  simp only [rows, Finset.mem_insert, Finset.mem_singleton] at inside
  rcases inside with rfl | rfl | rfl | rfl <;>
    exact edge_ground (node_ground rfl _) (node_ground rfl _)

/-! ## The hypotheses -/

/-- The module is range-restricted: T0 and T1 apply. -/
theorem rangeRestricted : ∀ l, RangeRestricted (module l) := by
  intro l
  apply (rangeRestricted_iff_boundOk (module l)).mpr
  cases l <;> simp [BoundOk, module, freeVars_reach, freeVars_edge, x, y, z, Term.freeVars]

/-- `reach-edge`'s query binds `y`. -/
theorem not_queriesBound : ¬ QueriesBound (module .edge) := by
  intro bounded
  have inside := bounded [] (edge x y) [] rfl
  have one : (1 : ℕ) ∈ (module .edge).bound [] :=
    inside (by rw [freeVars_edge]; simp [y, Term.freeVars])
  simp [ModuleRule.bound, module, freeVars_reach, x, Term.freeVars, bindsAll] at one

theorem holds_edge {s t : T} (member : edge s t ∈ rows) :
    ∀ p ∈ (module .edge).premises, Holds module ↑rows (sub s t t) p := by
  intro p inside
  simp only [module, List.mem_singleton] at inside
  subst inside
  show (sub s t t).applyAtom (edge x y) ∈ (↑rows : Set (Atom (readingSignature σ Label)))
  rw [applyAtom_edge]
  exact Finset.mem_coe.mpr member

theorem holds_step {s m t : T} (member : edge s m ∈ rows) (next : Derives module ↑rows (reach m) t) :
    ∀ p ∈ (module .step).premises, Holds module ↑rows (sub s m t) p := by
  intro p inside
  simp only [module, List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with rfl | rfl
  · show (sub s m t).applyAtom (edge x y) ∈ (↑rows : Set (Atom (readingSignature σ Label)))
    rw [applyAtom_edge]
    exact Finset.mem_coe.mpr member
  · show Derives module ↑rows ((sub s m t).applyTerm (reach y)) ((sub s m t).applyTerm z)
    rw [apply_reach]
    exact next

theorem derives_edge {s t : T} (member : edge s t ∈ rows) : Derives module ↑rows (reach s) t :=
  derives_iff.mpr ⟨.edge, sub s t t, (apply_reach (sub s t t) x).symm, rfl, holds_edge member⟩

theorem derives_step {s m t : T} (member : edge s m ∈ rows) (next : Derives module ↑rows (reach m) t) :
    Derives module ↑rows (reach s) t :=
  derives_iff.mpr ⟨.step, sub s m t, (apply_reach (sub s m t) x).symm, rfl, holds_step member next⟩

theorem edge_ab : edge a b ∈ rows := mem_rows.mpr (Or.inl ⟨rfl, rfl⟩)
theorem edge_bc : edge b c ∈ rows := mem_rows.mpr (Or.inr (Or.inl ⟨rfl, rfl⟩))
theorem edge_cd : edge c d ∈ rows := mem_rows.mpr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩)))
theorem edge_db : edge d b ∈ rows := mem_rows.mpr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))

/-- Both rules hold at `reach(a)`: the module is not exclusive. -/
theorem not_exclusive : ¬ Exclusive module ↑rows := fun exclusive =>
  exclusive .edge .step (sub a b b) (sub a b c) (by decide)
    ((apply_reach (sub a b b) x).trans (apply_reach (sub a b c) x).symm) (holds_edge edge_ab)
    (holds_step edge_ab (derives_edge edge_bc))

/-! ## Values and demands -/

/-- Every value is `b`, `c` or `d`: the target of an edge, or a value of a further call. -/
theorem values_of_derives {C w : T} (derives : Derives module ↑rows C w) : w = b ∨ w = c ∨ w = d := by
  induction derives with
  | rule l θ calls queries ih =>
    cases l with
    | edge =>
      have row := queries (edge x y) (by simp [module])
      rw [applyAtom_edge, Finset.mem_coe, mem_rows] at row
      show θ.applyTerm y = b ∨ θ.applyTerm y = c ∨ θ.applyTerm y = d
      rcases row with ⟨_, same⟩ | ⟨_, same⟩ | ⟨_, same⟩ | ⟨_, same⟩ <;> simp [same]
    | step => exact ih (reach y) z (by simp [module])

theorem derives_iff_reach_a (w : T) : Derives module ↑rows (reach a) w ↔ w = b ∨ w = c ∨ w = d := by
  constructor
  · exact values_of_derives
  · rintro (rfl | rfl | rfl)
    · exact derives_edge edge_ab
    · exact derives_step edge_ab (derives_edge edge_bc)
    · exact derives_step edge_ab (derives_step edge_bc (derives_edge edge_cd))

theorem demanded_reach {C : T} (demanded : Demanded module ↑rows (reach a) C) :
    C = reach a ∨ C = reach b ∨ C = reach c ∨ C = reach d := by
  induction demanded with
  | seed => exact Or.inl rfl
  | @call l θ pre post source target _ split holds _ =>
    cases l with
    | edge => rcases pre with _ | ⟨p, _ | ⟨q, pre⟩⟩ <;> simp [module] at split
    | step =>
      rcases pre with _ | ⟨p, _ | ⟨q, pre⟩⟩
      · simp [module] at split
      · simp only [module, List.cons_append, List.nil_append, List.cons.injEq, Premise.call.injEq] at split
        obtain ⟨rfl, ⟨rfl, rfl⟩, -⟩ := split
        have row := holds _ List.mem_cons_self
        change θ.applyAtom (edge x y) ∈ (↑rows : Set (Atom (readingSignature σ Label))) at row
        rw [applyAtom_edge, Finset.mem_coe, mem_rows] at row
        rw [apply_reach]
        rcases row with ⟨_, same⟩ | ⟨_, same⟩ | ⟨_, same⟩ | ⟨_, same⟩ <;> simp [same]
      · simp [module] at split

theorem demanded_next {s t : T} (asked : Demanded module ↑rows (reach a) (reach s)) (member : edge s t ∈ rows) :
    Demanded module ↑rows (reach a) (reach t) := by
  have next := Demanded.call (M := module) (Rel := ↑rows) (C₀ := reach a) (l := .step) (θ := sub s t t)
    (pre := [.query (edge x y)]) (post := []) (source := reach y) (target := z)
    (by rw [show (module .step).lhs = reach x from rfl, apply_reach]; exact asked) rfl
    (fun p inside => holds_edge member p inside)
  rwa [apply_reach] at next

/-- The demanded calls: `reach(a)` and, through the edges, `reach(b)`, `reach(c)`, `reach(d)`; the
cycle `d -> b` asks `reach(b)` again. -/
theorem demanded_iff (C : T) :
    Demanded module ↑rows (reach a) C ↔ C = reach a ∨ C = reach b ∨ C = reach c ∨ C = reach d := by
  refine ⟨demanded_reach, ?_⟩
  have ab := demanded_next .seed edge_ab
  have bc := demanded_next ab edge_bc
  have cd := demanded_next bc edge_cd
  rintro (rfl | rfl | rfl | rfl)
  exacts [.seed, ab, bc, cd]

/-! ## The closure and the runs -/

/-- **`reach(a)`'s values in the closure are exactly `b`, `c`, `d`.** -/
theorem reach_a_values (w : T) :
    valueRow (reach a) w ∈ SetStoreClosure.closure (consequence (P := reading module)) (seed (reach a) rows) ↔
      w = b ∨ w = c ∨ w = d := by
  rw [valueRow_mem_closure_iff rangeRestricted ground rows_ground, derives_iff_reach_a]
  exact ⟨fun both => both.2, fun values => ⟨.seed, values⟩⟩

/-- **The closure's demands are exactly `reach(a) .. reach(d)`**, the cycle included once. -/
theorem demand_rows (C : T) :
    demandRow C ∈ SetStoreClosure.closure (consequence (P := reading module)) (seed (reach a) rows) ↔
      C = reach a ∨ C = reach b ∨ C = reach c ∨ C = reach d := by
  rw [demandRow_mem_closure_iff rangeRestricted ground rows_ground]
  exact demanded_iff C

/-- T2's conclusion fails here: `reach(a)` has two different values in the closure. -/
theorem two_values :
    valueRow (reach a) b ∈ SetStoreClosure.closure (consequence (P := reading module)) (seed (reach a) rows) ∧
      valueRow (reach a) c ∈ SetStoreClosure.closure (consequence (P := reading module)) (seed (reach a) rows) ∧
      b ≠ c :=
  ⟨(reach_a_values b).mpr (Or.inl rfl), (reach_a_values c).mpr (Or.inr (Or.inl rfl)), b_ne_c⟩

theorem demands_finite : {C | Demanded module ↑rows (reach a) C}.Finite := by
  apply ((((Set.finite_singleton (reach d)).insert (reach c)).insert (reach b)).insert (reach a)).subset
  intro C demanded
  simpa using demanded_reach demanded

theorem values_finite (C : T) : {w | Derives module ↑rows C w}.Finite := by
  apply (((Set.finite_singleton d).insert c).insert b).subset
  intro w derives
  simpa using values_of_derives derives

/-- **Every discipline but `unique` has a terminal run**, and it holds exactly the values `b`, `c`, `d`
of `reach(a)`. -/
theorem reach_runs (discipline : Discipline) (notUnique : discipline ≠ .unique) (timing : SetStore.AskTiming) :
    ∃ after, Relation.ReflTransGen (DisciplinedStep discipline timing (reading module)) (seed (reach a) rows) after ∧
      TerminalWith discipline timing (reading module) after ∧
      ∀ w, valueRow (reach a) w ∈ after ↔ w = b ∨ w = c ∨ w = d := by
  obtain ⟨after, run, terminal, -, values⟩ := exists_terminal_run_rows (Equiv.refl ℕ) discipline timing
    rangeRestricted ground rows_ground demands_finite (fun C _ => values_finite C)
    (fun unique => absurd unique notUnique)
  refine ⟨after, run, terminal, fun w => ?_⟩
  rw [values, derives_iff_reach_a]
  exact ⟨fun both => both.2, fun inside => ⟨.seed, inside⟩⟩

#print axioms reading_rules
#print axioms reading_text
#print axioms rangeRestricted
#print axioms not_queriesBound
#print axioms not_exclusive
#print axioms values_of_derives
#print axioms derives_iff_reach_a
#print axioms demanded_iff
#print axioms reach_a_values
#print axioms demand_rows
#print axioms two_values
#print axioms reach_runs

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading.Reach
