import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading.Functional
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading.Print

/-!
# Control for T2: an exclusive module, where every call has exactly one value

The order combinator of the lambda module (`then-lt`, `then-eq`, `then-gt`) and a lexicographic
combination of three comparisons through two calls:

    then-lt. |- o:then(o:lt, o) ~> o:lt
    then-eq. |- o:then(o:eq, o) ~> o
    then-gt. |- o:then(o:gt, o) ~> o:gt
    lex3.    o:then(o2, o3) ~> r1, o:then(o1, r1) ~> r2 |- o:lex(o1, o2, o3) ~> r2

Every hypothesis of T2 holds (`rangeRestricted`, `queriesBound`, `exclusive`). From the call
`lex(eq, gt, lt)` the demanded calls are `lex(eq, gt, lt)`, `then(gt, lt)`, `then(eq, gt)`
(`demanded_iff`), and each has exactly one value row in the closure (`exactly_one_value`).
The reading prints as the library's for the same module (`reading_text`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading.Order

open Mettapedia.Logic.LP (LPSignature Term Atom Subst)
open SetStoreSyntax (consequence)

/-- The constructors `o:lt`, `o:eq`, `o:gt`, `o:then`, `o:lex`. -/
inductive Con where
  | lt | eq | gt | then | lex
  deriving DecidableEq

def Con.arity : Con → ℕ
  | .then => 2
  | .lex => 3
  | _ => 0

/-- The rules. -/
inductive Label where
  | thenLt | thenEq | thenGt | lex
  deriving DecidableEq

abbrev σ : LPSignature.{0, 0, 0, 0} := ⟨Empty, ℕ, Empty, (fun e => nomatch e), Con, Con.arity⟩

abbrev T := Term (readingSignature σ Label)

def lt : T := .app (Head.con Con.lt) ![]
def eq : T := .app (Head.con Con.eq) ![]
def gt : T := .app (Head.con Con.gt) ![]
def «then» (s t : T) : T := .app (Head.con Con.then) ![s, t]
def lex (p q r : T) : T := .app (Head.con Con.lex) ![p, q, r]

/-- `lex3`'s variables `o1 o2 o3 r1 r2` are `0 .. 4`; the `then` rules' `o` is `5`. -/
def v (n : ℕ) : T := .var n

def module : Label → ModuleRule (readingSignature σ Label)
  | .thenLt => ⟨«then» lt (v 5), [], lt⟩
  | .thenEq => ⟨«then» eq (v 5), [], v 5⟩
  | .thenGt => ⟨«then» gt (v 5), [], gt⟩
  | .lex => ⟨lex (v 0) (v 1) (v 2), [.call («then» (v 1) (v 2)) (v 3), .call («then» (v 0) (v 3)) (v 4)], v 4⟩

def rows : Finset (Atom (readingSignature σ Label)) := ∅

/-! ## Faithfulness to the library -/

def names : Names σ Label where
  con := fun | .lt => "o:lt" | .eq => "o:eq" | .gt => "o:gt" | .then => "o:then" | .lex => "o:lex"
  rel := fun e => nomatch e
  const := fun e => nomatch e
  var := fun | 0 => "o1" | 1 => "o2" | 2 => "o3" | 3 => "r1" | 4 => "r2" | 5 => "o" | n => "v" ++ toString n
  label := fun | .thenLt => "then-lt" | .thenEq => "then-eq" | .thenGt => "then-gt" | .lex => "lex3"

/-- **The reading prints as the library's** `tcalc:module-text` of the same module. -/
theorem reading_text : readingText names module [.thenLt, .thenEq, .thenGt, .lex] =
    "(rule then-lt (read (demand (o:then (o:lt) $o))) (make (value (o:then (o:lt) $o) (o:lt))))\n" ++
    "(rule then-eq (read (demand (o:then (o:eq) $o))) (make (value (o:then (o:eq) $o) $o)))\n" ++
    "(rule then-gt (read (demand (o:then (o:gt) $o))) (make (value (o:then (o:gt) $o) (o:gt))))\n" ++
    "(rule lex3/1.ask (read (demand (o:lex $o1 $o2 $o3))) (make (demand (o:then $o2 $o3))))\n" ++
    "(rule lex3/1 (read (demand (o:lex $o1 $o2 $o3)) (value (o:then $o2 $o3) $r1)) (make (lex3/1 (o:lex $o1 $o2 $o3) $r1)))\n" ++
    "(rule lex3/2.ask (read (lex3/1 (o:lex $o1 $o2 $o3) $r1)) (make (demand (o:then $o1 $r1))))\n" ++
    "(rule lex3/2 (read (lex3/1 (o:lex $o1 $o2 $o3) $r1) (value (o:then $o1 $r1) $r2)) (make (lex3/2 (o:lex $o1 $o2 $o3) $r1 $r2)))\n" ++
    "(rule lex3 (read (lex3/2 (o:lex $o1 $o2 $o3) $r1 $r2)) (make (value (o:lex $o1 $o2 $o3) $r2)))\n" := by
  decide +kernel

/-! ## Terms -/

theorem apply_nullary {n : Con} (zero : Con.arity n = 0) (θ : Subst (readingSignature σ Label))
    (args : Fin (Con.arity n) → T) :
    θ.applyTerm (Term.app (σ := readingSignature σ Label) (Head.con n) args) = Term.app (Head.con n) args := by
  show Term.app (σ := readingSignature σ Label) (Head.con n) (fun i : Fin (Con.arity n) => θ.applyTerm (args i)) =
    Term.app (Head.con n) args
  congr 1
  funext i
  exact absurd i.2 (by omega)

theorem apply_lt (θ : Subst (readingSignature σ Label)) : θ.applyTerm lt = lt := apply_nullary rfl θ _
theorem apply_eq (θ : Subst (readingSignature σ Label)) : θ.applyTerm eq = eq := apply_nullary rfl θ _
theorem apply_gt (θ : Subst (readingSignature σ Label)) : θ.applyTerm gt = gt := apply_nullary rfl θ _

theorem apply_then (θ : Subst (readingSignature σ Label)) (s t : T) :
    θ.applyTerm («then» s t) = «then» (θ.applyTerm s) (θ.applyTerm t) := by
  show Term.app (σ := readingSignature σ Label) (Head.con Con.then) (fun i : Fin 2 => θ.applyTerm (![s, t] i)) =
    Term.app (Head.con Con.then) ![θ.applyTerm s, θ.applyTerm t]
  congr 1
  funext i
  obtain ⟨k, bound⟩ := i
  rcases k with _ | _ | k
  · rfl
  · rfl
  · omega

theorem apply_lex (θ : Subst (readingSignature σ Label)) (p q r : T) :
    θ.applyTerm (lex p q r) = lex (θ.applyTerm p) (θ.applyTerm q) (θ.applyTerm r) := by
  show Term.app (σ := readingSignature σ Label) (Head.con Con.lex) (fun i : Fin 3 => θ.applyTerm (![p, q, r] i)) =
    Term.app (Head.con Con.lex) ![θ.applyTerm p, θ.applyTerm q, θ.applyTerm r]
  congr 1
  funext i
  obtain ⟨k, bound⟩ := i
  rcases k with _ | _ | _ | k
  · rfl
  · rfl
  · rfl
  · omega

theorem then_inj {s t s' t' : T} : «then» s t = «then» s' t' ↔ s = s' ∧ t = t' := by
  constructor
  · intro same
    have args := eq_of_heq (Term.app.inj same).2
    exact ⟨congrFun args 0, congrFun args 1⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem lex_inj {p q r p' q' r' : T} : lex p q r = lex p' q' r' ↔ p = p' ∧ q = q' ∧ r = r' := by
  constructor
  · intro same
    have args := eq_of_heq (Term.app.inj same).2
    exact ⟨congrFun args 0, congrFun args 1, congrFun args 2⟩
  · rintro ⟨rfl, rfl, rfl⟩
    rfl

theorem then_ne_lex (s t p q r : T) : «then» s t ≠ lex p q r := fun same => by
  have heads := Head.con.inj (Term.app.inj same).1
  cases heads

theorem lex_ne_then (p q r s t : T) : lex p q r ≠ «then» s t := fun same => then_ne_lex s t p q r same.symm

theorem lt_ne_eq : lt ≠ eq := fun same => by
  have heads := Head.con.inj (Term.app.inj same).1
  cases heads

theorem lt_ne_gt : lt ≠ gt := fun same => by
  have heads := Head.con.inj (Term.app.inj same).1
  cases heads

theorem eq_ne_gt : eq ≠ gt := fun same => by
  have heads := Head.con.inj (Term.app.inj same).1
  cases heads

theorem freeVars_nullary {n : Con} (zero : Con.arity n = 0) (args : Fin (Con.arity n) → T) :
    (Term.app (σ := readingSignature σ Label) (Head.con n) args).freeVars = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro w inside
  simp only [Term.freeVars, Finset.mem_biUnion] at inside
  obtain ⟨i, _, _⟩ := inside
  exact absurd i.2 (by change ¬ (i : ℕ) < Con.arity n; omega)

theorem freeVars_then (s t : T) : («then» s t).freeVars = s.freeVars ∪ t.freeVars := by
  change (Finset.univ : Finset (Fin 2)).biUnion (fun i => (![s, t] i).freeVars) = s.freeVars ∪ t.freeVars
  ext w
  simp [Fin.exists_fin_two]

theorem freeVars_lex (p q r : T) : (lex p q r).freeVars = p.freeVars ∪ q.freeVars ∪ r.freeVars := by
  change (Finset.univ : Finset (Fin 3)).biUnion (fun i => (![p, q, r] i).freeVars) = _
  ext w
  simp [Fin.exists_fin_succ]

theorem freeVars_lt : lt.freeVars = ∅ := freeVars_nullary rfl _
theorem freeVars_gt : gt.freeVars = ∅ := freeVars_nullary rfl _
theorem freeVars_eq : eq.freeVars = ∅ := freeVars_nullary rfl _

/-! ## T2's hypotheses hold -/

theorem rangeRestricted : ∀ l, RangeRestricted (module l) := by
  intro l
  apply (rangeRestricted_iff_boundOk (module l)).mpr
  cases l <;>
    simp [BoundOk, module, freeVars_then, freeVars_lex, freeVars_lt, freeVars_eq, freeVars_gt, v, Term.freeVars]

theorem queriesBound : ∀ l, QueriesBound (module l) := by
  intro l pre atom post split
  have inside : Premise.query atom ∈ (module l).premises := by
    rw [split]
    exact List.mem_append_right _ List.mem_cons_self
  cases l <;> simp [module] at inside

/-- Different rules' left sides have no common instance: the module is exclusive. -/
theorem exclusive : Exclusive module ↑rows := by
  apply exclusive_of_apart
  intro l₁ l₂ θ₁ θ₂ different same
  cases l₁ <;> cases l₂ <;>
    first
    | exact different rfl
    | simp [module, apply_then, apply_lex, apply_lt, apply_eq, apply_gt, then_inj, then_ne_lex,
        lex_ne_then, lt_ne_eq, lt_ne_gt, eq_ne_gt, lt_ne_eq.symm, lt_ne_gt.symm, eq_ne_gt.symm] at same

/-! ## Values -/

/-- Values for the variables `0 .. 5`. -/
def sub (values : List T) : Subst (readingSignature σ Label) := fun n => values.getD n lt

theorem derives_thenGt (t : T) : Derives module ↑rows («then» gt t) gt :=
  derives_iff.mpr ⟨.thenGt, sub [lt, lt, lt, lt, lt, t],
    by rw [show (module .thenGt).lhs = «then» gt (v 5) from rfl, apply_then, apply_gt]; rfl,
    (apply_gt _).symm, fun _ inside => by simp [module] at inside⟩

theorem derives_thenEq (t : T) : Derives module ↑rows («then» eq t) t :=
  derives_iff.mpr ⟨.thenEq, sub [lt, lt, lt, lt, lt, t],
    by rw [show (module .thenEq).lhs = «then» eq (v 5) from rfl, apply_then, apply_eq]; rfl,
    rfl, fun _ inside => by simp [module] at inside⟩

theorem derives_lex : Derives module ↑rows (lex eq gt lt) gt := by
  refine derives_iff.mpr ⟨.lex, sub [eq, gt, lt, gt, gt],
    by rw [show (module .lex).lhs = lex (v 0) (v 1) (v 2) from rfl, apply_lex]; rfl, rfl, ?_⟩
  intro p inside
  simp only [module, List.mem_cons, List.not_mem_nil, or_false] at inside
  rcases inside with rfl | rfl
  · show Derives module ↑rows ((sub [eq, gt, lt, gt, gt]).applyTerm («then» (v 1) (v 2)))
      ((sub [eq, gt, lt, gt, gt]).applyTerm (v 3))
    rw [apply_then]
    exact derives_thenGt lt
  · show Derives module ↑rows ((sub [eq, gt, lt, gt, gt]).applyTerm («then» (v 0) (v 3)))
      ((sub [eq, gt, lt, gt, gt]).applyTerm (v 4))
    rw [apply_then]
    exact derives_thenEq gt

/-- **T2 applies**: `Derives` is functional for this module. -/
theorem functional {C w₁ w₂ : T} (one : Derives module ↑rows C w₁) (two : Derives module ↑rows C w₂) :
    w₁ = w₂ :=
  derives_functional rangeRestricted queriesBound exclusive one two

theorem ground : (lex eq gt lt).isGround := by
  intro i
  obtain ⟨k, bound⟩ := i
  have nullary : ∀ n : Con, Con.arity n = 0 → ∀ args : Fin (Con.arity n) → T,
      (Term.app (σ := readingSignature σ Label) (Head.con n) args).isGround :=
    fun n zero args j => absurd j.2 (by change ¬ (j : ℕ) < Con.arity n; omega)
  rcases k with _ | _ | _ | k
  · exact nullary Con.eq rfl _
  · exact nullary Con.gt rfl _
  · exact nullary Con.lt rfl _
  · change k + 3 < 3 at bound
    omega

theorem rows_ground : ∀ e ∈ rows, e.isGround := fun _ inside => absurd inside (Finset.notMem_empty _)

/-! ## Demands, and exactly one value each -/

theorem demanded_cases {C : T} (demanded : Demanded module ↑rows (lex eq gt lt) C) :
    C = lex eq gt lt ∨ C = «then» gt lt ∨ C = «then» eq gt := by
  induction demanded with
  | seed => exact Or.inl rfl
  | @call l θ pre post source target _ split holds ih =>
    cases l with
    | thenLt => simp [module] at split
    | thenEq => simp [module] at split
    | thenGt => simp [module] at split
    | lex =>
      have matched : θ.applyTerm (v 0) = eq ∧ θ.applyTerm (v 1) = gt ∧ θ.applyTerm (v 2) = lt := by
        rcases ih with same | same | same
        · exact lex_inj.mp (by simpa only [module, apply_lex] using same)
        · exact absurd (by simpa only [module, apply_lex] using same) (lex_ne_then _ _ _ _ _)
        · exact absurd (by simpa only [module, apply_lex] using same) (lex_ne_then _ _ _ _ _)
      obtain ⟨first, second, third⟩ := matched
      rcases pre with _ | ⟨p, _ | ⟨q, pre⟩⟩
      · simp only [module, List.nil_append, List.cons.injEq, Premise.call.injEq] at split
        obtain ⟨⟨rfl, rfl⟩, -⟩ := split
        rw [apply_then, second, third]
        exact Or.inr (Or.inl rfl)
      · simp only [module, List.cons_append, List.nil_append, List.cons.injEq, Premise.call.injEq] at split
        obtain ⟨rfl, ⟨rfl, rfl⟩, -⟩ := split
        have value : Derives module ↑rows («then» gt lt) (θ.applyTerm (v 3)) := by
          have call := holds _ List.mem_cons_self
          change Derives module ↑rows (θ.applyTerm («then» (v 1) (v 2))) (θ.applyTerm (v 3)) at call
          rwa [apply_then, second, third] at call
        have isGt := functional value (derives_thenGt lt)
        rw [apply_then, first, isGt]
        exact Or.inr (Or.inr rfl)
      · simp [module] at split

theorem demanded_iff (C : T) :
    Demanded module ↑rows (lex eq gt lt) C ↔ C = lex eq gt lt ∨ C = «then» gt lt ∨ C = «then» eq gt := by
  refine ⟨demanded_cases, ?_⟩
  have asked : Demanded module ↑rows (lex eq gt lt)
      ((sub [eq, gt, lt, gt, gt]).applyTerm (module .lex).lhs) := by
    rw [show (module .lex).lhs = lex (v 0) (v 1) (v 2) from rfl, apply_lex]
    exact .seed
  have first := Demanded.call (M := module) (Rel := ↑rows) (C₀ := lex eq gt lt) (l := Label.lex) (pre := [])
    (post := [.call («then» (v 0) (v 3)) (v 4)])
    asked rfl (fun _ inside => absurd inside List.not_mem_nil)
  have second := Demanded.call (M := module) (Rel := ↑rows) (C₀ := lex eq gt lt) (l := Label.lex)
    (pre := [.call («then» (v 1) (v 2)) (v 3)]) (post := [])
    asked rfl (fun p inside => by
      obtain rfl := List.mem_singleton.mp inside
      show Derives module ↑rows ((sub [eq, gt, lt, gt, gt]).applyTerm («then» (v 1) (v 2)))
        ((sub [eq, gt, lt, gt, gt]).applyTerm (v 3))
      rw [apply_then]
      exact derives_thenGt lt)
  rw [apply_then] at first second
  rintro (rfl | rfl | rfl)
  · exact .seed
  · exact first
  · exact second

/-- **Each demanded call has exactly one value row in the closure.** -/
theorem exactly_one_value (C : T)
    (asked : demandRow C ∈ SetStoreClosure.closure (consequence (P := reading module)) (seed (lex eq gt lt) rows)) :
    ∃! w, valueRow C w ∈ SetStoreClosure.closure (consequence (P := reading module)) (seed (lex eq gt lt) rows) := by
  have demanded := (demandRow_mem_closure_iff rangeRestricted ground rows_ground C).mp asked
  have value : Derives module ↑rows C gt := by
    rcases demanded_cases demanded with rfl | rfl | rfl
    · exact derives_lex
    · exact derives_thenGt lt
    · exact derives_thenEq gt
  refine ⟨gt, (valueRow_mem_closure_iff rangeRestricted ground rows_ground C gt).mpr ⟨demanded, value⟩, ?_⟩
  intro w inside
  exact valueRow_unique rangeRestricted queriesBound exclusive ground rows_ground inside
    ((valueRow_mem_closure_iff rangeRestricted ground rows_ground C gt).mpr ⟨demanded, value⟩)

/-- The closure's value rows for `lex(eq, gt, lt)`: exactly `gt`. -/
theorem lex_values (w : T) :
    valueRow (lex eq gt lt) w ∈ SetStoreClosure.closure (consequence (P := reading module)) (seed (lex eq gt lt) rows) ↔
      w = gt := by
  rw [valueRow_mem_closure_iff rangeRestricted ground rows_ground]
  constructor
  · exact fun both => functional both.2 derives_lex
  · rintro rfl
    exact ⟨.seed, derives_lex⟩

#print axioms reading_text
#print axioms rangeRestricted
#print axioms queriesBound
#print axioms exclusive
#print axioms derives_lex
#print axioms functional
#print axioms demanded_iff
#print axioms exactly_one_value
#print axioms lex_values

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading.Order
