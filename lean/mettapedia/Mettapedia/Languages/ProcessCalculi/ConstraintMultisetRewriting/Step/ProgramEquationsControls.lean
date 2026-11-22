import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramEquations

/-!
# Controls for pattern equations

Each control is computed twice: as the program's answers (`answers`), and on the ordinary step,
where the admitted firings on the call occurrence from the initial configuration correspond one to
one with those answers (`initial_answers`).

* **Two matching equations, two answers** (`two_answers`, `two_answers_on_step`): `(= (f $x) (one $x))`
  and `(= (f $x) (two $x))` both match `(f a)`. Control: an equation with another head adds no answer
  (`other_head_adds_nothing`).
* **Duplicates are kept, not merged** (`duplicate_answers`): the same equation twice gives the same
  answer twice; the answers are a multiset, not a set.
* **Two-way: the call's variable is bound by the equation** (`variable_bound`,
  `variable_bound_on_step`): `(= (f a) b)` against `(f $y)` beside a row `(out $y)` answers `b` and
  binds `$y` to `a` in the other row.
* **No match: the call stays as it is** (`no_match_no_answer`, `no_match_stuck`,
  `no_match_stays`): `(= (f a) b)` against `(f c)` has no answer, no reference step and no translated
  firing; the initial configuration still represents the call, consistently.
* **A shared caller variable correlates the answers** (`correlated_answers`): `(= (f a) one)` and
  `(= (f c) two)` against `(f $y)` beside `(out $y)` answer `one` with `(out a)` and `two` with
  `(out c)`. Control (`independent_answers`): beside `(out $z)` with a separate variable both answers
  leave `(out $z)` unbound.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramEquations.Controls

open Mettapedia.Logic.LP
open ProgramRows ProgramTranslation ProgramEquationsOpen

/-! ## Computing answers -/

theorem answers_cons_some {e : Equation} {prog : Program} {n : ℕ} {t : Tm} {F W : Multiset Tm}
    (unifier : Subst rows) (unifies : Unifies unifier [(e.lhs.at n, t)])
    (forced : ∀ θ : Subst rows, IsMGU [(e.lhs.at n, t)] θ →
      thread (θ.applyTerm (e.rhs.at n)) ::ₘ F.map θ.applyTerm = W) :
    answers (e :: prog) n t F = W :: answers prog n t F := by
  obtain ⟨θ, accepted⟩ := unifyTotal_complete ⟨unifier, unifies⟩
  unfold answers
  refine List.filterMap_cons_some ?_
  simp only [accepted, Option.map_some]
  rw [forced θ (isMGU_of_unifyTotal accepted)]

theorem answers_cons_none {e : Equation} {prog : Program} {n : ℕ} {t : Tm} {F : Multiset Tm}
    (fails : ∀ θ : Subst rows, ¬ Unifies θ [(e.lhs.at n, t)]) :
    answers (e :: prog) n t F = answers prog n t F := by
  have none : unifyTotal [(e.lhs.at n, t)] = none :=
    (unifyTotal_none_iff_not_unifiable (σ := rows) _).mpr fun ⟨θ, h⟩ => fails θ h
  unfold answers
  exact List.filterMap_cons_none (by simp [none])

/-- After removing the call occurrence, the initial configuration reads as the other rows. -/
theorem erase_first (t : Tm) (rest : List Tm) :
    ((openInitial (t :: rest)).present.erase ⟨t, 0, 0⟩).val.map (readAt (Subst.id rows)) =
      (rest : Multiset Tm) := by
  have present : (openInitial (t :: rest)).present = insert ⟨t, 0, 0⟩ (openRows 1 rest).toFinset := by
    show (openRows 0 (t :: rest)).toFinset = _
    simp only [openRows, List.toFinset_cons]
  have absent : (⟨t, 0, 0⟩ : Occ) ∉ (openRows 1 rest).toFinset := fun h => by
    have := (openRows_mem (List.mem_toFinset.mp h)).2.1
    simp at this
  rw [present, Finset.erase_insert absent, List.toFinset_val, (openRows_nodup 1 rest).dedup,
    Multiset.map_coe, openRows_read]

/-- **On the step, from the initial configuration**, the admitted firings on the call occurrence
correspond one to one with the program's answers, each result representing its answer. -/
theorem initial_answers (prog : Program) (t : Tm) (rest : List Tm)
    (bounded : ∀ r ∈ thread t :: rest, Bounded 1 r) :
    List.Forall₂ (fun D W => ORepresents D W 2)
      (stepAnswers prog 1 (openInitial (thread t :: rest)) ⟨thread t, 0, 0⟩)
      (answers prog 1 t (rest : Multiset Tm)) := by
  have exact := answers_exact prog (openInitial_solved _ bounded)
    (o := ⟨thread t, 0, 0⟩) (t := t) (List.mem_toFinset.mpr List.mem_cons_self)
    (Subst.applyTerm_id _)
  rwa [erase_first] at exact

/-! ## Terms -/

theorem bounded_const (n k : ℕ) : Bounded n (.const k) := fun v h => by
  simp [Term.freeVars] at h

theorem bounded_tagged {n k : ℕ} {t : Tm} (h : Bounded n t) : Bounded n (tagged k t) := fun v hv => by
  rw [freeVars_tagged] at hv
  exact h v hv

theorem bounded_var {n : ℕ} {v : ℕ × ℕ} (lt : v.1 < n) : Bounded n (.var v) := fun w hw => by
  rw [Term.mem_freeVars_var (σ := rows)] at hw
  rw [hw]
  exact lt

theorem ground_const (k : ℕ) (σ : Subst rows) : σ.applyTerm (.const k) = .const k := rfl

def ka : Tm := .const 60
def kc : Tm := .const 62
def kOne : Tm := .const 63
def kTwo : Tm := .const 64

/-- The caller's variables `$y` and `$z`, at scope `0`. -/
def vy : Tm := .var (0, 0)
def vz : Tm := .var (0, 1)

/-- `(= (f $x) (g $x))`. -/
def xEq (f g : ℕ) : Equation := ⟨ptag f (.var 0), ptag g (.var 0)⟩

/-- `(= (f a) r)` with a constant argument and a constant right-hand side. -/
def groundEq (f a r : ℕ) : Equation := ⟨ptag f (.sym a), .sym r⟩

theorem xEq_unifies (f n : ℕ) (a : Tm) (ground : ∀ σ : Subst rows, σ.applyTerm a = a) :
    Unifies (Subst.single (n, 0) a) [((xEq f f).lhs.at n, tagged f a)] := by
  rw [show (xEq f f).lhs.at n = tagged f (.var (n, 0)) from rfl, unifies_tagged_iff, unifies_single,
    ground]
  exact Subst.single_eq _ _

theorem xEq_forced {f n : ℕ} {a : Tm} (ground : ∀ σ : Subst rows, σ.applyTerm a = a)
    {θ : Subst rows} (h : Unifies θ [((xEq f f).lhs.at n, tagged f a)]) : θ (n, 0) = a := by
  rw [show (xEq f f).lhs.at n = tagged f (.var (n, 0)) from rfl, unifies_tagged_iff, unifies_single,
    ground] at h
  exact h

/-- **The answer of `(= (f $x) (g $x))` to `(f a)`**, alone. -/
theorem answers_xEq {f g : ℕ} {prog : Program} {n : ℕ} {a : Tm}
    (ground : ∀ σ : Subst rows, σ.applyTerm a = a) :
    answers (xEq f g :: prog) n (tagged f a) 0 = {thread (tagged g a)} :: answers prog n (tagged f a) 0 :=
  answers_cons_some (Subst.single (n, 0) a) (xEq_unifies f n a ground) fun θ mgu => by
    have bound := xEq_forced (f := f) ground mgu.unifies
    rw [Multiset.map_zero, Multiset.cons_zero]
    show ({thread (θ.applyTerm ((ptag g (.var 0)).at n))} : Multiset Tm) = _
    rw [ptag_at, apply_tagged]
    change ({thread (tagged g (θ (n, 0)))} : Multiset Tm) = _
    rw [bound]

theorem groundEq_unifies_var (f a r n : ℕ) (v : ℕ × ℕ) :
    Unifies (Subst.single (σ := rows) v (.const a)) [((groundEq f a r).lhs.at n, tagged f (.var v))] := by
  rw [show (groundEq f a r).lhs.at n = tagged f (.const a) from rfl, unifies_tagged_iff, unifies_single]
  exact (Subst.single_eq (σ := rows) v (.const a)).symm

theorem groundEq_forced_var {f a r n : ℕ} {v : ℕ × ℕ} {θ : Subst rows}
    (h : Unifies θ [((groundEq f a r).lhs.at n, tagged f (.var v))]) : θ v = .const a := by
  rw [show (groundEq f a r).lhs.at n = tagged f (.const a) from rfl, unifies_tagged_iff, unifies_single]
    at h
  exact h.symm

theorem groundEq_eqVars (f a r n : ℕ) (v : ℕ × ℕ) :
    eqVars [((groundEq f a r).lhs.at n, tagged f (.var v))] = {v} := by
  show eqVars [(tagged f (.const a), tagged f (.var v))] = {v}
  simp [eqVars, freeVars_tagged, Term.freeVars]

/-- **The answer of `(= (f a) r)` to `(f $v)` beside the row `(out $v)`**: `r`, and the shared
variable is bound to `a` in the other row. -/
theorem answers_groundEq_shared {f a r : ℕ} {prog : Program} {n : ℕ} {v : ℕ × ℕ} :
    answers (groundEq f a r :: prog) n (tagged f (.var v)) (([tagged 70 (.var v)] : List Tm) : Multiset Tm) =
      (([thread (.const r), tagged 70 (.const a)] : List Tm) : Multiset Tm) ::
        answers prog n (tagged f (.var v)) (([tagged 70 (.var v)] : List Tm) : Multiset Tm) := by
  refine answers_cons_some (Subst.single (σ := rows) v (.const a)) (groundEq_unifies_var f a r n v) fun θ mgu => ?_
  have bound := groundEq_forced_var mgu.unifies
  change thread (.const r) ::ₘ (([tagged 70 (.var v)] : List Tm) : Multiset Tm).map θ.applyTerm = _
  rw [Multiset.map_coe, List.map_singleton, apply_tagged, Subst.applyTerm_var, bound, Multiset.cons_coe]

/-- **The answer of `(= (f a) r)` to `(f $v)` beside the row `(out $z)`** with a separate variable:
`r`, and `$z` stays unbound. -/
theorem answers_groundEq_independent {f a r : ℕ} {prog : Program} {n : ℕ} {v z : ℕ × ℕ}
    (apart : z ≠ v) :
    answers (groundEq f a r :: prog) n (tagged f (.var v)) (([tagged 70 (.var z)] : List Tm) : Multiset Tm) =
      (([thread (.const r), tagged 70 (.var z)] : List Tm) : Multiset Tm) ::
        answers prog n (tagged f (.var v)) (([tagged 70 (.var z)] : List Tm) : Multiset Tm) := by
  refine answers_cons_some (Subst.single (σ := rows) v (.const a)) (groundEq_unifies_var f a r n v) fun θ mgu => ?_
  have unbound : θ z = .var z := mgu.relevant.fixes z (by
    rw [groundEq_eqVars, Finset.mem_singleton]
    exact apart)
  change thread (.const r) ::ₘ (([tagged 70 (.var z)] : List Tm) : Multiset Tm).map θ.applyTerm = _
  rw [Multiset.map_coe, List.map_singleton, apply_tagged, Subst.applyTerm_var, unbound,
    Multiset.cons_coe]

theorem answers_nil (n : ℕ) (t : Tm) (F : Multiset Tm) : answers [] n t F = [] := rfl

/-! ## Two matching equations, two answers -/

/-- `(= (f $x) (one $x))` and `(= (f $x) (two $x))`. -/
def twoEquations : Program := [xEq 50 63, xEq 50 64]

theorem two_answers :
    answers twoEquations 1 (tagged 50 ka) 0 = [{thread (tagged 63 ka)}, {thread (tagged 64 ka)}] := by
  rw [twoEquations, ka, answers_xEq (ground_const 60), answers_xEq (ground_const 60), answers_nil]

theorem bounded_call (k a : ℕ) : ∀ r ∈ [thread (tagged k (.const a))], Bounded 1 r := by
  intro r h
  rw [List.mem_singleton] at h
  rw [h]
  exact bounded_tagged (bounded_tagged (bounded_const 1 a))

/-- **On the step: exactly two admitted firings on the call**, each representing one answer. -/
theorem two_answers_on_step :
    List.Forall₂ (fun D W => ORepresents D W 2)
      (stepAnswers twoEquations 1 (openInitial [thread (tagged 50 ka)]) ⟨thread (tagged 50 ka), 0, 0⟩)
      [{thread (tagged 63 ka)}, {thread (tagged 64 ka)}] := by
  have answers := initial_answers twoEquations (tagged 50 ka) [] (bounded_call 50 60)
  rwa [Multiset.coe_nil, two_answers] at answers

/-- **Control: an equation with another head adds no answer.** -/
theorem other_head_adds_nothing :
    answers (xEq 51 63 :: twoEquations) 1 (tagged 50 ka) 0 = answers twoEquations 1 (tagged 50 ka) 0 := by
  refine answers_cons_none fun θ h => ?_
  rw [show (xEq 51 63).lhs.at 1 = tagged 51 (.var (1, 0)) from rfl, unifies_single, apply_tagged,
    apply_tagged, tagged_inj] at h
  exact absurd h.1 (by decide)

/-- **Duplicates are kept**: the same equation twice gives its answer twice. -/
theorem duplicate_answers :
    answers [xEq 50 63, xEq 50 63] 1 (tagged 50 ka) 0 =
      [{thread (tagged 63 ka)}, {thread (tagged 63 ka)}] := by
  rw [ka, answers_xEq (ground_const 60), answers_xEq (ground_const 60), answers_nil]

/-! ## Two-way: the call's variable is bound by the equation -/

/-- `(= (f a) b)`. -/
def bindEquation : Program := [groundEq 50 60 61]

theorem bounded_shared (w : Tm) (bw : Bounded 1 w) :
    ∀ r ∈ [thread (tagged 50 vy), tagged 70 w], Bounded 1 r := by
  intro r h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl
  · exact bounded_tagged (bounded_tagged (bounded_var (by decide)))
  · exact bounded_tagged bw

/-- **`(f $y)` beside `(out $y)` answers `b`, and `$y` is bound to `a`.** -/
theorem variable_bound :
    answers bindEquation 1 (tagged 50 vy) (([tagged 70 vy] : List Tm) : Multiset Tm) =
      [(([thread (.const 61), tagged 70 ka] : List Tm) : Multiset Tm)] := by
  rw [bindEquation, vy, answers_groundEq_shared, answers_nil]
  rfl

theorem variable_bound_on_step :
    List.Forall₂ (fun D W => ORepresents D W 2)
      (stepAnswers bindEquation 1 (openInitial [thread (tagged 50 vy), tagged 70 vy])
        ⟨thread (tagged 50 vy), 0, 0⟩)
      [(([thread (.const 61), tagged 70 ka] : List Tm) : Multiset Tm)] := by
  have answers := initial_answers bindEquation (tagged 50 vy) [tagged 70 vy]
    (bounded_shared vy (bounded_var (by decide)))
  rwa [variable_bound] at answers

/-! ## No match: the call stays as it is -/

theorem no_match_fails (θ : Subst rows) : ¬ Unifies θ [((groundEq 50 60 61).lhs.at 1, tagged 50 kc)] := by
  rw [show (groundEq 50 60 61).lhs.at 1 = tagged 50 (.const 60) from rfl, unifies_tagged_iff,
    unifies_single]
  intro h
  change (.const 60 : Tm) = (.const 62 : Tm) at h
  simp at h

theorem no_match_no_answer : answers bindEquation 1 (tagged 50 kc) 0 = [] := by
  rw [bindEquation, answers_cons_none no_match_fails, answers_nil]

/-- A thread whose call unifies with no left-hand side has no reference step. -/
theorem singleton_stuck {prog : Program} {n : ℕ} {t : Tm}
    (fails : ∀ e ∈ prog, ∀ θ : Subst rows, ¬ Unifies θ [(e.lhs.at n, t)]) (s' : Multiset Tm × ℕ) :
    ¬ EqStep prog (({thread t} : Multiset Tm), n) s' := by
  intro step
  generalize hs : (({thread t} : Multiset Tm), n) = s at step
  cases step with
  | call j t' F n' θ mgu =>
      obtain ⟨hW, rfl⟩ := Prod.mk.inj hs
      obtain ⟨same, -⟩ := (Multiset.singleton_eq_cons_iff _).mp hW
      have : t = t' := (tagged_inj.mp same).2
      subst this
      exact fails _ (List.get_mem prog j) θ mgu.unifies

theorem bindEquation_fails : ∀ e ∈ bindEquation, ∀ θ : Subst rows,
    ¬ Unifies θ [(e.lhs.at 1, tagged 50 kc)] := by
  intro e member θ
  rw [bindEquation, List.mem_singleton] at member
  rw [member]
  exact no_match_fails θ

theorem no_match_tagged : ∀ r ∈ (([thread (tagged 50 kc)] : List Tm) : Multiset Tm), Tagged r := by
  intro r h
  rw [Multiset.mem_coe, List.mem_singleton] at h
  rw [h]
  exact tagged_tagged 40 _

/-- **No match: no reference step, no translated firing, and the call stays as it is**: the initial
configuration still represents the call, and its knowledge is consistent. -/
theorem no_match_stays :
    (∀ s', ¬ EqStep bindEquation ((([thread (tagged 50 kc)] : List Tm) : Multiset Tm), 1) s') ∧
      (∀ q, ¬ Translated (compiled bindEquation) (openInitial [thread (tagged 50 kc)], 1) q) ∧
      ORepresents (openInitial [thread (tagged 50 kc)])
        (([thread (tagged 50 kc)] : List Tm) : Multiset Tm) 1 ∧
      A.Consistent (openInitial [thread (tagged 50 kc)]).equations := by
  have rep := openInitial_represents [thread (tagged 50 kc)] (bounded_call 50 62)
  have stuck : ∀ s', ¬ EqStep bindEquation ((([thread (tagged 50 kc)] : List Tm) : Multiset Tm), 1) s' := by
    intro s'
    rw [Multiset.coe_singleton]
    exact singleton_stuck bindEquation_fails s'
  refine ⟨stuck, (stuck_iff rep no_match_tagged).mpr stuck, rep, ?_⟩
  obtain ⟨μ, solved, -⟩ := rep
  exact solved.consistent

/-! ## A shared caller variable correlates the answers -/

/-- `(= (f a) one)` and `(= (f c) two)`. -/
def correlatedEquations : Program := [groundEq 50 60 63, groundEq 50 62 64]

/-- **Correlated answers**: beside `(out $y)`, the answer `one` comes with `(out a)` and the answer
`two` with `(out c)`. -/
theorem correlated_answers :
    answers correlatedEquations 1 (tagged 50 vy) (([tagged 70 vy] : List Tm) : Multiset Tm) =
      [(([thread kOne, tagged 70 ka] : List Tm) : Multiset Tm),
        (([thread kTwo, tagged 70 kc] : List Tm) : Multiset Tm)] := by
  rw [correlatedEquations, vy, answers_groundEq_shared, answers_groundEq_shared, answers_nil]
  rfl

/-- **Control: with a separate variable the answers are not correlated**: beside `(out $z)`, both
answers leave `(out $z)` unbound. -/
theorem independent_answers :
    answers correlatedEquations 1 (tagged 50 vy) (([tagged 70 vz] : List Tm) : Multiset Tm) =
      [(([thread kOne, tagged 70 vz] : List Tm) : Multiset Tm),
        (([thread kTwo, tagged 70 vz] : List Tm) : Multiset Tm)] := by
  rw [correlatedEquations, vy, vz, answers_groundEq_independent (by decide),
    answers_groundEq_independent (by decide), answers_nil]
  rfl

theorem correlated_on_step :
    List.Forall₂ (fun D W => ORepresents D W 2)
      (stepAnswers correlatedEquations 1 (openInitial [thread (tagged 50 vy), tagged 70 vy])
        ⟨thread (tagged 50 vy), 0, 0⟩)
      [(([thread kOne, tagged 70 ka] : List Tm) : Multiset Tm),
        (([thread kTwo, tagged 70 kc] : List Tm) : Multiset Tm)] := by
  have answers := initial_answers correlatedEquations (tagged 50 vy) [tagged 70 vy]
    (bounded_shared vy (bounded_var (by decide)))
  rwa [correlated_answers] at answers

theorem independent_on_step :
    List.Forall₂ (fun D W => ORepresents D W 2)
      (stepAnswers correlatedEquations 1 (openInitial [thread (tagged 50 vy), tagged 70 vz])
        ⟨thread (tagged 50 vy), 0, 0⟩)
      [(([thread kOne, tagged 70 vz] : List Tm) : Multiset Tm),
        (([thread kTwo, tagged 70 vz] : List Tm) : Multiset Tm)] := by
  have answers := initial_answers correlatedEquations (tagged 50 vy) [tagged 70 vz]
    (bounded_shared vz (bounded_var (by decide)))
  rwa [independent_answers] at answers

#print axioms answers_cons_some
#print axioms answers_cons_none
#print axioms erase_first
#print axioms initial_answers
#print axioms two_answers
#print axioms two_answers_on_step
#print axioms other_head_adds_nothing
#print axioms duplicate_answers
#print axioms variable_bound
#print axioms variable_bound_on_step
#print axioms no_match_no_answer
#print axioms singleton_stuck
#print axioms no_match_stays
#print axioms correlated_answers
#print axioms independent_answers
#print axioms correlated_on_step
#print axioms independent_on_step

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramEquations.Controls
