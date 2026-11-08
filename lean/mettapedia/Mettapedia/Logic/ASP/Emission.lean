import Mettapedia.Logic.ASP.Certificate

/-!
# The solver emits its certificate

A solver that certifies `unsat` keeps a certificate beside its state (`Book`):
the steps emitted so far, the checker's live clauses after them, the identifier
of each nogood it has named, and the next free identifier. The completion
nogoods are named `1, 2, …` from the start (`Program.initialBook`).

`Program.Emit` is the solver transition system with emission. Its state part is
always a step of `Program.Step` or no change (`Program.Emit.project`), so every
emitting run is a run of the solver.

* `quiet`: a solver step that emits nothing. Every reason on its trail and every
  learned nogood must already be named, and it may not report `unsat`.
* `loop`: name the loop nogood of a set of program atoms without falsum atoms
  containing the atom, by a loop-nogood step.
* `backjump`: a backjump whose reason is added by a RUP step; the step's hints are
  named nogoods, and the checker's RUP test must accept it.
* `fail`: a refutation; the empty clause is added by a RUP step.

## Results

* **The book stays checked** (`Program.emitReachable_inv`): along every emitting
  run, the emitted steps are accepted by the certificate checker with exactly the
  book's live clauses, every name denotes its clause, and every reason on the
  trail and every learned nogood is named.
* **An emitting run that reports `unsat` has emitted an accepted certificate**
  (`Program.emitted_accepted`), which by itself proves that there is no stable
  model (`Program.emitted_no_stable`), independently of the transition system's
  own soundness.
* **First-UIP emission is always possible** (`Program.firstUIP_emit`): at a
  conflict above level 0 with a literal at the current level, the first-UIP
  backjump with the RUP step of `RUP` is an emitting step. At level 0 the
  refutation is (`Program.refutation_emit`). Propagation by a named nogood and
  decisions are quiet steps (`Program.propagate_emit`, `Program.decide_emit`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP

open Mettapedia.GSLT.Logic PropositionalFormula Relation

universe u

variable {A : Type u}

/-- The certificate a running solver keeps. -/
structure Book (A : Type u) where
  /-- The emitted steps, oldest first. -/
  steps : List CertStep
  /-- The checker's live clauses after the steps. -/
  live : List (ℕ × Clause)
  /-- The identifier of each named nogood, by its literals. -/
  names : List (List (Lit A) × ℕ)
  /-- The next free identifier. -/
  next : ℕ

section Emission

variable [DecidableEq A]

/-- The identifier of a nogood, by its literals. -/
def idOf (names : List (List (Lit A) × ℕ)) (lits : List (Lit A)) : Option ℕ :=
  (names.find? fun e => decide (e.1 = lits)).map Prod.snd

/-- A nogood is named in the book. -/
def Named (b : Book A) (lits : List (Lit A)) : Prop := ∃ i, idOf b.names lits = some i

instance (b : Book A) (lits : List (Lit A)) : Decidable (Named b lits) :=
  decidable_of_iff ((idOf b.names lits).isSome = true) Option.isSome_iff_exists

/-- Names for nogoods, numbered from `k` on. -/
def nameFrom : ℕ → List (Nogood A) → List (List (Lit A) × ℕ)
  | _, [] => []
  | k, δ :: Δ => (δ.lits, k) :: nameFrom (k + 1) Δ

/-- Every reason on the trail and every learned nogood is named. -/
def Covered (b : Book A) (s : State A) : Prop :=
  (∀ e ∈ s.trail, ∀ ρ, e.reason = some ρ → Named b ρ.lits) ∧ ∀ ε ∈ s.learned, Named b ε.lits

theorem idOf_mem {names : List (List (Lit A) × ℕ)} {lits : List (Lit A)} {i : ℕ} (h : idOf names lits = some i) :
    (lits, i) ∈ names := by
  unfold idOf at h
  obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
  have same := List.find?_some he
  simp only [decide_eq_true_eq] at same
  rw [← same]
  exact List.mem_of_find?_eq_some he

theorem named_cons {b : Book A} {lits : List (Lit A)} (h : Named b lits) (x : List (Lit A) × ℕ) (steps live next) :
    Named ⟨steps, live, x :: b.names, next⟩ lits := by
  obtain ⟨i, hi⟩ := h
  unfold idOf at hi
  show ∃ j, idOf (x :: b.names) lits = some j
  unfold idOf
  simp only [List.find?_cons]
  split
  · exact ⟨_, rfl⟩
  · exact ⟨i, hi⟩

theorem named_self (b : Book A) (lits : List (Lit A)) (i : ℕ) (steps live next) :
    Named ⟨steps, live, (lits, i) :: b.names, next⟩ lits :=
  ⟨i, by simp [idOf]⟩

omit [DecidableEq A] in
theorem nameFrom_mem : ∀ {k : ℕ} {Δ : List (Nogood A)} {p : List (Lit A) × ℕ}, p ∈ nameFrom k Δ →
    ∃ j δ, p.2 = k + j ∧ Δ[j]? = some δ ∧ δ.lits = p.1
  | _, [], _, h => by simp [nameFrom] at h
  | k, δ :: Δ, p, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨0, δ, by simp, rfl, rfl⟩
    · obtain ⟨j, δ', hp, hj, same⟩ := nameFrom_mem h
      exact ⟨j + 1, δ', by rw [hp]; omega, by simpa using hj, same⟩

omit [DecidableEq A] in
theorem mem_nameFrom : ∀ {k : ℕ} {Δ : List (Nogood A)} {δ : Nogood A}, δ ∈ Δ → ∃ i, (δ.lits, i) ∈ nameFrom k Δ
  | _, [], _, h => absurd h List.not_mem_nil
  | k, δ' :: Δ, δ, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨k, List.mem_cons_self⟩
    · obtain ⟨i, hi⟩ := mem_nameFrom (k := k + 1) h
      exact ⟨i, List.mem_cons_of_mem _ hi⟩

theorem named_of_mem {b : Book A} {lits : List (Lit A)} {i : ℕ} (h : (lits, i) ∈ b.names) : Named b lits := by
  unfold Named idOf
  obtain ⟨e, he⟩ := Option.isSome_iff_exists.mp
    (List.find?_isSome.mpr ⟨(lits, i), h, by simp⟩ : (b.names.find? fun e => decide (e.1 = lits)).isSome)
  exact ⟨e.2, by rw [he]; rfl⟩

/-- The identifiers of the hints. -/
def hintIds (b : Book A) (hints : List (Nogood A)) : List ℕ := hints.map fun ρ => (idOf b.names ρ.lits).getD 0

namespace Program

variable (P : Program A)

/-- The book at the start: no steps, the completion as input, its nogoods named `1, 2, …`. -/
def initialBook : Book A := ⟨[], P.inputs, nameFrom 1 P.completionNogoods, P.completionNogoods.length + 1⟩

/-- Emit a RUP step adding the clause of `lits`, and name it. -/
def emitRup (b : Book A) (lits : List (Lit A)) (hints : List (Nogood A)) : Book A :=
  ⟨b.steps ++ [.lrat (.rup b.next (P.lratClause lits) (hintIds b hints))], (b.next, P.lratClause lits) :: b.live,
    (lits, b.next) :: b.names, b.next + 1⟩

/-- The numbers of a list of atoms. -/
def atomNumbers (U : List A) : List ℕ := U.map fun a => P.index (.atom a)

/-- Emit a loop step adding the loop nogood of `U` for `a`, and name it. -/
def emitLoop (b : Book A) (U : List A) (a : A) : Book A :=
  ⟨b.steps ++ [.loop b.next (P.lratClause (P.loopNogood U.toFinset a).lits) (P.atomNumbers U) (P.index (.atom a))],
    (b.next, P.lratClause (P.loopNogood U.toFinset a).lits) :: b.live,
    ((P.loopNogood U.toFinset a).lits, b.next) :: b.names, b.next + 1⟩

/-- **The solver with emission.** -/
inductive Emit : Config A × Book A → Config A × Book A → Prop
  /-- A solver step that emits nothing: every reason and learned nogood stays named, and it does
  not report `unsat`. -/
  | quiet {s : State A} {c : Config A} {b : Book A} :
      P.Step (.running s) c → c ≠ .done .unsat → (∀ s', c = .running s' → Covered b s') →
      Emit (.running s, b) (c, b)
  /-- Name the loop nogood of a set of program atoms without falsum atoms containing the atom. -/
  | loop {s : State A} {b : Book A} {U : List A} {a : A} :
      a ∈ U → (∀ x ∈ U, P.IsVar (.atom x)) → (∀ x ∈ U, ¬ P.Falsum x) →
      Emit (.running s, b) (.running s, P.emitLoop b U a)
  /-- A backjump whose reason is added by a RUP step. -/
  | backjump {s : State A} {b : Book A} {ε : Nogood A} {hints : List (Nogood A)} {l : Lit A}
      {newer older : List (Entry A)} :
      P.Step (.running s) (.running ⟨⟨l.compl, levelOf older, some ε⟩ :: older, s.learned, s.restartMark⟩) →
      s.trail = newer ++ older → (∀ ρ ∈ hints, Named b ρ.lits) →
      PropositionalLRATActions.rupCheck (hints.map fun ρ => P.lratClause ρ.lits) (P.lratClause ε.lits) = true →
      Emit (.running s, b)
        (.running ⟨⟨l.compl, levelOf older, some ε⟩ :: older, s.learned, s.restartMark⟩, P.emitRup b ε.lits hints)
  /-- A refutation: the empty clause by a RUP step. -/
  | fail {s : State A} {b : Book A} {hints : List (Nogood A)} :
      P.Step (.running s) (.done .unsat) → (∀ ρ ∈ hints, Named b ρ.lits) →
      PropositionalLRATActions.rupCheck (hints.map fun ρ => P.lratClause ρ.lits) [] = true →
      Emit (.running s, b) (.done .unsat, P.emitRup b [] hints)

/-- Configurations an emitting run reaches. -/
def EmitReachable (c : Config A) (b : Book A) : Prop :=
  ReflTransGen P.Emit (.running State.initial, P.initialBook) (c, b)

/-- **Emission refines the solver**: the state part of an emitting step is a solver step or no
change. -/
theorem Emit.project {c c' : Config A} {b b' : Book A} (h : P.Emit (c, b) (c', b')) : c = c' ∨ P.Step c c' := by
  cases h with
  | quiet step _ _ => exact Or.inr step
  | loop _ _ _ => exact Or.inl rfl
  | backjump step _ _ _ => exact Or.inr step
  | fail step _ _ => exact Or.inr step

theorem emitReachable_reachable {c : Config A} {b : Book A} (h : P.EmitReachable c b) : P.Reachable c := by
  unfold EmitReachable at h
  suffices ∀ x, ReflTransGen P.Emit (.running State.initial, P.initialBook) x → P.Reachable x.1 from this _ h
  intro x reach
  induction reach with
  | refl => exact ReflTransGen.refl
  | @tail y z _ step ih =>
    obtain ⟨c, b⟩ := y
    obtain ⟨c', b'⟩ := z
    rcases Emit.project P step with same | step'
    · exact same ▸ ih
    · exact ih.tail step'

/-! ## The book invariant -/

/-- **The book invariant.** -/
structure BookInv (b : Book A) : Prop where
  run : P.certRun b.steps = some b.live
  names : ∀ p ∈ b.names, lookupClause b.live p.2 = some (P.lratClause p.1)
  fresh : ∀ e ∈ b.live, e.1 < b.next
  completion : ∀ δ ∈ P.completionNogoods, Named b δ.lits

theorem initialBook_inv : P.BookInv P.initialBook where
  run := rfl
  names := by
    intro p hp
    obtain ⟨j, δ, hid, hj, same⟩ := nameFrom_mem hp
    change lookupClause (numberFrom 1 P.completionLRAT) p.2 = _
    rw [hid, lookupClause_numberFrom, completionLRAT, List.getElem?_map, hj, ← same]
    rfl
  fresh := by
    intro e he
    have := numberFrom_lt he
    simp only [completionLRAT, List.length_map] at this
    change e.1 < P.completionNogoods.length + 1
    omega
  completion := by
    intro δ hδ
    obtain ⟨i, hi⟩ := mem_nameFrom (k := 1) hδ
    exact named_of_mem (b := P.initialBook) hi

theorem BookInv.lookup {b : Book A} (inv : P.BookInv b) {lits : List (Lit A)} {i : ℕ}
    (h : idOf b.names lits = some i) : lookupClause b.live i = some (P.lratClause lits) :=
  inv.names _ (idOf_mem h)

theorem BookInv.lookup_fresh {b : Book A} (inv : P.BookInv b) : lookupClause b.live b.next = none := by
  cases h : lookupClause b.live b.next with
  | none => rfl
  | some c => exact absurd (inv.fresh _ (lookupClause_mem h)) (lt_irrefl _)

theorem BookInv.hints {b : Book A} (inv : P.BookInv b) :
    ∀ {hints : List (Nogood A)}, (∀ ρ ∈ hints, Named b ρ.lits) →
      (hintIds b hints).mapM (lookupClause b.live) = some (hints.map fun ρ => P.lratClause ρ.lits)
  | [], _ => rfl
  | ρ :: hints, named => by
    obtain ⟨i, hi⟩ := named ρ List.mem_cons_self
    have rest := BookInv.hints inv fun ρ' h => named ρ' (List.mem_cons_of_mem _ h)
    unfold hintIds at rest ⊢
    simp only [List.map_cons, List.mapM_cons, hi, Option.getD_some, inv.lookup P hi, rest]
    rfl

theorem lookupClause_cons_self (live : List (ℕ × Clause)) (id : ℕ) (c : Clause) :
    lookupClause ((id, c) :: live) id = some c := by
  simp [lookupClause]

theorem lookupClause_cons_of_ne (live : List (ℕ × Clause)) {id i : ℕ} (c : Clause) (ne : i ≠ id) :
    lookupClause ((id, c) :: live) i = lookupClause live i := by
  have : (id == i) = false := by simpa using Ne.symm ne
  simp [lookupClause, this]

theorem certRun_append (steps : List CertStep) (st : CertStep) :
    P.certRun (steps ++ [st]) = (P.certRun steps).bind fun live => P.certStep live st := by
  unfold certRun
  rw [List.foldlM_append]
  cases List.foldlM P.certStep P.inputs steps with
  | none => rfl
  | some live =>
    simp only [List.foldlM_cons, List.foldlM_nil, Option.bind_some]
    cases h : P.certStep live st <;> simp [h]

/-- Adding a clause under the next identifier keeps the names, the freshness and the
completion names. -/
theorem BookInv.push {b : Book A} (inv : P.BookInv b) {st : CertStep} {lits : List (Lit A)}
    (run : P.certStep b.live st = some ((b.next, P.lratClause lits) :: b.live)) :
    P.BookInv ⟨b.steps ++ [st], (b.next, P.lratClause lits) :: b.live, (lits, b.next) :: b.names, b.next + 1⟩ where
  run := by
    change P.certRun (b.steps ++ [st]) = _
    rw [certRun_append, inv.run, Option.bind_some, run]
  names := by
    rintro p (_ | ⟨_, hp⟩)
    · exact lookupClause_cons_self _ _ _
    · have old := inv.names p hp
      have ne : p.2 ≠ b.next := fun same => by
        have := inv.fresh _ (lookupClause_mem old)
        simp only [same] at this
        exact lt_irrefl _ this
      change lookupClause ((b.next, P.lratClause lits) :: b.live) p.2 = _
      rw [lookupClause_cons_of_ne _ _ ne, old]
  fresh := by
    rintro e (_ | ⟨_, he⟩)
    · exact Nat.lt_succ_self _
    · exact Nat.lt_succ_of_lt (inv.fresh e he)
  completion := fun δ hδ => named_cons (inv.completion δ hδ) _ _ _ _

theorem BookInv.emitRup {b : Book A} (inv : P.BookInv b) {lits : List (Lit A)} {hints : List (Nogood A)}
    (named : ∀ ρ ∈ hints, Named b ρ.lits)
    (rup : PropositionalLRATActions.rupCheck (hints.map fun ρ => P.lratClause ρ.lits) (P.lratClause lits) = true) :
    P.BookInv (P.emitRup b lits hints) := by
  apply inv.push
  simp [certStep, inv.lookup_fresh, inv.hints P named, rup]

theorem filterMap_atomOf_atomNumbers {U : List A} (vars : ∀ x ∈ U, P.IsVar (.atom x)) :
    (P.atomNumbers U).filterMap P.atomOf = U := by
  unfold atomNumbers
  rw [List.filterMap_map]
  have same : ∀ x ∈ U, (P.atomOf ∘ fun a => P.index (Var.atom a)) x = some x :=
    fun x hx => P.atomOf_index (vars x hx)
  rw [List.filterMap_congr same, List.filterMap_some]

theorem loopClause_atomNumbers {U : List A} {a : A} (member : a ∈ U) (vars : ∀ x ∈ U, P.IsVar (.atom x))
    (noFalsum : ∀ x ∈ U, ¬ P.Falsum x) :
    P.loopClause (P.atomNumbers U) (P.index (.atom a)) = some (P.lratClause (P.loopNogood U.toFinset a).lits) := by
  have all : (P.atomNumbers U).all (fun i => (P.atomOf i).any fun a => !P.falsum a) = true := by
    rw [List.all_eq_true]
    intro i hi
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hi
    simp [P.atomOf_index (vars x hx), (P.falsum_eq_false_iff).mpr (noFalsum x hx)]
  have mem : P.index (.atom a) ∈ P.atomNumbers U := List.mem_map_of_mem member
  simp [loopClause, all, mem, P.atomOf_index (vars a member), P.filterMap_atomOf_atomNumbers vars]

theorem BookInv.emitLoop {b : Book A} (inv : P.BookInv b) {U : List A} {a : A} (member : a ∈ U)
    (vars : ∀ x ∈ U, P.IsVar (.atom x)) (noFalsum : ∀ x ∈ U, ¬ P.Falsum x) : P.BookInv (P.emitLoop b U a) := by
  apply inv.push
  have ok : P.loopStepOk (P.lratClause (P.loopNogood U.toFinset a).lits) (P.atomNumbers U) (P.index (.atom a)) = true := by
    simp [loopStepOk, P.loopClause_atomNumbers member vars noFalsum]
  simp [certStep, inv.lookup_fresh, ok]

theorem Covered.mono {b : Book A} {s : State A} (h : Covered b s) (lits : List (Lit A)) (i : ℕ) (steps live next) :
    Covered ⟨steps, live, (lits, i) :: b.names, next⟩ s :=
  ⟨fun e he ρ hρ => named_cons (h.1 e he ρ hρ) _ _ _ _, fun ε hε => named_cons (h.2 ε hε) _ _ _ _⟩

/-- **Emitting steps keep the book invariant and the naming of reasons.** -/
theorem Emit.inv {c c' : Config A} {b b' : Book A} (step : P.Emit (c, b) (c', b')) (inv : P.BookInv b)
    (covered : ∀ s, c = .running s → Covered b s) :
    P.BookInv b' ∧ ∀ s', c' = .running s' → Covered b' s' := by
  cases step with
  | quiet _ _ target => exact ⟨inv, target⟩
  | @loop s _ U a member vars noFalsum =>
    refine ⟨inv.emitLoop P member vars noFalsum, ?_⟩
    rintro s' ⟨⟩
    exact Covered.mono (covered s rfl) _ _ _ _ _
  | @backjump s _ ε hints l newer older _ split named rup =>
    refine ⟨inv.emitRup P named rup, ?_⟩
    rintro s' ⟨⟩
    obtain ⟨reasons, learned⟩ := covered s rfl
    refine ⟨?_, fun ε' hε' => named_cons (learned ε' hε') _ _ _ _⟩
    rintro e (_ | ⟨_, he⟩) ρ hρ
    · cases hρ
      exact named_self _ _ _ _ _ _
    · exact named_cons (reasons e (split ▸ List.mem_append_right _ he) ρ hρ) _ _ _ _
  | fail _ named rup =>
    refine ⟨inv.emitRup P named rup, ?_⟩
    rintro s' ⟨⟩

/-- **Along every emitting run, the book is checked and every reason is named.** -/
theorem emitReachable_inv {c : Config A} {b : Book A} (h : P.EmitReachable c b) :
    P.BookInv b ∧ ∀ s, c = .running s → Covered b s := by
  unfold EmitReachable at h
  suffices ∀ x, ReflTransGen P.Emit (.running State.initial, P.initialBook) x →
      P.BookInv x.2 ∧ ∀ s, x.1 = .running s → Covered x.2 s from this _ h
  intro x reach
  induction reach with
  | refl =>
    refine ⟨P.initialBook_inv, ?_⟩
    rintro s ⟨⟩
    exact ⟨fun e he => absurd he List.not_mem_nil, fun ε hε => absurd hε List.not_mem_nil⟩
  | @tail y z _ step ih =>
    obtain ⟨c, b⟩ := y
    obtain ⟨c', b'⟩ := z
    exact Emit.inv P step ih.1 ih.2

/-- **An emitting run that reports `unsat` has emitted an accepted certificate.** -/
theorem emitted_accepted {b : Book A} (h : P.EmitReachable (.done .unsat) b) : P.checkCert b.steps = true := by
  have inv := (P.emitReachable_inv h).1
  unfold EmitReachable at h
  rcases ReflTransGen.cases_tail h with same | ⟨⟨c₀, b₀⟩, _, last⟩
  · cases same
  · cases last with
    | quiet _ notUnsat _ => exact absurd rfl notUnsat
    | @fail s _ hints _ _ _ =>
      unfold checkCert
      rw [inv.run]
      exact List.any_eq_true.mpr ⟨_, List.mem_cons_self, by simp⟩

/-- **The emitted certificate refutes the program** by the checker alone. -/
theorem emitted_no_stable {b : Book A} (h : P.EmitReachable (.done .unsat) b) (M : Set A) : ¬ P.Stable M :=
  P.checkCert_sound (P.emitted_accepted h) M

/-! ## Emission is always possible -/

/-- Propagation by a named database nogood is a quiet step. -/
theorem propagate_emit {s : State A} {b : Book A} (reach : P.EmitReachable (.running s) b) {δ : Nogood A}
    {l : Lit A} (database : P.InDatabase s δ) (unit : s.UnitOn δ l) (isVar : P.IsVar l.var)
    (named : Named b δ.lits) :
    P.Emit (.running s, b) (.running (s.push ⟨l.compl, levelOf s.trail, some δ⟩), b) := by
  obtain ⟨reasons, learned⟩ := (P.emitReachable_inv reach).2 s rfl
  refine .quiet (.propagate database unit isVar) (by simp) ?_
  rintro s' ⟨⟩
  refine ⟨?_, learned⟩
  rintro e (_ | ⟨_, he⟩) ρ hρ
  · cases hρ
    exact named
  · exact reasons e he ρ hρ

/-- A decision is a quiet step. -/
theorem decide_emit {s : State A} {b : Book A} (reach : P.EmitReachable (.running s) b) {l : Lit A}
    (isVar : P.IsVar l.var) (unassigned : ¬ s.Assigned l.var) :
    P.Emit (.running s, b) (.running (s.push ⟨l, levelOf s.trail + 1, none⟩), b) := by
  obtain ⟨reasons, learned⟩ := (P.emitReachable_inv reach).2 s rfl
  refine .quiet (.decide isVar unassigned) (by simp) ?_
  rintro s' ⟨⟩
  refine ⟨?_, learned⟩
  rintro e (_ | ⟨_, he⟩) ρ hρ
  · cases hρ
  · exact reasons e he ρ hρ

theorem firstUIPHints_named {s : State A} {b : Book A} (covered : Covered b s) {δ : Nogood A}
    (named : Named b δ.lits) : ∀ ρ ∈ firstUIPHints s δ, Named b ρ.lits := by
  intro ρ hρ
  rcases List.mem_append.mp hρ with hρ | hρ
  · obtain ⟨e, he, hreason⟩ := uipReasons_mem (List.mem_reverse.mp hρ)
    refine covered.1 e ?_ ρ hreason
    rw [← currentLevel_append_belowLevel s.trail]
    exact List.mem_append_left _ he
  · rw [List.mem_singleton] at hρ
    exact hρ ▸ named

/-- **First-UIP learning is an emitting step**: at a conflict above level 0 with a literal at the
current level, the backjump to the assertion level, with the first-UIP nogood as its reason, emits
the RUP step of the nogood with the resolved reasons, oldest first, and the conflict as hints. -/
theorem firstUIP_emit {s : State A} {b : Book A} (reach : P.EmitReachable (.running s) b) {δ : Nogood A}
    (database : P.InDatabase s δ) (named : Named b δ.lits) (falsified : s.Falsifies δ) (level : levelOf s.trail ≠ 0)
    (current : ∃ m ∈ δ.lits, m ∈ (currentLevel s.trail).map Entry.lit) :
    ∃ u, P.Emit (.running s, b)
      (.running ⟨⟨u.compl, assertionLevel s.trail (firstUIP s δ) u,
          some ⟨firstUIP s δ, .learned b.next⟩⟩ :: cutTo (assertionLevel s.trail (firstUIP s δ) u) s.trail,
        s.learned, s.restartMark⟩,
        P.emitRup b (firstUIP s δ) (firstUIPHints s δ)) := by
  have reachable := P.emitReachable_reachable reach
  have inv := P.reachable_inv reachable
  have just := P.reachable_justified reachable
  obtain ⟨u, -, -, -, cutLevel, -, step⟩ :=
    P.firstUIP_backjump inv just database falsified level current (.learned b.next)
  refine ⟨u, ?_⟩
  obtain ⟨pre, split⟩ := cutTo_suffix (assertionLevel s.trail (firstUIP s δ) u) s.trail
  have emit := Emit.backjump (P := P) (b := b) (ε := ⟨firstUIP s δ, .learned b.next⟩) (hints := firstUIPHints s δ)
    (l := u) (newer := pre) (older := cutTo (assertionLevel s.trail (firstUIP s δ) u) s.trail)
    (by rwa [cutLevel]) split (firstUIPHints_named ((P.emitReachable_inv reach).2 s rfl) named)
    (P.firstUIP_rupCheck inv just falsified)
  rwa [cutLevel] at emit

/-- **The refutation is an emitting step**: at a level-0 conflict on a named nogood, the empty
clause is emitted with the trail's reasons, oldest first, and the conflict as hints. -/
theorem refutation_emit {s : State A} {b : Book A} (reach : P.EmitReachable (.running s) b) {δ : Nogood A}
    (database : P.InDatabase s δ) (named : Named b δ.lits) (falsified : s.Falsifies δ)
    (ground : levelOf s.trail = 0) :
    P.Emit (.running s, b) (.done .unsat, P.emitRup b [] (refutationHints s δ)) := by
  have reachable := P.emitReachable_reachable reach
  have inv := P.reachable_inv reachable
  have just := P.reachable_justified reachable
  have covered := (P.emitReachable_inv reach).2 s rfl
  refine .fail (.fail database falsified ground) ?_ (P.refutation_rupCheck inv just ground falsified)
  intro ρ hρ
  rcases List.mem_append.mp hρ with hρ | hρ
  · obtain ⟨e, he, hreason⟩ := trailReasons_mem (List.mem_reverse.mp hρ)
    exact covered.1 e he ρ hreason
  · rw [List.mem_singleton] at hρ
    exact hρ ▸ named

end Program

end Emission

end Mettapedia.Logic.ASP
