import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.Tower
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceStep

/-!
# Numbers on the step: representation independence for programs, and its converse

The first-order step (`Step`, of the module `OccurrenceStep`) is generic in its terms and their
declared equality (`SubstitutionAction`). It has no grounded operations. This module adds the smallest
extension that puts a grounded table inside the step: **a term syntax with stored numerals and
applications of grounded operations** (`NTerm`), **a table** (`Table`: for an operation and two
stored numbers, an answer or a refusal; a refused call stays as written), **evaluation** by the table
innermost first (`eval`), and **the knowledge's equality**: two terms are identified when every
instance of them evaluates to terms of equal value (`Identified`). This is a lawful substitution
action for every table (`action`); the step itself is the tree's, unchanged.

* **The knowledge identifies stored numbers of equal value**, for every table
  (`numerals_identified`).
* **Storage variants** (`Variant`): the same term up to the storage of its numerals. **The knowledge
  identifies every pair of storage variants exactly when every operation of the table respects the
  value lens** (`identifies_variants_iff`; `TableRespects`, and its reading as `Respects` of the
  observer concepts, `tableRespects_iff`).
* **Representation independence on the step**, with a table that respects the value lens:
  - re-storing any numerals of a query changes no count and no absence answer
    (`answer_count_variant`, `answer_absent_variant`; position by position for programs too, in the
    module `Variants`);
  - re-storing every numeral of a program, of its labels, of its knowledge and of its query by a
    re-storing `ρ` (`Tower.Restoring`) changes no answer (`answer_restore`), carries every step to a
    step (`step_restore`) and every run to a run (`reach_restore`); for an injective re-storing the
    converse holds too (`step_restore_back`, `reach_restore_back`), so the answers reachable by runs
    are the same (`program_answers_iff`, `program_every_answer_iff`).
* **The converse, by a one-row program** (`one_row_converse`, `one_row_step_converse`): a table with
  one operation that does not respect the value lens has a one-row configuration, holding the call,
  whose count answer for the call is `1` and for a storage variant of the call is not; the firing
  that checks the first is admitted and the one that checks the second is refused.

**Instances.** The exact table (`exactTable`) respects the value lens. Its witness program
(`incr`: take `(foo $x)`, make `(bar (+ $x 1))`) fires from the row `(foo 5)` (`incr_fires`), and
after it the count of `(bar 6)` is `1` (`incr_answer`); re-storing every numeral by the injective
swap of storage (`swapStorage`, `5 ↦ 5.0`, `5.0 ↦ 5`) keeps the run and the answer
(`incr_restored`). The storage-dependent division (`storedDivTable`, a model of the measured
behaviour of HE's `/`: `(/ 5 2)` is `2` and `(/ 5.0 2)` is `2.5`) does not respect the lens; on the
one-row configuration holding `(/ 5 2)` the count of the query `(/ 5 2)` is `1` and the count of its
storage variant `(/ 5.0 2)` is not `1` (`division_one_row`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.OnTheStep

open Distinctions.ObserverConcepts Distinctions.NumberLens Tower

/-! ## Terms with stored numerals -/

/-- **Names of grounded operations.** -/
inductive OpName
  | plus
  | minus
  | times
  | divide
  deriving DecidableEq

/-- **Terms over numerals of type `N`**: numerals, variables, symbols, application of data, and a
grounded operation applied to two terms. -/
inductive NTerm (N : Type) : Type
  | num (n : N)
  | var (x : ℕ)
  | sym (c : String)
  | app (f a : NTerm N)
  | op (o : OpName) (l r : NTerm N)

namespace NTerm

variable {N M K : Type}

/-- Changing every numeral. -/
def map (f : N → M) : NTerm N → NTerm M
  | .num n => .num (f n)
  | .var x => .var x
  | .sym c => .sym c
  | .app g a => .app (map f g) (map f a)
  | .op o l r => .op o (map f l) (map f r)

/-- Substitution of terms for variables. -/
def subst (σ : ℕ → NTerm N) : NTerm N → NTerm N
  | .num n => .num n
  | .var x => σ x
  | .sym c => .sym c
  | .app g a => .app (subst σ g) (subst σ a)
  | .op o l r => .op o (subst σ l) (subst σ r)

/-- The numeral a term is, if it is one. -/
def asNum : NTerm N → Option N
  | .num n => some n
  | _ => none

theorem map_map (f : N → M) (g : M → K) (t : NTerm N) : (t.map f).map g = t.map (g ∘ f) := by
  induction t with
  | num n => rfl
  | var x => rfl
  | sym c => rfl
  | app a b iha ihb => simp only [map, iha, ihb]
  | op o l r ihl ihr => simp only [map, ihl, ihr]

theorem map_congr {f g : N → M} (same : ∀ n, f n = g n) (t : NTerm N) : t.map f = t.map g := by
  induction t with
  | num n => simp only [map, same]
  | var x => rfl
  | sym c => rfl
  | app a b iha ihb => simp only [map, iha, ihb]
  | op o l r ihl ihr => simp only [map, ihl, ihr]

theorem subst_var (t : NTerm N) : t.subst NTerm.var = t := by
  induction t with
  | num n => rfl
  | var x => rfl
  | sym c => rfl
  | app a b iha ihb => simp only [subst, iha, ihb]
  | op o l r ihl ihr => simp only [subst, ihl, ihr]

theorem subst_subst (σ τ : ℕ → NTerm N) (t : NTerm N) :
    (t.subst τ).subst σ = t.subst (fun x => (τ x).subst σ) := by
  induction t with
  | num n => rfl
  | var x => rfl
  | sym c => rfl
  | app a b iha ihb => simp only [subst, iha, ihb]
  | op o l r ihl ihr => simp only [subst, ihl, ihr]

theorem map_subst (f : N → M) (σ : ℕ → NTerm N) (t : NTerm N) :
    (t.subst σ).map f = (t.map f).subst (fun x => (σ x).map f) := by
  induction t with
  | num n => rfl
  | var x => rfl
  | sym c => rfl
  | app a b iha ihb => simp only [subst, map, iha, ihb]
  | op o l r ihl ihr => simp only [subst, map, ihl, ihr]

theorem asNum_map (f : N → M) (t : NTerm N) : (t.map f).asNum = t.asNum.map f := by
  cases t <;> rfl

theorem map_injective {f : N → M} (injective : Function.Injective f) :
    Function.Injective (map f) := by
  intro s
  induction s with
  | num n =>
      intro t same
      cases t <;> simp [map] at same
      rw [injective same]
  | var x =>
      intro t same
      cases t <;> simp [map] at same
      rw [same]
  | sym c =>
      intro t same
      cases t <;> simp [map] at same
      rw [same]
  | app a b iha ihb =>
      intro t same
      cases t <;> simp [map] at same
      rw [iha same.1, ihb same.2]
  | op o l r ihl ihr =>
      intro t same
      cases t <;> simp [map] at same
      obtain ⟨rfl, sl, sr⟩ := same
      rw [ihl sl, ihr sr]

end NTerm

/-! ## A grounded table and the knowledge's equality -/

/-- **A grounded table**: for an operation and two stored numbers, an answer, or `none`: the
operation declines and the call stays as written. -/
abbrev Table := OpName → Stored → Stored → Option Stored

/-- The table's answer to an operation on two terms, when both are numerals. -/
def answer (G : Table) (o : OpName) (l r : NTerm Stored) : Option Stored :=
  l.asNum.bind fun a => r.asNum.bind fun b => G o a b

/-- One operation, after its arguments are evaluated. -/
def evalOp (G : Table) (o : OpName) (l r : NTerm Stored) : NTerm Stored :=
  match answer G o l r with
  | some c => .num c
  | none => .op o l r

/-- **Evaluation by the table**, innermost first. -/
def eval (G : Table) : NTerm Stored → NTerm Stored
  | .num n => .num n
  | .var x => .var x
  | .sym c => .sym c
  | .app f a => .app (eval G f) (eval G a)
  | .op o l r => evalOp G o (eval G l) (eval G r)

/-- **Identified by the knowledge**: every instance of the two terms evaluates to terms of equal
value. -/
def Identified (G : Table) (s t : NTerm Stored) : Prop :=
  ∀ σ : ℕ → NTerm Stored, (eval G (s.subst σ)).map value = (eval G (t.subst σ)).map value

/-- **The knowledge of the step with a grounded table**: a lawful substitution action for every
table. -/
def action (G : Table) : SubstitutionAction (NTerm Stored) (ℕ → NTerm Stored) where
  E := Identified G
  equivalence := ⟨fun _ _ => rfl, fun same σ => (same σ).symm,
    fun first second σ => (first σ).trans (second σ)⟩
  apply σ t := t.subst σ
  identity := NTerm.var
  compose outer inner := fun x => (inner x).subst outer
  apply_identity := NTerm.subst_var
  apply_compose outer inner t := (NTerm.subst_subst outer inner t).symm
  preserves := by
    intro τ s t same σ
    show (eval G ((s.subst τ).subst σ)).map value = (eval G ((t.subst τ).subst σ)).map value
    rw [NTerm.subst_subst, NTerm.subst_subst]
    exact same _

theorem identified_congr {G : Table} {s s' t t' : NTerm Stored} (hs : Identified G s s')
    (ht : Identified G t t') : Identified G s t ↔ Identified G s' t' :=
  ⟨fun h σ => ((hs σ).symm.trans (h σ)).trans (ht σ),
    fun h σ => ((hs σ).trans (h σ)).trans (ht σ).symm⟩

theorem identified_subst {G : Table} {s s' : NTerm Stored} (h : Identified G s s')
    (τ : ℕ → NTerm Stored) : Identified G (s.subst τ) (s'.subst τ) :=
  (action G).preserves τ h

/-- **The knowledge identifies stored numbers of equal value**, for every table. -/
theorem numerals_identified (G : Table) (a b : Stored) :
    Identified G (.num a) (.num b) ↔ value a = value b := by
  constructor
  · intro same
    have atIdentity := same NTerm.var
    simpa [NTerm.subst, eval, NTerm.map] using atIdentity
  · intro equal σ
    simp [NTerm.subst, eval, NTerm.map, equal]

/-! ## Storage variants -/

/-- **Storage variants**: the same term up to the storage of its numerals. -/
def Variant (s s' : NTerm Stored) : Prop := s.map value = s'.map value

/-- **Every operation of the table respects the value lens**: arguments of equal value give answers
of equal value, or refusals both. -/
def TableRespects (G : Table) : Prop :=
  ∀ (o : OpName) (a a' b b' : Stored), value a = value a' → value b = value b' →
    (G o a b).map value = (G o a' b').map value

/-- The value lens on answers: the value, or the refusal. -/
def answerLens : Unit → Option Stored → Option ℚ := fun _ r => r.map value

/-- **The same condition, as `Respects` of the observer concepts**: each operation respects the value
lens of its two arguments and the value lens of answers. -/
theorem tableRespects_iff (G : Table) :
    TableRespects G ↔ ∀ o, Respects (pairRead (fun _ : Unit => value) (fun _ : Unit => value))
      answerLens (fun p : Stored × Stored => G o p.1 p.2) := by
  constructor
  · intro respects o
    rw [respects_pair_iff]
    intro a a' b b' first second _
    exact respects o a a' b b' (first ()) (second ())
  · intro respects o a a' b b' first second
    exact ((respects_pair_iff _ _ _ _).mp (respects o) a a' b b' (fun _ => first) (fun _ => second)) ()

theorem asNum_variant {L L' : NTerm Stored} (same : Variant L L') :
    L.asNum.map value = L'.asNum.map value := by
  rw [← NTerm.asNum_map, ← NTerm.asNum_map]
  exact congrArg NTerm.asNum same

theorem answer_variant {G : Table} (respects : TableRespects G) (o : OpName)
    {L L' R R' : NTerm Stored} (sameL : Variant L L') (sameR : Variant R R') :
    (answer G o L R).map value = (answer G o L' R').map value := by
  have nL := asNum_variant sameL
  have nR := asNum_variant sameR
  unfold answer
  rcases hl : L.asNum with _ | a
  · rcases hl' : L'.asNum with _ | a'
    · rfl
    · rw [hl, hl'] at nL
      simp at nL
  · rcases hl' : L'.asNum with _ | a'
    · rw [hl, hl'] at nL
      simp at nL
    · rw [hl, hl'] at nL
      simp only [Option.map_some, Option.some.injEq] at nL
      rcases hr : R.asNum with _ | b
      · rcases hr' : R'.asNum with _ | b'
        · rfl
        · rw [hr, hr'] at nR
          simp at nR
      · rcases hr' : R'.asNum with _ | b'
        · rw [hr, hr'] at nR
          simp at nR
        · rw [hr, hr'] at nR
          simp only [Option.map_some, Option.some.injEq] at nR
          exact respects o a a' b b' nL nR

theorem evalOp_variant {G : Table} (respects : TableRespects G) (o : OpName)
    {L L' R R' : NTerm Stored} (sameL : Variant L L') (sameR : Variant R R') :
    Variant (evalOp G o L R) (evalOp G o L' R') := by
  have answers := answer_variant respects o sameL sameR
  have mapL : L.map value = L'.map value := sameL
  have mapR : R.map value = R'.map value := sameR
  unfold Variant evalOp
  revert answers
  rcases answer G o L R with _ | c <;> rcases answer G o L' R' with _ | c' <;> intro answers
  · simp only [NTerm.map, mapL, mapR]
  · simp at answers
  · simp at answers
  · simp only [Option.map_some, Option.some.injEq] at answers
    simp only [NTerm.map, answers]

/-- **With a table that respects the value lens, evaluation keeps storage variants storage
variants.** -/
theorem eval_variant {G : Table} (respects : TableRespects G) :
    ∀ {u u' : NTerm Stored}, Variant u u' → Variant (eval G u) (eval G u') := by
  intro u
  induction u with
  | num n =>
      intro u' same
      cases u' <;> simp [Variant, NTerm.map] at same
      simp [Variant, eval, NTerm.map, same]
  | var x =>
      intro u' same
      cases u' <;> simp [Variant, NTerm.map] at same
      simp [Variant, eval, NTerm.map, same]
  | sym c =>
      intro u' same
      cases u' <;> simp [Variant, NTerm.map] at same
      simp [Variant, eval, NTerm.map, same]
  | app f a ihf iha =>
      intro u' same
      cases u' <;> simp [Variant, NTerm.map] at same
      have hf : (eval G f).map value = (eval G _).map value := ihf same.1
      have ha : (eval G a).map value = (eval G _).map value := iha same.2
      simp only [Variant, eval, NTerm.map, hf, ha]
  | op o l r ihl ihr =>
      intro u' same
      cases u' <;> simp [Variant, NTerm.map] at same
      obtain ⟨rfl, sl, sr⟩ := same
      exact evalOp_variant respects o (ihl sl) (ihr sr)

theorem subst_variant {s s' : NTerm Stored} (same : Variant s s') (σ : ℕ → NTerm Stored) :
    Variant (s.subst σ) (s'.subst σ) := by
  have mapped : s.map value = s'.map value := same
  show (s.subst σ).map value = (s'.subst σ).map value
  rw [NTerm.map_subst, NTerm.map_subst, mapped]

/-- **With a table that respects the value lens, storage variants are identified.** -/
theorem identified_of_variant {G : Table} (respects : TableRespects G) {s s' : NTerm Stored}
    (same : Variant s s') : Identified G s s' :=
  fun σ => eval_variant respects (subst_variant same σ)

/-- A call of an operation on two numerals, identified with a storage variant, gives answers of
equal value. -/
theorem answers_of_identified_call {G : Table} {o : OpName} {a a' b b' : Stored}
    (identified : Identified G (.op o (.num a) (.num b)) (.op o (.num a') (.num b'))) :
    (G o a b).map value = (G o a' b').map value := by
  have atIdentity := identified NTerm.var
  change (evalOp G o (.num a) (.num b)).map value = (evalOp G o (.num a') (.num b')).map value
    at atIdentity
  unfold evalOp answer at atIdentity
  simp only [NTerm.asNum, Option.bind_some] at atIdentity
  revert atIdentity
  rcases G o a b with _ | c <;> rcases G o a' b' with _ | c' <;> intro atIdentity
  · rfl
  · simp [NTerm.map] at atIdentity
  · simp [NTerm.map] at atIdentity
  · simp only [NTerm.map, NTerm.num.injEq] at atIdentity
    simp [atIdentity]

/-- **Exactly when**: the knowledge identifies every pair of storage variants exactly when every
operation of the table respects the value lens. -/
theorem identifies_variants_iff (G : Table) :
    (∀ s s', Variant s s' → Identified G s s') ↔ TableRespects G := by
  constructor
  · intro identifies o a a' b b' first second
    apply answers_of_identified_call
    apply identifies
    simp [Variant, NTerm.map, first, second]
  · intro respects s s' same
    exact identified_of_variant respects same

/-! ## Answers on the step -/

variable {O : Type} [DecidableEq O]

/-- **The answer of a configuration to a check**: the check holds at every solution of the
knowledge. -/
def Answer (G : Table) (label : O → NTerm Stored) (C : Configuration (NTerm Stored) O)
    (check : Check (NTerm Stored)) : Prop :=
  (action G).Entails C.equations fun σ => check.Holds (action G) σ label C.present

omit [DecidableEq O] in
theorem matches_congr {G : Table} {σ : ℕ → NTerm Stored} {label label' : O → NTerm Stored}
    {store : Finset O} {p p' : NTerm Stored} (pattern : Identified G (p.subst σ) (p'.subst σ))
    (rows : ∀ o, Identified G ((label o).subst σ) ((label' o).subst σ)) :
    Check.«matches» (action G) σ label store p = Check.«matches» (action G) σ label' store p' := by
  classical
  unfold Check.«matches»
  apply Finset.filter_congr
  intro o _
  exact identified_congr pattern (rows o)

omit [DecidableEq O] in
/-- **Re-storing the numerals of a query changes no count answer**, with a table that respects the
value lens. -/
theorem answer_count_variant {G : Table} (respects : TableRespects G) (label : O → NTerm Stored)
    (C : Configuration (NTerm Stored) O) {p p' : NTerm Stored} (same : Variant p p') (n : ℕ) :
    Answer G label C (.count p n) ↔ Answer G label C (.count p' n) := by
  have equal : ∀ σ, Check.«matches» (action G) σ label C.present p =
      Check.«matches» (action G) σ label C.present p' := fun σ =>
    matches_congr (identified_subst (identified_of_variant respects same) σ)
      (fun o => fun _ => rfl)
  constructor
  · intro answered σ solved
    show (Check.«matches» (action G) σ label C.present p').card = n
    rw [← equal σ]
    exact answered σ solved
  · intro answered σ solved
    show (Check.«matches» (action G) σ label C.present p).card = n
    rw [equal σ]
    exact answered σ solved

omit [DecidableEq O] in
/-- **Re-storing the numerals of a query changes no absence answer**, with a table that respects
the value lens. -/
theorem answer_absent_variant {G : Table} (respects : TableRespects G) (label : O → NTerm Stored)
    (C : Configuration (NTerm Stored) O) {p p' : NTerm Stored} (same : Variant p p') :
    Answer G label C (.predicate .none p) ↔ Answer G label C (.predicate .none p') := by
  have rows : ∀ σ o, Identified G (p.subst σ) ((label o).subst σ) ↔
      Identified G (p'.subst σ) ((label o).subst σ) := fun σ o =>
    identified_congr (identified_subst (identified_of_variant respects same) σ) (fun _ => rfl)
  constructor
  · intro answered σ solved o present related
    exact answered σ solved o present ((rows σ o).mpr related)
  · intro answered σ solved o present related
    exact answered σ solved o present ((rows σ o).mp related)

/-! ## Re-storing a whole program -/

/-- Re-storing a store of equations. -/
def restoreStore (ρ : Stored → Stored) (store : EquationStore (NTerm Stored)) :
    EquationStore (NTerm Stored) :=
  store.map fun e => (e.1.map ρ, e.2.map ρ)

/-- Re-storing a configuration: its knowledge; the present occurrences are kept. -/
def restoreConf (ρ : Stored → Stored) (C : Configuration (NTerm Stored) O) :
    Configuration (NTerm Stored) O :=
  ⟨restoreStore ρ C.equations, C.present⟩

/-- A re-stored term is a storage variant of the term. -/
theorem variant_restore {ρ : Stored → Stored} (restoring : Restoring ρ) (t : NTerm Stored) :
    Variant (t.map ρ) t := by
  show (t.map ρ).map value = t.map value
  rw [NTerm.map_map]
  exact NTerm.map_congr (fun n => restoring n) t

theorem identified_restore {G : Table} (respects : TableRespects G) {ρ : Stored → Stored}
    (restoring : Restoring ρ) (t : NTerm Stored) : Identified G (t.map ρ) t :=
  identified_of_variant respects (variant_restore restoring t)

theorem solves_restore {G : Table} (respects : TableRespects G) {ρ : Stored → Stored}
    (restoring : Restoring ρ) (σ : ℕ → NTerm Stored) (e : Equation (NTerm Stored)) :
    (action G).Solves σ (e.1.map ρ, e.2.map ρ) ↔ (action G).Solves σ e :=
  identified_congr (identified_subst (identified_restore respects restoring e.1) σ)
    (identified_subst (identified_restore respects restoring e.2) σ)

theorem models_restore {G : Table} (respects : TableRespects G) {ρ : Stored → Stored}
    (restoring : Restoring ρ) (σ : ℕ → NTerm Stored) (store : EquationStore (NTerm Stored)) :
    (action G).Models σ (restoreStore ρ store) ↔ (action G).Models σ store := by
  constructor
  · intro solved e member
    exact (solves_restore respects restoring σ e).mp (solved _ (List.mem_map.mpr ⟨e, member, rfl⟩))
  · intro solved e' member
    obtain ⟨e, inside, rfl⟩ := List.mem_map.mp member
    exact (solves_restore respects restoring σ e).mpr (solved e inside)

omit [DecidableEq O] in
theorem holds_restore {G : Table} (respects : TableRespects G) {ρ : Stored → Stored}
    (restoring : Restoring ρ) (σ : ℕ → NTerm Stored) (label : O → NTerm Stored) (store : Finset O)
    (check : Check (NTerm Stored)) :
    (check.map (NTerm.map ρ)).Holds (action G) σ (NTerm.map ρ ∘ label) store ↔
      check.Holds (action G) σ label store := by
  have rows : ∀ o, Identified G (((NTerm.map ρ ∘ label) o).subst σ) ((label o).subst σ) :=
    fun o => identified_subst (identified_restore respects restoring (label o)) σ
  cases check with
  | equal l r => exact solves_restore respects restoring σ (l, r)
  | predicate quantifier p =>
      have pattern := identified_subst (identified_restore respects restoring p) σ
      exact quantifier.holds_congr fun o _ => identified_congr pattern (rows o)
  | count p n =>
      have equal := matches_congr (store := store)
        (identified_subst (identified_restore respects restoring p) σ) rows
      show (Check.«matches» (action G) σ (NTerm.map ρ ∘ label) store (p.map ρ)).card = n ↔
        (Check.«matches» (action G) σ label store p).card = n
      rw [equal]

omit [DecidableEq O] in
/-- **Re-storing every numeral changes no answer**: of the knowledge, the labels and the query,
for counts, absence and equations alike. -/
theorem answer_restore {G : Table} (respects : TableRespects G) {ρ : Stored → Stored}
    (restoring : Restoring ρ) (label : O → NTerm Stored) (C : Configuration (NTerm Stored) O)
    (check : Check (NTerm Stored)) :
    Answer G (NTerm.map ρ ∘ label) (restoreConf ρ C) (check.map (NTerm.map ρ)) ↔
      Answer G label C check := by
  constructor
  · intro answered σ solved
    exact (holds_restore respects restoring σ label C.present check).mp
      (answered σ ((models_restore respects restoring σ C.equations).mpr solved))
  · intro answered σ solved
    exact (holds_restore respects restoring σ label C.present check).mpr
      (answered σ ((models_restore respects restoring σ C.equations).mp solved))

omit [DecidableEq O] in
theorem equations_restore (f : NTerm Stored → NTerm Stored) (label : O → NTerm Stored) :
    ∀ (patterns : List (NTerm Stored)) (selected : List O),
      Selection.equations (f ∘ label) (patterns.map f) selected =
        (Selection.equations label patterns selected).map fun e => (f e.1, f e.2)
  | [], _ => rfl
  | _ :: _, [] => rfl
  | p :: ps, o :: os => by
      show (f p, f (label o)) :: Selection.equations (f ∘ label) (ps.map f) os =
        (f p, f (label o)) :: (Selection.equations label ps os).map fun e => (f e.1, f e.2)
      rw [equations_restore f label ps os]

omit [DecidableEq O] in
theorem problem_restore (ρ : Stored → Stored) (sel : Selection O) (label : O → NTerm Stored)
    (rule : RuleInstance (NTerm Stored)) (C : Configuration (NTerm Stored) O) :
    sel.problem (NTerm.map ρ ∘ label) (rule.map (NTerm.map ρ)) (restoreConf ρ C) =
      restoreStore ρ (sel.problem label rule C) := by
  simp only [Selection.problem, restoreConf, restoreStore, RuleInstance.map, List.map_append,
    equations_restore]

theorem result_restore (ρ : Stored → Stored) (sel : Selection O) (label : O → NTerm Stored)
    (rule : RuleInstance (NTerm Stored)) (C : Configuration (NTerm Stored) O) :
    restoreConf ρ (sel.result label rule C) =
      sel.result (NTerm.map ρ ∘ label) (rule.map (NTerm.map ρ)) (restoreConf ρ C) := by
  unfold Selection.result
  rw [problem_restore]
  rfl

/-- **Every step carries over to the re-stored program.** -/
theorem step_restore {G : Table} (respects : TableRespects G) {ρ : Stored → Stored}
    (restoring : Restoring ρ) {label : O → NTerm Stored} {rule : RuleInstance (NTerm Stored)}
    {C D : Configuration (NTerm Stored) O} (step : Step (action G) label rule C D) :
    Step (action G) (NTerm.map ρ ∘ label) (rule.map (NTerm.map ρ)) (restoreConf ρ C)
      (restoreConf ρ D) := by
  obtain ⟨sel, valid, rfl⟩ := step
  refine ⟨sel, ⟨valid.take_distinct, valid.output_distinct, ?_, ?_, ?_, ?_, ?_, ?_⟩,
    result_restore ρ sel label rule C⟩
  · simpa [RuleInstance.map] using valid.take_length
  · simpa [RuleInstance.map] using valid.read_length
  · show sel.made.map (NTerm.map ρ ∘ label) = rule.produce.map (NTerm.map ρ)
    exact (List.map_map (g := NTerm.map ρ) (f := label) (l := sel.made)).symm.trans
      (congrArg (List.map (NTerm.map ρ)) valid.outputs)
  · exact ⟨valid.occurrences.taken_subset, valid.occurrences.kept_subset, valid.occurrences.apart,
      valid.occurrences.fresh, fun _ member => absurd member List.not_mem_nil⟩
  · rw [problem_restore]
    obtain ⟨σ, solved⟩ := valid.consistent
    exact ⟨σ, (models_restore respects restoring σ _).mpr solved⟩
  · intro check' member σ solved
    rw [problem_restore] at solved
    obtain ⟨check, inside, rfl⟩ := List.mem_map.mp member
    exact (holds_restore respects restoring σ label C.present check).mpr
      (valid.checks check inside σ ((models_restore respects restoring σ _).mp solved))

/-- **For an injective re-storing, every step of the re-stored program comes from a step of the
program.** -/
theorem step_restore_back {G : Table} (respects : TableRespects G) {ρ : Stored → Stored}
    (restoring : Restoring ρ) (injective : Function.Injective ρ) {label : O → NTerm Stored}
    {rule : RuleInstance (NTerm Stored)} {C : Configuration (NTerm Stored) O}
    {D' : Configuration (NTerm Stored) O}
    (step : Step (action G) (NTerm.map ρ ∘ label) (rule.map (NTerm.map ρ)) (restoreConf ρ C) D') :
    ∃ D, Step (action G) label rule C D ∧ D' = restoreConf ρ D := by
  obtain ⟨sel, valid, rfl⟩ := step
  refine ⟨sel.result label rule C,
    ⟨sel, ⟨valid.take_distinct, valid.output_distinct, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩,
    (result_restore ρ sel label rule C).symm⟩
  · simpa [RuleInstance.map] using valid.take_length
  · simpa [RuleInstance.map] using valid.read_length
  · have outputs : (sel.made.map label).map (NTerm.map ρ) = rule.produce.map (NTerm.map ρ) :=
      List.map_map.trans valid.outputs
    exact List.map_injective_iff.mpr (NTerm.map_injective injective) outputs
  · exact ⟨valid.occurrences.taken_subset, valid.occurrences.kept_subset, valid.occurrences.apart,
      valid.occurrences.fresh, fun _ member => absurd member List.not_mem_nil⟩
  · obtain ⟨σ, solved⟩ := valid.consistent
    rw [problem_restore] at solved
    exact ⟨σ, (models_restore respects restoring σ _).mp solved⟩
  · intro check inside σ solved
    have restored := valid.checks (check.map (NTerm.map ρ)) (List.mem_map.mpr ⟨check, inside, rfl⟩) σ
      (by
        rw [problem_restore]
        exact (models_restore respects restoring σ _).mpr solved)
    exact (holds_restore respects restoring σ label C.present check).mp restored

/-- **Runs of a program**: firings of its rules, any number of times. -/
abbrev Reach (G : Table) (label : O → NTerm Stored) (R : Set (RuleInstance (NTerm Stored))) :
    Configuration (NTerm Stored) O → Configuration (NTerm Stored) O → Prop :=
  Relation.ReflTransGen fun C D => ∃ rule ∈ R, Step (action G) label rule C D

/-- The program with every numeral re-stored. -/
def restoreProgram (ρ : Stored → Stored) (R : Set (RuleInstance (NTerm Stored))) :
    Set (RuleInstance (NTerm Stored)) :=
  RuleInstance.map (NTerm.map ρ) '' R

/-- **Every run carries over to the re-stored program.** -/
theorem reach_restore {G : Table} (respects : TableRespects G) {ρ : Stored → Stored}
    (restoring : Restoring ρ) {label : O → NTerm Stored} {R : Set (RuleInstance (NTerm Stored))}
    {C D : Configuration (NTerm Stored) O} (reach : Reach G label R C D) :
    Reach G (NTerm.map ρ ∘ label) (restoreProgram ρ R) (restoreConf ρ C) (restoreConf ρ D) := by
  induction reach with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ fired ih =>
      obtain ⟨rule, member, step⟩ := fired
      exact ih.tail ⟨_, ⟨rule, member, rfl⟩, step_restore respects restoring step⟩

/-- **For an injective re-storing, every run of the re-stored program comes from a run.** -/
theorem reach_restore_back {G : Table} (respects : TableRespects G) {ρ : Stored → Stored}
    (restoring : Restoring ρ) (injective : Function.Injective ρ) {label : O → NTerm Stored}
    {R : Set (RuleInstance (NTerm Stored))} {C : Configuration (NTerm Stored) O}
    {D' : Configuration (NTerm Stored) O}
    (reach : Reach G (NTerm.map ρ ∘ label) (restoreProgram ρ R) (restoreConf ρ C) D') :
    ∃ D, Reach G label R C D ∧ D' = restoreConf ρ D := by
  induction reach with
  | refl => exact ⟨C, Relation.ReflTransGen.refl, rfl⟩
  | tail _ fired ih =>
      obtain ⟨D, reachD, rfl⟩ := ih
      obtain ⟨_, ⟨rule, member, rfl⟩, step⟩ := fired
      obtain ⟨E, back, rfl⟩ := step_restore_back respects restoring injective step
      exact ⟨E, reachD.tail ⟨rule, member, back⟩, rfl⟩

/-- **Representation independence for programs**: with a table that respects the value lens and an
injective re-storing, an answer is reachable by a run of the program exactly when the re-stored
answer is reachable by a run of the re-stored program. -/
theorem program_answers_iff {G : Table} (respects : TableRespects G) {ρ : Stored → Stored}
    (restoring : Restoring ρ) (injective : Function.Injective ρ) (label : O → NTerm Stored)
    (R : Set (RuleInstance (NTerm Stored))) (C : Configuration (NTerm Stored) O)
    (check : Check (NTerm Stored)) :
    (∃ D, Reach G label R C D ∧ Answer G label D check) ↔
      ∃ D', Reach G (NTerm.map ρ ∘ label) (restoreProgram ρ R) (restoreConf ρ C) D' ∧
        Answer G (NTerm.map ρ ∘ label) D' (check.map (NTerm.map ρ)) := by
  constructor
  · rintro ⟨D, reach, answered⟩
    exact ⟨_, reach_restore respects restoring reach,
      (answer_restore respects restoring label D check).mpr answered⟩
  · rintro ⟨D', reach, answered⟩
    obtain ⟨D, reachD, rfl⟩ := reach_restore_back respects restoring injective reach
    exact ⟨D, reachD, (answer_restore respects restoring label D check).mp answered⟩

/-- **The same for every run**: an answer holds after every run exactly when the re-stored answer
holds after every run of the re-stored program. -/
theorem program_every_answer_iff {G : Table} (respects : TableRespects G) {ρ : Stored → Stored}
    (restoring : Restoring ρ) (injective : Function.Injective ρ) (label : O → NTerm Stored)
    (R : Set (RuleInstance (NTerm Stored))) (C : Configuration (NTerm Stored) O)
    (check : Check (NTerm Stored)) :
    (∀ D, Reach G label R C D → Answer G label D check) ↔
      ∀ D', Reach G (NTerm.map ρ ∘ label) (restoreProgram ρ R) (restoreConf ρ C) D' →
        Answer G (NTerm.map ρ ∘ label) D' (check.map (NTerm.map ρ)) := by
  constructor
  · intro every D' reach
    obtain ⟨D, reachD, rfl⟩ := reach_restore_back respects restoring injective reach
    exact (answer_restore respects restoring label D check).mpr (every D reachD)
  · intro every D reach
    exact (answer_restore respects restoring label D check).mp
      (every _ (reach_restore respects restoring reach))

/-! ## The converse: a one-row program -/

/-- The firing that only checks a count. -/
def checkRule (p : NTerm Stored) (n : ℕ) : RuleInstance (NTerm Stored) := ⟨[], [], [], [.count p n], []⟩

/-- The empty selection. -/
def noSelection : Selection ℕ := ⟨[], [], []⟩

/-- The one-row configuration. -/
def oneRow : Configuration (NTerm Stored) ℕ := ⟨[], {0}⟩

theorem count_one_row {G : Table} {row p : NTerm Stored} :
    Answer G (fun _ : ℕ => row) oneRow (.count p 1) ↔ Identified G p row := by
  constructor
  · intro answered
    have atIdentity := answered NTerm.var (fun e member => absurd member List.not_mem_nil)
    change (Check.«matches» (action G) NTerm.var (fun _ : ℕ => row) {0} p).card = 1 at atIdentity
    classical
    unfold Check.«matches» at atIdentity
    rw [Finset.filter_singleton] at atIdentity
    split_ifs at atIdentity with related
    · have same : Identified G (p.subst NTerm.var) (row.subst NTerm.var) := related
      rw [NTerm.subst_var, NTerm.subst_var] at same
      exact same
    · simp at atIdentity
  · intro identified σ _
    show (Check.«matches» (action G) σ (fun _ : ℕ => row) {0} p).card = 1
    classical
    unfold Check.«matches»
    rw [Finset.filter_singleton, if_pos]
    · exact Finset.card_singleton 0
    · exact identified_subst identified σ

/-- **The converse, by a one-row program**: if one operation of the table gives answers of
different value to two storages of the same arguments, then on the configuration holding the one
call the count of the call is `1` and the count of its storage variant is not. -/
theorem one_row_converse {G : Table} {o : OpName} {a a' b b' : Stored} (first : value a = value a')
    (second : value b = value b') (differ : (G o a b).map value ≠ (G o a' b').map value) :
    Variant (.op o (.num a) (.num b)) (.op o (.num a') (.num b')) ∧
      Answer G (fun _ => .op o (.num a) (.num b)) oneRow (.count (.op o (.num a) (.num b)) 1) ∧
      ¬ Answer G (fun _ => .op o (.num a) (.num b)) oneRow (.count (.op o (.num a') (.num b')) 1) := by
  refine ⟨by simp [Variant, NTerm.map, first, second], count_one_row.mpr fun _ => rfl, ?_⟩
  intro answered
  have identified := count_one_row.mp answered
  exact differ (answers_of_identified_call fun σ => (identified σ).symm)

theorem checkRule_step_iff {G : Table} {row p : NTerm Stored} :
    (∃ D, Step (action G) (fun _ : ℕ => row) (checkRule p 1) oneRow D) ↔
      Answer G (fun _ : ℕ => row) oneRow (.count p 1) := by
  constructor
  · rintro ⟨D, sel, valid, _⟩
    have problem : sel.problem (fun _ : ℕ => row) (checkRule p 1) oneRow = [] := by
      have taken : sel.taken = [] := List.length_eq_zero_iff.mp valid.take_length.symm
      have read : sel.read = [] := List.length_eq_zero_iff.mp valid.read_length.symm
      simp [Selection.problem, Selection.equations, checkRule, oneRow, taken, read]
    have checked := valid.checks (.count p 1) (List.mem_singleton_self _)
    rw [problem] at checked
    exact checked
  · intro answered
    refine ⟨noSelection.result (fun _ : ℕ => row) (checkRule p 1) oneRow, noSelection,
      ⟨List.nodup_nil, List.nodup_nil, rfl, rfl, rfl, ?_, ?_, ?_⟩, rfl⟩
    · exact ⟨by simp [noSelection, Selection.commit], by simp [noSelection, Selection.commit],
        by simp [noSelection, Selection.commit], by simp [noSelection, Selection.commit],
        fun _ member => absurd member List.not_mem_nil⟩
    · exact ⟨NTerm.var, fun e member => absurd member List.not_mem_nil⟩
    · intro check member
      obtain rfl := List.mem_singleton.mp member
      exact answered

/-- **On the step**: the firing that checks the count of the call is admitted; the firing that
checks the count of its storage variant is refused. -/
theorem one_row_step_converse {G : Table} {o : OpName} {a a' b b' : Stored}
    (first : value a = value a') (second : value b = value b')
    (differ : (G o a b).map value ≠ (G o a' b').map value) :
    (∃ D, Step (action G) (fun _ : ℕ => .op o (.num a) (.num b))
        (checkRule (.op o (.num a) (.num b)) 1) oneRow D) ∧
      ¬ ∃ D, Step (action G) (fun _ : ℕ => .op o (.num a) (.num b))
        (checkRule (.op o (.num a') (.num b')) 1) oneRow D := by
  obtain ⟨_, admitted, refused⟩ := one_row_converse first second differ
  exact ⟨checkRule_step_iff.mpr admitted, fun fired => refused (checkRule_step_iff.mp fired)⟩

/-! ## Instances -/

/-- **The exact table**: addition, subtraction, multiplication, and division by a nonzero divisor,
on values. -/
def exactTable : Table
  | .plus, a, b => some (.frac (value a + value b))
  | .minus, a, b => some (.frac (value a - value b))
  | .times, a, b => some (.frac (value a * value b))
  | .divide, a, b => if value b = 0 then none else some (.frac (value a / value b))

theorem exactTable_respects : TableRespects exactTable := by
  intro o a a' b b' first second
  cases o <;> simp only [exactTable, first, second]

/-- **A model of measured behaviour, HE's `/`**: truncating on two stored integers, exact otherwise
(`NumberLens.storedDiv`); a zero divisor is declined here, where HE answers an error. Measured:
`(/ 5 2)` is `2`, `(/ 5.0 2)` is `2.5`. -/
def storedDivTable : Table
  | .divide, a, b => if value b = 0 then none else some (storedDiv a b)
  | _, _, _ => none

/-- **The storage-dependent division does not respect the value lens**, at `5` and `5.0`. -/
theorem storedDivTable_not_respects : ¬ TableRespects storedDivTable := by
  intro respects
  have equal := respects .divide five fiveFrac two.1 two.1 (value_five.trans value_fiveFrac.symm) rfl
  have nonzero : value two.1 ≠ 0 := two.2
  simp only [storedDivTable, if_neg nonzero, Option.map_some, Option.some.injEq] at equal
  rw [storedDiv_five_two, storedDiv_fiveFrac_two] at equal
  norm_num at equal

/-- **The one-row configuration holding `(/ 5 2)`**: the count of the query `(/ 5 2)` is `1`, and
the count of its storage variant `(/ 5.0 2)` is not `1`. -/
theorem division_one_row :
    Answer storedDivTable (fun _ => .op .divide (.num five) (.num two.1)) oneRow
        (.count (.op .divide (.num five) (.num two.1)) 1) ∧
      ¬ Answer storedDivTable (fun _ => .op .divide (.num five) (.num two.1)) oneRow
        (.count (.op .divide (.num fiveFrac) (.num two.1)) 1) := by
  have nonzero : value two.1 ≠ 0 := two.2
  have differ : (storedDivTable .divide five two.1).map value ≠
      (storedDivTable .divide fiveFrac two.1).map value := by
    simp only [storedDivTable, if_neg nonzero, Option.map_some, ne_eq, Option.some.injEq]
    rw [storedDiv_five_two, storedDiv_fiveFrac_two]
    norm_num
  obtain ⟨_, admitted, refused⟩ :=
    one_row_converse (value_five.trans value_fiveFrac.symm) (rfl : value two.1 = value two.1) differ
  exact ⟨admitted, refused⟩

/-! ### A program that computes, and its run -/

/-- `(foo t)`. -/
def foo (t : NTerm Stored) : NTerm Stored := .app (.sym "foo") t

/-- `(bar t)`. -/
def bar (t : NTerm Stored) : NTerm Stored := .app (.sym "bar") t

/-- **The rule**: take `(foo $x)`, make `(bar (+ $x 1))`. -/
def incr : RuleInstance (NTerm Stored) :=
  ⟨[foo (.var 0)], [], [], [], [bar (.op .plus (.var 0) (.num (.int 1)))]⟩

/-- The labels: the row `(foo 5)`, and fresh rows for what is made. -/
def incrLabel : ℕ → NTerm Stored
  | 0 => foo (.num (.int 5))
  | _ => bar (.op .plus (.var 0) (.num (.int 1)))

/-- The start: one row, `(foo 5)`. -/
def start : Configuration (NTerm Stored) ℕ := ⟨[], {0}⟩

/-- The selection: take row `0`, make row `1`. -/
def incrSelection : Selection ℕ := ⟨[0], [], [1]⟩

/-- The configuration after the firing. -/
def finish : Configuration (NTerm Stored) ℕ := incrSelection.result incrLabel incr start

theorem finish_equations : finish.equations = [(foo (.var 0), foo (.num (.int 5)))] := rfl

theorem finish_present : finish.present = {1} := by
  ext o
  simp [finish, Selection.result, incrSelection, start,
    MeTTaCalculus.OccurrenceCommits.fire, Selection.commit]

/-- **The rule fires** from `(foo 5)`. -/
theorem incr_fires : Step (action exactTable) incrLabel incr start finish := by
  refine ⟨incrSelection, ⟨by simp [incrSelection], by simp [incrSelection], rfl, rfl, rfl, ?_, ?_, ?_⟩,
    rfl⟩
  · exact ⟨by simp [incrSelection, Selection.commit, start],
      by simp [incrSelection, Selection.commit],
      by simp [incrSelection, Selection.commit],
      by simp [incrSelection, Selection.commit, start],
      fun _ member => absurd member List.not_mem_nil⟩
  · refine ⟨fun _ => .num (.int 5), fun e member => ?_⟩
    have problem : incrSelection.problem incrLabel incr start = [(foo (.var 0), foo (.num (.int 5)))] :=
      rfl
    rw [problem] at member
    obtain rfl := List.mem_singleton.mp member
    exact fun _ => rfl
  · intro check member
    exact absurd member List.not_mem_nil

/-- A term whose value reading is a numeral is a numeral. -/
theorem num_of_map_value {U : NTerm Stored} {q : ℚ} (same : U.map value = .num q) :
    ∃ u, U = .num u ∧ value u = q := by
  cases U with
  | num u => exact ⟨u, rfl, by simpa [NTerm.map] using same⟩
  | var x => simp [NTerm.map] at same
  | sym c => simp [NTerm.map] at same
  | app f a => simp [NTerm.map] at same
  | op o l r => simp [NTerm.map] at same

/-- **After the run, the count of `(bar 6)` is `1`**: the made row `(bar (+ $x 1))` is `(bar 6)` at
every solution of the knowledge, which binds `$x` to `5`. -/
theorem incr_answer : Answer exactTable incrLabel finish (.count (bar (.num (.int 6))) 1) := by
  intro σ solved
  have fooSolved : Identified exactTable (foo (σ 0)) (foo (.num (.int 5))) :=
    solved (foo (.var 0), foo (.num (.int 5))) (by rw [finish_equations]; exact List.mem_singleton_self _)
  have five : ∀ τ, ∃ u, eval exactTable ((σ 0).subst τ) = .num u ∧ value u = value (.int 5) := by
    intro τ
    have atτ : NTerm.app (.sym "foo") ((eval exactTable ((σ 0).subst τ)).map value) =
        NTerm.app (.sym "foo") (.num (value (.int 5))) := fooSolved τ
    injection atτ with _ inner
    exact num_of_map_value inner
  show (Check.«matches» (action exactTable) σ incrLabel finish.present (bar (.num (.int 6)))).card = 1
  rw [finish_present]
  classical
  unfold Check.«matches»
  rw [Finset.filter_singleton, if_pos]
  · exact Finset.card_singleton 1
  · intro τ
    obtain ⟨u, evaluated, valued⟩ := five τ
    have computed : eval exactTable (((incrLabel 1).subst σ).subst τ) =
        NTerm.app (.sym "bar") (.num (.frac (value u + value (.int 1)))) := by
      show NTerm.app (.sym "bar")
        (evalOp exactTable .plus (eval exactTable ((σ 0).subst τ)) (.num (.int 1))) = _
      rw [evaluated]
      rfl
    show (eval exactTable (((bar (.num (.int 6))).subst σ).subst τ)).map value =
      (eval exactTable (((incrLabel 1).subst σ).subst τ)).map value
    rw [computed]
    show NTerm.app (.sym "bar") (.num (value (.int 6))) =
      NTerm.app (.sym "bar") (.num (value u + value (.int 1)))
    rw [valued]
    norm_num [value]

/-- The run, as a run of the program `{incr}`. -/
theorem incr_reach : Reach exactTable incrLabel {incr} start finish :=
  Relation.ReflTransGen.single ⟨incr, rfl, incr_fires⟩

/-- **Swapping the storage of whole numbers**: an integer becomes a fraction and a whole fraction an
integer; other fractions are kept. -/
def swapStorage : Stored → Stored
  | .int n => .frac n
  | .frac q => if q.den = 1 then .int q.num else .frac q

theorem swapStorage_restoring : Restoring swapStorage := by
  intro x
  cases x with
  | int n => rfl
  | frac q =>
      simp only [swapStorage]
      split_ifs with whole
      · exact Rat.coe_int_num_of_den_eq_one whole
      · rfl

theorem swapStorage_injective : Function.Injective swapStorage := by
  intro x y same
  cases x with
  | int n =>
      cases y with
      | int m =>
          simp only [swapStorage, Stored.frac.injEq, Int.cast_inj] at same
          rw [same]
      | frac q =>
          simp only [swapStorage] at same
          by_cases whole : q.den = 1
          · rw [if_pos whole] at same
            cases same
          · rw [if_neg whole] at same
            cases same
            exact absurd (Rat.den_intCast n) whole
  | frac q =>
      cases y with
      | int m =>
          simp only [swapStorage] at same
          by_cases whole : q.den = 1
          · rw [if_pos whole] at same
            cases same
          · rw [if_neg whole] at same
            cases same
            exact absurd (Rat.den_intCast m) whole
      | frac q' =>
          simp only [swapStorage] at same
          by_cases whole : q.den = 1 <;> by_cases whole' : q'.den = 1
          · rw [if_pos whole, if_pos whole'] at same
            injection same with numerators
            rw [← Rat.coe_int_num_of_den_eq_one whole, ← Rat.coe_int_num_of_den_eq_one whole',
              numerators]
          · rw [if_pos whole, if_neg whole'] at same
            cases same
          · rw [if_neg whole, if_pos whole'] at same
            cases same
          · rw [if_neg whole, if_neg whole'] at same
            exact same

/-- **The re-stored program runs and answers as the program does**: with every numeral's storage
swapped (`(foo 5.0)`, `(bar (+ $x 1.0))`), the rule fires and the count of `(bar 6.0)` is `1`. -/
theorem incr_restored :
    Step (action exactTable) (NTerm.map swapStorage ∘ incrLabel) (incr.map (NTerm.map swapStorage))
        (restoreConf swapStorage start) (restoreConf swapStorage finish) ∧
      Answer exactTable (NTerm.map swapStorage ∘ incrLabel) (restoreConf swapStorage finish)
        ((Check.count (bar (.num (.int 6))) 1).map (NTerm.map swapStorage)) :=
  ⟨step_restore exactTable_respects swapStorage_restoring incr_fires,
    (answer_restore exactTable_respects swapStorage_restoring incrLabel finish _).mpr incr_answer⟩

#print axioms action
#print axioms numerals_identified
#print axioms tableRespects_iff
#print axioms eval_variant
#print axioms identified_of_variant
#print axioms answers_of_identified_call
#print axioms identifies_variants_iff
#print axioms answer_count_variant
#print axioms answer_absent_variant
#print axioms answer_restore
#print axioms step_restore
#print axioms step_restore_back
#print axioms reach_restore
#print axioms reach_restore_back
#print axioms program_answers_iff
#print axioms program_every_answer_iff
#print axioms count_one_row
#print axioms one_row_converse
#print axioms checkRule_step_iff
#print axioms one_row_step_converse
#print axioms exactTable_respects
#print axioms storedDivTable_not_respects
#print axioms division_one_row
#print axioms incr_fires
#print axioms incr_answer
#print axioms incr_reach
#print axioms swapStorage_restoring
#print axioms swapStorage_injective
#print axioms incr_restored

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.OnTheStep
